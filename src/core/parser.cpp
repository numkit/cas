// core/parser.cpp — pratt parser: source text -> Ctx constructors.
#include <numkit/cas/core/parser.hpp>

namespace numkit::cas {
namespace {

enum class Tok : std::uint8_t {
    End,
    Ident,  // [a-zA-Z_][a-zA-Z_0-9]*
    Number, // digits [. digits]
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    LParen,
    RParen,
};

struct Token {
    Tok kind = Tok::End;
    std::size_t pos = 0; // offset of the first character
    std::string text;    // Ident: name; Number: integer part
    std::string frac;    // Number: digits after '.' ("" if no point)
};

bool isSpace(char ch)
{
    return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n' ||
           ch == '\f' || ch == '\v';
}

bool isDigit(char ch) { return ch >= '0' && ch <= '9'; }

bool isIdentStart(char ch)
{
    return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_';
}

bool isIdentChar(char ch) { return isIdentStart(ch) || isDigit(ch); }

Token lex(const std::string &src, std::size_t &pos)
{
    while (pos < src.size() && isSpace(src[pos]))
        ++pos;
    Token t;
    t.pos = pos;
    if (pos >= src.size())
        return t;
    const char ch = src[pos];
    if (isIdentStart(ch)) {
        while (pos < src.size() && isIdentChar(src[pos])) {
            t.text += src[pos];
            ++pos;
        }
        t.kind = Tok::Ident;
        return t;
    }
    if (isDigit(ch)) {
        while (pos < src.size() && isDigit(src[pos])) {
            t.text += src[pos];
            ++pos;
        }
        if (pos < src.size() && src[pos] == '.') {
            ++pos;
            if (pos >= src.size() || !isDigit(src[pos]))
                throw ParseError(pos, "digit expected after '.'");
            while (pos < src.size() && isDigit(src[pos])) {
                t.frac += src[pos];
                ++pos;
            }
        }
        t.kind = Tok::Number;
        return t;
    }
    ++pos;
    switch (ch) {
    case '+': t.kind = Tok::Plus; break;
    case '-': t.kind = Tok::Minus; break;
    case '*': t.kind = Tok::Star; break;
    case '/': t.kind = Tok::Slash; break;
    case '^': t.kind = Tok::Caret; break;
    case '(': t.kind = Tok::LParen; break;
    case ')': t.kind = Tok::RParen; break;
    default: throw ParseError(t.pos, std::string("unexpected character '") + ch + "'");
    }
    return t;
}

// Binary operator binding powers; the printing ladder in expr.cpp
// (Add 40, Mul 50, Pow 60) is the same contract, so printed
// expressions re-parse to the identical node.
int bp(Tok k)
{
    switch (k) {
    case Tok::Plus:
    case Tok::Minus: return 40;
    case Tok::Star:
    case Tok::Slash: return 50;
    case Tok::Caret: return 60;
    default: return 0;
    }
}

class Parser
{
public:
    Parser(Ctx &c, const std::string &src) : c_(c), src_(src), cur_(lex(src, pos_)) {}

    Expr run()
    {
        Expr e = parseExpr(0);
        if (cur_.kind != Tok::End)
            fail(cur_.pos, "unexpected token after expression");
        return e;
    }

private:
    // MATLAB operator precedence, loose to tight: '+' '-' (40) <
    // '*' '/' (50) < unary +/- < '^' (60). The operand of a unary
    // sign therefore swallows only power expressions:
    //   -x^2 == -(x^2),  -x + y == (-x) + y,
    //   y^-1*exp(-y) == (y^-1)*exp(-y)   (NOT y^(-(1*exp(-y))))
    // Any value in (50, 60) implements that; 55 is the midpoint.
    static constexpr int kUnaryBp = 55;

    [[noreturn]] static void fail(std::size_t pos, const std::string &msg)
    {
        throw ParseError(pos, msg);
    }

    void advance() { cur_ = lex(src_, pos_); }

    void expect(Tok k, const char *msg)
    {
        if (cur_.kind != k)
            fail(cur_.pos, msg);
        advance();
    }

    Expr parseExpr(int minBp)
    {
        Expr left = nud();
        for (;;) {
            const int b = bp(cur_.kind);
            if (b <= minBp)
                break;
            const Tok op = cur_.kind;
            advance();
            // Left-associative operators parse the rhs at their own
            // binding power; '^' is right-associative and parses one
            // level lower so a following '^' binds to the right.
            left = apply(op, left, parseExpr(op == Tok::Caret ? b - 1 : b));
        }
        return left;
    }

    Expr nud()
    {
        switch (cur_.kind) {
        case Tok::Minus: {
            advance();
            return c_.neg(parseExpr(kUnaryBp));
        }
        case Tok::Plus: {
            advance();
            return parseExpr(kUnaryBp);
        }
        case Tok::Number:
            return numberLiteral();
        case Tok::Ident:
            return identLiteral();
        case Tok::LParen: {
            advance();
            const Expr e = parseExpr(0);
            expect(Tok::RParen, "')' expected");
            return e;
        }
        case Tok::End:
            fail(cur_.pos, "unexpected end of input");
        default:
            fail(cur_.pos, "unexpected token");
        }
    }

    Expr apply(Tok op, Expr a, Expr b)
    {
        switch (op) {
        case Tok::Plus: return c_.add({a, b});
        case Tok::Minus: return c_.add({a, c_.neg(b)});
        case Tok::Star: return c_.mul({a, b});
        case Tok::Slash: return c_.div(a, b);
        case Tok::Caret: return c_.pow(a, b);
        default: assert(false && "not a binary token"); return {};
        }
    }

    Expr numberLiteral()
    {
        const Token t = cur_;
        advance();
        BigInt ipart;
        if (!BigInt::tryParse(ipart, t.text))
            fail(t.pos, "malformed number '" + t.text + "'");
        if (t.frac.empty())
            return c_.number(Rational(std::move(ipart), BigInt(1)));
        // value = (ipart*10^k + frac)/10^k, k = frac.size(). The
        // literal is exact iff frac is divisible by 5^k (only then
        // does the value live in Z[1/2]); strip the fives and keep
        // the 2^k denominator.
        BigInt frac;
        if (!BigInt::tryParse(frac, t.frac))
            fail(t.pos, "malformed number '0." + t.frac + "'");
        std::size_t k = t.frac.size();
        const BigInt five(5);
        while (k > 0) {
            BigInt q, r;
            BigInt::divMod(frac, five, q, r);
            if (!r.isZero())
                break;
            frac = std::move(q);
            --k;
        }
        if (k != 0)
            fail(t.pos, "decimal '" + t.text + "." + t.frac +
                            "' is not exactly representable; write it as a fraction");
        const BigInt scale = BigInt::powUInt(BigInt(2), t.frac.size());
        BigInt num = ipart * scale + frac;
        return c_.number(Rational(std::move(num), scale));
    }

    Expr identLiteral()
    {
        const Token t = cur_;
        advance();
        if (cur_.kind == Tok::LParen) {
            advance();
            const Expr arg = parseExpr(0);
            expect(Tok::RParen, "')' expected");
            return c_.func(t.text, arg);
        }
        return c_.symbol(t.text);
    }

    Ctx &c_;
    const std::string &src_;
    std::size_t pos_ = 0;
    Token cur_;
};

} // namespace

Expr parseExpr(Ctx &c, const std::string &src)
{
    return Parser(c, src).run();
}

} // namespace numkit::cas
