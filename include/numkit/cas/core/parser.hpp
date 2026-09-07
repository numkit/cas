// core/parser.hpp — pratt parser from source text directly into a Ctx.
#pragma once

#include <numkit/cas/core/expr.hpp>

#include <cstddef>
#include <stdexcept>
#include <string>

namespace numkit::cas {

// Thrown by parseExpr on malformed input; pos() is the 0-based offset
// of the offending character (or src.size() for unexpected end).
class ParseError : public std::runtime_error {
public:
    ParseError(std::size_t pos, const std::string &msg)
        : std::runtime_error(msg), pos_(pos)
    {
    }
    std::size_t pos() const { return pos_; }

private:
    std::size_t pos_;
};

// Grammar (MATLAB-style precedence; see notes/c1-algebraic-layer.md
// item 8):
//   expr    := unary ( ('+'|'-'|'*'|'/'|'^') expr )?
//             '+' '-' bind 40 (left), '*' '/' 50 (left), '^' 60 (right)
//   unary   := ('-'|'+') unary | postfix     — looser than '^':
//             -x^2 == -(x^2), but exponents take a sign: 2^-1 == 1/2
//   postfix := primary ('^' unary)?
//   primary := number | symbol | ident '(' expr ')' | '(' expr ')'
// Numbers: integer literals, `p/q` via the '/' operator (canonical
// folding makes the Rational), decimal literals only when dyadic
// (exactly representable: 0.5 -> 1/2); others are a ParseError —
// non-dyadic decimals must be written as fractions, the sym('...')
// constructor contract. An identifier directly followed by '(' is a
// function of one argument (any name; the core owns the semantics),
// otherwise a symbol. The algebraic-number RootOf ATOM is not reachable
// from text: a "RootOf(...)" call parses as an ordinary Func node.
//
// After a complete expression only whitespace may remain.
Expr parseExpr(Ctx &c, const std::string &src);

} // namespace numkit::cas
