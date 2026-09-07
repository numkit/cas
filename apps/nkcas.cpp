// apps/nkcas.cpp — standalone CLI over the numkit-cas core.
//
//   nkcas integrate "1/(x^3+2)" x
//   nkcas diff "x^2*sin(x)" x
//   nkcas print "1/2*x + 0.25"
//   nkcas            (reads "<command> <expr> <var>" lines from stdin)
//
// Exit codes: 0 success (proved / printed), 1 usage or parse error,
// 2 honest Unevaluated — corpus runs can count the difference.
#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/integrate/ratint.hpp>

#include <iostream>
#include <string>
#include <vector>

namespace {

bool isSpace(char ch)
{
    return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

std::string trim(const std::string &s)
{
    std::size_t a = 0, b = s.size();
    while (a < b && isSpace(s[a]))
        ++a;
    while (b > a && isSpace(s[b - 1]))
        --b;
    return s.substr(a, b - a);
}

// Split "<command> <expr...> <var>" / "<command> <expr>": the variable
// is the last whitespace-separated token, the expression everything
// between (so expressions may contain spaces).
bool splitLine(const std::string &line, std::string &cmd,
               std::string &exprSrc, std::string &var)
{
    std::vector<std::string> words;
    std::size_t i = 0;
    while (i < line.size()) {
        while (i < line.size() && isSpace(line[i]))
            ++i;
        std::size_t start = i;
        while (i < line.size() && !isSpace(line[i]))
            ++i;
        if (i > start)
            words.push_back(line.substr(start, i - start));
    }
    if (words.empty())
        return false;
    cmd = words.front();
    if (cmd == "print") {
        exprSrc = trim(line.substr(cmd.size()));
        return !exprSrc.empty();
    }
    if (words.size() < 3)
        return false;
    var = words.back();
    const std::size_t varOff = line.rfind(var);
    exprSrc = trim(line.substr(cmd.size(), varOff - cmd.size()));
    return !exprSrc.empty();
}

int runCommand(const std::string &cmd, const std::string &exprSrc,
               const std::string &varName)
{
    numkit::cas::Ctx ctx;
    numkit::cas::Expr f;
    try {
        f = numkit::cas::parseExpr(ctx, exprSrc);
    } catch (const numkit::cas::ParseError &e) {
        std::cout << "parse error at offset " << e.pos() << ": " << e.what()
                  << "\n";
        return 1;
    }
    if (cmd == "print") {
        std::cout << ctx.toString(f) << "\n";
        return 0;
    }
    const numkit::cas::Expr var = ctx.symbol(varName);
    if (cmd == "diff") {
        std::cout << ctx.toString(ctx.diff(f, var)) << "\n";
        return 0;
    }
    if (cmd == "integrate") {
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(ctx, f, var);
        if (r.proved()) {
            std::cout << ctx.toString(r.F) << "\n";
            std::cout << "[certificate: PROVED_SYMBOLIC]\n";
            return 0;
        }
        std::cout << "Unevaluated: " << r.reason << "\n";
        return 2;
    }
    std::cout << "unknown command '" << cmd << "' (integrate, diff, print)\n";
    return 1;
}

void usage()
{
    std::cout << "usage: nkcas <command> <expr> <var>\n"
                 "  commands: integrate, diff; print takes no var\n"
                 "  or no arguments: read '<command> <expr> <var>' lines "
                 "from stdin\n";
}

} // namespace

int main(int argc, char **argv)
{
    if (argc == 4)
        return runCommand(argv[1], argv[2], argv[3]);
    if (argc == 3 && std::string(argv[1]) == "print")
        return runCommand(argv[1], argv[2], "");
    if (argc == 1) {
        std::string line;
        while (std::getline(std::cin, line)) {
            const std::string t = trim(line);
            if (t.empty())
                continue;
            if (t == "quit" || t == "exit")
                break;
            std::string cmd, exprSrc, var;
            if (!splitLine(t, cmd, exprSrc, var)) {
                std::cout << "malformed line (want: <command> <expr> <var>)\n";
                continue;
            }
            runCommand(cmd, exprSrc, var);
        }
        return 0;
    }
    usage();
    return 1;
}
