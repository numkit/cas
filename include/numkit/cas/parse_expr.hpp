// include/numkit/cas/parse_expr.hpp — throwing parseExpr adapter over keel::cas::tryParseExpr.
#pragma once

#include <keel/cas/core/parser.hpp>
#include <keel/core.h>
#include <keel/exception.h>
#include <keel/string.h>

namespace numkit::cas {

class ParseError : public keel::Exception {
public:
    ParseError(keel::usize pos, keel::StringRef msg)
        : keel::Exception(msg, keel::Error{keel::ErrorCode::InvalidData, 0}), pos_(pos)
    {
    }
    keel::usize pos() const { return pos_; }

private:
    keel::usize pos_;
};

inline keel::cas::Expr parseExpr(keel::cas::Ctx &c, keel::StringRef src)
{
    keel::cas::Expr out;
    keel::cas::ParseErrorInfo err;
    if (!keel::cas::tryParseExpr(c, src, out, &err)) {
        throw ParseError(err.pos, err.message.as_ref());
    }
    return out;
}

} // namespace numkit::cas
