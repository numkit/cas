// poly/solve.cpp — exact real-root solving over the Sturm machinery.
#include <numkit/cas/poly/solve.hpp>

#include <numkit/cas/poly/zassenhaus.hpp>

#include <algorithm>
#include <cassert>

namespace numkit::cas {

std::vector<RealRootSolution> solveRealRoots(const UPoly &p)
{
    assert(!p.isZero() && "solveRealRoots of the zero polynomial");
    std::vector<RealRootSolution> out;
    if (p.deg() < 1)
        return out; // non-zero constant: no roots

    UPoly sq = p.squarefreePart();
    sq.makeMonic();
    const std::vector<RootInterval> ivs = isolateRealRoots(sq); // ascending

    // Exact rational roots through the full factorization: a root r
    // of the linear factors of the squarefree part. The interval
    // bracket identifies which isolated root it is.
    std::vector<Rational> rationals;
    for (const UPoly &f : factorOverQ(sq))
        if (f.deg() == 1)
            rationals.push_back(f.coeff(0) * Rational(std::int64_t{-1}));
    std::sort(rationals.begin(), rationals.end());

    out.reserve(ivs.size());
    std::size_t nextRational = 0;
    for (std::size_t k = 0; k < ivs.size(); ++k) {
        RealRootSolution s;
        s.carrier = sq;
        s.realIndex = static_cast<int>(k);
        s.interval = ivs[k];
        // Matching rules against boundary ambiguity: a rational root
        // sitting ON a bracket boundary belongs to ITS OWN exact
        // interval (r, r], never to the neighbour whose hi (or lo)
        // merely touches it. Exact brackets match by value; a
        // non-exact bracket only matches a rational STRICTLY inside,
        // and then the bracket sharpens to the exact point.
        bool matched = false;
        if (nextRational < rationals.size()) {
            const Rational &r = rationals[nextRational];
            if (ivs[k].exact()) {
                matched = r == ivs[k].hi;
            } else if (r > ivs[k].lo && r < ivs[k].hi) {
                matched = true;
                s.interval = RootInterval{r, r}; // sharpen
            }
        }
        if (matched) {
            s.isRational = true;
            s.value = rationals[nextRational];
            assert(sq.eval(s.value).isZero() &&
                   "matched rational is not a root");
            ++nextRational;
        } else {
            assert(!ivs[k].exact() &&
                   "exact interval without a rational root: inconsistent");
        }
        out.push_back(std::move(s));
    }
    assert(nextRational == rationals.size() &&
           "unmatched rational root: isolation inconsistent");
    return out;
}

} // namespace numkit::cas
