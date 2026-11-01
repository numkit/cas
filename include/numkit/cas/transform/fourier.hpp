// transform/fourier.hpp — symbolic bilateral Fourier and inverse Fourier transforms.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <string>

namespace numkit::cas {

struct FourierResult
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    Expr F;             // transformed expression in `w` (fourier) or `t` (ifourier)
    std::string reason; // populated on Unevaluated

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Forward bilateral angular-frequency Fourier transform:
//   F{f(t)}(w) = int_{-inf}^{+inf} f(t) * exp(-I * w * t) dt
//              = int_{-inf}^{+inf} f(t) * cos(w * t) dt
//                - I * int_{-inf}^{+inf} f(t) * sin(w * t) dt.
// Supports linearity, Dirac delta impulses and shifts, constants and pure
// sinusoids, two-sided decaying exponentials exp(-a*abs(t)), causal exponentials
// exp(-a*t)*heaviside(t), Gaussians and Hermite-Gaussian wavepackets
// t^n*exp(-a*t^2), hyperbolic secant/cosecant kernels sech(a*t) and t*csch(a*t),
// sinc kernels sin(a*t)/t, and rational functions R(t) via upper-half-plane
// contour residues.
FourierResult fourier(Ctx &c, Expr f, Expr t, Expr w,
                      Budget *budget = nullptr);

// Inverse bilateral angular-frequency Fourier transform:
//   F^{-1}{F(w)}(t) = (1 / (2*pi)) * int_{-inf}^{+inf} F(w) * exp(I * w * t) dw,
// using Fourier duality and real/imaginary Hermitian decomposition, certified
// by round-trip verification F{f(t)}(w) == F(w).
FourierResult ifourier(Ctx &c, Expr F, Expr w, Expr t,
                       Budget *budget = nullptr);

} // namespace numkit::cas
