
Int[(F_^(c_.*(a_. + b_.*x_)))*Sinh[d_. + e_.*x_], x_Symbol] :=
  F^(c*(a + b*x))*(b*c*Log[F]*Sinh[d + e*x] - e*Cosh[d + e*x])/(b^2*c^2*Log[F]^2 - e^2) /;
FreeQ[{F, a, b, c, d, e}, x] && NeQ[b^2*c^2*Log[F]^2 - e^2, 0]

Int[(F_^(c_.*(a_. + b_.*x_)))*Cosh[d_. + e_.*x_], x_Symbol] :=
  F^(c*(a + b*x))*(b*c*Log[F]*Cosh[d + e*x] - e*Sinh[d + e*x])/(b^2*c^2*Log[F]^2 - e^2) /;
FreeQ[{F, a, b, c, d, e}, x] && NeQ[b^2*c^2*Log[F]^2 - e^2, 0]
