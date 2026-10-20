
Int[Sinh[c_. + d_.*x_], x_Symbol] :=
  Cosh[c + d*x]/d /;
FreeQ[{c, d}, x]

Int[Cosh[c_. + d_.*x_], x_Symbol] :=
  Sinh[c + d*x]/d /;
FreeQ[{c, d}, x]

Int[Tanh[c_. + d_.*x_], x_Symbol] :=
  Log[Cosh[c + d*x]]/d /;
FreeQ[{c, d}, x]

Int[Coth[c_. + d_.*x_], x_Symbol] :=
  Log[Sinh[c + d*x]]/d /;
FreeQ[{c, d}, x]

Int[Sech[c_. + d_.*x_], x_Symbol] :=
  ArcTan[Sinh[c + d*x]]/d /;
FreeQ[{c, d}, x]

Int[Csch[c_. + d_.*x_], x_Symbol] :=
  -ArcTanh[Cosh[c + d*x]]/d /;
FreeQ[{c, d}, x]

Int[Sech[c_. + d_.*x_]^2, x_Symbol] :=
  Tanh[c + d*x]/d /;
FreeQ[{c, d}, x]

Int[Csch[c_. + d_.*x_]^2, x_Symbol] :=
  -Coth[c + d*x]/d /;
FreeQ[{c, d}, x]

Int[Tanh[c_. + d_.*x_]^2, x_Symbol] :=
  x - Tanh[c + d*x]/d /;
FreeQ[{c, d}, x]

Int[Coth[c_. + d_.*x_]^2, x_Symbol] :=
  x - Coth[c + d*x]/d /;
FreeQ[{c, d}, x]

Int[Sinh[c_. + d_.*x_]^2, x_Symbol] :=
  -x/2 + Sinh[c + d*x]*Cosh[c + d*x]/(2*d) /;
FreeQ[{c, d}, x]

Int[Cosh[c_. + d_.*x_]^2, x_Symbol] :=
  x/2 + Sinh[c + d*x]*Cosh[c + d*x]/(2*d) /;
FreeQ[{c, d}, x]

Int[Sinh[c_. + d_.*x_]^n_, x_Symbol] :=
  Cosh[c + d*x]*Sinh[c + d*x]^(n - 1)/(d*n) - (n - 1)/n*Int[Sinh[c + d*x]^(n - 2), x] /;
FreeQ[{c, d}, x] && GtQ[n, 2] && IntegerQ[n]

Int[Cosh[c_. + d_.*x_]^n_, x_Symbol] :=
  Sinh[c + d*x]*Cosh[c + d*x]^(n - 1)/(d*n) + (n - 1)/n*Int[Cosh[c + d*x]^(n - 2), x] /;
FreeQ[{c, d}, x] && GtQ[n, 2] && IntegerQ[n]

Int[Tanh[c_. + d_.*x_]^n_, x_Symbol] :=
  -Tanh[c + d*x]^(n - 1)/(d*(n - 1)) + Int[Tanh[c + d*x]^(n - 2), x] /;
FreeQ[{c, d}, x] && GtQ[n, 2] && IntegerQ[n]

Int[Coth[c_. + d_.*x_]^n_, x_Symbol] :=
  -Coth[c + d*x]^(n - 1)/(d*(n - 1)) + Int[Coth[c + d*x]^(n - 2), x] /;
FreeQ[{c, d}, x] && GtQ[n, 2] && IntegerQ[n]

Int[Sech[c_. + d_.*x_]^n_, x_Symbol] :=
  Sinh[c + d*x]*Sech[c + d*x]^(n - 1)/(d*(n - 1)) + (n - 2)/(n - 1)*Int[Sech[c + d*x]^(n - 2), x] /;
FreeQ[{c, d}, x] && GtQ[n, 2] && IntegerQ[n]

Int[(g_.*Cosh[c_. + d_.*x_])*(a_. + b_.*Sinh[c_. + d_.*x_])^m_., x_Symbol] :=
  g*(a + b*Sinh[c + d*x])^(m + 1)/(b*d*(m + 1)) /;
FreeQ[{a, b, c, d, g, m}, x] && NeQ[m, -1]

Int[(g_.*Cosh[c_. + d_.*x_])/(a_. + b_.*Sinh[c_. + d_.*x_]), x_Symbol] :=
  g*Log[a + b*Sinh[c + d*x]]/(b*d) /;
FreeQ[{a, b, c, d, g}, x]

Int[(g_.*Sinh[c_. + d_.*x_])*(a_. + b_.*Cosh[c_. + d_.*x_])^m_., x_Symbol] :=
  g*(a + b*Cosh[c + d*x])^(m + 1)/(b*d*(m + 1)) /;
FreeQ[{a, b, c, d, g, m}, x] && NeQ[m, -1]

Int[(g_.*Sinh[c_. + d_.*x_])/(a_. + b_.*Cosh[c_. + d_.*x_]), x_Symbol] :=
  g*Log[a + b*Cosh[c + d*x]]/(b*d) /;
FreeQ[{a, b, c, d, g}, x]

Int[(c_. + d_.*x_)^m_.*Sinh[e_. + f_.*x_], x_Symbol] :=
  (c + d*x)^m*Cosh[e + f*x]/f - d*m/f*Int[(c + d*x)^(m - 1)*Cosh[e + f*x], x] /;
FreeQ[{c, d, e, f}, x] && GtQ[m, 0]

Int[(c_. + d_.*x_)^m_.*Cosh[e_. + f_.*x_], x_Symbol] :=
  (c + d*x)^m*Sinh[e + f*x]/f - d*m/f*Int[(c + d*x)^(m - 1)*Sinh[e + f*x], x] /;
FreeQ[{c, d, e, f}, x] && GtQ[m, 0]
