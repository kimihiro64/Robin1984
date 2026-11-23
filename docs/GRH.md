# Robin-style criteria for generalized RH

## Corrected divisor-sum criterion

Let $K$ be a number field with discriminant $D_K$ and put
$\kappa_K=\operatorname{Res}_{s=1}\zeta_K(s)$. For a nonzero integral ideal
$\mathfrak a$, define
$\sigma_K(\mathfrak a)=\sum_{\mathfrak d\mid\mathfrak a}N\mathfrak d$, with
the sum over integral ideal divisors and $N$ the absolute norm.

**Fieldwise equivalence.** The nontrivial zeros of $\zeta_K$ lie on
$\Re s=\tfrac12$ if and only if, for sufficiently large $N\mathfrak a$,
$$
\frac{\sigma_K(\mathfrak a)}{N\mathfrak a}
\le e^\gamma\kappa_K\left(
\log\log N\mathfrak a+
\frac{12+3\log|D_K|}{\sqrt{\log N\mathfrak a}}\right).
\tag{1}
$$
The threshold depends on $K$. The family of all $K=\mathbb Q(\zeta_m)$,
$m\ge 1$, gives **Dirichlet GRH**, by the factorization into the primitive
Dirichlet $L$-functions attached to the characters modulo $m$. Every
primitive character occurs at its conductor, and there are no poles in
$0<\Re s<1$ among the factors. Using every number field instead gives
**Dedekind-zeta GRH**.

The Lean file [Robin1984/GRH.lean](../Robin1984/GRH.lean) defines these three
equivalence propositions and proves uniqueness of the Dedekind continuation,
the Dirichlet change-of-level identity, and the cyclotomic reduction under
the stated zeta factorization. For every number field and every
$\Re s>1$, Lean proves the prime-ideal Euler product for Mathlib's
Dedekind zeta, its nonvanishing there, and the absolutely convergent
prime-power series for its negative logarithmic derivative, with the
three-point trigonometric positivity inequality in that half-plane. Lean
proves that an entire pole-cleared continuation with nonzero value at one
cannot vanish on the line of convergence. The natural-index Dirichlet
coefficients have Chebyshev partial sums and give the same logarithmic
derivative. Lean also proves the weighted Mellin transform of the Chebyshev
error, the ideal divisor ratio as a product of finite geometric factors,
and the exact log norm and local Euler factors of the cutoff ideal. The
signed Dedekind tail implication accepts a convergent improper primitive
with the prescribed value at one. The integrated-error and triangular-sum
criteria use their stated transform and tail hypotheses. The fieldwise and
family equivalences below are developed in prose.

### Forward implication

Write $q=N\mathfrak p$ for the norm of a prime ideal, and let
$$
\psi_K(x)=\sum_{q^j\le x}\log q,\qquad
\theta_K(x)=\sum_{q\le x}\log q,\qquad E(x)=\psi_K(x)-x .
$$
All sums over $q$ count each prime ideal separately, including ideals of
equal norm. Set
$$
A(x)=\sum_{q^j\le x}\frac{1}{j q^j},\qquad
H(x)=-\int_x^\infty E(t)\frac{1+\log t}{t^2\log^2t}\,dt .
$$
Partial summation and the number-field Mertens constant give
$$
A(x)=\gamma+\log\kappa_K+\log\log x+\frac{E(x)}{x\log x}+H(x).
\tag{2}
$$
[Garcia and Lee, number-field Mertens theorems](https://arxiv.org/abs/2007.10313)

Use $x=\log N\mathfrak a$ and $b(q)=-\log(1-q^{-1})$. The cost of
including a prime ideal in the support of $\mathfrak a$ is $\log q$.
Its Euler-factor contribution to the logarithm of the divisor ratio is at
most $b(q)$. Since $b(q)/\log q$ decreases with $q>1$, subtracting
$b(x)/\log x$ times the cost makes the surplus nonnegative precisely for
$q\le x$. Summing the surplus over those prime ideals gives
$$
\log\frac{\sigma_K(\mathfrak a)}{N\mathfrak a}
\le \sum_{q\le x} b(q)+ \frac{b(x)}{\log x}
\bigl(x-\theta_K(x)\bigr).
\tag{3}
$$
The tail $\sum_{q\le x}b(q)-A(x)$ is
$(1+o(1))/(\sqrt{x}\log x)$. Its main term is
$\frac12\sum_{\sqrt{x}<q\le x}q^{-2}$ by the prime ideal theorem.
For $q\le x^{1/3}$ the omitted powers contribute $O_K(x^{-2/3})$,
using $q^{\lfloor\log x/\log q\rfloor+1}>x$. The terms with
$q>x^{1/3}$ and exponent at least three have the same bound by partial
summation. Also $\psi_K(x)-\theta_K(x)\sim\sqrt{x}$, from the second
power layer. Using $b(x)=x^{-1}+O(x^{-2})$ in (3) cancels the
$E(x)/(x\log x)$ term of (2) and leaves
$$
\log\frac{\sigma_K(\mathfrak a)}{N\mathfrak a}
\le \gamma+\log\kappa_K+\log\log x+
H(x)+\frac{2+o(1)}{\sqrt{x}\log x}.
\tag{4}
$$

Under RH for $\zeta_K$, integrate the smoothed explicit formula for
$\int_1^x E(t)\,dt$ against the derivative of
$(1+\log t)/(t^2\log^2t)$. Absolute convergence of the integrated zero
sum gives
$$
\sqrt{x}\log x\,H(x)
=\sum_\rho\frac{x^{i\Im\rho}}{\rho(1-\rho)}+o(1).
\tag{5}
$$
Indeed the term in $\int_1^t E(u)\,du$ from $\rho$ is
$-t^{1+\rho}/[\rho(1+\rho)]$. After integration by parts its contribution
is $\rho^{-1}\int_x^\infty t^\rho(1+\log t)/(t^2\log^2t)\,dt$.
For each fixed zero this has the asymptotic in (5), while the
integration-by-parts form is dominated on the normalized scale by
$O(1/|\rho(1+\rho)|)$, a summable bound.
[Grenié and Molteni, smoothed prime ideal theorem](https://sites.unimi.it/molteni/research/papers-pdf/34-molteni-Explicit_smoothed_prime_ideals_theorems_under_GRH.pdf)

For the usual entire completed $\Xi_K$, set
$B_K=\sum_\rho(1/4+(\Im\rho)^2)^{-1}$, with multiplicities. Symmetry
about $1/2$ gives
$$
\frac{\Xi_K'(2)}{\Xi_K(2)}
=\sum_\rho \frac{3/2}{9/4+(\Im\rho)^2}.
$$
The summand in $B_K$ is at most six times the corresponding summand
here. At $2$ the gamma factors and $\zeta_K'/\zeta_K$ contribute
nonpositive terms, so $\Xi_K'/\Xi_K(2)\le 3/2+\frac12\log|D_K|$.
Thus $2+B_K\le11+3\log|D_K|$ in (4). Exponentiating leaves the same
leading coefficient on the $1/\sqrt{x}$ scale in (1), and the
remaining unit of slack gives the eventual inequality.

### Reverse implication

Take the ideal $\mathfrak L_x=\prod_{q^j\le x}\mathfrak p$. Its log norm
is $\psi_K(x)$. Its log divisor ratio differs from $A(x)$ by
$O_K(1/(\sqrt{x}\log x))$. For $k=\lfloor\log x/\log q\rfloor$, the
difference of the two local terms is $O(q^{-k-1})$. For $q\le\sqrt{x}$
use $q^{-k-1}<1/x$ and count prime ideals. For $q>\sqrt{x}$, sum
$O(q^{-2})$ by partial summation.

Apply (1) to $\mathfrak L_x$, take logs, and use
$\log\log\psi_K(x)\le\log\log x+E(x)/(x\log x)$ by concavity for
large $x$. Equation (2) gives $H(x)\le O_K(1/(\sqrt{x}\log x))$.
Writing $w(t)=(1+\log t)/\log^2 t$, integration by parts gives
$$
H_0(x):=-\int_x^\infty E(t)t^{-2}\,dt
=\frac{H(x)}{w(x)}+
\int_x^\infty H(t)(1/w)'(t)\,dt
\le O_K(x^{-1/2}).
$$
Here $(1/w)'\ge 0$, so the comparison uses a one-sided bound throughout.
The classical fixed-field prime ideal theorem with its zero-free-region
error justifies the boundary at infinity. Any fixed exceptional real
zero below 1 is absorbed into that error as $x\to\infty$.

For $\Re s>1$, put $F(s)=-\zeta_K'(s)/(s\zeta_K(s))-1/(s-1)$.
The Mellin transform of $H_0(x)$ against $x^{-s}dx$ on $x\ge1$
is $(F(s)-F(1))/(s-1)$. The apparent singularity at 1 is removable.
The transform of $C_Kx^{-1/2}-H_0(x)$, made nonnegative by ignoring
an initial bounded interval, is therefore meromorphic for $\Re s>1/2$.
A zero in this half-plane would force an abscissa of convergence
$\sigma_c>1/2$. Landau's theorem forces a real singularity at
$\sigma_c$. The only candidate is a real zero $\beta$ of multiplicity
$j$, where the transform has residue $-j/[\beta(1-\beta)]$. It tends
to $-\infty$ from the right, contradicting nonnegativity. The functional
equation excludes the reflected off-line zeros.

The independently verified Alpöge–Claude theorems cover the Riemann zeta
function and Dirichlet L-functions for every modulus and character. The
all-field Dedekind-zeta assertion includes the corresponding Hecke RH for
finite-order characters over every number field by abelian zeta
factorization. The standard automorphic formulation over all number
fields also includes general unitary Hecke characters and the standard
L-functions of higher-rank cuspidal representations.
[Statement and verification record](https://math.mit.edu/~drew/grh/)

## A weighted ideal inequality for Hecke $L$-functions

The supporting-line step has an exact version for Euler products with
nonnegative logarithmic coefficients. Let $Z$ have local logarithms
$\sum_{j\ge1}a_{\mathfrak p,j}/(j q^{js})$, with $a_{\mathfrak p,j}\ge0$,
a pole of order $m>0$ at 1, and leading coefficient
$\kappa_Z=\lim_{s\to1}(s-1)^m Z(s)>0$. Assume the usual functional-equation
symmetry of nontrivial zeros, no other poles in $\Re s>1/2$, and the
same fixed-product prime number theorem and integrated explicit formula
used above, with $mx$ in place of $x$. Define
$$
U_Z(\mathfrak a)=\sum_{\mathfrak p}\sum_{1\le j\le v_{\mathfrak p}(\mathfrak a)}
\frac{a_{\mathfrak p,j}}{j q^j},\qquad
y_Z(\mathfrak a)=\frac1m\sum_{\mathfrak p}
\sum_{1\le j\le v_{\mathfrak p}(\mathfrak a)}a_{\mathfrak p,j}\log q .
$$
Under these hypotheses, RH for $Z$ is equivalent to the existence of a
constant $C_Z$ such that, for all ideals of sufficiently large $y=y_Z(\mathfrak a)$,
$$
\exp U_Z(\mathfrak a)
\le e^{m\gamma}\kappa_Z(\log y)^m
\exp\!\left(\frac{C_Z}{\sqrt y\log y}\right).
\tag{6}
$$

For $x>1$ use $A_Z(x)=\sum_{q^j\le x}a_{\mathfrak p,j}/(j q^j)$ and
$\psi_Z(x)=\sum_{q^j\le x}a_{\mathfrak p,j}\log q$.
Each occupied level of positive cost has payoff per cost
$1/(q^j\log(q^j))$, independent of the coefficient. Subtracting
$1/(y\log y)$ times the cost gives the bound
$$
U_Z(\mathfrak a)\le A_Z(y)+\frac{my-\psi_Z(y)}{y\log y}.
$$
Partial summation gives
$$
A_Z(x)=c_Z+m\log\log x+
\frac{\psi_Z(x)-mx}{x\log x}+H_Z(x),
$$
where $H_Z$ is $H$ with $E(t)=\psi_Z(t)-mt$.
To get $c_Z$, use
$\log Z(1+u)=u\int_1^\infty A_Z(t)t^{-1-u}\,dt$ for real $u>0$.
The transform of $\log\log t$ is $-\log u-\gamma$, and
$\log Z(1+u)=-m\log u+\log\kappa_Z+o(1)$ as $u\downarrow0$.
Thus $c_Z=\log\kappa_Z+m\gamma$.
The supporting-line term cancels the boundary term of $A_Z$.
The integrated explicit formula bounds $H_Z$ under RH.
Conversely, on $\mathfrak L_x$ the payoff is exactly $A_Z(x)$ and
$y_Z=\psi_Z(x)/m$. The same concavity and Landau argument as for (1)
then gives RH. In the Mellin transform replace the main term
$1/(s-1)$ in $F$ by $m/(s-1)$. The zero residues are unchanged.

For a unitary Hecke character $\chi$ over $K$ that is not a pure
imaginary norm power, apply (6) to
$$
Z_\chi(s)=\zeta_K(s)^2L(s,\chi)L(s,\bar\chi).
$$
Its pole order at $1$ is $2$. With $\chi(\mathfrak p)=0$ at the
ramified Euler factors, the log coefficients are
$2+2\Re(\chi(\mathfrak p)^j)\ge0$. The Hecke prime ideal theorems and
explicit formulas for the fixed factors supply the analytic hypotheses of
(6). Its GRH assertion includes RH for $\zeta_K$ as well as for the
character pair. Pure norm powers vertically translate $\zeta_K$ and
are handled by its own criterion. For $Z=\zeta_K$ itself,
$y_Z=\log N\mathfrak a$, and (6) is the truncated log-Euler version of
the ideal divisor criterion.

For a unitary cuspidal representation $\pi$ on $\mathrm{GL}_n$, if
its finite local parameters have modulus at most one, the same device
uses $Z=\zeta_K^{2n}L(s,\pi)L(s,\tilde\pi)$, excluding pure norm powers
as above. The local log coefficients are then nonnegative, so (6)
applies with the indicated analytic hypotheses. The local bound is the
temperedness input. Another possibility is the self Rankin–Selberg
product for $1\boxplus\pi$. Its log coefficients at unramified primes
are $\left|1+\sum_i\alpha_i(\mathfrak p)^j\right|^2$. That product
contains $L(s,\pi\times\tilde\pi)$, whose zero statement would also be
part of the resulting test. Standard automorphic GRH by itself supplies
no general tensor-product transfer for that factor.
[Soundararajan and Thorner, with an appendix by Brumley](https://arxiv.org/abs/1804.03654)

## A one-sided prime-power criterion for grand RH

One can keep a one-sided inequality for standard automorphic
$L$-functions without the local positivity assumption by testing a
smoothed prime-power sum instead of optimizing over ideals.
For a normalized unitary cuspidal $L(s,\pi)$ over a number field $K$,
use $Z=L(s,\pi)L(s,\tilde\pi)$. For a pure imaginary norm power, use
$Z=\zeta_K$, since a vertical translation preserves the zero condition.
Let $m$ be the pole order at 1, so $m=0$ for the cuspidal pair and
$m=1$ for $\zeta_K$. Write
$-Z'/Z(s)=\sum_{\mathfrak p,j}b_{\mathfrak p,j}(N\mathfrak p)^{-js}$;
the coefficients are real by conjugation. Put
$$
R_Z(x)=\frac{mx}{2}-
\sum_{(N\mathfrak p)^j\le x} b_{\mathfrak p,j}
\left(1-\frac{(N\mathfrak p)^j}{x}\right).
$$
Then the one-sided criterion is
$$
\exists C_Z\ \forall x\text{ sufficiently large},\qquad
R_Z(x)\le C_Z\sqrt{x}.
\tag{7}
$$

For the forward direction use Perron's kernel $1/[s(s+1)]$. The
functional equation and the usual local archimedean bounds for unitary
cuspidal $L$-functions place the trivial zeros strictly to the left of
$1/2$. Under RH, shifting to a fixed line between them and $1/2$
leaves the zero sum
$\sum_\rho x^\rho/[\rho(\rho+1)]$ in $R_Z$, besides a lower-order
error. This sum is $O_Z(\sqrt{x})$ by the zero count. For the converse,
the Mellin transform of $R_Z$ against $x^{-s-1}dx$ on $x\ge1$ is
$$
\frac{m}{2(s-1)}+\frac{Z'(s)}{s(s+1)Z(s)} .
$$
Again the apparent pole at 1 cancels. A real zero $\beta>1/2$ of
multiplicity $j$ has residue $j/[\beta(\beta+1)]$ here, hence a
negative residue for the transform of $C_Z\sqrt{x}-R_Z(x)$. The same
Landau argument proves there are no zeros to the right of $1/2$,
including nonreal zeros, and the functional equations give the other
half. The conjugate pair detects the zeros of both factors, which have
no poles in the open strip.

Quantifying (7) over all number fields and all normalized unitary
cuspidal standard $L$-functions gives standard automorphic GRH.
Restricting to Dedekind zeta or Dirichlet factors gives the two lower
zero statements. Equation (7) is a prime-power criterion. Equations (1)
and (6) are ideal inequalities; (6) requires the positive coefficients
used in its supporting-line proof.
[Lagarias, Li coefficients and automorphic zero criteria](https://www.numdam.org/articles/10.5802/aif.2311/)
