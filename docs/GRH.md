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
The threshold depends on $K$. **Dirichlet GRH** asserts that every zero in
$0<\Re s<1$ of every Dirichlet $L$-function, over all positive moduli and
all characters, has real part $1/2$. This is equivalent to (1) for every
cyclotomic field $K=\mathbb Q(\zeta_m)$. The proof uses the factorization
into primitive Dirichlet factors and the nonvanishing of the finite
Euler factors that arise for imprimitive characters. **Dedekind ERH**
asserts the critical-line property for the Dedekind zeta function of
every number field and is equivalent to (1) for every number field.

The statements appear in the Mathlib-only [Challenge](../Challenge.lean)
and the proofs appear in [Solution](../Solution.lean). The fieldwise proof
combines the Dedekind forward and reverse implications. The Dirichlet
proof also establishes the cyclotomic factorization by matching the
logarithmic series coefficients, normalizing along the positive real
axis, and applying uniqueness of analytic continuation.

### Forward implication

Write $q=N\mathfrak p$ for the absolute norm of a prime ideal. All
prime-power sums count each eligible prime ideal separately. Set
$$
\psi_K(x)=\sum_{q^j\le x}\log q,\qquad E(x)=\psi_K(x)-x,\qquad
A(x)=\sum_{q^j\le x}\frac{1}{j q^j},\qquad
H(x)=-\int_x^\infty E(t)\frac{1+\log t}{t^2\log^2t}\,dt .
$$
Partial summation and the number-field Mertens constant give
$$
A(x)=\gamma+\log\kappa_K+\log\log x+\frac{E(x)}{x\log x}+H(x).
\tag{2}
$$
[Garcia and Lee, number-field Mertens theorems](https://arxiv.org/abs/2007.10313)

For $k\ge 0$, a local divisor factor satisfies
$\log\sum_{j=0}^k q^{-j}\le\sum_{j=1}^k1/(jq^j)$.
For $k\ge1$, the omitted logarithmic series tail is at most $q^{-k-1}$
and $\log(1-q^{-k-1})\le-q^{-k-1}$.
Each prime power in the divisor ratio has cost $\log q$ and contribution
$1/(j q^j)$, with a decreasing contribution-to-cost ratio as $q^j$
increases. At $x=\log N\mathfrak a$, subtract the ratio at $x$ times
the cost and sum the nonnegative surplus over $q^j\le x$. This gives
$$
\log\frac{\sigma_K(\mathfrak a)}{N\mathfrak a}
\le A(x)+\frac{x-\psi_K(x)}{x\log x}
=\gamma+\log\kappa_K+\log\log x+H(x).
\tag{3}
$$

Let $T(x)=\int_x^\infty E(t)t^{-2}\,dt$ as an improper integral.
For $F_K(s)=(s-1)\zeta_K(s)$ write
$\Phi(s)=(F_K'(s)/F_K(s)+1)/s$. The Mellin transform of $-T$ against
$x^{-s}dx$ on $x>1$ equals $(\Phi(s)-\Phi(1))/(1-s)$ for $\Re s>1$.
The logarithmic derivative of the entire completion $\Xi_K$, together
with the two digamma series, expands the divided difference into the
origin terms and the poles of the completed zero and Gamma series.
Mellin uniqueness gives the formula for $-xT(x)$ almost everywhere, with
completed-zero terms $x^\rho/(\rho(1-\rho))$ and an $O_K(1+\log x)$ remainder. The Gamma
series in the remainder use the negative lattices $-2n$ and $-n$ for
$n\ge1$, with the corresponding real and complex place multiplicities.

Under Dedekind RH, each completed-zero term has absolute value
$\sqrt{x}/(1/4+(\Im\rho)^2)$. Put
$B_K=\sum_\rho(1/4+(\Im\rho)^2)^{-1}$, counting zeros with multiplicity.
Subtracting the completed logarithmic derivatives at $2$ and $-1$
and using the functional equation gives
$$
B_K\le 6\Re\frac{\Xi_K'(2)}{\Xi_K(2)}\le 9+3\log|D_K|.
\tag{4}
$$
The second estimate uses nonpositive Gamma terms and the nonpositive
logarithmic derivative of $\zeta_K$ at $2$. Consequently
$|T(x)|\le (B_K+1)/\sqrt{x}$ almost everywhere beyond a cutoff.
Continuity of $T$ extends the bound to every sufficiently large $x$.
Integration by parts in $H$
then gives the explicit upper estimate
$$
H(x)\le \frac{B_K+1}{\sqrt{x}\log x}
       +\frac{7(B_K+1)}{\sqrt{x}\log^2x}
\tag{5}
$$
for sufficiently large $x$. The leading coefficient $B_K+1$ is strictly
below $12+3\log|D_K|$, which gives (1) after exponentiation.

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

Let $F(s)=(s-1)^mZ(s)$ be the pole-cleared uncompleted function. The
Mellin transform against $x^{-s-1}\,dx$ on $x>1$ is
$$
\int_1^\infty R_Z(x)x^{-s-1}\,dx
=\frac{m}{2(s-1)}+\frac{Z'(s)}{s(s+1)Z(s)}
=\frac{F'(s)/F(s)+m(s+2)/2}{s(s+1)}
\qquad (\operatorname{Re}s>1).
$$
The cancellation at $s=1$ leaves the logarithmic derivative of $F$.
The eventual upper bound in (7), by Landau's theorem, gives nonvanishing
of $F$ for $\operatorname{Re}s>1/2$.

For the forward direction, use the genus-one zero expansion of $F$.
Write $b$ for its constant logarithmic-derivative term and $m_0,m_{-1}$
for the multiplicities at $0,-1$. Matching the Mellin transforms gives the following identity for almost every $x>1$.
$$
R_Z(x)=\operatorname{Re}\left[
 b(1-x^{-1})+m(1-\tfrac12x^{-1})
 +m_0(\log x-1+x^{-1})-m_{-1}x^{-1}\log x
 +\sum_{\substack{\rho:\,F(\rho)=0\\\rho\notin\{0,-1\}}}
  \frac{x^\rho-x^{-1}}{\rho(\rho+1)}
 \right].
$$
The sum counts multiplicities. Under right-half-plane nonvanishing, every
zero in the sum satisfies $\operatorname{Re}\rho\le1/2$. The
summability of $1/|\rho(\rho+1)|$ and the elementary terms give an
almost-everywhere square-root bound. Continuity of $R_Z$ gives (7)
pointwise.

The completed zero condition concerns the pole-cleared completed
standard $L$-functions. On $\operatorname{Re}s>1/2$, the nonvanishing
completion factors transfer nonvanishing between the completed pair and
$F$. The completed functional equation transfers a zero at $s$ to
a zero of the dual at $1-s$. This argument allows trivial
zeros of the uncompleted function with real part below $1/2$.
[Lagarias, §6](https://aif.centre-mersenne.org/item/10.5802/aif.2311.pdf)

Lean proves the completed-zero formulation as `grandRobinCompletedCriterion`
under the paired Euler and Hadamard data and the completed functional
equations. The release Challenge still gives its earlier analytic-data
statement. The instantiation for standard automorphic $L$-functions of
every rank over every number field remains to be formalized.
For the trivial Hecke character of a field $K$, use $Z=\zeta_K$ and
$m=1$. Its logarithmic Euler coefficient at $(N\mathfrak p)^j$ is
$\log N\mathfrak p$. Thus, for $x\ge1$,
$$
R_{\zeta_K}(x)
=\frac{x}{2}-\frac1x\int_1^x\psi_K(t)\,dt
=\frac1{2x}-\frac1x\int_1^x(\psi_K(t)-t)\,dt .
$$
The first equality integrates the indicator of $t\ge (N\mathfrak p)^j$
over $[1,x]$ in the finite prime-power sum. The triangular and corrected
ideal criteria both test Dedekind RH in this specialization. The ideal
criterion uses the Mertens sum built from the same prime powers, with
weights $1/[j(N\mathfrak p)^j]$ and a comparison of positive divisor
products. Over the cyclotomic fields the shared Dedekind zero condition
gives Dirichlet GRH. The triangular sum also accepts signed coefficients,
which allows the higher-rank standard automorphic specialization.
[Lagarias, Li coefficients and automorphic zero criteria](https://www.numdam.org/articles/10.5802/aif.2311/)
