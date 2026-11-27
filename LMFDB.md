# Critical-line criteria by LMFDB identifier

The explorer tracks
location and multiplicity separately. Each entry identifies the actual
\(L\)-function, its arithmetic input at every place, the analytic provider,
and any missing proof. A proof of an equivalence and a proof that its
arithmetic inequality holds are different milestones. The catalogue and this research record live in the existing Robin1984 checkout. See [the explorer](lmfdb-explorer/index.html) and its [catalogue data](lmfdb-explorer/catalog.json).

## Robin1984 corrected ideal criterion

For a number field \(K\) of discriminant \(D_K\), let
\(\kappa_K=\operatorname{Res}_{s=1}\zeta_K(s)\),
\(\sigma_K(\mathfrak a)=\sum_{\mathfrak b\mid\mathfrak a} N\mathfrak b\),
and let \(\gamma\) be Euler's constant. The divisor sum ranges over integral
ideal divisors and \(N\) denotes absolute ideal norm.

**Fieldwise theorem.** For each number field \(K\), Dedekind RH for \(K\)
is equivalent to **\(\operatorname{CorrectedIdealRobin}(K)\)**, the assertion
that there exists \(A_K\in\mathbb N\) such that every nonzero integral ideal
\(\mathfrak a\subseteq\mathcal O_K\) with \(N\mathfrak a\ge A_K\) satisfies
\[
\frac{\sigma_K(\mathfrak a)}{N\mathfrak a}
\le e^\gamma\kappa_K\left(\log\log N\mathfrak a+
  \frac{12+3\log|D_K|}{\sqrt{\log N\mathfrak a}}\right).
\]
Dedekind RH here concerns the zeros of \(\zeta_K\) in the open critical
strip \(0<\Re s<1\). The cutoff depends on the field.

- **Dirichlet GRH** is equivalent to this criterion for every cyclotomic
  field \(\mathbb Q(\zeta_m)\), \(m\ge1\), with each field's own cutoff.
- **Dedekind ERH** is equivalent to this criterion for every number field,
  with each field's own cutoff.

The definition is `Robin1984.GRH.CorrectedIdealRobin` in
[GRH.lean](../Robin1984/GRH.lean#L37). The fieldwise and global proofs are
in [Solution.lean](../Solution.lean). The catalogue specializes the
proofs to these LMFDB records.

| Field | LMFDB entries represented | Exact scope of the field's inequality |
| --- | --- | --- |
| \(\mathbb Q\), \(D_K=1\) | `1-1-1.1-r0-0-0` | Ordinary RH. The ideal is \(n\mathbb Z\), \(\kappa_{\mathbb Q}=1\), and the criterion becomes \(\sigma(n)/n\le e^\gamma(\log\log n+12/\sqrt{\log n})\) for every positive integer \(n\ge A_{\mathbb Q}\). |
| \(\mathbb Q(i)\), \(D_K=-4\) | `1-2e2-4.3-r1-0-0` | Ordinary RH and Dirichlet beta RH jointly, since \(\zeta_K=\zeta L(s,\chi_4)\). Under ordinary RH this is equivalent to beta RH alone. Here \(\kappa_K=\pi/4\). |
| \(\mathbb Q(\sqrt{-3})\), \(D_K=-3\) | `1-3-3.2-r1-0-0` | Ordinary RH and RH for character `3.2` jointly. The residue is \(\pi/(3\sqrt3)\). |
| \(\mathbb Q(\sqrt5)\), \(D_K=5\) | `1-5-5.4-r0-0-0` | Ordinary RH and RH for character `5.4` jointly. The residue is \(2\log((1+\sqrt5)/2)/\sqrt5\). |
| \(\mathbb Q(\sqrt{-7})\), \(D_K=-7\) | `1-7-7.6-r1-0-0` | Ordinary RH and RH for character `7.6` jointly. The residue is \(\pi/\sqrt7\). |
| \(\mathbb Q(\zeta_5)\), \(D_K=125\) | `1-5-5.2-r1-0-0` and `1-5-5.3-r1-0-0` | Dedekind RH for \(\mathbb Q(\sqrt5)\) and RH for the two quartic characters jointly, by \(\zeta_K=\zeta_{\mathbb Q(\sqrt5)}L(s,\chi_{5.2})L(s,\chi_{5.3})\). Over the quadratic field hypothesis either quartic RH is equivalent to the criterion, since the quartic characters are conjugate. |
| \(K^+=\mathbb Q(\zeta_7)^+\), \(D_{K^+}=49\) | `1-7-7.2-r0-0-0` and `1-7-7.4-r0-0-0` | Ordinary RH and RH for the order-three pair jointly. Under ordinary RH, either member's RH is equivalent to the criterion for \(K^+\). |
| \(K=\mathbb Q(\zeta_7)\), \(D_K=-16807\) | `1-7-7.3-r1-0-0` and `1-7-7.5-r1-0-0` | Ordinary RH and RH for all five primitive characters modulo \(7\) jointly. Assuming Dedekind RH for \(K^+\) and RH for character `7.6`, either order-six member's RH is equivalent to the criterion for \(K\). |
| \(\mathbb Q(\sqrt{-2})\), \(D_K=-8\) | `1-2e3-8.3-r1-0-0` | Ordinary RH and RH for character `8.3` jointly. The residue is \(\pi/\sqrt8\). |
| \(\mathbb Q(\sqrt2)\), \(D_K=8\) | `1-2e3-8.5-r0-0-0` | Ordinary RH and RH for character `8.5` jointly. The residue is \(2\log(1+\sqrt2)/\sqrt8\). |
| \(\mathbb Q(\sqrt{-11})\), \(D_K=-11\) | `1-11-11.10-r1-0-0` | Ordinary RH and RH for character `11.10` jointly. The residue is \(\pi/\sqrt{11}\). |
| \(K^+=\mathbb Q(\zeta_9)^+\), \(D_{K^+}=81\) | `1-3e2-9.4-r0-0-0` and `1-3e2-9.7-r0-0-0` | Ordinary RH and RH for both order-three characters jointly. |
| \(K=\mathbb Q(\zeta_9)\), \(D_K=-19683\) | `1-3e2-9.2-r1-0-0` and `1-3e2-9.5-r1-0-0` | Dedekind RH for \(K^+\), RH for `3.2`, and RH for both order-six characters jointly. |
| \(\mathbb Q[T]/(T^3-T-1)\), \(D_K=-23\) | `3.1.23.1` and `2-23-23.22-c0-0-0` | Ordinary RH and RH for the level-23 weight-one form jointly, by \(\zeta_K=\zeta L(s,f_{23})\). Under ordinary RH the criterion is equivalent to RH for \(f_{23}\) alone. |

Every factor in these product identities is holomorphic in the open
critical strip. An off-line zero of a factor therefore gives an off-line
zero of the product. The field identities and their LMFDB identifications
are prose specializations of the Lean theorem. For the other reviewed
labels the notes below give arithmetic criteria based on primes, point
counts, or signed Frobenius traces. A corrected ideal-divisor transfer
for those labels would require a proved identification or factorization
with an appropriate Dedekind zeta function and precise hypotheses
isolating the relevant zeros.

## Arithmetic statements for the reviewed labels

The classical benchmark is ordinary RH, equivalent to Robin's
\(\sigma(n)<e^\gamma n\log\log n\) for every integer \(n\ge5041\), to
Lagarias's \(\sigma(n)\le H_n+e^{H_n}\log H_n\) for every \(n\ge1\), and
to Nicolas's \(P_k/\varphi(P_k)>e^\gamma\log\log P_k\) for each primorial
\(P_k\), \(k\ge2\).

[Robin1984 statements](https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean) ·
[Lagarias](https://websites.umich.edu/lagarias/doc/elementaryrh.pdf) ·
[Nicolas](https://www.sciencedirect.com/science/article/pii/0022314X83900550)

### Removing the triangular weight

Write \(F\) for the individual \(L\)-function or product being tested
and \(m\) for its pole order at 1. Define \(B(x)=\sum_{n\le x} b_n\)
from \(-F'/F=\sum b_n n^{-s}\), adding the coefficients at equal
prime-ideal norms when necessary. For the reviewed entries,
\(|b_n|\ll_F\log n\). For the number fields, use the sum of residue
degrees over a rational prime, bounded by the field degree. For the
other entries the unitary local roots have absolute value at most 1,
including the ramified factors. The meromorphic Artin entry uses the
completed divisor with signed orders.

Set
\[
P(x)=\sum_{n\le x}b_n(x-n)=\frac{mx^2}{2}-xR_F(x).
\]
In the triangular explicit formula the pole at 1 contributes
\(mx^2/2\) to \(P(x)\). A zero \(w\) of completed order \(d_w\)
contributes \(-d_w x^{w+1}/[w(w+1)]\), up to affine terms from
regularizing the Mellin inversion. For the Artin entry take the finite
signed sum of the Hecke formulas from Brauer induction, collecting the
orders before bounding. The standard local zero count is
\(\sum_{T\le|\Im w|<T+1}|d_w|\ll_F\log(2+T)\). In the Artin case
it is bounded by the sum of the local counts for the Hecke factors.
The gamma terms have \(w=-\mu-2k\) for shifts \(\Re\mu>-1/2\). In
the unit difference of \(P\), the finitely many such \(w\) with
\(\Re w>-1\) contribute \(O_F(\sqrt x+\log x)\); the rest sum
geometrically for \(x\ge2\). The exceptional terms at \(w=0,-1\)
have logarithms in the inversion and contribute \(O_F(\log(2x))\)
in the unit difference. The affine terms contribute \(O_F(1)\).

Suppose all the completed zeros under test, and the signed poles
for the Artin case, lie on \(\Re w=1/2\). Split \(P(x+1)-P(x)\)
at \(|\Im w|=x\). For the lower group,
\[
\left|\frac{(x+1)^{w+1}-x^{w+1}}{w(w+1)}\right|
\le\frac{\sqrt{x+1}}{|w|},
\qquad
\sum_{|\Im w|\le x}\frac{|d_w|}{|w|}\ll_F\log^2(2x).
\]
For the upper group, each difference is
\(O(x^{3/2}/|\Im w|^2)\), and the sum of \(|d_w|/|\Im w|^2\)
over that group is \(O_F(\log(2x)/x)\).
The difference \(P(x+1)-P(x)-B(x)\) uses only integers \(x<n\le x+1\)
and is \(O_F(\log(2x))\). Therefore
\[
B(x)=mx+O_F(\sqrt{x}\log^2(2x)).
\]
The higher powers of primes contribute \(O_F(\sqrt x)\) by
\(\sum_{2\le j\le\log_2 x}\sum_{p\le x^{1/j}}\log p=O(\sqrt x)\)
using the Chebyshev upper bound. For prime-ideal powers, apply the
same rational-prime bound with the residue-degree multiplicity above.
Thus the bound on \(B\) is equivalent to the same bound on the sum
of first-power coefficients \(a(q,1)\log q\) over primes or prime ideals.
Omitting any fixed finite set of primes leaves the estimate equivalent.

Conversely, restore higher powers using the same bound. First for
\(\Re s>1\) one has
\[
s\int_1^\infty [B(x)-mx] x^{-s-1}\,dx
=-F'(s)/F(s)-\frac{ms}{s-1}.
\]
The bound on \(B(x)-mx\) makes the left side holomorphic for
\(\Re s>1/2\). The term at \(s=1\) cancels the original pole contribution.
Any other zero or pole there would give a nonzero residue on the right.
Gamma factors are regular and nonvanishing in this half-plane.
Functional equation and dual conjugation exclude the other open
half-plane. In the meromorphic case this argument reads the signed divisor.

Partial summation in both directions, using \(\log q\) and its inverse,
now gives
\[
\sum_{q\le x} a(q,1)
=m\operatorname{Li}(x)+O_F(\sqrt{x}\log(2x)),\qquad
\operatorname{Li}(x)=\int_2^x\frac{dt}{\log t}.
\]
If \(m=0\) and \(a(p,1)=A_p/p^\lambda\), use
\(t^\lambda/\log t\) and its inverse in partial summation. The equivalent
bound on the unweighted sum of \(A_p\) is
\(O_F(x^{1/2+\lambda}\log(2x))\). In every case the domain is every real
\(x\ge2\) with a fixed constant for the entry.

| Entry | Arithmetic equivalent |
| --- | --- |
| Beta | Difference of prime counts for 1 and 3 modulo 4 is \(O(\sqrt{x}\log(2x))\). |
| Quadratic `3.2` | \(\pi(x;3,1)-\pi(x;3,2)=O(\sqrt x\log(2x))\). |
| Quadratic `5.4` | \(\pi(x;5,1)+\pi(x;5,4)-\pi(x;5,2)-\pi(x;5,3)=O(\sqrt x\log(2x))\). |
| Quadratic `7.6` | \(\pi(x;7,1)+\pi(x;7,2)+\pi(x;7,4)-\pi(x;7,3)-\pi(x;7,5)-\pi(x;7,6)=O(\sqrt x\log(2x))\). |
| Either quartic mod 5 | The norm of the discrepancies for 1 versus 4 and 2 versus 3 is \(O(\sqrt{x}\log(2x))\). The character of 2 is \(i\) or \(-i\), and the two dual characters give the same norm. |
| Level 23 | Twice the count of completely split primes minus the count of inert primes for \(T^3-T-1\), with 23 omitted, is \(O(\sqrt{x}\log(2x))\). The trace is the number of roots minus one. |
| Cubic zeta | The prime-ideal count is \(\operatorname{Li}(x)+O(\sqrt{x}\log(2x))\). |
| Ramanujan's \(\Delta\) | \(\sum_{p\le x}\tau(p)=O(x^6\log(2x))\), with \(\lambda=11/2\). |
| Elliptic 37.a1 | \(\sum_{p\le x,\ p\ne37}(\#E(\mathbb F_p)-p-1)=O(x\log(2x))\), with \(\lambda=1/2\). |
| Genus two 277.a | \(\sum_{p\le x,\ p\ne277}(\#C(\mathbb F_p)-p-1)=O(x\log(2x))\), from the trace on \(H^1(C)\), with \(\lambda=1/2\). |
| Even icosahedral Artin | The individual Frobenius trace sum over primes other than 2141 is \(O(\sqrt{x}\log(2x))\) in complex modulus, equivalent to central-line location of the signed divisor. |

For the joint \(\Delta\) case the first coefficient of
\(\zeta^2 L(\Delta)^2 L(\operatorname{Sym}^2\Delta)\) is
\((1+\tau(p)/p^{11/2})^2\). The pole order is 2. The unweighted sum
of these squares is \(2\operatorname{Li}(x)+O(\sqrt{x}\log(2x))\)
if and only if all three factor hypotheses hold. This is the scope of
the joint test. The \(\tau(p)\) cancellation above tests only \(\Delta\).

The arithmetic transfers are prose specializations. The published Lean
family theorems supply the triangular and ideal-divisor criteria.
The explicit-formula bounds are standard in scope, and the displayed
prime and point-count identities specialize them to the listed objects.

[Unconditional explicit formula for standard automorphic functions](https://intlpress.com/site/pub/files/_fulltext/journals/pamq/2007/0003/0002/PAMQ-2007-0003-0002-a004.pdf) ·
[Prime trace for the level-23 form](https://www.college-de-france.fr/media/jean-pierre-serre/UPL1210350903026534135_on_a_theorem_of_Jordan.pdf)

### Multiplicity directly from unsmoothed data

After location, use \(B\) for the individual \(F\), with its own pole
main term. Write \(w=1/2+it\), \(s=w+\delta\) for \(\delta>0\), and set
\[
U(t,\delta)=-\delta s\int_1^\infty [B(x)-mx]x^{-s-1}\,dx.
\]
The preceding identity gives \(U(t,\delta)\to\operatorname{ord}_{w}
\Lambda_F\) as \(\delta\downarrow0\), since
\(\delta ms/(s-1)\to0\). Eventual \(\Re U(t,\delta)<3/2\) for each
\(t\ne0\) tests noncentral simplicity in the holomorphic cases.
Eventual \(|\Re U(0,\delta)-r|<1/2\) tests exact central order \(r\).
The cutoffs in \(\delta\) may depend on \(t\). Higher prime powers
matter in this boundary test because their series can have singularities
on \(\Re s=1/2\). For the Artin function, eventual
\(\Re U(t,\delta)>-1/2\) at every \(t\) excludes all remaining poles.
Combining it with the upper threshold tests holomorphy and simplicity.
The Gaussian criterion below is a separate equivalent test in the
holomorphic case.

### Primitive quadratic characters of conductors 3, 5, and 7

For \(D\in\{-3,5,-7\}\), put \(q=|D|\), \(K=\mathbb Q(\sqrt D)\), and
\(\chi_D(n)=(D/n)\). The characters are primitive with values \(+1\) and
\(-1\) on the residue classes shown in the prime-count table and zero on
multiples of \(q\). Hence for all primes \(p\) and integers \(j\ge1\) the
logarithmic prime-power coefficient is \(\chi_D(p)^j\log p\). The
completion is \(q^{s/2}\Gamma_{\mathbb R}(s+a)L(s,\chi_D)\) with
\(a=0\) for \(D>0\) and \(a=1\) for \(D<0\). The quadratic Gauss sum
gives root number \(+1\). The completion is entire of order at most
one, with zero pole order, and the triangular remainder is
\[
R_D(x)=-\sum_{\substack{p\ {\rm prime},\, j\ge1\\p^j\le x}}
  \chi_D(p)^j\log p\,(1-p^j/x).
\]
Its critical-line criterion is equivalent to the corresponding prime-count
bound in the table. The sum is the number of split primes up to \(x\)
minus the number of inert primes up to \(x\), excluding the ramified prime.
This is an individual-character instance of the classical explicit-formula
scale.

At each rational prime the exact factorization
\(\zeta_K(s)=\zeta(s)L(s,\chi_D)\) follows from the split, inert, and ramified
Euler polynomials \((1-T)^2\), \(1-T^2\), and \(1-T\), respectively.
There are no poles of either factor in \(0<\Re s<1\). Thus **assuming
ordinary RH**, the individual-character critical-line hypothesis, the
prime-count bound, and the field-specific
\(\operatorname{CorrectedIdealRobin}(K)\) are equivalent. The ideal
inequality itself implies both ordinary RH and the character's
critical-line hypothesis. The three residues in the field table follow
from the analytic class number formula.

The exact central order is zero. Put \(f(u)=u^{-1/2}\) and group the
convergent character series for \(L(1/2,\chi_D)\) into consecutive blocks
of length \(q\). For \(D=-3\), pair \(1\) against \(2\). For \(D=-7\),
pair \(1,2,4\) against \(3,5,6\) in that order. Every difference in these
two cases is positive by strict decrease of \(f\). For \(D=5\), the block
is
\[
[f(5k+1)-f(5k+2)]-[f(5k+3)-f(5k+4)]>0
\qquad(k\ge0)
\]
by strict convexity. Thus the individual prime-power multiplicity criterion
tests simplicity only at noncentral zeros, conditional on this character's
location hypothesis. The Gaussian criterion uses the individual sequence
\(\chi_D(p)^j\log p\), including all \(j\ge1\).

[LMFDB character 3.2](https://www.lmfdb.org/Character/Dirichlet/3/2) ·
[LMFDB character 5.4](https://www.lmfdb.org/Character/Dirichlet/5/4) ·
[LMFDB character 7.6](https://www.lmfdb.org/Character/Dirichlet/7/6) ·
[LMFDB fields for \(D=-3\)](https://www.lmfdb.org/NumberField/2.0.3.1),
[\(D=5\)](https://www.lmfdb.org/NumberField/2.2.5.1), and
[\(D=-7\)](https://www.lmfdb.org/NumberField/2.0.7.1)

### Complex primitive characters modulo 7

Let \(\chi_m=\chi_7(m,\cdot)\) in Conrey's notation and
\(\xi=e^{\pi i/3}\), \(\omega=\xi^2\). The least primitive root \(3\)
has powers \(1,3,2,6,4,5\) in order. For \(1\le a\le6\) the
exponent of \(\xi\) in \(\chi_m(a)\) is the product modulo \(6\) of
the discrete logarithms of \(m\) and \(a\) to base \(3\).
This gives exact local data at every prime.

| LMFDB L-function | Character order and parity | Exponents of \(\xi\) at residues \(1,2,3,4,5,6\) |
| --- | --- | --- |
| `1-7-7.2-r0-0-0` | 3, even | \(0,4,2,2,4,0\) |
| `1-7-7.3-r1-0-0` | 6, odd | \(0,2,1,4,5,3\) |
| `1-7-7.4-r0-0-0` | 3, even | \(0,2,4,4,2,0\) |
| `1-7-7.5-r1-0-0` | 6, odd | \(0,4,5,2,1,3\) |

For parity \(a=0,1\), the completion is
\(7^{s/2}\Gamma_{\mathbb R}(s+a)L(s,\chi_m)\). Its functional
equation pairs it with \(\overline{\chi_m}\) and has exact root number
\(\tau(\chi_m)/(i^a\sqrt7)\), where
\(\tau(\chi_m)=\sum_{r=1}^{6}\chi_m(r)\xi_7^r\) and
\(\xi_7=e^{2\pi i/7}\). The product of the two completions is an
entire, self-dual location test of order at most one. Its pole order is zero.
The paired triangular remainder is
\[
-\sum_{\substack{p\ {\rm prime},\, j\ge1\\p^j\le x}}
  2\Re(\chi_m(p)^j)\log p\,(1-p^j/x).
\]
Each individual location hypothesis is equivalent to that for its
conjugate, since \(L(s,\overline{\chi_m})=\overline{L(\bar s,\chi_m)}\).

Write \(P_j=\pi(x;7,j)\). For the two pairs, the full arithmetic location
conditions for all real \(x\ge2\) are respectively
\[
\begin{aligned}
|P_1+P_6+\omega(P_3+P_4)+\omega^2(P_2+P_5)|
  &\le C\sqrt{x}\log x,\\
|P_1-P_6+\xi(P_3-P_4)+\xi^2(P_2-P_5)|
  &\le C\sqrt{x}\log x .
\end{aligned}
\]
The constant can depend on the pair. These are the absolute values
of the individual prime sums for \(\chi_2,\chi_3\). The other
members conjugate the expression. The prime \(7\) contributes zero.

The fields satisfy
\[
\zeta_{K^+}=\zeta L(s,\chi_2)L(s,\chi_4),
\qquad
\zeta_K=\zeta_{K^+}L(s,\chi_6)L(s,\chi_3)L(s,\chi_5),
\quad K^+=\mathbb Q(\zeta_7)^+,\quad K=\mathbb Q(\zeta_7).
\]
The even characters are precisely the characters of the real quotient.
At \(7\) both fields are totally ramified, so each has just the factor
\((1-7^{-s})^{-1}\) from \(\zeta\). The factors have no poles in
\(0<\Re s<1\), so the auxiliary RH hypotheses shown in the field table
isolate exactly the intended pair. The fieldwise theorem gives the
corrections \(12+3\log49\) and \(12+3\log16807\), respectively.

For the multiplicity criterion the individual coefficients are
\(\chi_m(p)^j\log p\), including all \(j\ge1\). To prove that the
central order is zero, put \(f(u)=u^{-1/2}\) and group the convergent
series into blocks of length \(7\). With \(A_r=f(7k+r)\), the block
imaginary parts for \(\chi_2,\chi_3\), divided by \(\sqrt3/2\), are
\[
 A_3+A_4-A_2-A_5<0,\qquad (A_2-A_5)+(A_3-A_4)>0 .
\]
The first strict inequality follows from strict convexity and the second
from strict decrease. Conjugation reverses the sign for the other member
of each pair. The completed functions therefore have exact central order
zero. Under individual location, the boundary or Gaussian criterion
is equivalent to simplicity of the remaining zeros.

[Conrey convention](https://www.lmfdb.org/knowledge/show/character.dirichlet.conrey) ·
[Real cubic field](https://www.lmfdb.org/NumberField/3.3.49.1) ·
[Full cyclotomic field](https://www.lmfdb.org/NumberField/6.0.16807.1)

### Dirichlet characters of conductors 8, 9, and 11

The primitive quadratic characters below have discriminants \(-8,8,-11\).
For \(\chi_D=(D/\cdot)\), write \(q=|D|\), and denote by \(S_+\), \(S_-\)
the residue classes where \(\chi_D\) is \(+1\), \(-1\), respectively.

| LMFDB character | \(S_+\) | \(S_-\) |
| --- | --- | --- |
| `8.3` | \(1,3\) | \(5,7\) |
| `8.5` | \(1,7\) | \(3,5\) |
| `11.10` | \(1,3,4,5,9\) | \(2,6,7,8,10\) |

Their coefficients are \(\chi_D(p)^j\), zero at the ramified prime.
The completion and triangular remainder have the same formulas as for
the earlier primitive quadratic characters. The arithmetic equivalence is
\[
\left|\sum_{a\in S_+}\pi(x;q,a)-\sum_{a\in S_-}\pi(x;q,a)\right|
 \le C\sqrt{x}\log x\quad(x\ge2),
\]
for some \(C>0\), testing the zero location of the individual character
without additional hypotheses. The factorization
\(\zeta_{\mathbb Q(\sqrt{D})}=\zeta L(s,\chi_D)\) gives the separate
corrected ideal equivalence under ordinary RH. These fields have class
number one. For the real field the fundamental unit is \(1+\sqrt2\),
and the two imaginary fields have two roots of unity. The analytic class
number formula therefore gives the residues listed in the field table.
For central nonvanishing, compare the positive and negative residues
in the two odd cases term by term in each block in the displayed order.
Every positive residue is smaller than its partner. In the even case
use strict convexity of \(t^{-1/2}\) on the equally spaced
arguments \(8k+1,8k+3,8k+5,8k+7\). All block sums are positive.

For modulus \(9\), \(2\) is the least primitive root and its powers in
order are \(1,2,4,8,7,5\). With \(\xi=e^{\pi i/3}\), the exact
Conrey exponents of \(\xi\), in residue order \(1,2,4,5,7,8\), are

| LMFDB L-function | Character order and parity | Exponents of \(\xi\) |
| --- | --- | --- |
| `1-3e2-9.2-r1-0-0` | 6, odd | \(0,1,2,5,4,3\) |
| `1-3e2-9.4-r0-0-0` | 3, even | \(0,2,4,4,2,0\) |
| `1-3e2-9.5-r1-0-0` | 6, odd | \(0,5,4,1,2,3\) |
| `1-3e2-9.7-r0-0-0` | 3, even | \(0,4,2,2,4,0\) |

Nonunits have character value zero. The primitive completion is
\(9^{s/2}\Gamma_{\mathbb R}(s+a)L(s,\chi)\), with parity \(a\) and
root number \(\tau(\chi)/(i^a\sqrt9)\). As for modulus \(7\), its
paired triangular remainder uses \(2\Re(\chi(p)^j)\), and the
unpaired multiplicity test uses \(\chi(p)^j\). With \(P_j=\pi(x;9,j)\)
and \(\omega=\xi^2\), the arithmetic location tests are
\[
\begin{aligned}
 |P_1-P_8+\xi(P_2-P_7)+\xi^2(P_4-P_5)| &\le C\sqrt{x}\log x,\\
 |P_1+P_8+\omega(P_2+P_7)+\omega^2(P_4+P_5)| &\le C\sqrt{x}\log x
 \qquad(x\ge2).
\end{aligned}
\]
The first tests either order-six character and the second tests either
order-three character. The other member in each pair conjugates the sum.
The \(L\)-functions for the conjugate pair have equivalent location
hypotheses, with the ordinates reflected.

Using \(\chi_m=\chi_9(m,\cdot)\) and \(K^+=\mathbb Q(\zeta_9)^+\),
\(K=\mathbb Q(\zeta_9)\), the zeta factorizations are
\[
\zeta_{K^+}=\zeta L(s,\chi_4)L(s,\chi_7),\qquad
\zeta_K=\zeta_{K^+}L(s,\chi_{-3})L(s,\chi_2)L(s,\chi_5).
\]
The odd quadratic factor has primitive conductor \(3\) and LMFDB
character label `3.2`. At \(3\) both fields have the single factor
\((1-3^{-s})^{-1}\) from \(\zeta\). No factor has a pole in the open
critical strip. The fieldwise theorem gives discriminant corrections
\(12+3\log81\) and \(12+3\log19683\).
Ordinary RH isolates the order-three pair in \(K^+\). Dedekind RH for
\(K^+\) together with RH for `3.2` isolates the order-six pair in \(K\).

Write \(A_r=(9k+r)^{-1/2}\) for \(k\ge0\). In the central series,
divide the block imaginary parts by \(\sqrt3/2\). These become
\((A_2-A_7)+(A_4-A_5)>0\) for `9.2` and
\(A_2+A_7-A_4-A_5>0\) for `9.4`. The first uses strict
decrease. For the second, the two pairs have the same sum of arguments
and the outer pair is more separated, so strict convexity applies.
Their conjugates reverse the signs. All seven central orders are zero,
and under the respective location hypothesis the individual
multiplicity criterion tests the simplicity of the noncentral zeros.

[Real cubic field](https://www.lmfdb.org/NumberField/3.3.81.1) ·
[Full cyclotomic field](https://www.lmfdb.org/NumberField/6.0.19683.1) ·
[Conrey convention](https://www.lmfdb.org/knowledge/show/character.dirichlet.conrey)

## Location and arithmetic data

Use unitary normalization throughout, with critical line \(\Re s=1/2\).
Let \(\mathfrak p\) be a prime ideal of the base field, \(q=N\mathfrak p\),
and \(P_{\mathfrak p}(T)=\prod_k(1-\alpha_{\mathfrak p,k}T)\) the exact local
polynomial. Define \(b_{\mathfrak p,j}=\log q\sum_k\alpha_{\mathfrak p,k}^j\).
Keep the real local degree at ramified primes. When LMFDB gives a polynomial
in arithmetic normalization of motivic weight \(w\), substitute
\(T\mapsto T/q^{w/2}\). For a location test using \(L\widetilde L\), replace
\(b\) by \(2\Re b\) and use the pole order of the product. For a self-dual
pole-free function the individual real-coefficient test is obtained by
dividing the paired bound by two.

For the chosen test \(Z\) with pole order \(m\) at \(1\), take
\[
R_Z(x)=\frac{mx}{2}-\sum_{\substack{\mathfrak p,\ j\ge1\\q^j\le x}}
b_{\mathfrak p,j}(Z)\left(1-\frac{q^j}{x}\right).
\]
Location is equivalent to \(\exists C>0,\ X\ge1,\ \forall x\in\mathbb R,\
x\ge X,\ R_Z(x)\le C\sqrt{x}\), on the analytic domain of the criterion.
Use the actual Euler logarithm, absolute summability for \(\Re s>1\),
entireness and order at most one after pole clearing, the exact completion
factors with shifts \(\Re\mu>-1/2\), and dual reflection. The pole at \(1\)
contributes \(mx/2\). The resulting Mellin transform is
\[
\mathcal M R_Z(s)=\frac{m}{2(s-1)}+\frac{Z'(s)/Z(s)}{s(s+1)}.
\]
The explicit formula gives the square-root bound when the completed zeros
lie on the line. Conversely, the eventual nonnegative function
\(C\sqrt{x}-R_Z(x)\) would have a real Mellin singularity at its abscissa
of convergence if any pole occurred to the right of the line. A real zero
of the pole-cleared function gives a negative residue for this comparison
transform, contradicting nonnegativity. Reflection excludes the left side.

The repository's actual rank-one construction is in
[HeckeStandardRankOne.lean](https://github.com/kimihiro64/Robin1984/blob/main/Robin1984/GRH/HeckeStandardRankOne.lean).
[Solution.lean](https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean) provides the standard location and
multiplicity equivalences for supplied higher-rank data. The individual
higher-rank entries below use those arguments in prose. A focused
classical \(\mathrm{GL}_2\) Lean provider would first construct the
absolutely convergent Euler logarithm and identify the Mellin transform of
the cusp expansion. Fricke reflection gives exponential decay at zero
after multiplication by a power. Combined with exponential decay at
infinity, this gives an entire transform with order-at-most-one growth and
the required reflection. The concrete analytic identifications are the
next Lean obligations.

## Multiplicity once location holds

Use each individual, possibly complex, coefficient \(b_{\mathfrak p,j}\)
in the triangle and form \(A(t)=e^{-t/2}R_L(e^t)\) for \(t\ge0\), extended
by zero for \(t<0\). With the normalization and convolution sign used in
[MultiplicityGaussian.lean](https://github.com/kimihiro64/Robin1984/blob/main/Robin1984/GRH/MultiplicityGaussian.lean)
and [MultiplicityFourierSeries.lean](https://github.com/kimihiro64/Robin1984/blob/main/Robin1984/GRH/MultiplicityFourierSeries.lean),
\[
g_a(v)=\frac{e^{-v^2/(4a)}}{\sqrt{4\pi a}},\qquad
k_a(v)=\left(\frac{v^2}{4a^2}-\frac va+\frac34-\frac1{2a}\right)g_a(v),
\qquad H_a(t)=\int_{\mathbb R} k_a(v)A(t-v)\,dv.
\]
Let \(c_a(u)\) be the mean Fourier coefficient of \(H_a\) at \(u\).
Choose finite exceptional ordinates \(E\) and finite prescribed ordinates
\(J\), and write \(H_{a,E}(t)=H_a(t)-\sum_{u\in E}c_a(u)e^{iut}\).
The test from [MultiplicityExceptions.lean](https://github.com/kimihiro64/Robin1984/blob/main/Robin1984/GRH/MultiplicityExceptions.lean) is
\[
\limsup_{T\to\infty}\frac1T\int_0^T|H_{1,E}(t)|^2dt
+\sum_{u\in J}|c_1(u)-d(u)e^{-u^2}|^2
\ \le\ \limsup_{t\to\infty}\Re H_{2,E}(t).
\]
It is equivalent to order at most one outside \(E\) and exact order \(d(u)\)
on \(J\). Under location, \(c_a(u)=e^{-au^2}\operatorname{ord}_{1/2+iu}\Lambda\).
The pilot uses \(J=\{0\}\), \(E=\varnothing\) for orders zero and one. A
target of central order at least two uses \(E=J=\{0\}\) so the two demands
are compatible. A self-dual square would double every zero order, and a
dual product can merge orders from two distinct factors. Use the individual
signal in both cases.

## Level 23 and the cubic field

For [2-23-23.22-c0-0-0](https://www.lmfdb.org/L/2/23/23.22/c0/0/0) and the
[cubic field 3.1.23.1](https://www.lmfdb.org/NumberField/3.1.23.1), Serre's
factorization is \(\zeta_K=\zeta L(f)\), with \(f=\eta(z)\eta(23z)\).
For \(p\ne23\), the individual log coefficient of \(L(f)\), divided by
\(\log p\), is the number of fixed points of \(\operatorname{Frob}_p^j\) on
the three roots minus one. At \(23\) it is \(1\) for every \(j\), from
\(1-T\). Adding \(1\) at each \(p^j\) gives the rational-prime aggregation
for \(\zeta_K\). Its corrected ideal Robin bound, with correction numerator
\(12+3\log 23\), is equivalent to location for both factors jointly.

The arithmetic Mellin integral of \(f(it)\) is strictly positive at
\(s=1/2\) since both eta factors are positive there for every \(t>0\).
The same argument for \(\eta(it)^{24}\) at arithmetic \(s=6\) treats
[\(\Delta\)](https://www.lmfdb.org/L/2/1/1.1/c11/0/0). The alternating eta
series gives \(\zeta(1/2)<0\), so the cubic field has central order zero
as well. In its \(S_3\) Galois closure the nontrivial two-dimensional
factor occurs squared. Each of its zeros contributes order at least
two to the closure's zeta function.

[Serre's factorization and Frobenius calculation](https://www.college-de-france.fr/media/jean-pierre-serre/UPL1210350903026534135_on_a_theorem_of_Jordan.pdf)

## Exact central orders for elliptic 37.a1 and genus two 277.a

For [37.a1](https://www.lmfdb.org/L/2/37/1.1/c1/0/1), use the unitary
local parameter \(-1/\sqrt{37}\) at the bad prime. The Fricke sign is
\(-1\). Put \(B=2\pi/\sqrt{37}>1\), \(q_0=e^{-B}<3/8\),
\(F(t)=\sum_{n\ge1}a_ne^{-Bnt}\), and \(H(q)=\sum_{n\ge1}a_nq^{n-1}\).
Then \(F(t)=-t^{-2}F(1/t)\), so \(H(q_0)=0\). The coefficients
\(a_2,\ldots,a_7\) are \(-2,-3,2,-2,6,-1\). The local root bounds give
\(|a_n|\le d(n)\sqrt n\le2n\), where \(d(n)\) counts the divisors of \(n\).
For \(0\le q\le3/8\),
\[
H'(q)\le -2-6q+6q^2+30q^4+2\sum_{n\ge8}n(n-1)q^{n-2}<0.
\]
Here \(30q^4<3/5\) and the tail is at most
\(112(3/8)^6/(1-27/56)<2/3\). Consequently \(H(q)>0\) for \(q<q_0\).
The arithmetic completed derivative at \(1\) is
\(2\int_1^\infty F(t)\log(t)\,dt>0\), up to a positive normalization
factor. Thus the central order is exactly one.

For [277.a](https://www.lmfdb.org/L/4/277/1.1/c1e2/0/0), all local factors
agree with the paramodular spin function. The ordinary coefficient bound is
\(|a_n|\le\sqrt n\,d_4(n)\), including the bad factor
\((1+T)(1-8T+277T^2)\). Its arithmetic completion is proportional to
\(A^s\Gamma(s)^2 L(s)\), \(A=\sqrt{277}/(4\pi^2)\), with sign \(+1\).
Writing \(B=2/\sqrt A>3\), inverse Mellin and the functional equation give
\[
L(1)=\frac4{\sqrt A}\sum_{n\ge1}\frac{a_n}{\sqrt n}K_1(B\sqrt n).
\]
In the inverse Mellin step, the kernel for \(\Gamma(s)^2\) is
\(2K_0(2\sqrt t)\). The sign \(+1\) doubles the integral from \(1\) to
infinity at the center. The \(n=1\) term is positive. The integral
representation of \(K_1(y)\), using \(1\le\sqrt{1+v}\le1+v/2\),
sandwiches it between \(\sqrt{\pi/(2y)}e^{-y}\) and that expression
times \(1+3/(8y)\). The absolute ratio of the \(n\)th term to the first
is at most
\[
|a_n|n^{-3/4}e^{-3(\sqrt n-1)}(1+1/(8\sqrt n)).
\]
The exact coefficients \(a_2,\ldots,a_{15}\) are
\(-2,-1,0,-1,2,1,4,0,2,-2,0,3,-2,1\).
Use \(\sqrt2>7/5,\ \sqrt3>17/10,\ \sqrt5>11/5,\ \sqrt9=3\) and
\(e^{6/5}>3,\ e^2>7,\ e^3>20\). The ratios on \(n=2\), \(n=3\),
\(5\le n\le8\), and \(9\le n\le15\) sum to less than
\(1/2+1/12+1/6+1/100<7/8\).
For \(n\ge16\) use \(d_4(n)\le(10/3)n\). This follows by maximizing
\(\binom{e+3}{3}/p^e\) at each prime, with maxima \(5/2,\ 4/3,\ 1\)
for \(p=2,\ p=3,\ p\ge5\), respectively. The bin
\(k^2\le n<(k+1)^2\) has ratio sum at most
\[
(10/3)(2k+1)(k+1)^2 e^{-3(k-1)}(1+1/(8k)),\qquad k\ge4 .
\]
The first bound is below \(24750/256000\), and the ratio of successive
bounds is below \(11/125\). The tail is below \(1/8\). Hence \(L(1)>0\)
and the central order is zero.

[Paramodularity, Theorem 7.1.3](https://msp.org/ant/2019/13-5/ant-v13-n5-p05-p.pdf) ·
[Bessel integral representation](https://dlmf.nist.gov/10.32.E8) ·
[Bessel Mellin transform](https://dlmf.nist.gov/10.43.E19)

## Exact central order for elliptic 389.a1

For \(E:y^2+y=x^3+x^2-2x\), modularity gives the weight-two form
of conductor \(389\). At a good prime write \(a_p=p+1-\#E(\mathbb F_p)\).
The normalized local parameters are the roots of
\(T^2-(a_p/\sqrt p)T+1\). At \(389\) the reduction is split
multiplicative, so the single normalized parameter is \(1/\sqrt{389}\).
The global root number is \(+1\). These inputs give the individual
triangular location test, and removal of the triangular weight gives
the full equivalent statement
\[
 \left|\sum_{\substack{p\le x\\p\ {\rm prime},\ p\ne389}}
      (\#E(\mathbb F_p)-p-1)\right|\le C x\log x
 \qquad(x\ge2)
\]
for some \(C>0\). The bound concerns all real \(x\ge2\) and the primes
of good reduction.

The rational points \(P=(0,0)\) and \(Q=(1,0)\) give a lower bound
on central order. Over \(\mathbb F_5\) the curve has nine points, so
the rational group has no \(2\)-torsion by injectivity of reduction
on prime-to-\(5\) torsion. Over \(\mathbb F_{11}\) the subgroup
\(2E(\mathbb F_{11})\) consists of
\(\mathcal O,(3,5),(6,4),(6,6)\).
The images of \(P,Q,P+Q=(9,10)\) lie outside this subgroup. An integral
relation would have both coefficients even; since there is no
\(2\)-torsion one can divide them by \(2\), ruling out every nonzero
relation. The rank is at least two. The Gross–Zagier and Kolyvagin
theorem for analytic rank zero or one now gives
\(\operatorname{ord}_{s=1}L(E,s)\ge2\).

For the upper bound put \(B=2\pi/\sqrt{389}\) and
\(F(t)=\sum_{n\ge1} a_n e^{-Bnt}\), using the arithmetic coefficients.
Take exactly
\(\Lambda(s)=(\sqrt{389}/(2\pi))^s\Gamma(s)L(E,s)\).
Since the sign is \(+1\), Mellin integration gives
\[
\Lambda''(1)=2\int_1^\infty F(t)(\log t)^2\,dt.
\]
The coefficient bound \(|a_n|\le d(n)\sqrt n\le2n\) follows from the
local root bounds, including the bad Euler factor, and justifies the
differentiation. The exact interval verifier gives
\[
 \int_1^{64}\left(\sum_{n=1}^{64}a_n e^{-Bnt}\right)
          (\log t)^2\,dt \ \ge\ \frac{2341}{1000}.
\]
The code computes the first \(64\) coefficients by point counting and
the exact prime-power recurrence. On the grid of step \(1/128\), the
positive terms use lower exponential bounds at the right endpoint
and the negative terms use upper exponential bounds at the left
endpoint. For the square of the logarithm, use the lower left bound
when the lower sum is positive and the upper right bound when it
is negative. The initial exponentials and the step factors come from
alternating Taylor partial sums with \(318/1000<B<319/1000\).
For logarithms use range reduction by powers of \(2\) and the first
16 terms of \(2\sum_{k\ge0}z^{2k+1}/(2k+1)\), \(z=(u-1)/(u+1)\),
\(1\le u\le2\). The remaining terms are bounded by \(3/3^{33}\).
All rounded bounds use integer scale \(10^{20}\) with outward rounding.

For the coefficient tail use
\((\log t)^2\le(t-1)^2\) and integrate each \(n>64\) term against
the exponential. Since \(B>3/10\) and \(e^{-B}<3/4\), its total
absolute integral on \([1,\infty)\) is bounded by
\[
 \frac{16000}{27\cdot65^2}(3/4)^{65}<1/200.
\]
For the integration tail, \(|F(t)|\le 32e^{-Bt}\) for \(t\ge1\),
by summing \(2n e^{-Bnt}\). Using \((\log t)^2\le t^2\) shows the
absolute integral over \(t\ge64\) is bounded by
\[
32(3/4)^{64}
 \left(\frac{40960}{3}+\frac{12800}{9}+\frac{2000}{27}\right)<1/200.
\]
Thus \(\Lambda''(1)>4.662\) in the stated normalization. The analytic
central order is exactly two. Under the critical-line hypothesis the
individual multiplicity criterion tests simplicity at every noncentral
zero, with prescribed central order two. This certificate independently
reproduces the central order for this particular curve.

At \(p=3\) there are six points, so \(a_3=-2\), and the unitary trace
has square \(4/3\). The same proof as in the following section rules
out the direct all-prime Dedekind-factor route for this curve.

[Curve and local data](https://www.lmfdb.org/EllipticCurve/Q/389/a/1) ·
[Gross on the analytic-rank theorem](https://users.dm.unipi.it/lombardo/Kolyvagin/Gross.pdf) ·
[Exact interval verifier](lmfdb-explorer/verify-389-center.mjs)

## Obstruction to a direct corrected ideal transfer for Δ, 37.a1, and 277.a

For any number field \(K\), the reciprocal Euler polynomial of \(\zeta_K\)
at a rational prime \(p\) is \(\prod_{\mathfrak p\mid p}(1-T^{f_{\mathfrak p}})\),
with \(f_{\mathfrak p}\) the residue degrees. This also holds at ramified
primes. Its roots are roots of unity. Thus any individual factor matched
as an exact Euler-polynomial divisor at every prime must have a sum of
local eigenvalues that is an algebraic integer at every prime. An algebraic
integer with rational square has an integer square.

| Entry | Exact witness prime | Unitary trace | Trace squared |
| --- | ---: | --- | --- |
| Ramanujan's \(\Delta\) | \(2\) | \(-24/2^{11/2}\) | \(9/32\) |
| Elliptic \(37.a1\) | \(5\) | \(-2/\sqrt5\) | \(4/5\) |
| Genus two \(277.a\) | \(3\) | \(-1/\sqrt3\) | \(1/3\) |

For \(\Delta\), the coefficient of \(q^2\) in
\(q\prod_{n\ge1}(1-q^n)^{24}\) is \(-24\).
For \(37.a1\), the numbers of affine solutions over \(\mathbb F_5\)
to \(y^2+y=x^3-x\) are \(2,2,1,0,2\), in order of \(x=0,\dots,4\).
The point at infinity gives \(8\) points, hence trace \(-2\).
For \(277.a.277.1\), the affine model is
\(y^2+(x^3+x^2+x+1)y=-x^2-x\).
Over \(\mathbb F_3\) it has \(2,0,1\) affine solutions at \(x=0,1,2\).
At infinity the chart \(v=y/x^3\) gives \(v^2+v=0\), with two distinct
solutions, so the smooth curve has \(5\) points and trace \(-1\).

These witnesses close the direct all-prime Dedekind-factor route for
the stated unitary \(L\)-functions. A transfer that permits other
factors at the witness prime, or that connects location to a Dedekind
inequality indirectly, requires a separate argument. The catalogue
keeps the proven coefficient and point-count location equivalences and
the individual multiplicity criteria for all three.

[Level-one newform](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/1/12/a/a/) ·
[Curve 37.a1](https://www.lmfdb.org/EllipticCurve/Q/37/a/1) ·
[Curve 277.a.277.1](https://www.lmfdb.org/Genus2Curve/Q/277/a/277/1)

## Artin functions when holomorphy is missing

For a nontrivial irreducible finite-image Artin representation \(\rho\),
use the individual coefficients
\(b_{\mathfrak p,j}=\log q\,\operatorname{tr}(\operatorname{Frob}_{\mathfrak p}^j
|\,V^{I_{\mathfrak p}})\), and take \(m=0\). The following is a
**two-sided** arithmetic equivalence in ordinary mathematics:
\[
|R_\rho(x)|=O_\rho(\sqrt{x})
\quad\Longleftrightarrow\quad
\text{every zero and pole of the meromorphic completion lies on }\Re s=1/2.
\]
The individual coefficients allow complex values. Brauer induction writes
\(L(s,\rho)\) as a finite signed product of finite-order Hecke functions.
The trivial-character pole exponents cancel by Frobenius reciprocity.
Combine their order-one logarithmic-derivative expansions by signed order
at each common zero. The normalized Hadamard term at a point \(w\ne0,-1\)
inverts to \((x^w-x^{-1})/(w(w+1))\), and the terms at \(0\) and \(-1\)
are \(\log x-1+x^{-1}\) and \(-x^{-1}\log x\), respectively.
The divisor sum is absolutely convergent after the two powers in the
denominator. The gamma shifts for finite-image Artin data are \(0\) and
\(1\), so the ordinary zeros or poles from gamma factors occur at
\(\Re w\le0\). Under the right-hand condition this gives the claimed
two-sided bound. In the reverse direction the absolute bound makes the
Mellin transform \(L_\rho'/[s(s+1)L_\rho]\) holomorphic on
\(\Re s>1/2\). Any nonzero signed order there yields an uncancelled
residue. Dual reflection and conjugation exclude the other half-plane.

For \(w=1/2+iu\), put
\[
D_w(\delta)=\delta(w+\delta)(w+\delta+1)
\int_1^\infty R_\rho(x)x^{-w-\delta-1}dx.
\]
Under the two-sided bound \(D_w(\delta)\to\operatorname{ord}_w\Lambda_\rho\),
the signed integer order. Requiring \(\Re D_w(\delta)>-1/2\) eventually
as \(\delta\downarrow0\) for each \(u\) is equivalent to the absence of
central poles. Combining location and this test gives an arithmetic
equivalence to holomorphy **and** the critical-line hypothesis.
Adding the eventual upper bound \(\Re D_w(\delta)<3/2\), at ordinates
where simplicity is wanted, gives order zero or one.
The global limsup expression above uses nonnegative zero orders, so the
signed extension uses the pointwise residue test.

For the even icosahedral origin
[2.4583881.120.a.b](https://www.lmfdb.org/ArtinRepresentation/2.2141e2.120.1c2),
the archimedean factor is \(\Gamma_{\mathbb R}(s+1)^2\), since complex
conjugation has trace \(-2\). At the only ramified prime \(2141\) the
inertia is tame and its fixed space is zero by the conductor exponent two.
The local polynomial is \(1\). At other primes the two trace powers have
determinant-one recurrence. The one-sided provider remains blocked by a
case-specific holomorphy proof or a suitable pole-sign theorem. A real
pole would contribute the opposite residue from that used in the Landau
converse. The LMFDB Artin entry supplies the origin identifier.

[Artin continuation and finite-height verification](https://arxiv.org/abs/math/0507502) ·
[Brauer induction](https://doi.org/10.2307/1969183)

## Coverage and reproducibility

The [research backlog workflow](LMFDB_BACKLOG.md) defines the queue,
inventory receipts, stage decisions, and browser progress snapshot.

Use the existing Robin1984 checkout for source edits, proof research and
validation. Open `docs/lmfdb-explorer/index.html` in a browser to use the
explorer. It loads its catalogue from a classic script in the same directory.
Treat `catalog.json` as the source of truth. After editing it, run
`docs/lmfdb-explorer/check-catalog.mjs --write-browser-data` with a resolved
Node executable from Robin1984. Run the validator without flags before
release. It checks that the generated browser asset matches the JSON.
For an HTTP preview, serve `docs` and open `/lmfdb-explorer/`.
The site opens with the exact fieldwise statement and links each
established ideal transfer to its LMFDB row. Site publication is a
separate operation from editing or validating this checkout.

The pilot inventory tracks labels individually. The site derives its
status counts from its JSON records. The published LMFDB cohort counts
are separate source denominators and are not summed. A family-level
provider is evidence for applying a theorem to a qualifying entry but
does not count as reviewing every matching LMFDB label. Deduplicate
multiple origins for the same function, retain distinct dual labels, and
record which functions share a paired location test. A missing exact
factor, analytic theorem, or Lean identification should be recorded
against the affected row.

For the explorer's sample plot, the theorem domain is every real
\(x\ge X\) for an unknown fixed cutoff \(X\). The evaluator's domain is
121 equally spaced real sample points from \(2\) through the displayed
maximum, with every rational prime power through each endpoint included.
The quartic curves use the paired signal for location. The cubic zeta
uses the rational-prime aggregation of prime-ideal slots. The finite
plot illustrates the kernel and gives no assertion about the eventual
inequality or about zeros beyond the shown interval.
