// Generated from catalog.json by check-catalog.mjs.
globalThis.LMFDB_CATALOG = {
  "asOf": "2026-11-27",
  "snapshotSource": "https://www.lmfdb.org/L/Completeness",
  "cohorts": [
    {
      "id": "dirichlet",
      "name": "Primitive Dirichlet L-functions",
      "total": 7655469
    },
    {
      "id": "newforms",
      "name": "Embedded classical newforms",
      "total": 14398359
    },
    {
      "id": "maass3",
      "name": "GL₃ Maass L-functions",
      "total": 1552
    },
    {
      "id": "genus2",
      "name": "Genus-two L-functions",
      "total": 65534
    }
  ],
  "entries": [
    {
      "id": "1-1-1.1-r0-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ",
            "zeros": "Ordinary RH for ζ(s).",
            "arithmetic": "There exists A ∈ ℕ such that the following holds for every positive integer n ≥ A.",
            "formula": "σ(n) / n ≤ eᵞ [log log n + 12 / √(log n)].",
            "note": "The nonzero ideals are nℤ with norm n, σ(n) = ∑_{d ∣ n} d, D_ℚ = 1, and κ_ℚ = 1.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ]
            ]
          },
          {
            "title": "Robin’s divisor-sum inequality",
            "zeros": "Every zero of the pole-cleared Riemann zeta completion lies on Re s = 1/2.",
            "arithmetic": "For every integer n ≥ 5041.",
            "formula": "σ(n) < eᵞ n log log n.",
            "note": "σ(n) = ∑_{d ∣ n} d; γ is Euler’s constant.",
            "links": [
              [
                "Robin’s divisor-sum inequality source",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean"
              ]
            ]
          },
          {
            "title": "Lagarias’s harmonic-number inequality",
            "zeros": "Every zero of the pole-cleared Riemann zeta completion lies on Re s = 1/2.",
            "arithmetic": "For every integer n ≥ 1.",
            "formula": "σ(n) ≤ Hₙ + exp(Hₙ) log Hₙ.",
            "note": "Hₙ = ∑_{1 ≤ j ≤ n} 1/j.",
            "links": [
              [
                "Lagarias’s harmonic-number inequality source",
                "https://websites.umich.edu/lagarias/doc/elementaryrh.pdf"
              ]
            ]
          },
          {
            "title": "Nicolas’s primorial totient inequality",
            "zeros": "Every zero of the pole-cleared Riemann zeta completion lies on Re s = 1/2.",
            "arithmetic": "For every k ≥ 2, let Pₖ be the product of the first k primes.",
            "formula": "Pₖ / φ(Pₖ) > eᵞ log log Pₖ.",
            "note": "φ is Euler’s totient function.",
            "links": [
              [
                "Nicolas’s primorial totient inequality source",
                "https://www.sciencedirect.com/science/article/pii/0022314X83900550"
              ]
            ]
          },
          {
            "title": "Ordinary prime-counting error",
            "zeros": "Every zero of the pole-cleared Riemann zeta completion lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|π(x) − Li(x)| ≤ C√x log x.",
            "note": "π(x) counts primes p ≤ x and Li(x) = ∫₂ˣ dt / log t."
          }
        ],
        "location": {
          "subject": "the pole-cleared Riemann zeta completion",
          "remainder": "R(x) = x/2 − ∑_{pʲ ≤ x} log p (1 − pʲ/x)"
        },
        "centralOrder": 0,
        "idealField": "rational"
      },
      "url": "https://www.lmfdb.org/L/1/1/1.1/r0/0/0",
      "name": "Riemann zeta",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "ζ"
      ],
      "demo": "zeta",
      "pole": 1,
      "coef": "a(p,j) = 1",
      "completion": "s(s−1) Γℝ(s) ζ(s), up to a nonzero constant",
      "basis": "Classical zeta continuation and functional equation. Robin1984 proves the zeta case and the global prime-power multiplicity theorem.",
      "orders": "Use the individual coefficients with m=1. The alternating eta series has positive value at 1/2 and 1−√2 is negative, so ζ(1/2) ≠ 0.",
      "obligation": "The benchmark tracks the criterion, with simplicity a separate all-zero assertion."
    },
    {
      "id": "1-2e2-4.3-r1-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(i)",
            "zeros": "Every zero of the Dirichlet beta completion Λ(s, χ₄) lies on Re s = 1/2.",
            "hypothesis": "Assuming ordinary RH for ζ(s)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(i) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 4) / √(log N𝔞)].",
            "note": "σ_K(𝔞) = ∑_{𝔟 ∣ 𝔞} N𝔟, κ_K = Resₛ₌₁ ζ_K(s), and γ is Euler’s constant. ζ_{ℚ(i)} = ζ·L(s,χ₄) and κ_K = π/4.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Field on LMFDB",
                "https://www.lmfdb.org/NumberField/2.0.4.1"
              ],
              [
                "Corrected ideal Robin theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean"
              ]
            ]
          },
          {
            "title": "Prime-count imbalance modulo 4",
            "zeros": "Every zero of the Dirichlet beta completion Λ(s, χ₄) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|π(x;4,1) − π(x;4,3)| ≤ C√x log x.",
            "note": "π(x;q,a) counts primes p ≤ x with p ≡ a (mod q). This equivalence holds independently of ordinary RH."
          }
        ],
        "location": {
          "subject": "the Dirichlet beta completion Λ(s, χ₄)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} χ₄(p)ʲ log p (1 − pʲ/x)"
        },
        "centralOrder": 0,
        "idealField": "gaussian"
      },
      "url": "https://www.lmfdb.org/L/1/2e2/4.3/r1/0/0",
      "name": "Dirichlet beta",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "4.3",
        "χ₄"
      ],
      "demo": "beta",
      "pole": 0,
      "coef": "a(p,j) = χ₄(p)ʲ, with χ₄(2) = 0",
      "completion": "4ˢᐟ² Γℝ(s+1) L(s,χ₄); root number +1",
      "basis": "Primitive rank-one instance. The Dirichlet and Hecke family theorems supply the analytic criterion.",
      "orders": "Use each individual coefficient χ₄(p)ʲ log p. Pairing this self-dual function would double every zero order. Pair the terms 4k+1 and 4k+3 in the central value to prove strict positivity.",
      "obligation": "Apply the global inequality to test off-center simplicity, conditional on location."
    },
    {
      "id": "1-3-3.2-r1-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(√−3)",
            "zeros": "Every zero of the completed quadratic Dirichlet function Λ(s, χ_−3) lies on Re s = 1/2.",
            "hypothesis": "Assuming ordinary RH for ζ(s)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(√−3) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 3) / √(log N𝔞)].",
            "note": "ζ_K = ζ·L(s,χ_−3) and κ_K = π/(3√3).",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Quadratic field on LMFDB",
                "https://www.lmfdb.org/NumberField/2.0.3.1"
              ],
              [
                "Fieldwise theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean#L318"
              ]
            ]
          },
          {
            "title": "Prime-count imbalance modulo 3",
            "zeros": "Every zero of the completed quadratic Dirichlet function Λ(s, χ_−3) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|π(x;3,1) − π(x;3,2)| ≤ C√x log x.",
            "note": "π(x;q,a) counts primes p ≤ x with p ≡ a (mod q). The difference counts split primes minus inert primes in ℚ(√−3). The ramified prime 3 contributes zero.",
            "links": [
              [
                "Character on LMFDB",
                "https://www.lmfdb.org/Character/Dirichlet/3/2"
              ],
              [
                "Proof and exact local data",
                "https://github.com/kimihiro64/Robin1984/blob/gh-pages/LMFDB.md#primitive-quadratic-characters-of-conductors-3-5-and-7"
              ]
            ]
          }
        ],
        "location": {
          "subject": "the completed quadratic Dirichlet function Λ(s, χ_−3)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} χ_−3(p)ʲ log p (1 − pʲ/x)"
        },
        "centralOrder": 0,
        "idealField": "quadraticMinus3"
      },
      "url": "https://www.lmfdb.org/L/1-3-3.2-r1-0-0",
      "name": "Quadratic character 3.2",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "3.2",
        "2.0.3.1",
        "D = −3"
      ],
      "pole": 0,
      "coef": "a(p,j) = χ_−3(p)ʲ. Modulo 3, χ is +1 on 1, −1 on 2, and 0 on 0.",
      "completion": "3^(s/2) Γℝ(s+1) L(s,χ_−3); root number +1",
      "basis": "Primitive real Dirichlet character. The Lean family results supply the triangular and Gaussian criteria. The prime-count transfer and quadratic factorization are documented prose specializations.",
      "orders": "Use the individual coefficients for the global Gaussian or boundary multiplicity criterion, conditional on this character’s critical-line hypothesis. In each block 3k+1 contributes more than 3k+2. Summing these positive blocks proves L(1/2,χ_−3) > 0.",
      "obligation": "Off-center simplicity is equivalent to the multiplicity test once location holds. The exact central order is zero."
    },
    {
      "id": "1-5-5.4-r0-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(√5)",
            "zeros": "Every zero of the completed quadratic Dirichlet function Λ(s, χ_5) lies on Re s = 1/2.",
            "hypothesis": "Assuming ordinary RH for ζ(s)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(√5) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 5) / √(log N𝔞)].",
            "note": "ζ_K = ζ·L(s,χ_5) and κ_K = 2 log((1+√5)/2)/√5.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Quadratic field on LMFDB",
                "https://www.lmfdb.org/NumberField/2.2.5.1"
              ],
              [
                "Fieldwise theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean#L318"
              ]
            ]
          },
          {
            "title": "Prime-count imbalance modulo 5",
            "zeros": "Every zero of the completed quadratic Dirichlet function Λ(s, χ_5) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|(π(x;5,1) + π(x;5,4)) − (π(x;5,2) + π(x;5,3))| ≤ C√x log x.",
            "note": "π(x;q,a) counts primes p ≤ x with p ≡ a (mod q). The difference counts split primes minus inert primes in ℚ(√5). The ramified prime 5 contributes zero.",
            "links": [
              [
                "Character on LMFDB",
                "https://www.lmfdb.org/Character/Dirichlet/5/4"
              ],
              [
                "Proof and exact local data",
                "https://github.com/kimihiro64/Robin1984/blob/gh-pages/LMFDB.md#primitive-quadratic-characters-of-conductors-3-5-and-7"
              ]
            ]
          }
        ],
        "location": {
          "subject": "the completed quadratic Dirichlet function Λ(s, χ_5)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} χ_5(p)ʲ log p (1 − pʲ/x)"
        },
        "centralOrder": 0,
        "idealField": "quadraticPlus5"
      },
      "url": "https://www.lmfdb.org/L/1-5-5.4-r0-0-0",
      "name": "Quadratic character 5.4",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "5.4",
        "2.2.5.1",
        "D = 5"
      ],
      "pole": 0,
      "coef": "a(p,j) = χ_5(p)ʲ. Modulo 5, χ is +1 on 1, 4, −1 on 2, 3, and 0 on 0.",
      "completion": "5^(s/2) Γℝ(s) L(s,χ_5); root number +1",
      "basis": "Primitive real Dirichlet character. The Lean family results supply the triangular and Gaussian criteria. The prime-count transfer and quadratic factorization are documented prose specializations.",
      "orders": "Use the individual coefficients for the global Gaussian or boundary multiplicity criterion, conditional on this character’s critical-line hypothesis. For f(t) = 1/√t, convexity gives f(5k+1) − f(5k+2) > f(5k+3) − f(5k+4). Summing these positive blocks proves L(1/2,χ_5) > 0.",
      "obligation": "Off-center simplicity is equivalent to the multiplicity test once location holds. The exact central order is zero."
    },
    {
      "id": "1-7-7.6-r1-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(√−7)",
            "zeros": "Every zero of the completed quadratic Dirichlet function Λ(s, χ_−7) lies on Re s = 1/2.",
            "hypothesis": "Assuming ordinary RH for ζ(s)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(√−7) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 7) / √(log N𝔞)].",
            "note": "ζ_K = ζ·L(s,χ_−7) and κ_K = π/√7.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Quadratic field on LMFDB",
                "https://www.lmfdb.org/NumberField/2.0.7.1"
              ],
              [
                "Fieldwise theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean#L318"
              ]
            ]
          },
          {
            "title": "Prime-count imbalance modulo 7",
            "zeros": "Every zero of the completed quadratic Dirichlet function Λ(s, χ_−7) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|(π(x;7,1) + π(x;7,2) + π(x;7,4)) − (π(x;7,3) + π(x;7,5) + π(x;7,6))| ≤ C√x log x.",
            "note": "π(x;q,a) counts primes p ≤ x with p ≡ a (mod q). The difference counts split primes minus inert primes in ℚ(√−7). The ramified prime 7 contributes zero.",
            "links": [
              [
                "Character on LMFDB",
                "https://www.lmfdb.org/Character/Dirichlet/7/6"
              ],
              [
                "Proof and exact local data",
                "https://github.com/kimihiro64/Robin1984/blob/gh-pages/LMFDB.md#primitive-quadratic-characters-of-conductors-3-5-and-7"
              ]
            ]
          }
        ],
        "location": {
          "subject": "the completed quadratic Dirichlet function Λ(s, χ_−7)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} χ_−7(p)ʲ log p (1 − pʲ/x)"
        },
        "centralOrder": 0,
        "idealField": "quadraticMinus7"
      },
      "url": "https://www.lmfdb.org/L/1-7-7.6-r1-0-0",
      "name": "Quadratic character 7.6",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "7.6",
        "2.0.7.1",
        "D = −7"
      ],
      "pole": 0,
      "coef": "a(p,j) = χ_−7(p)ʲ. Modulo 7, χ is +1 on 1, 2, 4, −1 on 3, 5, 6, and 0 on 0.",
      "completion": "7^(s/2) Γℝ(s+1) L(s,χ_−7); root number +1",
      "basis": "Primitive real Dirichlet character. The Lean family results supply the triangular and Gaussian criteria. The prime-count transfer and quadratic factorization are documented prose specializations.",
      "orders": "Use the individual coefficients for the global Gaussian or boundary multiplicity criterion, conditional on this character’s critical-line hypothesis. The positive residues 1, 2, 4 pair with the larger negative residues 3, 5, 6 in each block. Summing these positive blocks proves L(1/2,χ_−7) > 0.",
      "obligation": "Off-center simplicity is equivalent to the multiplicity test once location holds. The exact central order is zero."
    },
    {
      "id": "1-7-7.2-r0-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(ζ₇)⁺",
            "zeros": "Every zero of the completion Λ(s, χ₇.2) lies on Re s = 1/2.",
            "hypothesis": "Assuming ordinary RH for ζ(s)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(ζ₇)⁺ with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 49) / √(log N𝔞)].",
            "note": "ζ_K = ζ·L(s,χ₇.₂)·L(s,χ₇.₄). Here κ_K = Resₛ₌₁ ζ_K(s). The two characters in this pair have equivalent location hypotheses by conjugation.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Number field on LMFDB",
                "https://www.lmfdb.org/NumberField/3.3.49.1"
              ],
              [
                "Fieldwise theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean#L318"
              ]
            ]
          },
          {
            "title": "Weighted prime counts for character 7.2",
            "zeros": "Every zero of the completion Λ(s, χ₇.2) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|(π₁ + π₆) + ω(π₃ + π₄) + ω²(π₂ + π₅)| ≤ C√x log x.",
            "note": "πₐ = π(x;7,a) counts primes p ≤ x in the residue class a. ω = exp(2πi/3). The prime 7 contributes zero. The conjugate character has the same absolute value.",
            "links": [
              [
                "Exact character on LMFDB",
                "https://www.lmfdb.org/Character/Dirichlet/7/2"
              ],
              [
                "Local factors and proof",
                "https://github.com/kimihiro64/Robin1984/blob/gh-pages/LMFDB.md#complex-primitive-characters-modulo-7"
              ]
            ]
          }
        ],
        "location": {
          "subject": "the completion Λ(s, χ₇.2)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} 2 Re(χ₇.2(p)ʲ) log p (1 − pʲ/x)",
          "note": "The paired triangular remainder tests both characters jointly. Their individual location assertions are equivalent by conjugation."
        },
        "individual": "R(x) = −∑_{pʲ ≤ x} χ₇.2(p)ʲ log p (1 − pʲ/x)",
        "centralOrder": 0,
        "idealField": "realCyclotomic7"
      },
      "url": "https://www.lmfdb.org/L/1-7-7.2-r0-0-0",
      "name": "Order-three character 7.2",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "7.2"
      ],
      "dual": "1-7-7.4-r0-0-0",
      "pole": 0,
      "coef": "a(p,j) = χ₇.2(p)ʲ. For residues 1, 2, 3, 4, 5, 6, the exponents of ξ = exp(πi/3) are 0, 4, 2, 2, 4, 0. At 7 the coefficient is zero.",
      "completion": "7^(s/2) Γℝ(s) L(s,χ₇.2); ε = τ(χ₇.2)/(√7), with τ the character Gauss sum",
      "basis": "Exact Conrey coefficients give the location and multiplicity inputs to the Dirichlet family results. The prime-count and corrected-ideal specializations are proved in the research notes.",
      "orders": "Use the individual complex coefficients. For f(u) = u⁻¹ᐟ², strict convexity gives f(7k+2)+f(7k+5) > f(7k+3)+f(7k+4) for every k ≥ 0. The imaginary parts of the blocks of L(1/2) are all strictly of one sign. Conjugation reverses this sign and proves nonvanishing for both characters.",
      "obligation": "Once location holds, the individual multiplicity test is equivalent to simplicity of the noncentral zeros."
    },
    {
      "id": "1-7-7.3-r1-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(ζ₇)",
            "zeros": "Every zero of the completion Λ(s, χ₇.3) lies on Re s = 1/2.",
            "hypothesis": "Assuming Dedekind RH for ℚ(ζ₇)⁺ and the critical-line hypothesis for character 7.6",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(ζ₇) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 16807) / √(log N𝔞)].",
            "note": "ζ_K = ζ_{ℚ(ζ₇)⁺}·L(s,χ₇.₆)·L(s,χ₇.₃)·L(s,χ₇.₅). Here κ_K = Resₛ₌₁ ζ_K(s). The two characters in this pair have equivalent location hypotheses by conjugation.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Number field on LMFDB",
                "https://www.lmfdb.org/NumberField/6.0.16807.1"
              ],
              [
                "Fieldwise theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean#L318"
              ]
            ]
          },
          {
            "title": "Weighted prime counts for character 7.3",
            "zeros": "Every zero of the completion Λ(s, χ₇.3) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|(π₁ − π₆) + ξ(π₃ − π₄) + ξ²(π₂ − π₅)| ≤ C√x log x.",
            "note": "πₐ = π(x;7,a) counts primes p ≤ x in the residue class a. ξ = exp(πi/3). The prime 7 contributes zero. The conjugate character has the same absolute value.",
            "links": [
              [
                "Exact character on LMFDB",
                "https://www.lmfdb.org/Character/Dirichlet/7/3"
              ],
              [
                "Local factors and proof",
                "https://github.com/kimihiro64/Robin1984/blob/gh-pages/LMFDB.md#complex-primitive-characters-modulo-7"
              ]
            ]
          }
        ],
        "location": {
          "subject": "the completion Λ(s, χ₇.3)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} 2 Re(χ₇.3(p)ʲ) log p (1 − pʲ/x)",
          "note": "The paired triangular remainder tests both characters jointly. Their individual location assertions are equivalent by conjugation."
        },
        "individual": "R(x) = −∑_{pʲ ≤ x} χ₇.3(p)ʲ log p (1 − pʲ/x)",
        "centralOrder": 0,
        "idealField": "cyclotomic7"
      },
      "url": "https://www.lmfdb.org/L/1-7-7.3-r1-0-0",
      "name": "Order-six character 7.3",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "7.3"
      ],
      "dual": "1-7-7.5-r1-0-0",
      "pole": 0,
      "coef": "a(p,j) = χ₇.3(p)ʲ. For residues 1, 2, 3, 4, 5, 6, the exponents of ξ = exp(πi/3) are 0, 2, 1, 4, 5, 3. At 7 the coefficient is zero.",
      "completion": "7^(s/2) Γℝ(s+1) L(s,χ₇.3); ε = τ(χ₇.3)/(i√7), with τ the character Gauss sum",
      "basis": "Exact Conrey coefficients give the location and multiplicity inputs to the Dirichlet family results. The prime-count and corrected-ideal specializations are proved in the research notes.",
      "orders": "Use the individual complex coefficients. Each difference f(7k+2)−f(7k+5) and f(7k+3)−f(7k+4) is positive for f(u) = u⁻¹ᐟ² and every k ≥ 0. The imaginary parts of the blocks of L(1/2) are all strictly of one sign. Conjugation reverses this sign and proves nonvanishing for both characters.",
      "obligation": "Once location holds, the individual multiplicity test is equivalent to simplicity of the noncentral zeros."
    },
    {
      "id": "1-7-7.4-r0-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(ζ₇)⁺",
            "zeros": "Every zero of the completion Λ(s, χ₇.4) lies on Re s = 1/2.",
            "hypothesis": "Assuming ordinary RH for ζ(s)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(ζ₇)⁺ with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 49) / √(log N𝔞)].",
            "note": "ζ_K = ζ·L(s,χ₇.₂)·L(s,χ₇.₄). Here κ_K = Resₛ₌₁ ζ_K(s). The two characters in this pair have equivalent location hypotheses by conjugation.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Number field on LMFDB",
                "https://www.lmfdb.org/NumberField/3.3.49.1"
              ],
              [
                "Fieldwise theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean#L318"
              ]
            ]
          },
          {
            "title": "Weighted prime counts for character 7.4",
            "zeros": "Every zero of the completion Λ(s, χ₇.4) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|(π₁ + π₆) + ω²(π₃ + π₄) + ω(π₂ + π₅)| ≤ C√x log x.",
            "note": "πₐ = π(x;7,a) counts primes p ≤ x in the residue class a. ω = exp(2πi/3). The prime 7 contributes zero. The conjugate character has the same absolute value.",
            "links": [
              [
                "Exact character on LMFDB",
                "https://www.lmfdb.org/Character/Dirichlet/7/4"
              ],
              [
                "Local factors and proof",
                "https://github.com/kimihiro64/Robin1984/blob/gh-pages/LMFDB.md#complex-primitive-characters-modulo-7"
              ]
            ]
          }
        ],
        "location": {
          "subject": "the completion Λ(s, χ₇.4)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} 2 Re(χ₇.4(p)ʲ) log p (1 − pʲ/x)",
          "note": "The paired triangular remainder tests both characters jointly. Their individual location assertions are equivalent by conjugation."
        },
        "individual": "R(x) = −∑_{pʲ ≤ x} χ₇.4(p)ʲ log p (1 − pʲ/x)",
        "centralOrder": 0,
        "idealField": "realCyclotomic7"
      },
      "url": "https://www.lmfdb.org/L/1-7-7.4-r0-0-0",
      "name": "Order-three character 7.4",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "7.4"
      ],
      "dual": "1-7-7.2-r0-0-0",
      "pole": 0,
      "coef": "a(p,j) = χ₇.4(p)ʲ. For residues 1, 2, 3, 4, 5, 6, the exponents of ξ = exp(πi/3) are 0, 2, 4, 4, 2, 0. At 7 the coefficient is zero.",
      "completion": "7^(s/2) Γℝ(s) L(s,χ₇.4); ε = τ(χ₇.4)/(√7), with τ the character Gauss sum",
      "basis": "Exact Conrey coefficients give the location and multiplicity inputs to the Dirichlet family results. The prime-count and corrected-ideal specializations are proved in the research notes.",
      "orders": "Use the individual complex coefficients. For f(u) = u⁻¹ᐟ², strict convexity gives f(7k+2)+f(7k+5) > f(7k+3)+f(7k+4) for every k ≥ 0. The imaginary parts of the blocks of L(1/2) are all strictly of one sign. Conjugation reverses this sign and proves nonvanishing for both characters.",
      "obligation": "Once location holds, the individual multiplicity test is equivalent to simplicity of the noncentral zeros."
    },
    {
      "id": "1-7-7.5-r1-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(ζ₇)",
            "zeros": "Every zero of the completion Λ(s, χ₇.5) lies on Re s = 1/2.",
            "hypothesis": "Assuming Dedekind RH for ℚ(ζ₇)⁺ and the critical-line hypothesis for character 7.6",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(ζ₇) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 16807) / √(log N𝔞)].",
            "note": "ζ_K = ζ_{ℚ(ζ₇)⁺}·L(s,χ₇.₆)·L(s,χ₇.₃)·L(s,χ₇.₅). Here κ_K = Resₛ₌₁ ζ_K(s). The two characters in this pair have equivalent location hypotheses by conjugation.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Number field on LMFDB",
                "https://www.lmfdb.org/NumberField/6.0.16807.1"
              ],
              [
                "Fieldwise theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean#L318"
              ]
            ]
          },
          {
            "title": "Weighted prime counts for character 7.5",
            "zeros": "Every zero of the completion Λ(s, χ₇.5) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|(π₁ − π₆) + ξ⁵(π₃ − π₄) + ξ⁴(π₂ − π₅)| ≤ C√x log x.",
            "note": "πₐ = π(x;7,a) counts primes p ≤ x in the residue class a. ξ = exp(πi/3). The prime 7 contributes zero. The conjugate character has the same absolute value.",
            "links": [
              [
                "Exact character on LMFDB",
                "https://www.lmfdb.org/Character/Dirichlet/7/5"
              ],
              [
                "Local factors and proof",
                "https://github.com/kimihiro64/Robin1984/blob/gh-pages/LMFDB.md#complex-primitive-characters-modulo-7"
              ]
            ]
          }
        ],
        "location": {
          "subject": "the completion Λ(s, χ₇.5)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} 2 Re(χ₇.5(p)ʲ) log p (1 − pʲ/x)",
          "note": "The paired triangular remainder tests both characters jointly. Their individual location assertions are equivalent by conjugation."
        },
        "individual": "R(x) = −∑_{pʲ ≤ x} χ₇.5(p)ʲ log p (1 − pʲ/x)",
        "centralOrder": 0,
        "idealField": "cyclotomic7"
      },
      "url": "https://www.lmfdb.org/L/1-7-7.5-r1-0-0",
      "name": "Order-six character 7.5",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "7.5"
      ],
      "dual": "1-7-7.3-r1-0-0",
      "pole": 0,
      "coef": "a(p,j) = χ₇.5(p)ʲ. For residues 1, 2, 3, 4, 5, 6, the exponents of ξ = exp(πi/3) are 0, 4, 5, 2, 1, 3. At 7 the coefficient is zero.",
      "completion": "7^(s/2) Γℝ(s+1) L(s,χ₇.5); ε = τ(χ₇.5)/(i√7), with τ the character Gauss sum",
      "basis": "Exact Conrey coefficients give the location and multiplicity inputs to the Dirichlet family results. The prime-count and corrected-ideal specializations are proved in the research notes.",
      "orders": "Use the individual complex coefficients. Each difference f(7k+2)−f(7k+5) and f(7k+3)−f(7k+4) is positive for f(u) = u⁻¹ᐟ² and every k ≥ 0. The imaginary parts of the blocks of L(1/2) are all strictly of one sign. Conjugation reverses this sign and proves nonvanishing for both characters.",
      "obligation": "Once location holds, the individual multiplicity test is equivalent to simplicity of the noncentral zeros."
    },
    {
      "id": "1-5-5.2-r1-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(ζ₅)",
            "zeros": "Every zero of the completion Λ(s, χ₅.₂) lies on Re s = 1/2.",
            "hypothesis": "Assuming Dedekind RH for ℚ(√5)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(ζ₅) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 125) / √(log N𝔞)].",
            "note": "σ_K(𝔞) = ∑_{𝔟 ∣ 𝔞} N𝔟, κ_K = Resₛ₌₁ ζ_K(s), and γ is Euler’s constant. ζ_{ℚ(ζ₅)} = ζ_{ℚ(√5)}·L(s,χ₅.₂)·L(s,χ₅.₃). Conjugation makes the two quartic location assertions equivalent.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Field on LMFDB",
                "https://www.lmfdb.org/NumberField/4.0.125.1"
              ],
              [
                "Corrected ideal Robin theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean"
              ]
            ]
          },
          {
            "title": "Two prime-count imbalances modulo 5",
            "zeros": "Every zero of the completion Λ(s, χ₅.₂) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "√[(π₁(x) − π₄(x))² + (π₂(x) − π₃(x))²] ≤ C√x log x.",
            "note": "πₐ(x) counts primes p ≤ x with p ≡ a (mod 5). The real and imaginary discrepancies come from the individual quartic character, and the norm is the same for its dual."
          }
        ],
        "location": {
          "subject": "the completion Λ(s, χ₅.₂)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} 2 Re(χ₅.₂(p)ʲ) log p (1 − pʲ/x)",
          "note": "The paired remainder tests the character and its conjugate jointly. Their individual location assertions are equivalent by conjugation."
        },
        "individual": "R(x) = −∑_{pʲ ≤ x} χ₅.₂(p)ʲ log p (1 − pʲ/x)",
        "centralOrder": 0,
        "idealField": "cyclotomic5"
      },
      "url": "https://www.lmfdb.org/L/1/5/5.2/r1/0/0",
      "name": "Quartic character 5.2",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "5.2",
        "modulus 5"
      ],
      "demo": "quartic",
      "pole": 0,
      "dual": "1-5-5.3-r1-0-0",
      "coef": "a(p,j) = χ(p)ʲ; pair coefficient 2 Re a(p,j)",
      "completion": "5ˢᐟ² Γℝ(s+1) L(s,χ), reflected to the dual",
      "basis": "The pair tests both characters. Conjugation across the real axis makes their location assertions equivalent, so it also tests this individual entry.",
      "orders": "Keep the complex coefficients for this character, separate from its dual. The real part at 1/2 is the positive sum of (5k+1)⁻¹ᐟ² − (5k+4)⁻¹ᐟ².",
      "obligation": "Use the individual signal for orders at each signed ordinate."
    },
    {
      "id": "1-5-5.3-r1-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ(ζ₅)",
            "zeros": "Every zero of the completion Λ(s, χ₅.₃) lies on Re s = 1/2.",
            "hypothesis": "Assuming Dedekind RH for ℚ(√5)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ(ζ₅) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 125) / √(log N𝔞)].",
            "note": "σ_K(𝔞) = ∑_{𝔟 ∣ 𝔞} N𝔟, κ_K = Resₛ₌₁ ζ_K(s), and γ is Euler’s constant. ζ_{ℚ(ζ₅)} = ζ_{ℚ(√5)}·L(s,χ₅.₂)·L(s,χ₅.₃). Conjugation makes the two quartic location assertions equivalent.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Field on LMFDB",
                "https://www.lmfdb.org/NumberField/4.0.125.1"
              ],
              [
                "Corrected ideal Robin theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean"
              ]
            ]
          },
          {
            "title": "Two prime-count imbalances modulo 5",
            "zeros": "Every zero of the completion Λ(s, χ₅.₃) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "√[(π₁(x) − π₄(x))² + (π₂(x) − π₃(x))²] ≤ C√x log x.",
            "note": "πₐ(x) counts primes p ≤ x with p ≡ a (mod 5). The real and imaginary discrepancies come from the individual quartic character, and the norm is the same for its dual."
          }
        ],
        "location": {
          "subject": "the completion Λ(s, χ₅.₃)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} 2 Re(χ₅.₃(p)ʲ) log p (1 − pʲ/x)",
          "note": "The paired remainder tests the character and its conjugate jointly. Their individual location assertions are equivalent by conjugation."
        },
        "individual": "R(x) = −∑_{pʲ ≤ x} χ₅.₃(p)ʲ log p (1 − pʲ/x)",
        "centralOrder": 0,
        "idealField": "cyclotomic5"
      },
      "url": "https://www.lmfdb.org/L/1/5/5.3/r1/0/0",
      "name": "Quartic character 5.3",
      "family": "Zeta & Dirichlet",
      "degree": 1,
      "status": "done",
      "proof": "Lean provider",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "dirichlet",
      "origins": [
        "5.3",
        "modulus 5"
      ],
      "demo": "quartic",
      "pole": 0,
      "dual": "1-5-5.2-r1-0-0",
      "coef": "a(p,j) = χ̄(p)ʲ; pair coefficient 2 Re a(p,j)",
      "completion": "5ˢᐟ² Γℝ(s+1) L(s,χ̄), reflected to the dual",
      "basis": "Conjugate of 5.2. Distinct LMFDB entry and individual multiplicity signal, with the same location sum.",
      "orders": "Use the conjugate complex coefficients. The same positive real part proves central order zero.",
      "obligation": "The paired location sum contains no information distinguishing the two individual orders."
    },
    {
      "id": "2-23-23.22-c0-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ[T]/(T³ − T − 1)",
            "zeros": "Every zero of the completion of the level-23 weight-one L-function lies on Re s = 1/2.",
            "hypothesis": "Assuming ordinary RH for ζ(s)",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ[T]/(T³ − T − 1) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 23) / √(log N𝔞)].",
            "note": "σ_K(𝔞) = ∑_{𝔟 ∣ 𝔞} N𝔟, κ_K = Resₛ₌₁ ζ_K(s), and γ is Euler’s constant. The identity ζ_K = ζ·L(s,f) isolates the weight-one factor under this assumption.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Field on LMFDB",
                "https://www.lmfdb.org/NumberField/3.1.23.1"
              ],
              [
                "Corrected ideal Robin theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean"
              ]
            ]
          },
          {
            "title": "Split-versus-inert prime imbalance",
            "zeros": "Every zero of the completion of the level-23 weight-one L-function lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|2π_split(x) − π_inert(x)| ≤ C√x log x.",
            "note": "Among primes p ≤ x other than 23, π_split counts those for which T³−T−1 has three roots in 𝔽ₚ and π_inert counts those with no roots. A prime with one root contributes zero."
          }
        ],
        "location": {
          "subject": "the completion of the level-23 weight-one L-function",
          "remainder": "R(x) = −∑_{pʲ ≤ x} a₂₃(p,j) log p (1 − pʲ/x)"
        },
        "centralOrder": 0,
        "idealField": "cubic23"
      },
      "url": "https://www.lmfdb.org/L/2/23/23.22/c0/0/0",
      "name": "Level 23 weight-one form",
      "family": "Classical newforms",
      "degree": 2,
      "status": "done",
      "proof": "Prose specialization",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "newforms",
      "origins": [
        "23.1.b.a",
        "2.23.3t2.b.a",
        "3.1.23.1"
      ],
      "demo": "s3",
      "pole": 0,
      "coef": "a(p,j) = #Fix(Frobₚʲ) − 1 for p ≠ 23; a(23,j) = 1",
      "completion": "23ˢᐟ² Γℂ(s) L(s,f); root number +1",
      "basis": "Serre identifies the L-function of η(z)η(23z) with the standard S₃ Artin factor of the −23 cubic zeta. Dihedral induction also realizes it as a finite-order Hecke L-function.",
      "orders": "Use the undoubled Frobenius trace coefficient. η(it)η(23it) > 0 and the positive Mellin integral prove central order zero.",
      "obligation": "In Lean, identify the actual cubic prime factors and the induced Hecke L-function with this catalogued object.",
      "sources": [
        [
          "Serre’s factorization",
          "https://www.college-de-france.fr/media/jean-pierre-serre/UPL1210350903026534135_on_a_theorem_of_Jordan.pdf"
        ]
      ]
    },
    {
      "id": "3.1.23.1",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Robin1984 corrected ideal criterion for ℚ[T]/(T³ − T − 1)",
            "zeros": "Every zero of the pole-cleared ζ_K completion lies on Re s = 1/2, equivalently both ζ and the level-23 form satisfy their critical-line hypotheses.",
            "arithmetic": "There exists A_K ∈ ℕ such that the following holds for every nonzero integral ideal 𝔞 of K = ℚ[T]/(T³ − T − 1) with N𝔞 ≥ A_K.",
            "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log 23) / √(log N𝔞)].",
            "note": "σ_K(𝔞) = ∑_{𝔟 ∣ 𝔞} N𝔟, κ_K = Resₛ₌₁ ζ_K(s), and γ is Euler’s constant. The field is generated by a root of T³−T−1.",
            "links": [
              [
                "Robin1984 corrected ideal theorem",
                "#corrected-ideal-robin"
              ],
              [
                "Field on LMFDB",
                "https://www.lmfdb.org/NumberField/3.1.23.1"
              ],
              [
                "Corrected ideal Robin theorem in Lean",
                "https://github.com/kimihiro64/Robin1984/blob/main/Solution.lean"
              ]
            ]
          },
          {
            "title": "Prime-ideal counting error",
            "zeros": "Every zero of the pole-cleared Dedekind zeta completion for the cubic field K lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|π_K(x) − Li(x)| ≤ C√x log x.",
            "note": "π_K(x) counts each prime ideal 𝔭 with absolute norm N𝔭 ≤ x, and Li(x) = ∫₂ˣ dt / log t."
          }
        ],
        "location": {
          "subject": "the pole-cleared Dedekind zeta completion for the cubic field K",
          "remainder": "R(x) = x/2 − ∑_{(N𝔭)ʲ ≤ x} log(N𝔭) (1 − (N𝔭)ʲ/x)."
        },
        "centralOrder": 0,
        "idealField": "cubic23"
      },
      "url": "https://www.lmfdb.org/NumberField/3.1.23.1",
      "name": "Cubic field of discriminant −23",
      "family": "Dedekind zeta",
      "degree": 3,
      "status": "done",
      "proof": "Prose specialization",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "origins": [
        "x³−x−1",
        "S₃ cubic",
        "23.1.b.a"
      ],
      "demo": "cubic",
      "pole": 1,
      "coef": "a(p,j) = 1 + a₂₃(p,j); equivalently sum f over prime ideals above p with f dividing j",
      "completion": "s(s−1)·23ˢᐟ² Γℝ(s) Γℂ(s) ζₖ(s)",
      "basis": "ζₖ=ζ L(f). Corrected ideal Robin with correction numerator 12+3 log 23 is equivalent to RH for both factors jointly.",
      "orders": "Use prime-ideal weights or the aggregate rational-prime coefficients. Orders from ζ and L(f) add. Both central factors are nonzero.",
      "obligation": "The field label is tracked as an origin for this Dedekind zeta. Match a canonical L-function label if one is confirmed."
    },
    {
      "id": "2-1-1.1-c11-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Cancellation in Ramanujan’s τ at primes",
            "zeros": "Every zero of the unitary completion of L(s, Δ) lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|∑_{p ≤ x} τ(p)| ≤ C x⁶ log x.",
            "note": "τ(p) is the pth coefficient of Δ = q∏ₙ₌₁∞(1−qⁿ)²⁴. The unitary first coefficient is τ(p)/p¹¹ᐟ²."
          },
          {
            "title": "Joint second moment of 1 + normalized τ",
            "zeros": "The pole-cleared ζ completion, the unitary Δ completion, and the unitary symmetric-square completion of Δ all have their zeros on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|∑_{p ≤ x} (1 + τ(p)/p¹¹ᐟ²)² − 2 Li(x)| ≤ C√x log x.",
            "note": "This tests ζ² L(s,Δ)² L(s,Sym²Δ). The squared coefficient is the first log-derivative coefficient of that product, before multiplication by log p."
          }
        ],
        "location": {
          "subject": "the unitary completion of L(s, Δ)",
          "remainder": "R(x) = −∑_{pʲ ≤ x} aΔ(p,j) log p (1 − pʲ/x)"
        },
        "centralOrder": 0,
        "additional": [
          {
            "title": "Δ and its symmetric square",
            "zeros": "The pole-cleared ζ completion, the unitary Δ completion, and the unitary symmetric-square completion of Δ all have their zeros on Re s = 1/2.",
            "arithmetic": "There exist C > 0 and X ≥ 1 such that for every real x ≥ X:",
            "formula": "∑_{p ≤ x} (1 + τ(p)/p¹¹ᐟ²)² log p (1 − p/x) ≥ x − C√x.",
            "note": "This prose consequence uses ζ² L(Δ)² L(Sym² Δ). The omitted higher prime powers contribute O(√x)."
          }
        ]
      },
      "url": "https://www.lmfdb.org/L/2/1/1.1/c11/0/0",
      "name": "Ramanujan’s Δ",
      "family": "Classical newforms",
      "degree": 2,
      "status": "done",
      "proof": "Prose specialization",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "newforms",
      "origins": [
        "1.12.a.a",
        "tau",
        "symmetric powers"
      ],
      "pole": 0,
      "coef": "a(p,0)=2, a(p,1)=τ(p)/p¹¹ᐟ², a(p,j+1)=a(p,1)a(p,j)−a(p,j−1)",
      "completion": "Γℂ(s+11/2) Lᵤ(s,Δ); root number +1",
      "basis": "The level-one normalized cusp form supplies all local factors and its Mellin completion. No finite primes are ramified.",
      "orders": "Use the individual trace recurrence above. The positive Mellin integral of η(it)²⁴ at arithmetic s=6 proves central order zero.",
      "idealAssessment": "At p = 2 the unitary trace is −24/2^(11/2), with square 9/32. This trace cannot be an algebraic integer, so an identification as a factor of a Dedekind zeta function at every prime is impossible. An indirect transfer remains open.",
      "obligation": "Formalize the level-one form’s analytic completion and its Euler identification with the concrete coefficients.",
      "sources": [
        [
          "Newton–Thorne symmetric powers",
          "https://arxiv.org/abs/1912.11261"
        ]
      ]
    },
    {
      "id": "2-37-1.1-c1-0-1",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Total point-count error for 37.a1",
            "zeros": "Every zero of the unitary Hasse–Weil completion of 37.a1 lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|∑_{p ≤ x, p ≠ 37} (#E(𝔽ₚ) − p − 1)| ≤ C x log x.",
            "note": "E is the projective completion of y² + y = x³ − x. Count the point at infinity in #E(𝔽ₚ)."
          }
        ],
        "location": {
          "subject": "the unitary Hasse–Weil completion of 37.a1",
          "remainder": "R(x) = −∑_{pʲ ≤ x} a₃₇(p,j) log p (1 − pʲ/x)",
          "note": "The unitary line Re s = 1/2 corresponds to Re s = 1 in arithmetic normalization."
        },
        "centralOrder": 1
      },
      "url": "https://www.lmfdb.org/L/2/37/1.1/c1/0/1",
      "name": "Elliptic curve 37.a1",
      "family": "Elliptic curves",
      "degree": 2,
      "status": "done",
      "proof": "Prose specialization",
      "multiplicity": "applied",
      "center": "Order 1 proved",
      "cohort": "newforms",
      "origins": [
        "37.a1",
        "37.2.a.a"
      ],
      "demo": "curve37",
      "pole": 0,
      "coef": "Good p: roots of T² − (aₚ/√p)T + 1. At p=37: a(37,j) = (−1/√37)ʲ.",
      "completion": "37ˢᐟ² Γℂ(s+1/2) Lᵤ(s,E); root number −1",
      "basis": "Modularity identifies the Hasse–Weil function with the weight-two form. At good primes aₚ=p+1−#E(Fₚ). The rank-one Euler factor at 37 is retained.",
      "orders": "The Fricke sign forces a central zero. A q-expansion tail bound gives a positive Mellin derivative, proving exact order one. Use J={0}, d(0)=1 in the individual signal.",
      "idealAssessment": "At p = 5 the unitary trace is −2/√5, with square 4/5. This trace cannot be an algebraic integer, so an identification as a factor of a Dedekind zeta function at every prime is impossible. An indirect transfer remains open.",
      "obligation": "The arithmetic criterion for exact order 1 is separate from the location bound.",
      "sources": [
        [
          "Modularity of elliptic curves",
          "https://math.stanford.edu/~conrad/papers/tswfinal.pdf"
        ]
      ]
    },
    {
      "id": "4-277-1.1-c1e2-0-0",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Total curve point-count error for 277.a",
            "zeros": "Every zero of the unitary degree-four spin completion of the Jacobian of 277.a.277.1 lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|∑_{p ≤ x, p ≠ 277} (#C(𝔽ₚ) − p − 1)| ≤ C x log x.",
            "note": "Take the smooth projective model of y² + (x³ + x² + x + 1)y = −x² − x, with LMFDB label 277.a.277.1. The L-function is that of its Jacobian."
          }
        ],
        "location": {
          "subject": "the unitary degree-four spin completion of the Jacobian of 277.a.277.1",
          "remainder": "R(x) = −∑_{pʲ ≤ x} a₂₇₇(p,j) log p (1 − pʲ/x)",
          "note": "The unitary line Re s = 1/2 corresponds to Re s = 1 in arithmetic normalization."
        },
        "centralOrder": 0
      },
      "url": "https://www.lmfdb.org/L/4/277/1.1/c1e2/0/0",
      "name": "Genus-two Jacobian 277.a",
      "family": "Genus two",
      "degree": 4,
      "status": "done",
      "proof": "Prose specialization",
      "multiplicity": "applied",
      "center": "Order 0 proved",
      "cohort": "genus2",
      "origins": [
        "277.a.277.1",
        "paramodular spin"
      ],
      "pole": 0,
      "coef": "a(p,j) = Σ αₚ,ₖʲ from the unitary polynomial Pₚ(T/√p). At 277 use (1+T)(1−8T+277T²) before that substitution.",
      "completion": "277ˢᐟ² Γℂ(s+1/2)² Lᵤ(s); root number +1",
      "basis": "Brumer–Pacetti–Poor–Tornaría–Voight–Yuen prove all local factors match the paramodular spin form with a cuspidal degree-four transfer.",
      "orders": "An explicit Bessel kernel bound from the Euler coefficients proves central nonvanishing. Use the individual coefficients and J={0}, d(0)=0 to test the prescribed central order and off-center simplicity.",
      "idealAssessment": "At p = 3 the unitary trace is −1/√3, with square 1/3. This trace cannot be an algebraic integer, so an identification as a factor of a Dedekind zeta function at every prime is impossible. An indirect transfer remains open.",
      "obligation": "The public Lean interfaces still need the concrete spin completion and exact local-factor identification.",
      "sources": [
        [
          "Paramodularity, Theorem 7.1.3",
          "https://msp.org/ant/2019/13-5/ant-v13-n5-p05-p.pdf"
        ]
      ]
    },
    {
      "id": "2.4583881.120.a.b",
      "equivalences": {
        "arithmeticEndpoints": [
          {
            "title": "Cancellation in the individual Frobenius trace",
            "zeros": "Every zero and pole of Λρ lies on Re s = 1/2.",
            "arithmetic": "There is a constant C > 0 such that the following holds for every real x ≥ 2.",
            "formula": "|∑_{p ≤ x, p ≠ 2141} tr ρ(Frobₚ)| ≤ C√x log x.",
            "note": "The complex modulus tests the signed divisor of the meromorphic function. At 2141 the inertia-invariant space is zero."
          }
        ],
        "location": {
          "subject": "the meromorphic Artin completion Λρ",
          "mode": "absolute",
          "remainder": "R(x) = −∑_{pʲ ≤ x} tr(Frobₚʲ | Vᴵᵖ) log p (1 − pʲ/x)",
          "note": "The one-sided version is blocked for this label. This two-sided result uses the individual coefficients and tracks zeros and poles."
        },
        "signed": {
          "formula": "U(t,δ) = −δs ∫₁∞ B(x) x⁻ˢ⁻¹ dx, where s = 1/2 + it + δ.",
          "location": "for every real t, Re U(t,δ) > −1/2 for all sufficiently small δ > 0.",
          "simplicity": "For every real t, −1/2 < Re U(t,δ) < 3/2 for all sufficiently small δ > 0."
        }
      },
      "url": "https://www.lmfdb.org/ArtinRepresentation/2.2141e2.120.1c2",
      "name": "Even icosahedral Artin representation",
      "family": "Artin representations",
      "degree": 2,
      "status": "blocked",
      "proof": "Meromorphic alternative",
      "multiplicity": "signed",
      "center": "Signed order test",
      "origins": [
        "SL(2,5)",
        "2141²",
        "A₅ projective image"
      ],
      "pole": 0,
      "coef": "Unramified trace recurrence with determinant 1; at 2141 the inertia-invariant space is zero.",
      "completion": "4583881ˢᐟ² Γℝ(s+1)² L(s,ρ), meromorphic",
      "basis": "Brauer induction supplies a signed finite product of finite-order Hecke L-functions. The LMFDB character table gives trace −2 for complex conjugation, so both Gamma shifts are 1.",
      "orders": "Use the signed Mellin residue. Eventual real part greater than −1/2 at every central ordinate rules out poles there, once the absolute triangular bound holds.",
      "obligation": "A case-specific entire continuation or equivalent pole-sign input is needed for the ordinary one-sided transfer. No such proof was located for this label. The two-sided alternative tests combined zero and pole location."
    },
    {
      "id": "2-389-1.1-c1-0-29",
      "url": "https://www.lmfdb.org/L/2/389/1.1/c1/0/29",
      "name": "Elliptic curve 389.a1",
      "family": "Elliptic curves",
      "degree": 2,
      "status": "unreviewed",
      "proof": "Queued",
      "multiplicity": "unreviewed",
      "center": "Order 2 reported",
      "cohort": "newforms",
      "origins": [
        "389.a1",
        "389.2.a.a"
      ],
      "obligation": "Next use the weight-two provider and review the exact central-order evidence for the rank-two regression."
    },
    {
      "id": "3-1-1.1-r0e3-m0.31m20.04p20.36-0",
      "url": "https://www.lmfdb.org/L/3/1/1.1/r0e3/m0.31m20.04p20.36/0",
      "name": "Level-one GL₃ Maass entry",
      "family": "Maass forms",
      "degree": 3,
      "status": "unreviewed",
      "proof": "Queued",
      "multiplicity": "unreviewed",
      "center": "Awaiting review",
      "cohort": "maass3",
      "origins": [
        "GL₃",
        "non-self-dual"
      ],
      "obligation": "Establish the exact automorphic realization and contragredient, and distinguish numerical eigenvalue data from the inputs needed for a proof."
    }
  ],
  "correctedIdealRobin": {
    "declaration": "Robin1984.GRH.CorrectedIdealRobin",
    "formula": "σ_K(𝔞) / N𝔞 ≤ eᵞ κ_K [log log N𝔞 + (12 + 3 log |D_K|) / √(log N𝔞)].",
    "fields": {
      "rational": {
        "field": "ℚ",
        "discriminant": 1,
        "zeros": "Ordinary RH for ζ(s)."
      },
      "gaussian": {
        "field": "ℚ(i)",
        "discriminant": -4,
        "zeros": "Ordinary RH and the critical-line hypothesis for Dirichlet beta, jointly."
      },
      "quadraticMinus3": {
        "field": "ℚ(√−3)",
        "discriminant": -3,
        "zeros": "Ordinary RH and the critical-line hypothesis for the quadratic character 3.2, jointly."
      },
      "quadraticPlus5": {
        "field": "ℚ(√5)",
        "discriminant": 5,
        "zeros": "Ordinary RH and the critical-line hypothesis for the quadratic character 5.4, jointly."
      },
      "quadraticMinus7": {
        "field": "ℚ(√−7)",
        "discriminant": -7,
        "zeros": "Ordinary RH and the critical-line hypothesis for the quadratic character 7.6, jointly."
      },
      "cyclotomic5": {
        "field": "ℚ(ζ₅)",
        "discriminant": 125,
        "zeros": "Dedekind RH for ℚ(√5) and the critical-line hypotheses for both quartic characters modulo 5, jointly."
      },
      "realCyclotomic7": {
        "field": "ℚ(ζ₇)⁺",
        "discriminant": 49,
        "zeros": "Ordinary RH and the critical-line hypotheses for the two order-three characters 7.2 and 7.4, jointly."
      },
      "cyclotomic7": {
        "field": "ℚ(ζ₇)",
        "discriminant": -16807,
        "zeros": "Ordinary RH and the critical-line hypotheses for all five primitive characters modulo 7, jointly."
      },
      "cubic23": {
        "field": "ℚ[T]/(T³ − T − 1)",
        "discriminant": -23,
        "zeros": "Ordinary RH and the critical-line hypothesis for the level-23 weight-one form, jointly."
      }
    }
  }
};
