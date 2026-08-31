import Robin1984.Finite.Certificates.Row00
import Robin1984.Finite.Certificates.Row01
import Robin1984.Finite.Certificates.Row02
import Robin1984.Finite.Certificates.Row03
import Robin1984.Finite.Certificates.Row04
import Robin1984.Finite.Certificates.Row05
import Robin1984.Finite.Certificates.Row06
import Robin1984.Finite.Certificates.Row07
import Robin1984.Finite.Certificates.Row08
import Robin1984.Finite.Certificates.Row09
import Robin1984.Finite.Certificates.Row10
import Robin1984.Finite.Certificates.Row11
import Robin1984.Finite.Certificates.Row12
import Robin1984.Finite.Certificates.Row13
import Robin1984.Finite.Certificates.Row14
import Robin1984.Finite.Certificates.Row15
import Robin1984.Finite.Certificates.Row16
import Robin1984.Finite.Certificates.Row17
import Robin1984.Finite.Certificates.Row18
import Robin1984.Finite.Certificates.Row19
import Robin1984.Finite.Certificates.Row20
import Robin1984.Finite.Certificates.Row21
import Robin1984.Finite.Certificates.Row22
import Robin1984.Finite.Certificates.Row23
import Robin1984.Finite.Certificates.Row24
import Robin1984.Finite.Certificates.Row25
import Robin1984.Finite.Certificates.Row26
import Robin1984.Finite.Certificates.Row27
import Robin1984.Finite.Certificates.Row28
import Robin1984.Finite.Certificates.Row29
import Robin1984.Finite.Certificates.Row30
import Robin1984.Finite.Certificates.Row31
import Robin1984.Finite.Certificates.Row32
import Robin1984.Finite.Certificates.Row33
import Robin1984.Finite.Certificates.Row34
import Robin1984.Finite.Certificates.Row35
import Robin1984.Finite.FiniteCover
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Complete finite log-height certificate cover

`robinFiniteRows` collects the 36 rational row certificates in increasing
order. `robinFiniteRows_checks` dispatches membership in this list to the
corresponding row theorem, while `robinFiniteRows_cover` kernel-checks that
their endpoints form a gap-free chain from `336 / 25` through
`37283397387 / 500000`, beyond the analytic cutoff `74500`.

This is the aggregate certificate consumed by the finite-range proof of
Robin's inequality.
-/

namespace Robin1984

def robinFiniteRows : List RobinFiniteRow := [
  robinFiniteRow00,
  robinFiniteRow01,
  robinFiniteRow02,
  robinFiniteRow03,
  robinFiniteRow04,
  robinFiniteRow05,
  robinFiniteRow06,
  robinFiniteRow07,
  robinFiniteRow08,
  robinFiniteRow09,
  robinFiniteRow10,
  robinFiniteRow11,
  robinFiniteRow12,
  robinFiniteRow13,
  robinFiniteRow14,
  robinFiniteRow15,
  robinFiniteRow16,
  robinFiniteRow17,
  robinFiniteRow18,
  robinFiniteRow19,
  robinFiniteRow20,
  robinFiniteRow21,
  robinFiniteRow22,
  robinFiniteRow23,
  robinFiniteRow24,
  robinFiniteRow25,
  robinFiniteRow26,
  robinFiniteRow27,
  robinFiniteRow28,
  robinFiniteRow29,
  robinFiniteRow30,
  robinFiniteRow31,
  robinFiniteRow32,
  robinFiniteRow33,
  robinFiniteRow34,
  robinFiniteRow35
]

theorem robinFiniteRows_checks (r : RobinFiniteRow)
    (hr : Membership.mem robinFiniteRows r) : RobinFiniteRowChecks r := by
  simp only [robinFiniteRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  all_goals subst r
  . exact robinFiniteRow00_checks
  . exact robinFiniteRow01_checks
  . exact robinFiniteRow02_checks
  . exact robinFiniteRow03_checks
  . exact robinFiniteRow04_checks
  . exact robinFiniteRow05_checks
  . exact robinFiniteRow06_checks
  . exact robinFiniteRow07_checks
  . exact robinFiniteRow08_checks
  . exact robinFiniteRow09_checks
  . exact robinFiniteRow10_checks
  . exact robinFiniteRow11_checks
  . exact robinFiniteRow12_checks
  . exact robinFiniteRow13_checks
  . exact robinFiniteRow14_checks
  . exact robinFiniteRow15_checks
  . exact robinFiniteRow16_checks
  . exact robinFiniteRow17_checks
  . exact robinFiniteRow18_checks
  . exact robinFiniteRow19_checks
  . exact robinFiniteRow20_checks
  . exact robinFiniteRow21_checks
  . exact robinFiniteRow22_checks
  . exact robinFiniteRow23_checks
  . exact robinFiniteRow24_checks
  . exact robinFiniteRow25_checks
  . exact robinFiniteRow26_checks
  . exact robinFiniteRow27_checks
  . exact robinFiniteRow28_checks
  . exact robinFiniteRow29_checks
  . exact robinFiniteRow30_checks
  . exact robinFiniteRow31_checks
  . exact robinFiniteRow32_checks
  . exact robinFiniteRow33_checks
  . exact robinFiniteRow34_checks
  . exact robinFiniteRow35_checks

theorem robinFiniteRows_cover :
    RobinFiniteCover (336 / 25) (37283397387 / 500000) robinFiniteRows := by
  decide +kernel

end Robin1984
