import Robin1984.Analytic.PrimeProductBlocks

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Exact prime-product blocks 000-007

These 8 consecutive blocks cover the integer interval
`[0, 396)`. Each block stores the products over primes in its
interval of `p^2 - 1`, `p * (p - 1)`, and `p`.

The accompanying `decide +kernel` theorem for every block checks its size and
upper bound and recomputes all three products using the bounded primality
test. The verified blocks are later concatenated to supply the first-layer
products for the largest finite row.
-/

namespace Robin1984

def robinPrimeBlock000 : RobinPrimeProductBlock where
  start := 0
  count := 18
  numerator := 160526499840
  denominator := 47048601600
  baseProduct := 510510

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock000_checks : RobinPrimeProductBlockChecks robinPrimeBlock000 := by
  decide +kernel

def robinPrimeBlock001 : RobinPrimeProductBlock where
  start := 18
  count := 11
  numerator := 190080
  denominator := 173052
  baseProduct := 437

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock001_checks : RobinPrimeProductBlockChecks robinPrimeBlock001 := by
  decide +kernel

def robinPrimeBlock002 : RobinPrimeProductBlock where
  start := 29
  count := 18
  numerator := 3424899760128000
  denominator := 2979235241740800
  baseProduct := 58642669

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock002_checks : RobinPrimeProductBlockChecks robinPrimeBlock002 := by
  decide +kernel

def robinPrimeBlock003 : RobinPrimeProductBlock where
  start := 47
  count := 30
  numerator := 9673106229556993327104000
  denominator := 8620381316892759711897600
  baseProduct := 3113232716449

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock003_checks : RobinPrimeProductBlockChecks robinPrimeBlock003 := by
  decide +kernel

def robinPrimeBlock004 : RobinPrimeProductBlock where
  start := 77
  count := 44
  numerator := 601731624334985396978343896678400000
  denominator := 548434058992861157328881671549747200
  baseProduct := 776093850365240417

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock004_checks : RobinPrimeProductBlockChecks robinPrimeBlock004 := by
  decide +kernel

def robinPrimeBlock005 : RobinPrimeProductBlock where
  start := 121
  count := 64
  numerator := 29139543909607388291344386512580055590449971200000000
  denominator := 26940680320947695790881845886666693252461254574080000
  baseProduct := 170747768525029167262956271

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock005_checks : RobinPrimeProductBlockChecks robinPrimeBlock005 := by
  decide +kernel

def robinPrimeBlock006 : RobinPrimeProductBlock where
  start := 185
  count := 90
  numerator := 3441055422298317985962011876623554667740731792871796263119486976000000000000
  denominator := 3208199148311804243338162563207354693202753217287616688671405050429440000000
  baseProduct := 58669672700730402561167463176047360583

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock006_checks : RobinPrimeProductBlockChecks robinPrimeBlock006 := by
  decide +kernel

def robinPrimeBlock007 : RobinPrimeProductBlock where
  start := 275
  count := 121
  numerator := 654481494117079119454072982862431884532357299373035397132155726958108309950552428930662400000000
  denominator := 617953753725743606382279190868069932396194925565484009765220647173582852199348838847528042496000
  baseProduct := 809071570100634918731540230003790633463788552651

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock007_checks : RobinPrimeProductBlockChecks robinPrimeBlock007 := by
  decide +kernel

end Robin1984
