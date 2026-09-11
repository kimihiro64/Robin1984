import Robin1984.Lagarias.FiniteCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001) supplies the finite range.
- Formalization note: Generated exact factor and rational certificate data.
- PROVENANCE-END
-/

/-! # Lagarias finite certificate packet 03 -/

namespace Robin1984

def lagariasFiniteBlock39 : LagariasFiniteBlock where
  first := 2520
  sigmaBound := 9360
  harmonicLower := (3772514591798568749163700398237908590878615261118994074073607187540040006740837954543088560627258225721387566340327810200674912531549787770550477758785300999890600738861024085756843140548164323166422467258458295467 / 448616246971288039752649573894899215350321144577351242906115506289526510410468717976023470703322326738185640815486203348278409561843768982573391292454952354309987621063345521551593505523971131733000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 360
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock39_harmonicLower_le :
    (lagariasFiniteBlock39.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock39.first : Real) := by
  change (((3772514591798568749163700398237908590878615261118994074073607187540040006740837954543088560627258225721387566340327810200674912531549787770550477758785300999890600738861024085756843140548164323166422467258458295467 / 448616246971288039752649573894899215350321144577351242906115506289526510410468717976023470703322326738185640815486203348278409561843768982573391292454952354309987621063345521551593505523971131733000000000000000000) : Rat) : Real) <=     (harmonic 2520 : Real)
  have hLog :
      (11 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((315 / 256) : Rat)           32 : Real) <=
        Real.log (2520 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (2520 : Real))
      (q := ((315 / 256) : Rat))
      (r := ((315 / 256) : Rat))
      11 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((3772514591798568749163700398237908590878615261118994074073607187540040006740837954543088560627258225721387566340327810200674912531549787770550477758785300999890600738861024085756843140548164323166422467258458295467 / 448616246971288039752649573894899215350321144577351242906115506289526510410468717976023470703322326738185640815486203348278409561843768982573391292454952354309987621063345521551593505523971131733000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((11 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((315 / 256) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock39_analyticValid : lagariasFiniteBlock39.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock39
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock39_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock39.first lagariasFiniteBlock39.sigmaBound
        lagariasFiniteBlock39.count = true := by
  unfold lagariasFiniteBlock39
  decide +kernel

theorem lagariasFiniteBlock39_valid : lagariasFiniteBlock39.Valid :=
  And.intro lagariasFiniteBlock39_analyticValid lagariasFiniteBlock39_rangeValid

def lagariasFiniteBlock40 : LagariasFiniteBlock where
  first := 2880
  sigmaBound := 10890
  harmonicLower := (445323005121812189840709792678020780538988187834985820360651717445631921705511215829003343774672113630797978792172360606164520517568281606523174063294698403067 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 480
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock40_harmonicLower_le :
    (lagariasFiniteBlock40.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock40.first : Real) := by
  change (((445323005121812189840709792678020780538988187834985820360651717445631921705511215829003343774672113630797978792172360606164520517568281606523174063294698403067 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000) : Rat) : Real) <=     (harmonic 2880 : Real)
  have hLog :
      (11 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((45 / 32) : Rat)           32 : Real) <=
        Real.log (2880 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (2880 : Real))
      (q := ((45 / 32) : Rat))
      (r := ((45 / 32) : Rat))
      11 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((445323005121812189840709792678020780538988187834985820360651717445631921705511215829003343774672113630797978792172360606164520517568281606523174063294698403067 / 52128730748484906023622520035570656965904785395360285614032624079020349523761113044023692071179618891692168689807335614031612484822607184133000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((11 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((45 / 32) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock40_analyticValid : lagariasFiniteBlock40.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock40
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock40_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock40.first lagariasFiniteBlock40.sigmaBound
        lagariasFiniteBlock40.count = true := by
  unfold lagariasFiniteBlock40
  decide +kernel

theorem lagariasFiniteBlock40_valid : lagariasFiniteBlock40.Valid :=
  And.intro lagariasFiniteBlock40_analyticValid lagariasFiniteBlock40_rangeValid

end Robin1984
