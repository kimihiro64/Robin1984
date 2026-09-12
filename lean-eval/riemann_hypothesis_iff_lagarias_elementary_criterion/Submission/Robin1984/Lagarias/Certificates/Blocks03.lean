import Submission.Robin1984.Lagarias.FiniteCertificate

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
private theorem lagariasFiniteBlock39_rangeChunk00 :
    lagariasSigmaRangeValidBool
      2520 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk01 :
    lagariasSigmaRangeValidBool
      2550 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk02 :
    lagariasSigmaRangeValidBool
      2580 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk03 :
    lagariasSigmaRangeValidBool
      2610 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk04 :
    lagariasSigmaRangeValidBool
      2640 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk05 :
    lagariasSigmaRangeValidBool
      2670 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk06 :
    lagariasSigmaRangeValidBool
      2700 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk07 :
    lagariasSigmaRangeValidBool
      2730 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk08 :
    lagariasSigmaRangeValidBool
      2760 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk09 :
    lagariasSigmaRangeValidBool
      2790 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk10 :
    lagariasSigmaRangeValidBool
      2820 9360 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock39_rangeChunk11 :
    lagariasSigmaRangeValidBool
      2850 9360 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock39_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock39.first lagariasFiniteBlock39.sigmaBound
        lagariasFiniteBlock39.count = true := by
  unfold lagariasFiniteBlock39
  have hRange10 :
      lagariasSigmaRangeValidBool
        2820 9360 60 = true :=
    lagariasSigmaRangeValidBool_add
      2820 9360 30 30
      lagariasFiniteBlock39_rangeChunk10 lagariasFiniteBlock39_rangeChunk11
  have hRange09 :
      lagariasSigmaRangeValidBool
        2790 9360 90 = true :=
    lagariasSigmaRangeValidBool_add
      2790 9360 30 60
      lagariasFiniteBlock39_rangeChunk09 hRange10
  have hRange08 :
      lagariasSigmaRangeValidBool
        2760 9360 120 = true :=
    lagariasSigmaRangeValidBool_add
      2760 9360 30 90
      lagariasFiniteBlock39_rangeChunk08 hRange09
  have hRange07 :
      lagariasSigmaRangeValidBool
        2730 9360 150 = true :=
    lagariasSigmaRangeValidBool_add
      2730 9360 30 120
      lagariasFiniteBlock39_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        2700 9360 180 = true :=
    lagariasSigmaRangeValidBool_add
      2700 9360 30 150
      lagariasFiniteBlock39_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        2670 9360 210 = true :=
    lagariasSigmaRangeValidBool_add
      2670 9360 30 180
      lagariasFiniteBlock39_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        2640 9360 240 = true :=
    lagariasSigmaRangeValidBool_add
      2640 9360 30 210
      lagariasFiniteBlock39_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        2610 9360 270 = true :=
    lagariasSigmaRangeValidBool_add
      2610 9360 30 240
      lagariasFiniteBlock39_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        2580 9360 300 = true :=
    lagariasSigmaRangeValidBool_add
      2580 9360 30 270
      lagariasFiniteBlock39_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        2550 9360 330 = true :=
    lagariasSigmaRangeValidBool_add
      2550 9360 30 300
      lagariasFiniteBlock39_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        2520 9360 360 = true :=
    lagariasSigmaRangeValidBool_add
      2520 9360 30 330
      lagariasFiniteBlock39_rangeChunk00 hRange01
  exact hRange00

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
private theorem lagariasFiniteBlock40_rangeChunk00 :
    lagariasSigmaRangeValidBool
      2880 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk01 :
    lagariasSigmaRangeValidBool
      2910 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk02 :
    lagariasSigmaRangeValidBool
      2940 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk03 :
    lagariasSigmaRangeValidBool
      2970 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk04 :
    lagariasSigmaRangeValidBool
      3000 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk05 :
    lagariasSigmaRangeValidBool
      3030 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk06 :
    lagariasSigmaRangeValidBool
      3060 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk07 :
    lagariasSigmaRangeValidBool
      3090 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk08 :
    lagariasSigmaRangeValidBool
      3120 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk09 :
    lagariasSigmaRangeValidBool
      3150 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk10 :
    lagariasSigmaRangeValidBool
      3180 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk11 :
    lagariasSigmaRangeValidBool
      3210 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk12 :
    lagariasSigmaRangeValidBool
      3240 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk13 :
    lagariasSigmaRangeValidBool
      3270 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk14 :
    lagariasSigmaRangeValidBool
      3300 10890 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock40_rangeChunk15 :
    lagariasSigmaRangeValidBool
      3330 10890 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock40_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock40.first lagariasFiniteBlock40.sigmaBound
        lagariasFiniteBlock40.count = true := by
  unfold lagariasFiniteBlock40
  have hRange14 :
      lagariasSigmaRangeValidBool
        3300 10890 60 = true :=
    lagariasSigmaRangeValidBool_add
      3300 10890 30 30
      lagariasFiniteBlock40_rangeChunk14 lagariasFiniteBlock40_rangeChunk15
  have hRange13 :
      lagariasSigmaRangeValidBool
        3270 10890 90 = true :=
    lagariasSigmaRangeValidBool_add
      3270 10890 30 60
      lagariasFiniteBlock40_rangeChunk13 hRange14
  have hRange12 :
      lagariasSigmaRangeValidBool
        3240 10890 120 = true :=
    lagariasSigmaRangeValidBool_add
      3240 10890 30 90
      lagariasFiniteBlock40_rangeChunk12 hRange13
  have hRange11 :
      lagariasSigmaRangeValidBool
        3210 10890 150 = true :=
    lagariasSigmaRangeValidBool_add
      3210 10890 30 120
      lagariasFiniteBlock40_rangeChunk11 hRange12
  have hRange10 :
      lagariasSigmaRangeValidBool
        3180 10890 180 = true :=
    lagariasSigmaRangeValidBool_add
      3180 10890 30 150
      lagariasFiniteBlock40_rangeChunk10 hRange11
  have hRange09 :
      lagariasSigmaRangeValidBool
        3150 10890 210 = true :=
    lagariasSigmaRangeValidBool_add
      3150 10890 30 180
      lagariasFiniteBlock40_rangeChunk09 hRange10
  have hRange08 :
      lagariasSigmaRangeValidBool
        3120 10890 240 = true :=
    lagariasSigmaRangeValidBool_add
      3120 10890 30 210
      lagariasFiniteBlock40_rangeChunk08 hRange09
  have hRange07 :
      lagariasSigmaRangeValidBool
        3090 10890 270 = true :=
    lagariasSigmaRangeValidBool_add
      3090 10890 30 240
      lagariasFiniteBlock40_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        3060 10890 300 = true :=
    lagariasSigmaRangeValidBool_add
      3060 10890 30 270
      lagariasFiniteBlock40_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        3030 10890 330 = true :=
    lagariasSigmaRangeValidBool_add
      3030 10890 30 300
      lagariasFiniteBlock40_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        3000 10890 360 = true :=
    lagariasSigmaRangeValidBool_add
      3000 10890 30 330
      lagariasFiniteBlock40_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        2970 10890 390 = true :=
    lagariasSigmaRangeValidBool_add
      2970 10890 30 360
      lagariasFiniteBlock40_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        2940 10890 420 = true :=
    lagariasSigmaRangeValidBool_add
      2940 10890 30 390
      lagariasFiniteBlock40_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        2910 10890 450 = true :=
    lagariasSigmaRangeValidBool_add
      2910 10890 30 420
      lagariasFiniteBlock40_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        2880 10890 480 = true :=
    lagariasSigmaRangeValidBool_add
      2880 10890 30 450
      lagariasFiniteBlock40_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock40_valid : lagariasFiniteBlock40.Valid :=
  And.intro lagariasFiniteBlock40_analyticValid lagariasFiniteBlock40_rangeValid

end Robin1984
