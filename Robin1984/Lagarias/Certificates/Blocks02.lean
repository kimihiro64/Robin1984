import Robin1984.Lagarias.FiniteCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001) supplies the finite range.
- Formalization note: Generated exact factor and rational certificate data.
- PROVENANCE-END
-/

/-! # Lagarias finite certificate packet 02 -/

namespace Robin1984

def lagariasFiniteBlock36 : LagariasFiniteBlock where
  first := 1680
  sigmaBound := 6120
  harmonicLower := (252362447698959082861546297343713582457171383401228888849961739118451510640984836675740356391998025133359828428951998866753180900638018120543893912241671841168601030992674470446057 / 31530490287905542027906012341798360282354409069688035665791284264366834922678983710362615176853597419187793893543211975099238465003954018178586995134831451877657300000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 300
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock36_harmonicLower_le :
    (lagariasFiniteBlock36.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock36.first : Real) := by
  change (((252362447698959082861546297343713582457171383401228888849961739118451510640984836675740356391998025133359828428951998866753180900638018120543893912241671841168601030992674470446057 / 31530490287905542027906012341798360282354409069688035665791284264366834922678983710362615176853597419187793893543211975099238465003954018178586995134831451877657300000000000000000) : Rat) : Real) <=     (harmonic 1680 : Real)
  have hLog :
      (10 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((105 / 64) : Rat)           32 : Real) <=
        Real.log (1680 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (1680 : Real))
      (q := ((105 / 64) : Rat))
      (r := ((105 / 64) : Rat))
      10 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((252362447698959082861546297343713582457171383401228888849961739118451510640984836675740356391998025133359828428951998866753180900638018120543893912241671841168601030992674470446057 / 31530490287905542027906012341798360282354409069688035665791284264366834922678983710362615176853597419187793893543211975099238465003954018178586995134831451877657300000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((10 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((105 / 64) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock36_analyticValid : lagariasFiniteBlock36.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock36
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk00 :
    lagariasSigmaRangeValidBool
      1680 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk01 :
    lagariasSigmaRangeValidBool
      1710 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk02 :
    lagariasSigmaRangeValidBool
      1740 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk03 :
    lagariasSigmaRangeValidBool
      1770 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk04 :
    lagariasSigmaRangeValidBool
      1800 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk05 :
    lagariasSigmaRangeValidBool
      1830 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk06 :
    lagariasSigmaRangeValidBool
      1860 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk07 :
    lagariasSigmaRangeValidBool
      1890 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk08 :
    lagariasSigmaRangeValidBool
      1920 6120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock36_rangeChunk09 :
    lagariasSigmaRangeValidBool
      1950 6120 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock36_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock36.first lagariasFiniteBlock36.sigmaBound
        lagariasFiniteBlock36.count = true := by
  unfold lagariasFiniteBlock36
  have hRange08 :
      lagariasSigmaRangeValidBool
        1920 6120 60 = true :=
    lagariasSigmaRangeValidBool_add
      1920 6120 30 30
      lagariasFiniteBlock36_rangeChunk08 lagariasFiniteBlock36_rangeChunk09
  have hRange07 :
      lagariasSigmaRangeValidBool
        1890 6120 90 = true :=
    lagariasSigmaRangeValidBool_add
      1890 6120 30 60
      lagariasFiniteBlock36_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        1860 6120 120 = true :=
    lagariasSigmaRangeValidBool_add
      1860 6120 30 90
      lagariasFiniteBlock36_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        1830 6120 150 = true :=
    lagariasSigmaRangeValidBool_add
      1830 6120 30 120
      lagariasFiniteBlock36_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        1800 6120 180 = true :=
    lagariasSigmaRangeValidBool_add
      1800 6120 30 150
      lagariasFiniteBlock36_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        1770 6120 210 = true :=
    lagariasSigmaRangeValidBool_add
      1770 6120 30 180
      lagariasFiniteBlock36_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        1740 6120 240 = true :=
    lagariasSigmaRangeValidBool_add
      1740 6120 30 210
      lagariasFiniteBlock36_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        1710 6120 270 = true :=
    lagariasSigmaRangeValidBool_add
      1710 6120 30 240
      lagariasFiniteBlock36_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        1680 6120 300 = true :=
    lagariasSigmaRangeValidBool_add
      1680 6120 30 270
      lagariasFiniteBlock36_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock36_valid : lagariasFiniteBlock36.Valid :=
  And.intro lagariasFiniteBlock36_analyticValid lagariasFiniteBlock36_rangeValid

def lagariasFiniteBlock37 : LagariasFiniteBlock where
  first := 1980
  sigmaBound := 6944
  harmonicLower := (679340104094043164617696446412290718528290961810134264068075961410246342078398777460365085002498780853302684734461585377380789219853324092439814394715918766349373077721884071811784781048373852099206239842992460044606520343 / 83170291044170317387891209815333666307222641970169366301855474567642418880113819617080768761170969979483958300935322167752067402406053494795575593207713625730480223938942619831809722072372967918105923302700000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 180
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock37_harmonicLower_le :
    (lagariasFiniteBlock37.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock37.first : Real) := by
  change (((679340104094043164617696446412290718528290961810134264068075961410246342078398777460365085002498780853302684734461585377380789219853324092439814394715918766349373077721884071811784781048373852099206239842992460044606520343 / 83170291044170317387891209815333666307222641970169366301855474567642418880113819617080768761170969979483958300935322167752067402406053494795575593207713625730480223938942619831809722072372967918105923302700000000000000000) : Rat) : Real) <=     (harmonic 1980 : Real)
  have hLog :
      (10 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((495 / 256) : Rat)           32 : Real) <=
        Real.log (1980 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (1980 : Real))
      (q := ((495 / 256) : Rat))
      (r := ((495 / 256) : Rat))
      10 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((679340104094043164617696446412290718528290961810134264068075961410246342078398777460365085002498780853302684734461585377380789219853324092439814394715918766349373077721884071811784781048373852099206239842992460044606520343 / 83170291044170317387891209815333666307222641970169366301855474567642418880113819617080768761170969979483958300935322167752067402406053494795575593207713625730480223938942619831809722072372967918105923302700000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((10 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((495 / 256) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock37_analyticValid : lagariasFiniteBlock37.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock37
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock37_rangeChunk00 :
    lagariasSigmaRangeValidBool
      1980 6944 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock37_rangeChunk01 :
    lagariasSigmaRangeValidBool
      2010 6944 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock37_rangeChunk02 :
    lagariasSigmaRangeValidBool
      2040 6944 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock37_rangeChunk03 :
    lagariasSigmaRangeValidBool
      2070 6944 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock37_rangeChunk04 :
    lagariasSigmaRangeValidBool
      2100 6944 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock37_rangeChunk05 :
    lagariasSigmaRangeValidBool
      2130 6944 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock37_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock37.first lagariasFiniteBlock37.sigmaBound
        lagariasFiniteBlock37.count = true := by
  unfold lagariasFiniteBlock37
  have hRange04 :
      lagariasSigmaRangeValidBool
        2100 6944 60 = true :=
    lagariasSigmaRangeValidBool_add
      2100 6944 30 30
      lagariasFiniteBlock37_rangeChunk04 lagariasFiniteBlock37_rangeChunk05
  have hRange03 :
      lagariasSigmaRangeValidBool
        2070 6944 90 = true :=
    lagariasSigmaRangeValidBool_add
      2070 6944 30 60
      lagariasFiniteBlock37_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        2040 6944 120 = true :=
    lagariasSigmaRangeValidBool_add
      2040 6944 30 90
      lagariasFiniteBlock37_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        2010 6944 150 = true :=
    lagariasSigmaRangeValidBool_add
      2010 6944 30 120
      lagariasFiniteBlock37_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        1980 6944 180 = true :=
    lagariasSigmaRangeValidBool_add
      1980 6944 30 150
      lagariasFiniteBlock37_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock37_valid : lagariasFiniteBlock37.Valid :=
  And.intro lagariasFiniteBlock37_analyticValid lagariasFiniteBlock37_rangeValid

def lagariasFiniteBlock38 : LagariasFiniteBlock where
  first := 2160
  sigmaBound := 7812
  harmonicLower := (1877495741446063429171142999790669264582501726876336890691284720671005918682692631608828457937385301822740465089673182647374804201459290160364216578863889457769828960288692092415024656397756763 / 227435375504750421431092767989847777403801040879102089793752662262603042002336789886290636844117109258385325695792759001003997644936592594760603394260710852941576056165584037000000000000000000)
  expTerms := 32
  outerLogTerms := 32
  count := 360
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock38_harmonicLower_le :
    (lagariasFiniteBlock38.harmonicLower : Real) <=
      (harmonic lagariasFiniteBlock38.first : Real) := by
  change (((1877495741446063429171142999790669264582501726876336890691284720671005918682692631608828457937385301822740465089673182647374804201459290160364216578863889457769828960288692092415024656397756763 / 227435375504750421431092767989847777403801040879102089793752662262603042002336789886290636844117109258385325695792759001003997644936592594760603394260710852941576056165584037000000000000000000) : Rat) : Real) <=     (harmonic 2160 : Real)
  have hLog :
      (11 : Real) *           (693147180559945309 / 1000000000000000000) +
        (robinLogLower ((135 / 128) : Rat)           32 : Real) <=
        Real.log (2160 : Real) :=
    (robin_log_bounds_of_dyadic_bracket
      (x := (2160 : Real))
      (q := ((135 / 128) : Rat))
      (r := ((135 / 128) : Rat))
      11 32
      (by norm_num) (by norm_num) (by norm_num)       (by norm_num)).1
  have hLowerValue :
      (((1877495741446063429171142999790669264582501726876336890691284720671005918682692631608828457937385301822740465089673182647374804201459290160364216578863889457769828960288692092415024656397756763 / 227435375504750421431092767989847777403801040879102089793752662262603042002336789886290636844117109258385325695792759001003997644936592594760603394260710852941576056165584037000000000000000000) : Rat) : Real) =
        (57721 / 100000 : Real) +
          ((11 : Real) *
              (693147180559945309 / 1000000000000000000) +
            (robinLogLower ((135 / 128) : Rat)
              32 : Real)) := by
    norm_num [robinLogLower, Rat.logSeriesLower,
      Finset.sum_range_succ]
  exact lagariasHarmonicLower_of_euler_log     (by norm_num) hLowerValue hLog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem lagariasFiniteBlock38_analyticValid : lagariasFiniteBlock38.AnalyticValid := by
  unfold LagariasFiniteBlock.AnalyticValid lagariasFiniteBlock38
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk00 :
    lagariasSigmaRangeValidBool
      2160 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk01 :
    lagariasSigmaRangeValidBool
      2190 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk02 :
    lagariasSigmaRangeValidBool
      2220 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk03 :
    lagariasSigmaRangeValidBool
      2250 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk04 :
    lagariasSigmaRangeValidBool
      2280 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk05 :
    lagariasSigmaRangeValidBool
      2310 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk06 :
    lagariasSigmaRangeValidBool
      2340 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk07 :
    lagariasSigmaRangeValidBool
      2370 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk08 :
    lagariasSigmaRangeValidBool
      2400 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk09 :
    lagariasSigmaRangeValidBool
      2430 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk10 :
    lagariasSigmaRangeValidBool
      2460 7812 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
private theorem lagariasFiniteBlock38_rangeChunk11 :
    lagariasSigmaRangeValidBool
      2490 7812 30 = true := by
  decide +kernel

theorem lagariasFiniteBlock38_rangeValid :
    lagariasSigmaRangeValidBool lagariasFiniteBlock38.first lagariasFiniteBlock38.sigmaBound
        lagariasFiniteBlock38.count = true := by
  unfold lagariasFiniteBlock38
  have hRange10 :
      lagariasSigmaRangeValidBool
        2460 7812 60 = true :=
    lagariasSigmaRangeValidBool_add
      2460 7812 30 30
      lagariasFiniteBlock38_rangeChunk10 lagariasFiniteBlock38_rangeChunk11
  have hRange09 :
      lagariasSigmaRangeValidBool
        2430 7812 90 = true :=
    lagariasSigmaRangeValidBool_add
      2430 7812 30 60
      lagariasFiniteBlock38_rangeChunk09 hRange10
  have hRange08 :
      lagariasSigmaRangeValidBool
        2400 7812 120 = true :=
    lagariasSigmaRangeValidBool_add
      2400 7812 30 90
      lagariasFiniteBlock38_rangeChunk08 hRange09
  have hRange07 :
      lagariasSigmaRangeValidBool
        2370 7812 150 = true :=
    lagariasSigmaRangeValidBool_add
      2370 7812 30 120
      lagariasFiniteBlock38_rangeChunk07 hRange08
  have hRange06 :
      lagariasSigmaRangeValidBool
        2340 7812 180 = true :=
    lagariasSigmaRangeValidBool_add
      2340 7812 30 150
      lagariasFiniteBlock38_rangeChunk06 hRange07
  have hRange05 :
      lagariasSigmaRangeValidBool
        2310 7812 210 = true :=
    lagariasSigmaRangeValidBool_add
      2310 7812 30 180
      lagariasFiniteBlock38_rangeChunk05 hRange06
  have hRange04 :
      lagariasSigmaRangeValidBool
        2280 7812 240 = true :=
    lagariasSigmaRangeValidBool_add
      2280 7812 30 210
      lagariasFiniteBlock38_rangeChunk04 hRange05
  have hRange03 :
      lagariasSigmaRangeValidBool
        2250 7812 270 = true :=
    lagariasSigmaRangeValidBool_add
      2250 7812 30 240
      lagariasFiniteBlock38_rangeChunk03 hRange04
  have hRange02 :
      lagariasSigmaRangeValidBool
        2220 7812 300 = true :=
    lagariasSigmaRangeValidBool_add
      2220 7812 30 270
      lagariasFiniteBlock38_rangeChunk02 hRange03
  have hRange01 :
      lagariasSigmaRangeValidBool
        2190 7812 330 = true :=
    lagariasSigmaRangeValidBool_add
      2190 7812 30 300
      lagariasFiniteBlock38_rangeChunk01 hRange02
  have hRange00 :
      lagariasSigmaRangeValidBool
        2160 7812 360 = true :=
    lagariasSigmaRangeValidBool_add
      2160 7812 30 330
      lagariasFiniteBlock38_rangeChunk00 hRange01
  exact hRange00

theorem lagariasFiniteBlock38_valid : lagariasFiniteBlock38.Valid :=
  And.intro lagariasFiniteBlock38_analyticValid lagariasFiniteBlock38_rangeValid

end Robin1984
