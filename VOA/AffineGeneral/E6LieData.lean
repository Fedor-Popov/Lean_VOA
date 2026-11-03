/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataPairA
import VOA.AffineGeneral.E6LieDataPairB
import VOA.AffineGeneral.E6LieDataPairC
import VOA.AffineGeneral.E6LieDataCasA
import VOA.AffineGeneral.E6LieDataCasB
import VOA.AffineGeneral.E6LieDataCasC
import VOA.AffineGeneral.E6LieDataCasD
import VOA.AffineGeneral.E6LieDataCasE
import VOA.AffineGeneral.E6LieDataCasF
import VOA.AffineGeneral.E6LieDataSkewA
import VOA.AffineGeneral.E6LieDataSkewB
import VOA.AffineGeneral.E6Lie

set_option linter.style.longLine false

/-!
# `LieData` for `𝔢₆` in the carrier basis, and `V^{-3}(𝔢₆)`

`e6LieData : LieData (formG e6Checks e6Gm) (Fin 78)`: the structure-constant algebra `e6Lie` of `E6Table` (basis of
`casimir_cert/cert_E6.json`, the carrier basis of `E6data`), the invariant form `e6Gm` (long roots of length `2`), its
dual family, and `h = 12`.  Invariance: the 12 Chevalley generators are `κ`-skew (`E6LieDataSkew*`), and skewness
passes along the 66 single-term brackets (`skew_of_entry`).

`e6AffineVOA' k hk := affineVOA e6LieData k hk`, `V^{-3}(𝔢₆)` at the Deligne level, whose currents `J a` are the
carrier currents of `E6data` by construction.
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

noncomputable section

theorem e6Skew11 : Skew e6Checks e6Gm (basis e6Checks (11 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 11
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 11 e6_skewOK2_11)

theorem e6Skew10 : Skew e6Checks e6Gm (basis e6Checks (10 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 10
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 10 e6_skewOK2_10)

theorem e6Skew9 : Skew e6Checks e6Gm (basis e6Checks (9 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 9
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 9 e6_skewOK2_9)

theorem e6Skew8 : Skew e6Checks e6Gm (basis e6Checks (8 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 8
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 8 e6_skewOK2_8)

theorem e6Skew7 : Skew e6Checks e6Gm (basis e6Checks (7 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 7
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 7 e6_skewOK2_7)

theorem e6Skew6 : Skew e6Checks e6Gm (basis e6Checks (6 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 6
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 6 e6_skewOK2_6)

theorem e6Skew47 : Skew e6Checks e6Gm (basis e6Checks (47 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 47
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 47 e6_skewOK2_47)

theorem e6Skew46 : Skew e6Checks e6Gm (basis e6Checks (46 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 46
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 46 e6_skewOK2_46)

theorem e6Skew45 : Skew e6Checks e6Gm (basis e6Checks (45 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 45
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 45 e6_skewOK2_45)

theorem e6Skew44 : Skew e6Checks e6Gm (basis e6Checks (44 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 44
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 44 e6_skewOK2_44)

theorem e6Skew43 : Skew e6Checks e6Gm (basis e6Checks (43 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 43
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 43 e6_skewOK2_43)

theorem e6Skew42 : Skew e6Checks e6Gm (basis e6Checks (42 : Fin 78)) :=
  skew_basis_of_check e6Checks e6Gm e6_gInRange 42
    (skewOK_of_2 e6T 78 e6Gm e6_symm e6Gc e6_gc 42 e6_skewOK2_42)

theorem e6Skew12 : Skew e6Checks e6Gm (basis e6Checks (12 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew6 e6Skew7

theorem e6Skew5 : Skew e6Checks e6Gm (basis e6Checks (5 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew6 e6Skew42

theorem e6Skew13 : Skew e6Checks e6Gm (basis e6Checks (13 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew7 e6Skew8

theorem e6Skew4 : Skew e6Checks e6Gm (basis e6Checks (4 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew7 e6Skew43

theorem e6Skew14 : Skew e6Checks e6Gm (basis e6Checks (14 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew8 e6Skew9

theorem e6Skew15 : Skew e6Checks e6Gm (basis e6Checks (15 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew8 e6Skew10

theorem e6Skew3 : Skew e6Checks e6Gm (basis e6Checks (3 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew8 e6Skew44

theorem e6Skew16 : Skew e6Checks e6Gm (basis e6Checks (16 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew9 e6Skew11

theorem e6Skew2 : Skew e6Checks e6Gm (basis e6Checks (2 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew9 e6Skew45

theorem e6Skew1 : Skew e6Checks e6Gm (basis e6Checks (1 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew10 e6Skew46

theorem e6Skew0 : Skew e6Checks e6Gm (basis e6Checks (0 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew11 e6Skew47

theorem e6Skew48 : Skew e6Checks e6Gm (basis e6Checks (48 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew42 e6Skew43

theorem e6Skew49 : Skew e6Checks e6Gm (basis e6Checks (49 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew43 e6Skew44

theorem e6Skew50 : Skew e6Checks e6Gm (basis e6Checks (50 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew44 e6Skew45

theorem e6Skew51 : Skew e6Checks e6Gm (basis e6Checks (51 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew44 e6Skew46

theorem e6Skew52 : Skew e6Checks e6Gm (basis e6Checks (52 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew45 e6Skew47

theorem e6Skew17 : Skew e6Checks e6Gm (basis e6Checks (17 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew6 e6Skew13

theorem e6Skew18 : Skew e6Checks e6Gm (basis e6Checks (18 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew7 e6Skew14

theorem e6Skew19 : Skew e6Checks e6Gm (basis e6Checks (19 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew7 e6Skew15

theorem e6Skew21 : Skew e6Checks e6Gm (basis e6Checks (21 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew8 e6Skew16

theorem e6Skew20 : Skew e6Checks e6Gm (basis e6Checks (20 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew9 e6Skew15

theorem e6Skew22 : Skew e6Checks e6Gm (basis e6Checks (22 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew12 e6Skew14

theorem e6Skew23 : Skew e6Checks e6Gm (basis e6Checks (23 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew12 e6Skew15

theorem e6Skew25 : Skew e6Checks e6Gm (basis e6Checks (25 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew13 e6Skew16

theorem e6Skew26 : Skew e6Checks e6Gm (basis e6Checks (26 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew15 e6Skew16

theorem e6Skew53 : Skew e6Checks e6Gm (basis e6Checks (53 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew42 e6Skew49

theorem e6Skew54 : Skew e6Checks e6Gm (basis e6Checks (54 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew43 e6Skew50

theorem e6Skew55 : Skew e6Checks e6Gm (basis e6Checks (55 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew43 e6Skew51

theorem e6Skew57 : Skew e6Checks e6Gm (basis e6Checks (57 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew44 e6Skew52

theorem e6Skew56 : Skew e6Checks e6Gm (basis e6Checks (56 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew45 e6Skew51

theorem e6Skew58 : Skew e6Checks e6Gm (basis e6Checks (58 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew48 e6Skew50

theorem e6Skew59 : Skew e6Checks e6Gm (basis e6Checks (59 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew48 e6Skew51

theorem e6Skew61 : Skew e6Checks e6Gm (basis e6Checks (61 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew49 e6Skew52

theorem e6Skew62 : Skew e6Checks e6Gm (basis e6Checks (62 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew51 e6Skew52

theorem e6Skew29 : Skew e6Checks e6Gm (basis e6Checks (29 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew6 e6Skew25

theorem e6Skew24 : Skew e6Checks e6Gm (basis e6Checks (24 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew7 e6Skew20

theorem e6Skew30 : Skew e6Checks e6Gm (basis e6Checks (30 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew7 e6Skew26

theorem e6Skew27 : Skew e6Checks e6Gm (basis e6Checks (27 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew9 e6Skew23

theorem e6Skew32 : Skew e6Checks e6Gm (basis e6Checks (32 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew12 e6Skew26

theorem e6Skew28 : Skew e6Checks e6Gm (basis e6Checks (28 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew13 e6Skew20

theorem e6Skew33 : Skew e6Checks e6Gm (basis e6Checks (33 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew13 e6Skew26

theorem e6Skew31 : Skew e6Checks e6Gm (basis e6Checks (31 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew14 e6Skew23

theorem e6Skew35 : Skew e6Checks e6Gm (basis e6Checks (35 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew17 e6Skew26

theorem e6Skew34 : Skew e6Checks e6Gm (basis e6Checks (34 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew18 e6Skew23

theorem e6Skew36 : Skew e6Checks e6Gm (basis e6Checks (36 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew18 e6Skew26

theorem e6Skew38 : Skew e6Checks e6Gm (basis e6Checks (38 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew22 e6Skew26

theorem e6Skew37 : Skew e6Checks e6Gm (basis e6Checks (37 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew23 e6Skew25

theorem e6Skew65 : Skew e6Checks e6Gm (basis e6Checks (65 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew42 e6Skew61

theorem e6Skew60 : Skew e6Checks e6Gm (basis e6Checks (60 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew43 e6Skew56

theorem e6Skew66 : Skew e6Checks e6Gm (basis e6Checks (66 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew43 e6Skew62

theorem e6Skew63 : Skew e6Checks e6Gm (basis e6Checks (63 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew45 e6Skew59

theorem e6Skew68 : Skew e6Checks e6Gm (basis e6Checks (68 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew48 e6Skew62

theorem e6Skew64 : Skew e6Checks e6Gm (basis e6Checks (64 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew49 e6Skew56

theorem e6Skew69 : Skew e6Checks e6Gm (basis e6Checks (69 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew49 e6Skew62

theorem e6Skew67 : Skew e6Checks e6Gm (basis e6Checks (67 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew50 e6Skew59

theorem e6Skew71 : Skew e6Checks e6Gm (basis e6Checks (71 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew53 e6Skew62

theorem e6Skew70 : Skew e6Checks e6Gm (basis e6Checks (70 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew54 e6Skew59

theorem e6Skew72 : Skew e6Checks e6Gm (basis e6Checks (72 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew54 e6Skew62

theorem e6Skew74 : Skew e6Checks e6Gm (basis e6Checks (74 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew58 e6Skew62

theorem e6Skew73 : Skew e6Checks e6Gm (basis e6Checks (73 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew59 e6Skew61

theorem e6Skew39 : Skew e6Checks e6Gm (basis e6Checks (39 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew7 e6Skew38

theorem e6Skew40 : Skew e6Checks e6Gm (basis e6Checks (40 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew13 e6Skew38

theorem e6Skew41 : Skew e6Checks e6Gm (basis e6Checks (41 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew19 e6Skew38

theorem e6Skew75 : Skew e6Checks e6Gm (basis e6Checks (75 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew43 e6Skew74

theorem e6Skew76 : Skew e6Checks e6Gm (basis e6Checks (76 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := -1) (by norm_num) (by decide +kernel) e6Skew49 e6Skew74

theorem e6Skew77 : Skew e6Checks e6Gm (basis e6Checks (77 : Fin 78)) :=
  skew_of_entry e6Checks e6Gm (κ := 1) (by norm_num) (by decide +kernel) e6Skew55 e6Skew74

theorem e6Skew_all : ∀ c : Fin 78, Skew e6Checks e6Gm (basis e6Checks c) := by
  intro c
  fin_cases c
  · exact e6Skew0
  · exact e6Skew1
  · exact e6Skew2
  · exact e6Skew3
  · exact e6Skew4
  · exact e6Skew5
  · exact e6Skew6
  · exact e6Skew7
  · exact e6Skew8
  · exact e6Skew9
  · exact e6Skew10
  · exact e6Skew11
  · exact e6Skew12
  · exact e6Skew13
  · exact e6Skew14
  · exact e6Skew15
  · exact e6Skew16
  · exact e6Skew17
  · exact e6Skew18
  · exact e6Skew19
  · exact e6Skew20
  · exact e6Skew21
  · exact e6Skew22
  · exact e6Skew23
  · exact e6Skew24
  · exact e6Skew25
  · exact e6Skew26
  · exact e6Skew27
  · exact e6Skew28
  · exact e6Skew29
  · exact e6Skew30
  · exact e6Skew31
  · exact e6Skew32
  · exact e6Skew33
  · exact e6Skew34
  · exact e6Skew35
  · exact e6Skew36
  · exact e6Skew37
  · exact e6Skew38
  · exact e6Skew39
  · exact e6Skew40
  · exact e6Skew41
  · exact e6Skew42
  · exact e6Skew43
  · exact e6Skew44
  · exact e6Skew45
  · exact e6Skew46
  · exact e6Skew47
  · exact e6Skew48
  · exact e6Skew49
  · exact e6Skew50
  · exact e6Skew51
  · exact e6Skew52
  · exact e6Skew53
  · exact e6Skew54
  · exact e6Skew55
  · exact e6Skew56
  · exact e6Skew57
  · exact e6Skew58
  · exact e6Skew59
  · exact e6Skew60
  · exact e6Skew61
  · exact e6Skew62
  · exact e6Skew63
  · exact e6Skew64
  · exact e6Skew65
  · exact e6Skew66
  · exact e6Skew67
  · exact e6Skew68
  · exact e6Skew69
  · exact e6Skew70
  · exact e6Skew71
  · exact e6Skew72
  · exact e6Skew73
  · exact e6Skew74
  · exact e6Skew75
  · exact e6Skew76
  · exact e6Skew77

theorem e6_pair : pairOK 78 e6Gm e6dl e6D = true :=
  pairOK_of_chunks e6Gm e6dl e6D fun j hj => by
    rcases (show (0 ≤ j ∧ j < 26) ∨ (26 ≤ j ∧ j < 52) ∨ (52 ≤ j ∧ j < 78) by omega) with h | h | h
    · exact ⟨0, 26, h.1, h.2, e6_pair0⟩
    · exact ⟨26, 52, h.1, h.2, e6_pair1⟩
    · exact ⟨52, 78, h.1, h.2, e6_pair2⟩

theorem e6_cas : ∀ x : Fin 78, casOK e6T 78 e6dl e6D 3 24 x = true := by
  intro x
  have hx : x.val < 78 := x.2
  rcases (show (0 ≤ x.val ∧ x.val < 13) ∨ (13 ≤ x.val ∧ x.val < 26) ∨ (26 ≤ x.val ∧ x.val < 39) ∨ (39 ≤ x.val ∧ x.val < 52) ∨ (52 ≤ x.val ∧ x.val < 65) ∨ (65 ≤ x.val ∧ x.val < 78) by omega) with h | h | h | h | h | h
  · exact e6_cas0 x h.1 h.2
  · exact e6_cas1 x h.1 h.2
  · exact e6_cas2 x h.1 h.2
  · exact e6_cas3 x h.1 h.2
  · exact e6_cas4 x h.1 h.2
  · exact e6_cas5 x h.1 h.2

/-- **Lie data for `𝔢₆` in the carrier basis**, with the normalized invariant form and `h = 12`. -/
def e6LieData : LieData (formG e6Checks e6Gm) (Fin 78) :=
  lieDataOf e6Checks e6Gm e6_gInRange e6_symm e6Skew_all e6dl e6D e6_pair 3 24 (by norm_num) e6_cas

theorem e6LieData_h : e6LieData.h = 12 := by
  show (((24 : ℤ) : ℂ) / 2) = 12
  norm_num

theorem e6_level_ne' : (-3 : ℂ) + e6LieData.h ≠ 0 := by rw [e6LieData_h]; norm_num

/-- **`V^k(𝔢₆)` with currents in the carrier basis.** -/
def e6AffineVOA' (k : ℂ) (hk : k + e6LieData.h ≠ 0) := affineVOA e6LieData k hk

end

end VOA.AffineGeneral.SCLie

section AxiomAudit
open VOA.AffineGeneral.SCLie
#print axioms e6LieData
end AxiomAudit
