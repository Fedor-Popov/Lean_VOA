import VOA.Classification.COne.OrbRat3Eval

/-! # Certified inner products `U₍ₙ₎ h(-1)1` in `V₈`, `0 ≤ n ≤ 8`

Each `Z n` is the executable description of `U₍ₙ₎ h(-1)1` (charges `∓1`), certified by
`decide +kernel` against the evaluator `actU` of `OrbRat3Eval`.  For `n ≥ 6` the product
vanishes.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000

namespace VOA.Classification.COne.OrbRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod

/-- Executable description of `U₍0₎ h(-1)1`. -/
def Z0 : St :=
  [(-1, [(840, [0, 1, 1, 1, 2]), (180, [0, 1, 4]), (120, [0, 2, 3]), (-960, [1, 1, 1, 1, 1]),
    (-960, [1, 1, 3]), (-720, [1, 2, 2])]), (1, [(-840, [0, 1, 1, 1, 2]), (-180, [0, 1, 4]),
    (-120, [0, 2, 3]), (-960, [1, 1, 1, 1, 1]), (-960, [1, 1, 3]), (-720, [1, 2, 2])])]

/-- Executable description of `U₍1₎ h(-1)1`. -/
def Z1 : St :=
  [(-1, [(405, [0, 1, 1, 1, 1]), (180, [0, 1, 3]), (135/2, [0, 2, 2]), (-1620, [1, 1, 2]),
    (-90, [4])]), (1, [(-405, [0, 1, 1, 1, 1]), (-180, [0, 1, 3]), (-135/2, [0, 2, 2]),
    (-1620, [1, 1, 2]), (-90, [4])])]

/-- Executable description of `U₍2₎ h(-1)1`. -/
def Z2 : St :=
  [(-1, [(270, [0, 1, 2]), (-1080, [1, 1, 1]), (-120, [3])]), (1, [(-270, [0, 1, 2]),
    (-1080, [1, 1, 1]), (-120, [3])])]

/-- Executable description of `U₍3₎ h(-1)1`. -/
def Z3 : St :=
  [(-1, [(270, [0, 1, 1]), (-180, [2])]), (1, [(-270, [0, 1, 1]), (-180, [2])])]

/-- Executable description of `U₍4₎ h(-1)1`. -/
def Z4 : St :=
  [(-1, [(-360, [1])]), (1, [(-360, [1])])]

/-- Executable description of `U₍5₎ h(-1)1`. -/
def Z5 : St :=
  [(-1, [(30, [0])]), (1, [(-30, [0])])]

/-- Executable description of `U₍6₎ h(-1)1`. -/
def Z6 : St :=
  [(-1, []), (1, [])]

/-- Executable description of `U₍7₎ h(-1)1`. -/
def Z7 : St :=
  [(-1, []), (1, [])]

/-- Executable description of `U₍8₎ h(-1)1`. -/
def Z8 : St :=
  [(-1, []), (1, [])]

theorem inner_cert_0 : bucket [-1, 1] (actU 0 5 hSt) = Z0 := by decide +kernel

theorem inner_cert_1 : bucket [-1, 1] (actU 1 5 hSt) = Z1 := by decide +kernel

theorem inner_cert_2 : bucket [-1, 1] (actU 2 5 hSt) = Z2 := by decide +kernel

theorem inner_cert_3 : bucket [-1, 1] (actU 3 5 hSt) = Z3 := by decide +kernel

theorem inner_cert_4 : bucket [-1, 1] (actU 4 5 hSt) = Z4 := by decide +kernel

theorem inner_cert_5 : bucket [-1, 1] (actU 5 5 hSt) = Z5 := by decide +kernel

theorem inner_cert_6 : bucket [-1, 1] (actU 6 5 hSt) = Z6 := by decide +kernel

theorem inner_cert_7 : bucket [-1, 1] (actU 7 5 hSt) = Z7 := by decide +kernel

theorem inner_cert_8 : bucket [-1, 1] (actU 8 5 hSt) = Z8 := by decide +kernel

theorem actU_hSt_sectors (n : ℤ) : ∀ p ∈ actU n 5 hSt, p.1 ∈ [-1, 1] := by
  intro p hp
  simp only [actU, termU, scaleSt, actJ, actE, hSt, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_cons, List.mem_range, List.not_mem_nil, or_false] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hp with ⟨i, -, hp⟩
  aesop

theorem inner_0 : (V2m 4 four_ge_one).smul Uc 0 hV = evalSt Z0 := by
  rw [← evalSt_hSt, actU_sound 0 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_0,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_1 : (V2m 4 four_ge_one).smul Uc 1 hV = evalSt Z1 := by
  rw [← evalSt_hSt, actU_sound 1 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_1,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_2 : (V2m 4 four_ge_one).smul Uc 2 hV = evalSt Z2 := by
  rw [← evalSt_hSt, actU_sound 2 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_2,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_3 : (V2m 4 four_ge_one).smul Uc 3 hV = evalSt Z3 := by
  rw [← evalSt_hSt, actU_sound 3 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_3,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_4 : (V2m 4 four_ge_one).smul Uc 4 hV = evalSt Z4 := by
  rw [← evalSt_hSt, actU_sound 4 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_4,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_5 : (V2m 4 four_ge_one).smul Uc 5 hV = evalSt Z5 := by
  rw [← evalSt_hSt, actU_sound 5 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_5,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_6 : (V2m 4 four_ge_one).smul Uc 6 hV = evalSt Z6 := by
  rw [← evalSt_hSt, actU_sound 6 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_6,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_7 : (V2m 4 four_ge_one).smul Uc 7 hV = evalSt Z7 := by
  rw [← evalSt_hSt, actU_sound 7 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_7,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

theorem inner_8 : (V2m 4 four_ge_one).smul Uc 8 hV = evalSt Z8 := by
  rw [← evalSt_hSt, actU_sound 8 5 hSt (r := 1) (by rw [evalSt_hSt]; exact hV_mem)
    (by norm_num) (by norm_num), ← inner_cert_8,
    evalSt_bucket _ (by decide) _ (actU_hSt_sectors _)]

end VOA.Classification.COne.OrbRat3
