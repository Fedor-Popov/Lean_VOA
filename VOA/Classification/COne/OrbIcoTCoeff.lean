import VOA.Classification.COne.OrbIcoChan2

/-! The normalized sixth-transvectant matrix on degree-twelve monomials. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoT
open OrbPrim OrbRat6 OrbIco

def sixthRow0 : List ℚ :=
  [0, 0, 0, 0, 0, 0, 1, 7, 28, 84, 210, 462, 924]

def sixthRow1 : List ℚ :=
  [0, 0, 0, 0, 0, (-7 / 12), (-5 / 2), (-21 / 4), (-14 / 3), (21 / 2), 63, (385 / 2), 462]

def sixthRow2 : List ℚ :=
  [0, 0, 0, 0, (14 / 33), (21 / 22), (4 / 11), (-175 / 66), (-84 / 11), (-105 / 11), (56 / 11), 63,
    210]

def sixthRow3 : List ℚ :=
  [0, 0, 0, (-21 / 55), (-14 / 55), (35 / 44), (43 / 22), (63 / 44), (-126 / 55), (-903 / 110),
    (-105 / 11), (21 / 2), 84]

def sixthRow4 : List ℚ :=
  [0, 0, (14 / 33), (-14 / 55), (-56 / 55), (-7 / 11), 1, (28 / 11), (28 / 15), (-126 / 55), (-84 /
    11), (-14 / 3), 28]

def sixthRow5 : List ℚ :=
  [0, (-7 / 12), (21 / 22), (35 / 44), (-7 / 11), (-35 / 22), (-10 / 11), (35 / 33), (28 / 11), (63
    / 44), (-175 / 66), (-21 / 4), 7]

def sixthRow6 : List ℚ :=
  [1, (-5 / 2), (4 / 11), (43 / 22), 1, (-10 / 11), (-20 / 11), (-10 / 11), 1, (43 / 22), (4 / 11),
    (-5 / 2), 1]

def sixthRow7 : List ℚ :=
  [7, (-21 / 4), (-175 / 66), (63 / 44), (28 / 11), (35 / 33), (-10 / 11), (-35 / 22), (-7 / 11),
    (35 / 44), (21 / 22), (-7 / 12), 0]

def sixthRow8 : List ℚ :=
  [28, (-14 / 3), (-84 / 11), (-126 / 55), (28 / 15), (28 / 11), 1, (-7 / 11), (-56 / 55), (-14 /
    55), (14 / 33), 0, 0]

def sixthRow9 : List ℚ :=
  [84, (21 / 2), (-105 / 11), (-903 / 110), (-126 / 55), (63 / 44), (43 / 22), (35 / 44), (-14 /
    55), (-21 / 55), 0, 0, 0]

def sixthRow10 : List ℚ :=
  [210, 63, (56 / 11), (-105 / 11), (-84 / 11), (-175 / 66), (4 / 11), (21 / 22), (14 / 33), 0, 0,
    0, 0]

def sixthRow11 : List ℚ :=
  [462, (385 / 2), 63, (21 / 2), (-14 / 3), (-21 / 4), (-5 / 2), (-7 / 12), 0, 0, 0, 0, 0]

def sixthRow12 : List ℚ :=
  [924, 462, 210, 84, 28, 7, 1, 0, 0, 0, 0, 0, 0]

def sixthCoeff (i j : ℕ) : ℚ :=
  ([sixthRow0, sixthRow1, sixthRow2, sixthRow3, sixthRow4, sixthRow5,
    sixthRow6, sixthRow7, sixthRow8, sixthRow9, sixthRow10, sixthRow11,
    sixthRow12].getD i []).getD j 0

def sixthFormula (i j : ℕ) : ℚ :=
  (∑ k ∈ Finset.range 7, (-1 : ℚ) ^ k * (6).choose k *
    (12 - i).descFactorial (6 - k) * i.descFactorial k *
    (12 - j).descFactorial k * j.descFactorial (6 - k)) / 479001600

set_option maxHeartbeats 2000000 in
-- Identify every table entry with the alternating sixth-derivative formula.
theorem sixthCoeff_formula : ∀ i j : Fin 13,
    sixthCoeff i.val j.val = sixthFormula i.val j.val := by
  decide +kernel

set_option maxHeartbeats 1000000 in
-- The rational Clebsch--Gordan recurrence on the complete finite multiplet.
theorem sixthCoeff_rec_check : ∀ i j : Fin 13, 6 < i.val + j.val →
    sixthCoeff i.val j.val * ((i.val : ℚ) + j.val - 6) =
      i.val * sixthCoeff (i.val - 1) j.val + j.val * sixthCoeff i.val (j.val - 1) := by
  decide +kernel

set_option maxHeartbeats 1000000 in
-- Coefficients outside the output multiplet vanish.
theorem sixthCoeff_support_check : ∀ i j : Fin 13,
    i.val + j.val < 6 ∨ 18 < i.val + j.val → sixthCoeff i.val j.val = 0 := by
  decide +kernel

theorem sixthCoeff_rec (i j : ℕ) (hi : i ≤ 12) (hj : j ≤ 12) (h : 6 < i + j) :
    (sixthCoeff i j : ℂ) * ((i : ℂ) + j - 6) =
      i * (sixthCoeff (i - 1) j : ℂ) + j * (sixthCoeff i (j - 1) : ℂ) := by
  exact_mod_cast sixthCoeff_rec_check ⟨i, by omega⟩ ⟨j, by omega⟩ h

theorem sixthCoeff_support (i j : ℕ) (hi : i ≤ 12) (hj : j ≤ 12)
    (h : i + j < 6 ∨ 18 < i + j) : sixthCoeff i j = 0 :=
  sixthCoeff_support_check ⟨i, by omega⟩ ⟨j, by omega⟩ h

end VOA.Classification.COne.OrbIcoT
