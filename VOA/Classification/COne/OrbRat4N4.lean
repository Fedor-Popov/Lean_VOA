import VOA.Classification.COne.OrbRat4Cert

/-! # The outer product `U₍12₎ U₍4₎ h(-1)1` in `V₈`, through skew-symmetry

Machine-generated.  Every value is kernel-checked
(`decide +kernel`); `E J` terms with `i < 3` are split into the 2 monomials of `Z4`.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
-- sequential elaboration: keeps the peak memory at one certificate at a time
set_option Elab.async false

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbRat3

/-- The `J E` table for `n = 4`. -/
def aTab4 (j i : ℕ) : ℚ := if j = 5 ∧ i = 0 then (-30240 : ℚ) else 0

/-- The `E J` table for `n = 4`. -/
def tTab4 (i : ℕ) : ℚ :=
  ([(7257600 : ℚ), (3991680 : ℚ), (1935360 : ℚ), (756000 : ℚ), (172800 : ℚ), (0 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ)]
    : List ℚ).getD i 0

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hA4 : ∀ j : ℕ, j < 6 → ∀ i : ℕ, i < 9 →
    evalSt (actJ ((j : ℤ) - 2 - i) (actE (12 - j + i) Z4)) = ((aTab4 j i : ℚ) : ℂ) • hV :=
  hA_of_check 12 9 Z4 Z_sectors_4 aTab4 (by decide +kernel)

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hTw4 : ∀ i ∈ ([3, 4, 5, 6, 7, 8] : List ℕ),
    evalSt (actE (12 - 2 - i) (actJ i Z4)) = ((tTab4 i : ℚ) : ℂ) • hV :=
  hT_of_check 12 _ Z4 Z_sectors_4 tTab4 (by decide +kernel)

def q4_0 : St := [(-1, [(-360, [1])])]
def q4_1 : St := [(1, [(-360, [1])])]

def pcs4 : List St := [q4_0, q4_1]

theorem pieces4 : pieces Z4 = pcs4 := by decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c4_0_0 : bucket [-2, 0, 2] (actE (12 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q4_0)) = expect (3628800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c4_0_1 : bucket [-2, 0, 2] (actE (12 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q4_1)) = expect (3628800 : ℚ) := by
  decide +kernel

theorem hT4_0 : evalSt (actE (12 - 2 - ((0 : ℕ) : ℤ)) (actJ ((0 : ℕ) : ℤ) Z4)) =
    ((tTab4 0 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces4, pcs4]
  refine (sum_of_vals _ (fun q => evalSt (actE (12 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q)))
      [(3628800 : ℚ), (3628800 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c4_0_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c4_0_1)
      (.nil))
  · rw [show ([(3628800 : ℚ), (3628800 : ℚ)]
      : List ℚ).sum = tTab4 0 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c4_1_0 : bucket [-2, 0, 2] (actE (12 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q4_0)) = expect (1995840 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c4_1_1 : bucket [-2, 0, 2] (actE (12 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q4_1)) = expect (1995840 : ℚ) := by
  decide +kernel

theorem hT4_1 : evalSt (actE (12 - 2 - ((1 : ℕ) : ℤ)) (actJ ((1 : ℕ) : ℤ) Z4)) =
    ((tTab4 1 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces4, pcs4]
  refine (sum_of_vals _ (fun q => evalSt (actE (12 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q)))
      [(1995840 : ℚ), (1995840 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c4_1_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c4_1_1)
      (.nil))
  · rw [show ([(1995840 : ℚ), (1995840 : ℚ)]
      : List ℚ).sum = tTab4 1 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c4_2_0 : bucket [-2, 0, 2] (actE (12 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q4_0)) = expect (967680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c4_2_1 : bucket [-2, 0, 2] (actE (12 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q4_1)) = expect (967680 : ℚ) := by
  decide +kernel

theorem hT4_2 : evalSt (actE (12 - 2 - ((2 : ℕ) : ℤ)) (actJ ((2 : ℕ) : ℤ) Z4)) =
    ((tTab4 2 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces4, pcs4]
  refine (sum_of_vals _ (fun q => evalSt (actE (12 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q)))
      [(967680 : ℚ), (967680 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c4_2_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c4_2_1)
      (.nil))
  · rw [show ([(967680 : ℚ), (967680 : ℚ)]
      : List ℚ).sum = tTab4 2 by decide +kernel]

theorem hT4 : ∀ i : ℕ, i < 9 →
    evalSt (actE (12 - 2 - i) (actJ i Z4)) = ((tTab4 i : ℚ) : ℂ) • hV := by
  intro i hi
  interval_cases i
  · exact hT4_0
  · exact hT4_1
  · exact hT4_2
  all_goals exact hTw4 _ (by decide)

/-- `U₍12₎ U₍4₎ h(-1)1 = -259200 h(-1)1` in `V₈`. -/
theorem outer4 : (V2m 4 four_ge_one).smul Uc 12 ((V2m 4 four_ge_one).smul Uc 4 hV) =
    ((-259200 : ℚ) : ℂ) • hV := by
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (4 : ℤ)
  rw [inner_4] at hz ⊢
  rw [assemble 12 9 Z4 hz (by norm_num) (by norm_num) aTab4 tTab4 hA4 hT4]
  rw [show outerQ 12 9 aTab4 tTab4 = -259200 by decide +kernel]

end VOA.Classification.COne.OrbRat4
