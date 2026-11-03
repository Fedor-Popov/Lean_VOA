import VOA.Classification.COne.OrbRat4Cert

/-! # The outer product `U₍13₎ U₍3₎ h(-1)1` in `V₈`, through skew-symmetry

Machine-generated.  Every value is kernel-checked
(`decide +kernel`); `E J` terms with `i < 4` are split into the 4 monomials of `Z3`.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
-- sequential elaboration: keeps the peak memory at one certificate at a time
set_option Elab.async false

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbRat3

/-- The `J E` table for `n = 3`. -/
def aTab3 (j i : ℕ) : ℚ := if j = 5 ∧ i = 0 then (-172800 : ℚ) else 0

/-- The `E J` table for `n = 3`. -/
def tTab3 (i : ℕ) : ℚ :=
  ([(56833920 : ℚ), (33540480 : ℚ), (18023040 : ℚ), (8380800 : ℚ), (2963520 : ℚ),
    (570240 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
    : List ℚ).getD i 0

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hA3 : ∀ j : ℕ, j < 6 → ∀ i : ℕ, i < 10 →
    evalSt (actJ ((j : ℤ) - 2 - i) (actE (13 - j + i) Z3)) = ((aTab3 j i : ℚ) : ℂ) • hV :=
  hA_of_check 13 10 Z3 Z_sectors_3 aTab3 (by decide +kernel)

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hTw3 : ∀ i ∈ ([4, 5, 6, 7, 8, 9] : List ℕ),
    evalSt (actE (13 - 2 - i) (actJ i Z3)) = ((tTab3 i : ℚ) : ℂ) • hV :=
  hT_of_check 13 _ Z3 Z_sectors_3 tTab3 (by decide +kernel)

def q3_0 : St := [(-1, [(270, [0, 1, 1])])]
def q3_1 : St := [(-1, [(-180, [2])])]
def q3_2 : St := [(1, [(-270, [0, 1, 1])])]
def q3_3 : St := [(1, [(-180, [2])])]

def pcs3 : List St := [q3_0, q3_1, q3_2, q3_3]

theorem pieces3 : pieces Z3 = pcs3 := by decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_0_0 : bucket [-2, 0, 2] (actE (13 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q3_0)) = expect (25375680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_0_1 : bucket [-2, 0, 2] (actE (13 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q3_1)) = expect (3041280 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_0_2 : bucket [-2, 0, 2] (actE (13 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q3_2)) = expect (25375680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_0_3 : bucket [-2, 0, 2] (actE (13 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q3_3)) = expect (3041280 : ℚ) := by
  decide +kernel

theorem hT3_0 : evalSt (actE (13 - 2 - ((0 : ℕ) : ℤ)) (actJ ((0 : ℕ) : ℤ) Z3)) =
    ((tTab3 0 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces3, pcs3]
  refine (sum_of_vals _ (fun q => evalSt (actE (13 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q)))
      [(25375680 : ℚ), (3041280 : ℚ), (25375680 : ℚ), (3041280 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_0_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_0_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_0_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_0_3)
      (.nil))))
  · rw [show ([(25375680 : ℚ), (3041280 : ℚ), (25375680 : ℚ), (3041280 : ℚ)]
      : List ℚ).sum = tTab3 0 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_1_0 : bucket [-2, 0, 2] (actE (13 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q3_0)) = expect (14929920 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_1_1 : bucket [-2, 0, 2] (actE (13 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q3_1)) = expect (1840320 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_1_2 : bucket [-2, 0, 2] (actE (13 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q3_2)) = expect (14929920 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_1_3 : bucket [-2, 0, 2] (actE (13 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q3_3)) = expect (1840320 : ℚ) := by
  decide +kernel

theorem hT3_1 : evalSt (actE (13 - 2 - ((1 : ℕ) : ℤ)) (actJ ((1 : ℕ) : ℤ) Z3)) =
    ((tTab3 1 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces3, pcs3]
  refine (sum_of_vals _ (fun q => evalSt (actE (13 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q)))
      [(14929920 : ℚ), (1840320 : ℚ), (14929920 : ℚ), (1840320 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_1_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_1_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_1_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_1_3)
      (.nil))))
  · rw [show ([(14929920 : ℚ), (1840320 : ℚ), (14929920 : ℚ), (1840320 : ℚ)]
      : List ℚ).sum = tTab3 1 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_2_0 : bucket [-2, 0, 2] (actE (13 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q3_0)) = expect (7983360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_2_1 : bucket [-2, 0, 2] (actE (13 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q3_1)) = expect (1028160 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_2_2 : bucket [-2, 0, 2] (actE (13 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q3_2)) = expect (7983360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_2_3 : bucket [-2, 0, 2] (actE (13 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q3_3)) = expect (1028160 : ℚ) := by
  decide +kernel

theorem hT3_2 : evalSt (actE (13 - 2 - ((2 : ℕ) : ℤ)) (actJ ((2 : ℕ) : ℤ) Z3)) =
    ((tTab3 2 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces3, pcs3]
  refine (sum_of_vals _ (fun q => evalSt (actE (13 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q)))
      [(7983360 : ℚ), (1028160 : ℚ), (7983360 : ℚ), (1028160 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_2_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_2_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_2_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_2_3)
      (.nil))))
  · rw [show ([(7983360 : ℚ), (1028160 : ℚ), (7983360 : ℚ), (1028160 : ℚ)]
      : List ℚ).sum = tTab3 2 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_3_0 : bucket [-2, 0, 2] (actE (13 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q3_0)) = expect (3680640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_3_1 : bucket [-2, 0, 2] (actE (13 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q3_1)) = expect (509760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_3_2 : bucket [-2, 0, 2] (actE (13 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q3_2)) = expect (3680640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c3_3_3 : bucket [-2, 0, 2] (actE (13 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q3_3)) = expect (509760 : ℚ) := by
  decide +kernel

theorem hT3_3 : evalSt (actE (13 - 2 - ((3 : ℕ) : ℤ)) (actJ ((3 : ℕ) : ℤ) Z3)) =
    ((tTab3 3 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces3, pcs3]
  refine (sum_of_vals _ (fun q => evalSt (actE (13 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q)))
      [(3680640 : ℚ), (509760 : ℚ), (3680640 : ℚ), (509760 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_3_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_3_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_3_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c3_3_3)
      (.nil))))
  · rw [show ([(3680640 : ℚ), (509760 : ℚ), (3680640 : ℚ), (509760 : ℚ)]
      : List ℚ).sum = tTab3 3 by decide +kernel]

theorem hT3 : ∀ i : ℕ, i < 10 →
    evalSt (actE (13 - 2 - i) (actJ i Z3)) = ((tTab3 i : ℚ) : ℂ) • hV := by
  intro i hi
  interval_cases i
  · exact hT3_0
  · exact hT3_1
  · exact hT3_2
  · exact hT3_3
  all_goals exact hTw3 _ (by decide)

/-- `U₍13₎ U₍3₎ h(-1)1 = -2462400 h(-1)1` in `V₈`. -/
theorem outer3 : (V2m 4 four_ge_one).smul Uc 13 ((V2m 4 four_ge_one).smul Uc 3 hV) =
    ((-2462400 : ℚ) : ℂ) • hV := by
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (3 : ℤ)
  rw [inner_3] at hz ⊢
  rw [assemble 13 10 Z3 hz (by norm_num) (by norm_num) aTab3 tTab3 hA3 hT3]
  rw [show outerQ 13 10 aTab3 tTab3 = -2462400 by decide +kernel]

end VOA.Classification.COne.OrbRat4
