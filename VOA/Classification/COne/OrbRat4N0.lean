import VOA.Classification.COne.OrbRat4Cert

/-! # The outer product `U₍16₎ U₍0₎ h(-1)1` in `V₈`, through skew-symmetry

Machine-generated.  Every value is kernel-checked
(`decide +kernel`); `E J` terms with `i < 7` are split into the 12 monomials of `Z0`.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
-- sequential elaboration: keeps the peak memory at one certificate at a time
set_option Elab.async false

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbRat3

/-- The `J E` table for `n = 0`. -/
def aTab0 (j i : ℕ) : ℚ := if j = 5 ∧ i = 0 then (-6687360 : ℚ) else 0

/-- The `E J` table for `n = 0`. -/
def tTab0 (i : ℕ) : ℚ :=
  ([(4795338240 : ℚ), (3240933120 : ℚ), (2087769600 : ℚ), (1262286720 : ℚ),
    (695692800 : ℚ), (332501760 : ℚ), (127042560 : ℚ), (33747840 : ℚ), (5045760 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
    : List ℚ).getD i 0

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hA0 : ∀ j : ℕ, j < 6 → ∀ i : ℕ, i < 13 →
    evalSt (actJ ((j : ℤ) - 2 - i) (actE (16 - j + i) Z0)) = ((aTab0 j i : ℚ) : ℂ) • hV :=
  hA_of_check 16 13 Z0 Z_sectors_0 aTab0 (by decide +kernel)

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hTw0 : ∀ i ∈ ([7, 8, 9, 10, 11, 12] : List ℕ),
    evalSt (actE (16 - 2 - i) (actJ i Z0)) = ((tTab0 i : ℚ) : ℂ) • hV :=
  hT_of_check 16 _ Z0 Z_sectors_0 tTab0 (by decide +kernel)

def q0_0 : St := [(-1, [(840, [0, 1, 1, 1, 2])])]
def q0_1 : St := [(-1, [(180, [0, 1, 4])])]
def q0_2 : St := [(-1, [(120, [0, 2, 3])])]
def q0_3 : St := [(-1, [(-960, [1, 1, 1, 1, 1])])]
def q0_4 : St := [(-1, [(-960, [1, 1, 3])])]
def q0_5 : St := [(-1, [(-720, [1, 2, 2])])]
def q0_6 : St := [(1, [(-840, [0, 1, 1, 1, 2])])]
def q0_7 : St := [(1, [(-180, [0, 1, 4])])]
def q0_8 : St := [(1, [(-120, [0, 2, 3])])]
def q0_9 : St := [(1, [(-960, [1, 1, 1, 1, 1])])]
def q0_10 : St := [(1, [(-960, [1, 1, 3])])]
def q0_11 : St := [(1, [(-720, [1, 2, 2])])]

def pcs0 : List St := [q0_0, q0_1, q0_2, q0_3, q0_4, q0_5, q0_6, q0_7, q0_8, q0_9, q0_10, q0_11]

theorem pieces0 : pieces Z0 = pcs0 := by decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_0 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_0)) = expect (1131217920 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_1 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_1)) = expect (55883520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_2 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_2)) = expect (37739520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_3 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_3)) = expect (779304960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_4 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_4)) = expect (217405440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_5 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_5)) = expect (176117760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_6 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_6)) = expect (1131217920 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_7 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_7)) = expect (55883520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_8 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_8)) = expect (37739520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_9 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_9)) = expect (779304960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_10 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_10)) = expect (217405440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_0_11 : bucket [-2, 0, 2] (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q0_11)) = expect (176117760 : ℚ) := by
  decide +kernel

theorem hT0_0 : evalSt (actE (16 - 2 - ((0 : ℕ) : ℤ)) (actJ ((0 : ℕ) : ℤ) Z0)) =
    ((tTab0 0 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces0, pcs0]
  refine (sum_of_vals _ (fun q => evalSt (actE (16 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q)))
      [(1131217920 : ℚ), (55883520 : ℚ), (37739520 : ℚ), (779304960 : ℚ), (217405440 : ℚ),
      (176117760 : ℚ), (1131217920 : ℚ), (55883520 : ℚ), (37739520 : ℚ), (779304960 : ℚ),
      (217405440 : ℚ), (176117760 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_9)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_10)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_0_11)
      (.nil))))))))))))
  · rw [show ([(1131217920 : ℚ), (55883520 : ℚ), (37739520 : ℚ), (779304960 : ℚ), (217405440 : ℚ),
      (176117760 : ℚ), (1131217920 : ℚ), (55883520 : ℚ), (37739520 : ℚ), (779304960 : ℚ),
      (217405440 : ℚ), (176117760 : ℚ)]
      : List ℚ).sum = tTab0 0 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_0 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_0)) = expect (759951360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_1 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_1)) = expect (40037760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_2 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_2)) = expect (26357760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_3 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_3)) = expect (524206080 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_4 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_4)) = expect (150405120 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_5 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_5)) = expect (119508480 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_6 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_6)) = expect (759951360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_7 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_7)) = expect (40037760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_8 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_8)) = expect (26357760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_9 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_9)) = expect (524206080 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_10 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_10)) = expect (150405120 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_1_11 : bucket [-2, 0, 2] (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q0_11)) = expect (119508480 : ℚ) := by
  decide +kernel

theorem hT0_1 : evalSt (actE (16 - 2 - ((1 : ℕ) : ℤ)) (actJ ((1 : ℕ) : ℤ) Z0)) =
    ((tTab0 1 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces0, pcs0]
  refine (sum_of_vals _ (fun q => evalSt (actE (16 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q)))
      [(759951360 : ℚ), (40037760 : ℚ), (26357760 : ℚ), (524206080 : ℚ), (150405120 : ℚ),
      (119508480 : ℚ), (759951360 : ℚ), (40037760 : ℚ), (26357760 : ℚ), (524206080 : ℚ),
      (150405120 : ℚ), (119508480 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_9)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_10)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_1_11)
      (.nil))))))))))))
  · rw [show ([(759951360 : ℚ), (40037760 : ℚ), (26357760 : ℚ), (524206080 : ℚ), (150405120 : ℚ),
      (119508480 : ℚ), (759951360 : ℚ), (40037760 : ℚ), (26357760 : ℚ), (524206080 : ℚ),
      (150405120 : ℚ), (119508480 : ℚ)]
      : List ℚ).sum = tTab0 1 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_0 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_0)) = expect (485452800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_1 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_1)) = expect (27820800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_2 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_2)) = expect (17740800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_3 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_3)) = expect (335462400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_4 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_4)) = expect (99993600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_5 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_5)) = expect (77414400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_6 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_6)) = expect (485452800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_7 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_7)) = expect (27820800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_8 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_8)) = expect (17740800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_9 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_9)) = expect (335462400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_10 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_10)) = expect (99993600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_2_11 : bucket [-2, 0, 2] (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q0_11)) = expect (77414400 : ℚ) := by
  decide +kernel

theorem hT0_2 : evalSt (actE (16 - 2 - ((2 : ℕ) : ℤ)) (actJ ((2 : ℕ) : ℤ) Z0)) =
    ((tTab0 2 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces0, pcs0]
  refine (sum_of_vals _ (fun q => evalSt (actE (16 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q)))
      [(485452800 : ℚ), (27820800 : ℚ), (17740800 : ℚ), (335462400 : ℚ), (99993600 : ℚ),
      (77414400 : ℚ), (485452800 : ℚ), (27820800 : ℚ), (17740800 : ℚ), (335462400 : ℚ),
      (99993600 : ℚ), (77414400 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_9)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_10)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_2_11)
      (.nil))))))))))))
  · rw [show ([(485452800 : ℚ), (27820800 : ℚ), (17740800 : ℚ), (335462400 : ℚ), (99993600 : ℚ),
      (77414400 : ℚ), (485452800 : ℚ), (27820800 : ℚ), (17740800 : ℚ), (335462400 : ℚ),
      (99993600 : ℚ), (77414400 : ℚ)]
      : List ℚ).sum = tTab0 2 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_0 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_0)) = expect (289981440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_1 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_1)) = expect (18567360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_2 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_2)) = expect (11381760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_3 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_3)) = expect (200908800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_4 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_4)) = expect (63129600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_5 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_5)) = expect (47174400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_6 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_6)) = expect (289981440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_7 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_7)) = expect (18567360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_8 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_8)) = expect (11381760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_9 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_9)) = expect (200908800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_10 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_10)) = expect (63129600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_3_11 : bucket [-2, 0, 2] (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q0_11)) = expect (47174400 : ℚ) := by
  decide +kernel

theorem hT0_3 : evalSt (actE (16 - 2 - ((3 : ℕ) : ℤ)) (actJ ((3 : ℕ) : ℤ) Z0)) =
    ((tTab0 3 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces0, pcs0]
  refine (sum_of_vals _ (fun q => evalSt (actE (16 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q)))
      [(289981440 : ℚ), (18567360 : ℚ), (11381760 : ℚ), (200908800 : ℚ), (63129600 : ℚ),
      (47174400 : ℚ), (289981440 : ℚ), (18567360 : ℚ), (11381760 : ℚ), (200908800 : ℚ),
      (63129600 : ℚ), (47174400 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_9)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_10)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_3_11)
      (.nil))))))))))))
  · rw [show ([(289981440 : ℚ), (18567360 : ℚ), (11381760 : ℚ), (200908800 : ℚ), (63129600 : ℚ),
      (47174400 : ℚ), (289981440 : ℚ), (18567360 : ℚ), (11381760 : ℚ), (200908800 : ℚ),
      (63129600 : ℚ), (47174400 : ℚ)]
      : List ℚ).sum = tTab0 3 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_0 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_0)) = expect (158376960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_1 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_1)) = expect (11715840 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_2 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_2)) = expect (6888960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_3 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_3)) = expect (106905600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_4 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_4)) = expect (37140480 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_5 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_5)) = expect (26818560 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_6 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_6)) = expect (158376960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_7 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_7)) = expect (11715840 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_8 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_8)) = expect (6888960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_9 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_9)) = expect (106905600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_10 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_10)) = expect (37140480 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_4_11 : bucket [-2, 0, 2] (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q0_11)) = expect (26818560 : ℚ) := by
  decide +kernel

theorem hT0_4 : evalSt (actE (16 - 2 - ((4 : ℕ) : ℤ)) (actJ ((4 : ℕ) : ℤ) Z0)) =
    ((tTab0 4 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces0, pcs0]
  refine (sum_of_vals _ (fun q => evalSt (actE (16 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q)))
      [(158376960 : ℚ), (11715840 : ℚ), (6888960 : ℚ), (106905600 : ℚ), (37140480 : ℚ),
      (26818560 : ℚ), (158376960 : ℚ), (11715840 : ℚ), (6888960 : ℚ), (106905600 : ℚ),
      (37140480 : ℚ), (26818560 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_9)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_10)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_4_11)
      (.nil))))))))))))
  · rw [show ([(158376960 : ℚ), (11715840 : ℚ), (6888960 : ℚ), (106905600 : ℚ), (37140480 : ℚ),
      (26818560 : ℚ), (158376960 : ℚ), (11715840 : ℚ), (6888960 : ℚ), (106905600 : ℚ),
      (37140480 : ℚ), (26818560 : ℚ)]
      : List ℚ).sum = tTab0 4 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_0 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_0)) = expect (74672640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_1 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_1)) = expect (6894720 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_2 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_2)) = expect (4020480 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_3 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_3)) = expect (46080000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_4 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_4)) = expect (20551680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_5 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_5)) = expect (14031360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_6 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_6)) = expect (74672640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_7 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_7)) = expect (6894720 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_8 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_8)) = expect (4020480 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_9 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_9)) = expect (46080000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_10 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_10)) = expect (20551680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_5_11 : bucket [-2, 0, 2] (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q0_11)) = expect (14031360 : ℚ) := by
  decide +kernel

theorem hT0_5 : evalSt (actE (16 - 2 - ((5 : ℕ) : ℤ)) (actJ ((5 : ℕ) : ℤ) Z0)) =
    ((tTab0 5 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces0, pcs0]
  refine (sum_of_vals _ (fun q => evalSt (actE (16 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q)))
      [(74672640 : ℚ), (6894720 : ℚ), (4020480 : ℚ), (46080000 : ℚ), (20551680 : ℚ),
      (14031360 : ℚ), (74672640 : ℚ), (6894720 : ℚ), (4020480 : ℚ), (46080000 : ℚ),
      (20551680 : ℚ), (14031360 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_9)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_10)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_5_11)
      (.nil))))))))))))
  · rw [show ([(74672640 : ℚ), (6894720 : ℚ), (4020480 : ℚ), (46080000 : ℚ), (20551680 : ℚ),
      (14031360 : ℚ), (74672640 : ℚ), (6894720 : ℚ), (4020480 : ℚ), (46080000 : ℚ),
      (20551680 : ℚ), (14031360 : ℚ)]
      : List ℚ).sum = tTab0 5 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_0 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_0)) = expect (30320640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_1 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_1)) = expect (3801600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_2 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_2)) = expect (2027520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_3 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_3)) = expect (11059200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_4 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_4)) = expect (10229760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_5 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_5)) = expect (6082560 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_6 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_6)) = expect (30320640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_7 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_7)) = expect (3801600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_8 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_8)) = expect (2027520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_9 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_9)) = expect (11059200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_10 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_10)) = expect (10229760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c0_6_11 : bucket [-2, 0, 2] (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q0_11)) = expect (6082560 : ℚ) := by
  decide +kernel

theorem hT0_6 : evalSt (actE (16 - 2 - ((6 : ℕ) : ℤ)) (actJ ((6 : ℕ) : ℤ) Z0)) =
    ((tTab0 6 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces0, pcs0]
  refine (sum_of_vals _ (fun q => evalSt (actE (16 - 2 - ((6 : ℕ) : ℤ))
    (actJ ((6 : ℕ) : ℤ) q)))
      [(30320640 : ℚ), (3801600 : ℚ), (2027520 : ℚ), (11059200 : ℚ), (10229760 : ℚ),
      (6082560 : ℚ), (30320640 : ℚ), (3801600 : ℚ), (2027520 : ℚ), (11059200 : ℚ),
      (10229760 : ℚ), (6082560 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_9)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_10)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c0_6_11)
      (.nil))))))))))))
  · rw [show ([(30320640 : ℚ), (3801600 : ℚ), (2027520 : ℚ), (11059200 : ℚ), (10229760 : ℚ),
      (6082560 : ℚ), (30320640 : ℚ), (3801600 : ℚ), (2027520 : ℚ), (11059200 : ℚ),
      (10229760 : ℚ), (6082560 : ℚ)]
      : List ℚ).sum = tTab0 6 by decide +kernel]

theorem hT0 : ∀ i : ℕ, i < 13 →
    evalSt (actE (16 - 2 - i) (actJ i Z0)) = ((tTab0 i : ℚ) : ℂ) • hV := by
  intro i hi
  interval_cases i
  · exact hT0_0
  · exact hT0_1
  · exact hT0_2
  · exact hT0_3
  · exact hT0_4
  · exact hT0_5
  · exact hT0_6
  all_goals exact hTw0 _ (by decide)

/-- `U₍16₎ U₍0₎ h(-1)1 = -379468800 h(-1)1` in `V₈`. -/
theorem outer0 : (V2m 4 four_ge_one).smul Uc 16 ((V2m 4 four_ge_one).smul Uc 0 hV) =
    ((-379468800 : ℚ) : ℂ) • hV := by
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (0 : ℤ)
  rw [inner_0] at hz ⊢
  rw [assemble 16 13 Z0 hz (by norm_num) (by norm_num) aTab0 tTab0 hA0 hT0]
  rw [show outerQ 16 13 aTab0 tTab0 = -379468800 by decide +kernel]

end VOA.Classification.COne.OrbRat4
