import VOA.Classification.COne.OrbRat4Cert

/-! # The outer product `U₍14₎ U₍2₎ h(-1)1` in `V₈`, through skew-symmetry

Machine-generated.  Every value is kernel-checked
(`decide +kernel`); `E J` terms with `i < 5` are split into the 6 monomials of `Z2`.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
-- sequential elaboration: keeps the peak memory at one certificate at a time
set_option Elab.async false

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbRat3

/-- The `J E` table for `n = 2`. -/
def aTab2 (j i : ℕ) : ℚ := if j = 5 ∧ i = 0 then (-711360 : ℚ) else 0

/-- The `E J` table for `n = 2`. -/
def tTab2 (i : ℕ) : ℚ :=
  ([(310613760 : ℚ), (193636800 : ℚ), (112227840 : ℚ), (58561920 : ℚ), (25666560 : ℚ),
    (8184960 : ℚ), (1370880 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
    : List ℚ).getD i 0

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hA2 : ∀ j : ℕ, j < 6 → ∀ i : ℕ, i < 11 →
    evalSt (actJ ((j : ℤ) - 2 - i) (actE (14 - j + i) Z2)) = ((aTab2 j i : ℚ) : ℂ) • hV :=
  hA_of_check 14 11 Z2 Z_sectors_2 aTab2 (by decide +kernel)

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hTw2 : ∀ i ∈ ([5, 6, 7, 8, 9, 10] : List ℕ),
    evalSt (actE (14 - 2 - i) (actJ i Z2)) = ((tTab2 i : ℚ) : ℂ) • hV :=
  hT_of_check 14 _ Z2 Z_sectors_2 tTab2 (by decide +kernel)

def q2_0 : St := [(-1, [(270, [0, 1, 2])])]
def q2_1 : St := [(-1, [(-1080, [1, 1, 1])])]
def q2_2 : St := [(-1, [(-120, [3])])]
def q2_3 : St := [(1, [(-270, [0, 1, 2])])]
def q2_4 : St := [(1, [(-1080, [1, 1, 1])])]
def q2_5 : St := [(1, [(-120, [3])])]

def pcs2 : List St := [q2_0, q2_1, q2_2, q2_3, q2_4, q2_5]

theorem pieces2 : pieces Z2 = pcs2 := by decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_0_0 : bucket [-2, 0, 2] (actE (14 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q2_0)) = expect (41005440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_0_1 : bucket [-2, 0, 2] (actE (14 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q2_1)) = expect (111248640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_0_2 : bucket [-2, 0, 2] (actE (14 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q2_2)) = expect (3052800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_0_3 : bucket [-2, 0, 2] (actE (14 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q2_3)) = expect (41005440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_0_4 : bucket [-2, 0, 2] (actE (14 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q2_4)) = expect (111248640 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_0_5 : bucket [-2, 0, 2] (actE (14 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q2_5)) = expect (3052800 : ℚ) := by
  decide +kernel

theorem hT2_0 : evalSt (actE (14 - 2 - ((0 : ℕ) : ℤ)) (actJ ((0 : ℕ) : ℤ) Z2)) =
    ((tTab2 0 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces2, pcs2]
  refine (sum_of_vals _ (fun q => evalSt (actE (14 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q)))
      [(41005440 : ℚ), (111248640 : ℚ), (3052800 : ℚ), (41005440 : ℚ), (111248640 : ℚ),
      (3052800 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_0_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_0_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_0_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_0_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_0_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_0_5)
      (.nil))))))
  · rw [show ([(41005440 : ℚ), (111248640 : ℚ), (3052800 : ℚ), (41005440 : ℚ), (111248640 : ℚ),
      (3052800 : ℚ)]
      : List ℚ).sum = tTab2 0 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_1_0 : bucket [-2, 0, 2] (actE (14 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q2_0)) = expect (25855200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_1_1 : bucket [-2, 0, 2] (actE (14 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q2_1)) = expect (68947200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_1_2 : bucket [-2, 0, 2] (actE (14 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q2_2)) = expect (2016000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_1_3 : bucket [-2, 0, 2] (actE (14 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q2_3)) = expect (25855200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_1_4 : bucket [-2, 0, 2] (actE (14 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q2_4)) = expect (68947200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_1_5 : bucket [-2, 0, 2] (actE (14 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q2_5)) = expect (2016000 : ℚ) := by
  decide +kernel

theorem hT2_1 : evalSt (actE (14 - 2 - ((1 : ℕ) : ℤ)) (actJ ((1 : ℕ) : ℤ) Z2)) =
    ((tTab2 1 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces2, pcs2]
  refine (sum_of_vals _ (fun q => evalSt (actE (14 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q)))
      [(25855200 : ℚ), (68947200 : ℚ), (2016000 : ℚ), (25855200 : ℚ), (68947200 : ℚ),
      (2016000 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_1_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_1_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_1_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_1_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_1_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_1_5)
      (.nil))))))
  · rw [show ([(25855200 : ℚ), (68947200 : ℚ), (2016000 : ℚ), (25855200 : ℚ), (68947200 : ℚ),
      (2016000 : ℚ)]
      : List ℚ).sum = tTab2 1 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_2_0 : bucket [-2, 0, 2] (actE (14 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q2_0)) = expect (15240960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_2_1 : bucket [-2, 0, 2] (actE (14 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q2_1)) = expect (39605760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_2_2 : bucket [-2, 0, 2] (actE (14 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q2_2)) = expect (1267200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_2_3 : bucket [-2, 0, 2] (actE (14 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q2_3)) = expect (15240960 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_2_4 : bucket [-2, 0, 2] (actE (14 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q2_4)) = expect (39605760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_2_5 : bucket [-2, 0, 2] (actE (14 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q2_5)) = expect (1267200 : ℚ) := by
  decide +kernel

theorem hT2_2 : evalSt (actE (14 - 2 - ((2 : ℕ) : ℤ)) (actJ ((2 : ℕ) : ℤ) Z2)) =
    ((tTab2 2 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces2, pcs2]
  refine (sum_of_vals _ (fun q => evalSt (actE (14 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q)))
      [(15240960 : ℚ), (39605760 : ℚ), (1267200 : ℚ), (15240960 : ℚ), (39605760 : ℚ),
      (1267200 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_2_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_2_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_2_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_2_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_2_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_2_5)
      (.nil))))))
  · rw [show ([(15240960 : ℚ), (39605760 : ℚ), (1267200 : ℚ), (15240960 : ℚ), (39605760 : ℚ),
      (1267200 : ℚ)]
      : List ℚ).sum = tTab2 2 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_3_0 : bucket [-2, 0, 2] (actE (14 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q2_0)) = expect (8164800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_3_1 : bucket [-2, 0, 2] (actE (14 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q2_1)) = expect (20373120 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_3_2 : bucket [-2, 0, 2] (actE (14 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q2_2)) = expect (743040 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_3_3 : bucket [-2, 0, 2] (actE (14 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q2_3)) = expect (8164800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_3_4 : bucket [-2, 0, 2] (actE (14 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q2_4)) = expect (20373120 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_3_5 : bucket [-2, 0, 2] (actE (14 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q2_5)) = expect (743040 : ℚ) := by
  decide +kernel

theorem hT2_3 : evalSt (actE (14 - 2 - ((3 : ℕ) : ℤ)) (actJ ((3 : ℕ) : ℤ) Z2)) =
    ((tTab2 3 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces2, pcs2]
  refine (sum_of_vals _ (fun q => evalSt (actE (14 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q)))
      [(8164800 : ℚ), (20373120 : ℚ), (743040 : ℚ), (8164800 : ℚ), (20373120 : ℚ),
      (743040 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_3_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_3_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_3_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_3_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_3_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_3_5)
      (.nil))))))
  · rw [show ([(8164800 : ℚ), (20373120 : ℚ), (743040 : ℚ), (8164800 : ℚ), (20373120 : ℚ),
      (743040 : ℚ)]
      : List ℚ).sum = tTab2 3 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_4_0 : bucket [-2, 0, 2] (actE (14 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q2_0)) = expect (3836160 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_4_1 : bucket [-2, 0, 2] (actE (14 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q2_1)) = expect (8605440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_4_2 : bucket [-2, 0, 2] (actE (14 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q2_2)) = expect (391680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_4_3 : bucket [-2, 0, 2] (actE (14 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q2_3)) = expect (3836160 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_4_4 : bucket [-2, 0, 2] (actE (14 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q2_4)) = expect (8605440 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c2_4_5 : bucket [-2, 0, 2] (actE (14 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q2_5)) = expect (391680 : ℚ) := by
  decide +kernel

theorem hT2_4 : evalSt (actE (14 - 2 - ((4 : ℕ) : ℤ)) (actJ ((4 : ℕ) : ℤ) Z2)) =
    ((tTab2 4 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces2, pcs2]
  refine (sum_of_vals _ (fun q => evalSt (actE (14 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q)))
      [(3836160 : ℚ), (8605440 : ℚ), (391680 : ℚ), (3836160 : ℚ), (8605440 : ℚ),
      (391680 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_4_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_4_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_4_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_4_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_4_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c2_4_5)
      (.nil))))))
  · rw [show ([(3836160 : ℚ), (8605440 : ℚ), (391680 : ℚ), (3836160 : ℚ), (8605440 : ℚ),
      (391680 : ℚ)]
      : List ℚ).sum = tTab2 4 by decide +kernel]

theorem hT2 : ∀ i : ℕ, i < 11 →
    evalSt (actE (14 - 2 - i) (actJ i Z2)) = ((tTab2 i : ℚ) : ℂ) • hV := by
  intro i hi
  interval_cases i
  · exact hT2_0
  · exact hT2_1
  · exact hT2_2
  · exact hT2_3
  · exact hT2_4
  all_goals exact hTw2 _ (by decide)

/-- `U₍14₎ U₍2₎ h(-1)1 = -16416000 h(-1)1` in `V₈`. -/
theorem outer2 : (V2m 4 four_ge_one).smul Uc 14 ((V2m 4 four_ge_one).smul Uc 2 hV) =
    ((-16416000 : ℚ) : ℂ) • hV := by
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (2 : ℤ)
  rw [inner_2] at hz ⊢
  rw [assemble 14 11 Z2 hz (by norm_num) (by norm_num) aTab2 tTab2 hA2 hT2]
  rw [show outerQ 14 11 aTab2 tTab2 = -16416000 by decide +kernel]

end VOA.Classification.COne.OrbRat4
