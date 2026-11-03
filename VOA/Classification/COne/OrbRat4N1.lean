import VOA.Classification.COne.OrbRat4Cert

/-! # The outer product `U₍15₎ U₍1₎ h(-1)1` in `V₈`, through skew-symmetry

Machine-generated.  Every value is kernel-checked
(`decide +kernel`); `E J` terms with `i < 6` are split into the 10 monomials of `Z1`.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
-- sequential elaboration: keeps the peak memory at one certificate at a time
set_option Elab.async false

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbRat3

/-- The `J E` table for `n = 1`. -/
def aTab1 (j i : ℕ) : ℚ := if j = 5 ∧ i = 0 then (-2358720 : ℚ) else 0

/-- The `E J` table for `n = 1`. -/
def tTab1 (i : ℕ) : ℚ :=
  ([(1333463040 : ℚ), (868855680 : ℚ), (533977920 : ℚ), (302883840 : ℚ), (151873920 : ℚ),
    (62190720 : ℚ), (17992800 : ℚ), (2725920 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
    : List ℚ).getD i 0

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hA1 : ∀ j : ℕ, j < 6 → ∀ i : ℕ, i < 12 →
    evalSt (actJ ((j : ℤ) - 2 - i) (actE (15 - j + i) Z1)) = ((aTab1 j i : ℚ) : ℂ) • hV :=
  hA_of_check 15 12 Z1 Z_sectors_1 aTab1 (by decide +kernel)

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem hTw1 : ∀ i ∈ ([6, 7, 8, 9, 10, 11] : List ℕ),
    evalSt (actE (15 - 2 - i) (actJ i Z1)) = ((tTab1 i : ℚ) : ℂ) • hV :=
  hT_of_check 15 _ Z1 Z_sectors_1 tTab1 (by decide +kernel)

def q1_0 : St := [(-1, [(405, [0, 1, 1, 1, 1])])]
def q1_1 : St := [(-1, [(180, [0, 1, 3])])]
def q1_2 : St := [(-1, [(135/2, [0, 2, 2])])]
def q1_3 : St := [(-1, [(-1620, [1, 1, 2])])]
def q1_4 : St := [(-1, [(-90, [4])])]
def q1_5 : St := [(1, [(-405, [0, 1, 1, 1, 1])])]
def q1_6 : St := [(1, [(-180, [0, 1, 3])])]
def q1_7 : St := [(1, [(-135/2, [0, 2, 2])])]
def q1_8 : St := [(1, [(-1620, [1, 1, 2])])]
def q1_9 : St := [(1, [(-90, [4])])]

def pcs1 : List St := [q1_0, q1_1, q1_2, q1_3, q1_4, q1_5, q1_6, q1_7, q1_8, q1_9]

theorem pieces1 : pieces Z1 = pcs1 := by decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_0 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_0)) = expect (343699200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_1 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_1)) = expect (39312000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_2 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_2)) = expect (15500160 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_3 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_3)) = expect (264850560 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_4 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_4)) = expect (3369600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_5 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_5)) = expect (343699200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_6 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_6)) = expect (39312000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_7 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_7)) = expect (15500160 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_8 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_8)) = expect (264850560 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_0_9 : bucket [-2, 0, 2] (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q1_9)) = expect (3369600 : ℚ) := by
  decide +kernel

theorem hT1_0 : evalSt (actE (15 - 2 - ((0 : ℕ) : ℤ)) (actJ ((0 : ℕ) : ℤ) Z1)) =
    ((tTab1 0 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces1, pcs1]
  refine (sum_of_vals _ (fun q => evalSt (actE (15 - 2 - ((0 : ℕ) : ℤ))
    (actJ ((0 : ℕ) : ℤ) q)))
      [(343699200 : ℚ), (39312000 : ℚ), (15500160 : ℚ), (264850560 : ℚ), (3369600 : ℚ),
      (343699200 : ℚ), (39312000 : ℚ), (15500160 : ℚ), (264850560 : ℚ), (3369600 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_0_9)
      (.nil))))))))))
  · rw [show ([(343699200 : ℚ), (39312000 : ℚ), (15500160 : ℚ), (264850560 : ℚ), (3369600 : ℚ),
      (343699200 : ℚ), (39312000 : ℚ), (15500160 : ℚ), (264850560 : ℚ), (3369600 : ℚ)]
      : List ℚ).sum = tTab1 0 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_0 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_0)) = expect (222393600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_1 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_1)) = expect (26611200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_2 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_2)) = expect (10264320 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_3 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_3)) = expect (172782720 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_4 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_4)) = expect (2376000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_5 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_5)) = expect (222393600 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_6 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_6)) = expect (26611200 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_7 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_7)) = expect (10264320 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_8 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_8)) = expect (172782720 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_1_9 : bucket [-2, 0, 2] (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q1_9)) = expect (2376000 : ℚ) := by
  decide +kernel

theorem hT1_1 : evalSt (actE (15 - 2 - ((1 : ℕ) : ℤ)) (actJ ((1 : ℕ) : ℤ) Z1)) =
    ((tTab1 1 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces1, pcs1]
  refine (sum_of_vals _ (fun q => evalSt (actE (15 - 2 - ((1 : ℕ) : ℤ))
    (actJ ((1 : ℕ) : ℤ) q)))
      [(222393600 : ℚ), (26611200 : ℚ), (10264320 : ℚ), (172782720 : ℚ), (2376000 : ℚ),
      (222393600 : ℚ), (26611200 : ℚ), (10264320 : ℚ), (172782720 : ℚ), (2376000 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_1_9)
      (.nil))))))))))
  · rw [show ([(222393600 : ℚ), (26611200 : ℚ), (10264320 : ℚ), (172782720 : ℚ), (2376000 : ℚ),
      (222393600 : ℚ), (26611200 : ℚ), (10264320 : ℚ), (172782720 : ℚ), (2376000 : ℚ)]
      : List ℚ).sum = tTab1 1 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_0 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_0)) = expect (135302400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_1 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_1)) = expect (17236800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_2 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_2)) = expect (6454080 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_3 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_3)) = expect (106375680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_4 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_4)) = expect (1620000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_5 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_5)) = expect (135302400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_6 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_6)) = expect (17236800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_7 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_7)) = expect (6454080 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_8 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_8)) = expect (106375680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_2_9 : bucket [-2, 0, 2] (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q1_9)) = expect (1620000 : ℚ) := by
  decide +kernel

theorem hT1_2 : evalSt (actE (15 - 2 - ((2 : ℕ) : ℤ)) (actJ ((2 : ℕ) : ℤ) Z1)) =
    ((tTab1 2 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces1, pcs1]
  refine (sum_of_vals _ (fun q => evalSt (actE (15 - 2 - ((2 : ℕ) : ℤ))
    (actJ ((2 : ℕ) : ℤ) q)))
      [(135302400 : ℚ), (17236800 : ℚ), (6454080 : ℚ), (106375680 : ℚ), (1620000 : ℚ),
      (135302400 : ℚ), (17236800 : ℚ), (6454080 : ℚ), (106375680 : ℚ), (1620000 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_2_9)
      (.nil))))))))))
  · rw [show ([(135302400 : ℚ), (17236800 : ℚ), (6454080 : ℚ), (106375680 : ℚ), (1620000 : ℚ),
      (135302400 : ℚ), (17236800 : ℚ), (6454080 : ℚ), (106375680 : ℚ), (1620000 : ℚ)]
      : List ℚ).sum = tTab1 2 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_0 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_0)) = expect (75582720 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_1 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_1)) = expect (10523520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_2 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_2)) = expect (3784320 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_3 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_3)) = expect (60497280 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_4 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_4)) = expect (1054080 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_5 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_5)) = expect (75582720 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_6 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_6)) = expect (10523520 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_7 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_7)) = expect (3784320 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_8 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_8)) = expect (60497280 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_3_9 : bucket [-2, 0, 2] (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q1_9)) = expect (1054080 : ℚ) := by
  decide +kernel

theorem hT1_3 : evalSt (actE (15 - 2 - ((3 : ℕ) : ℤ)) (actJ ((3 : ℕ) : ℤ) Z1)) =
    ((tTab1 3 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces1, pcs1]
  refine (sum_of_vals _ (fun q => evalSt (actE (15 - 2 - ((3 : ℕ) : ℤ))
    (actJ ((3 : ℕ) : ℤ) q)))
      [(75582720 : ℚ), (10523520 : ℚ), (3784320 : ℚ), (60497280 : ℚ), (1054080 : ℚ),
      (75582720 : ℚ), (10523520 : ℚ), (3784320 : ℚ), (60497280 : ℚ), (1054080 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_3_9)
      (.nil))))))))))
  · rw [show ([(75582720 : ℚ), (10523520 : ℚ), (3784320 : ℚ), (60497280 : ℚ), (1054080 : ℚ),
      (75582720 : ℚ), (10523520 : ℚ), (3784320 : ℚ), (60497280 : ℚ), (1054080 : ℚ)]
      : List ℚ).sum = tTab1 3 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_0 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_0)) = expect (36391680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_1 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_1)) = expect (5909760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_2 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_2)) = expect (2047680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_3 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_3)) = expect (30948480 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_4 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_4)) = expect (639360 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_5 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_5)) = expect (36391680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_6 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_6)) = expect (5909760 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_7 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_7)) = expect (2047680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_8 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_8)) = expect (30948480 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_4_9 : bucket [-2, 0, 2] (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q1_9)) = expect (639360 : ℚ) := by
  decide +kernel

theorem hT1_4 : evalSt (actE (15 - 2 - ((4 : ℕ) : ℤ)) (actJ ((4 : ℕ) : ℤ) Z1)) =
    ((tTab1 4 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces1, pcs1]
  refine (sum_of_vals _ (fun q => evalSt (actE (15 - 2 - ((4 : ℕ) : ℤ))
    (actJ ((4 : ℕ) : ℤ) q)))
      [(36391680 : ℚ), (5909760 : ℚ), (2047680 : ℚ), (30948480 : ℚ), (639360 : ℚ),
      (36391680 : ℚ), (5909760 : ℚ), (2047680 : ℚ), (30948480 : ℚ), (639360 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_4_9)
      (.nil))))))))))
  · rw [show ([(36391680 : ℚ), (5909760 : ℚ), (2047680 : ℚ), (30948480 : ℚ), (639360 : ℚ),
      (36391680 : ℚ), (5909760 : ℚ), (2047680 : ℚ), (30948480 : ℚ), (639360 : ℚ)]
      : List ℚ).sum = tTab1 4 by decide +kernel]

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_0 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_0)) = expect (13063680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_1 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_1)) = expect (3110400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_2 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_2)) = expect (1036800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_3 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_3)) = expect (13530240 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_4 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_4)) = expect (354240 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_5 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_5)) = expect (13063680 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_6 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_6)) = expect (3110400 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_7 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_7)) = expect (1036800 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_8 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_8)) = expect (13530240 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 40000 in
-- memory guard for the kernel check (keeps one certificate under ~2 GB)
theorem c1_5_9 : bucket [-2, 0, 2] (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q1_9)) = expect (354240 : ℚ) := by
  decide +kernel

theorem hT1_5 : evalSt (actE (15 - 2 - ((5 : ℕ) : ℤ)) (actJ ((5 : ℕ) : ℤ) Z1)) =
    ((tTab1 5 : ℚ) : ℂ) • hV := by
  rw [evalSt_EJ_pieces, pieces1, pcs1]
  refine (sum_of_vals _ (fun q => evalSt (actE (15 - 2 - ((5 : ℕ) : ℤ))
    (actJ ((5 : ℕ) : ℤ) q)))
      [(13063680 : ℚ), (3110400 : ℚ), (1036800 : ℚ), (13530240 : ℚ), (354240 : ℚ),
      (13063680 : ℚ), (3110400 : ℚ), (1036800 : ℚ), (13530240 : ℚ), (354240 : ℚ)]
      ?_).trans ?_
  · exact .cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_0)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_1)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_2)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_3)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_4)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_5)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_6)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_7)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_8)
      (.cons (val_of_bucket _ (EJ_sectors _ _ _ (by decide)) _ c1_5_9)
      (.nil))))))))))
  · rw [show ([(13063680 : ℚ), (3110400 : ℚ), (1036800 : ℚ), (13530240 : ℚ), (354240 : ℚ),
      (13063680 : ℚ), (3110400 : ℚ), (1036800 : ℚ), (13530240 : ℚ), (354240 : ℚ)]
      : List ℚ).sum = tTab1 5 by decide +kernel]

theorem hT1 : ∀ i : ℕ, i < 12 →
    evalSt (actE (15 - 2 - i) (actJ i Z1)) = ((tTab1 i : ℚ) : ℂ) • hV := by
  intro i hi
  interval_cases i
  · exact hT1_0
  · exact hT1_1
  · exact hT1_2
  · exact hT1_3
  · exact hT1_4
  · exact hT1_5
  all_goals exact hTw1 _ (by decide)

/-- `U₍15₎ U₍1₎ h(-1)1 = -86184000 h(-1)1` in `V₈`. -/
theorem outer1 : (V2m 4 four_ge_one).smul Uc 15 ((V2m 4 four_ge_one).smul Uc 1 hV) =
    ((-86184000 : ℚ) : ℂ) • hV := by
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (1 : ℤ)
  rw [inner_1] at hz ⊢
  rw [assemble 15 12 Z1 hz (by norm_num) (by norm_num) aTab1 tTab1 hA1 hT1]
  rw [show outerQ 15 12 aTab1 tTab1 = -86184000 by decide +kernel]

end VOA.Classification.COne.OrbRat4
