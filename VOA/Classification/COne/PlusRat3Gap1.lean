import VOA.Classification.COne.PlusRat3GenTransfer
import VOA.Classification.COne.PlusRat3Six

/-! # Every gap-one charged/charged pair splits (all `m`)

General form of `PlusRat3Six`.  Let `r, r'` be charged rows with
`weight (c_{r'}) = weight (c_r) + 1` (equivalently `s'² = s² + 4m`, `s = r + 1`, `s' = r' + 1`),
each the unique row of its weight.  Then the pair (kernel `c_{r'}`, quotient `c_r`) splits
(`pairSplitting_charged_gap_one`), hence both orientations (`pairSplitting_charged_gap_one_both`).

The `M(1)⁺` part is `h`-independent; the `E`-part uses the virtual eigenvalue
`(2K-1)(K-2) · o(H⁴)(E₍ₘ₋₂₎x) = 2((m-1)² - 4m h) · E₍ₘ₋₂₎x` (`K = 2m`), nonzero since `s ≠ m - 1`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible

section GenTop
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) (r : Fin (m - 1))
  (huq : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r → j = .inl r)
  {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M) {x : M}

include hm2 huq in
theorem zero_mode_top_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) {k : ℤ}
    {a : VP m hm} (ha : a ∈ (V2mPlus m hm).grading k) :
    mode (A.YM a) (k - 1) x = chiT m hm hm2 (.inl r) (VOA.mk (V2mPlus m hm) a) • x := by
  have h := top_char_unique m hm hm2 A hxΩ hxL (.inl r) huq (VOA.mk (V2mPlus m hm) a)
  rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h
  exact h

include hm2 huq in
theorem oH4_top_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (HP m hm 2)) 3 x = 0 := by
  have h := zero_mode_top_gen m hm hm2 r huq A hxΩ hxL (HP_mem_grading m hm 2 (by norm_num) (by norm_num))
  rw [chiT_HP_zero m hm hm2 r 2 (Or.inl rfl), zero_smul] at h
  simpa using h

include hm2 huq in
theorem oH6_top_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (HP m hm 3)) 5 x = 0 := by
  have h := zero_mode_top_gen m hm hm2 r huq A hxΩ hxL (HP_mem_grading m hm 3 (by norm_num) (by norm_num))
  rw [chiT_HP_zero m hm hm2 r 3 (Or.inr rfl), zero_smul] at h
  simpa using h

include hm2 huq in
theorem oE_top_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0 := by
  have h := zero_mode_top_gen m hm hm2 r huq A hxΩ hxL (EP_mem_grading m hm)
  have hv := (chiT_hasValues m hm hm2 (.inl r)).2.2
  change chiT m hm hm2 (.inl r) (VOA.mk (V2mPlus m hm) (EP m hm)) = _ at hv
  rw [hv] at h
  simp [values] at h
  simpa using h

include hm2 huq in
theorem comm_H4_p2_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 2)) 2 x) =
      (1 / 15 : ℂ) • mode (A.YM (HP m hm 1)) 0 x - mode (A.YM (HP m hm 2)) 2 x +
        (3 : ℂ) • mode (A.YM (HP m hm 3)) 4 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 2) 2 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, oH4_top_gen m hm hm2 r huq A hxΩ hxL, map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H44_eq m hm 0 (by norm_num), H44_eq m hm 1 (by norm_num), H44_eq m hm 2 (by norm_num),
    H44_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T44, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include hm2 huq in
theorem comm_H4_p3_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 3)) 4 x) =
      (-1 / 35 : ℂ) • mode (A.YM (HP m hm 1)) 0 x + (3 / 5 : ℂ) • mode (A.YM (HP m hm 2)) 2 x -
        (2 : ℂ) • mode (A.YM (HP m hm 3)) 4 x + (3 : ℂ) • mode (A.YM (HP m hm 4)) 6 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 3) 4 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, oH4_top_gen m hm hm2 r huq A hxΩ hxL, map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H46_eq m hm 0 (by norm_num), H46_eq m hm 1 (by norm_num), H46_eq m hm 2 (by norm_num),
    H46_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T46, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include hm2 huq in
theorem comm_H6_p2_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 2)) 2 x) =
      (-1 / 21 : ℂ) • mode (A.YM (HP m hm 1)) 0 x + mode (A.YM (HP m hm 2)) 2 x -
        (10 / 3 : ℂ) • mode (A.YM (HP m hm 3)) 4 x + (5 : ℂ) • mode (A.YM (HP m hm 4)) 6 x := by
  have h := zero_mode_comm A 5 (HP m hm 3) (HP m hm 2) 2 x
  rw [show ((5 : ℕ) : ℤ) = 5 by rfl, oH6_top_gen m hm hm2 r huq A hxΩ hxL, map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H64_eq m hm 0 (by norm_num), H64_eq m hm 1 (by norm_num), H64_eq m hm 2 (by norm_num),
    H64_eq m hm 3 (by norm_num), H64_eq m hm 4 (by norm_num), H64_eq m hm 5 (by norm_num)]
  simp only [mode_combV, T64, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  simp only [show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl,
    show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl,
    show Nat.choose 5 4 = 5 from rfl, show Nat.choose 5 5 = 1 from rfl]
  norm_num
  module

include hm2 huq in
theorem oH4_p1_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 1)) 0 x) =
      (3 : ℂ) • mode (A.YM (HP m hm 2)) 2 x := by
  change mode (A.YM (HP m hm 2)) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) = _
  rw [mode_translation, oH4_top_gen m hm hm2 r huq A hxΩ hxL, map_zero, zero_add]
  norm_num

include hm2 huq in
theorem oH6_p1_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 1)) 0 x) =
      (5 : ℂ) • mode (A.YM (HP m hm 3)) 4 x := by
  change mode (A.YM (HP m hm 3)) 5 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) = _
  rw [mode_translation, oH6_top_gen m hm hm2 r huq A hxΩ hxL, map_zero, zero_add]
  norm_num

theorem L1_on_gen (hxΩ : x ∈ Omega A) {wt : ℤ} {u : VP m hm} (hu : u ∈ (V2mPlus m hm).grading wt)
    (n : ℤ) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM u) n x) =
      ((2 * wt - n - 2 : ℤ) : ℂ) • mode (A.YM u) (n + 1) x + mode (A.YM ((V2mPlus m hm).L 1 u)) n x := by
  have h := L1_comm A hu n x
  rw [Omega_mode_vanish hxΩ (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num),
    map_zero, sub_zero] at h
  exact h

include hm2 in
theorem L1_p1_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (2 * hC m r) • x := by
  rw [L1_on_gen m hm A hxΩ (V2mPlus m hm).conformal_mem 0, L1_omega_zero_gen m hm hm2, map_zero,
    mode_zero, LinearMap.zero_apply, add_zero]
  have hL : mode (A.YM (V2mPlus m hm).conformalVector) (0 + 1) x = hC m r • x := hxL
  rw [hL, smul_smul]
  norm_num

include hm2 huq in
theorem L1_p2_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 2)) 2 x) =
      (2 * hC m r / 3) • x := by
  rw [L1_on_gen m hm A hxΩ (HP_mem_grading m hm 2 (by norm_num) (by norm_num)) 2, L1_H4]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have h3 : mode (A.YM (HP m hm 2)) (2 + 1) x = 0 := oH4_top_gen m hm hm2 r huq A hxΩ hxL
  have hL : mode (A.YM (HP m hm 1)) (2 - ((1 : ℕ) : ℤ)) x = hC m r • x := hxL
  rw [h3, hL]
  push_cast
  module

include hm2 huq in
theorem L1_p3_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 3)) 4 x) =
      (2 * hC m r / 5) • x := by
  rw [L1_on_gen m hm A hxΩ (HP_mem_grading m hm 3 (by norm_num) (by norm_num)) 4, L1_H6]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have h5 : mode (A.YM (HP m hm 3)) (4 + 1) x = 0 := oH6_top_gen m hm hm2 r huq A hxΩ hxL
  have hL : mode (A.YM (HP m hm 1)) (4 - ((3 : ℕ) : ℤ)) x = hC m r • x := hxL
  have h3 : mode (A.YM (HP m hm 2)) (4 - ((1 : ℕ) : ℤ)) x = 0 := oH4_top_gen m hm hm2 r huq A hxΩ hxL
  rw [h5, hL, h3]
  push_cast
  module

include hm2 huq in
theorem L1_v_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (EP m hm)) ((m : ℤ) - 2) x) = 0 := by
  rw [L1_on_gen m hm A hxΩ (EP_mem_grading m hm) _, L1_E m hm, map_zero, mode_zero,
    LinearMap.zero_apply, add_zero, show (m : ℤ) - 2 + 1 = (m : ℤ) - 1 by ring,
    oE_top_gen m hm hm2 r huq A hxΩ hxL, smul_zero]

theorem LE_mem_grading_gen : (V2mPlus m hm).L (-1) (EP m hm) ∈ (V2mPlus m hm).grading ((m : ℤ) + 1) := by
  rw [L_neg_one_eq_smul]
  have := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading (V2mPlus m hm).conformal_mem
    (EP_mem_grading m hm) 0
  convert this using 2
  ring

include hm2 huq in
theorem E_Lx_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    mode (A.YM (EP m hm)) ((m : ℤ) - 1) (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (((m : ℤ) - 1 : ℤ) : ℂ) • mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
  rw [mode_translation, oE_top_gen m hm hm2 r huq A hxΩ hxL, map_zero, zero_add,
    show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring]

include hm2 huq in
/-- The virtual `H⁴`-eigenvalue of `v = E₍ₘ₋₂₎x`:
`(2K-1)(K-2) o(H⁴) v = 2((m-1)² - 4m h) v`, `K = 2m`. -/
theorem oH4_v_gen (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x) :
    ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2)) •
        mode (A.YM (HP m hm 2)) 3 (mode (A.YM (EP m hm)) ((m : ℤ) - 2) x) =
      (2 * (((m : ℂ) - 1) ^ 2 - 4 * m * hC m r)) • mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
  set h := hC m r
  have hLx := E_Lx_gen m hm hm2 r huq A hxΩ hxL
  -- j = 3
  have e3 : mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 3 (EP m hm))) ((m : ℤ) - 2) x = 0 := by
    rw [H4_3_E]; simp
  -- j = 2
  have e2 : (3 : ℂ) • mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 2 (EP m hm))) ((m : ℤ) - 1) x =
      (-(((m : ℤ) - 1 : ℤ) : ℂ)) • mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
    have h2 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 1) x) (H4_2_E m hm)
    simp only [map_smul, mode_smul, LinearMap.smul_apply] at h2
    rw [T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring] at h2
    exact h2
  -- j = 1
  have e1 : (2 * (2 * (m : ℂ)) - 1) • mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 1 (EP m hm))) (m : ℤ) x =
      (2 * (2 * (m : ℂ)) * ((m : ℂ) - 1 + h) - (m : ℂ) * ((m : ℂ) - 1)) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
    have h1 := congrArg (fun y => mode (A.YM y) (m : ℤ) x) (H4_1_E m hm)
    simp only [map_smul, map_sub, mode_smul, mode_sub, LinearMap.smul_apply,
      LinearMap.sub_apply] at h1
    have hω := omega_neg_mode A hxΩ hxL (EP_mem_grading m hm) 1 le_rfl
    rw [show ((m : ℕ) : ℤ) + 1 - 1 = (m : ℤ) by ring, hLx, negOnePow_neg_one'] at hω
    rw [hω, T_mode, T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring] at h1
    rw [h1]
    push_cast
    module
  -- j = 0
  have e0 : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) •
      mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 0 (EP m hm))) ((m : ℤ) + 1) x =
      ((4 * (2 * (m : ℂ)) ^ 2 - 6 * (2 * (m : ℂ))) * (-((m : ℂ) - 1 + 2 * h)) +
        4 * (2 * (m : ℂ)) * (((m : ℂ) - 1) * ((m : ℂ) + h)) -
        2 * (((m : ℂ) + 1) * (m : ℂ) * ((m : ℂ) - 1))) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
    have h0 := congrArg (fun y => mode (A.YM y) ((m : ℤ) + 1) x) (H4_0_E m hm)
    simp only [map_smul, map_sub, map_add, mode_smul, mode_sub, mode_add, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply] at h0
    have hω2 := omega_neg_mode A hxΩ hxL (EP_mem_grading m hm) 2 (by norm_num)
    rw [show ((m : ℕ) : ℤ) + 2 - 1 = (m : ℤ) + 1 by ring, hLx,
      show ((m : ℕ) : ℤ) - 2 = (m : ℤ) - 2 by rfl, negOnePow_neg_two'] at hω2
    have hω1 := omega_neg_mode A hxΩ hxL (LE_mem_grading_gen m hm) 1 le_rfl
    rw [show (m : ℤ) + 1 + 1 - 1 = (m : ℤ) + 1 by ring, show (m : ℤ) + 1 - 1 = (m : ℤ) by ring,
      show (m : ℤ) + 1 - 2 = (m : ℤ) - 1 by ring, T_mode, T_mode,
      show (m : ℤ) - 1 = (m : ℤ) - 1 by rfl, negOnePow_neg_one'] at hω1
    rw [show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring, hLx] at hω1
    rw [hω2, hω1, T_mode, T_mode, T_mode, show (m : ℤ) + 1 - 1 = (m : ℤ) by ring,
      show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring] at h0
    rw [h0]
    push_cast
    module
  have hc := zero_mode_comm A 3 (HP m hm 2) (EP m hm) ((m : ℤ) - 2) x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, oH4_top_gen m hm hm2 r huq A hxΩ hxL, map_zero, zero_add] at hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl] at hc
  rw [show (3 : ℤ) + ((m : ℤ) - 2) - 0 = (m : ℤ) + 1 by ring,
    show (3 : ℤ) + ((m : ℤ) - 2) - 1 = (m : ℤ) by ring,
    show (3 : ℤ) + ((m : ℤ) - 2) - 2 = (m : ℤ) - 1 by ring,
    show (3 : ℤ) + ((m : ℤ) - 2) - 3 = (m : ℤ) - 2 by ring, e3] at hc
  rw [hc]
  linear_combination (norm := module) e0 +
    (3 * (2 * (m : ℂ) - 2)) • e1 + ((2 * (2 * (m : ℂ)) - 1) * (2 * (m : ℂ) - 2)) • e2

theorem L0_degOne_gen (hxL : L0 A x = hC m r • x) {k : ℤ} {a : VP m hm}
    (ha : a ∈ (V2mPlus m hm).grading k) :
    L0 A (mode (A.YM a) (k - 2) x) = (hC m r + 1) • mode (A.YM a) (k - 2) x := by
  rw [L0_commutator_weak A ha x (k - 2), hxL, map_smul, ← add_smul]
  congr 1
  push_cast; ring

include hm2 in
/-- On a top vector of the kernel row `r'` (unique at its weight), `o(H⁴)` and `o(H⁶)` vanish. -/
theorem omega_route_gen (r' : Fin (m - 1))
    (huq' : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r' → j = .inl r')
    {w : M} (hwΩ : w ∈ Omega A) (hwL : L0 A w = hC m r' • w) (t : ℕ)
    (ht : t = 2 ∨ t = 3) : mode (A.YM (HP m hm t)) ((2 * t : ℕ) - 1 : ℤ) w = 0 := by
  have h := top_char_unique m hm hm2 A hwΩ hwL (.inl r') huq' (VOA.mk (V2mPlus m hm) (HP m hm t))
  rw [topEvaluation_mk, oLevW_homogeneous A 0 (HP_mem_grading m hm t (by omega) (by omega)),
    add_zero, chiT_HP_zero m hm hm2 r' t ht, zero_smul] at h
  exact h

include hm2 huq in
/-- The `M(1)⁺` obstruction vanishes: `H⁴₍₂₎x = L(-1)x/3`. -/
theorem p2_eq_gen (hs : r.val + 3 ≤ m) (r' : Fin (m - 1))
    (huq' : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r' → j = .inl r')
    (hgap : hC m r' = hC m r + 1)
    (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x)
    (hlow : ∀ μ : ℂ, μ.re < (hC m r).re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (hx0 : x ≠ 0) :
    mode (A.YM (HP m hm 2)) 2 x = (1 / 3 : ℂ) • mode (A.YM (HP m hm 1)) 0 x := by
  have hh0 := hC_ne_zero m hm2 r
  have hg2 := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  obtain ⟨c2, hw2⟩ := transfer_Omega_gen m hm hm2 r hs huq A hxΩ hxL hlow hg2
  obtain ⟨c3, hw3⟩ := transfer_Omega_gen m hm hm2 r hs huq A hxΩ hxL hlow hg3
  rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hw2
  rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hw3
  have hL1 : ∀ w : M, w ∈ Omega A → mode (A.YM (V2mPlus m hm).conformalVector) 2 w = 0 :=
    fun w hw => Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
  have hp1 := L1_p1_gen m hm hm2 r A hxΩ hxL
  have hc2 : c2 = 1 / 3 := by
    have h := hL1 _ hw2
    rw [map_sub, map_smul, L1_p2_gen m hm hm2 r huq A hxΩ hxL, hp1, smul_smul, ← sub_smul] at h
    rcases smul_eq_zero.mp h with h | h
    · have h' : (2 * hC m r) * (1 - 3 * c2) = 0 := by linear_combination 3 * h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd (by linear_combination h'' / 2) hh0
      · linear_combination -h'' / 3
    · exact absurd h hx0
  have hc3 : c3 = 1 / 5 := by
    have h := hL1 _ hw3
    rw [map_sub, map_smul, L1_p3_gen m hm hm2 r huq A hxΩ hxL, hp1, smul_smul, ← sub_smul] at h
    rcases smul_eq_zero.mp h with h | h
    · have h' : (2 * hC m r) * (1 - 5 * c3) = 0 := by linear_combination 5 * h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd (by linear_combination h'' / 2) hh0
      · linear_combination -h'' / 5
    · exact absurd h hx0
  subst hc2 hc3
  have hLp1 := L0_degOne_gen m hm r A hxL (V2mPlus m hm).conformal_mem
  have hLp2 := L0_degOne_gen m hm r A hxL hg2
  have hLp3 := L0_degOne_gen m hm r A hxL hg3
  rw [show ((2 : ℤ) - 2) = 0 by norm_num] at hLp1
  rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hLp2
  rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hLp3
  have hwL2 : L0 A (mode (A.YM (HP m hm 2)) 2 x - (1 / 3 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x)
      = hC m r' • (mode (A.YM (HP m hm 2)) 2 x - (1 / 3 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) := by
    rw [hgap, map_sub, map_smul, hLp1, hLp2, smul_sub, smul_comm]
  have hwL3 : L0 A (mode (A.YM (HP m hm 3)) 4 x - (1 / 5 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x)
      = hC m r' • (mode (A.YM (HP m hm 3)) 4 x - (1 / 5 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) := by
    rw [hgap, map_sub, map_smul, hLp1, hLp3, smul_sub, smul_comm]
  have hR1 := omega_route_gen m hm hm2 A r' huq' hw2 hwL2 2 (Or.inl rfl)
  have hR2 := omega_route_gen m hm hm2 A r' huq' hw3 hwL3 2 (Or.inl rfl)
  have hR3 := omega_route_gen m hm hm2 A r' huq' hw2 hwL2 3 (Or.inr rfl)
  rw [show ((2 * 2 : ℕ) : ℤ) - 1 = 3 by norm_num] at hR1 hR2
  rw [show ((2 * 3 : ℕ) : ℤ) - 1 = 5 by norm_num] at hR3
  have e1 := comm_H4_p2_gen m hm hm2 r huq A hxΩ hxL
  have e2 := comm_H4_p3_gen m hm hm2 r huq A hxΩ hxL
  have e3 := comm_H6_p2_gen m hm hm2 r huq A hxΩ hxL
  have f1 := oH4_p1_gen m hm hm2 r huq A hxΩ hxL
  have f2 := oH6_p1_gen m hm hm2 r huq A hxΩ hxL
  change mode (A.YM (HP m hm 2)) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) = _ at f1
  change mode (A.YM (HP m hm 3)) 5 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) = _ at f2
  change _ = (1 / 15 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x - _ + _ at e1
  change _ = (-1 / 35 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x + _ - _ + _ at e2
  change _ = (-1 / 21 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x + _ - _ + _ at e3
  rw [map_sub, map_smul, e1, f1] at hR1
  rw [map_sub, map_smul, e2, f1] at hR2
  rw [map_sub, map_smul, e3, f2] at hR3
  change _ = (1 / 3 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x
  linear_combination (norm := module) (-5 : ℂ) • hR1 + (15 : ℂ) • hR2 - (9 : ℂ) • hR3

include hm2 huq in
/-- The `E`-obstruction vanishes: `E₍ₘ₋₂₎x = 0`. -/
theorem v_eq_zero_gen (hs : r.val + 3 ≤ m) (r' : Fin (m - 1))
    (huq' : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r' → j = .inl r')
    (hgap : hC m r' = hC m r + 1)
    (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x)
    (hlow : ∀ μ : ℂ, μ.re < (hC m r).re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (hx0 : x ≠ 0) :
    mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0 := by
  obtain ⟨cE, hw⟩ := transfer_Omega_gen m hm hm2 r hs huq A hxΩ hxL hlow (EP_mem_grading m hm)
  have hp1 := L1_p1_gen m hm hm2 r A hxΩ hxL
  have hcE : cE = 0 := by
    have h := Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
    rw [map_sub, map_smul, L1_v_gen m hm hm2 r huq A hxΩ hxL, hp1, smul_smul, zero_sub,
      neg_eq_zero] at h
    rcases smul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd (by linear_combination h / 2) (hC_ne_zero m hm2 r)
    · exact absurd h hx0
  subst hcE
  rw [zero_smul, sub_zero] at hw
  have hwL := L0_degOne_gen m hm r A hxL (EP_mem_grading m hm)
  rw [← hgap] at hwL
  have hR := omega_route_gen m hm hm2 A r' huq' hw hwL 2 (Or.inl rfl)
  rw [show ((2 * 2 : ℕ) : ℤ) - 1 = 3 by norm_num] at hR
  have hv := oH4_v_gen m hm hm2 r huq A hxΩ hxL
  rw [hR, smul_zero] at hv
  rcases smul_eq_zero.mp hv.symm with h | h
  · exfalso
    -- `4m h = s²` and `s ≤ m - 2`
    have hh : 4 * (m : ℂ) * hC m r = (((r.val + 1 : ℕ) : ℂ)) ^ 2 := by
      simp only [hC, weight]
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      push_cast
      field_simp
    rw [hh] at h
    have h2 : (((m : ℂ) - 1) ^ 2 - (((r.val + 1 : ℕ) : ℂ)) ^ 2) = 0 := by
      linear_combination h / 2
    have h3 : (((m : ℤ) - 1) ^ 2 - (((r.val + 1 : ℕ) : ℤ)) ^ 2 : ℤ) = 0 := by
      exact_mod_cast h2
    have h4 : ((m : ℤ) - 1 - (r.val + 1)) * ((m : ℤ) - 1 + (r.val + 1)) = 0 := by
      push_cast at h3; linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5 <;> omega
  · exact h

end GenTop

/-! ## The splitting, general `m` -/

section GenSplit
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
include hm2

/-- The degree-one span of the top is the line of `L(-1)x`. -/
theorem degOne_le_line_gen (r : Fin (m - 1)) (hs : r.val + 3 ≤ m)
    (huq : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r → j = .inl r) (r' : Fin (m - 1))
    (huq' : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r' → j = .inl r')
    (hgap : hC m r' = hC m r + 1)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
    {x : M} (hxΩ : x ∈ Omega A) (hxL : L0 A x = hC m r • x)
    (hlow : ∀ μ : ℂ, μ.re < (hC m r).re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (hx0 : x ≠ 0) :
    degOneSpan A x ≤ Submodule.span ℂ {mode (A.YM (V2mPlus m hm).conformalVector) 0 x} := by
  set G := Set.range (gP m hm)
  have hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ (V2mPlus m hm).grading j := by
    rintro g ⟨i, rfl⟩
    exact ⟨_, by fin_cases i <;> simp [wtP] <;> omega, gP_mem_grading m hm i⟩
  have hST : ScalarTop A x := ⟨hxΩ, fun j c hc =>
    ⟨_, zero_mode_top_gen m hm hm2 r huq A hxΩ hxL hc⟩⟩
  have hraise := raise_mem hG (top_eq_span_iterProd m hm hm2) hST
  set L := Submodule.span ℂ {mode (A.YM (V2mPlus m hm).conformalVector) 0 x}
  have hp1 : mode (A.YM (V2mPlus m hm).conformalVector) 0 x ∈ L := Submodule.mem_span_singleton_self _
  have hgen : raiseSpan A G x ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, g, ⟨i, rfl⟩, hgj, rfl⟩
    have hwt := gP_mem_grading m hm i
    by_cases hj : j = wtP m i
    · subst hj
      fin_cases i
      · change mode (A.YM (V2mPlus m hm).conformalVector) ((2 : ℤ) - 2) x ∈ L
        rw [show (2 : ℤ) - 2 = 0 by norm_num]; exact hp1
      · change mode (A.YM (WP m hm)) ((4 : ℤ) - 2) x ∈ L
        rw [WP_eq_comb m hm]
        simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
        have h2 : mode (A.YM (HP m hm 2)) (4 - 2 - ((0 : ℕ) : ℤ)) x =
            (1 / 3 : ℂ) • mode (A.YM (HP m hm 1)) 0 x := by
          rw [show (4 : ℤ) - 2 - ((0 : ℕ) : ℤ) = 2 by norm_num]
          exact p2_eq_gen m hm hm2 r huq A hs r' huq' hgap hxΩ hxL hlow hx0
        rw [h2, show (4 : ℤ) - 2 - ((2 : ℕ) : ℤ) = 0 by norm_num]
        change _ • (_ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) +
          (_ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x + 0) ∈ L
        exact L.add_mem (L.smul_mem _ (L.smul_mem _ hp1)) (L.add_mem (L.smul_mem _ hp1) L.zero_mem)
      · change mode (A.YM (EP m hm)) (((m : ℕ) : ℤ) - 2) x ∈ L
        rw [v_eq_zero_gen m hm hm2 r huq A hs r' huq' hgap hxΩ hxL hlow hx0]
        exact L.zero_mem
    · rw [eq_zero_of_mem_two_gradings hj hgj hwt, map_zero, mode_zero, LinearMap.zero_apply]
      exact L.zero_mem
  apply Submodule.span_le.mpr
  rintro _ ⟨β, a, ha, rfl⟩
  exact hgen (hraise β a ha)

/-- **Every gap-one charged/charged pair splits** (kernel `c_{r'}`, quotient `c_r`), when
both rows are unique at their weights. -/
theorem pairSplitting_charged_gap_one (r r' : Fin (m - 1))
    (hgap : weight m (.inl r') = weight m (.inl r) + 1)
    (huq : ∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r)
    (huq' : ∀ j : Label m, weight m j = weight m (.inl r') → j = .inl r') :
    PairSplitting m hm (.inl r') (.inl r) := by
  intro M _ _ A P hP hQ hb ht
  -- arithmetic
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsq : ((r'.val + 1 : ℕ) : ℤ) ^ 2 = ((r.val + 1 : ℕ) : ℤ) ^ 2 + 4 * m := by
    have h := hgap
    simp only [weight] at h
    field_simp at h
    have : (((r'.val + 1 : ℕ) : ℤ) ^ 2 : ℚ) = ((((r.val + 1 : ℕ) : ℤ) ^ 2 + 4 * m : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast this
  have hs : r.val + 3 ≤ m := by
    have hr := r.isLt
    have hr' := r'.isLt
    by_contra hcon
    have hrm : r.val + 2 = m := by omega
    have : ((r'.val + 1 : ℕ) : ℤ) ^ 2 = ((m : ℤ) + 1) ^ 2 := by
      rw [hsq]; push_cast; rw [show (r.val : ℤ) = (m : ℤ) - 2 by omega]; ring
    have h4 : (((r'.val + 1 : ℕ) : ℤ) - ((m : ℤ) + 1)) * (((r'.val + 1 : ℕ) : ℤ) + ((m : ℤ) + 1)) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp h4 with h5 | h5 <;> push_cast at h5 <;> omega
  have hgapC : hC m r' = hC m r + 1 := by
    simp only [hC]; rw [hgap]; push_cast; ring
  have huqC : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r → j = .inl r :=
    fun j h => huq j (Rat.cast_injective h)
  have huqC' : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r' → j = .inl r' :=
    fun j h => huq' j (Rat.cast_injective h)
  change FactorBottom A ⊥ P (hC m r') at hb
  change FactorBottom A P ⊤ (hC m r) at ht
  have hre : (hC m r').re = (hC m r).re + 1 := by rw [hgapC]; simp
  have hlow : ∀ μ : ℂ, μ.re < (hC m r).re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0 := by
    intro μ hμ v hv
    have hvP : v ∈ P := by
      by_contra h
      have hw : FactorWeight A P ⊤ μ := fun hT => h (hT ⟨Submodule.mem_top, hv⟩)
      have := ht.2 μ hw
      linarith
    exact kernel_generalized_below_bottom_eq_zero A P _ hb hvP hv (by rw [hre]; linarith)
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift (V2mPlus_c2Cofinite m hm) A P hP
    (show hC m r' ≠ hC m r by rw [hgapC]; intro h; simpa using congrArg (· - hC m r) h) hb ht
  have hx0 : x ≠ 0 := fun h => hxP (h ▸ P.zero_mem)
  have hxg : x ∈ (L0 A).maxGenEigenspace (hC m r) :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  have hxΩ : x ∈ Omega A := by
    intro β v hv n hn
    apply hlow _ _ _ (mode_mem_maxGenEigenspace A hv n hxg)
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show β - n - 1 ≤ -1 by omega)
    rw [Complex.add_re, Complex.intCast_re]
    linarith
  apply (exists_cyclic_lift_iff_complement A P hQ (hC m r) ht).mp
  refine ⟨x, hxg, hxP, ?_⟩
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  have hyg : y ∈ (L0 A).maxGenEigenspace (hC m r + ((1 : ℤ) : ℂ)) := by
    rw [show hC m r + ((1 : ℤ) : ℂ) = hC m r' by rw [hgapC]; push_cast; ring]; exact hy.2
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0' x,
    no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite m hm) A hxg 1 hyg]
  intro hyD
  have hyL := degOne_le_line_gen m hm hm2 r hs huqC r' huqC' hgapC A hxΩ hxL hlow hx0
    (degreeSpan_one_le A hxL hyD)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyL
  have hL1 := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 2 hy.1
  rw [map_smul, L1_p1_gen m hm hm2 r A hxΩ hxL, smul_smul] at hL1
  by_cases hc : c = 0
  · subst hc; rw [zero_smul] at hy0'; exact hy0' rfl
  · apply hxP
    have hc' : c * (2 * hC m r) ≠ 0 := mul_ne_zero hc (mul_ne_zero two_ne_zero (hC_ne_zero m hm2 r))
    have := P.smul_mem ((algebraMap ℂ (modeAlg A)) (c * (2 * hC m r))⁻¹) hL1
    rw [algebraMap_smul, smul_smul, inv_mul_cancel₀ hc', one_smul] at this
    exact this

/-- Both orientations of a gap-one charged/charged pair. -/
theorem pairSplitting_charged_gap_one_both (r r' : Fin (m - 1))
    (hgap : weight m (.inl r') = weight m (.inl r) + 1)
    (huq : ∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r)
    (huq' : ∀ j : Label m, weight m j = weight m (.inl r') → j = .inl r') :
    PairSplitting m hm (.inl r') (.inl r) ∧ PairSplitting m hm (.inl r) (.inl r') :=
  ⟨pairSplitting_charged_gap_one m hm hm2 r r' hgap huq huq',
    pairSplitting_swap m hm (by rw [hgap]; intro h; linarith)
      (pairSplitting_charged_gap_one m hm hm2 r r' hgap huq huq')⟩

end GenSplit

end VOA.Classification.COne.PlusRat3
