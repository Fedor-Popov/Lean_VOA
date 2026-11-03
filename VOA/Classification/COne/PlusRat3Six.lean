import VOA.Classification.COne.PlusRat3Transfer
import VOA.Classification.COne.PlusRat3Charged
import VOA.Classification.COne.PlusRat3Degree
import VOA.Classification.COne.PlusRat2Unordered

/-! # `V₁₂⁺` is strongly rational: the charged pair `(c₁, c₅)` splits

Orientation: kernel bottom `25/24` (row `c₅`),
quotient bottom `1/24` (row `c₁`).  For the quotient-bottom lift `x` (a top vector of the whole
extension with the character of `c₁`):

* `p_t = H^{2t}₍₂ₜ₋₂₎x` (`p₁ = L(-1)x`) and `v = E₍₄₎x`;
* `[o(H⁴), p₂]`, `[o(H⁴), p₃]`, `[o(H⁶), p₂]` from the product tables of `PlusRat3Quad`;
* `o(H⁴) v = (24/115) v` from `PlusRat3Charged` and the iterate formula;
* the transfer lemma makes `p_t - c_t p₁` and `v` top vectors of weight `25/24`, on which
  `o(H⁴) = o(H⁶) = 0` (row `c₅`).

Hence `p₂ = p₁/3`, `v = 0`, the degree-one part of the cyclic module of `x` is `ℂ L(-1)x`, and the
cyclic module avoids the kernel.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible

/-! ## §1  Modes of `combV` -/

section Comb
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M)

theorem mode_combV (n : ℤ) (y : M) : ∀ L : List (ℚ × ℕ × ℕ),
    mode (A.YM (combV m hm L)) n y =
      (L.map fun e => (((e.1 : ℚ) : ℂ) * fallC n e.2.1) •
        mode (A.YM (HP m hm e.2.2)) (n - e.2.1) y).sum
  | [] => by simp [combV]
  | (c, k, t) :: rest => by
    rw [combV, map_add, map_smul, mode_add, mode_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LmV, Tpow_mode A, mode_combV n y rest, List.map_cons, List.sum_cons, smul_smul]

end Comb

/-! ## §2  The top vector of the extension -/

section Top

theorem two_le_six : 2 ≤ 6 := by norm_num

variable (hm : 1 ≤ 6) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus 6 hm) M) {x : M}

/-- Zero modes act on the top `x` by the row `c₁`. -/
theorem zero_mode_top (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) {k : ℤ}
    {a : VP 6 hm} (ha : a ∈ (V2mPlus 6 hm).grading k) :
    mode (A.YM a) (k - 1) x = chiT 6 hm two_le_six (.inl 0) (VOA.mk (V2mPlus 6 hm) a) • x := by
  have h := top_char_unique 6 hm two_le_six A hxΩ hxL (.inl 0) uniq_six_one (VOA.mk (V2mPlus 6 hm) a)
  rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h
  exact h

theorem oH4_top (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 2)) 3 x = 0 := by
  have h := zero_mode_top hm A hxΩ hxL (HP_mem_grading 6 hm 2 (by norm_num) (by norm_num))
  rw [chiT_HP_zero 6 hm two_le_six 0 2 (Or.inl rfl), zero_smul] at h
  simpa using h

theorem oH6_top (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 3)) 5 x = 0 := by
  have h := zero_mode_top hm A hxΩ hxL (HP_mem_grading 6 hm 3 (by norm_num) (by norm_num))
  rw [chiT_HP_zero 6 hm two_le_six 0 3 (Or.inr rfl), zero_smul] at h
  simpa using h

theorem oE_top (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (EP 6 hm)) 5 x = 0 := by
  have h := zero_mode_top hm A hxΩ hxL (EP_mem_grading 6 hm)
  have hv := (chiT_hasValues 6 hm two_le_six (.inl 0)).2.2
  change chiT 6 hm two_le_six (.inl 0) (VOA.mk (V2mPlus 6 hm) (EP 6 hm)) = _ at hv
  rw [hv] at h
  simp [values] at h
  simpa using h

/-- `[o(H⁴), p₂] = p₁/15 - p₂ + 3p₃`. -/
theorem comm_H4_p2 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 2)) 3 (mode (A.YM (HP 6 hm 2)) 2 x) =
      (1 / 15 : ℂ) • mode (A.YM (HP 6 hm 1)) 0 x - mode (A.YM (HP 6 hm 2)) 2 x +
        (3 : ℂ) • mode (A.YM (HP 6 hm 3)) 4 x := by
  have h := zero_mode_comm A 3 (HP 6 hm 2) (HP 6 hm 2) 2 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, oH4_top hm A hxΩ hxL, map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H44_eq 6 hm 0 (by norm_num), H44_eq 6 hm 1 (by norm_num), H44_eq 6 hm 2 (by norm_num),
    H44_eq 6 hm 3 (by norm_num)]
  simp only [mode_combV, T44, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

/-- `[o(H⁴), p₃] = -p₁/35 + 3p₂/5 - 2p₃ + 3p₄`. -/
theorem comm_H4_p3 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 2)) 3 (mode (A.YM (HP 6 hm 3)) 4 x) =
      (-1 / 35 : ℂ) • mode (A.YM (HP 6 hm 1)) 0 x + (3 / 5 : ℂ) • mode (A.YM (HP 6 hm 2)) 2 x -
        (2 : ℂ) • mode (A.YM (HP 6 hm 3)) 4 x + (3 : ℂ) • mode (A.YM (HP 6 hm 4)) 6 x := by
  have h := zero_mode_comm A 3 (HP 6 hm 2) (HP 6 hm 3) 4 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, oH4_top hm A hxΩ hxL, map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H46_eq 6 hm 0 (by norm_num), H46_eq 6 hm 1 (by norm_num), H46_eq 6 hm 2 (by norm_num),
    H46_eq 6 hm 3 (by norm_num)]
  simp only [mode_combV, T46, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

/-- `[o(H⁶), p₂] = -p₁/21 + p₂ - 10p₃/3 + 5p₄`. -/
theorem comm_H6_p2 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 3)) 5 (mode (A.YM (HP 6 hm 2)) 2 x) =
      (-1 / 21 : ℂ) • mode (A.YM (HP 6 hm 1)) 0 x + mode (A.YM (HP 6 hm 2)) 2 x -
        (10 / 3 : ℂ) • mode (A.YM (HP 6 hm 3)) 4 x + (5 : ℂ) • mode (A.YM (HP 6 hm 4)) 6 x := by
  have h := zero_mode_comm A 5 (HP 6 hm 3) (HP 6 hm 2) 2 x
  rw [show ((5 : ℕ) : ℤ) = 5 by rfl, oH6_top hm A hxΩ hxL, map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H64_eq 6 hm 0 (by norm_num), H64_eq 6 hm 1 (by norm_num), H64_eq 6 hm 2 (by norm_num),
    H64_eq 6 hm 3 (by norm_num), H64_eq 6 hm 4 (by norm_num), H64_eq 6 hm 5 (by norm_num)]
  simp only [mode_combV, T64, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  simp only [show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl,
    show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl,
    show Nat.choose 5 4 = 5 from rfl, show Nat.choose 5 5 = 1 from rfl]
  norm_num
  module

theorem oH4_p1 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 2)) 3 (mode (A.YM (HP 6 hm 1)) 0 x) =
      (3 : ℂ) • mode (A.YM (HP 6 hm 2)) 2 x := by
  change mode (A.YM (HP 6 hm 2)) 3 (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) = _
  rw [mode_translation, oH4_top hm A hxΩ hxL, map_zero, zero_add]
  norm_num

theorem oH6_p1 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 3)) 5 (mode (A.YM (HP 6 hm 1)) 0 x) =
      (5 : ℂ) • mode (A.YM (HP 6 hm 3)) 4 x := by
  change mode (A.YM (HP 6 hm 3)) 5 (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) = _
  rw [mode_translation, oH6_top hm A hxΩ hxL, map_zero, zero_add]
  norm_num

/-- `L(1)` on a degree-one vector `u₍ₙ₎x` of the top. -/
theorem L1_on (hxΩ : x ∈ Omega A) {wt : ℤ} {u : VP 6 hm} (hu : u ∈ (V2mPlus 6 hm).grading wt)
    (n : ℤ) :
    mode (A.YM (V2mPlus 6 hm).conformalVector) 2 (mode (A.YM u) n x) =
      ((2 * wt - n - 2 : ℤ) : ℂ) • mode (A.YM u) (n + 1) x + mode (A.YM ((V2mPlus 6 hm).L 1 u)) n x := by
  have h := L1_comm A hu n x
  rw [Omega_mode_vanish hxΩ (V2mPlus 6 hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num),
    map_zero, sub_zero] at h
  exact h

theorem L1_omega_zero : (V2mPlus 6 hm).L 1 (V2mPlus 6 hm).conformalVector = 0 := by
  have hg : (V2mPlus 6 hm).L 1 (V2mPlus 6 hm).conformalVector ∈ (V2mPlus 6 hm).grading 1 := by
    have := (V2mPlus 6 hm).toPreVertexAlgebra.smul_mem_grading (V2mPlus 6 hm).conformal_mem
      (V2mPlus 6 hm).conformal_mem 2
    rw [VertexOperatorAlgebra.L_def]
    simpa using this
  rw [grading_one_eq_bot 6 hm two_le_six, Submodule.mem_bot] at hg
  exact hg

theorem L1_p1 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (V2mPlus 6 hm).conformalVector) 2 (mode (A.YM (HP 6 hm 1)) 0 x) =
      (1 / 12 : ℂ) • x := by
  change mode (A.YM (V2mPlus 6 hm).conformalVector) 2
    (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) = _
  rw [L1_on hm A hxΩ (V2mPlus 6 hm).conformal_mem 0, L1_omega_zero hm, map_zero, mode_zero,
    LinearMap.zero_apply, add_zero]
  have hL : mode (A.YM (V2mPlus 6 hm).conformalVector) (0 + 1) x = (1 / 24 : ℂ) • x := hxL
  rw [hL, smul_smul]
  norm_num

theorem L1_p2 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (V2mPlus 6 hm).conformalVector) 2 (mode (A.YM (HP 6 hm 2)) 2 x) =
      (1 / 36 : ℂ) • x := by
  rw [L1_on hm A hxΩ (HP_mem_grading 6 hm 2 (by norm_num) (by norm_num)) 2, L1_H4]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have h3 : mode (A.YM (HP 6 hm 2)) (2 + 1) x = 0 := oH4_top hm A hxΩ hxL
  have hL : mode (A.YM (HP 6 hm 1)) (2 - ((1 : ℕ) : ℤ)) x = (1 / 24 : ℂ) • x := hxL
  rw [h3, hL]
  norm_num
  module

theorem L1_p3 (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (V2mPlus 6 hm).conformalVector) 2 (mode (A.YM (HP 6 hm 3)) 4 x) =
      (1 / 60 : ℂ) • x := by
  rw [L1_on hm A hxΩ (HP_mem_grading 6 hm 3 (by norm_num) (by norm_num)) 4, L1_H6]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have h5 : mode (A.YM (HP 6 hm 3)) (4 + 1) x = 0 := oH6_top hm A hxΩ hxL
  have hL : mode (A.YM (HP 6 hm 1)) (4 - ((3 : ℕ) : ℤ)) x = (1 / 24 : ℂ) • x := hxL
  have h3 : mode (A.YM (HP 6 hm 2)) (4 - ((1 : ℕ) : ℤ)) x = 0 := oH4_top hm A hxΩ hxL
  rw [h5, hL, h3]
  norm_num
  module

theorem L1_v (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (V2mPlus 6 hm).conformalVector) 2 (mode (A.YM (EP 6 hm)) 4 x) = 0 := by
  rw [L1_on hm A hxΩ (EP_mem_grading 6 hm) 4, L1_E 6 hm, map_zero, mode_zero,
    LinearMap.zero_apply, add_zero]
  have h5 : mode (A.YM (EP 6 hm)) (4 + 1) x = 0 := oE_top hm A hxΩ hxL
  rw [h5, smul_zero]

theorem negOnePow_neg_one' : negOnePow (-1) = -1 := by
  have h := negOnePow_succ (-1)
  rw [show (-1 : ℤ) + 1 = 0 by norm_num, show negOnePow 0 = 1 by simp [negOnePow]] at h
  linear_combination h

theorem negOnePow_neg_two' : negOnePow (-2) = 1 := by
  have h := negOnePow_succ (-2)
  rw [show (-2 : ℤ) + 1 = -1 by norm_num, negOnePow_neg_one'] at h
  linear_combination h

theorem LE_mem_grading : (V2mPlus 6 hm).L (-1) (EP 6 hm) ∈ (V2mPlus 6 hm).grading 7 := by
  rw [L_neg_one_eq_smul]
  have := (V2mPlus 6 hm).toPreVertexAlgebra.smul_mem_grading (V2mPlus 6 hm).conformal_mem
    (EP_mem_grading 6 hm) 0
  convert this using 2

/-- `E₍₅₎L(-1)x = 5 v`. -/
theorem E5_Lx (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (EP 6 hm)) 5 (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) =
      (5 : ℂ) • mode (A.YM (EP 6 hm)) 4 x := by
  rw [mode_translation, oE_top hm A hxΩ hxL, map_zero, zero_add]
  norm_num

/-- The virtual `H⁴`-eigenvalue of `v = E₍₄₎x`: `o(H⁴) v = (24/115) v`. -/
theorem oH4_v (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x) :
    mode (A.YM (HP 6 hm 2)) 3 (mode (A.YM (EP 6 hm)) 4 x) =
      (24 / 115 : ℂ) • mode (A.YM (EP 6 hm)) 4 x := by
  have h5 := E5_Lx hm A hxΩ hxL
  -- j = 3
  have e3 : mode (A.YM ((V2mPlus 6 hm).smul (HP 6 hm 2) 3 (EP 6 hm))) 4 x = 0 := by
    rw [H4_3_E]; simp
  -- j = 2
  have e2 : mode (A.YM ((V2mPlus 6 hm).smul (HP 6 hm 2) 2 (EP 6 hm))) 5 x =
      (-5 / 3 : ℂ) • mode (A.YM (EP 6 hm)) 4 x := by
    have h2 := congrArg (fun y => mode (A.YM y) 5 x) (H4_2_E 6 hm)
    simp only [map_smul, mode_smul, LinearMap.smul_apply] at h2
    rw [T_mode, show (5 : ℤ) - 1 = 4 by norm_num] at h2
    push_cast at h2
    linear_combination (norm := module) (1 / 3 : ℂ) • h2
  -- j = 1
  have e1 : mode (A.YM ((V2mPlus 6 hm).smul (HP 6 hm 2) 1 (EP 6 hm))) 6 x =
      (91 / 23 : ℂ) • mode (A.YM (EP 6 hm)) 4 x := by
    have h1 := congrArg (fun y => mode (A.YM y) 6 x) (H4_1_E 6 hm)
    simp only [map_smul, map_sub, mode_smul, mode_sub, LinearMap.smul_apply,
      LinearMap.sub_apply] at h1
    have hω := omega_neg_mode A hxΩ hxL (EP_mem_grading 6 hm) 1 le_rfl
    rw [show ((6 : ℕ) : ℤ) + 1 - 1 = 6 by norm_num, show ((6 : ℕ) : ℤ) - 1 = 5 by norm_num,
      show ((6 : ℕ) : ℤ) - 2 = 4 by norm_num, h5, negOnePow_neg_one'] at hω
    rw [hω, T_mode, T_mode, show (6 : ℤ) - 1 = 5 by norm_num, show (5 : ℤ) - 1 = 4 by norm_num] at h1
    push_cast at h1
    linear_combination (norm := module) (1 / 23 : ℂ) • h1
  -- j = 0
  have e0 : mode (A.YM ((V2mPlus 6 hm).smul (HP 6 hm 2) 0 (EP 6 hm))) 7 x =
      (-766 / 115 : ℂ) • mode (A.YM (EP 6 hm)) 4 x := by
    have h0 := congrArg (fun y => mode (A.YM y) 7 x) (H4_0_E 6 hm)
    simp only [map_smul, map_sub, map_add, mode_smul, mode_sub, mode_add, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply] at h0
    have hω2 := omega_neg_mode A hxΩ hxL (EP_mem_grading 6 hm) 2 (by norm_num)
    rw [show ((6 : ℕ) : ℤ) + 2 - 1 = 7 by norm_num, show ((6 : ℕ) : ℤ) - 1 = 5 by norm_num,
      show ((6 : ℕ) : ℤ) - 2 = 4 by norm_num, h5, negOnePow_neg_two'] at hω2
    have hω1 := omega_neg_mode A hxΩ hxL (LE_mem_grading hm) 1 le_rfl
    rw [show (7 : ℤ) + 1 - 1 = 7 by norm_num, show (7 : ℤ) - 1 = 6 by norm_num,
      show (7 : ℤ) - 2 = 5 by norm_num, T_mode, T_mode, negOnePow_neg_one'] at hω1
    rw [show (6 : ℤ) - 1 = 5 by norm_num, h5] at hω1
    rw [show (5 : ℤ) - 1 = 4 by norm_num] at hω1
    rw [hω2, hω1, T_mode, T_mode, T_mode, show (7 : ℤ) - 1 = 6 by norm_num,
      show (6 : ℤ) - 1 = 5 by norm_num, show (5 : ℤ) - 1 = 4 by norm_num] at h0
    push_cast at h0
    linear_combination (norm := module) (1 / 230 : ℂ) • h0
  have h := zero_mode_comm A 3 (HP 6 hm 2) (EP 6 hm) 4 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, oH4_top hm A hxΩ hxL, map_zero, zero_add] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl]
  rw [show (3 : ℤ) + 4 - 0 = 7 by norm_num, show (3 : ℤ) + 4 - 1 = 6 by norm_num,
    show (3 : ℤ) + 4 - 2 = 5 by norm_num, show (3 : ℤ) + 4 - 3 = 4 by norm_num, e0, e1, e2, e3]
  module

/-! ### The Omega-route: top vectors of weight `25/24` -/

theorem L0_degOne (hxL : L0 A x = (1 / 24 : ℂ) • x) {k : ℤ} {a : VP 6 hm}
    (ha : a ∈ (V2mPlus 6 hm).grading k) :
    L0 A (mode (A.YM a) (k - 2) x) = (25 / 24 : ℂ) • mode (A.YM a) (k - 2) x := by
  rw [L0_commutator_weak A ha x (k - 2), hxL, map_smul, ← add_smul]
  congr 1
  push_cast; ring

/-- On a top vector of weight `25/24` (row `c₅`), `o(H⁴)` and `o(H⁶)` vanish. -/
theorem omega_route {w : M} (hwΩ : w ∈ Omega A) (hwL : L0 A w = (25 / 24 : ℂ) • w) (t : ℕ)
    (ht : t = 2 ∨ t = 3) : mode (A.YM (HP 6 hm t)) ((2 * t : ℕ) - 1 : ℤ) w = 0 := by
  have h := top_char_unique 6 hm two_le_six A hwΩ hwL (.inl 4) uniq_six_five
    (VOA.mk (V2mPlus 6 hm) (HP 6 hm t))
  rw [topEvaluation_mk, oLevW_homogeneous A 0 (HP_mem_grading 6 hm t (by omega) (by omega)),
    add_zero, chiT_HP_zero 6 hm two_le_six 4 t ht, zero_smul] at h
  exact h

/-- **The M(1)⁺ obstruction vanishes**: `H⁴₍₂₎x = L(-1)x/3`. -/
theorem p2_eq (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x)
    (hlow : ∀ μ : ℂ, μ.re < 1 / 24 → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (hx0 : x ≠ 0) :
    mode (A.YM (HP 6 hm 2)) 2 x = (1 / 3 : ℂ) • mode (A.YM (HP 6 hm 1)) 0 x := by
  have hg2 := HP_mem_grading 6 hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading 6 hm 3 (by norm_num) (by norm_num)
  obtain ⟨c2, hw2⟩ := transfer_Omega hm two_le_six A hxΩ hxL hlow hg2
  obtain ⟨c3, hw3⟩ := transfer_Omega hm two_le_six A hxΩ hxL hlow hg3
  rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hw2
  rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hw3
  have hL1 : ∀ w : M, w ∈ Omega A → mode (A.YM (V2mPlus 6 hm).conformalVector) 2 w = 0 :=
    fun w hw => Omega_mode_vanish hw (V2mPlus 6 hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
  have hp1 := L1_p1 hm A hxΩ hxL
  change mode (A.YM (V2mPlus 6 hm).conformalVector) 2 (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x)
    = _ at hp1
  -- the constants `c₂ = 1/3`, `c₃ = 1/5`
  have hc2 : c2 = 1 / 3 := by
    have h := hL1 _ hw2
    rw [map_sub, map_smul, L1_p2 hm A hxΩ hxL, hp1, smul_smul, ← sub_smul] at h
    rcases smul_eq_zero.mp h with h | h
    · linear_combination (-12 : ℂ) * h
    · exact absurd h hx0
  have hc3 : c3 = 1 / 5 := by
    have h := hL1 _ hw3
    rw [map_sub, map_smul, L1_p3 hm A hxΩ hxL, hp1, smul_smul, ← sub_smul] at h
    rcases smul_eq_zero.mp h with h | h
    · linear_combination (-12 : ℂ) * h
    · exact absurd h hx0
  subst hc2 hc3
  -- weights
  have hLp1 := L0_degOne hm A hxL (V2mPlus 6 hm).conformal_mem
  have hLp2 := L0_degOne hm A hxL hg2
  have hLp3 := L0_degOne hm A hxL hg3
  rw [show ((2 : ℤ) - 2) = 0 by norm_num] at hLp1
  rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hLp2
  rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hLp3
  have hwL2 : L0 A (mode (A.YM (HP 6 hm 2)) 2 x - (1 / 3 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x)
      = (25 / 24 : ℂ) • (mode (A.YM (HP 6 hm 2)) 2 x - (1 / 3 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) := by
    rw [map_sub, map_smul, hLp1, hLp2, smul_sub, smul_comm]
  have hwL3 : L0 A (mode (A.YM (HP 6 hm 3)) 4 x - (1 / 5 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x)
      = (25 / 24 : ℂ) • (mode (A.YM (HP 6 hm 3)) 4 x - (1 / 5 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) := by
    rw [map_sub, map_smul, hLp1, hLp3, smul_sub, smul_comm]
  -- the three relations
  have hR1 := omega_route hm A hw2 hwL2 2 (Or.inl rfl)
  have hR2 := omega_route hm A hw3 hwL3 2 (Or.inl rfl)
  have hR3 := omega_route hm A hw2 hwL2 3 (Or.inr rfl)
  rw [show ((2 * 2 : ℕ) : ℤ) - 1 = 3 by norm_num] at hR1 hR2
  rw [show ((2 * 3 : ℕ) : ℤ) - 1 = 5 by norm_num] at hR3
  have e1 := comm_H4_p2 hm A hxΩ hxL
  have e2 := comm_H4_p3 hm A hxΩ hxL
  have e3 := comm_H6_p2 hm A hxΩ hxL
  have f1 := oH4_p1 hm A hxΩ hxL
  have f2 := oH6_p1 hm A hxΩ hxL
  change mode (A.YM (HP 6 hm 2)) 3 (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) = _ at f1
  change mode (A.YM (HP 6 hm 3)) 5 (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) = _ at f2
  change _ = (1 / 15 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x - _ + _ at e1
  change _ = (-1 / 35 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x + _ - _ + _ at e2
  change _ = (-1 / 21 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x + _ - _ + _ at e3
  rw [map_sub, map_smul, e1, f1] at hR1
  rw [map_sub, map_smul, e2, f1] at hR2
  rw [map_sub, map_smul, e3, f2] at hR3
  change _ = (1 / 3 : ℂ) • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x
  linear_combination (norm := module) (-5 : ℂ) • hR1 + (15 : ℂ) • hR2 - (9 : ℂ) • hR3

/-- **The E-obstruction vanishes**: `E₍₄₎x = 0`. -/
theorem v_eq_zero (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x)
    (hlow : ∀ μ : ℂ, μ.re < 1 / 24 → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (hx0 : x ≠ 0) :
    mode (A.YM (EP 6 hm)) 4 x = 0 := by
  obtain ⟨cE, hw⟩ := transfer_Omega hm two_le_six A hxΩ hxL hlow (EP_mem_grading 6 hm)
  rw [show ((6 : ℕ) : ℤ) - 2 = 4 by norm_num] at hw
  have hp1 := L1_p1 hm A hxΩ hxL
  change mode (A.YM (V2mPlus 6 hm).conformalVector) 2 (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x)
    = _ at hp1
  have hcE : cE = 0 := by
    have h := Omega_mode_vanish hw (V2mPlus 6 hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
    rw [map_sub, map_smul, L1_v hm A hxΩ hxL, hp1, smul_smul, zero_sub, neg_eq_zero] at h
    rcases smul_eq_zero.mp h with h | h
    · linear_combination (12 : ℂ) * h
    · exact absurd h hx0
  subst hcE
  rw [zero_smul, sub_zero] at hw
  have hwL := L0_degOne hm A hxL (EP_mem_grading 6 hm)
  rw [show ((6 : ℕ) : ℤ) - 2 = 4 by norm_num] at hwL
  have hR := omega_route hm A hw hwL 2 (Or.inl rfl)
  rw [show ((2 * 2 : ℕ) : ℤ) - 1 = 3 by norm_num, oH4_v hm A hxΩ hxL] at hR
  rcases smul_eq_zero.mp hR with h | h
  · norm_num at h
  · exact h

end Top

/-! ## §3  The splitting -/

section Split
variable (hm : 1 ≤ 6)

/-- The degree-one span of the top is the line of `L(-1)x`. -/
theorem degOne_le_line {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus 6 hm) M)
    {x : M} (hxΩ : x ∈ Omega A) (hxL : L0 A x = (1 / 24 : ℂ) • x)
    (hlow : ∀ μ : ℂ, μ.re < 1 / 24 → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (hx0 : x ≠ 0) :
    degOneSpan A x ≤ Submodule.span ℂ {mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x} := by
  set G := Set.range (gP 6 hm)
  have hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ (V2mPlus 6 hm).grading j := by
    rintro g ⟨i, rfl⟩
    exact ⟨_, by fin_cases i <;> simp [wtP], gP_mem_grading 6 hm i⟩
  have hST : ScalarTop A x := ⟨hxΩ, fun j c hc =>
    ⟨_, zero_mode_top hm A hxΩ hxL hc⟩⟩
  have hraise := raise_mem hG (top_eq_span_iterProd 6 hm two_le_six) hST
  set L := Submodule.span ℂ {mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x}
  have hp1 : mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x ∈ L := Submodule.mem_span_singleton_self _
  -- the generators
  have hgen : raiseSpan A G x ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, g, ⟨i, rfl⟩, hgj, rfl⟩
    have hwt := gP_mem_grading 6 hm i
    by_cases hj : j = wtP 6 i
    · subst hj
      fin_cases i
      · -- ω
        change mode (A.YM (V2mPlus 6 hm).conformalVector) ((2 : ℤ) - 2) x ∈ L
        rw [show (2 : ℤ) - 2 = 0 by norm_num]; exact hp1
      · -- W = 10 H⁴ + L(-1)²ω/3
        change mode (A.YM (WP 6 hm)) ((4 : ℤ) - 2) x ∈ L
        rw [WP_eq_comb 6 hm]
        simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
        have h2 : mode (A.YM (HP 6 hm 2)) (4 - 2 - ((0 : ℕ) : ℤ)) x =
            (1 / 3 : ℂ) • mode (A.YM (HP 6 hm 1)) 0 x := by
          rw [show (4 : ℤ) - 2 - ((0 : ℕ) : ℤ) = 2 by norm_num]
          exact p2_eq hm A hxΩ hxL hlow hx0
        rw [h2, show (4 : ℤ) - 2 - ((2 : ℕ) : ℤ) = 0 by norm_num]
        change _ • (_ • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) +
          (_ • mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x + 0) ∈ L
        exact L.add_mem (L.smul_mem _ (L.smul_mem _ hp1)) (L.add_mem (L.smul_mem _ hp1) L.zero_mem)
      · -- E
        change mode (A.YM (EP 6 hm)) (((6 : ℕ) : ℤ) - 2) x ∈ L
        rw [show ((6 : ℕ) : ℤ) - 2 = 4 by norm_num, v_eq_zero hm A hxΩ hxL hlow hx0]
        exact L.zero_mem
    · rw [eq_zero_of_mem_two_gradings hj hgj hwt, map_zero, mode_zero, LinearMap.zero_apply]
      exact L.zero_mem
  apply Submodule.span_le.mpr
  rintro _ ⟨β, a, ha, rfl⟩
  exact hgen (hraise β a ha)

/-- **The pair (c₅ kernel, c₁ quotient) splits at `m = 6`.** -/
theorem pairSplitting_c5_c1 : PairSplitting 6 hm (.inl 4) (.inl 0) := by
  intro M _ _ A P hP hQ hb ht
  have hw5 : ((weight 6 (.inl 4) : ℚ) : ℂ) = 25 / 24 := by norm_num [weight]
  have hw1 : ((weight 6 (.inl 0) : ℚ) : ℂ) = 1 / 24 := by norm_num [weight]
  rw [hw5] at hb
  rw [hw1] at ht
  have hlow : ∀ μ : ℂ, μ.re < 1 / 24 → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0 := by
    intro μ hμ v hv
    have hvP : v ∈ P := by
      by_contra h
      have hw : FactorWeight A P ⊤ μ := fun hT => h (hT ⟨Submodule.mem_top, hv⟩)
      have := ht.2 μ hw
      norm_num at this
      linarith
    exact kernel_generalized_below_bottom_eq_zero A P _ hb hvP hv (by norm_num; linarith)
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift (V2mPlus_c2Cofinite 6 hm) A P hP
    (show (25 / 24 : ℂ) ≠ 1 / 24 by norm_num) hb ht
  have hx0 : x ≠ 0 := fun h => hxP (h ▸ P.zero_mem)
  have hxg := mem_maxGen_of_eigen hm A hxL
  have hxΩ : x ∈ Omega A := by
    intro β v hv n hn
    apply hlow _ _ _ (mode_mem_maxGenEigenspace A hv n hxg)
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show β - n - 1 ≤ -1 by omega)
    rw [Complex.add_re, Complex.intCast_re]
    have h1 : (1 / 24 : ℂ).re = 1 / 24 := by norm_num
    rw [h1]; linarith
  apply (exists_cyclic_lift_iff_complement A P hQ (1 / 24) ht).mp
  refine ⟨x, hxg, hxP, ?_⟩
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  have hyg : y ∈ (L0 A).maxGenEigenspace (1 / 24 + ((1 : ℤ) : ℂ)) := by
    have h : (1 / 24 : ℂ) + ((1 : ℤ) : ℂ) = 25 / 24 := by push_cast; norm_num
    rw [h]; exact hy.2
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0' x,
    no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite 6 hm) A hxg 1 hyg]
  intro hyD
  have hyL := degOne_le_line hm A hxΩ hxL hlow hx0 (degreeSpan_one_le A hxL hyD)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyL
  have hL1 := PlusRat2Dual.mem_P_mode A P (V2mPlus 6 hm).conformalVector 2 hy.1
  have hp1 := L1_p1 hm A hxΩ hxL
  change mode (A.YM (V2mPlus 6 hm).conformalVector) 2
    (mode (A.YM (V2mPlus 6 hm).conformalVector) 0 x) = _ at hp1
  rw [map_smul, hp1, smul_smul] at hL1
  by_cases hc : c = 0
  · subst hc; rw [zero_smul] at hy0'; exact hy0' rfl
  · apply hxP
    have hc' : c * (1 / 12 : ℂ) ≠ 0 := mul_ne_zero hc (by norm_num)
    have := P.smul_mem ((algebraMap ℂ (modeAlg A)) (c * (1 / 12))⁻¹) hL1
    rw [algebraMap_smul, smul_smul, inv_mul_cancel₀ hc', one_smul] at this
    exact this

end Split

/-! ## §4  `V₁₂⁺` is strongly rational -/

/-- The single non-vacuum obligation at `m = 6`. -/
theorem pairSplitting_c1_c5 (hm : 1 ≤ 6) : PairSplitting 6 hm (.inl 0) (.inl 4) :=
  pairSplitting_swap 6 hm (by norm_num [weight]) (pairSplitting_c5_c1 hm)

/-- **`V₁₂⁺ = V_{√12 ℤ}⁺` is strongly rational.** -/
theorem V2mPlus_stronglyRational_six (hm : 1 ≤ 6) : StronglyRational (V2mPlus 6 hm) :=
  V2mPlus_stronglyRational_six_of hm (pairSplitting_c1_c5 hm)

end VOA.Classification.COne.PlusRat3
