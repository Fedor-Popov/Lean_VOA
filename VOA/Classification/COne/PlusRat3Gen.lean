import VOA.Classification.COne.PlusRat3Gap1

/-! # Parameterized top computations and the general transfer lemma

* `transfer_general` (any VOA): if `x` (in `A`) and `e ≠ 0` (in a model `B`) are top vectors on
  which Zhu's algebra acts through the same function, and `t₍ₖ₋₂₎e = c L(-1)e` in the model, then
  `t₍ₖ₋₂₎x - c L(-1)x` is a top vector of `A` (given no generalized weights of `A` below `h`).
* For `V_{2m}⁺`: the commutators, `L(1)`-values and the `E`-virtual eigenvalue on a top `x` with
  `L(0) = h`, `o(H⁴) = a₄`, `o(H⁶) = a₆`, `o(E) = 0` (`commG_*`, `L1G_*`, `oG_H4_v`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible

/-! ## §1  Transfer, any VOA -/

section GenTransfer
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

/-- **Transfer** (any VOA). -/
theorem transfer_general (A : WeakModule W M) (B : WeakModule W N) (χ : VOA.A W → ℂ)
    {x : M} {e : N} (hxΩ : x ∈ Omega A) (heΩ : e ∈ Omega B)
    (hχx : ∀ r, topEvaluation A x hxΩ r = χ r • x) (hχe : ∀ r, topEvaluation B e heΩ r = χ r • e)
    (he0 : e ≠ 0) {h : ℂ} (hxL : L0 A x = h • x)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0)
    {k : ℤ} {t : V} (ht : t ∈ W.grading k) {c : ℂ}
    (hc : mode (B.YM t) (k - 2) e = c • mode (B.YM W.conformalVector) 0 e) :
    mode (A.YM t) (k - 2) x - c • mode (A.YM W.conformalVector) 0 x ∈ Omega A := by
  intro β b hb n hn
  rcases eq_or_lt_of_le hn with hnβ | hnβ
  · subst hnβ
    by_cases hβ0 : β < 0
    · rw [W.positivity β hβ0, Submodule.mem_bot] at hb
      subst hb
      rw [map_zero, mode_zero, LinearMap.zero_apply]
    obtain ⟨P, rfl⟩ : ∃ P : ℕ, β = P := ⟨β.toNat, by omega⟩
    have h1 := lowering_composite_eq A ht hb hxΩ P (k - 2) le_rfl (by ring)
    have h2 := lowering_composite_eq A W.conformal_mem hb hxΩ P 0 le_rfl (by ring)
    have h1e := lowering_composite_eq B ht hb heΩ P (k - 2) le_rfl (by ring)
    have h2e := lowering_composite_eq B W.conformal_mem hb heΩ P 0 le_rfl (by ring)
    rw [← topEvaluation_mk A x hxΩ, hχx] at h1 h2
    rw [← topEvaluation_mk B e heΩ, hχe] at h1e h2e
    have hrel : mode (B.YM b) P (mode (B.YM t) (k - 2) e) =
        c • mode (B.YM b) P (mode (B.YM W.conformalVector) 0 e) := by
      rw [hc, map_smul]
    rw [h1e, h2e, smul_smul] at hrel
    have hs0 : (χ (VOA.mk W (zstate W t b P)) -
        c * χ (VOA.mk W (zstate W W.conformalVector b P))) • e = 0 := by
      rw [sub_smul, hrel, sub_self]
    rw [map_sub, map_smul, h1, h2, smul_smul, ← sub_smul]
    rcases smul_eq_zero.mp hs0 with h0 | h0
    · rw [h0, zero_smul]
    · exact absurd h0 he0
  · have hxg : x ∈ (L0 A).maxGenEigenspace h :=
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
    have hv : mode (A.YM t) (k - 2) x - c • mode (A.YM W.conformalVector) 0 x ∈
        (L0 A).maxGenEigenspace (h + 1) := by
      have h1 := mode_mem_maxGenEigenspace A ht (k - 2) hxg
      have h2 := mode_mem_maxGenEigenspace A W.conformal_mem 0 hxg
      have hc1 : h + ((k - (k - 2) - 1 : ℤ) : ℂ) = h + 1 := by push_cast; ring
      have hc2 : h + ((2 - 0 - 1 : ℤ) : ℂ) = h + 1 := by push_cast; ring
      rw [hc1] at h1
      rw [hc2] at h2
      exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2)
    have h3 := mode_mem_maxGenEigenspace A hb n hv
    apply hlow _ _ _ h3
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (show β - n - 1 ≤ -2 by omega)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
    linarith

end GenTransfer

/-! ## §2  Parameterized top computations in `V_{2m}⁺` -/

section GenComp
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h a4 a6 : ℂ}
  (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x)
  (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x) (h6 : mode (A.YM (HP m hm 3)) 5 x = a6 • x)
  (hE : mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0)

include h4 in
theorem commG_H4_p2 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 2)) 2 x) =
      (1 / 15 : ℂ) • mode (A.YM (HP m hm 1)) 0 x + (a4 - 1) • mode (A.YM (HP m hm 2)) 2 x +
        (3 : ℂ) • mode (A.YM (HP m hm 3)) 4 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 2) 2 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H44_eq m hm 0 (by norm_num), H44_eq m hm 1 (by norm_num), H44_eq m hm 2 (by norm_num),
    H44_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T44, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h4 in
theorem commG_H4_p3 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (HP m hm 3)) 4 x) =
      (-1 / 35 : ℂ) • mode (A.YM (HP m hm 1)) 0 x + (3 / 5 : ℂ) • mode (A.YM (HP m hm 2)) 2 x +
        (a4 - 2) • mode (A.YM (HP m hm 3)) 4 x + (3 : ℂ) • mode (A.YM (HP m hm 4)) 6 x := by
  have h := zero_mode_comm A 3 (HP m hm 2) (HP m hm 3) 4 x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H46_eq m hm 0 (by norm_num), H46_eq m hm 1 (by norm_num), H46_eq m hm 2 (by norm_num),
    H46_eq m hm 3 (by norm_num)]
  simp only [mode_combV, T46, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  norm_num
  module

include h6 in
theorem commG_H6_p2 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (HP m hm 2)) 2 x) =
      (-1 / 21 : ℂ) • mode (A.YM (HP m hm 1)) 0 x + (a6 + 1) • mode (A.YM (HP m hm 2)) 2 x -
        (10 / 3 : ℂ) • mode (A.YM (HP m hm 3)) 4 x + (5 : ℂ) • mode (A.YM (HP m hm 4)) 6 x := by
  have h := zero_mode_comm A 5 (HP m hm 3) (HP m hm 2) 2 x
  rw [show ((5 : ℕ) : ℤ) = 5 by rfl, h6, map_smul] at h
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

include h4 in
theorem oG_H4_p1 :
    mode (A.YM (HP m hm 2)) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      a4 • mode (A.YM (V2mPlus m hm).conformalVector) 0 x + (3 : ℂ) • mode (A.YM (HP m hm 2)) 2 x := by
  rw [mode_translation, h4, map_smul]
  norm_num

include h6 in
theorem oG_H6_p1 :
    mode (A.YM (HP m hm 3)) 5 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      a6 • mode (A.YM (V2mPlus m hm).conformalVector) 0 x + (5 : ℂ) • mode (A.YM (HP m hm 3)) 4 x := by
  rw [mode_translation, h6, map_smul]
  norm_num

include hm2 hxΩ hxL in
theorem L1G_p1 :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (2 * h) • x := by
  rw [L1_on_gen m hm A hxΩ (V2mPlus m hm).conformal_mem 0, L1_omega_zero_gen m hm hm2, map_zero,
    mode_zero, LinearMap.zero_apply, add_zero]
  have hL : mode (A.YM (V2mPlus m hm).conformalVector) (0 + 1) x = h • x := hxL
  rw [hL, smul_smul]
  norm_num

include hxΩ hxL h4 in
theorem L1G_p2 :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 2)) 2 x) =
      (4 * a4 + 2 * h / 3) • x := by
  rw [L1_on_gen m hm A hxΩ (HP_mem_grading m hm 2 (by norm_num) (by norm_num)) 2, L1_H4]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have h3 : mode (A.YM (HP m hm 2)) (2 + 1) x = a4 • x := h4
  have hL : mode (A.YM (HP m hm 1)) (2 - ((1 : ℕ) : ℤ)) x = h • x := hxL
  rw [h3, hL]
  push_cast
  module

include hxΩ hxL h4 h6 in
theorem L1G_p3 :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (HP m hm 3)) 4 x) =
      (6 * a6 + 6 * a4 + 2 * h / 5) • x := by
  rw [L1_on_gen m hm A hxΩ (HP_mem_grading m hm 3 (by norm_num) (by norm_num)) 4, L1_H6]
  simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have h5 : mode (A.YM (HP m hm 3)) (4 + 1) x = a6 • x := h6
  have hL : mode (A.YM (HP m hm 1)) (4 - ((3 : ℕ) : ℤ)) x = h • x := hxL
  have h3 : mode (A.YM (HP m hm 2)) (4 - ((1 : ℕ) : ℤ)) x = a4 • x := h4
  rw [h5, hL, h3]
  push_cast
  module

include hxΩ hE in
theorem L1G_v :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (EP m hm)) ((m : ℤ) - 2) x) = 0 := by
  rw [L1_on_gen m hm A hxΩ (EP_mem_grading m hm) _, L1_E m hm, map_zero, mode_zero,
    LinearMap.zero_apply, add_zero, show (m : ℤ) - 2 + 1 = (m : ℤ) - 1 by ring, hE, smul_zero]

include hE in
theorem EG_Lx :
    mode (A.YM (EP m hm)) ((m : ℤ) - 1) (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (((m : ℤ) - 1 : ℤ) : ℂ) • mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
  rw [mode_translation, hE, map_zero, zero_add, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring]

include hxΩ hxL h4 hE in
/-- The `E`-virtual eigenvalue on a general top:
`(2K-1)(K-2) o(H⁴) v = ((2K-1)(K-2) a₄ + 2((m-1)² - 4m h)) v`, `K = 2m`. -/
theorem oG_H4_v :
    ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2)) •
        mode (A.YM (HP m hm 2)) 3 (mode (A.YM (EP m hm)) ((m : ℤ) - 2) x) =
      ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) * a4 + 2 * (((m : ℂ) - 1) ^ 2 - 4 * m * h)) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
  have hLx := EG_Lx m hm A hE
  have e3 : mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 3 (EP m hm))) ((m : ℤ) - 2) x = 0 := by
    rw [H4_3_E]; simp
  have e2 : (3 : ℂ) • mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 2 (EP m hm))) ((m : ℤ) - 1) x =
      (-(((m : ℤ) - 1 : ℤ) : ℂ)) • mode (A.YM (EP m hm)) ((m : ℤ) - 2) x := by
    have h2 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 1) x) (H4_2_E m hm)
    simp only [map_smul, mode_smul, LinearMap.smul_apply] at h2
    rw [T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring] at h2
    exact h2
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
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at hc
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

theorem L0G_degOne {k : ℤ} {a : VP m hm} (ha : a ∈ (V2mPlus m hm).grading k) (hxL : L0 A x = h • x) :
    L0 A (mode (A.YM a) (k - 2) x) = (h + 1) • mode (A.YM a) (k - 2) x := by
  rw [L0_commutator_weak A ha x (k - 2), hxL, map_smul, ← add_smul]
  congr 1
  push_cast; ring

end GenComp

end VOA.Classification.COne.PlusRat3
