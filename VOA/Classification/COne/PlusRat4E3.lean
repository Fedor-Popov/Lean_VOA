import VOA.Classification.COne.PlusRat4Top3

/-! # The `E`-part at degree three

* `omega_neg_mode3` (any VOA): `(ω₍₋ₖ₎a)₍α+k-3₎x` on a top vector.
* `oH4_v3`: `(2K²-5K+2)·o(H⁴)E₍ₘ₋₄₎x = ((2K²-5K+2)a₄ + 6((m-3)² - 4mh))·E₍ₘ₋₄₎x`, `K = 2m`,
  given `o(E)x = 0`, `E₍ₘ₋₂₎x = 0`, `E₍ₘ₋₃₎x = 0`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

section General
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

/-- `(ω₍₋ₖ₎a)₍α+k-3₎x` on a top vector. -/
theorem omega_neg_mode3 {x : M} (hx : x ∈ Omega A) {h : ℂ} (hL : L0 A x = h • x)
    {α : ℤ} {a : V} (ha : a ∈ W.grading α) (k : ℤ) (hk : 1 ≤ k) :
    mode (A.YM (W.smul W.conformalVector (-k) a)) (α + k - 3) x =
      mode (A.YM W.conformalVector) (-k) (mode (A.YM a) (α + k - 3) x) +
        (k : ℂ) • mode (A.YM W.conformalVector) (-k - 1) (mode (A.YM a) (α + k - 2) x) -
        negOnePow (-k) • (mode (A.YM a) (α - 3) (mode (A.YM W.conformalVector) 0 x)
          + ((k : ℂ) * h) • mode (A.YM a) (α - 4) x) := by
  rw [module_iterate0 A W.conformalVector a x (-k) (α + k - 3)]
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · rw [Finset.sum_pair (by norm_num)]
    have hω1 : mode (A.YM W.conformalVector) 1 x = h • x := hL
    rw [cbz_zero, cbz_one', show negOnePow 0 = 1 by simp [negOnePow],
      negOnePow_one', hω1, map_smul,
      show -k + (α + k - 3) - 0 = α - 3 by ring, show -k + (α + k - 3) - 1 = α - 4 by ring,
      show -k - 0 = -k by ring, show α + k - 3 + 0 = α + k - 3 by ring,
      show α + k - 3 + 1 = α + k - 2 by ring]
    push_cast
    module
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hne
    apply hi
    by_cases hneg : i < 0
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · rw [Omega_mode_vanish hx ha (show α ≤ α + k - 3 + i by omega), map_zero, zero_sub,
        Omega_mode_vanish hx W.conformal_mem (show (2 : ℤ) ≤ i by omega), map_zero,
        smul_zero, neg_zero, smul_zero]

end General

section EPart3
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h a4 : ℂ}
  (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x)
  (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x)
  (hE0 : mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0)
  (hE1 : mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0)
  (hE2 : mode (A.YM (EP m hm)) ((m : ℤ) - 3) x = 0)

include hE2 in
theorem E3_Lx :
    mode (A.YM (EP m hm)) ((m : ℤ) - 3) (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (((m : ℤ) - 3 : ℤ) : ℂ) • mode (A.YM (EP m hm)) ((m : ℤ) - 4) x := by
  rw [mode_translation, hE2, map_zero, zero_add, show (m : ℤ) - 3 - 1 = (m : ℤ) - 4 by ring]

include hxΩ hxL h4 hE0 hE1 hE2 in
/-- The `E`-virtual eigenvalue at degree three. -/
theorem oH4_v3 :
    ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2)) •
        mode (A.YM (HP m hm 2)) 3 (mode (A.YM (EP m hm)) ((m : ℤ) - 4) x) =
      ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) * a4 + 6 * (((m : ℂ) - 3) ^ 2 - 4 * m * h)) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 4) x := by
  have hLx := E3_Lx m hm A hE2
  have e3 : mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 3 (EP m hm))) ((m : ℤ) - 4) x = 0 := by
    rw [H4_3_E]; simp
  have e2 : (3 : ℂ) • mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 2 (EP m hm))) ((m : ℤ) - 3) x =
      (-(((m : ℤ) - 3 : ℤ) : ℂ)) • mode (A.YM (EP m hm)) ((m : ℤ) - 4) x := by
    have h2 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 3) x) (H4_2_E m hm)
    simp only [map_smul, mode_smul, LinearMap.smul_apply] at h2
    rw [T_mode, show (m : ℤ) - 3 - 1 = (m : ℤ) - 4 by ring] at h2
    exact h2
  have e1 : (2 * (2 * (m : ℂ)) - 1) •
      mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 1 (EP m hm))) ((m : ℤ) - 2) x =
      (2 * (2 * (m : ℂ)) * ((m : ℂ) - 3 + h) - ((m : ℂ) - 2) * ((m : ℂ) - 3)) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 4) x := by
    have h1 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 2) x) (H4_1_E m hm)
    simp only [map_smul, map_sub, mode_smul, mode_sub, LinearMap.smul_apply,
      LinearMap.sub_apply] at h1
    have hω := omega_neg_mode3 A hxΩ hxL (EP_mem_grading m hm) 1 le_rfl
    rw [show ((m : ℕ) : ℤ) + 1 - 3 = (m : ℤ) - 2 by ring, show ((m : ℕ) : ℤ) + 1 - 2 = (m : ℤ) - 1 by ring,
      hE1, hE0, map_zero, map_zero, smul_zero, zero_add, zero_sub, hLx,
      negOnePow_neg_one', show ((m : ℕ) : ℤ) - 4 = (m : ℤ) - 4 by rfl] at hω
    rw [hω, T_mode, T_mode, show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring,
      show (m : ℤ) - 3 - 1 = (m : ℤ) - 4 by ring] at h1
    rw [h1]
    push_cast
    module
  have e0 : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) •
      mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 0 (EP m hm))) ((m : ℤ) - 1) x =
      ((4 * (2 * (m : ℂ)) ^ 2 - 6 * (2 * (m : ℂ))) * (-((m : ℂ) - 3 + 2 * h)) +
        4 * (2 * (m : ℂ)) * (((m : ℂ) - 3) * ((m : ℂ) - 2 + h)) -
        2 * (((m : ℂ) - 1) * ((m : ℂ) - 2) * ((m : ℂ) - 3))) •
        mode (A.YM (EP m hm)) ((m : ℤ) - 4) x := by
    have h0 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 1) x) (H4_0_E m hm)
    simp only [map_smul, map_sub, map_add, mode_smul, mode_sub, mode_add, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply] at h0
    have hω2 := omega_neg_mode3 A hxΩ hxL (EP_mem_grading m hm) 2 (by norm_num)
    rw [show ((m : ℕ) : ℤ) + 2 - 3 = (m : ℤ) - 1 by ring, show ((m : ℕ) : ℤ) + 2 - 2 = (m : ℤ) by ring,
      hE0, Omega_mode_vanish hxΩ (EP_mem_grading m hm) (le_refl (m : ℤ)), map_zero, map_zero,
      smul_zero, zero_add, zero_sub, hLx, negOnePow_neg_two',
      show ((m : ℕ) : ℤ) - 4 = (m : ℤ) - 4 by rfl] at hω2
    have hω1 := omega_neg_mode3 A hxΩ hxL (LE_mem_grading_gen m hm) 1 le_rfl
    rw [show (m : ℤ) + 1 + 1 - 3 = (m : ℤ) - 1 by ring, show (m : ℤ) + 1 + 1 - 2 = (m : ℤ) by ring,
      show (m : ℤ) + 1 - 3 = (m : ℤ) - 2 by ring, show (m : ℤ) + 1 - 4 = (m : ℤ) - 3 by ring,
      T_mode, T_mode, T_mode, T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring,
      show (m : ℤ) - 1 = (m : ℤ) - 1 by rfl, hE1, hE0, smul_zero, smul_zero, map_zero, map_zero,
      smul_zero, zero_add, zero_sub, show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring, hLx,
      show (m : ℤ) - 3 - 1 = (m : ℤ) - 4 by ring, negOnePow_neg_one'] at hω1
    rw [hω2, hω1, T_mode, T_mode, T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring,
      show (m : ℤ) - 2 - 1 = (m : ℤ) - 3 by ring, show (m : ℤ) - 3 - 1 = (m : ℤ) - 4 by ring] at h0
    rw [h0]
    push_cast
    module
  have hc := zero_mode_comm A 3 (HP m hm 2) (EP m hm) ((m : ℤ) - 4) x
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, h4, map_smul] at hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl] at hc
  rw [show (3 : ℤ) + ((m : ℤ) - 4) - 0 = (m : ℤ) - 1 by ring,
    show (3 : ℤ) + ((m : ℤ) - 4) - 1 = (m : ℤ) - 2 by ring,
    show (3 : ℤ) + ((m : ℤ) - 4) - 2 = (m : ℤ) - 3 by ring,
    show (3 : ℤ) + ((m : ℤ) - 4) - 3 = (m : ℤ) - 4 by ring, e3] at hc
  rw [hc]
  linear_combination (norm := module) e0 +
    (3 * (2 * (m : ℂ) - 2)) • e1 + ((2 * (2 * (m : ℂ)) - 1) * (2 * (m : ℂ) - 2)) • e2

end EPart3

end VOA.Classification.COne.PlusRat4
