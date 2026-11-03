import VOA.Classification.COne.PlusRat4Frame
import VOA.Classification.COne.PlusRat4Transfer3

/-! # Gap two at `h = 1/4` (degenerate Kac determinant)

At `h = 1/4` (`c = 1`) the level-two Virasoro vectors `L(-1)²x`, `L(-2)x` become proportional in
the Fock model; the degree-two space of the model is spanned by `Q₁ = L(-2)e` and
`Q₂ = H⁴₍₁₎e`, and the extra lowering functional `H⁴₍₄₎` separates it.

x-side formulas (`p₂ = c₂ L(-1)x`, `p₃ = c₃ L(-1)x`):
* `H⁴₍₄₎Q₁ = (7c₂ + 5/3) L(-1)x`, `H⁴₍₄₎Q₂ = (7c₂ + 9c₃ - 2/15) L(-1)x`,
  `H⁴₍₄₎R = (8a₄ + 12c₂) L(-1)x`, `H⁴₍₄₎E₍ₘ₋₃₎x = 0`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-! ## §1  Certificates -/

theorem cert44_4 : normR (polyActW H4R (-4 - 1) H4R) = normR (combR [(10 / 3, 1, 1)]) := by
  decide +kernel

theorem certE4 : normR (polyActWC H4R (-4 - 1) P0) = [] := by decide +kernel

section Certs
variable (m : ℕ) (hm : 1 ≤ m)

theorem H44_4_eq : (V2mPlus m hm).smul (HP m hm 2) 4 (HP m hm 2) = combV m hm [(10 / 3, 1, 1)] :=
  smul_HP_eq m hm 2 2 (by norm_num) (by norm_num) 4 _ (by decide) cert44_4

/-- `H⁴₍₄₎E = 0`. -/
theorem H4_4_E : (V2mPlus m hm).smul (HP m hm 2) 4 (EP m hm) = 0 := by
  rw [EP_eq_y0, PreVertexAlgebra.smul_smul_right]
  have h := eq_of_hasC m hm (hasC_H4 m hm 4 (hasC_y0 m hm)) (hasC_zero m hm) (by
    rw [certE4]; rfl)
  rw [h, smul_zero]

theorem H4_4_omega (hm2 : 2 ≤ m) : (V2mPlus m hm).smul (HP m hm 2) 4 (HP m hm 1) = 0 := by
  have hg : (V2mPlus m hm).smul (HP m hm 2) 4 (HP m hm 1) ∈ (V2mPlus m hm).grading 1 := by
    have := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading
      (HP_mem_grading m hm 2 (by norm_num) (by norm_num)) (V2mPlus m hm).conformal_mem 4
    simpa using this
  rw [grading_one_eq_bot m hm hm2, Submodule.mem_bot] at hg
  exact hg

end Certs

/-! ## §2  `H⁴₍₄₎` on degree-two vectors -/

section H44
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h a4 c2 c3 : ℂ}
  (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x)
  (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x)
  (hp2 : mode (A.YM (HP m hm 2)) 2 x = c2 • mode (A.YM (HP m hm 1)) 0 x)
  (hp3 : mode (A.YM (HP m hm 3)) 4 x = c3 • mode (A.YM (HP m hm 1)) 0 x)

include hxΩ in
theorem H44_comm (b : VP m hm) (n : ℤ) :
    mode (A.YM (HP m hm 2)) 4 (mode (A.YM b) n x) =
      ∑ j ∈ Finset.range 5, ((Nat.choose 4 j : ℕ) : ℂ) •
        mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) j b)) ((4 : ℤ) + n - j) x := by
  have h := zero_mode_comm A 4 (HP m hm 2) b n x
  rw [show ((4 : ℕ) : ℤ) = 4 by rfl, Omega_mode_vanish hxΩ
    (HP_mem_grading m hm 2 (by norm_num) (by norm_num)) (show (((2 * 2 : ℕ) : ℤ)) ≤ 4 by norm_num),
    map_zero, zero_add] at h
  exact h

include hxΩ hp2 in
/-- `H⁴₍₄₎Q₁ = (7c₂ + 5/3) L(-1)x`. -/
theorem H44_Q1 (hm2 : 2 ≤ m) :
    mode (A.YM (HP m hm 2)) 4 (mode (A.YM (HP m hm 1)) (-1) x) =
      (7 * c2 + 5 / 3) • mode (A.YM (HP m hm 1)) 0 x := by
  rw [H44_comm m hm A hxΩ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4w_eq m hm 0 (by norm_num), H4w_eq m hm 1 (by norm_num), H4w_eq m hm 2 (by norm_num),
    H4w_eq m hm 3 (by norm_num), show ((4 : ℕ) : ℤ) = 4 from rfl, H4_4_omega m hm hm2]
  simp only [mode_combV, T4w, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC,
    map_zero, mode_zero, LinearMap.zero_apply, smul_zero, add_zero]
  have e1 : mode (A.YM (HP m hm 2)) (4 + -1 - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) x =
      c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have e2 : mode (A.YM (HP m hm 2)) (4 + -1 - ((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) x =
      c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have f0 : mode (A.YM (HP m hm 1)) (4 + -1 - ((0 : ℕ) : ℤ) - ((3 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  have f1 : mode (A.YM (HP m hm 1)) (4 + -1 - ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  have f2 : mode (A.YM (HP m hm 1)) (4 + -1 - ((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  have f3 : mode (A.YM (HP m hm 1)) (4 + -1 - ((3 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  rw [e1, e2, f0, f1, f2, f3]
  simp only [Nat.choose, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  push_cast
  module

include hxΩ hp2 hp3 in
/-- `H⁴₍₄₎Q₂ = (7c₂ + 9c₃ - 2/15) L(-1)x`. -/
theorem H44_Q2 :
    mode (A.YM (HP m hm 2)) 4 (mode (A.YM (HP m hm 2)) 1 x) =
      (7 * c2 + 9 * c3 - 2 / 15) • mode (A.YM (HP m hm 1)) 0 x := by
  rw [H44_comm m hm A hxΩ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H44_eq m hm 0 (by norm_num), H44_eq m hm 1 (by norm_num), H44_eq m hm 2 (by norm_num),
    H44_eq m hm 3 (by norm_num), show ((4 : ℕ) : ℤ) = 4 from rfl, H44_4_eq m hm]
  simp only [mode_combV, T44, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
  have e1 : mode (A.YM (HP m hm 2)) (4 + 1 - ((0 : ℕ) : ℤ) - ((3 : ℕ) : ℤ)) x =
      c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have e2 : mode (A.YM (HP m hm 2)) (4 + 1 - ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) x =
      c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have e3 : mode (A.YM (HP m hm 2)) (4 + 1 - ((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) x =
      c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have e4 : mode (A.YM (HP m hm 2)) (4 + 1 - ((3 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) x =
      c2 • mode (A.YM (HP m hm 1)) 0 x := hp2
  have g1 : mode (A.YM (HP m hm 3)) (4 + 1 - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) x =
      c3 • mode (A.YM (HP m hm 1)) 0 x := hp3
  have g2 : mode (A.YM (HP m hm 3)) (4 + 1 - ((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) x =
      c3 • mode (A.YM (HP m hm 1)) 0 x := hp3
  have f0 : mode (A.YM (HP m hm 1)) (4 + 1 - ((0 : ℕ) : ℤ) - ((5 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  have f1 : mode (A.YM (HP m hm 1)) (4 + 1 - ((1 : ℕ) : ℤ) - ((4 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  have f2 : mode (A.YM (HP m hm 1)) (4 + 1 - ((2 : ℕ) : ℤ) - ((3 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  have f3 : mode (A.YM (HP m hm 1)) (4 + 1 - ((3 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  have f4 : mode (A.YM (HP m hm 1)) (4 + 1 - 4 - ((1 : ℕ) : ℤ)) x =
      mode (A.YM (HP m hm 1)) 0 x := rfl
  rw [e1, e2, e3, e4, g1, g2, f0, f1, f2, f3, f4]
  simp only [Nat.choose, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  push_cast
  module

include hxΩ h4 hp2 in
/-- `H⁴₍₄₎R = (8a₄ + 12c₂) L(-1)x`. -/
theorem H44_R :
    mode (A.YM (HP m hm 2)) 4 (mode (A.YM (HP m hm 1)) 0 (mode (A.YM (HP m hm 1)) 0 x)) =
      (8 * a4 + 12 * c2) • mode (A.YM (HP m hm 1)) 0 x := by
  rw [HP_one] at hp2 ⊢
  have e0 : mode (A.YM (HP m hm 2)) 4 x = 0 := Omega_mode_vanish hxΩ
    (HP_mem_grading m hm 2 (by norm_num) (by norm_num)) (show (((2 * 2 : ℕ) : ℤ)) ≤ 4 by norm_num)
  have e1 : mode (A.YM (HP m hm 2)) 4 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (4 * a4) • x := by
    rw [mode_translation A (HP m hm 2) 4 x, e0, map_zero, zero_add,
      show (4 : ℤ) - 1 = 3 by norm_num, h4, smul_smul]
    push_cast; ring_nf
  have e2 : mode (A.YM (HP m hm 2)) 3 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      (a4 + 3 * c2) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x := by
    rw [mode_translation A (HP m hm 2) 3 x, h4, show (3 : ℤ) - 1 = 2 by norm_num, hp2, map_smul,
      smul_smul, ← add_smul]
    push_cast; ring_nf
  rw [mode_translation A (HP m hm 2) 4 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x), e1,
    map_smul, show (4 : ℤ) - 1 = 3 by norm_num, e2, smul_smul]
  push_cast
  module

end H44

/-! ## §3  `H⁴₍₄₎` on the `E`-vector, degree-one constants -/

section EV
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h : ℂ}
  (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x)
  (hE0 : mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0)
  (hE1 : mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0)

include hE0 hE1 in
theorem E1_Lx : mode (A.YM (EP m hm)) ((m : ℤ) - 1) (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) = 0 := by
  rw [mode_translation, hE0, map_zero, zero_add, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring, hE1,
    smul_zero]

include hm2 hxΩ hxL hE0 hE1 in
/-- `H⁴₍₄₎E₍ₘ₋₃₎x = 0`. -/
theorem H44_v : mode (A.YM (HP m hm 2)) 4 (mode (A.YM (EP m hm)) ((m : ℤ) - 3) x) = 0 := by
  have hK1 : (2 * (2 * (m : ℂ)) - 1) ≠ 0 := by
    have : (2 * (2 * (m : ℤ)) - 1) ≠ 0 := by omega
    exact_mod_cast this
  have hK2 : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) ≠ 0 := by
    have : (2 * (2 * (m : ℤ)) ^ 2 - 5 * (2 * (m : ℤ)) + 2) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hEL := E1_Lx m hm A hE0 hE1
  -- `j = 2`
  have e2 : mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 2 (EP m hm))) ((m : ℤ) - 1) x = 0 := by
    have h2 := congrArg (fun y => mode (A.YM y) ((m : ℤ) - 1) x) (H4_2_E m hm)
    simp only [map_smul, mode_smul, LinearMap.smul_apply] at h2
    rw [T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring, hE1, smul_zero] at h2
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  -- `j = 1`
  have e1 : mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 1 (EP m hm))) (m : ℤ) x = 0 := by
    have h1 := congrArg (fun y => mode (A.YM y) (m : ℤ) x) (H4_1_E m hm)
    simp only [map_smul, map_sub, mode_smul, mode_sub, LinearMap.smul_apply,
      LinearMap.sub_apply] at h1
    have hω := omega_neg_mode A hxΩ hxL (EP_mem_grading m hm) 1 le_rfl
    rw [show ((m : ℕ) : ℤ) + 1 - 1 = (m : ℤ) by ring, hEL,
      show ((m : ℕ) : ℤ) - 2 = (m : ℤ) - 2 by rfl, hE1, smul_zero, add_zero, smul_zero] at hω
    rw [hω, T_mode, T_mode, show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring, hE1] at h1
    simp only [smul_zero, sub_zero] at h1
    exact (smul_eq_zero.mp h1).resolve_left hK1
  -- `j = 0`
  have e0 : mode (A.YM ((V2mPlus m hm).smul (HP m hm 2) 0 (EP m hm))) ((m : ℤ) + 1) x = 0 := by
    have h0 := congrArg (fun y => mode (A.YM y) ((m : ℤ) + 1) x) (H4_0_E m hm)
    simp only [map_smul, map_sub, map_add, mode_smul, mode_sub, mode_add, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply] at h0
    have hω2 := omega_neg_mode A hxΩ hxL (EP_mem_grading m hm) 2 (by norm_num)
    rw [show ((m : ℕ) : ℤ) + 2 - 1 = (m : ℤ) + 1 by ring, hEL,
      show ((m : ℕ) : ℤ) - 2 = (m : ℤ) - 2 by rfl, hE1, smul_zero, add_zero, smul_zero] at hω2
    have hω1 := omega_neg_mode A hxΩ hxL (LE_mem_grading_gen m hm) 1 le_rfl
    rw [show (m : ℤ) + 1 + 1 - 1 = (m : ℤ) + 1 by ring, show (m : ℤ) + 1 - 1 = (m : ℤ) by ring,
      show (m : ℤ) + 1 - 2 = (m : ℤ) - 1 by ring, T_mode, T_mode,
      show (m : ℤ) - 1 = (m : ℤ) - 1 by rfl, hEL,
      show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring, hE1] at hω1
    simp only [smul_zero, add_zero] at hω1
    rw [hω2, hω1, T_mode, T_mode, T_mode, show (m : ℤ) + 1 - 1 = (m : ℤ) by ring,
      show (m : ℤ) - 1 - 1 = (m : ℤ) - 2 by ring, hE1] at h0
    simp only [smul_zero, sub_zero, add_zero] at h0
    exact (smul_eq_zero.mp h0).resolve_left hK2
  rw [H44_comm m hm A hxΩ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  rw [show (4 : ℤ) + ((m : ℤ) - 3) - 0 = (m : ℤ) + 1 by ring,
    show (4 : ℤ) + ((m : ℤ) - 3) - 1 = (m : ℤ) by ring,
    show (4 : ℤ) + ((m : ℤ) - 3) - 2 = (m : ℤ) - 1 by ring, e0, e1, e2, H4_3_E, H4_4_E]
  simp

end EV

section Consts
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {N : Type} [AddCommGroup N] [Module ℂ N]
  (B : WeakModule (V2mPlus m hm) N) {y : N} {h : ℂ}

/-- On a top vector with `o(H⁴) = o(H⁶) = 0` and the degree-one line:
`H⁴₍₂₎y = L(-1)y/3`, `H⁶₍₄₎y = L(-1)y/5`. -/
theorem charged_consts (hyΩ : y ∈ Omega B) (hyL : L0 B y = h • y) (hh : h ≠ 0) (hy0 : y ≠ 0)
    (hD : Deg1Line B y) (h4 : mode (B.YM (HP m hm 2)) 3 y = (0 : ℂ) • y)
    (h6 : mode (B.YM (HP m hm 3)) 5 y = (0 : ℂ) • y) :
    mode (B.YM (HP m hm 2)) 2 y = (1 / 3 : ℂ) • mode (B.YM (HP m hm 1)) 0 y ∧
      mode (B.YM (HP m hm 3)) 4 y = (1 / 5 : ℂ) • mode (B.YM (HP m hm 1)) 0 y := by
  have hg2 := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  have h2h : (2 : ℂ) * h ≠ 0 := mul_ne_zero two_ne_zero hh
  constructor
  · obtain ⟨κ, hκ⟩ := hD _ _ hg2
    rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hκ
    have hβ := L1G_p2 m hm B hyΩ hyL h4
    rw [hκ, map_smul, L1_L B hyΩ hyL, smul_smul] at hβ
    have h1 : (κ * (2 * h) - (4 * 0 + 2 * h / 3)) • y = 0 := by rw [sub_smul, hβ, sub_self]
    have h2 := (smul_eq_zero.mp h1).resolve_right hy0
    have hk : κ = 1 / 3 := by
      have h3 : (κ - 1 / 3) * (2 * h) = 0 := by linear_combination h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right h2h)
    rw [hκ, hk]; rfl
  · obtain ⟨κ, hκ⟩ := hD _ _ hg3
    rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hκ
    have hβ := L1G_p3 m hm B hyΩ hyL h4 h6
    rw [hκ, map_smul, L1_L B hyΩ hyL, smul_smul] at hβ
    have h1 : (κ * (2 * h) - (6 * 0 + 6 * 0 + 2 * h / 5)) • y = 0 := by rw [sub_smul, hβ, sub_self]
    have h2 := (smul_eq_zero.mp h1).resolve_right hy0
    have hk : κ = 1 / 5 := by
      have h3 : (κ - 1 / 5) * (2 * h) = 0 := by linear_combination h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right h2h)
    rw [hκ, hk]; rfl

include hm2 in
/-- With `c₂ = 1/3`, `c₃ = 1/5`: `L(-2)y` and `H⁴₍₁₎y` are linearly independent
(`L(1)` and `H⁴₍₄₎`: determinant `3·4 - 2·4 = 4`). -/
theorem Q12_indep (hyΩ : y ∈ Omega B) (hLy0 : mode (B.YM (V2mPlus m hm).conformalVector) 0 y ≠ 0)
    (hp2 : mode (B.YM (HP m hm 2)) 2 y = (1 / 3 : ℂ) • mode (B.YM (HP m hm 1)) 0 y)
    (hp3 : mode (B.YM (HP m hm 3)) 4 y = (1 / 5 : ℂ) • mode (B.YM (HP m hm 1)) 0 y)
    (s t : ℂ) (hst : s • mode (B.YM (V2mPlus m hm).conformalVector) (-1) y +
      t • mode (B.YM (HP m hm 2)) 1 y = 0) : s = 0 ∧ t = 0 := by
  have e1 := congrArg (fun v => mode (B.YM (V2mPlus m hm).conformalVector) 2 v) hst
  have e2 := congrArg (fun v => mode (B.YM (HP m hm 2)) 4 v) hst
  simp only at e1 e2
  have q1 := L1_Q1 m hm B hyΩ hm2
  have q2 := L1_Q2 m hm B hyΩ hp2
  have r1 := H44_Q1 m hm B hyΩ hp2 hm2
  have r2 := H44_Q2 m hm B hyΩ hp2 hp3
  rw [HP_one] at q1 q2 r1 r2
  rw [map_add, map_smul, map_smul, q1, q2, map_zero, smul_smul, smul_smul, ← add_smul] at e1
  rw [map_add, map_smul, map_smul, r1, r2, map_zero, smul_smul, smul_smul, ← add_smul] at e2
  have f1 := (smul_eq_zero.mp e1).resolve_right hLy0
  have f2 := (smul_eq_zero.mp e2).resolve_right hLy0
  constructor
  · linear_combination f1 - (1 / 2 : ℂ) * f2
  · linear_combination (-1 : ℂ) * f1 + (3 / 4 : ℂ) * f2

end Consts

/-! ## §4  The model, the degree-two span, the splitting -/

section QFrame
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

include hm2 in
/-- In the charged model (`s ≤ m - 3`) every vector of weight `h + 2` is `b L(-2)e + c H⁴₍₁₎e`. -/
theorem lat_Q12 (r : Fin (m - 1)) (hs : r.val + 4 ≤ m) {v : LatModuleGen (latP m)}
    (hv : v ∈ (Ns m hm r).weight (hC m r + 2)) :
    ∃ b c : ℂ, v = b • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) (-1) (latVacuumGen (latP m)) +
      c • mode ((Ns m hm r).YM (HP m hm 2)) 1 (latVacuumGen (latP m)) := by
  have hs3 : r.val + 3 ≤ m := by omega
  have heTD := lat_topData m hm hm2 r hs3
  have he0 := latVacuumGen_ne_zero' m hm
  have hh := hC_ne_zero m hm2 r
  have hzero : ∀ t : ℕ, t = 2 ∨ t = 3 → mode ((Ns m hm r).YM (HP m hm t)) ((2 * t : ℕ) - 1 : ℤ)
      (latVacuumGen (latP m)) = (0 : ℂ) • latVacuumGen (latP m) := by
    intro t ht
    have h1 := heTD.zero (HP_mem_grading m hm t (by omega) (by omega))
    rw [chiT_HP_zero m hm hm2 r t ht] at h1
    exact h1
  have h4 := hzero 2 (Or.inl rfl)
  have h6 := hzero 3 (Or.inr rfl)
  rw [show ((2 * 2 : ℕ) : ℤ) - 1 = 3 by norm_num] at h4
  rw [show ((2 * 3 : ℕ) : ℤ) - 1 = 5 by norm_num] at h6
  obtain ⟨hp2, hp3⟩ := charged_consts m hm (Ns m hm r).toWeakModule heTD.omega heTD.L0 hh he0
    heTD.line h4 h6
  have hw : ∀ {j : ℤ} {c : VP m hm}, c ∈ (V2mPlus m hm).grading j →
      mode ((Ns m hm r).YM c) (j - 3) (latVacuumGen (latP m)) ∈ (Ns m hm r).weight (hC m r + 2) := by
    intro j c hc
    have h := mode_mem_weight (Ns m hm r) hc (es_weight m hm r) (j - 3)
    have hc' : hC m r + (j : ℂ) - ((j - 3 : ℤ) : ℂ) - 1 = hC m r + 2 := by push_cast; ring
    rwa [hc'] at h
  have hQ1 := hw (V2mPlus m hm).conformal_mem
  rw [show ((2 : ℤ) - 3) = -1 by norm_num] at hQ1
  have hQ2 := hw (HP_mem_grading m hm 2 (by norm_num) (by norm_num))
  rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num] at hQ2
  exact exists_comb_of_span_pair (lat_weight_two_mem_span m hm r hs hv)
    (lat_weight_two_mem_span m hm r hs hQ1) (lat_weight_two_mem_span m hm r hs hQ2)
    (Q12_indep m hm hm2 (Ns m hm r).toWeakModule heTD.omega (heTD.Lm1_ne_zero hh he0) hp2 hp3)

variable {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M) {x : M} {h : ℂ}

include hm2 in
/-- The degree-two span lies in any subspace containing `R, Q₁, Q₂, E₍ₘ₋₃₎x`. -/
theorem degTwo_le_gen (hST : ScalarTop A x) (hD : Deg1Line A x) (L : Submodule ℂ M)
    (hR : mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) ∈ L)
    (hQ1 : mode (A.YM (V2mPlus m hm).conformalVector) (-1) x ∈ L)
    (hQ2 : mode (A.YM (HP m hm 2)) 1 x ∈ L)
    (hv : mode (A.YM (EP m hm)) ((m : ℤ) - 3) x ∈ L) : degSpan A x 2 ≤ L := by
  set G := Set.range (gP m hm)
  have hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ (V2mPlus m hm).grading j := by
    rintro g ⟨j, rfl⟩
    refine ⟨_, ?_, gP_mem_grading m hm j⟩
    fin_cases j <;> simp [wtP] <;> omega
  have hraise := raise2_mem hG (top_eq_span_iterProd m hm hm2) hST hD
  have hgen : raiseSpan2 A G x ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ (hy | ⟨j, g, ⟨i', rfl⟩, hgj, rfl⟩)
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hR
    have hwt := gP_mem_grading m hm i'
    by_cases hj : j = wtP m i'
    · subst hj
      fin_cases i'
      · change mode (A.YM (V2mPlus m hm).conformalVector) ((2 : ℤ) - 3) x ∈ L
        rw [show (2 : ℤ) - 3 = -1 by norm_num]; exact hQ1
      · change mode (A.YM (WP m hm)) ((4 : ℤ) - 3) x ∈ L
        rw [WP_eq_comb m hm]
        simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
        have e1 : mode (A.YM (HP m hm 2)) (4 - 3 - ((0 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 2)) 1 x :=
          rfl
        rw [e1]
        norm_num
        exact L.smul_mem _ hQ2
      · change mode (A.YM (EP m hm)) (((m : ℕ) : ℤ) - 3) x ∈ L
        exact hv
    · rw [eq_zero_of_mem_two_gradings hj hgj hwt, map_zero, mode_zero, LinearMap.zero_apply]
      exact L.zero_mem
  apply Submodule.span_le.mpr
  rintro _ ⟨β, a, ha, rfl⟩
  rw [show β - 1 - 2 = β - 3 by ring]
  exact hgen (hraise β a ha)

include hm2 in
/-- **Splitting from `span(L(-2)x, H⁴₍₁₎x)`** (`c₂ = 1/3`, `c₃ = 1/5`): `L(1)` and `H⁴₍₄₎`
separate this span from the kernel. -/
theorem split_of_Q12 (P : Submodule (modeAlg A) M) (hP : IsAtom P) (hQ : P ⋖ ⊤)
    (hb : FactorBottom A ⊥ P (h + 2)) (ht : FactorBottom A P ⊤ h)
    (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x) (hxP : x ∉ P) (hh : h ≠ 0)
    (hp2 : mode (A.YM (HP m hm 2)) 2 x = (1 / 3 : ℂ) • mode (A.YM (HP m hm 1)) 0 x)
    (hp3 : mode (A.YM (HP m hm 3)) 4 x = (1 / 5 : ℂ) • mode (A.YM (HP m hm 1)) 0 x)
    (hD : degSpan A x 2 ≤ Submodule.span ℂ {mode (A.YM (V2mPlus m hm).conformalVector) (-1) x,
      mode (A.YM (HP m hm 2)) 1 x}) : ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  have hxg : x ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  apply (exists_cyclic_lift_iff_complement A P hQ h ht).mp
  refine ⟨x, hxg, hxP, ?_⟩
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  have hyg : y ∈ (L0 A).maxGenEigenspace (h + ((2 : ℤ) : ℂ)) := by
    rw [show h + ((2 : ℤ) : ℂ) = h + 2 by push_cast; ring]; exact hy.2
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0' x,
    no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite m hm) A hxg 2 hyg]
  intro hyD
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hD (degreeSpan_le A hxL 2 hyD))
  have q1 := L1_Q1 m hm A hxΩ hm2
  have q2 := L1_Q2 m hm A hxΩ hp2
  have r1 := H44_Q1 m hm A hxΩ hp2 hm2
  have r2 := H44_Q2 m hm A hxΩ hp2 hp3
  rw [HP_one] at q1 q2 r1 r2
  have hL1 := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 2 hy.1
  have hL2 := PlusRat2Dual.mem_P_mode A P (HP m hm 2) 4 hy.1
  rw [← hab, map_add, map_smul, map_smul, q1, q2, smul_smul, smul_smul, ← add_smul] at hL1
  rw [← hab, map_add, map_smul, map_smul, r1, r2, smul_smul, smul_smul, ← add_smul] at hL2
  have hLx : mode (A.YM (V2mPlus m hm).conformalVector) 0 x ∉ P := by
    intro hLx
    apply hxP
    have h2 := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 2 hLx
    rw [L1_L A hxΩ hxL] at h2
    exact mem_of_smul_mem m hm A (mul_ne_zero two_ne_zero hh) h2
  have f1 : a * 3 + b * (5 * (1 / 3) + 1 / 3) = 0 := by
    by_contra hc; exact hLx (mem_of_smul_mem m hm A hc hL1)
  have f2 : a * (7 * (1 / 3) + 5 / 3) + b * (7 * (1 / 3) + 9 * (1 / 5) - 2 / 15) = 0 := by
    by_contra hc; exact hLx (mem_of_smul_mem m hm A hc hL2)
  have ha : a = 0 := by linear_combination f1 - (1 / 2 : ℂ) * f2
  have hb' : b = 0 := by linear_combination (-1 : ℂ) * f1 + (3 / 4 : ℂ) * f2
  subst ha hb'
  apply hy0'
  rw [← hab]; simp

end QFrame

/-! ## §5  The gap-two theorem at `h = 1/4` -/

section QMain
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

@[reducible] local instance zhuRingQ : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebraQ : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

set_option maxHeartbeats 1000000 in
include hm2 in
/-- **Gap two at `h = 1/4`.**  Quotient a charged row `c_s` with `s² = m` (`h = 1/4`),
`s ≤ m - 3`; kernel any row `i` of weight `9/4` all of whose weight-`9/4` companions kill `H⁴`
(e.g. the half rows at `m = 9`, the row `c_{3s}` in general). -/
theorem pairSplitting_quarter (r : Fin (m - 1)) (i : Label m) (hq : hC m r = 1 / 4)
    (hs : r.val + 4 ≤ m) (hm5 : 5 ≤ m)
    (hwi : weight m i = weight m (.inl r) + 2)
    (huq : ∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r)
    (hno1 : ∀ j : Label m, weight m j ≠ weight m (.inl r) + 1)
    (hkr : ∀ j : Label m, weight m j = weight m i →
      chiT m hm hm2 j (VOA.mk (V2mPlus m hm) (HP m hm 2)) = 0) :
    PairSplitting m hm i (.inl r) := by
  intro M _ _ A P hP hQ hb ht
  have hs3 : r.val + 3 ≤ m := by omega
  have hwiC : ((weight m i : ℚ) : ℂ) = hC m r + 2 := by
    simp only [hC]; rw [hwi]; push_cast; ring
  have huqC : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r → j = .inl r :=
    fun j h => huq j (Rat.cast_injective h)
  have hno1C : ∀ j : Label m, ((weight m j : ℚ) : ℂ) ≠ hC m r + 1 := by
    intro j h
    apply hno1 j
    apply Rat.cast_injective (α := ℂ)
    rw [h]; push_cast; rfl
  rw [hwiC] at hb
  change FactorBottom A P ⊤ (hC m r) at ht
  set h := hC m r with hhdef
  have hh : h ≠ 0 := hC_ne_zero m hm2 r
  have hlow := lowWeights m hm A hb ht
  obtain ⟨x, hxL, hxP, hx0, hxΩ⟩ := exists_top_lift m hm A hP hb ht
  -- the character of `x`
  set χ := chiT m hm hm2 (.inl r)
  have hχx := top_char_unique m hm hm2 A hxΩ hxL (.inl r) huqC
  have hzero : ∀ {k : ℤ} {a : VP m hm}, a ∈ (V2mPlus m hm).grading k →
      mode (A.YM a) (k - 1) x = χ (VOA.mk (V2mPlus m hm) a) • x := by
    intro k a ha
    have h1 := hχx (VOA.mk (V2mPlus m hm) a)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h1
    exact h1
  have hg2 := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  have h4 : mode (A.YM (HP m hm 2)) 3 x = (0 : ℂ) • x := by
    have h1 := hzero hg2
    rw [chiT_HP_zero m hm hm2 r 2 (Or.inl rfl)] at h1
    exact h1
  have h6 : mode (A.YM (HP m hm 3)) 5 x = (0 : ℂ) • x := by
    have h1 := hzero hg3
    rw [chiT_HP_zero m hm hm2 r 3 (Or.inr rfl)] at h1
    exact h1
  have hE0 : mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0 := by
    have h1 := hzero (EP_mem_grading m hm)
    have hv := (chiT_hasValues m hm hm2 (.inl r)).2.2
    change chiT m hm hm2 (.inl r) (VOA.mk (V2mPlus m hm) (EP m hm)) = _ at hv
    rw [hv] at h1
    simp [values] at h1
    simpa using h1
  -- degree one
  have hD1 : Deg1Line A x := by
    intro j c hc
    obtain ⟨κ, hκ⟩ := transfer_Omega_gen m hm hm2 r hs3 huqC A hxΩ hxL hlow hc
    refine ⟨κ, ?_⟩
    have hL : L0 A (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
        (h + 1) • (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) := by
      rw [map_sub, map_smul, L0_mode_eigen A hxL hc, L0_mode_eigen A hxL (V2mPlus m hm).conformal_mem]
      push_cast
      module
    have h0 := top_eval_zero_of_rows m hm hm2 A hκ (c := h + 1) hL 1
      (fun j hj => absurd hj (hno1C j))
    rw [topEvaluation_one] at h0
    exact sub_eq_zero.mp h0
  have hxTD : TopData A χ h x := ⟨hxΩ, hχx, hxL, hD1⟩
  have heTD := lat_topData m hm hm2 r hs3
  have he0 := latVacuumGen_ne_zero' m hm
  have hLx0 := hxTD.Lm1_ne_zero hh hx0
  obtain ⟨hp2, hp3⟩ := charged_consts m hm A hxΩ hxL hh hx0 hD1 h4 h6
  have hE1 : mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0 := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ (EP_mem_grading m hm)
    have hβ := L1G_v m hm A hxΩ hE0
    rw [hκ, map_smul, L1_L A hxΩ hxL, smul_smul] at hβ
    have hk : κ * (2 * h) = 0 := (smul_eq_zero.mp hβ).resolve_right hx0
    have hk' : κ = 0 := (mul_eq_zero.mp hk).resolve_right (mul_ne_zero two_ne_zero hh)
    rw [hκ, hk', zero_smul]
  -- the kernel rows kill `H⁴`
  have hker : ∀ w : M, w ∈ Omega A → L0 A w = (h + 2) • w → mode (A.YM (HP m hm 2)) 3 w = 0 := by
    intro w hw hwL
    have e2 := top_eval_zero_of_rows m hm hm2 A hw (c := h + 2) hwL
      (VOA.mk (V2mPlus m hm) (HP m hm 2)) (fun j hj => hkr j (by
        apply Rat.cast_injective (α := ℂ)
        rw [hj, hwiC]))
    rw [topEvaluation_mk, oLevW_homogeneous A 0 hg2] at e2
    exact e2
  -- weights of the degree-two vectors
  have hLR : L0 A (mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)) = (h + 2) •
      mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) := by
    rw [L0_mode_eigen A (L0_mode_eigen A hxL (V2mPlus m hm).conformal_mem 0)
      (V2mPlus m hm).conformal_mem 0]
    congr 1; push_cast; ring
  have hLQ1 : L0 A (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) =
      (h + 2) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x := by
    rw [L0_mode_eigen A hxL (V2mPlus m hm).conformal_mem]; congr 1
    all_goals (push_cast; ring)
  have hLQ2 : L0 A (mode (A.YM (HP m hm 2)) 1 x) = (h + 2) • mode (A.YM (HP m hm 2)) 1 x := by
    rw [L0_mode_eigen A hxL hg2]; congr 1
    all_goals (push_cast; ring)
  have hLv : L0 A (mode (A.YM (EP m hm)) ((m : ℤ) - 3) x) =
      (h + 2) • mode (A.YM (EP m hm)) ((m : ℤ) - 3) x := by
    rw [L0_mode_eigen A hxL (EP_mem_grading m hm)]; congr 1
    all_goals (push_cast; ring)
  -- the functionals `L(1)` and `H⁴₍₄₎`
  have q1 := L1_Q1 m hm A hxΩ hm2
  have q2 := L1_Q2 m hm A hxΩ hp2
  have r1 := H44_Q1 m hm A hxΩ hp2 hm2
  have r2 := H44_Q2 m hm A hxΩ hp2 hp3
  have rR := H44_R m hm A hxΩ h4 hp2
  have lR := L1_R A hxΩ hxL
  rw [HP_one] at q1 q2 r1 r2 rR
  have hmodel : ∀ {v : LatModuleGen (latP m)}, v ∈ (Ns m hm r).weight (h + 2) →
      ∃ b c : ℂ, v = b • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) (-1) (latVacuumGen (latP m)) +
        c • mode ((Ns m hm r).YM (HP m hm 2)) 1 (latVacuumGen (latP m)) :=
    fun hv => lat_Q12 m hm hm2 r hs hv
  have hwmodel : ∀ {j : ℤ} {c : VP m hm}, c ∈ (V2mPlus m hm).grading j →
      mode ((Ns m hm r).YM c) (j - 3) (latVacuumGen (latP m)) ∈ (Ns m hm r).weight (h + 2) := by
    intro j c hc
    have h' := mode_mem_weight (Ns m hm r) hc (es_weight m hm r) (j - 3)
    have hc' : h + (j : ℂ) - ((j - 3 : ℤ) : ℂ) - 1 = h + 2 := by push_cast; ring
    rwa [hc'] at h'
  -- `u = R - b Q₁ - c Q₂`
  obtain ⟨b, c, hbc⟩ : ∃ b c : ℂ, mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0
      (mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) 0 (latVacuumGen (latP m))) =
      b • mode ((Ns m hm r).YM (V2mPlus m hm).conformalVector) (-1) (latVacuumGen (latP m)) +
        c • mode ((Ns m hm r).YM (HP m hm 2)) 1 (latVacuumGen (latP m)) := by
    apply hmodel
    have h1 := mode_mem_weight (Ns m hm r) (V2mPlus m hm).conformal_mem (es_weight m hm r) 0
    have h2 := mode_mem_weight (Ns m hm r) (V2mPlus m hm).conformal_mem h1 0
    have hc' : h + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = h + 2 := by
      push_cast; ring
    rwa [hc'] at h2
  have hcu : TopData.wv3 (Ns m hm r).toWeakModule (latVacuumGen (latP m)) 0 2 (HP m hm 2)
      ((2 * 2 : ℕ) : ℤ) (-1) b c = 0 := by
    simp only [TopData.wv3, TopData.wv, map_zero, mode_zero, LinearMap.zero_apply, zero_smul,
      sub_zero]
    rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num, hbc]
    module
  have hu0 := transfer3 A (Ns m hm r).toWeakModule χ hxTD heTD hx0 he0 hh hlow
    ((V2mPlus m hm).grading 2).zero_mem hg2 hcu
  have hu : mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) -
      b • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x - c • mode (A.YM (HP m hm 2)) 1 x ∈
      Omega A := by
    convert hu0 using 1
    simp only [TopData.wv3, TopData.wv, map_zero, mode_zero, LinearMap.zero_apply, zero_smul,
      sub_zero]
    rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num]
    module
  have g1 := Omega_mode_vanish hu (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
  have g2 := Omega_mode_vanish hu hg2 (show (((2 * 2 : ℕ) : ℤ)) ≤ 4 by norm_num)
  rw [map_sub, map_sub, map_smul, map_smul, lR, q1, q2] at g1
  rw [map_sub, map_sub, map_smul, map_smul, rR, r1, r2] at g2
  have f1 : (4 * h + 2) - b * 3 - c * (5 * (1 / 3) + 1 / 3) = 0 := by
    have : ((4 * h + 2) - b * 3 - c * (5 * (1 / 3) + 1 / 3)) •
        mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g1
    exact (smul_eq_zero.mp this).resolve_right hLx0
  have f2 : (8 * 0 + 12 * (1 / 3)) - b * (7 * (1 / 3) + 5 / 3) -
      c * (7 * (1 / 3) + 9 * (1 / 5) - 2 / 15) = 0 := by
    have : ((8 * 0 + 12 * (1 / 3)) - b * (7 * (1 / 3) + 5 / 3) -
        c * (7 * (1 / 3) + 9 * (1 / 5) - 2 / 15)) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g2
    exact (smul_eq_zero.mp this).resolve_right hLx0
  rw [hq] at f1
  have hb1 : b = 1 := by linear_combination (-1 : ℂ) * f1 + (1 / 2 : ℂ) * f2
  have hc0 : c = 0 := by linear_combination f1 - (3 / 4 : ℂ) * f2
  subst hb1 hc0
  -- `o(H⁴)u = 2(R - Q₁)`, hence `R = Q₁`
  have hRQ : mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
      mode (A.YM (V2mPlus m hm).conformalVector) (-1) x := by
    have huL : L0 A (mode (A.YM (V2mPlus m hm).conformalVector) 0
        (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) -
        (1 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x -
        (0 : ℂ) • mode (A.YM (HP m hm 2)) 1 x) = (h + 2) • (mode (A.YM (V2mPlus m hm).conformalVector) 0
        (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) -
        (1 : ℂ) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x -
        (0 : ℂ) • mode (A.YM (HP m hm 2)) 1 x) := by
      rw [map_sub, map_sub, map_smul, map_smul, hLR, hLQ1, hLQ2]
      module
    have o := hker _ hu huL
    have eR := oH4_R m hm A h4 hp2
    have eQ1 := oH4_Q1 m hm A h4
    have eQ2 := oH4_Q2 m hm A h4
    rw [HP_one] at eR eQ1
    rw [map_sub, map_sub, map_smul, map_smul, eR, eQ1, eQ2] at o
    have h2 : (2 : ℂ) • (mode (A.YM (V2mPlus m hm).conformalVector) 0
        (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) -
        mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) = 0 := by
      linear_combination (norm := module) o
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left two_ne_zero)
  -- the `E`-part
  obtain ⟨bE, cE, hbcE⟩ := hmodel (hwmodel (EP_mem_grading m hm))
  have hcE : TopData.wv3 (Ns m hm r).toWeakModule (latVacuumGen (latP m)) (EP m hm) (m : ℤ)
      (HP m hm 2) ((2 * 2 : ℕ) : ℤ) 0 bE cE = 0 := by
    simp only [TopData.wv3, TopData.wv, zero_smul, sub_zero]
    rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num, hbcE]
    module
  have hvE0 := transfer3 A (Ns m hm r).toWeakModule χ hxTD heTD hx0 he0 hh hlow
    (EP_mem_grading m hm) hg2 hcE
  have hvE : mode (A.YM (EP m hm)) ((m : ℤ) - 3) x -
      bE • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x - cE • mode (A.YM (HP m hm 2)) 1 x ∈
      Omega A := by
    convert hvE0 using 1
    simp only [TopData.wv3, TopData.wv, zero_smul, sub_zero]
    rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num]
  have g5 := Omega_mode_vanish hvE (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
  have g6 := Omega_mode_vanish hvE hg2 (show (((2 * 2 : ℕ) : ℤ)) ≤ 4 by norm_num)
  rw [map_sub, map_sub, map_smul, map_smul, L1_v m hm A hxΩ hE1, q1, q2] at g5
  rw [map_sub, map_sub, map_smul, map_smul, H44_v m hm hm2 A hxΩ hxL hE0 hE1, r1, r2] at g6
  have f5 : bE * 3 + cE * (5 * (1 / 3) + 1 / 3) = 0 := by
    have : (bE * 3 + cE * (5 * (1 / 3) + 1 / 3)) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) -g5
    exact (smul_eq_zero.mp this).resolve_right hLx0
  have f6 : bE * (7 * (1 / 3) + 5 / 3) + cE * (7 * (1 / 3) + 9 * (1 / 5) - 2 / 15) = 0 := by
    have : (bE * (7 * (1 / 3) + 5 / 3) + cE * (7 * (1 / 3) + 9 * (1 / 5) - 2 / 15)) •
        mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) -g6
    exact (smul_eq_zero.mp this).resolve_right hLx0
  have hbE0 : bE = 0 := by linear_combination f5 - (1 / 2 : ℂ) * f6
  have hcE0 : cE = 0 := by linear_combination (-1 : ℂ) * f5 + (3 / 4 : ℂ) * f6
  subst hbE0 hcE0
  simp only [zero_smul, sub_zero] at hvE
  have hv0 : mode (A.YM (EP m hm)) ((m : ℤ) - 3) x = 0 := by
    have o := hker _ hvE hLv
    have ev := oH4_v2 m hm A hxΩ hxL h4 hE0 hE1
    rw [o, smul_zero] at ev
    have hne : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) * 0 +
        4 * (((m : ℂ) - 2) ^ 2 - 4 * m * h) ≠ 0 := by
      rw [hq, mul_zero, zero_add]
      have : (((m : ℤ) - 2) ^ 2 - m) ≠ 0 := by nlinarith
      have h' : (((m : ℂ) - 2) ^ 2 - 4 * m * (1 / 4)) = ((((m : ℤ) - 2) ^ 2 - m : ℤ) : ℂ) := by
        push_cast; ring
      rw [h']
      exact mul_ne_zero (by norm_num) (by exact_mod_cast this)
    exact (smul_eq_zero.mp ev.symm).resolve_left hne
  -- conclusion
  have hST : ScalarTop A x := ⟨hxΩ, fun j c hc => ⟨_, hzero hc⟩⟩
  set L := Submodule.span ℂ {mode (A.YM (V2mPlus m hm).conformalVector) (-1) x,
    mode (A.YM (HP m hm 2)) 1 x}
  have hQ1L : mode (A.YM (V2mPlus m hm).conformalVector) (-1) x ∈ L :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hQ2L : mode (A.YM (HP m hm 2)) 1 x ∈ L := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  exact split_of_Q12 m hm hm2 A P hP hQ hb ht hxΩ hxL hxP hh hp2 hp3
    (degTwo_le_gen m hm hm2 A hST hD1 L (hRQ ▸ hQ1L) hQ1L hQ2L (by rw [hv0]; exact L.zero_mem))

end QMain

end VOA.Classification.COne.PlusRat4
