import VOA.Classification.COne.PlusRat4Model

/-! # The degree-two splitting frame for `V_{2m}⁺`

Setting: an extension `0 → P → M → Q → 0` with simple kernel `P` (bottom `h + 2`) and simple
quotient (bottom `h`), `x` a quotient-bottom lift, `x ∈ Ω`.

* `split_of_degTwo`: if every degree-two single mode on `x` lies in `span(L(-1)²x, L(-2)x)`
  (and `h ≠ 0`, `4h ≠ 1`), the extension splits.  A kernel-bottom vector `aR + bQ₁` would be killed
  by `L(1)` and `L(2)` (they land in `P` at weights `h + 1`, `h`, where `L(-1)x, x ∉ P`), and the
  Kac determinant `(4h-1)²` forces `a = b = 0`.
* `degTwo_le`: with the degree-one line, `H⁴₍₁₎x ∈ span(R, Q₁)` and `E₍ₘ₋₃₎x = 0`, the raising
  lemma gives the hypothesis of `split_of_degTwo`.
* `kac_zero`: `L(1)(aR + bQ₁) = L(2)(aR + bQ₁) = 0` forces `a = b = 0`.
* `E_deg2_zero`: the `E`-obstruction vanishes when the virtual eigenvalue is nonzero.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-! ## §1  General VOA: weights of the corrected vector -/

section GenL0
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

theorem L0_mode_eigen {x : M} {h : ℂ} (hxL : L0 A x = h • x) {k : ℤ} {a : V}
    (ha : a ∈ W.grading k) (n : ℤ) :
    L0 A (mode (A.YM a) n x) = (h + ((k - n - 1 : ℤ) : ℂ)) • mode (A.YM a) n x := by
  rw [L0_commutator_weak A ha x n, hxL, map_smul, ← add_smul]
  congr 1
  push_cast; ring

theorem L0_wv {x : M} {h : ℂ} (hxL : L0 A x = h • x) {k : ℤ} {t : V} (ht : t ∈ W.grading k)
    (a b : ℂ) : L0 A (TopData.wv A x t k a b) = (h + 2) • TopData.wv A x t k a b := by
  have e1 := L0_mode_eigen A hxL ht (k - 3)
  have e2 := L0_mode_eigen A hxL W.conformal_mem 0
  have e3 := L0_mode_eigen A e2 W.conformal_mem 0
  have e4 := L0_mode_eigen A hxL W.conformal_mem (-1)
  simp only [TopData.wv, map_sub, map_smul, e1, e3, e4]
  rw [show h + ((k - (k - 3) - 1 : ℤ) : ℂ) = h + 2 by push_cast; ring,
    show h + ((2 - 0 - 1 : ℤ) : ℂ) + ((2 - 0 - 1 : ℤ) : ℂ) = h + 2 by push_cast; ring,
    show h + ((2 - (-1) - 1 : ℤ) : ℂ) = h + 2 by push_cast; ring]
  module

end GenL0

/-! ## §2  `V⁺`: Kac, the degree-two span, and the splitting -/

section Frame
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h : ℂ}

/-- `span(L(-1)²x, L(-2)x)`. -/
abbrev RQspan (A : WeakModule (V2mPlus m hm) M) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {mode (A.YM (V2mPlus m hm).conformalVector) 0
    (mode (A.YM (V2mPlus m hm).conformalVector) 0 x),
    mode (A.YM (V2mPlus m hm).conformalVector) (-1) x}

include hm2 in
/-- `L(1)` and `L(2)` of `aR + bQ₁`. -/
theorem L12_RQ (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x) (a b : ℂ) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2
        (a • mode (A.YM (V2mPlus m hm).conformalVector) 0
          (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) +
          b • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) =
        (a * (4 * h + 2) + b * 3) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x ∧
      mode (A.YM (V2mPlus m hm).conformalVector) 3
        (a • mode (A.YM (V2mPlus m hm).conformalVector) 0
          (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) +
          b • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) =
        (a * (6 * h) + b * (4 * h + 1 / 2)) • x := by
  have q1 := L1_Q1 m hm A hxΩ hm2
  have q2 := L2_Q1 m hm A hxΩ hxL hm2
  rw [HP_one] at q1 q2
  constructor
  · rw [map_add, map_smul, map_smul, L1_R A hxΩ hxL, q1, smul_smul, smul_smul, ← add_smul]
  · rw [map_add, map_smul, map_smul, L2_R A hxΩ hxL, q2, smul_smul, smul_smul, ← add_smul]

/-- Kac: `(4h-1)² ≠ 0` and `L(1)`, `L(2)` of `aR + bQ₁` vanish force `a = b = 0`. -/
theorem kac_zero (h14 : 4 * h - 1 ≠ 0) (a b : ℂ) (f1 : a * (4 * h + 2) + b * 3 = 0)
    (f2 : a * (6 * h) + b * (4 * h + 1 / 2) = 0) : a = 0 ∧ b = 0 := by
  have hdet : (4 * h - 1) ^ 2 ≠ 0 := pow_ne_zero 2 h14
  have hs : (4 * h - 1) ^ 2 * a = 0 := by linear_combination (4 * h + 1 / 2) * f1 - 3 * f2
  have ht : (4 * h - 1) ^ 2 * b = 0 := by linear_combination (4 * h + 2) * f2 - 6 * h * f1
  exact ⟨(mul_eq_zero.mp hs).resolve_left hdet, (mul_eq_zero.mp ht).resolve_left hdet⟩

theorem mem_of_smul_mem {P : Submodule (modeAlg A) M} {c : ℂ} {v : M} (hc : c ≠ 0)
    (hv : c • v ∈ P) : v ∈ P := by
  have := P.smul_mem ((algebraMap ℂ (modeAlg A)) c⁻¹) hv
  rw [algebraMap_smul, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  exact this

include hm2 in
/-- **Splitting from the degree-two line.** -/
theorem split_of_degTwo (P : Submodule (modeAlg A) M) (hP : IsAtom P) (hQ : P ⋖ ⊤)
    (hb : FactorBottom A ⊥ P (h + 2)) (ht : FactorBottom A P ⊤ h)
    (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x) (hxP : x ∉ P) (hh : h ≠ 0) (h14 : 4 * h - 1 ≠ 0)
    (hD : degSpan A x 2 ≤ RQspan m hm A x) : ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
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
  obtain ⟨e1, e2⟩ := L12_RQ m hm hm2 A hxΩ hxL a b
  have hL1 := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 2 hy.1
  have hL2 := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 3 hy.1
  rw [← hab, e1] at hL1
  rw [← hab, e2] at hL2
  have f1 : a * (4 * h + 2) + b * 3 = 0 := by
    by_contra hc
    apply hxP
    have hLx := mem_of_smul_mem m hm A hc hL1
    have h2 := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 2 hLx
    rw [L1_L A hxΩ hxL] at h2
    exact mem_of_smul_mem m hm A (mul_ne_zero two_ne_zero hh) h2
  have f2 : a * (6 * h) + b * (4 * h + 1 / 2) = 0 := by
    by_contra hc
    exact hxP (mem_of_smul_mem m hm A hc hL2)
  obtain ⟨rfl, rfl⟩ := kac_zero h14 a b f1 f2
  apply hy0'
  rw [← hab]; simp

include hm2 in
/-- **The degree-two span** from the degree-one line, `H⁴₍₁₎x ∈ span(R, Q₁)` and
`E₍ₘ₋₃₎x = 0`. -/
theorem degTwo_le (hST : ScalarTop A x) (hD : Deg1Line A x)
    (hQ2 : mode (A.YM (HP m hm 2)) 1 x ∈ RQspan m hm A x)
    (hv : mode (A.YM (EP m hm)) ((m : ℤ) - 3) x = 0) :
    degSpan A x 2 ≤ RQspan m hm A x := by
  set G := Set.range (gP m hm)
  set L := RQspan m hm A x
  have hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ (V2mPlus m hm).grading j := by
    rintro g ⟨j, rfl⟩
    refine ⟨_, ?_, gP_mem_grading m hm j⟩
    fin_cases j <;> simp [wtP] <;> omega
  have hraise := raise2_mem hG (top_eq_span_iterProd m hm hm2) hST hD
  have hR : mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) ∈ L :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hQ1 : mode (A.YM (V2mPlus m hm).conformalVector) (-1) x ∈ L :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
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
        rw [hv]; exact L.zero_mem
    · rw [eq_zero_of_mem_two_gradings hj hgj hwt, map_zero, mode_zero, LinearMap.zero_apply]
      exact L.zero_mem
  apply Submodule.span_le.mpr
  rintro _ ⟨β, a, ha, rfl⟩
  rw [show β - 1 - 2 = β - 3 by ring]
  exact hgen (hraise β a ha)

end Frame

end VOA.Classification.COne.PlusRat4
