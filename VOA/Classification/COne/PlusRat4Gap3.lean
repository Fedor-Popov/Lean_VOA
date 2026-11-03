import VOA.Classification.COne.PlusRat4Model3
import VOA.Classification.COne.PlusRat4E3
import VOA.Classification.COne.PlusRat4Deg3
import VOA.Classification.COne.PlusRat4Words
import VOA.Classification.COne.PlusRat4Quarter

/-! # Gap three for charged/charged pairs

Kernel `c_{s'}` with bottom `h + 3`, quotient `c_s` with bottom `h` (`s'² = s² + 12m`).
`x` a quotient-bottom lift.  The argument is the degree-two one lifted by one level:

1. no top vectors at `h + 1`, `h + 2` (no rows there): `word_transfer` gives the degree-one line
   and the degree-two plane exactly as in the model; `E₍ₘ₋₂₎x = E₍ₘ₋₃₎x = 0`;
2. `raise3_mem`: `D₃(x) ⊆ span(V₁, V₂, V₃, H⁴₍₀₎x, E₍ₘ₋₄₎x)`;
3. `word_transfer` at degree three: `T_t - C_t·V` are top vectors (model coordinates `C_t`, pinned on
   the x-side by `L(1), L(2)`); `E₍ₘ₋₄₎x` is a top vector, killed by the virtual eigenvalue
   `6((m-3)² - 4mh) ≠ 0`;
4. the kernel character gives three relations; `Gap3Cert h` (a pure linear-algebra statement,
   checked per instance) turns them into `T₂ ∈ span(V₁, V₂, V₃)`;
5. Kac at level three (`h ∉ {0, 1/4, 1}`) excludes a kernel-bottom vector.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-- The elimination step of gap three, as a statement of linear algebra (checked per instance).
`A₂, B₂, A₃, B₃` are the degree-two coordinates of `H⁴₍₁₎x, H⁶₍₃₎x`; `C, D` the degree-three
coordinates of `T₂, T₃`, pinned by `L(1), L(2)`; `r₁, r₂, r₃` the kernel relations. -/
def Gap3Cert (h : ℂ) : Prop :=
  ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (V1 V2 V3 T2 T3 T4 : E) (A2 B2 A3 B3 C1 C2 C3 D1 D2 D3 : ℂ),
    (4 * h - 1) * A2 = -1 → (4 * h - 1) * B2 = 4 * h → (4 * h - 1) * A3 = -3 / 2 →
    (4 * h - 1) * B3 = 6 * h →
    6 * A2 - C1 * (6 * h + 6) - C2 * 3 = 0 → 6 * B2 - C2 * (2 * h + 4) - C3 * 4 = 0 →
    6 - C1 * (18 * h + 6) - C2 * (4 * h + 19 / 2) - C3 * 5 = 0 →
    (8 * A3 + 3 * A2) - D1 * (6 * h + 6) - D2 * 3 = 0 →
    (8 * B3 + 3 * B2) - D2 * (2 * h + 4) - D3 * 4 = 0 →
    15 - D1 * (18 * h + 6) - D2 * (4 * h + 19 / 2) - D3 * 5 = 0 →
    (9 / 2 : ℂ) • T2 + (9 : ℂ) • T3 - C1 • ((3 + 18 * A2) • V1 + (18 * B2) • V2 + (6 : ℂ) • T2) -
      C2 • ((6 * A2) • V1 + (3 + 6 * B2) • V2 + (6 : ℂ) • V3 + (15 : ℂ) • T2) -
      C3 • ((9 : ℂ) • V3 + (9 : ℂ) • T2) = 0 →
    (27 / 20 : ℂ) • T2 - (9 / 2 : ℂ) • T3 + (9 : ℂ) • T4 -
      D1 • ((3 + 18 * A2) • V1 + (18 * B2) • V2 + (6 : ℂ) • T2) -
      D2 • ((6 * A2) • V1 + (3 + 6 * B2) • V2 + (6 : ℂ) • V3 + (15 : ℂ) • T2) -
      D3 • ((9 : ℂ) • V3 + (9 : ℂ) • T2) = 0 →
    (3 / 2 : ℂ) • T2 + (45 : ℂ) • T3 + (15 : ℂ) • T4 -
      C1 • ((3 + 60 * A3) • V1 + (60 * B3) • V2 + (60 : ℂ) • T3) -
      C2 • ((15 * A2 + 10 * A3) • V1 + (3 + 15 * B2 + 10 * B3) • V2 + (30 : ℂ) • V3 +
        (165 / 2 : ℂ) • T2 + (45 : ℂ) • T3) -
      C3 • ((33 : ℂ) • V3 + (135 / 2 : ℂ) • T2 + (15 : ℂ) • T3) = 0 →
    T2 - C1 • V1 - C2 • V2 - C3 • V3 = 0

/-! ## §1  Word combinations for degrees two and three (general VOA) -/

section Words
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

/-- `t₍ₖ₋₃₎ - a L(-1)² - b L(-2)`. -/
def F2 (W : VertexOperatorAlgebra V) {t : V} {k : ℤ} (ht : t ∈ W.grading k) (a b : ℂ) : WComb W :=
  [(1, [⟨t, k, k - 3, ht⟩]),
   (-a, [⟨W.conformalVector, 2, 0, W.conformal_mem⟩, ⟨W.conformalVector, 2, 0, W.conformal_mem⟩]),
   (-b, [⟨W.conformalVector, 2, -1, W.conformal_mem⟩])]

/-- `t₍ₖ₋₄₎ - a L(-1)³ - b L(-1)L(-2) - c L(-3)`. -/
def F3 (W : VertexOperatorAlgebra V) {t : V} {k : ℤ} (ht : t ∈ W.grading k) (a b c : ℂ) :
    WComb W :=
  [(1, [⟨t, k, k - 4, ht⟩]),
   (-a, [⟨W.conformalVector, 2, 0, W.conformal_mem⟩, ⟨W.conformalVector, 2, 0, W.conformal_mem⟩,
     ⟨W.conformalVector, 2, 0, W.conformal_mem⟩]),
   (-b, [⟨W.conformalVector, 2, 0, W.conformal_mem⟩, ⟨W.conformalVector, 2, -1, W.conformal_mem⟩]),
   (-c, [⟨W.conformalVector, 2, -2, W.conformal_mem⟩])]

theorem evalW_F2 (A : WeakModule W M) {t : V} {k : ℤ} (ht : t ∈ W.grading k) (a b : ℂ) (y : M) :
    evalW A (F2 W ht a b) y = mode (A.YM t) (k - 3) y -
      a • mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 y) -
      b • mode (A.YM W.conformalVector) (-1) y := by
  simp only [evalW, F2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, homogeneousWord,
    LinearMap.comp_apply, LinearMap.id_apply]
  module

theorem WDeg_F2 {t : V} {k : ℤ} (ht : t ∈ W.grading k) (a b : ℂ) : WDeg (F2 W ht a b) 2 := by
  intro p hp
  simp only [F2, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp only [homogeneousDegree] <;> ring

theorem evalW_F3 (A : WeakModule W M) {t : V} {k : ℤ} (ht : t ∈ W.grading k) (a b c : ℂ) (y : M) :
    evalW A (F3 W ht a b c) y = mode (A.YM t) (k - 4) y -
      a • mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0
        (mode (A.YM W.conformalVector) 0 y)) -
      b • mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) (-1) y) -
      c • mode (A.YM W.conformalVector) (-2) y := by
  simp only [evalW, F3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, homogeneousWord,
    LinearMap.comp_apply, LinearMap.id_apply]
  module

theorem WDeg_F3 {t : V} {k : ℤ} (ht : t ∈ W.grading k) (a b c : ℂ) : WDeg (F3 W ht a b c) 3 := by
  intro p hp
  simp only [F3, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [homogeneousDegree] <;> ring

end Words

/-! ## §2  The degree-three span and the splitting -/

section Frame3
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {x : M} {h : ℂ}

/-- `span(L(-1)³x, L(-1)L(-2)x, L(-3)x)`. -/
abbrev Vspan (A : WeakModule (V2mPlus m hm) M) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range ![mode (A.YM (V2mPlus m hm).conformalVector) 0
    (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)),
    mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x),
    mode (A.YM (V2mPlus m hm).conformalVector) (-2) x])

theorem mem_Vspan_iff {v : M} : v ∈ Vspan m hm A x ↔ ∃ a b c : ℂ, a • mode (A.YM (V2mPlus m hm).conformalVector) 0
    (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)) +
    b • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) +
    c • mode (A.YM (V2mPlus m hm).conformalVector) (-2) x = v := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨f, hf⟩
    rw [Fin.sum_univ_three] at hf
    exact ⟨f 0, f 1, f 2, hf⟩
  · rintro ⟨a, b, c, habc⟩
    refine ⟨![a, b, c], ?_⟩
    rw [Fin.sum_univ_three]
    exact habc

include hm2 in
/-- **The degree-three span**, given the lower lines, `H⁴₍₀₎x ∈ span(V)` and `E₍ₘ₋₄₎x = 0`. -/
theorem degThree_le (hST : ScalarTop A x) (hD1 : Deg1Line A x) (hD2 : Deg2Plane A x)
    (hT2 : mode (A.YM (HP m hm 2)) 0 x ∈ Vspan m hm A x)
    (hv : mode (A.YM (EP m hm)) ((m : ℤ) - 4) x = 0) :
    degSpan A x 3 ≤ Vspan m hm A x := by
  set G := Set.range (gP m hm)
  set L := Vspan m hm A x
  have hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ (V2mPlus m hm).grading j := by
    rintro g ⟨j, rfl⟩
    refine ⟨_, ?_, gP_mem_grading m hm j⟩
    fin_cases j <;> simp [wtP] <;> omega
  have hraise := raise3_mem hG (top_eq_span_iterProd m hm hm2) hST hD1 hD2
  have hV1 : mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)) ∈ L := Submodule.subset_span ⟨0, rfl⟩
  have hV2 : mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) ∈ L :=
    Submodule.subset_span ⟨1, rfl⟩
  have hV3 : mode (A.YM (V2mPlus m hm).conformalVector) (-2) x ∈ L := Submodule.subset_span ⟨2, rfl⟩
  have hgen : raiseSpan3 A G x ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ (hy | ⟨j, g, ⟨i', rfl⟩, hgj, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hV1
      · exact hV2
      · exact hV3
    have hwt := gP_mem_grading m hm i'
    by_cases hj : j = wtP m i'
    · subst hj
      fin_cases i'
      · change mode (A.YM (V2mPlus m hm).conformalVector) ((2 : ℤ) - 4) x ∈ L
        rw [show (2 : ℤ) - 4 = -2 by norm_num]; exact hV3
      · change mode (A.YM (WP m hm)) ((4 : ℤ) - 4) x ∈ L
        rw [WP_eq_comb m hm]
        simp only [mode_combV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fallC]
        have e1 : mode (A.YM (HP m hm 2)) (4 - 4 - ((0 : ℕ) : ℤ)) x = mode (A.YM (HP m hm 2)) 0 x :=
          rfl
        rw [e1]
        norm_num
        exact L.smul_mem _ hT2
      · change mode (A.YM (EP m hm)) (((m : ℕ) : ℤ) - 4) x ∈ L
        rw [hv]; exact L.zero_mem
    · rw [eq_zero_of_mem_two_gradings hj hgj hwt, map_zero, mode_zero, LinearMap.zero_apply]
      exact L.zero_mem
  apply Submodule.span_le.mpr
  rintro _ ⟨β, a, ha, rfl⟩
  rw [show β - 1 - 3 = β - 4 by ring]
  exact hgen (hraise β a ha)

include hm2 in
/-- **Splitting from the degree-three span** (Kac at level three). -/
theorem split_of_degThree (P : Submodule (modeAlg A) M) (hP : IsAtom P) (hQ : P ⋖ ⊤)
    (hb : FactorBottom A ⊥ P (h + 3)) (ht : FactorBottom A P ⊤ h)
    (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x) (hxP : x ∉ P) (hx0 : x ≠ 0) (hh : h ≠ 0)
    (h14 : 4 * h - 1 ≠ 0) (h1 : h - 1 ≠ 0)
    (hD : degSpan A x 3 ≤ Vspan m hm A x) : ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  have hxg : x ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  apply (exists_cyclic_lift_iff_complement A P hQ h ht).mp
  refine ⟨x, hxg, hxP, ?_⟩
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  have hyg : y ∈ (L0 A).maxGenEigenspace (h + ((3 : ℤ) : ℂ)) := by
    rw [show h + ((3 : ℤ) : ℂ) = h + 3 by push_cast; ring]; exact hy.2
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0' x,
    no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite m hm) A hxg 3 hyg]
  intro hyD
  obtain ⟨a, b, c, habc⟩ := (mem_Vspan_iff m hm A).mp (hD (degreeSpan_le A hxL 3 hyD))
  obtain ⟨g1, g2⟩ := L12_V m hm hm2 A hxΩ hxL a b c
  have hre : ∀ k : ℂ, k.re < 3 → (h + k).re < (h + 3).re := by
    intro k hk; simp only [Complex.add_re]; linarith [show (3 : ℂ).re = 3 by norm_num]
  -- `L(1)y` and `L(2)y` lie in `P` below its bottom
  have hL1 : mode (A.YM (V2mPlus m hm).conformalVector) 2 y = 0 := by
    have hmP := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 2 hy.1
    have hmg := mode_mem_maxGenEigenspace A (V2mPlus m hm).conformal_mem 2 hyg
    rw [show h + ((3 : ℤ) : ℂ) + ((2 - 2 - 1 : ℤ) : ℂ) = h + 2 by push_cast; ring] at hmg
    exact kernel_generalized_below_bottom_eq_zero A P _ hb hmP hmg (hre 2 (by norm_num))
  have hL2 : mode (A.YM (V2mPlus m hm).conformalVector) 3 y = 0 := by
    have hmP := PlusRat2Dual.mem_P_mode A P (V2mPlus m hm).conformalVector 3 hy.1
    have hmg := mode_mem_maxGenEigenspace A (V2mPlus m hm).conformal_mem 3 hyg
    rw [show h + ((3 : ℤ) : ℂ) + ((2 - 3 - 1 : ℤ) : ℂ) = h + 1 by push_cast; ring] at hmg
    exact kernel_generalized_below_bottom_eq_zero A P _ hb hmP hmg (hre 1 (by norm_num))
  rw [← habc] at hL1 hL2
  rw [g1] at hL1
  rw [g2] at hL2
  obtain ⟨e1, e2⟩ := RQ_indep m hm hm2 A hxΩ hxL hx0 hh h14 _ _ hL1
  have hLx0 : mode (A.YM (V2mPlus m hm).conformalVector) 0 x ≠ 0 := by
    intro h0
    have := L1_L A hxΩ hxL
    rw [h0, map_zero] at this
    rcases smul_eq_zero.mp this.symm with h2 | h2
    · exact hh (by linear_combination h2 / 2)
    · exact hx0 h2
  have e3 := (smul_eq_zero.mp hL2).resolve_right hLx0
  obtain ⟨rfl, rfl, rfl⟩ := kac3_scalars h1 a b c e1 e2 e3
  apply hy0'
  rw [← habc]; simp

end Frame3

/-! ## §3  The gap-three theorem -/

section Main3
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

@[reducible] local instance zhuRing3 : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebra3 : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

set_option maxHeartbeats 4000000 in
include hm2 in
/-- **Gap-three charged/charged pairs split**, given the per-instance elimination
certificate `Gap3Cert h`. -/
theorem pairSplitting_charged_gap_three (r r' : Fin (m - 1))
    (hgap : weight m (.inl r') = weight m (.inl r) + 3)
    (huq : ∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r)
    (huq' : ∀ j : Label m, weight m j = weight m (.inl r') → j = .inl r')
    (hno1 : ∀ j : Label m, weight m j ≠ weight m (.inl r) + 1)
    (hno2 : ∀ j : Label m, weight m j ≠ weight m (.inl r) + 2)
    (h14 : 4 * hC m r - 1 ≠ 0) (h1 : hC m r - 1 ≠ 0) (hcert : Gap3Cert (hC m r)) :
    PairSplitting m hm (.inl r') (.inl r) := by
  intro M _ _ A P hP hQ hb ht
  -- arithmetic
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsq : ((r'.val + 1 : ℕ) : ℤ) ^ 2 = ((r.val + 1 : ℕ) : ℤ) ^ 2 + 12 * m := by
    have h := hgap
    simp only [weight] at h
    field_simp at h
    have : (((r'.val + 1 : ℕ) : ℤ) ^ 2 : ℚ) = ((((r.val + 1 : ℕ) : ℤ) ^ 2 + 12 * m : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast this
  have hs : r.val + 5 ≤ m := by
    have hr' := r'.isLt
    have h1' : ((r'.val + 1 : ℕ) : ℤ) ≤ (m : ℤ) - 1 := by push_cast; omega
    have h0 : (0 : ℤ) ≤ ((r'.val + 1 : ℕ) : ℤ) := by positivity
    have h3 : ((r'.val + 1 : ℕ) : ℤ) ^ 2 ≤ ((m : ℤ) - 1) ^ 2 := pow_le_pow_left₀ h0 h1' 2
    have hs1 : (1 : ℤ) ≤ ((r.val + 1 : ℕ) : ℤ) := by push_cast; omega
    have hm14 : (14 : ℤ) ≤ m := by nlinarith
    by_contra hcon
    have h2' : (m : ℤ) - 4 ≤ ((r.val + 1 : ℕ) : ℤ) := by push_cast; omega
    have h5 : 0 ≤ (((r.val + 1 : ℕ) : ℤ) - ((m : ℤ) - 4)) * (((r.val + 1 : ℕ) : ℤ) + ((m : ℤ) - 4)) :=
      mul_nonneg (sub_nonneg.mpr h2') (by push_cast; omega)
    nlinarith
  have hs3 : r.val + 3 ≤ m := by omega
  have hs4 : r.val + 4 ≤ m := by omega
  have hgapC : hC m r' = hC m r + 3 := by
    simp only [hC]; rw [hgap]; push_cast; ring
  have huqC : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r → j = .inl r :=
    fun j h => huq j (Rat.cast_injective h)
  have huqC' : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r + 3 → j = .inl r' :=
    fun j h => huq' j (Rat.cast_injective (h.trans hgapC.symm))
  have hnoC : ∀ k : ℕ, 0 < k → k < 3 → ∀ j : Label m, ((weight m j : ℚ) : ℂ) ≠ hC m r + k := by
    intro k hk0 hk3 j h
    interval_cases k
    · apply hno1 j; apply Rat.cast_injective (α := ℂ); rw [h]; push_cast; rfl
    · apply hno2 j; apply Rat.cast_injective (α := ℂ); rw [h]; push_cast; rfl
  change FactorBottom A ⊥ P (hC m r') at hb
  change FactorBottom A P ⊤ (hC m r) at ht
  rw [hgapC] at hb
  set h := hC m r with hhdef
  have hh : h ≠ 0 := hC_ne_zero m hm2 r
  have hre : (h + 3).re = h.re + 3 := by simp
  have hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0 := by
    intro μ hμ v hv
    have hvP : v ∈ P := by
      by_contra hc
      have hw : FactorWeight A P ⊤ μ := fun hT => hc (hT ⟨Submodule.mem_top, hv⟩)
      have := ht.2 μ hw
      linarith
    exact kernel_generalized_below_bottom_eq_zero A P _ hb hvP hv (by rw [hre]; linarith)
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift (V2mPlus_c2Cofinite m hm) A P hP
    (show h + 3 ≠ h by intro hc; have := congrArg (· - h) hc; simp at this) hb ht
  have hx0 : x ≠ 0 := fun h => hxP (h ▸ P.zero_mem)
  have hxg : x ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  have hxΩ : x ∈ Omega A := by
    intro β v hv n hn
    apply hlow _ _ _ (mode_mem_maxGenEigenspace A hv n hxg)
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show β - n - 1 ≤ -1 by omega)
    rw [Complex.add_re, Complex.intCast_re]
    linarith
  -- intermediate top vectors vanish
  have hmid : ∀ k : ℕ, 0 < k → k < 3 → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0 := by
    intro k hk0 hk3 v hv hvL
    have h0 := top_eval_zero_of_rows m hm hm2 A hv (c := h + k) hvL 1
      (fun j hj => absurd hj (hnoC k hk0 hk3 j))
    rwa [topEvaluation_one] at h0
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
  -- the model
  have heTD := lat_topData m hm hm2 r hs3
  have he0 := latVacuumGen_ne_zero' m hm
  set B := (Ns m hm r).toWeakModule
  set e := latVacuumGen (latP m)
  -- degree one
  have hD1 : Deg1Line A x := by
    intro j c hc
    obtain ⟨κ, hκ⟩ := transfer_Omega_gen m hm hm2 r hs3 huqC A hxΩ hxL hlow hc
    refine ⟨κ, ?_⟩
    have hL : L0 A (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
        (h + ((1 : ℕ) : ℂ)) • (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) := by
      rw [map_sub, map_smul, L0_mode_eigen A hxL hc, L0_mode_eigen A hxL (V2mPlus m hm).conformal_mem]
      push_cast
      module
    exact sub_eq_zero.mp (hmid 1 (by norm_num) (by norm_num) _ hκ hL)
  have hxTD : TopData A χ h x := ⟨hxΩ, hχx, hxL, hD1⟩
  have hLx0 := hxTD.Lm1_ne_zero hh hx0
  obtain ⟨hp2, hp3⟩ := charged_consts m hm A hxΩ hxL hh hx0 hD1 h4 h6
  have hE1 : mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0 := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ (EP_mem_grading m hm)
    have hβ := L1G_v m hm A hxΩ hE0
    rw [hκ, map_smul, L1_L A hxΩ hxL, smul_smul] at hβ
    have hk : κ * (2 * h) = 0 := (smul_eq_zero.mp hβ).resolve_right hx0
    have hk' : κ = 0 := (mul_eq_zero.mp hk).resolve_right (mul_ne_zero two_ne_zero hh)
    rw [hκ, hk', zero_smul]
  -- degree two: the plane, by word transfer
  have hWT := word_transfer A B χ hxΩ heTD.omega hχx heTD.char hxL heTD.L0 he0 hlow 3 hmid
  have hD2 : Deg2Plane A x := by
    intro j c hc
    have hte : mode ((Ns m hm r).YM c) (j - 3) e ∈ (Ns m hm r).weight (h + 2) := by
      have h' := mode_mem_weight (Ns m hm r) hc (es_weight m hm r) (j - 3)
      have hc' : h + (j : ℂ) - ((j - 3 : ℤ) : ℂ) - 1 = h + 2 := by push_cast; ring
      rwa [hc'] at h'
    obtain ⟨a, b, hab⟩ := lat_deg2 m hm hm2 r hs4 h14 hc
    refine ⟨a, b, ?_⟩
    have hFe : evalW B (F2 (V2mPlus m hm) hc a b) e = 0 := by
      rw [evalW_F2, hab]; abel
    have := (hWT 2 (by norm_num) _ (WDeg_F2 hc a b) hFe).2 (by norm_num)
    rw [evalW_F2] at this
    rw [← sub_eq_zero, ← this]; abel
  -- the degree-two coordinates
  have q1L1 := L1_Q1 m hm A hxΩ hm2
  have q1L2 := L2_Q1 m hm A hxΩ hxL hm2
  have q2L1 := L1_Q2 m hm A hxΩ hp2
  have q2L2 := L2_Q2 m hm A hxΩ hxL h4
  have q3L1 := L1_Q3 m hm A hxΩ hp2 hp3
  have q3L2 := L2_Q3 m hm A hxΩ hxL h4 h6
  have rL1 := L1_R A hxΩ hxL
  have rL2 := L2_R A hxΩ hxL
  rw [HP_one] at q1L1 q1L2 q2L1 q3L1
  have coords : ∀ {j : ℤ} {c : VP m hm} {α β : ℂ}, c ∈ (V2mPlus m hm).grading j →
      mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM c) (j - 3) x) =
        α • mode (A.YM (V2mPlus m hm).conformalVector) 0 x →
      mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM c) (j - 3) x) = β • x →
      ∃ a b : ℂ, mode (A.YM c) (j - 3) x =
          a • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) +
            b • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x ∧
        α - a * (4 * h + 2) - b * 3 = 0 ∧ β - a * (6 * h) - b * (4 * h + 1 / 2) = 0 := by
    intro j c α β hc hα hβ
    obtain ⟨a, b, hab⟩ := hD2 j c hc
    refine ⟨a, b, hab, ?_, ?_⟩
    · rw [hab, map_add, map_smul, map_smul, rL1, q1L1, smul_smul, smul_smul, ← add_smul] at hα
      have : (α - a * (4 * h + 2) - b * 3) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
        rw [sub_smul, sub_smul, ← hα]; module
      exact (smul_eq_zero.mp this).resolve_right hLx0
    · rw [hab, map_add, map_smul, map_smul, rL2, q1L2, smul_smul, smul_smul, ← add_smul] at hβ
      have : (β - a * (6 * h) - b * (4 * h + 1 / 2)) • x = 0 := by
        rw [sub_smul, sub_smul, ← hβ]; module
      exact (smul_eq_zero.mp this).resolve_right hx0
  obtain ⟨A2, B2, hQ2, fa2, fb2⟩ := coords hg2 (by rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num]; exact q2L1)
    (by rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num]; exact q2L2)
  obtain ⟨A3, B3, hQ3, fa3, fb3⟩ := coords hg3 (by rw [show ((2 * 3 : ℕ) : ℤ) - 3 = 3 by norm_num]; exact q3L1)
    (by rw [show ((2 * 3 : ℕ) : ℤ) - 3 = 3 by norm_num]; exact q3L2)
  rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num] at hQ2
  rw [show ((2 * 3 : ℕ) : ℤ) - 3 = 3 by norm_num] at hQ3
  obtain ⟨sa2, sb2⟩ := solve_AB fa2 fb2
  obtain ⟨sa3, sb3⟩ := solve_AB fa3 fb3
  have hA2 : (4 * h - 1) * A2 = -1 := by
    have h1' : (4 * h - 1) * ((4 * h - 1) * A2 + 1) = 0 := by linear_combination sa2
    linear_combination (mul_eq_zero.mp h1').resolve_left h14
  have hB2 : (4 * h - 1) * B2 = 4 * h := by
    have h1' : (4 * h - 1) * ((4 * h - 1) * B2 - 4 * h) = 0 := by linear_combination sb2
    linear_combination (mul_eq_zero.mp h1').resolve_left h14
  have hA3 : (4 * h - 1) * A3 = -3 / 2 := by
    have h1' : (4 * h - 1) * ((4 * h - 1) * A3 + 3 / 2) = 0 := by linear_combination sa3
    linear_combination (mul_eq_zero.mp h1').resolve_left h14
  have hB3 : (4 * h - 1) * B3 = 6 * h := by
    have h1' : (4 * h - 1) * ((4 * h - 1) * B3 - 6 * h) = 0 := by linear_combination sb3
    linear_combination (mul_eq_zero.mp h1').resolve_left h14
  -- `E₍ₘ₋₃₎x = 0`
  have hE2 : mode (A.YM (EP m hm)) ((m : ℤ) - 3) x = 0 := by
    obtain ⟨a, b, hab, fa, fb⟩ := coords (α := 0) (β := 0) (EP_mem_grading m hm)
      (by rw [L1_v m hm A hxΩ hE1, zero_smul]) (by rw [L2_v m hm A hxΩ hE0, zero_smul])
    obtain ⟨rfl, rfl⟩ := kac_zero h14 a b (by linear_combination -fa) (by linear_combination -fb)
    rw [hab]; simp
  -- degree three: transfer
  have hD3 : ∀ {k : ℤ} {t : VP m hm}, t ∈ (V2mPlus m hm).grading k → ∃ a b c : ℂ,
      (mode (A.YM t) (k - 4) x -
        a • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0
          (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)) -
        b • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) -
        c • mode (A.YM (V2mPlus m hm).conformalVector) (-2) x) ∈ Omega A ∧
      L0 A (mode (A.YM t) (k - 4) x -
        a • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0
          (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)) -
        b • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) -
        c • mode (A.YM (V2mPlus m hm).conformalVector) (-2) x) = (h + 3) •
      (mode (A.YM t) (k - 4) x -
        a • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0
          (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)) -
        b • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) -
        c • mode (A.YM (V2mPlus m hm).conformalVector) (-2) x) := by
    intro k t htk
    have hte : mode ((Ns m hm r).YM t) (k - 4) e ∈ (Ns m hm r).weight (h + 3) := by
      have h' := mode_mem_weight (Ns m hm r) htk (es_weight m hm r) (k - 4)
      have hc' : h + (k : ℂ) - ((k - 4 : ℤ) : ℂ) - 1 = h + 3 := by push_cast; ring
      rwa [hc'] at h'
    obtain ⟨a, b, c, habc⟩ := lat_deg3 m hm hm2 r hs h14 h1 hte
    refine ⟨a, b, c, ?_, ?_⟩
    · have hFe : evalW B (F3 (V2mPlus m hm) htk a b c) e = 0 := by
        rw [evalW_F3, habc]; abel
      have := (hWT 3 le_rfl _ (WDeg_F3 htk a b c) hFe).1
      rwa [evalW_F3] at this
    · have := evalW_eigen A hxL (F3 (V2mPlus m hm) htk a b c) (WDeg_F3 htk a b c)
      rw [evalW_F3] at this
      exact_mod_cast this
  -- the kernel character
  have hker : ∀ w : M, w ∈ Omega A → L0 A w = (h + 3) • w →
      mode (A.YM (HP m hm 2)) 3 w = 0 ∧ mode (A.YM (HP m hm 3)) 5 w = 0 := by
    intro w hw hwL
    have hrow : ∀ t, t = 2 ∨ t = 3 → topEvaluation A w hw (VOA.mk (V2mPlus m hm) (HP m hm t)) = 0 :=
      fun t ht' => top_eval_zero_of_rows m hm hm2 A hw (c := h + 3) hwL _ (fun j hj => by
        rw [huqC' j hj]; exact chiT_HP_zero m hm hm2 r' t ht')
    have e2 := hrow 2 (Or.inl rfl)
    have e3 := hrow 3 (Or.inr rfl)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 hg2] at e2
    rw [topEvaluation_mk, oLevW_homogeneous A 0 hg3] at e3
    exact ⟨e2, e3⟩
  -- Virasoro values at level three
  have v1L1 := L1_V1 m hm hm2 A hxΩ hxL
  have v2L1 := L1_V2 m hm hm2 A hxΩ hxL
  have v3L1 := L1_V3 m hm hm2 A hxΩ hxL
  have v1L2 := L2_V1 m hm hm2 A hxΩ hxL
  have v2L2 := L2_V2 m hm hm2 A hxΩ hxL
  have v3L2 := L2_V3 m hm hm2 A hxΩ hxL
  have t2L1 := L1_T2 m hm A hxΩ
  have t2L2 := L2_T2 m hm A hxΩ hxL hp2 hm2
  have t3L1 := L1_T3 m hm A hxΩ hp2
  have t3L2 := L2_T3 m hm A hxΩ hxL hp2 hp3
  rw [HP_one] at t2L2 t3L2
  -- coordinates of `T₂`
  obtain ⟨C1, C2, C3, hw2, hw2L⟩ := hD3 hg2
  rw [show ((2 * 2 : ℕ) : ℤ) - 4 = 0 by norm_num] at hw2 hw2L
  obtain ⟨D1, D2, D3, hw3, hw3L⟩ := hD3 hg3
  rw [show ((2 * 3 : ℕ) : ℤ) - 4 = 2 by norm_num] at hw3 hw3L
  have hL1 : ∀ w : M, w ∈ Omega A → mode (A.YM (V2mPlus m hm).conformalVector) 2 w = 0 :=
    fun w hw => Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (by norm_num)
  have hL2 : ∀ w : M, w ∈ Omega A → mode (A.YM (V2mPlus m hm).conformalVector) 3 w = 0 :=
    fun w hw => Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (by norm_num)
  have g1 := hL1 _ hw2
  have g2 := hL2 _ hw2
  have g3 := hL1 _ hw3
  have g4 := hL2 _ hw3
  rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, t2L1, hQ2, v1L1, v2L1, v3L1] at g1
  rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, t2L2, v1L2, v2L2, v3L2] at g2
  rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, t3L1, hQ2, hQ3, v1L1, v2L1, v3L1] at g3
  rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, t3L2, v1L2, v2L2, v3L2] at g4
  obtain ⟨e1, e2⟩ := RQ_indep m hm hm2 A hxΩ hxL hx0 hh h14
    (6 * A2 - C1 * (6 * h + 6) - C2 * 3) (6 * B2 - C2 * (2 * h + 4) - C3 * 4)
    (by linear_combination (norm := module) g1)
  have e3 : 6 - C1 * (18 * h + 6) - C2 * (4 * h + 19 / 2) - C3 * 5 = 0 := by
    have : (6 - C1 * (18 * h + 6) - C2 * (4 * h + 19 / 2) - C3 * 5) •
        mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g2
    exact (smul_eq_zero.mp this).resolve_right hLx0
  obtain ⟨f1, f2⟩ := RQ_indep m hm hm2 A hxΩ hxL hx0 hh h14
    ((8 * A3 + 3 * A2) - D1 * (6 * h + 6) - D2 * 3) ((8 * B3 + 3 * B2) - D2 * (2 * h + 4) - D3 * 4)
    (by linear_combination (norm := module) g3)
  have f3 : 15 - D1 * (18 * h + 6) - D2 * (4 * h + 19 / 2) - D3 * 5 = 0 := by
    have : (15 - D1 * (18 * h + 6) - D2 * (4 * h + 19 / 2) - D3 * 5) •
        mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g4
    exact (smul_eq_zero.mp this).resolve_right hLx0
  -- the `E`-part at degree three
  have hE3 : mode (A.YM (EP m hm)) ((m : ℤ) - 4) x = 0 := by
    obtain ⟨aE, bE, cE, hwE, hwEL⟩ := hD3 (EP_mem_grading m hm)
    have gE1 := hL1 _ hwE
    have gE2 := hL2 _ hwE
    have hvL1 : mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM (EP m hm)) ((m : ℤ) - 4) x) = 0 := by
      rw [L1_on_gen m hm A hxΩ (EP_mem_grading m hm) _, L1_E m hm, map_zero, mode_zero,
        LinearMap.zero_apply, add_zero, show (m : ℤ) - 4 + 1 = (m : ℤ) - 3 by ring, hE2, smul_zero]
    have hvL2 : mode (A.YM (V2mPlus m hm).conformalVector) 3 (mode (A.YM (EP m hm)) ((m : ℤ) - 4) x) = 0 := by
      have e3' : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (EP m hm) = 0 := L2_E m hm
      rw [L2_on3 A hxΩ (EP_mem_grading m hm) _, L1_E m hm, e3',
        show (m : ℤ) - 4 + 2 = (m : ℤ) - 2 by ring, hE1]
      simp
    rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, hvL1, v1L1, v2L1, v3L1] at gE1
    rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, hvL2, v1L2, v2L2, v3L2] at gE2
    obtain ⟨k1, k2⟩ := RQ_indep m hm hm2 A hxΩ hxL hx0 hh h14
      (aE * (6 * h + 6) + bE * 3) (bE * (2 * h + 4) + cE * 4)
      (by linear_combination (norm := module) -gE1)
    have k3 : aE * (18 * h + 6) + bE * (4 * h + 19 / 2) + cE * 5 = 0 := by
      have : (aE * (18 * h + 6) + bE * (4 * h + 19 / 2) + cE * 5) •
          mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
        linear_combination (norm := module) -gE2
      exact (smul_eq_zero.mp this).resolve_right hLx0
    obtain ⟨rfl, rfl, rfl⟩ := kac3_scalars h1 aE bE cE k1 k2 k3
    simp only [zero_smul, sub_zero] at hwE hwEL
    have o := (hker _ hwE hwEL).1
    have ev := oH4_v3 m hm A hxΩ hxL h4 hE0 hE1 hE2
    rw [o, smul_zero, mul_zero, zero_add] at ev
    have hne : (6 * (((m : ℂ) - 3) ^ 2 - 4 * m * h)) ≠ 0 := by
      rw [hhdef, four_m_hC m hm2 r]
      have hq : ((m : ℂ) - 3) ^ 2 - ((r.val + 1 : ℕ) : ℂ) ^ 2 =
          ((m : ℂ) - 3 - ((r.val + 1 : ℕ) : ℂ)) * ((m : ℂ) - 3 + ((r.val + 1 : ℕ) : ℂ)) := by ring
      rw [hq]
      have hq1 : ((m : ℂ) - 3 - ((r.val + 1 : ℕ) : ℂ)) ≠ 0 := by
        have : ((m : ℤ) - 3 - ((r.val + 1 : ℕ) : ℤ)) ≠ 0 := by omega
        exact_mod_cast this
      have hq2 : ((m : ℂ) - 3 + ((r.val + 1 : ℕ) : ℂ)) ≠ 0 := by
        have : ((m : ℤ) - 3 + ((r.val + 1 : ℕ) : ℤ)) ≠ 0 := by omega
        exact_mod_cast this
      exact mul_ne_zero (by norm_num) (mul_ne_zero hq1 hq2)
    exact (smul_eq_zero.mp ev.symm).resolve_left hne
  -- the three relations
  have eT2 := oH4_T2 m hm A h4
  have eT3 := oH4_T3 m hm A h4
  have fT2 := oH6_T2 m hm A h6
  have eV1 := oH4_V1 m hm A h4 hp2
  have eV2 := oH4_V2 m hm A h4 hp2
  have eV3 := oH4_V3 m hm A h4
  have fV1 := oH6_V1 m hm A h6 hp3
  have fV2 := oH6_V2 m hm A h6 hp3
  have fV3 := oH6_V3 m hm A h6
  rw [HP_one] at eV1 eV2 eV3 fV1 fV2 fV3
  rw [hQ2] at eV1 eV2 fV2
  rw [hQ3] at fV1 fV2
  simp only [map_add, map_smul] at eV1 eV2 fV1 fV2
  obtain ⟨o4, o6⟩ := hker _ hw2 hw2L
  obtain ⟨o4', -⟩ := hker _ hw3 hw3L
  rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, eT2, eV1, eV2, eV3] at o4
  rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, eT3, eV1, eV2, eV3] at o4'
  rw [map_sub, map_sub, map_sub, map_smul, map_smul, map_smul, fT2, fV1, fV2, fV3] at o6
  have hrel := hcert (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (V2mPlus m hm).conformalVector) 0 x)))
    (mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) (-1) x))
    (mode (A.YM (V2mPlus m hm).conformalVector) (-2) x) (mode (A.YM (HP m hm 2)) 0 x)
    (mode (A.YM (HP m hm 3)) 2 x) (mode (A.YM (HP m hm 4)) 4 x) A2 B2 A3 B3 C1 C2 C3 D1 D2 D3
    hA2 hB2 hA3 hB3 e1 e2 e3 f1 f2 f3
    (by linear_combination (norm := module) o4) (by linear_combination (norm := module) o4')
    (by linear_combination (norm := module) o6)
  have hT2 : mode (A.YM (HP m hm 2)) 0 x ∈ Vspan m hm A x := by
    rw [mem_Vspan_iff]
    exact ⟨C1, C2, C3, by linear_combination (norm := module) -hrel⟩
  have hST : ScalarTop A x := ⟨hxΩ, fun j c hc => ⟨_, hzero hc⟩⟩
  exact split_of_degThree m hm hm2 A P hP hQ hb ht hxΩ hxL hxP hx0 hh h14 h1
    (degThree_le m hm hm2 A hST hD1 hD2 hT2 hE3)

end Main3

end VOA.Classification.COne.PlusRat4
