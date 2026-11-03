/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.AKGradingInstance
import VOA.Modularity.SqModeWeight
import VOA.Modularity.SqWeightNat
import VOA.Modularity.SquareBracketVirasoro
import VOA.Modularity.ZhuRecursion

/-!
# `AKWeightGrading` for every VOA

* (B) `akTotalWeightSpace_isInternal`: `E46 ⊗ 𝒱` is the internal direct sum of its total-weight spaces.
  - Spanning: pure tensors split into homogeneous pieces.
  - Independence: every total-weight space lies in an eigenspace of `Wt ⊗ 1 + 1 ⊗ L[0]`.
* (C) `blockRelSpanE_isHomogeneous`: Zhu's relation module is homogeneous for the total weight. Every
  generator is a sum of relations in `L[0]`-homogeneous inputs, and those relations are homogeneous by
  Zhu's covariance `sqMode_mem_sqWeightSpace`.
* `akWeightGrading W : AKWeightGrading W`, for **every** `W : VertexOperatorAlgebra 𝒱`.
-/

open scoped TensorProduct

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-! ## (B) The total-weight decomposition -/

/-- The modular-weight operator `f ↦ Σ_k k·f_k` on `E46`. -/
noncomputable def e46WtOp : E46 →ₗ[ℂ] E46 :=
  letI := e46Decomposition
  (DirectSum.toModule ℂ ℤ E46 fun k => (k : ℂ) • (e46WeightSpace k).subtype).comp
    (DirectSum.decomposeLinearEquiv e46WeightSpace).toLinearMap

theorem e46WtOp_of_mem {k : ℤ} {f : E46} (hf : f ∈ e46WeightSpace k) :
    e46WtOp f = (k : ℂ) • f := by
  letI := e46Decomposition
  simp only [e46WtOp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem e46WeightSpace hf]
  erw [DirectSum.toModule_lof]
  rfl

/-- The total-weight operator `Wt ⊗ 1 + 1 ⊗ L[0]`. -/
noncomputable def akTotalOp : 𝒱E 𝒱 →ₗ[ℂ] 𝒱E 𝒱 :=
  TensorProduct.map e46WtOp LinearMap.id + TensorProduct.map LinearMap.id (Lsq W 0)

theorem akTotalWeightSpace_le_eigenspace (n : ℤ) :
    akTotalWeightSpace W n ≤ Module.End.eigenspace (akTotalOp W) (n : ℂ) := by
  rw [akTotalWeightSpace, Submodule.span_le]
  rintro x ⟨p, q, f, v, hpq, hf, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
  rw [mem_sqWeightSpace_iff] at hv
  simp only [akTotalOp, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    e46WtOp_of_mem hf, hv, TensorProduct.smul_tmul, TensorProduct.tmul_smul, ← add_smul]
  rw [← hpq]; push_cast; ring_nf

theorem akTotalWeightSpace_iSupIndep : iSupIndep (akTotalWeightSpace W) :=
  (iSupIndep.comp (Module.End.eigenspaces_iSupIndep (akTotalOp W))
    (Int.cast_injective (α := ℂ))).mono fun n => akTotalWeightSpace_le_eigenspace W n

theorem akTotalWeightSpace_iSup_eq_top : ⨆ n, akTotalWeightSpace W n = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨f, v, rfl⟩
  have hf : f ∈ ⨆ k, e46WeightSpace k := by rw [e46WeightSpace_iSup_eq_top]; trivial
  have hv : v ∈ ⨆ m : ℕ, sqWeightSpace W ((m : ℕ) : ℂ) := by
    rw [sqWeightSpace_nat_spans_top]; trivial
  induction hf using Submodule.iSup_induction' with
  | mem p f hf =>
      induction hv using Submodule.iSup_induction' with
      | mem q v hv =>
          refine Submodule.mem_iSup_of_mem (p + q) ?_
          exact tmul_mem_akTotalWeightSpace W hf (q := q) (by exact_mod_cast hv)
      | zero => simp
      | add v v' _ _ h h' => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h h'
  | zero => simp
  | add f f' _ _ h h' => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ h h'

/-- (B) **`E46 ⊗ 𝒱` is graded by total weight.** -/
theorem akTotalWeightSpace_isInternal : DirectSum.IsInternal (akTotalWeightSpace W) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨akTotalWeightSpace_iSupIndep W, akTotalWeightSpace_iSup_eq_top W⟩

@[reducible] noncomputable def akTotalDecomposition : DirectSum.Decomposition (akTotalWeightSpace W) :=
  (akTotalWeightSpace_isInternal W).chooseDecomposition

/-! ## (C) Homogeneity of Zhu's relation module -/

section Homogeneity

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ℳ : ℤ → Submodule ℂ M}
  [DirectSum.Decomposition ℳ]

/-- A span of homogeneous elements is homogeneous. -/
theorem isHomogeneous_span (H : Set M) (hH : ∀ h ∈ H, ∃ i, h ∈ ℳ i) :
    DirectSum.SetLike.IsHomogeneous ℳ (Submodule.span ℂ H) := by
  classical
  intro i m hm
  induction hm using Submodule.span_induction with
  | mem h hh =>
      obtain ⟨j, hj⟩ := hH h hh
      by_cases hij : j = i
      · subst hij; rw [DirectSum.decompose_of_mem_same ℳ hj]; exact Submodule.subset_span hh
      · rw [DirectSum.decompose_of_mem_ne ℳ hj hij]; exact Submodule.zero_mem _
  | zero => rw [DirectSum.decompose_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      rw [DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]
      exact Submodule.smul_mem _ c hx

end Homogeneity

theorem vacuum_mem_sqWeightSpace_zero' : W.vacuum ∈ sqWeightSpace W ((0 : ℤ) : ℂ) := by
  rw [mem_sqWeightSpace_iff, Int.cast_zero, zero_smul, Lsq_zero_apply]
  refine finsum_eq_zero_of_forall_eq_zero (fun a => ?_)
  by_cases ha : a < 0
  · rw [sqBracketCoeff_zero_of_neg ha, zero_smul]
  · push Not at ha
    rw [VertexOperatorAlgebra.L_def,
      show mode (W.Y W.conformalVector) (a + 1) W.vacuum
        = W.smul W.conformalVector (a + 1) W.vacuum from rfl,
      W.smul_vacuum_nonneg _ (by omega), smul_zero]

/-- The vacuum's square-bracket modes vanish away from `−1`, by Zhu's covariance. -/
theorem sqMode_vacuum_eq_zero {j : ℤ} (hj : j ≠ -1) (x : 𝒱) : sqMode W j W.vacuum x = 0 := by
  have hvac : ∀ y : 𝒱, sqMode W j W.vacuum y = sqBracketCoeffZ 0 j (-1) • y := fun y => by
    rw [sqMode_of_mem_grading W W.vacuum_mem j]
    exact vSqZ_vacuum_scalar W j y
  rw [hvac]
  by_cases h0 : W.vacuum = 0
  · have hx : x = 0 := by
      have := W.smul_vacuum_neg_one x
      rw [h0] at this
      rw [← this]
      exact map_zero _
    rw [hx, smul_zero]
  · have h1 := sqMode_mem_sqWeightSpace W (vacuum_mem_sqWeightSpace_zero' W)
      (vacuum_mem_sqWeightSpace_zero' W) j
    rw [hvac] at h1
    have h2 : sqBracketCoeffZ 0 j (-1) • W.vacuum ∈ sqWeightSpace W ((0 : ℤ) : ℂ) :=
      Submodule.smul_mem _ _ (vacuum_mem_sqWeightSpace_zero' W)
    have hne : (((0 + 0 - j - 1 : ℤ)) : ℂ) ≠ ((0 : ℤ) : ℂ) := by
      exact_mod_cast (show (0 + 0 - j - 1 : ℤ) ≠ 0 by omega)
    have hd := (sqWeightSpace_iSupIndep W).pairwiseDisjoint hne
    have hz := (Submodule.disjoint_def.mp hd) _ h1 h2
    rcases smul_eq_zero.mp hz with hs | hs
    · rw [hs, zero_smul]
    · exact absurd hs h0

/-- The `a[0]`-relation, on arbitrary inputs. -/
noncomputable def relS (b x : 𝒱) : 𝒱E 𝒱 := ιE (sqMode W 0 b x)

/-- The `a[−2]`-relation with an Eisenstein tail of length `K`, on arbitrary inputs. -/
noncomputable def relR (K : ℕ) (b x : 𝒱) : 𝒱E 𝒱 :=
  ιE (sqMode W (-2) b x) +
    ∑ m ∈ Finset.range K, coefE m • ιE (sqMode W (2 * (m + 2) - 2 : ℤ) b x)

theorem relS_add_left (b b' x : 𝒱) : relS W (b + b') x = relS W b x + relS W b' x := by
  rw [relS, relS, relS, map_add, LinearMap.add_apply, map_add]
theorem relS_add_right (b x x' : 𝒱) : relS W b (x + x') = relS W b x + relS W b x' := by
  rw [relS, relS, relS, map_add (sqMode W 0 b), map_add]
theorem relR_add_left (K : ℕ) (b b' x : 𝒱) :
    relR W K (b + b') x = relR W K b x + relR W K b' x := by
  simp only [relR, map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]; abel
theorem relR_add_right (K : ℕ) (b x x' : 𝒱) :
    relR W K b (x + x') = relR W K b x + relR W K b x' := by
  simp only [relR, map_add, smul_add, Finset.sum_add_distrib]; abel
theorem relS_zero_left (x : 𝒱) : relS W 0 x = 0 := by
  rw [relS, map_zero, LinearMap.zero_apply, map_zero]
theorem relS_zero_right (b : 𝒱) : relS W b 0 = 0 := by
  rw [relS, map_zero, map_zero]
theorem relR_zero_left (K : ℕ) (x : 𝒱) : relR W K 0 x = 0 := by
  simp only [relR, map_zero, LinearMap.zero_apply, smul_zero, Finset.sum_const_zero, add_zero]
theorem relR_zero_right (K : ℕ) (b : 𝒱) : relR W K b 0 = 0 := by
  simp only [relR, map_zero, smul_zero, Finset.sum_const_zero, add_zero]

theorem relS_vacuum (c : ℂ) (x : 𝒱) : relS W (c • W.vacuum) x = 0 := by
  simp only [relS, map_smul, LinearMap.smul_apply,
    sqMode_vacuum_eq_zero W (show (0 : ℤ) ≠ -1 by omega), smul_zero, map_zero]

theorem relR_vacuum (K : ℕ) (c : ℂ) (x : 𝒱) : relR W K (c • W.vacuum) x = 0 := by
  simp only [relR, map_smul, LinearMap.smul_apply,
    sqMode_vacuum_eq_zero W (show (-2 : ℤ) ≠ -1 by omega), smul_zero, map_zero, zero_add]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [sqMode_vacuum_eq_zero W (by omega)]
  simp

/-- Every `a[0]`-relation lies in the relation module. -/
theorem relS_mem (b x : 𝒱) : relS W b x ∈ blockRelSpanE W := by
  have hb : b ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  induction hb using Submodule.iSup_induction' with
  | mem k b hb =>
      rcases lt_trichotomy k 0 with hk | rfl | hk
      · rw [W.positivity k hk, Submodule.mem_bot] at hb; rw [hb, relS_zero_left]
        exact Submodule.zero_mem _
      · rw [W.vacuum_grade] at hb
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
        rw [relS_vacuum]; exact Submodule.zero_mem _
      · have hb' : b ∈ W.grading ((k.toNat : ℕ) : ℤ) := by rwa [Int.toNat_of_nonneg hk.le]
        refine Submodule.subset_span (Or.inl ⟨k.toNat, b, x, by omega, hb', ?_⟩)
        rw [relS, sqMode_of_mem_grading W hb]
  | zero => rw [relS_zero_left]; exact Submodule.zero_mem _
  | add b b' _ _ h h' => rw [relS_add_left]; exact Submodule.add_mem _ h h'

/-- Every long enough `a[−2]`-relation lies in the relation module. -/
theorem relR_mem (b x : 𝒱) : ∃ K0 : ℕ, ∀ K, K0 ≤ K → relR W K b x ∈ blockRelSpanE W := by
  have hb : b ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  induction hb using Submodule.iSup_induction' with
  | mem k b hb =>
      rcases lt_trichotomy k 0 with hk | rfl | hk
      · rw [W.positivity k hk, Submodule.mem_bot] at hb
        exact ⟨0, fun K _ => by rw [hb, relR_zero_left]; exact Submodule.zero_mem _⟩
      · rw [W.vacuum_grade] at hb
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
        exact ⟨0, fun K _ => by rw [relR_vacuum]; exact Submodule.zero_mem _⟩
      · have hb' : b ∈ W.grading ((k.toNat : ℕ) : ℤ) := by rwa [Int.toNat_of_nonneg hk.le]
        obtain ⟨N, hN⟩ := vSqZ_eventually_zero W b k.toNat x
        refine ⟨N.toNat, fun K hK => Submodule.subset_span (Or.inr ⟨k.toNat, K, b, x, by omega,
          hb', fun m hm => hN _ (by omega), ?_⟩)⟩
        simp only [relR, sqMode_of_mem_grading W hb]
  | zero => exact ⟨0, fun K _ => by rw [relR_zero_left]; exact Submodule.zero_mem _⟩
  | add b b' _ _ h h' =>
      obtain ⟨K1, h1⟩ := h
      obtain ⟨K2, h2⟩ := h'
      exact ⟨max K1 K2, fun K hK => by
        rw [relR_add_left]
        exact Submodule.add_mem _ (h1 K (le_of_max_le_left hK)) (h2 K (le_of_max_le_right hK))⟩

theorem coefE_mem (m : ℕ) : coefE m ∈ e46WeightSpace (2 * ((m : ℤ) + 2)) := by
  have h := (zhuGE_weight (m + 2) (by omega)).smul (((2 * (m + 2) - 1 : ℕ) : ℂ))
  push_cast at h
  exact h

theorem relS_homog {K n : ℤ} {b x : 𝒱} (hb : b ∈ sqWeightSpace W (K : ℂ))
    (hx : x ∈ sqWeightSpace W (n : ℂ)) : relS W b x ∈ akTotalWeightSpace W (K + n - 0 - 1) :=
  ιE_mem_akTotalWeightSpace W (sqMode_mem_sqWeightSpace W hb hx 0)

theorem relR_homog (L : ℕ) {K n : ℤ} {b x : 𝒱} (hb : b ∈ sqWeightSpace W (K : ℂ))
    (hx : x ∈ sqWeightSpace W (n : ℂ)) : relR W L b x ∈ akTotalWeightSpace W (K + n + 1) := by
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun m _ => ?_)
  · have := ιE_mem_akTotalWeightSpace W (sqMode_mem_sqWeightSpace W hb hx (-2))
    rwa [show K + n - -2 - 1 = K + n + 1 by ring] at this
  · have := e46Weight_smul_mem_akTotalWeightSpace W (coefE_mem m)
      (ιE_mem_akTotalWeightSpace W (sqMode_mem_sqWeightSpace W hb hx (2 * (m + 2) - 2 : ℤ)))
    rwa [show 2 * ((m : ℤ) + 2) + (K + n - (2 * ((m : ℤ) + 2) - 2) - 1) = K + n + 1 by ring] at this

/-- The homogeneous elements of the relation module. -/
def relHom : Set (𝒱E 𝒱) := {h | h ∈ blockRelSpanE W ∧ ∃ N, h ∈ akTotalWeightSpace W N}

theorem sq_mem_iSup (b : 𝒱) : b ∈ ⨆ m : ℕ, sqWeightSpace W ((m : ℕ) : ℂ) := by
  rw [sqWeightSpace_nat_spans_top]; trivial

theorem relS_mem_span (b x : 𝒱) : relS W b x ∈ Submodule.span ℂ (relHom W) := by
  induction sq_mem_iSup W b using Submodule.iSup_induction' generalizing x with
  | mem K b hb =>
      induction sq_mem_iSup W x using Submodule.iSup_induction' with
      | mem n x hx =>
          exact Submodule.subset_span ⟨relS_mem W b x, _,
            relS_homog W (K := K) (n := n) (by exact_mod_cast hb) (by exact_mod_cast hx)⟩
      | zero => rw [relS_zero_right]; exact Submodule.zero_mem _
      | add x x' _ _ h h' => rw [relS_add_right]; exact Submodule.add_mem _ h h'
  | zero => rw [relS_zero_left]; exact Submodule.zero_mem _
  | add b b' _ _ h h' => rw [relS_add_left]; exact Submodule.add_mem _ (h x) (h' x)

theorem relR_mem_span (b x : 𝒱) :
    ∃ K0 : ℕ, ∀ K, K0 ≤ K → relR W K b x ∈ Submodule.span ℂ (relHom W) := by
  induction sq_mem_iSup W b using Submodule.iSup_induction' generalizing x with
  | mem K b hb =>
      induction sq_mem_iSup W x using Submodule.iSup_induction' with
      | mem n x hx =>
          obtain ⟨K0, hK0⟩ := relR_mem W b x
          exact ⟨K0, fun L hL => Submodule.subset_span ⟨hK0 L hL, _,
            relR_homog W L (K := K) (n := n) (by exact_mod_cast hb) (by exact_mod_cast hx)⟩⟩
      | zero => exact ⟨0, fun L _ => by rw [relR_zero_right]; exact Submodule.zero_mem _⟩
      | add x x' _ _ h h' =>
          obtain ⟨K1, h1⟩ := h
          obtain ⟨K2, h2⟩ := h'
          exact ⟨max K1 K2, fun L hL => by
            rw [relR_add_right]
            exact Submodule.add_mem _ (h1 L (le_of_max_le_left hL)) (h2 L (le_of_max_le_right hL))⟩
  | zero => exact ⟨0, fun L _ => by rw [relR_zero_left]; exact Submodule.zero_mem _⟩
  | add b b' _ _ h h' =>
      obtain ⟨K1, h1⟩ := h x
      obtain ⟨K2, h2⟩ := h' x
      exact ⟨max K1 K2, fun L hL => by
        rw [relR_add_left]
        exact Submodule.add_mem _ (h1 L (le_of_max_le_left hL)) (h2 L (le_of_max_le_right hL))⟩

/-- A relation stabilises once its tail modes vanish. -/
theorem relR_stable {K : ℕ} {b x : 𝒱}
    (h : ∀ m : ℕ, K ≤ m → sqMode W (2 * (m + 1) - 2 : ℤ) b x = 0) :
    ∀ L, K ≤ L → relR W L b x = relR W K b x := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => rfl
  | succ L hL ih =>
      rw [← ih, relR, relR, Finset.sum_range_succ,
        show (2 * (((L : ℕ) : ℤ) + 2) - 2 : ℤ) = 2 * (((L + 1 : ℕ) : ℤ) + 1) - 2 by push_cast; ring,
        h (L + 1) (by omega), map_zero, smul_zero, add_zero]

/-- The `ℂ`-span of `E46`-multiples of homogeneous relations, by homogeneous coefficients. -/
def relHomE : Set (𝒱E 𝒱) :=
  {y | ∃ (k : ℤ) (e : E46) (h : 𝒱E 𝒱), e ∈ e46WeightSpace k ∧ h ∈ relHom W ∧ y = e • h}

theorem relHomE_homog : ∀ y ∈ relHomE W, ∃ i, y ∈ akTotalWeightSpace W i := by
  rintro _ ⟨k, e, h, he, ⟨-, N, hN⟩, rfl⟩
  exact ⟨k + N, e46Weight_smul_mem_akTotalWeightSpace W he hN⟩

theorem smul_mem_span_relHomE (e : E46) {y : 𝒱E 𝒱} (hy : y ∈ Submodule.span ℂ (relHomE W)) :
    e • y ∈ Submodule.span ℂ (relHomE W) := by
  have he : e ∈ ⨆ k, e46WeightSpace k := by rw [e46WeightSpace_iSup_eq_top]; trivial
  induction he using Submodule.iSup_induction' with
  | mem k e he =>
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨k', e', h, he', hh, rfl⟩ := hy
          rw [smul_smul]
          exact Submodule.subset_span ⟨k + k', e * e', h, E46Weight.mul he he', hh, rfl⟩
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h h' => rw [smul_add]; exact Submodule.add_mem _ h h'
      | smul c y _ h => rw [smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add e e' _ _ h h' => rw [add_smul]; exact Submodule.add_mem _ h h'

theorem relHom_le_span (y : 𝒱E 𝒱) (hy : y ∈ Submodule.span ℂ (relHom W)) :
    y ∈ Submodule.span ℂ (relHomE W) := by
  refine Submodule.span_le.mpr (fun h hh => ?_) hy
  exact Submodule.subset_span ⟨0, 1, h, E46Weight.one, hh, (one_smul _ _).symm⟩

/-- (C) **Zhu's relation module is homogeneous for the total weight.** -/
theorem blockRelSpanE_eq_span :
    (blockRelSpanE W).restrictScalars ℂ = Submodule.span ℂ (relHomE W) := by
  apply le_antisymm
  · -- the `E46`-submodule carried by the span
    let Q : Submodule E46 (𝒱E 𝒱) :=
      { toAddSubmonoid := (Submodule.span ℂ (relHomE W)).toAddSubmonoid
        smul_mem' := fun e y hy => smul_mem_span_relHomE W e hy }
    have hle : blockRelSpanE W ≤ Q := by
      refine Submodule.span_le.mpr ?_
      rintro y (⟨ka, a, v, hka, ha, rfl⟩ | ⟨ka, K, a, v, hka, ha, htail, rfl⟩)
      · have := relHom_le_span W _ (relS_mem_span W a v)
        rwa [relS, sqMode_of_mem_grading W ha] at this
      · obtain ⟨K0, hK0⟩ := relR_mem_span W a v
        have hstab := relR_stable W (K := K) (b := a) (x := v) (fun m hm => by
          rw [sqMode_of_mem_grading W ha]; exact htail m hm) (max K K0) (le_max_left _ _)
        have := relHom_le_span W _ (hK0 (max K K0) (le_max_right _ _))
        rw [hstab] at this
        simpa only [relR, sqMode_of_mem_grading W ha] using this
    intro y hy
    exact hle hy
  · rw [Submodule.span_le]
    rintro _ ⟨k, e, h, -, ⟨hh, -⟩, rfl⟩
    exact (blockRelSpanE W).smul_mem e hh

/-- **`AKWeightGrading` holds for every VOA.** -/
noncomputable def akWeightGrading : AKWeightGrading W where
  coeffDecomposition := e46Decomposition
  totalDecomposition := akTotalDecomposition W
  relationHomogeneous := by
    letI := akTotalDecomposition W
    rw [blockRelSpanE_eq_span]
    exact isHomogeneous_span _ (relHomE_homog W)

end VOA

section AxiomAudit
#print axioms VOA.akTotalWeightSpace_isInternal
#print axioms VOA.blockRelSpanE_eq_span
#print axioms VOA.akWeightGrading
end AxiomAudit
