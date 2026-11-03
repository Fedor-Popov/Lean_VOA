/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LevelOneStructure
import VOA.Modularity.CuspLimit

/-!
# The cusp as a `ℂ`-point of the coefficient algebra, and lifting quotient bases

With `Modularity.LevelOneStructure` the block-relation coefficients all lie in the finitely
generated `ℂ`-algebra `E46 = ℂ⟨E₄, E₆⟩`.  Route (i) to Zhu's Theorem 5.3.3 then needs two
structural facts, banked here:

* **the cusp is a `ℂ`-point of `E46`** — every element of `E46` has a limit along `atImInfty`, and
  taking that limit is a `ℂ`-algebra homomorphism `evInfty : E46 →ₐ[ℂ] ℂ` sending `G_{2j}` to
  `zhuG j 0`.  (Contrast `FormalSpecialization`: over `ℂ⟦q⟧` there is no such hom at a point of
  `ℍ`; over a finitely generated algebra of *functions* every point of `ℍ` — and the cusp — is one.)
* **lifting a quotient basis** — `dim (𝒱 ⧸ K) ≤ n` produces a finite `T` with `#T ≤ n` and
  `⊤ = span T ⊔ K`, which is the exact input shape of
  `finrank_analyticBlocks_le_card_of_blockRel`.

## Main results

* `cuspLimSubalg`, `E46_le_cuspLimSubalg`, `tendsto_of_mem_E46`;
* `evInfty : E46 →ₐ[ℂ] ℂ`, `evInfty_E4`, `evInfty_E6`, `evInfty_zhuGC`;
* `exists_finset_card_le_span_sup_eq_top`;
* `exists_finset_span_sup_blockRelSpanAtCusp` — the cusp fibre as a spanning set.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open ModularForm UpperHalfPlane Filter Module
open scoped MatrixGroups Topology

/-! ## The cusp as a `ℂ`-point -/

/-- Functions on `ℍ` that have a limit at the cusp. -/
noncomputable def cuspLimSubalg : Subalgebra ℂ (UpperHalfPlane → ℂ) where
  carrier := {f : UpperHalfPlane → ℂ | ∃ L : ℂ, Tendsto f atImInfty (𝓝 L)}
  mul_mem' := fun ⟨L₁, h₁⟩ ⟨L₂, h₂⟩ => ⟨L₁ * L₂, h₁.mul h₂⟩
  add_mem' := fun ⟨L₁, h₁⟩ ⟨L₂, h₂⟩ => ⟨L₁ + L₂, h₁.add h₂⟩
  zero_mem' := ⟨0, tendsto_const_nhds⟩
  one_mem' := ⟨1, tendsto_const_nhds⟩
  algebraMap_mem' := fun c => ⟨c, tendsto_const_nhds⟩

theorem E46_le_cuspLimSubalg : E46 ≤ cuspLimSubalg := by
  rw [E46, Algebra.adjoin_le_iff]
  rintro f (rfl | hf)
  · exact ⟨_, tendsto_modularForm_atImInfty ModularForm.E₄⟩
  · rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨_, tendsto_modularForm_atImInfty ModularForm.E₆⟩

/-- Every element of `E46` converges at the cusp, to its `valueAtInfty`. -/
theorem tendsto_of_mem_E46 {f : UpperHalfPlane → ℂ} (hf : f ∈ E46) :
    Tendsto f atImInfty (𝓝 (valueAtInfty f)) := by
  obtain ⟨L, hL⟩ := E46_le_cuspLimSubalg hf
  rw [show valueAtInfty f = L from hL.limUnder_eq]
  exact hL

/-- **The cusp, as a `ℂ`-point of the coefficient algebra.** -/
noncomputable def evInfty : E46 →ₐ[ℂ] ℂ where
  toFun f := valueAtInfty (f : UpperHalfPlane → ℂ)
  map_one' := tendsto_nhds_unique (tendsto_of_mem_E46 (one_mem E46)) tendsto_const_nhds
  map_mul' f g := tendsto_nhds_unique (tendsto_of_mem_E46 (mul_mem f.2 g.2))
    ((tendsto_of_mem_E46 f.2).mul (tendsto_of_mem_E46 g.2))
  map_zero' := tendsto_nhds_unique (tendsto_of_mem_E46 (zero_mem E46)) tendsto_const_nhds
  map_add' f g := tendsto_nhds_unique (tendsto_of_mem_E46 (add_mem f.2 g.2))
    ((tendsto_of_mem_E46 f.2).add (tendsto_of_mem_E46 g.2))
  commutes' c := tendsto_nhds_unique
    (tendsto_of_mem_E46 (E46.algebraMap_mem c)) tendsto_const_nhds

@[simp] theorem evInfty_apply (f : E46) : evInfty f = valueAtInfty (f : UpperHalfPlane → ℂ) := rfl

theorem evInfty_E4 : evInfty ⟨_, E4_mem_E46⟩ = 1 := valueAtInfty_E (by norm_num) (by decide)

theorem evInfty_E6 : evInfty ⟨_, E6_mem_E46⟩ = 1 := valueAtInfty_E (by norm_num) (by decide)

/-- **The cusp point sends `G_{2j}` to its constant term** — the `q → 0` specialisation of the
block relations is evaluation of `E46` at this point. -/
theorem evInfty_zhuGC {j : ℕ} (hj : 2 ≤ j) :
    evInfty ⟨_, zhuGC_mem_E46 hj⟩ = zhuG j 0 :=
  (tendsto_zhuGC_atImInfty hj).limUnder_eq

/-! ## Lifting a quotient basis to a spanning family -/

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **From a quotient dimension bound to a spanning family.**  If `dim (𝒱 ⧸ K) ≤ n`, there is a
finite `T` with `#T ≤ n` and `⊤ = span T ⊔ K` — the input shape of
`finrank_analyticBlocks_le_card_of_blockRel`. -/
theorem exists_finset_card_le_span_sup_eq_top {K : Submodule ℂ 𝒱}
    [FiniteDimensional ℂ (𝒱 ⧸ K)] {n : ℕ} (hn : finrank ℂ (𝒱 ⧸ K) ≤ n) :
    ∃ T : Finset 𝒱, T.card ≤ n ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ K := by
  classical
  set b := Module.finBasis ℂ (𝒱 ⧸ K) with hb
  choose lift hlift using fun i => K.mkQ_surjective (b i)
  refine ⟨Finset.image lift Finset.univ, ?_, ?_⟩
  · calc (Finset.image lift Finset.univ).card
        ≤ (Finset.univ : Finset (Fin (finrank ℂ (𝒱 ⧸ K)))).card := Finset.card_image_le
      _ = finrank ℂ (𝒱 ⧸ K) := by simp
      _ ≤ n := hn
  · refine le_antisymm ?_ le_top
    intro x _
    set y : 𝒱 := ∑ i, (b.repr (K.mkQ x) i) • lift i with hy
    have hymk : K.mkQ y = K.mkQ x := by
      rw [hy, map_sum]
      simp_rw [map_smul, hlift]
      exact b.sum_repr (K.mkQ x)
    have hmem : x - y ∈ K := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hymk, sub_self]
    have hyspan : y ∈ Submodule.span ℂ ((Finset.image lift Finset.univ : Finset 𝒱) : Set 𝒱) := by
      rw [hy]
      refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      simp
    have hsplit : x = y + (x - y) := by abel
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hyspan) (Submodule.mem_sup_right hmem)

/-! ## The cusp fibre as a spanning family -/

section CuspSpan

variable {W : VertexOperatorAlgebra 𝒱}

/-- The cusp fibre is finite-dimensional as soon as `A(𝒱)` is. -/
theorem finiteDimensional_quot_blockRelSpanAtCusp
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W)) :
    FiniteDimensional ℂ (𝒱 ⧸ blockRelSpanAtCusp W) := by
  have hzero : VacuumGradeZero W := vacuumGradeZero_holds W
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  rw [blockRelSpanAtCusp_eq_cuspRelSpan]
  exact (cuspRelSpanQuotEquiv hzero).symm.finiteDimensional

/-- **The cusp fibre, as a spanning family**: `𝒱` is spanned modulo the `q → 0` relation space
by `dim A(𝒱)/[A(𝒱),A(𝒱)]` vectors — exactly the input shape of
`finrank_analyticBlocks_le_card_of_blockRel`, at the cusp. -/
theorem exists_finset_span_sup_blockRelSpanAtCusp
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W)) :
    ∃ T : Finset 𝒱,
      T.card ≤ (letI := instRingA W; letI := instAlgebraA W;
        finrank ℂ (A W ⧸ commSpan ℂ (A W))) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ blockRelSpanAtCusp W := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  haveI := finiteDimensional_quot_blockRelSpanAtCusp hfd
  exact exists_finset_card_le_span_sup_eq_top
    (le_of_eq (finrank_quot_blockRelSpanAtCusp_eq))

/-- Artin–Wedderburn form: the spanning family has `#(Wedderburn factors)` members. -/
theorem exists_finset_span_sup_blockRelSpanAtCusp_wedderburn
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    {n : ℕ} {d : Fin n → ℕ} (hd : ∀ i, NeZero (d i))
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ T : Finset 𝒱, T.card ≤ n ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ blockRelSpanAtCusp W := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  haveI := finiteDimensional_quot_blockRelSpanAtCusp hfd
  refine exists_finset_card_le_span_sup_eq_top (le_of_eq ?_)
  rw [finrank_quot_blockRelSpanAtCusp_eq]
  exact finrank_quot_commSpan_eq_of_algEquiv_pi_matrix hd e

end CuspSpan

end VOA
