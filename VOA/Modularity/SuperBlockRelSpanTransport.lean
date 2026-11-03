/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperBlockRelSpanE
import VOA.Modularity.BlockRelSpanTransport

/-!
# Nakayama transport for integral-weight super block relations

An arbitrary finite family spanning the super state space modulo the specialized cusp relations
spans it modulo the analytic relations at some point of the upper half-plane.  The family itself
is unchanged, so its cardinality is preserved exactly.

This theorem is independent of the interpretation of the cusp quotient.  Once the signed super
Zhu commutator congruence supplies a cusp family whose cardinality is bounded by the
supercommutator quotient, the final analytic bound follows immediately from
`finrank_superAnalyticBlocks_le_card_of_cusp_span` below.

## Main results

* `evalAt_mem_superBlockRelSpan`;
* `ιE_mem_sup_cuspIdeal_smul_of_mem_superBlockRelSpanAtCusp`;
* `exists_interior_span_sup_superBlockRelSpan_of_cusp`;
* `finrank_superAnalyticBlocks_le_card_of_cusp_span`;
* `finrank_superAnalyticBlocks_le_of_exists_cusp_span`.
-/

namespace VOA

open scoped BigOperators TensorProduct Topology
open ModularForm UpperHalfPlane Filter Module
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-- Specialization at an interior point carries the `E46` super relation module into the
corresponding complex relation space. -/
theorem evalAt_mem_superBlockRelSpan (z0 : UpperHalfPlane) {x : 𝒱E 𝒱}
    (hx : x ∈ V.superBlockRelSpanE) :
    blockEvalAt z0 x ∈ V.superBlockRelSpan (z0 : ℂ) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨k, a, v, hk, ha, rfl⟩ | ⟨k, K, a, v, hk, ha, hK, rfl⟩
      · rw [evalAt_ιE]
        exact Submodule.subset_span (Or.inl ⟨k, a, v, hk, ha, rfl⟩)
      · rw [map_add, evalAt_ιE, map_sum]
        have hcong : ∀ m ∈ Finset.range K,
            blockEvalAt z0
                (coefE m • (ιE (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱))
              = (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) (z0 : ℂ))
                • V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v := by
          intro m _
          rw [evalAt_smul, evalAt_ιE, evAt_coefE]
        rw [Finset.sum_congr rfl hcong]
        exact Submodule.subset_span (Or.inr ⟨k, K, a, v, hk, ha, hK, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [evalAt_smul]
      exact Submodule.smul_mem _ _ hx

/-- At the cusp, the specialized and `E46` relation generators differ by coefficients in the
cusp ideal. -/
theorem ιE_mem_sup_cuspIdeal_smul_of_mem_superBlockRelSpanAtCusp {x : 𝒱}
    (hx : x ∈ V.superBlockRelSpanAtCusp) :
    (ιE x : 𝒱E 𝒱) ∈
      V.superBlockRelSpanE ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨k, a, v, hk, ha, rfl⟩ | ⟨k, K, a, v, hk, ha, hK, rfl⟩
      · exact Submodule.mem_sup_left
          (Submodule.subset_span (Or.inl ⟨k, a, v, hk, ha, rfl⟩))
      · set G : 𝒱E 𝒱 := (ιE (V.superVSqZ a k (-2) v) : 𝒱E 𝒱)
          + ∑ m ∈ Finset.range K,
            coefE m • (ιE (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱)
        with hG
        have hGmem : G ∈ V.superBlockRelSpanE :=
          Submodule.subset_span (Or.inr ⟨k, K, a, v, hk, ha, hK, rfl⟩)
        have hdiff : (ιE (V.superVSqZ a k (-2) v + ∑ m ∈ Finset.range K,
              (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
                • V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱)
            = G + ∑ m ∈ Finset.range K,
              ((algebraMap ℂ (↥E46)
                  (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)) - coefE m)
                • (ιE (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱) := by
          rw [hG, map_add, map_sum, add_assoc, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_smul, ← algebraMap_smul (↥E46)
            (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0), sub_smul]
          abel
        rw [hdiff]
        refine Submodule.add_mem _ (Submodule.mem_sup_left hGmem) (Submodule.mem_sup_right ?_)
        refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [mem_cuspIdeal, map_sub, AlgHom.commutes, coefE, map_smul, smul_eq_mul,
          evInfty_zhuGE]
        simp
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      rw [map_smul, ← algebraMap_smul (↥E46) c]
      exact Submodule.smul_mem _ _ hx

set_option maxHeartbeats 1600000 in
-- The base-changed Nakayama argument expands several nested submodule maps and quotients.
/-- A cusp-spanning family spans at some interior point, with no change of family or cardinality.
-/
theorem exists_interior_span_sup_superBlockRelSpan_of_cusp
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) (T : Set 𝒱)
    (hT : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ T ⊔ W.toSuperNearVOA.superBlockRelSpanAtCusp) :
    ∃ z0 : UpperHalfPlane, (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ T ⊔ W.toSuperNearVOA.superBlockRelSpan (z0 : ℂ) := by
  classical
  let V := W.toSuperNearVOA
  set N : Submodule (↥E46) (𝒱E 𝒱) :=
    Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' T) ⊔ V.superBlockRelSpanE
  have hleN : V.superBlockRelSpanE ≤ N := le_sup_right
  haveI : Module.Finite (↥E46) ((𝒱E 𝒱) ⧸ V.superBlockRelSpanE) :=
    moduleFinite_quot_superBlockRelSpanE W hW hC2
  have hcomap : V.superBlockRelSpanE ≤
      Submodule.comap (LinearMap.id : 𝒱E 𝒱 →ₗ[↥E46] 𝒱E 𝒱) N := hleN
  haveI : Module.Finite (↥E46) ((𝒱E 𝒱) ⧸ N) := by
    refine Module.Finite.of_surjective
      (Submodule.mapQ V.superBlockRelSpanE N LinearMap.id hcomap) ?_
    intro y
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    exact ⟨V.superBlockRelSpanE.mkQ x, rfl⟩
  have hsp : Submodule.span (↥E46) (Set.range (ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱))
      ≤ N ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ T ⊔ V.superBlockRelSpanAtCusp := by
      rw [← hT]
      trivial
    obtain ⟨t, ht, g, hg, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_left (ιE_mem_span_image_of_mem_span T ht))
    · rcases Submodule.mem_sup.mp
        (V.ιE_mem_sup_cuspIdeal_smul_of_mem_superBlockRelSpanAtCusp hg) with
        ⟨u, hu, w, hw, hsum⟩
      rw [← hsum]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_right hu))
        (Submodule.mem_sup_right hw)
  have htopN : (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      ≤ N ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) :=
    le_trans (le_of_eq (span_range_ιE_eq_top (𝒱 := 𝒱)).symm) hsp
  have hquot : (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N))
      ≤ cuspIdeal • (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N)) := by
    have hmap : Submodule.map N.mkQ
        (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱)))
        = cuspIdeal • (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N)) := by
      rw [Submodule.map_smul'', Submodule.map_top, N.range_mkQ]
    rintro y -
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    have hx : x ∈ N ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) :=
      htopN Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    have hu0 : N.mkQ u = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hu
    rw [map_add, hu0, zero_add, ← hmap]
    exact Submodule.mem_map_of_mem hw
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    cuspIdeal (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N))
      (Module.finite_def.mp inferInstance) hquot
  have hev : evInfty r = 1 := by
    have hr := (mem_cuspIdeal).mp hr1
    rw [map_sub, map_one, sub_eq_zero] at hr
    exact hr
  have htend : Tendsto ((r : UpperHalfPlane → ℂ)) atImInfty (𝓝 (evInfty r)) := by
    have hr := tendsto_of_mem_E46 r.2
    rwa [show valueAtInfty ((r : UpperHalfPlane → ℂ)) = evInfty r from rfl] at hr
  have hne : ∀ᶠ z in atImInfty, ((r : UpperHalfPlane → ℂ)) z ≠ 0 := by
    refine htend.eventually_ne ?_
    rw [hev]
    exact one_ne_zero
  obtain ⟨z0, hz0⟩ := hne.exists
  refine ⟨z0, le_antisymm ?_ le_top⟩
  intro v _
  have hrv : r • (ιE v : 𝒱E 𝒱) ∈ N := by
    have hzero : N.mkQ (r • (ιE v : 𝒱E 𝒱)) = 0 := by
      rw [map_smul]
      exact hr0 _ Submodule.mem_top
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
  have hspec : blockEvalAt z0 (r • (ιE v : 𝒱E 𝒱))
      ∈ Submodule.span ℂ T ⊔ V.superBlockRelSpan (z0 : ℂ) := by
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp hrv
    rw [← hsum, map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (evalAt_mem_span_image z0 T hu))
      (Submodule.mem_sup_right (V.evalAt_mem_superBlockRelSpan z0 hw))
  rw [evalAt_smul, evalAt_ιE] at hspec
  have hrz : evAt z0 r ≠ 0 := hz0
  have hscaled := Submodule.smul_mem
    (Submodule.span ℂ T ⊔ V.superBlockRelSpan (z0 : ℂ)) (evAt z0 r)⁻¹ hspec
  rwa [smul_smul, inv_mul_cancel₀ hrz, one_smul] at hscaled

/-- A finite cusp-spanning family gives the analytic block bound with the same cardinality. -/
theorem finrank_superAnalyticBlocks_le_card_of_cusp_span
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) (T : Finset 𝒱)
    (hT : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱)
      ⊔ W.toSuperNearVOA.superBlockRelSpanAtCusp) :
    FiniteDimensional ℂ
        (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks) ∧
      finrank ℂ (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks) ≤ T.card := by
  obtain ⟨z0, hz0⟩ :=
    exists_interior_span_sup_superBlockRelSpan_of_cusp W hW hC2 (T : Set 𝒱) hT
  exact finrank_superAnalyticBlocks_le_card_of_superBlockRel (coe_mem_imGT_zero z0) T hz0

/-- Cardinality-only feeder: any cusp family of size at most `n` bounds the analytic block space
by `n`. -/
theorem finrank_superAnalyticBlocks_le_of_exists_cusp_span
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) {n : ℕ}
    (hex : ∃ T : Finset 𝒱, T.card ≤ n ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱)
        ⊔ W.toSuperNearVOA.superBlockRelSpanAtCusp) :
    FiniteDimensional ℂ
        (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks) ∧
      finrank ℂ (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks) ≤ n := by
  obtain ⟨T, hcard, hT⟩ := hex
  obtain ⟨hfd, hle⟩ := finrank_superAnalyticBlocks_le_card_of_cusp_span W hW hC2 T hT
  exact ⟨hfd, hle.trans hcard⟩

end SuperNearVOA

end VOA
