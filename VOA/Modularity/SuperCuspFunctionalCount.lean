/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperZhuCommutator
import VOA.Modularity.SuperSymmetricFunctionals
import VOA.Modularity.SuperZhuAlgebraFinite
import VOA.Modularity.CuspPoint

/-!
# The integral super cusp quotient

For an integral-weight super VOA, the cusp relation quotient is canonically the
supercommutator quotient of its super Zhu algebra.  The nontrivial sign-sensitive inclusion is
`superZhuCommSpan_le_map_superCuspRelSpan`; this file proves the converse and packages the exact
linear equivalence needed by the super Arike--Nagatomo bound.

No rationality or semisimplicity hypothesis occurs.
-/

namespace VOA

open Module (finrank)
open GammaThetaStmt

set_option autoImplicit false

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-! ## Linearity in the left state -/

@[simp] theorem superVSqZ_zero_left (k : ℕ) (m : ℤ) (b : 𝒱) :
    V.superVSqZ 0 k m b = 0 := by
  rw [V.superVSqZ_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [SuperVertexAlgebra.smul_zero_left, smul_zero]

theorem superVSqZ_add_left (a₁ a₂ : 𝒱) (k : ℕ) (m : ℤ) (b : 𝒱) :
    V.superVSqZ (a₁ + a₂) k m b = V.superVSqZ a₁ k m b + V.superVSqZ a₂ k m b := by
  rw [V.superVSqZ_apply, V.superVSqZ_apply, V.superVSqZ_apply]
  simp only [SuperVertexAlgebra.smul_add_left, smul_add]
  rw [finsum_add_distrib (V.superSqModeZ_support_finite a₁ k m b)
    (V.superSqModeZ_support_finite a₂ k m b)]

theorem superVSqZ_sum_left {ι : Type v} (s : Finset ι) (a : ι → 𝒱)
    (k : ℕ) (m : ℤ) (b : 𝒱) :
    V.superVSqZ (∑ i ∈ s, a i) k m b = ∑ i ∈ s, V.superVSqZ (a i) k m b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, V.superVSqZ_add_left, ih, Finset.sum_insert hi]

/-! ## The image of the cusp relation -/

/-- The square-bracket zero mode of a positive-weight state maps to the supercommutator span.
The proof explicitly decomposes the left state by parity and the right state by weight and
parity, so the Koszul sign is attached only to genuinely homogeneous pairs. -/
theorem superMk_superVSqZ_zero_mem_superZhuCommSpan
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    {K : ℕ} (hK : 1 ≤ K) {a : 𝒱}
    (haK : a ∈ W.toSuperNearVOA.gradingZ (K : ℤ)) (b : 𝒱) :
    let hZ := W.superZhuRingData hV
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    W.toSuperNearVOA.superMk hV (W.toSuperNearVOA.superVSqZ a K 0 b)
      ∈ hZ.superZhuCommSpan := by
  classical
  let V := W.toSuperNearVOA
  let hZ := W.superZhuRingData hV
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  obtain ⟨s, hs, -⟩ := V.exists_sum_parProj a
  rw [← hs, V.superVSqZ_sum_left, map_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hap : V.parProj p a ∈ V.parity p := V.parProj_mem p a
  have haKp : V.parProj p a ∈ V.gradingZ (K : ℤ) := by
    exact V.parProj_mem_grading p haK
  refine V.reduce_bihomogeneous hV
    (P := fun v => V.superMk hV (V.superVSqZ (V.parProj p a) K 0 v)
      ∈ hZ.superZhuCommSpan) ?_ ?_ ?_ b
  · intro M q v hv
    rw [Submodule.mem_inf] at hv
    rcases lt_or_ge M 0 with hM | hM
    · have hv0 : v = 0 := by
        have hbot := W.gradingZ_neg_eq_bot M hM
        rw [hbot, Submodule.mem_bot] at hv
        exact hv.1
      subst v
      simp
    · have hvM : v ∈ V.gradingZ ((M.toNat : ℕ) : ℤ) := by
        simpa [show ((M.toNat : ℕ) : ℤ) = M from by omega] using hv.1
      have hcomm := V.superZhu_comm_mod_superO hV hK haKp hap hvM hv.2
      have hzero : V.superMk hV
          (V.superZhuMul hV (V.parProj p a) v
            - koszul p q • V.superZhuMul hV v (V.parProj p a)
            - V.superVSqZ (V.parProj p a) K 0 v) = 0 :=
        (V.superMk_eq_zero_iff hV).2 hcomm
      rw [map_sub, map_sub, map_smul, sub_eq_zero] at hzero
      rw [← hzero, ← hZ.superAmul_mk, ← hZ.superAmul_mk,
        ← hZ.AsRing_mul_eq, ← hZ.AsRing_mul_eq]
      exact mul_sub_koszul_smul_mul_mem_superCommSpan
        hZ.superAAssociativeSuperalgebra
        (V.superMk_mem_superAParity hV hap)
        (V.superMk_mem_superAParity hV hv.2)
  · simp
  · intro x y hx hy
    simpa only [map_add] using Submodule.add_mem hZ.superZhuCommSpan hx hy

/-- The image of the intrinsic cusp relation space is exactly the homogeneous
supercommutator span of the super Zhu algebra. -/
theorem map_superMk_superCuspRelSpan_eq_superZhuCommSpan
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights) :
    let hZ := W.superZhuRingData hV
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    Submodule.map (W.toSuperNearVOA.superMk hV)
        (W.toSuperNearVOA.superCuspRelSpan hV)
      = hZ.superZhuCommSpan := by
  classical
  let V := W.toSuperNearVOA
  let hZ := W.superZhuRingData hV
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · intro x hx
      change V.superMk hV x ∈ hZ.superZhuCommSpan
      have hx0 : V.superMk hV x = 0 := (V.superMk_eq_zero_iff hV).2 hx
      rw [hx0]
      exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨K, a, b, hK, haK, rfl⟩
      exact superMk_superVSqZ_zero_mem_superZhuCommSpan W hV hK haK b
  · exact superZhuCommSpan_le_map_superCuspRelSpan W hV hZ

/-! ## Quotient equivalence and finite cusp families -/

/-- The cusp quotient is canonically the supercommutator quotient of the super Zhu algebra. -/
noncomputable def superCuspRelSpanQuotEquiv
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights) :
    let hZ := W.superZhuRingData hV
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    (𝒱 ⧸ W.toSuperNearVOA.superCuspRelSpan hV) ≃ₗ[ℂ]
      W.toSuperNearVOA.superA hV ⧸ hZ.superZhuCommSpan := by
  let V := W.toSuperNearVOA
  let hZ := W.superZhuRingData hV
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  have hker : V.superCuspRelSpan hV ≤
      LinearMap.ker ((hZ.superZhuCommSpan).mkQ.comp (V.superMk hV)) := by
    intro x hx
    change hZ.superZhuCommSpan.mkQ (V.superMk hV x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← map_superMk_superCuspRelSpan_eq_superZhuCommSpan W hV]
    exact ⟨x, hx, rfl⟩
  refine LinearEquiv.ofBijective
    (Submodule.liftQ _ (hZ.superZhuCommSpan.mkQ.comp (V.superMk hV)) hker) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := (V.superCuspRelSpan hV).mkQ_surjective q
    have hx : hZ.superZhuCommSpan.mkQ (V.superMk hV x) = 0 := hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← map_superMk_superCuspRelSpan_eq_superZhuCommSpan W hV] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hdiff : x - y ∈ V.superO hV := by
      rw [← V.superMk_eq_zero_iff hV, map_sub, hxy, sub_self]
    have hxmem : x ∈ V.superCuspRelSpan hV := by
      have hadd := (V.superCuspRelSpan hV).add_mem
        (superO_le_superCuspRelSpan hdiff) hy
      simpa using hadd
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hxmem
  · intro q
    obtain ⟨p, rfl⟩ := hZ.superZhuCommSpan.mkQ_surjective q
    obtain ⟨x, rfl⟩ := V.superMk_surjective hV p
    exact ⟨(V.superCuspRelSpan hV).mkQ x, rfl⟩

theorem finrank_quot_superCuspRelSpan_eq
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights) :
    let hZ := W.superZhuRingData hV
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    finrank ℂ (𝒱 ⧸ W.toSuperNearVOA.superCuspRelSpan hV) =
      finrank ℂ (W.toSuperNearVOA.superA hV ⧸ hZ.superZhuCommSpan) :=
  (superCuspRelSpanQuotEquiv W hV).finrank_eq

/-- The same equivalence stated directly for the specialized analytic relation space at the
cusp. -/
noncomputable def superBlockRelSpanAtCuspQuotEquiv
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights) :
    let hZ := W.superZhuRingData hV
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    (𝒱 ⧸ W.toSuperNearVOA.superBlockRelSpanAtCusp) ≃ₗ[ℂ]
      W.toSuperNearVOA.superA hV ⧸ hZ.superZhuCommSpan := by
  rw [superBlockRelSpanAtCusp_eq_superCuspRelSpan W hV]
  exact superCuspRelSpanQuotEquiv W hV

theorem finrank_quot_superBlockRelSpanAtCusp_eq
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights) :
    let hZ := W.superZhuRingData hV
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    finrank ℂ (𝒱 ⧸ W.toSuperNearVOA.superBlockRelSpanAtCusp) =
      finrank ℂ (W.toSuperNearVOA.superA hV ⧸ hZ.superZhuCommSpan) :=
  (superBlockRelSpanAtCuspQuotEquiv W hV).finrank_eq

/-- `C₂`-cofiniteness produces a cusp-spanning family whose cardinality is bounded sharply by
the supercommutator quotient. -/
theorem exists_finset_span_sup_superBlockRelSpanAtCusp
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    ∃ T : Finset 𝒱,
      T.card ≤ (let hZ := W.superZhuRingData hV
        letI := hZ.AsRing
        letI := hZ.AsAlgebra
        finrank ℂ (W.toSuperNearVOA.superA hV ⧸ hZ.superZhuCommSpan)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔
        W.toSuperNearVOA.superBlockRelSpanAtCusp := by
  let hZ := W.superZhuRingData hV
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  haveI : FiniteDimensional ℂ (W.toSuperNearVOA.superA hV) :=
    finiteDimensional_superA_of_superC2Cofinite W hV hC2
  haveI : FiniteDimensional ℂ (𝒱 ⧸ W.toSuperNearVOA.superCuspRelSpan hV) :=
    (superCuspRelSpanQuotEquiv W hV).symm.finiteDimensional
  rw [superBlockRelSpanAtCusp_eq_superCuspRelSpan W hV]
  exact exists_finset_card_le_span_sup_eq_top
    (le_of_eq (finrank_quot_superCuspRelSpan_eq W hV))

end SuperNearVOA

end VOA
