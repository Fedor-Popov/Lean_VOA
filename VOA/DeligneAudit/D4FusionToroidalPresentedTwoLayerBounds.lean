import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerSpanEq

/-! Rank bounds reduced to the explicit positive span and the quadratic seed. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def twoPositiveToLayer : twoPositiveSpan →ₗ[ℂ]
    ((twoN 1) ⧸ twoN2inN1) :=
  (twoN2inN1).mkQ.comp (Submodule.inclusion twoPositiveSpan_le_N1)

theorem twoPositiveToLayer_surjective : Function.Surjective twoPositiveToLayer := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective twoN2inN1 q
  have hx : (x : PTE 2) ∈ twoN 2 ⊔ twoPositiveSpan := by
    rw [← twoN_one_eq_two_generators]
    exact x.property
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  let a₁ : twoN 1 := ⟨a, twoN_mono (by omega) ha⟩
  let b₁ : twoN 1 := ⟨b, twoPositiveSpan_le_N1 hb⟩
  have hxb : x = a₁ + b₁ := Subtype.ext hab.symm
  refine ⟨⟨b, hb⟩, ?_⟩
  change (twoN2inN1).mkQ b₁ = (twoN2inN1).mkQ x
  rw [hxb, map_add]
  have ha₁ : a₁ ∈ twoN2inN1 := ha
  have ha0 : (twoN2inN1).mkQ a₁ = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ha₁
  rw [ha0]
  simp

def TwoPositiveSpanBound : Prop :=
  FiniteDimensional ℂ twoPositiveSpan ∧ Module.finrank ℂ twoPositiveSpan ≤ 56

theorem two_first_layer_bound_of_span (h : TwoPositiveSpanBound) :
    FiniteDimensional ℂ ((twoN 1) ⧸ twoN2inN1) ∧
      Module.finrank ℂ ((twoN 1) ⧸ twoN2inN1) ≤ 56 := by
  letI : FiniteDimensional ℂ twoPositiveSpan := h.1
  letI : FiniteDimensional ℂ ((twoN 1) ⧸ twoN2inN1) :=
    Module.Finite.of_surjective twoPositiveToLayer twoPositiveToLayer_surjective
  exact ⟨inferInstance,
    (LinearMap.finrank_le_finrank_of_surjective twoPositiveToLayer_surjective).trans h.2⟩

def twoQuadraticSeed : PTE 2 :=
  (ρPTE 2).op D4sector.c₀ 1 0
    ((ρPTE 2).op D4sector.c₀ 1 0 (pTE 2))

def TwoUTwoCollapse : Prop :=
  twoN 2 ≤ Submodule.span ℂ {twoQuadraticSeed}

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoPositiveToLayer_surjective
#print axioms VOA.DeligneAudit.Toroidal.two_first_layer_bound_of_span
