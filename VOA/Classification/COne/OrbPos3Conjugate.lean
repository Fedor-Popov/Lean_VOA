import VOA.Classification.COne.OrbPos2Sectors

/-!
# Conjugating actual twisted modules

Precomposition of every fractional field with an inverse VOA automorphism
preserves the full twisted Jacobi identity, the conformal weights, and
irreducibility. This is independent of Li's still-missing twist construction.
-/

namespace VOA.Classification.COne.OrbPos3
open VOA OrbPos2

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {g : Aut W} {n : ℕ}

theorem inverse_mem_twistedEigenspace (φ : Aut W) (j : ℕ) {v : V}
    (hv : v ∈ (φ * g * φ⁻¹).twistedEigenspace n j) :
    φ⁻¹ v ∈ g.twistedEigenspace n j := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff] at hv ⊢
  change (φ * g * φ⁻¹) v = _ at hv
  have h := congrArg φ.toLinearEquiv.symm hv
  simpa only [Aut.mul_apply, Aut.inv_apply, LinearEquiv.symm_apply_apply, map_smul] using h

/-- Conjugation transport with all fractional fields and the original grading. -/
noncomputable def conjugateTwisted (P : TwistedModule g n M) (φ : Aut W) :
    TwistedModule (φ * g * φ⁻¹) n M where
  YM := P.YM.comp (φ⁻¹).toLinearEquiv.toLinearMap
  vacuum_YM := by
    intro k
    change P.YM ((φ⁻¹).toLinearEquiv W.vacuum) k = _
    rw [(φ⁻¹).map_vacuum]
    exact P.vacuum_YM k
  truncation := fun v x => P.truncation (φ⁻¹ v) x
  support := fun j v hv k hk => P.support j (φ⁻¹ v)
    (inverse_mem_twistedEigenspace φ j hv) k hk
  jacobi := by
    intro j v hv w x ℓ k m hk
    have h := P.jacobi j (φ⁻¹ v) (inverse_mem_twistedEigenspace φ j hv)
      (φ⁻¹ w) x ℓ k m hk
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, (φ⁻¹).map_smul'] using h
  weight := P.weight
  isInternal := P.isInternal
  L0_weight := by
    intro α x hx
    change P.YM ((φ⁻¹).toLinearEquiv W.conformalVector) n x = α • x
    rw [(φ⁻¹).map_omega]
    exact P.L0_weight α x hx
  finrank := P.finrank
  boundedBelow := P.boundedBelow

theorem conjugateTwisted_weight (P : TwistedModule g n M) (φ : Aut W) (α : ℂ) :
    (conjugateTwisted P φ).weight α = P.weight α := rfl

theorem conjugateTwisted_irreducible (P : TwistedModule g n M) (φ : Aut W)
    (hi : TwistedIrreducible P) : TwistedIrreducible (conjugateTwisted P φ) := by
  refine ⟨hi.1, fun S hS => hi.2 S ?_⟩
  intro v k x hx
  have h := hS (φ v) k x hx
  change P.YM (φ.toLinearEquiv.symm (φ.toLinearEquiv v)) k x ∈ S at h
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- Every finite-order V₂ sector can be transported to an actual torus sector,
with exactly the same weight spaces on the same vector space. -/
theorem v2_twisted_torus_reduction
    {g : Aut (V2m 1 le_rfl)} {n : ℕ} (hn : 0 < n) (ho : orderOf g = n)
    {M : Type} [AddCommGroup M] [Module ℂ M] (P : TwistedModule g n M)
    (hi : TwistedIrreducible P) :
    ∃ (u : ℂˣ) (Q : TwistedModule (charU 1 le_rfl u) n M),
      orderOf (charU 1 le_rfl u) = n ∧
      TwistedIrreducible Q ∧ ∀ α, Q.weight α = P.weight α := by
  have hex : ∃ (φ : Aut (V2m 1 le_rfl)) (z : ℂˣ),
      φ * g * φ⁻¹ = charU 1 le_rfl z :=
    exists_conj_charU g (orderOf_pos_iff.mp (ho.symm ▸ hn))
  obtain ⟨φ, z, hz⟩ := hex
  have ho' : orderOf (φ * g * φ⁻¹) = n := by
    calc
      _ = orderOf g := (MulAut.conj φ).orderOf_eq g
      _ = n := ho
  refine ⟨z, ?_⟩
  rw [← hz]
  exact ⟨conjugateTwisted P φ, ho', conjugateTwisted_irreducible P φ hi,
    conjugateTwisted_weight P φ⟩

end VOA.Classification.COne.OrbPos3
