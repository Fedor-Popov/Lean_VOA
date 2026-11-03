/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelationAffine
import VOA.DeligneAudit.DeligneCarrierData

/-!
# The vacuum quartic relation from the type data (any Deligne type)

The per-type input of the MLDE route, reduced to the carrier data constructed for each
type:

* a `LieData` `D` in the certificate basis (`Fin CD.n`) and a level `k` with `c = -2(h∨+1)`;
* The `DeligneCarrierData CD` (relations of `I₂ⁿˢ`, Casimir, **U3**);
* the Casimir match `casPoly D = c₀ · Q_CD` (`c₀ ≠ 0`), checkable entrywise by
  `quadraticRelation_eq_of_symm` (no expansion of a `dim²` sum);
* vanishing square symbols of the relations: `sym_singular` for the highest ones (singular vectors
  + bracket/form shadows), `sym_step` along the coadjoint derivation for the rest.

`targetLowerBound_of_carrierData`: then `TargetLowerBoundQ L_k(𝔤) (mldeCoeff h∨)`.
-/

namespace VOA.DeligneAudit.VacuumRelation

open VOA VOA.ZhuCoordinate VOA.DeligneAudit.DeligneMLDE MvPolynomial
open VOA.AffineGeneral VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.DeligneCarrier

noncomputable section

/-- Two quadratic forms with the same symmetrization give the same quadratic polynomial. -/
theorem quadraticRelation_eq_of_symm {σ : Type*} [Fintype σ] (q q' : σ × σ → ℂ)
    (h : ∀ a b, q (a, b) + q (b, a) = q' (a, b) + q' (b, a)) :
    quadraticRelation q = quadraticRelation q' := by
  have key : ∀ q : σ × σ → ℂ, (2 : ℂ) • quadraticRelation q
      = ∑ xy : σ × σ, (q xy + q xy.swap) • (X xy.1 * X xy.2) := by
    intro q
    unfold quadraticRelation
    rw [two_smul]
    conv_lhs => arg 2; rw [← (Equiv.prodComm σ σ).sum_comp]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun xy _ => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_smul]
    rw [mul_comm (X xy.2) (X xy.1)]
  have h2 := (key q).trans ((Finset.sum_congr rfl fun xy _ => by
    rw [show q xy + q xy.swap = q' xy + q' xy.swap from h xy.1 xy.2]).trans (key q').symm)
  have h2' := congrArg (fun p => (2 : ℂ)⁻¹ • p) h2
  simpa [smul_smul] using h2'

theorem casPoly_eq_quadraticRelation {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} {ι : Type*} [Fintype ι] (E : SqCurrentData W ι) :
    E.casPoly = quadraticRelation (fun p : ι × ι => E.K p.1 p.2) := by
  unfold SqCurrentData.casPoly quadraticRelation
  rw [← Finset.sum_product']
  refine Finset.sum_congr rfl fun xy _ => ?_
  rw [smul_eq_C_mul]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤}

/-- `5c²/4 + 11c/2 = (h+1)(5h-6)` at `c = -2(h+1)`. -/
theorem kappa_of_c (c h : ℂ) (hc : c = -2 * (h + 1)) :
    5 / 4 * c ^ 2 + 11 / 2 * c = (h + 1) * (5 * h - 6) := by
  rw [hc]; ring

/-- **The vacuum quartic relation from the type data.** -/
theorem vacuumQuarticRelation_of_carrierData (CD : DeligneCarrierData) (D : LieData κ (Fin CD.n))
    (k : ℂ) (hk : k + D.h ≠ 0) (c₀ : ℂ)
    (hcas : (affineCurrentData D k hk).casPoly = MvPolynomial.C c₀ * CD.Q)
    (hrel : ∀ r, (affineCurrentData D k hk).sym (quadraticRelation (CD.rel r)) = 0) :
    VacuumQuarticRelation (simpleVOA D k hk)
      (5 / 4 * (simpleVOA D k hk).centralCharge ^ 2 + 11 / 2 * (simpleVOA D k hk).centralCharge) :=
  vacuumQuarticRelation_affine_of_relations D k hk (fun r => quadraticRelation (CD.rel r)) hrel
    fun i => by
      rw [hcas, mul_left_comm]
      exact Ideal.mul_mem_left _ _ (CD.u3 i)

/-- **The MLDE target lower bound from the type data** (any Deligne type): with
`c = dim·k/(k+h∨) = -2(h+1)`, `dim (L_k(𝔤))_N ≥ mldeCoeff h N`. -/
theorem targetLowerBound_of_carrierData (CD : DeligneCarrierData) (D : LieData κ (Fin CD.n))
    (k : ℂ) (hk : k + D.h ≠ 0) (h : ℕ)
    (hc : (CD.n : ℂ) * k / (k + D.h) = -2 * ((h : ℂ) + 1)) (c₀ : ℂ)
    (hcas : (affineCurrentData D k hk).casPoly = MvPolynomial.C c₀ * CD.Q)
    (hrel : ∀ r, (affineCurrentData D k hk).sym (quadraticRelation (CD.rel r)) = 0) :
    DeligneCharacter.TargetLowerBoundQ (simpleVOA D k hk) (DeligneCharacter.mldeCoeff h) :=
  targetLowerBoundQ_of_vacuumQuarticRelation (simpleVOA D k hk) h
    (by rw [simple_centralCharge', Fintype.card_fin]; exact hc)
    (simple_vacuum_ne_zero' D k hk)
    (vacuumQuarticRelation_of_carrierData CD D k hk c₀ hcas hrel)

end

end VOA.DeligneAudit.VacuumRelation

section AxiomAudit
#print axioms VOA.DeligneAudit.VacuumRelation.quadraticRelation_eq_of_symm
#print axioms VOA.DeligneAudit.VacuumRelation.vacuumQuarticRelation_of_carrierData
#print axioms VOA.DeligneAudit.VacuumRelation.targetLowerBound_of_carrierData
end AxiomAudit
