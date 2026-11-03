/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.DeligneAudit.A2CarrierResummation
import VOA.Commutative.QuadraticCurrentGradedCarrier
import VOA.Commutative.DeligneAuxiliaryDegree
import VOA.Commutative.DeligneCasimirJetFiltration

/-!
# Type data for the Deligne carrier chain

The carrier side of the Deligne chain needs, for each type, only:

* the number `n = dim g` of currents;
* the quadratic relations of `I₂ⁿˢ`, as coefficient matrices `rel : ρ → Fin n × Fin n → ℂ`;
* the Casimir quadratic, as a coefficient matrix `cas`;
* input U3: `X a · Q ∈ (I₂ⁿˢ)` for every current `a`.

`DeligneCarrierData` packages these.  Everything downstream (`DeligneCarrierChain`,
`DeligneCarrierFiltration`, `DeligneCarrierAux*`, `DeligneCarrierLayerBound`) is stated for an
arbitrary `D : DeligneCarrierData`; `DeligneCarrierA2` and `DeligneCarrierD4` are instances.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial VOA.FiniteJet VOA.QuadraticJetCoefficientPairing

noncomputable section

/-- **Type data for the carrier chain.** -/
structure DeligneCarrierData where
  /-- Number of currents, `dim g`. -/
  n : ℕ
  /-- Labels of the relations of `I₂ⁿˢ`. -/
  ρ : Type
  /-- The relations of `I₂ⁿˢ`. -/
  rel : ρ → Fin n × Fin n → ℂ
  /-- The Casimir quadratic. -/
  cas : Fin n × Fin n → ℂ
  /-- Input U3: every current times the Casimir lies in `I₂ⁿˢ`. -/
  u3 : ∀ a : Fin n, X a * quadraticRelation cas ∈ quadraticIdeal rel

namespace DeligneCarrierData

variable (D : DeligneCarrierData)

/-- The ideal `I₂ⁿˢ`. -/
abbrev I : Ideal (MvPolynomial (Fin D.n) ℂ) := quadraticIdeal D.rel

/-- The Casimir. -/
abbrev Q : MvPolynomial (Fin D.n) ℂ := quadraticRelation D.cas

theorem quadraticRelation_isHomogeneous {σ : Type*} [Fintype σ] (c : σ × σ → ℂ) :
    (quadraticRelation c).IsHomogeneous 2 := by
  unfold quadraticRelation
  apply MvPolynomial.IsHomogeneous.sum
  intro xy _
  rw [← mem_homogeneousSubmodule]
  exact Submodule.smul_mem _ _ ((isHomogeneous_X ℂ xy.1).mul (isHomogeneous_X ℂ xy.2))

theorem Q_isHomogeneous : D.Q.IsHomogeneous 2 := quadraticRelation_isHomogeneous D.cas

theorem Q_isWeightedHomogeneous : D.Q.IsWeightedHomogeneous (fun _ : Fin D.n => 1) 2 :=
  D.Q_isHomogeneous

theorem rel_mem (r : D.ρ) : quadraticRelation (D.rel r) ∈ D.I := Ideal.subset_span ⟨r, rfl⟩

theorem quadraticRelation_mem_span_X {σ : Type*} [Fintype σ] (c : σ × σ → ℂ) :
    quadraticRelation c ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ ℂ)) := by
  unfold quadraticRelation
  refine Ideal.sum_mem _ fun xy _ => ?_
  rw [smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨xy.1, rfl⟩))

theorem mul_Q_mem_of_mem_span_X (f : MvPolynomial (Fin D.n) ℂ)
    (hf : f ∈ Ideal.span (Set.range (X : Fin D.n → MvPolynomial (Fin D.n) ℂ))) :
    f * D.Q ∈ D.I := by
  refine Submodule.span_induction (p := fun f _ => f * D.Q ∈ D.I) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨a, rfl⟩
    exact D.u3 a
  · simp
  · intro f g _ _ hf hg
    rw [add_mul]
    exact Ideal.add_mem _ hf hg
  · intro r f _ hf
    rw [smul_eq_mul, mul_assoc]
    exact Ideal.mul_mem_left _ r hf

/-- `Q² ∈ I₂ⁿˢ`. -/
theorem Q_sq_mem : D.Q * D.Q ∈ D.I :=
  D.mul_Q_mem_of_mem_span_X _ (quadraticRelation_mem_span_X D.cas)

/-- The literal carrier family of the type. -/
abbrev Carrier (p N : ℕ) : Type := CarrierEmbedding.Carrier D.rel p N

/-- The full `I₂ = I₂ⁿˢ ⊕ ℂ Q`: the Casimir (`none`) and the relations of `I₂ⁿˢ`. -/
def fullMatrix : Option D.ρ → Fin D.n × Fin D.n → ℂ
  | none => D.cas
  | some r => D.rel r

theorem quadraticRelation_fullMatrix_none : quadraticRelation (D.fullMatrix none) = D.Q := rfl

theorem quadraticRelation_fullMatrix_some (r : D.ρ) :
    quadraticRelation (D.fullMatrix (some r)) = quadraticRelation (D.rel r) := rfl

end DeligneCarrierData

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier
#print axioms DeligneCarrierData.Q_sq_mem
end AxiomAudit
