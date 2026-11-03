import VOA.Huang.AssocConverseReduction
import VOA.Huang.PzTensorDecompPBW

/-! # Finite irredundant representatives for converse associativity

The DLM route retains its finiteness hypothesis and does not use the PBW theorem `VOA.pbw`.
The separate PBW corollary uses the existing project witness explicitly.
Neither statement asserts product-channel faithfulness.
-/

namespace VOA.Huang.AssocConverse
open VOA

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}

/-- Completeness and irredundancy for an explicitly indexed finite family. -/
def CompleteIrredundantFamily {ι : Type*} (R : ι → LWModule W) : Prop :=
  (∀ j, (R j).IsIrreducibleLW) ∧
  (∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j)) ∧
  (∀ i j, LWModule.Iso W (R i) (R j) → i = j)

theorem exists_completeIrredundantFamily (hfin : Finite (Φ W)) :
    ∃ (n : ℕ) (R : Fin n → LWModule W), CompleteIrredundantFamily R := by
  classical
  letI := hfin
  letI := Fintype.ofFinite (Φ W)
  let e := (Fintype.equivFin (Φ W)).symm
  refine ⟨Fintype.card (Φ W), fun j => canonicalIrrLWModule (e j), ?_, ?_, ?_⟩
  · exact fun j => canonicalIrrLWModule_irreducible (e j)
  · intro Q hQ
    let X : IrrModule W := ⟨Q.carrier, Q.isMod, hQ⟩
    obtain ⟨j, hj⟩ := e.surjective X.toΦ
    refine ⟨j, ?_⟩
    have h : (canonicalIrrModule (e j)).toΦ = X.toΦ :=
      (canonicalIrrModule_toΦ _).trans hj
    obtain ⟨d⟩ := Quotient.exact h
    exact ⟨d.symm⟩
  · intro i j hij
    apply e.injective
    have h : (canonicalIrrModule (e i)).toΦ = (canonicalIrrModule (e j)).toΦ :=
      Quotient.sound hij
    simpa using h

/-- DLM finiteness gives representatives without a PBW dependency; DLM remains
an explicit hypothesis, not an axiom or a theorem proved in this file. -/
theorem exists_completeIrredundantFamily_of_DLM (hV : StronglyRational W)
    (hfin : DLMFinitelyManyIrredAdmissible W) :
    ∃ (n : ℕ) (R : Fin n → LWModule W), CompleteIrredundantFamily R :=
  exists_completeIrredundantFamily (finite_Φ_of_finite_Φadm W (hfin hV.rational))

/-- Representatives from the existing PBW-relative Zhu finiteness theorem. -/
theorem exists_completeIrredundantFamily_pbw (hV : StronglyRational W) :
    ∃ (n : ℕ) (R : Fin n → LWModule W), CompleteIrredundantFamily R :=
  exists_completeIrredundantFamily
    (VOA.Huang.PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV)

end VOA.Huang.AssocConverse
