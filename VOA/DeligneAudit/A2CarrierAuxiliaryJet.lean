/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierFiltration

/-!
# The auxiliary algebra and its substitution map (B1, step 1)

The auxiliary algebra of the Casimir filtration has one extra generator `c` (the Casimir, weight 2)
besides the eight currents: `AuxVar = Fin 8 ⊕ Unit`.  Its quadratic relations `auxMatrix` are

* `inl o`: the full `I₂` on currents (`fullMatrix o`: the eight adjoint relations and the Casimir);
* `inr (inl a)`: the mixed relation `x_a · c`;
* `inr (inr ())`: the Casimir square `c · c`.

The substitution `c ↦ Q` is `baseSubst`; on jets it is `auxJetSubst p`, sending `c^{(b)}` to the
Hasse–Schmidt coefficient `Q_{(b)} = relationCoeff p b casimir`.  We prove that jet substitution
commutes with taking Hasse–Schmidt coefficients (`auxJetSubst_relationCoeff`), and that every auxiliary
jet relation is sent into `jetIdeal p I₂ⁿˢ`, except the Casimir relation of `I₂`, which is sent to the
Casimir jet coefficient itself (`auxJetSubst_relation_*`).
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial
open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing

noncomputable section

/-- Generators of the auxiliary algebra: the eight currents and the Casimir. -/
abbrev AuxVar := Fin 8 ⊕ Unit

/-- Relation labels of the auxiliary algebra. -/
abbrev AuxRel := Option (Fin 8) ⊕ (Fin 8 ⊕ Unit)

/-- The quadratic relations of the auxiliary algebra. -/
def auxMatrix : AuxRel → AuxVar × AuxVar → ℂ
  | .inl o => fun xy => match xy with
      | (.inl x, .inl y) => fullMatrix o (x, y)
      | _ => 0
  | .inr (.inl a) => fun xy => if xy = (.inl a, .inr ()) then 1 else 0
  | .inr (.inr _) => fun xy => if xy = (.inr (), .inr ()) then 1 else 0

/-- The base substitution `x ↦ x`, `c ↦ Q`. -/
def baseSubst : MvPolynomial AuxVar ℂ →ₐ[ℂ] MvPolynomial (Fin 8) ℂ :=
  aeval (Sum.elim X (fun _ => casimir))

theorem baseSubst_auxMatrix_inl (o : Option (Fin 8)) :
    baseSubst (quadraticRelation (auxMatrix (.inl o))) = quadraticRelation (fullMatrix o) := by
  simp [quadraticRelation, baseSubst, auxMatrix, Fintype.sum_prod_type, Fintype.sum_sum_type,
    MvPolynomial.smul_eq_C_mul]

theorem baseSubst_auxMatrix_mixed (a : Fin 8) :
    baseSubst (quadraticRelation (auxMatrix (.inr (.inl a)))) = X a * casimir := by
  simp [quadraticRelation, baseSubst, auxMatrix]

theorem baseSubst_auxMatrix_square (u : Unit) :
    baseSubst (quadraticRelation (auxMatrix (.inr (.inr u)))) = casimir * casimir := by
  simp [quadraticRelation, baseSubst, auxMatrix]

/-- Every relation other than the Casimir relation of `I₂` is sent into `I₂ⁿˢ`. -/
theorem baseSubst_auxMatrix_mem (r : AuxRel) (hr : r ≠ .inl none) :
    baseSubst (quadraticRelation (auxMatrix r)) ∈ I2ns := by
  rcases r with (_ | a) | (a | u)
  · exact absurd rfl hr
  · rw [baseSubst_auxMatrix_inl, quadraticRelation_fullMatrix_some]
    exact relationPoly_mem_I2ns a
  · rw [baseSubst_auxMatrix_mixed]
    exact X_mul_casimir_mem_I2ns a
  · rw [baseSubst_auxMatrix_square]
    exact casimir_sq_mem_I2ns

theorem baseSubst_auxMatrix_casimir :
    baseSubst (quadraticRelation (auxMatrix (.inl none))) = casimir := by
  rw [baseSubst_auxMatrix_inl, quadraticRelation_fullMatrix_none]

/-- The image of one auxiliary jet variable. -/
def auxJetImage (p : ℕ) (v : JetVar AuxVar p) : JetPoly ℂ (Fin 8) p :=
  Sum.elim (fun x => X ⟨x, v.order⟩) (fun _ => relationCoeff (R := ℂ) p v.order casimir)
    v.generator

/-- Jet substitution `x^{(a)} ↦ x^{(a)}`, `c^{(b)} ↦ Q_{(b)}`. -/
def auxJetSubst (p : ℕ) : JetPoly ℂ AuxVar p →ₐ[ℂ] JetPoly ℂ (Fin 8) p :=
  aeval (auxJetImage p)

theorem auxJetSubst_relationCoeff_X (p n : ℕ) (hn : n ≤ p) (v : AuxVar) :
    auxJetSubst p (relationCoeff (R := ℂ) p n (X v)) =
      relationCoeff (R := ℂ) p n (baseSubst (X v)) := by
  rw [relationCoeff_X, jetVariable_of_le p v n hn, auxJetSubst, aeval_X]
  rcases v with x | u
  · simp [auxJetImage, baseSubst, jetVariable_of_le p x n hn]
  · simp [auxJetImage, baseSubst]

/-- **Jet substitution commutes with Hasse–Schmidt coefficients** (in retained orders). -/
theorem auxJetSubst_relationCoeff (p : ℕ) (f : MvPolynomial AuxVar ℂ) :
    ∀ n ≤ p, auxJetSubst p (relationCoeff (R := ℂ) p n f) =
      relationCoeff (R := ℂ) p n (baseSubst f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro n _
    cases n with
    | zero => simp [auxJetSubst]
    | succ n => simp
  | add f g hf hg =>
    intro n hn
    rw [relationCoeff_add, map_add, hf n hn, hg n hn, map_add, relationCoeff_add]
  | mul_X f v hf =>
    intro n hn
    rw [relationCoeff_mul, map_sum, map_mul, relationCoeff_mul]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have hij' := Finset.mem_antidiagonal.mp hij
    rw [map_mul, hf ij.1 (by omega), auxJetSubst_relationCoeff_X p ij.2 (by omega)]

/-- Every auxiliary jet relation except the Casimir one lands in `jetIdeal p I₂ⁿˢ`. -/
theorem auxJetSubst_relation_mem (p n : ℕ) (hn : n ≤ p) (r : AuxRel) (hr : r ≠ .inl none) :
    auxJetSubst p (relationCoeff (R := ℂ) p n (quadraticRelation (auxMatrix r))) ∈
      jetIdeal (R := ℂ) p I2ns := by
  rw [auxJetSubst_relationCoeff p _ n hn]
  exact relationCoeff_mem_jetIdeal p n I2ns _ (baseSubst_auxMatrix_mem r hr) hn

/-- The Casimir relation of `I₂` is sent to the Casimir jet coefficient. -/
theorem auxJetSubst_relation_casimir (p n : ℕ) (hn : n ≤ p) :
    auxJetSubst p (relationCoeff (R := ℂ) p n (quadraticRelation (auxMatrix (.inl none)))) =
      relationCoeff (R := ℂ) p n casimir := by
  rw [auxJetSubst_relationCoeff p _ n hn, baseSubst_auxMatrix_casimir]

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms baseSubst_auxMatrix_mem
#print axioms auxJetSubst_relationCoeff
#print axioms auxJetSubst_relation_mem
#print axioms auxJetSubst_relation_casimir
end AxiomAudit
