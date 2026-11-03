/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierFiltration

/-!
# Type-generic version of `A2CarrierAuxiliaryJet`

Mechanically generalized from the A₂ file `A2CarrierAuxiliaryJet` to arbitrary type data
`D : DeligneCarrierData` (`Fin 8 ↦ Fin D.n`, `I2ns ↦ D.I`, `casimir ↦ D.Q`, U3 ↦ `D.u3`).
See that file for the mathematical commentary.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial
open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing
open DeligneCarrierData

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable (D : DeligneCarrierData)
include D


/-- Generators of the auxiliary algebra: the eight currents and the Casimir. -/
abbrev AuxVar := Fin D.n ⊕ Unit

/-- Relation labels of the auxiliary algebra. -/
abbrev AuxRel := Option D.ρ ⊕ (Fin D.n ⊕ Unit)

/-- The quadratic relations of the auxiliary algebra. -/
def auxMatrix : (AuxRel D) → (AuxVar D) × (AuxVar D) → ℂ
  | .inl o => fun xy => match xy with
      | (.inl x, .inl y) => D.fullMatrix o (x, y)
      | _ => 0
  | .inr (.inl a) => fun xy => if xy = (.inl a, .inr ()) then 1 else 0
  | .inr (.inr _) => fun xy => if xy = (.inr (), .inr ()) then 1 else 0

/-- The base substitution `x ↦ x`, `c ↦ Q`. -/
def baseSubst : MvPolynomial (AuxVar D) ℂ →ₐ[ℂ] MvPolynomial (Fin D.n) ℂ :=
  aeval (Sum.elim X (fun _ => D.Q))

theorem baseSubst_auxMatrix_inl (o : Option D.ρ) :
    (baseSubst D) (quadraticRelation ((auxMatrix D) (.inl o))) = quadraticRelation (D.fullMatrix o) := by
  simp [quadraticRelation, baseSubst, auxMatrix, Fintype.sum_prod_type, Fintype.sum_sum_type,
    MvPolynomial.smul_eq_C_mul]

theorem baseSubst_auxMatrix_mixed (a : Fin D.n) :
    (baseSubst D) (quadraticRelation ((auxMatrix D) (.inr (.inl a)))) = X a * D.Q := by
  simp [quadraticRelation, baseSubst, auxMatrix]

theorem baseSubst_auxMatrix_square (u : Unit) :
    (baseSubst D) (quadraticRelation ((auxMatrix D) (.inr (.inr u)))) = D.Q * D.Q := by
  simp [quadraticRelation, baseSubst, auxMatrix]

/-- Every relation other than the Casimir relation of `I₂` is sent into `I₂ⁿˢ`. -/
theorem baseSubst_auxMatrix_mem (r : (AuxRel D)) (hr : r ≠ .inl none) :
    (baseSubst D) (quadraticRelation ((auxMatrix D) r)) ∈ D.I := by
  rcases r with (_ | a) | (a | u)
  · exact absurd rfl hr
  · rw [(baseSubst_auxMatrix_inl D), D.quadraticRelation_fullMatrix_some]
    exact D.rel_mem a
  · rw [(baseSubst_auxMatrix_mixed D)]
    exact D.u3 a
  · rw [(baseSubst_auxMatrix_square D)]
    exact D.Q_sq_mem

theorem baseSubst_auxMatrix_casimir :
    (baseSubst D) (quadraticRelation ((auxMatrix D) (.inl none))) = D.Q := by
  rw [(baseSubst_auxMatrix_inl D), D.quadraticRelation_fullMatrix_none]

/-- The image of one auxiliary jet variable. -/
def auxJetImage (p : ℕ) (v : JetVar (AuxVar D) p) : JetPoly ℂ (Fin D.n) p :=
  Sum.elim (fun x => X ⟨x, v.order⟩) (fun _ => relationCoeff (R := ℂ) p v.order D.Q)
    v.generator

/-- Jet substitution `x^{(a)} ↦ x^{(a)}`, `c^{(b)} ↦ Q_{(b)}`. -/
def auxJetSubst (p : ℕ) : JetPoly ℂ (AuxVar D) p →ₐ[ℂ] JetPoly ℂ (Fin D.n) p :=
  aeval ((auxJetImage D) p)

theorem auxJetSubst_relationCoeff_X (p n : ℕ) (hn : n ≤ p) (v : (AuxVar D)) :
    (auxJetSubst D) p (relationCoeff (R := ℂ) p n (X v)) =
      relationCoeff (R := ℂ) p n ((baseSubst D) (X v)) := by
  rw [relationCoeff_X, jetVariable_of_le p v n hn, auxJetSubst, aeval_X]
  rcases v with x | u
  · simp [auxJetImage, baseSubst, jetVariable_of_le p x n hn]
  · simp [auxJetImage, baseSubst]

/-- **Jet substitution commutes with Hasse–Schmidt coefficients** (in retained orders). -/
theorem auxJetSubst_relationCoeff (p : ℕ) (f : MvPolynomial (AuxVar D) ℂ) :
    ∀ n ≤ p, (auxJetSubst D) p (relationCoeff (R := ℂ) p n f) =
      relationCoeff (R := ℂ) p n ((baseSubst D) f) := by
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
    rw [map_mul, hf ij.1 (by omega), (auxJetSubst_relationCoeff_X D) p ij.2 (by omega)]

/-- Every auxiliary jet relation except the Casimir one lands in `jetIdeal p I₂ⁿˢ`. -/
theorem auxJetSubst_relation_mem (p n : ℕ) (hn : n ≤ p) (r : (AuxRel D)) (hr : r ≠ .inl none) :
    (auxJetSubst D) p (relationCoeff (R := ℂ) p n (quadraticRelation ((auxMatrix D) r))) ∈
      jetIdeal (R := ℂ) p D.I := by
  rw [(auxJetSubst_relationCoeff D) p _ n hn]
  exact relationCoeff_mem_jetIdeal p n D.I _ ((baseSubst_auxMatrix_mem D) r hr) hn

/-- The Casimir relation of `I₂` is sent to the Casimir jet coefficient. -/
theorem auxJetSubst_relation_casimir (p n : ℕ) (hn : n ≤ p) :
    (auxJetSubst D) p (relationCoeff (R := ℂ) p n (quadraticRelation ((auxMatrix D) (.inl none)))) =
      relationCoeff (R := ℂ) p n D.Q := by
  rw [(auxJetSubst_relationCoeff D) p _ n hn, (baseSubst_auxMatrix_casimir D)]

end

end VOA.DeligneAudit.DeligneCarrier
