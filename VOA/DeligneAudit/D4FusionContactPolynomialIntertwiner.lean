import VOA.DeligneAudit.D4FusionContactPolynomialEval
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# A proved operator intertwiner gives full annihilator stability

The commutator identities on variables extend to every polynomial by
induction. Thus derivation closure applies to the entire annihilator
ideal, including multiplied relations.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)
variable {ι : Type} (letter : ι → CurrentLetter)

theorem polyEval_C (c : ℂ) :
    polyEval R w letter (MvPolynomial.C c) = c • grGenerator R w := by
  rw [MvPolynomial.C_eq_smul_one, map_smul, polyEval_one]

/-- Generator commutators of an actual graded operator imply the full
polynomial derivation identity. The eigenvalue of the source generator is
retained explicitly, so zero-mode Cartan currents are included. -/
theorem derivation_intertwines
    (D : Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ))
    (T : Module.End ℂ (Gr R w)) (a : ℂ)
    (hgen : T (grGenerator R w) = a • grGenerator R w)
    (hcomm : ∀ i, T * polyOp R w letter i - polyOp R w letter i * T =
      polyAlg R w letter (D (MvPolynomial.X i))) (p : MvPolynomial ι ℂ) :
    polyEval R w letter (D p) = T (polyEval R w letter p) - a • polyEval R w letter p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.derivation_C, map_zero, polyEval_C, map_smul, hgen]
      module
  | add p q ihp ihq =>
      simp only [map_add, ihp, ihq, smul_add]
      abel
  | mul_X p i ih =>
      have hc := congrArg (fun A : Module.End ℂ (Gr R w) => A (polyEval R w letter p))
        (hcomm i)
      simp only [Module.End.mul_apply, LinearMap.sub_apply] at hc
      calc
        polyEval R w letter (D (p * MvPolynomial.X i)) =
            polyAlg R w letter (D (MvPolynomial.X i)) (polyEval R w letter p) +
              grOp R w (letter i).1 (letter i).2 (polyEval R w letter (D p)) := by
          rw [D.leibniz]
          change polyEval R w letter (p * D (MvPolynomial.X i) + MvPolynomial.X i * D p) = _
          rw [map_add, mul_comm p (D (MvPolynomial.X i)), polyEval_mul, polyEval_X_mul]
        _ = T (polyEval R w letter (p * MvPolynomial.X i)) -
            a • polyEval R w letter (p * MvPolynomial.X i) := by
          rw [ih, ← hc, mul_comm p (MvPolynomial.X i), polyEval_X_mul, map_sub, map_smul]
          dsimp only [polyOp]
          abel

/-- Stability follows for every annihilating polynomial, not only the
initial seed set. Closure under polynomial multipliers is already part
of the actual `annIdeal` definition. -/
theorem annIdeal_derivation_closed
    (D : Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ))
    (T : Module.End ℂ (Gr R w)) (a : ℂ)
    (hgen : T (grGenerator R w) = a • grGenerator R w)
    (hcomm : ∀ i, T * polyOp R w letter i - polyOp R w letter i * T =
      polyAlg R w letter (D (MvPolynomial.X i))) :
    ∀ p ∈ annIdeal R w letter, D p ∈ annIdeal R w letter := by
  intro p hp
  change polyEval R w letter (D p) = 0
  rw [derivation_intertwines R w letter D T a hgen hcomm p, hp, map_zero, smul_zero, sub_zero]

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.derivation_intertwines
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.annIdeal_derivation_closed
