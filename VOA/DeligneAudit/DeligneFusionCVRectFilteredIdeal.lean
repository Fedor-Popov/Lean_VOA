import VOA.DeligneAudit.DeligneFusionCVRectFilteredSource
import VOA.DeligneAudit.DeligneFusionCVRectFilteredCoeff

/-!
# Actual annihilator ideal and coefficient-generator dimension transfer

Polynomial evaluation acts through the commuting graded currents. Hence
polynomials annihilating the graded cyclic generator form an actual ideal.
Proved generator annihilation therefore suffices for the quotient bound;
the closure is a theorem, not an additional straightening hypothesis.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)
variable {ι : Type} (letter : ι → NegLtr)

theorem polyEval_mul (a p : MvPolynomial ι ℂ) :
    polyEval R w letter (a * p) = polyAlg R w letter a (polyEval R w letter p) := by
  change polyAlg R w letter (a * p) (grGenerator R w) = _
  rw [map_mul, Module.End.mul_apply]
  rfl

/-- The genuine annihilator of the graded cyclic vector under polynomial
evaluation. Commutativity is already proved by the source current bracket. -/
def polyAnnihilator : Ideal (MvPolynomial ι ℂ) where
  carrier := {p | polyEval R w letter p = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro a b ha hb
    change polyEval R w letter (a + b) = 0
    rw [map_add, ha, hb, add_zero]
  smul_mem' := by
    intro a p hp
    change polyEval R w letter (a * p) = 0
    rw [polyEval_mul, hp, map_zero]

theorem span_le_polyEval_ker (S : Set (MvPolynomial ι ℂ))
    (hS : ∀ p ∈ S, polyEval R w letter p = 0) :
    (Ideal.span S).restrictScalars ℂ ≤ LinearMap.ker (polyEval R w letter) := by
  have hh : Ideal.span S ≤ polyAnnihilator R w letter := Ideal.span_le.mpr hS
  intro p hp
  exact hh hp

/-- The complete source-bound interface from actual coefficient-generator
annihilation. No annihilator inclusion or source dimension bound is assumed. -/
theorem source_bound_of_generators {ε ν ϱ : Weight} {j : ℕ}
    (h : CV3Rel R w ε ν ϱ j) (hspan : currentCyclic R w = ⊤)
    (S : Set (MvPolynomial ι ℂ))
    (hS : ∀ p ∈ S, polyEval R w letter p = 0)
    (hcover : ∀ a r, (∃ i, letter i = (a, r)) ∨ R.op (negRoot a) r w = 0)
    [FiniteDimensional ℂ (MvPolynomial ι ℂ ⧸ (Ideal.span S).restrictScalars ℂ)] :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤
      Module.finrank ℂ (MvPolynomial ι ℂ ⧸ (Ideal.span S).restrictScalars ℂ) :=
  source_bound_of_polynomial h hspan letter (Ideal.span S)
    (span_le_polyEval_ker R w letter S hS) hcover

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.span_le_polyEval_ker
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.source_bound_of_generators
