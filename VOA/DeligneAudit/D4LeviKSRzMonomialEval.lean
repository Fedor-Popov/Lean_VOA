import VOA.DeligneAudit.D4LeviKSRzOrbitGenerator

/-! Fixed-shape evaluation of a polynomial monomial. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xyzEvaluation_prod_X_pow {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (d : σ → ℕ) :
    xyzEvaluation ρ w shape
        (∏ t : σ, (X t : MvPolynomial σ ℂ) ^ d t) =
      radicalWord ρ w
        (Finset.univ.toList.map fun t => (shape t, d t)) := by
  classical
  rw [MvPolynomial.prod_X_pow]
  change modeWordEvaluation σ _ (modeMonomial σ _) = _
  rw [modeWordEvaluation_monomial]
  simp [shapedModes]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_prod_X_pow
