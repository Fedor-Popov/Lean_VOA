import VOA.DeligneAudit.DeligneFusionCVRectFilteredCurrent
import VOA.DeligneAudit.DeligneFusionCVRectFilteredIdeal
import VOA.DeligneAudit.DeligneFusionCVRectStarBound

/-!
# Transparent transfer of the proved STAR quotient count to an actual source

The only relation premise is the displayed family of actual current
coefficients modulo shorter actual PBW words. The source polynomial map,
annihilator closure, quotient count, and filtered dimension transfer are all
proved internally. This is a conditional bridge, not an established instance
of the mixed rectangular base bounds.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectStarFamily
open VOA.DeligneAudit.A2.CVRectStarCount

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

theorem star_ideal_le_ker (left right center : List ℕ)
    (hx : ∀ t, left.length ≤ t → R.op 3 t w = 0)
    (hy : ∀ t, left.length + right.length + center.length ≤ t → R.op 5 t w = 0)
    (hz : ∀ t, right.length ≤ t → R.op 4 t w = 0)
    (hrel : ∀ p q r j, j < starOrder left right center p q r →
      j ≤ reverseDegree left.length (left.length + right.length + center.length) right.length p q r →
      orderedCoeff R w p q r
        (reverseDegree left.length (left.length + right.length + center.length) right.length p q r - j)
          ∈ Pbelow R w (p + q + r)) :
    (ideal left.length (left.length + right.length + center.length)
      right.length left right center).restrictScalars ℂ ≤ LinearMap.ker
        (polyEval R w (modeLetter left.length
          (left.length + right.length + center.length) right.length)) := by
  apply span_le_polyEval_ker
  rintro P ⟨p, q, r, j, hj, rfl⟩
  by_cases hD : j ≤ reverseDegree left.length
      (left.length + right.length + center.length) right.length p q r
  · rw [starCoeff_eval R w _ _ _ p q r j hx hy hz hD]
    exact gradedOrderedCoeff_zero R w p q r _ (hrel p q r j hj hD)
  · exact starCoeff_eval_high R w _ _ _ p q r j (by omega)

/-- Actual source upper bound from explicitly proved source coefficient
relations. The polynomial quotient's finiteness and product count are theorems,
not hypotheses. The source's finite-dimensionality is a conclusion. -/
theorem source_star_bound {ε ν ϱ : Weight} {j : ℕ}
    (h : CV3Rel R w ε ν ϱ j) (hspan : currentCyclic R w = ⊤)
    (left right center : List ℕ)
    (hx : ∀ t, left.length ≤ t → R.op 3 t w = 0)
    (hy : ∀ t, left.length + right.length + center.length ≤ t → R.op 5 t w = 0)
    (hz : ∀ t, right.length ≤ t → R.op 4 t w = 0)
    (hrel : ∀ p q r i, i < starOrder left right center p q r →
      i ≤ reverseDegree left.length (left.length + right.length + center.length) right.length p q r →
      orderedCoeff R w p q r
        (reverseDegree left.length (left.length + right.length + center.length) right.length p q r - i)
          ∈ Pbelow R w (p + q + r)) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ starWeight left right center := by
  let I := ideal left.length (left.length + right.length + center.length)
    right.length left right center
  let letter := modeLetter left.length (left.length + right.length + center.length) right.length
  have hb := CVRectStarBound.family_bound left right center
  haveI := hb.1
  let E : (StarRing left.length (left.length + right.length + center.length) right.length ⧸
      I.restrictScalars ℂ) ≃ₗ[ℂ] Family left right center :=
    Submodule.Quotient.restrictScalarsEquiv ℂ I
  haveI := E.symm.finiteDimensional
  have hI : I.restrictScalars ℂ ≤ LinearMap.ker (polyEval R w letter) :=
    star_ideal_le_ker R w left right center hx hy hz hrel
  obtain ⟨hFD, hdim⟩ := source_bound_of_polynomial h hspan letter I hI
    (modeLetter_cover R w _ _ _ hx hy hz)
  exact ⟨hFD, hdim.trans (E.finrank_eq.le.trans hb.2)⟩

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.star_ideal_le_ker
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.source_star_bound
