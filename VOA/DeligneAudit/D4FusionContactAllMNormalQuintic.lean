import VOA.DeligneAudit.D4FusionContactAllMNormalCubic

/-! A whole quintic source family selected by the m=4 defect computation.
Only actual cubic relations, current derivations and ideal multiplication
are used. No leading coefficient or completeness assertion is made. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4
noncomputable section

/-- Keep the entire lowest admissible cubic coefficient and its polar word. -/
def lowCubicPolar (m : ℕ) : Poly m :=
  g0Deriv m 9 0 (g0Deriv m 9 0
    (g0Deriv m 8 0 (g0Deriv m 7 0 (cubic m (m - 2)))))

/-- The two contact multipliers are the actual lower and last modes. -/
def quinticLowRow (m : ℕ) : Poly m :=
  modeX m 1 0 * modeX m 2 (m - 1) * lowCubicPolar m

theorem lowCubicPolar_mem (m : ℕ) : lowCubicPolar m ∈ AllM.candidateIdeal m := by
  exact g0_closed m 0 9 (g0_closed m 0 9
    (g0_closed m 0 8 (g0_closed m 0 7 (cubic_mem m (m - 2) (by omega)))))

/-- A proved source row for every m, with no dimension or normal-form premise. -/
theorem quinticLowRow_mem (m : ℕ) : quinticLowRow m ∈ AllM.candidateIdeal m :=
  (AllM.candidateIdeal m).mul_mem_left _ (lowCubicPolar_mem m)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

theorem quinticLowRow_mem_ann (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    quinticLowRow m ∈ annIdeal R w (modeLetter m) :=
  AllM.source_candidateIdeal_le_ann hm h (quinticLowRow_mem m)

end
#print axioms quinticLowRow_mem_ann
#print axioms lowCubicPolar_mem
#print axioms quinticLowRow_mem
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal
