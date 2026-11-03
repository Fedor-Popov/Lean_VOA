import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeTopShiftClosureBase
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePolarZeroClosure
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePolarModeSeeds

/-! Plain highest-color shifts preserve the literal top quadratic/cubic ideal.
Its image lies in the actual static polar ideal. No global Cartan action or
higher-power stability is assumed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Only admissible WHOLE highest-color coefficients of source powers two and three. -/
def topQuadraticCubicSeeds (m : ℕ) : Set (TopPoly m) :=
  {p | ∃ r s, (r = 2 ∨ r = 3) ∧ m < r + s ∧
    p = PowerSeries.coeff s (topCurrent m ^ r)}

def topQuadraticCubicIdeal (m : ℕ) : Ideal (TopPoly m) :=
  Ideal.span (topQuadraticCubicSeeds m)

theorem topQuadraticCubic_coeff_mem (m r s : ℕ) (hr : r = 2 ∨ r = 3)
    (hs : m < r + s) :
    PowerSeries.coeff s (topCurrent m ^ r) ∈ topQuadraticCubicIdeal m :=
  Ideal.subset_span ⟨r,s,hr,hs,rfl⟩

/-- Every plain shift sends each admissible highest quadratic/cubic seed into
its literal top ideal; linear truncation and quadratic tails supply the proof. -/
theorem topShift_seed_mem_topIdeal (m r s ell : ℕ) (hr : r = 2 ∨ r = 3)
    (hs : m < r + s) :
    topShift m ell (PowerSeries.coeff s (topCurrent m ^ r)) ∈
      topQuadraticCubicIdeal m := by
  rcases hr with rfl | rfl
  · rw [topShift_highest_coeff_recurrence m 1 s ell]
    apply (topQuadraticCubicIdeal m).sub_mem
    · exact (topQuadraticCubicIdeal m).nsmul_mem
        (topQuadraticCubic_coeff_mem m 2 (s + ell) (Or.inl rfl) (by omega)) 2
    · exact (topQuadraticCubicIdeal m).nsmul_mem (by
        apply Submodule.sum_mem
        intro a ha
        have ha' : a < ell := Finset.mem_range.mp ha
        rw [topLinear_coeff_high m (s + ell - a) (by omega),mul_zero]
        exact (topQuadraticCubicIdeal m).zero_mem) 2
  · rw [topShift_highest_coeff_recurrence m 2 s ell]
    apply (topQuadraticCubicIdeal m).sub_mem
    · exact (topQuadraticCubicIdeal m).nsmul_mem
        (topQuadraticCubic_coeff_mem m 3 (s + ell) (Or.inr rfl) (by omega)) 3
    · exact (topQuadraticCubicIdeal m).nsmul_mem (by
        apply Submodule.sum_mem
        intro a ha
        have ha' : a < ell := Finset.mem_range.mp ha
        exact (topQuadraticCubicIdeal m).mul_mem_left _
          (topQuadraticCubic_coeff_mem m 2 (s + ell - a) (Or.inl rfl) (by omega))) 3

/-- The literal top quadratic/cubic ideal is preserved by every plain shift mode. -/
theorem topQuadraticCubicIdeal_shift_closed (m ell : ℕ) {p : TopPoly m}
    (hp : p ∈ topQuadraticCubicIdeal m) :
    topShift m ell p ∈ topQuadraticCubicIdeal m := by
  apply polar_ideal_span_derivation_closed (topShift m ell)
    (topQuadraticCubicSeeds m) ?_ hp
  rintro p ⟨r,s,hr,hs,rfl⟩
  exact topShift_seed_mem_topIdeal m r s ell hr hs

/-- Mapping the whole literal top ideal produces actual J23 members. -/
theorem topMap_topQuadraticCubicIdeal_le_polarIdeal (m : ℕ) :
    (topQuadraticCubicIdeal m).map (topMap m).toRingHom ≤
      quadraticCubicPolarIdeal m := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro p ⟨r,s,hr,hs,rfl⟩
  change topMap m (PowerSeries.coeff s (topCurrent m ^ r)) ∈
    quadraticCubicPolarIdeal m
  rw [topMap_seed]
  exact highest_coeff_mem_polarIdeal m r s hr hs

theorem topMap_topQuadraticCubicIdeal_mem (m : ℕ) {p : TopPoly m}
    (hp : p ∈ topQuadraticCubicIdeal m) :
    topMap m p ∈ quadraticCubicPolarIdeal m :=
  topMap_topQuadraticCubicIdeal_le_polarIdeal m
    (Ideal.mem_map_of_mem (topMap m).toRingHom hp)

/-- A quartic plain-shift step is the shifted static coefficient times four,
modulo the literal TOP quadratic/cubic ideal. This is not quartic membership. -/
theorem topShift_quartic_step_mem_topIdeal (m s ell : ℕ) (hs : m < 4 + s) :
    topShift m ell (PowerSeries.coeff s (topCurrent m ^ 4)) -
      4 • PowerSeries.coeff (s + ell) (topCurrent m ^ 4) ∈
      topQuadraticCubicIdeal m := by
  rw [topShift_highest_coeff_recurrence m 3 s ell,
    sub_right_comm,sub_self,zero_sub]
  apply (topQuadraticCubicIdeal m).neg_mem
  exact (topQuadraticCubicIdeal m).nsmul_mem (by
    apply Submodule.sum_mem
    intro a ha
    have ha' : a < ell := Finset.mem_range.mp ha
    exact (topQuadraticCubicIdeal m).mul_mem_left _
      (topQuadraticCubic_coeff_mem m 3 (s + ell - a) (Or.inr rfl) (by omega))) 4

end
#print axioms topQuadraticCubicIdeal_shift_closed
#print axioms topMap_topQuadraticCubicIdeal_le_polarIdeal
#print axioms topShift_quartic_step_mem_topIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
