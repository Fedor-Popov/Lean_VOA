import VOA.DeligneAudit.D4FusionContactNormalSpan
import VOA.DeligneAudit.D4FusionContactQuadraticSource
import VOA.DeligneAudit.D4FusionContactTruncation

/-!
# The actual D₄ multiplicity-one sharp total upper bound

This is the m=1 case only. The source relations supply every quadratic
row, the center cube, and current truncation. No source finiteness or
fusion dimension premise is used.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorGraded
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V}

theorem localWeyl_one_piece_two_le_normal (h : LocalWeylRelG D4sector R w 1) :
    piece R w 2 ≤ normalSpan R w := by
  apply piece_two_le_normal
  intro r
  exact Quadratic.Source.raw_rows_mem_of_square (highestRel_of_localWeyl h)
    (localWeyl_simple_square h) r

/-- The degree-zero source is finite dimensional with sharp upper
bound 28, all supplied by the actual defining relations. -/
theorem localWeyl_one_zero_bound (h : LocalWeylRelG D4sector R w 1) :
    FiniteDimensional ℂ (cycDeg R w 0) ∧ Module.finrank ℂ (cycDeg R w 0) ≤ 28 := by
  have hN := normalSpan_bound (R := R) (w := w)
  haveI : FiniteDimensional ℂ (normalSpan R w) := hN.1
  have hle := (localWeyl_one_cycDeg_le_piece h).trans (localWeyl_one_piece_two_le_normal h)
  haveI : FiniteDimensional ℂ (cycDeg R w 0) := Submodule.finiteDimensional_of_le hle
  exact ⟨inferInstance, (Submodule.finrank_mono hle).trans hN.2⟩

theorem localWeyl_one_finite (h : LocalWeylRelG D4sector R w 1) (d : ℕ) :
    FiniteDimensional ℂ (cycDeg R w d) := by
  by_cases hd : d = 0
  · subst d
    exact (localWeyl_one_zero_bound h).1
  · rw [localWeyl_one_cycDeg_eq_bot h d (by omega)]
    infer_instance

/-- The actual m=1 total fusion dimension bound. This does not assert
the all-m D₄ FusionTotalDimG input. -/
theorem localWeyl_one_total_dim (h : LocalWeylRelG D4sector R w 1) (B : ℕ) :
    ∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d) ≤ 28 := by
  classical
  by_cases hB : B = 0
  · subst B
    simp
  calc
    _ = Module.finrank ℂ (cycDeg R w 0) := by
      apply Finset.sum_eq_single 0
      · intro d _ hd
        rw [localWeyl_one_cycDeg_eq_bot h d (by omega)]
        simp
      · intro hz
        exact False.elim (hz (Finset.mem_range.mpr (by omega)))
    _ ≤ 28 := (localWeyl_one_zero_bound h).2

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_one_zero_bound
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_one_finite
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_one_total_dim
