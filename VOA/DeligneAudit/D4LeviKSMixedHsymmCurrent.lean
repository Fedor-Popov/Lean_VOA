import VOA.DeligneAudit.D4LeviKSMixedCoeffAlloc

/-! Evaluation of a complete homogeneous polynomial as a mixed-current coefficient. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xyz_hsymm_evaluation_current
    (ρ : CurrentModule D4sector.f V) (w : V)
    (n s : ℕ) (shape : Fin n → Fin 6) :
    xyzEvaluation ρ w shape (hsymm (Fin n) ℂ s) =
      (PowerSeries.coeff s
        (((List.finRange n).map fun i =>
          fCurrent (fun r => ρ.op (radicalColour (shape i)) r)).prod)) w := by
  rw [xyz_hsymm_evaluation_allocations]
  have hseries :
      ((List.finRange n).map fun i =>
        fCurrent (fun r => ρ.op (radicalColour (shape i)) r)) =
      (((List.finRange n).map fun i =>
        (fun r => ρ.op (radicalColour (shape i)) r)).map fCurrent) := by
    simp [List.map_map]
  rw [hseries]
  rw [mixed_current_coeff_allocations]
  have hlen : ((List.finRange n).map fun i =>
      (fun r => ρ.op (radicalColour (shape i)) r)).length = n := by
    simp
  simp only [hlen]
  have hsum (ts : List (Module.End ℂ V)) :
      ts.sum w = (ts.map fun T => T w).sum := by
    induction ts with
    | nil => simp
    | cons T ts ih => simp [ih, LinearMap.add_apply]
  rw [hsum]
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro modes hm
  rw [radicalWord_eq_prod]
  congr 1
  simp [List.zip_map_left, List.map_map, Function.comp_def, Prod.map]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyz_hsymm_evaluation_current
