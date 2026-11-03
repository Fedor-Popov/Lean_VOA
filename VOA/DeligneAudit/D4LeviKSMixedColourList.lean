import VOA.DeligneAudit.D4LeviKSMixedHsymmCurrent

/-! The mixed-current identity with a concrete list of radical colours. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xyz_hsymm_evaluation_colourList
    (ρ : CurrentModule D4sector.f V) (w : V)
    (cs : List (Fin 6)) (s : ℕ) :
    xyzEvaluation ρ w cs.get (hsymm (Fin cs.length) ℂ s) =
      (PowerSeries.coeff s
        ((cs.map fun j => fCurrent (fun r =>
          ρ.op (radicalColour j) r)).prod)) w := by
  rw [xyz_hsymm_evaluation_current]
  have h : (List.finRange cs.length).map cs.get = cs := by
    simpa [List.ofFn_eq_map] using List.ofFn_get cs
  have hmap :
      (List.finRange cs.length).map (fun i =>
        fCurrent (fun r => ρ.op (radicalColour (cs.get i)) r)) =
      cs.map (fun j => fCurrent (fun r => ρ.op (radicalColour j) r)) := by
    calc
      _ = ((List.finRange cs.length).map cs.get).map
          (fun j => fCurrent (fun r => ρ.op (radicalColour j) r)) := by
            simp only [List.map_map, Function.comp_def]
      _ = _ := congrArg _ h
  rw [hmap]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyz_hsymm_evaluation_colourList
