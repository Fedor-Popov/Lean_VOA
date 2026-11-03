/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionSecondWard

/-!
# Ward equations at any nonresonant parameter

The defect argument needs invertibility of finitely many ordinary scalar
diagonals, not a nonreal parameter. This version applies to any actual
preterminal sequence, including the directly constructed rational one.
It does not assert that the terminal state is nonzero.
-/
namespace VOA.InverseDS.VirasoroVerma
section
variable (h b t : ℂ) (N R : ℕ) (ht : t≠0) (hN : 3≤N)
  (f : wardSequenceSpace (vermaBSACharge t) h)
  (hf : ∀ r<R, (wardSourceAt (vermaBSACharge t) h b t (vermaBSAWeight N t) N f).val r=0)
  (hd : ∀ r, 0<r → r<R → wardBSASourceDiagonal h b t N r N (vermaBSAWeight N t+(N:ℂ))≠0)

include ht hN hf hd

/-- Interior diagonal invertibility forces the first input defect to
vanish through the penultimate preterminal coefficient. -/
theorem nonresonant_first_below : ∀ r<R-1,
    (wardP1Map (vermaBSACharge t) h b (vermaBSAWeight N t) f).val r=0 := by
  apply ward_zero_of_source_zero _ _
    (wardSourceAt (vermaBSACharge t) h b t (vermaBSAWeight N t-1) N)
    (fun r => wardBSASourceDiagonal h b t N r N ((vermaBSAWeight N t-1)+(N:ℂ)))
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · intro r hr
    rw [wardSourceDiagonal_shift_one]
    exact hd (r+1) (by omega) (by omega)
  · intro r hr
    rw [← wardSourceAt_first_defect _ _ _ t N ht (by omega)]
    change vermaMode _ _ 1 _-(_ : ℂ) • _=0
    rw [hf (r+1) (by omega),hf r (by omega),map_zero,smul_zero,sub_zero]

/-- Consequently the entire second-defect correction vanishes in the
range needed for the terminal L2 equation. -/
theorem nonresonant_error_below : ∀ r<R-1,
    (wardSourceErrorAt (vermaBSACharge t) h b t (vermaBSAWeight N t) N f).val r=0 := by
  intro r hr
  exact wardSecondSourceError_below _ _ _ _ N N _ (R-1)
    (wardFieldLift_below _ _ _ _ _ (nonresonant_first_below h b t N R ht hN f hf hd)) _ r hr

/-- The second input defect vanishes below R-2 by the shifted diagonal
and the already proved first-defect error bound. -/
theorem nonresonant_second_below : ∀ r<R-2,
    (wardP2Map (vermaBSACharge t) h b (vermaBSAWeight N t) f).val r=0 := by
  apply ward_zero_of_source_zero _ _
    (wardSourceAt (vermaBSACharge t) h b t (vermaBSAWeight N t-2) N)
    (fun r => wardBSASourceDiagonal h b t N r N ((vermaBSAWeight N t-2)+(N:ℂ)))
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · intro r hr
    rw [wardSourceDiagonal_shift_two]
    exact hd (r+2) (by omega) (by omega)
  · intro r hr
    have hh := wardSourceAt_second_defect h b t N ht hN f
    have he := congrArg (fun g : wardSequenceSpace (vermaBSACharge t) h => g.val r) hh
    dsimp only at he
    simp only [Submodule.coe_add,Pi.add_apply] at he
    change vermaMode _ _ 2 _-(_ : ℂ) • _-(3:ℂ) • (vermaMode _ _ 1 _-(_ : ℂ) • _)=_ at he
    rw [hf (r+2) (by omega),hf (r+1) (by omega),hf r (by omega),
      nonresonant_error_below h b t N R ht hN f hf hd r (by omega)] at he
    simpa only [map_zero,smul_zero,sub_zero,add_zero] using he.symm

/-- A terminal diagonal zero gives the actual L1 equation for any
preterminal sequence at any parameter meeting ordinary nonresonance. -/
theorem nonresonant_terminal_L1 (hR : 0<R)
    (hz : wardBSASourceDiagonal h b t N R N (vermaBSAWeight N t+(N:ℂ))=0) :
    vermaMode (vermaBSACharge t) h 1
      ((wardSourceAt (vermaBSACharge t) h b t (vermaBSAWeight N t) N f).val R)=0 := by
  have hh := wardSourceAt_first_defect (vermaBSACharge t) h b t N ht (by omega) f
  have he := congrArg (fun g : wardSequenceSpace (vermaBSACharge t) h => g.val (R-1)) hh
  dsimp only at he
  rw [wardSourceAt_diagonal _ _ _ _ _ _ _ _
    (nonresonant_first_below h b t N R ht hN f hf hd),wardSourceDiagonal_shift_one,
    show R-1+1=R by omega,hz,zero_smul] at he
  change vermaMode _ _ 1 _-(_ : ℂ) • _=0 at he
  rw [hf (R-1) (by omega),smul_zero,sub_zero] at he
  simpa only [show R-1+1=R by omega] using he

/-- The analogous actual L2 equation includes and discharges the complete
second-defect correction. No primary-seed assumption enters. -/
theorem nonresonant_terminal_L2 (hR : 2≤R)
    (hz : wardBSASourceDiagonal h b t N R N (vermaBSAWeight N t+(N:ℂ))=0) :
    vermaMode (vermaBSACharge t) h 2
      ((wardSourceAt (vermaBSACharge t) h b t (vermaBSAWeight N t) N f).val R)=0 := by
  have hh := wardSourceAt_second_defect h b t N ht hN f
  have he := congrArg (fun g : wardSequenceSpace (vermaBSACharge t) h => g.val (R-2)) hh
  dsimp only at he
  simp only [Submodule.coe_add,Pi.add_apply] at he
  rw [wardSourceAt_diagonal _ _ _ _ _ _ _ _
    (nonresonant_second_below h b t N R ht hN f hf hd),wardSourceDiagonal_shift_two,
    show R-2+2=R by omega,hz,zero_smul] at he
  change vermaMode _ _ 2 _-(_ : ℂ) • _-(3:ℂ) • (vermaMode _ _ 1 _-(_ : ℂ) • _)=_ at he
  rw [hf (R-2) (by omega),hf (R-2+1) (by omega),
    nonresonant_error_below h b t N R ht hN f hf hd (R-2) (by omega)] at he
  simpa only [show R-2+2=R by omega,smul_zero,map_zero,sub_zero,add_zero] using he
end
end VOA.InverseDS.VirasoroVerma
