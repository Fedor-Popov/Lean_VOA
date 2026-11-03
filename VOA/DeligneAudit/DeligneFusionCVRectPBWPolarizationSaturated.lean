import VOA.DeligneAudit.DeligneFusionCVRectPBWPolarizationGraded
import VOA.DeligneAudit.DeligneFusionCVRectPBWPolarizationThree
import VOA.DeligneAudit.DeligneFusionCVRectFilteredCoeff

/-!
# Actual highest-root coefficients polarize in the PBW associated graded

The Cartan terms have strictly lower PBW length. The actual restricted
raising operators therefore satisfy the exact hypotheses of the generic
three-color polarization theorem. No mixed coefficient ideal is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWPolarization

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open CVFamily CVRectFiltered VOA.DeligneAudit.CVsl2

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

theorem threeCoeff_zero_of_actual_Q {ε ν ϱ : Weight} {j : ℕ}
    (h : CV3Rel R w ε ν ϱ j) (p q r s : ℕ)
    (hQ : Q (R.op 5) (p + q + r) s w = 0) : gradedOrderedCoeff R w p q r s = 0 := by
  let E₂ := grRaising R w h true
  let E₁ := -grRaising R w h false
  have hE₂Y (k : ℕ) : E₂ * grOp R w 1 k - grOp R w 1 k * E₂ = grOp R w 0 k := by
    simpa only [E₂, grRaisingTail, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero] using
      grRaising_comm R w h true 1 k
  have hE₂X (k : ℕ) : E₂ * grOp R w 0 k = grOp R w 0 k * E₂ := by
    apply sub_eq_zero.mp
    simpa [E₂, grRaisingTail] using grRaising_comm R w h true 0 k
  have hE₁Y (k : ℕ) : E₁ * grOp R w 1 k - grOp R w 1 k * E₁ = grOp R w 2 k := by
    calc
      E₁ * grOp R w 1 k - grOp R w 1 k * E₁ =
          -(grRaising R w h false * grOp R w 1 k -
            grOp R w 1 k * grRaising R w h false) := by dsimp [E₁]; noncomm_ring
      _ = grOp R w 2 k := by rw [grRaising_comm]; simp [grRaisingTail]
  have hE₁X (k : ℕ) : E₁ * grOp R w 0 k = grOp R w 0 k * E₁ := by
    have he : grRaising R w h false * grOp R w 0 k =
        grOp R w 0 k * grRaising R w h false := by
      apply sub_eq_zero.mp
      simpa [grRaisingTail] using grRaising_comm R w h false 0 k
    simpa only [E₁, neg_mul, mul_neg] using congrArg Neg.neg he
  have hE₁Z (k : ℕ) : E₁ * grOp R w 2 k = grOp R w 2 k * E₁ := by
    have he : grRaising R w h false * grOp R w 2 k =
        grOp R w 2 k * grRaising R w h false := by
      apply sub_eq_zero.mp
      simpa [grRaisingTail] using grRaising_comm R w h false 2 k
    simpa only [E₁, neg_mul, mul_neg] using congrArg Neg.neg he
  have hsource : orderedCoeff R w 0 (p + q + r) 0 s = 0 := by
    simpa only [orderedCoeff, pow_zero, one_mul, mul_one, Q] using hQ
  have hsourceGr := gradedOrderedCoeff_zero R w 0 (p + q + r) 0 s (by
    rw [hsource]
    exact Submodule.zero_mem _)
  have hQGr : Q (grOp R w 1) (p + q + r) s (grGenerator R w) = 0 := by
    simpa only [gradedOrderedCoeff, pow_zero, one_mul, mul_one, Q] using hsourceGr
  have hz := CVPolarizationThree.threeCoeff_zero_of_Q
    (grOp R w 0) (grOp R w 1) (grOp R w 2) E₂ E₁
    hE₂Y hE₂X (fun k l => grOp_commute R w 1 0 k l)
    hE₁Y hE₁X hE₁Z (fun k l => grOp_commute R w 1 2 k l)
    (grRaising_generator R w h true)
    (by simp only [E₁, LinearMap.neg_apply, grRaising_generator, neg_zero]) hQGr p q r rfl
  exact hz

end

end VOA.DeligneAudit.A2.CVRectPBWPolarization

#print axioms VOA.DeligneAudit.A2.CVRectPBWPolarization.threeCoeff_zero_of_actual_Q
