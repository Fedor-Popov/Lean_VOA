/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumFusionRecursion

/-!
# The actual quartic vacuum fusion recurrence

At seed index four the full vacuum projection has three terms: the
current coefficient, the coefficient two levels earlier, and the one
four levels earlier. The last multiplier is -t/16. This computation is
an actual projection identity and does not assert terminal nonvanishing.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The quartic source's two-level-earlier coefficient. Its field weight
and incoming highest weight remain explicit for later specializations. -/
noncomputable def vacuumFourSubdiagonal (b t a : ℂ) (r : ℕ) : ℂ :=
  t/4*((r:ℂ)-2*b-a-2)+
    5*t^2/36*((r:ℂ)-b-a-2)*((r:ℂ)-b-a-3)

set_option maxHeartbeats 1000000 in
/-- Expanding the full finite scalar recursion gives the exact quartic
three-term formula. The four-level-earlier contribution is nonzero
whenever t is nonzero, but cancellation between the other terms can occur. -/
theorem wardBSAVacuumSource_four (b t a : ℂ) (u : ℕ → ℂ) (r : ℕ) :
    wardBSAVacuumSource b t a 4 4 u (r+4)=
      wardBSASourceDiagonal 0 b t 4 (r+4) 4 (a+4)*u (r+4)+
      vacuumFourSubdiagonal b t a (r+4)*u (r+2)-t/16*u r := by
  simp only [wardBSAVacuumSource,wardBSASourceDiagonal,Fin.sum_univ_four]
  iterate 5
    norm_num [wardVacuumStep,wardCreationDiagonal,wardBSAVacuum,wardBSADiagonal,
      show 2≤r+4 by omega, show 2≤r+2 by omega]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [vacuumFourSubdiagonal]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- At level two only the first lower coefficient is present. This is
the initial even-step equation of the quartic vacuum recurrence. -/
theorem wardBSAVacuumSource_four_two (b t a : ℂ) (u : ℕ → ℂ) :
    wardBSAVacuumSource b t a 4 4 u 2=
      wardBSASourceDiagonal 0 b t 4 2 4 (a+4)*u 2+
      vacuumFourSubdiagonal b t a 2*u 0 := by
  simp only [wardBSAVacuumSource,wardBSASourceDiagonal,Fin.sum_univ_four]
  iterate 5
    norm_num [wardVacuumStep,wardCreationDiagonal,wardBSAVacuum,wardBSADiagonal]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [vacuumFourSubdiagonal]
  norm_num
  ring

/-- The quartic three-term scalar formula is the actual survival value
of the operator on any level sequence, with no primary equation assumed. -/
theorem vermaVacuumSurvival_sourceAt_four (c b t a : ℂ)
    (f : wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardSourceAt c 0 b t a 4 f).val (r+4))=
      wardBSASourceDiagonal 0 b t 4 (r+4) 4 (a+4)*
        vermaVacuumSurvival c (f.val (r+4))+
      vacuumFourSubdiagonal b t a (r+4)*vermaVacuumSurvival c (f.val (r+2))-
      t/16*vermaVacuumSurvival c (f.val r) := by
  rw [wardSourceAt_vacuum,wardBSAVacuumSource_four]

end VOA.InverseDS.VirasoroVerma
