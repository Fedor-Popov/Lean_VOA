import VOA.DeligneAudit.DeligneFusionCVKernel
import VOA.DeligneAudit.DeligneFusionCVKernelQuotient
import VOA.DeligneAudit.DeligneFusionCVSymmetry

/-!
# The complete second auxiliary CV kernel source in the quotient

The checked Dynkin symmetry supplies the highest-weight relations and sharp
nilpotence of the second kernel generator. After quotienting by the first
generator, the stronger linear and quadratic relations give the second
source presentation in SRK's zero-epsilon recurrence.

Every target relation is derived from the source presentation and the actual
quotient relation. No dimension bound, kernel map, or target presentation is
assumed here.
-/

namespace VOA.DeligneAudit.A2.CVFamily

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight} {j : ℕ}

/-- The second generator satisfies the diagram-symmetric fundamental source
presentation even before quotienting by the first generator. -/
theorem second_kernel_rel_fundamental (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j) :
    CV3Rel R (R.op 4 (ν.2 + ϱ.2 + j - 1) w)
      (1, 0) (ν + (1, 0)) ϱ (j - 2) := by
  have hs := first_kernel_rel_zero (CVSymmetry.cv3Rel_swap h) hj
  have hb := CVSymmetry.cv3Rel_swap hs
  simpa only [CVSymmetry.swapRep_swapRep, CVSymmetry.swapRep_op3,
    Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero,
    Nat.add_zero, Nat.zero_add] using hb

/-- The quotient's stronger first-root relations give its full first-root CV
partition, with one extra part three and two fewer parts one. -/
theorem second_kernel_first_cv (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0) :
    CVRel (R.op 3) (parts (ϱ.1 + 1) ν.1 (j - 2))
      (R.op 4 (ν.2 + ϱ.2 + j - 1) w) := by
  have hf := second_kernel_rel_fundamental h hj
  apply cvrel_parts123 (ϱ.1 + 1) ν.1 (j - 2) (CVRoots.sl2_first R)
    (fun s => hf.raising 0 (by decide) s)
    (fun p hp => hf.cartan_pos 6 (by decide) p hp)
  · rw [Module.End.pow_apply]
    rw [show 3 * (ϱ.1 + 1) + 2 * ν.1 + (j - 2) + 1 =
      1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + (j - 2) + 1 by omega]
    exact hf.lowering_first
  · intro q hq
    exact CVKernelQuotient.second_kernel_first_trunc h hj hfirst q (by omega)
  · intro s hs
    exact CVKernelQuotient.second_kernel_first_quadratic h hj hfirst s (by omega)

/-- The quotient's improved highest-root linear cutoff supplies its full
highest-root CV partition; no quadratic coefficient survives that cutoff. -/
theorem second_kernel_highest_cv (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0) :
    CVRel (R.op 5) (parts (ϱ.1 + ϱ.2 + 1) (ν.1 + ν.2 + (j - 2)) 0)
      (R.op 4 (ν.2 + ϱ.2 + j - 1) w) := by
  have hf := second_kernel_rel_fundamental h hj
  let L := (ϱ.1 + ϱ.2 + 1) + (ν.1 + ν.2 + (j - 2))
  have htr : ∀ q, L ≤ q →
      R.op 5 q (R.op 4 (ν.2 + ϱ.2 + j - 1) w) = 0 := by
    intro q hq
    exact CVKernelQuotient.second_kernel_theta_trunc h hj hfirst q
      (by dsimp [L] at hq; omega)
  apply cvrel_parts123 (ϱ.1 + ϱ.2 + 1) (ν.1 + ν.2 + (j - 2)) 0
    (CVRoots.sl2_highest R) (fun s => hf.raising 2 (by decide) s)
  · intro p hp
    simp only [LinearMap.add_apply, hf.cartan_pos 6 (by decide) p hp,
      hf.cartan_pos 7 (by decide) p hp, add_zero]
  · have hn := CVKernelHW.cvrel_zero_nil hf.highest
    rw [CVKernelHW.parts_sum] at hn
    change (R.op 5 0 ^
      (3 * (ϱ.1 + ϱ.2) + 2 * ((ν.1 + 1) + ν.2 + (j - 2)) + 1 + 1)) _ = 0 at hn
    rw [show 3 * (ϱ.1 + ϱ.2 + 1) + 2 * (ν.1 + ν.2 + (j - 2)) + 0 + 1 =
      3 * (ϱ.1 + ϱ.2) + 2 * ((ν.1 + 1) + ν.2 + (j - 2)) + 1 + 1 by omega]
    exact hn
  · intro q hq
    exact htr q (by simpa only [Nat.add_zero] using hq)
  · intro s hs
    exact Q_high (CVRoots.sl2_highest R).hFF htr 2 s
      (by dsimp only [L]; omega)

/-- The second kernel generator satisfies the complete smaller zero-epsilon
presentation after the first generator has been set to zero. This establishes
all source relations; it assumes no dimension or kernel-map conclusion. -/
theorem second_kernel_rel_zero (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (hfirst : R.op 3 (ν.1 + ϱ.1 + j - 1) w = 0) :
    CV3Rel R (R.op 4 (ν.2 + ϱ.2 + j - 1) w)
      (0, 0) ν (ϱ + (1, 0)) (j - 2) := by
  have hf := second_kernel_rel_fundamental h hj
  refine ⟨hf.raising, hf.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R.op 6 0 _ = ((0 + 2 * ν.1 + 3 * (ϱ.1 + 1) + (j - 2) : ℕ) : ℂ) • _
    rw [show 0 + 2 * ν.1 + 3 * (ϱ.1 + 1) + (j - 2) =
      1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + (j - 2) by omega]
    exact hf.cartan_first
  · simpa only [Prod.snd_add, Nat.add_zero] using hf.cartan_second
  · change (R.op 3 0)^[0 + 2 * ν.1 + 3 * (ϱ.1 + 1) + (j - 2) + 1] _ = 0
    rw [show 0 + 2 * ν.1 + 3 * (ϱ.1 + 1) + (j - 2) + 1 =
      1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + (j - 2) + 1 by omega]
    exact hf.lowering_first
  · simpa only [Prod.snd_add, Nat.add_zero] using hf.lowering_second
  · simpa only [Prod.fst_add, Nat.zero_add] using second_kernel_first_cv h hj hfirst
  · simpa only [Prod.snd_add, Nat.add_zero] using hf.second
  · change CVRel (R.op 5)
      (parts ((ϱ.1 + 1) + ϱ.2) (ν.1 + ν.2 + (j - 2)) (0 + 0)) _
    rw [show (ϱ.1 + 1) + ϱ.2 = ϱ.1 + ϱ.2 + 1 by omega, Nat.zero_add]
    exact second_kernel_highest_cv h hj hfirst

end VOA.DeligneAudit.A2.CVFamily

#print axioms VOA.DeligneAudit.A2.CVFamily.second_kernel_rel_fundamental
#print axioms VOA.DeligneAudit.A2.CVFamily.second_kernel_first_cv
#print axioms VOA.DeligneAudit.A2.CVFamily.second_kernel_highest_cv
#print axioms VOA.DeligneAudit.A2.CVFamily.second_kernel_rel_zero
