import VOA.DeligneAudit.DeligneFusionCVTotal
import VOA.DeligneAudit.DeligneFusionCVResidualThetaZero
import VOA.DeligneAudit.DeligneFusionCVRectFamilyCanonical
import VOA.DeligneAudit.DeligneFusionCVRectMixedUniversal

/-!
# Unconditional one- and two-adjoint total bounds

The actual one-orientation bases and opposite two-rectangle bound supply
every smaller source in the two-adjoint recurrence: 36 + 18 + 10 = 64.
The graded transfer then gives the original degree-sum statement for every
model with the corresponding local Weyl/fusion relations. No total-bound
or sharp-base family is assumed. This does not prove the all-N input.
-/

namespace VOA.DeligneAudit.A2.CVSmall

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open CVFamily CVUniv CVRectFamilyCanonical CVRectMixedUniversal

noncomputable section

theorem left_bound (e n r : ℕ) : CVBound (e, 0) (n, 0) (r, 0) 0 := by
  have hb := univ_one_orientation_bound e n r
  exact ⟨hb.1, by simpa [cvCount] using hb.2⟩

theorem right_bound (e n r : ℕ) : CVBound (0, e) (0, n) (0, r) 0 :=
  (left_bound e n r).swap

theorem one_adjoint_bound : CVBound (0, 0) (0, 0) (0, 0) 1 := by
  have hb := CVResidualThetaZero.universal_adjoint_bound
  exact ⟨hb.1, by simpa [cvCount] using hb.2⟩

/-- The actual three smaller universal modules have the proved bounds
36,18,10, so the two-adjoint case is unconditional. -/
theorem two_adjoint_bound : CVBound (0, 0) (0, 0) (0, 0) 2 := by
  have hT : CVBound (0, 0) (1, 1) (0, 0) 0 := by
    simpa [pairEpsilon, pairNu, pairRho] using
      pair_universal_bound 2 2 (by decide) (by decide) (by decide) (by decide)
  have hA : CVBound (0, 1) (0, 1) (0, 0) 0 := right_bound 1 1 0
  have hB : CVBound (0, 0) (0, 0) (1, 0) 0 := left_bound 0 0 1
  exact cvBound_zero_step (ν := (0, 0)) (ϱ := (0, 0)) (k := 0) hT hA hB

/-- Transfer one actual universal bound to every model, by summing the
separated universal degree pieces before mapping to the target. -/
theorem totalDim_of_bound {m : ℕ} (hC : CVBound (0, 0) (0, 0) (0, 0) m)
    (hm : 0 < m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule bracketTable V) (w : V) (hW : LocalWeylRel R w m) (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤ 8 ^ m := by
  haveI := hC.1
  have hc := mabRel_zero_cv3 ((mabRel_zero_iff R w m).mpr hW) hm
  calc
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤
        ∑ d ∈ Finset.range B, Module.finrank ℂ
          (cycDeg (cvUnivRep (0, 0) (0, 0) (0, 0) m)
            (cv_wU (0, 0) (0, 0) (0, 0) m) d) :=
      Finset.sum_le_sum fun d _ => by
        rw [← map_cycDeg hc d]
        exact Submodule.finrank_map_le _ _
    _ ≤ Module.finrank ℂ (CVMod (0, 0) (0, 0) (0, 0) m) :=
      sum_finrank_cycDeg_le (0, 0) (0, 0) (0, 0) m (Finset.range B)
    _ ≤ 8 ^ m := by simpa only [cvCount, Nat.zero_add, pow_zero, one_mul] using hC.2

theorem totalDim_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule bracketTable V) (w : V) (hW : LocalWeylRel R w 1) (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤ 8 := by
  simpa using totalDim_of_bound one_adjoint_bound (by decide) R w hW B

theorem totalDim_two {V : Type} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule bracketTable V) (w : V) (hW : LocalWeylRel R w 2) (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤ 64 := by
  simpa using totalDim_of_bound two_adjoint_bound (by decide) R w hW B

end

end VOA.DeligneAudit.A2.CVSmall

#print axioms VOA.DeligneAudit.A2.CVSmall.two_adjoint_bound
#print axioms VOA.DeligneAudit.A2.CVSmall.totalDim_one
#print axioms VOA.DeligneAudit.A2.CVSmall.totalDim_two
