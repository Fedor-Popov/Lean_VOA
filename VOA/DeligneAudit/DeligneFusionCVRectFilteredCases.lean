import VOA.DeligneAudit.DeligneFusionCVRectFilteredZero
import VOA.DeligneAudit.DeligneFusionCVRectPBWLeadingSymmetry
import VOA.DeligneAudit.DeligneFusionCVRectPBWPolarizationSaturated

/-!
# Complete finite-case assembly of actual mixed rectangular PBW relations

Highest-root polarization handles both saturated color loads. The actual
simple-root, one-theta, one-first/one-theta, and two-theta source lemmas cover
every remaining case. The final small-epsilon theorem has no leading-ideal
or coefficient-annihilation premise. A reusable intermediate theorem leaves
only its two displayed genuine two-theta boundary families explicit.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectPBWLeading

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight}

theorem clippedSum_parts_saturated (r n e d : ℕ) (hd : 3 ≤ d) :
    clippedSum (parts r n e) d = r * 3 + n * 2 + e := by
  rw [clippedSum_parts, Nat.min_eq_right hd,
    Nat.min_eq_right (by omega : 2 ≤ d), Nat.min_eq_right (by omega : 1 ≤ d), mul_one]

/-- Saturated mixed leading relations are actual consequences of the source
highest-root CV coefficients and checked graded raising action. -/
theorem graded_saturated (h : CV3Rel R w ε ν ϱ 0) (p q r s : ℕ)
    (hL : 3 ≤ p + q) (hR : 3 ≤ q + r)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) (p + q) +
      clippedSum (parts ϱ.2 ν.2 ε.2) (q + r) < s + (p + q + r)) :
    gradedOrderedCoeff R w p q r s = 0 := by
  have hclip : clippedSum (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2) (ε.1 + ε.2)) (p + q + r) =
      clippedSum (parts ϱ.1 ν.1 ε.1) (p + q) +
        clippedSum (parts ϱ.2 ν.2 ε.2) (q + r) := by
    rw [clippedSum_parts_saturated _ _ _ _ (by omega),
      clippedSum_parts_saturated _ _ _ _ hL,
      clippedSum_parts_saturated _ _ _ _ hR]
    omega
  have hCV : CVRel (R.op 5)
      (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2) (ε.1 + ε.2)) w := by
    simpa only [Nat.add_zero] using h.highest
  apply CVRectPBWPolarization.threeCoeff_zero_of_actual_Q R w h p q r s
  exact part_Q_zero_of_clipped (R.op 5) hCV (p + q + r) s (by rwa [hclip])

/-- Reusable actual finite-case classification. The two explicit boundary
families are instantiated below for the small-epsilon rectangular modules,
and can be supplied by stronger actual source relations in other families. -/
theorem graded_all_of_two_theta (h : CV3Rel R w ε ν ϱ 0)
    (hleft : ∀ r s, clippedSum (parts ϱ.1 ν.1 ε.1) 2 +
      clippedSum (parts ϱ.2 ν.2 ε.2) (r + 2) < s + r + 2 →
        gradedOrderedCoeff R w 0 2 r s = 0)
    (hright : ∀ p s, clippedSum (parts ϱ.1 ν.1 ε.1) (p + 2) +
      clippedSum (parts ϱ.2 ν.2 ε.2) 2 < s + p + 2 →
        gradedOrderedCoeff R w p 2 0 s = 0)
    (p q r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) (p + q) +
      clippedSum (parts ϱ.2 ν.2 ε.2) (q + r) < s + (p + q + r)) :
    gradedOrderedCoeff R w p q r s = 0 := by
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ 3 ≤ q by omega) with rfl | rfl | rfl | hq
  · exact (orderedCoeff_mem_iff_zero R w p 0 r s).mp
      (orderedCoeff_zero_theta_mem h p r s (by simpa only [Nat.add_zero, Nat.zero_add] using hs))
  · by_cases hp0 : p = 0
    · subst p
      exact theta_second_one_graded h r s
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs)
    by_cases hp1 : p = 1
    · subst p
      exact first_theta_second h r s
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs)
    by_cases hr0 : r = 0
    · subst r
      exact first_theta_one_graded h p s (by simpa only [Nat.add_zero, Nat.add_assoc] using hs)
    by_cases hr1 : r = 1
    · subst r
      exact first_theta_second_mirror h p s (by simpa only [Nat.add_assoc] using hs)
    exact graded_saturated h p 1 r s (by omega) (by omega) hs
  · by_cases hp0 : p = 0
    · subst p
      exact hleft r s (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs)
    by_cases hr0 : r = 0
    · subst r
      exact hright p s (by simpa only [Nat.add_zero, Nat.add_assoc] using hs)
    exact graded_saturated h p 2 r s (by omega) (by omega) hs
  · exact graded_saturated h p q r s (by omega) (by omega) hs

/-- All actual mixed graded coefficient relations for the three rectangular
base families. Every small-load boundary is supplied by a proved source
lemma; no coefficient-family or leading-ideal hypothesis remains. -/
theorem graded_all_small (h : CV3Rel R w ε ν ϱ 0)
    (hε : ε = (0, 0) ∨ ε = (1, 0) ∨ ε = (0, 1)) (p q r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) (p + q) +
      clippedSum (parts ϱ.2 ν.2 ε.2) (q + r) < s + (p + q + r)) :
    gradedOrderedCoeff R w p q r s = 0 := by
  apply graded_all_of_two_theta h ?_ ?_ p q r s hs
  · intro r s hs
    rcases hε with rfl | rfl | rfl
    · exact theta_second_two_no_one_graded h r s hs
    · exact theta_second_two_one_graded h r s hs
    · exact theta_second_two_no_one_graded h r s hs
  · intro p s hs
    rcases hε with rfl | rfl | rfl
    · exact first_theta_two_no_one_graded h p s hs
    · exact first_theta_two_no_one_graded h p s hs
    · exact first_theta_two_one_graded h p s hs

/-- The complete actual source coefficient-mod-shorter family, obtained from
the checked graded relations by exactness of the original PBW symbols. -/
theorem orderedCoeff_all_small_mem (h : CV3Rel R w ε ν ϱ 0)
    (hε : ε = (0, 0) ∨ ε = (1, 0) ∨ ε = (0, 1)) (p q r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) (p + q) +
      clippedSum (parts ϱ.2 ν.2 ε.2) (q + r) < s + (p + q + r)) :
    orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r) :=
  (orderedCoeff_mem_iff_zero R w p q r s).mpr (graded_all_small h hε p q r s hs)

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.graded_saturated
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.graded_all_of_two_theta
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.orderedCoeff_all_small_mem
