import VOA.DeligneAudit.DeligneFusionCVKernelHW
import VOA.DeligneAudit.DeligneFusionCVShort

/-!
# The CV quotient presentation after killing the two kernel generators

Merging the last two parts one into a part two is realized, in the
current highest-weight setting, by adding the new last-mode truncation.
The construction proved here gives the auxiliary CV presentation
obtained by killing both simple-root kernel generators. It uses actual
coefficient relations, without a universal-module or dimension assumption.
-/

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.A2.CVFamily

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V} {w : V}

/-- Adding the new last-mode relation merges the final two parts one into
a part two. All higher coefficients follow from the short CV criterion. -/
theorem cvrel_merge_last_two_ones (r n e : ℕ)
    (hS : SL2 E H F) (hE : ∀ s, E s w = 0)
    (hH : ∀ p, 1 ≤ p → H p w = 0)
    (hCV : CVRel F (parts r n (e + 2)) w)
    (htop : F (r + n + e + 1) w = 0) :
    CVRel F (parts r (n + 1) e) w := by
  apply cvrel_parts123 r (n + 1) e hS hE hH
  · have hn := VOA.DeligneAudit.A2.CVKernelHW.cvrel_zero_nil hCV
    rw [VOA.DeligneAudit.A2.CVKernelHW.parts_sum] at hn
    rw [show 3 * r + 2 * (n + 1) + e + 1 = 3 * r + 2 * n + (e + 2) + 1 by omega]
    exact hn
  · intro q hq
    by_cases heq : q = r + n + e + 1
    · simpa only [heq] using htop
    · apply trunc_of_cvrel hCV q
      rw [parts_length]
      omega
  · intro s hs
    apply hCV 2 s (r + n) (by omega)
    rw [parts_tail]
    omega

/-- Splitting a part two back into two parts one weakens the CV relations.
The shorter presentation also supplies precisely the additional top mode. -/
theorem cvrel_split_last_two_ones (r n e : ℕ)
    (hS : SL2 E H F) (hE : ∀ s, E s w = 0)
    (hH : ∀ p, 1 ≤ p → H p w = 0)
    (hCV : CVRel F (parts r (n + 1) e) w) :
    CVRel F (parts r n (e + 2)) w ∧ F (r + n + e + 1) w = 0 := by
  have hlin : ∀ q, r + n + e + 1 ≤ q → F q w = 0 := by
    intro q hq
    apply trunc_of_cvrel hCV q
    rw [parts_length]
    omega
  refine ⟨?_, hlin _ le_rfl⟩
  apply cvrel_parts123 r n (e + 2) hS hE hH
  · have hn := VOA.DeligneAudit.A2.CVKernelHW.cvrel_zero_nil hCV
    rw [VOA.DeligneAudit.A2.CVKernelHW.parts_sum] at hn
    rw [show 3 * r + 2 * n + (e + 2) + 1 = 3 * r + 2 * (n + 1) + e + 1 by omega]
    exact hn
  · intro q hq
    exact hlin q (by omega)
  · intro s hs
    apply hCV 2 s (r + (n + 1)) (by omega)
    rw [parts_tail]
    omega

/-- The shorter CV presentation is exactly the longer one together with
the new top-mode relation, in the current highest-weight setting. -/
theorem cvrel_merge_last_two_ones_iff (r n e : ℕ)
    (hS : SL2 E H F) (hE : ∀ s, E s w = 0)
    (hH : ∀ p, 1 ≤ p → H p w = 0) :
    CVRel F (parts r (n + 1) e) w ↔
      CVRel F (parts r n (e + 2)) w ∧ F (r + n + e + 1) w = 0 := by
  constructor
  · exact cvrel_split_last_two_ones r n e hS hE hH
  · rintro ⟨hCV, htop⟩
    exact cvrel_merge_last_two_ones r n e hS hE hH hCV htop

end VOA.DeligneAudit.CVsl2

namespace VOA.DeligneAudit.A2.CVFamily

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight} {k : ℕ}

/-- Killing the two simple-root kernel generators gives the complete CV
quotient presentation. This holds for every epsilon and auxiliary weight. -/
theorem quotient_rel (h : CV3Rel R w ε ν ϱ (k + 2))
    (htop1 : R.op 3 (ε.1 + ν.1 + ϱ.1 + k + 1) w = 0)
    (htop2 : R.op 4 (ε.2 + ν.2 + ϱ.2 + k + 1) w = 0) :
    CV3Rel R w ε (ν + (1, 1)) ϱ k := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R.op 6 0 w = ((ε.1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + k : ℕ) : ℂ) • w
    rw [show ε.1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + k =
      ε.1 + 2 * ν.1 + 3 * ϱ.1 + (k + 2) by omega]
    exact h.cartan_first
  · change R.op 7 0 w = ((ε.2 + 2 * (ν.2 + 1) + 3 * ϱ.2 + k : ℕ) : ℂ) • w
    rw [show ε.2 + 2 * (ν.2 + 1) + 3 * ϱ.2 + k =
      ε.2 + 2 * ν.2 + 3 * ϱ.2 + (k + 2) by omega]
    exact h.cartan_second
  · change (R.op 3 0)^[ε.1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + k + 1] w = 0
    rw [show ε.1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + k + 1 =
      ε.1 + 2 * ν.1 + 3 * ϱ.1 + (k + 2) + 1 by omega]
    exact h.lowering_first
  · change (R.op 4 0)^[ε.2 + 2 * (ν.2 + 1) + 3 * ϱ.2 + k + 1] w = 0
    rw [show ε.2 + 2 * (ν.2 + 1) + 3 * ϱ.2 + k + 1 =
      ε.2 + 2 * ν.2 + 3 * ϱ.2 + (k + 2) + 1 by omega]
    exact h.lowering_second
  · change CVRel (R.op 3) (parts ϱ.1 (ν.1 + 1) (ε.1 + k)) w
    apply cvrel_merge_last_two_ones ϱ.1 ν.1 (ε.1 + k) (CVRoots.sl2_first R)
      (fun s => h.raising 0 (by decide) s)
      (fun p hp => h.cartan_pos 6 (by decide) p hp)
    · simpa only [Nat.add_assoc] using h.first
    · rw [show ϱ.1 + ν.1 + (ε.1 + k) + 1 = ε.1 + ν.1 + ϱ.1 + k + 1 by omega]
      exact htop1
  · change CVRel (R.op 4) (parts ϱ.2 (ν.2 + 1) (ε.2 + k)) w
    apply cvrel_merge_last_two_ones ϱ.2 ν.2 (ε.2 + k) (CVRoots.sl2_second R)
      (fun s => h.raising 1 (by decide) s)
      (fun p hp => h.cartan_pos 7 (by decide) p hp)
    · simpa only [Nat.add_assoc] using h.second
    · rw [show ϱ.2 + ν.2 + (ε.2 + k) + 1 = ε.2 + ν.2 + ϱ.2 + k + 1 by omega]
      exact htop2
  · change CVRel (R.op 5)
      (parts (ϱ.1 + ϱ.2) ((ν.1 + 1) + (ν.2 + 1) + k) (ε.1 + ε.2)) w
    rw [show (ν.1 + 1) + (ν.2 + 1) + k = ν.1 + ν.2 + (k + 2) by omega]
    exact h.highest

/-- Conversely, the proposed quotient presentation has exactly the original
relations and the two additional simple-root top-mode relations. -/
theorem quotient_rel_iff :
    CV3Rel R w ε (ν + (1, 1)) ϱ k ↔
      CV3Rel R w ε ν ϱ (k + 2) ∧
        R.op 3 (ε.1 + ν.1 + ϱ.1 + k + 1) w = 0 ∧
        R.op 4 (ε.2 + ν.2 + ϱ.2 + k + 1) w = 0 := by
  constructor
  · intro h
    have h1 := cvrel_split_last_two_ones ϱ.1 ν.1 (ε.1 + k) (CVRoots.sl2_first R)
      (fun s => h.raising 0 (by decide) s)
      (fun p hp => h.cartan_pos 6 (by decide) p hp) h.first
    have h2 := cvrel_split_last_two_ones ϱ.2 ν.2 (ε.2 + k) (CVRoots.sl2_second R)
      (fun s => h.raising 1 (by decide) s)
      (fun p hp => h.cartan_pos 7 (by decide) p hp) h.second
    have htop1 : R.op 3 (ε.1 + ν.1 + ϱ.1 + k + 1) w = 0 := by
      rw [show ε.1 + ν.1 + ϱ.1 + k + 1 = ϱ.1 + ν.1 + (ε.1 + k) + 1 by omega]
      exact h1.2
    have htop2 : R.op 4 (ε.2 + ν.2 + ϱ.2 + k + 1) w = 0 := by
      rw [show ε.2 + ν.2 + ϱ.2 + k + 1 = ϱ.2 + ν.2 + (ε.2 + k) + 1 by omega]
      exact h2.2
    refine ⟨⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, htop1, htop2⟩
    · rw [show ε.1 + 2 * ν.1 + 3 * ϱ.1 + (k + 2) =
        ε.1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + k by omega]
      exact h.cartan_first
    · rw [show ε.2 + 2 * ν.2 + 3 * ϱ.2 + (k + 2) =
        ε.2 + 2 * (ν.2 + 1) + 3 * ϱ.2 + k by omega]
      exact h.cartan_second
    · rw [show ε.1 + 2 * ν.1 + 3 * ϱ.1 + (k + 2) + 1 =
        ε.1 + 2 * (ν.1 + 1) + 3 * ϱ.1 + k + 1 by omega]
      exact h.lowering_first
    · rw [show ε.2 + 2 * ν.2 + 3 * ϱ.2 + (k + 2) + 1 =
        ε.2 + 2 * (ν.2 + 1) + 3 * ϱ.2 + k + 1 by omega]
      exact h.lowering_second
    · simpa only [Nat.add_assoc] using h1.1
    · simpa only [Nat.add_assoc] using h2.1
    · rw [show ν.1 + ν.2 + (k + 2) = (ν.1 + 1) + (ν.2 + 1) + k by omega]
      exact h.highest
  · rintro ⟨h, htop1, htop2⟩
    exact quotient_rel h htop1 htop2

end VOA.DeligneAudit.A2.CVFamily

#print axioms VOA.DeligneAudit.CVsl2.cvrel_merge_last_two_ones
#print axioms VOA.DeligneAudit.A2.CVFamily.quotient_rel
#print axioms VOA.DeligneAudit.CVsl2.cvrel_merge_last_two_ones_iff
#print axioms VOA.DeligneAudit.A2.CVFamily.quotient_rel_iff
