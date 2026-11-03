import VOA.DeligneAudit.DeligneFusionCVBound

/-!
# Same-root CV relations for a last-mode descendant

If a current highest-weight vector has CV partition `μ ++ 1^j`, with `j ≥ 2`,
then its last-mode descendant has CV partition `μ ++ 1^(j-2)`.

This is the minus-side relation argument from `CVsl2.cv_step`, specialized to
the last part one and separated from every dimension estimate. It supplies
the same-root relations for the first kernel generator in the enlarged A₂
CV family. Cross-root relations and source-module upper bounds remain separate.
-/

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.CVPart

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V} {y : V}

/-- The minus-side CV relation for a partition whose final two parts are one.
No finite-dimensionality or dimension-bound hypothesis is used. -/
theorem cvrel_kernel_last_one (μ : List ℕ) (c : ℕ)
    (hS : SL2 E H F) (hE : ∀ s, E s y = 0)
    (hH : ∀ p, 1 ≤ p → H p y = 0) (hR : CVRel F (P μ c 1 1) y) :
    CVRel F (Pm μ c 1 1) (F (μ.length + c + 1) y) := by
  let L1 := μ.length + c + 1
  have hFhigh : ∀ q, L1 + 1 ≤ q → F q y = 0 := by
    intro q hq
    have hz := hR 1 q (μ.length + c + 2) le_rfl
      (by rw [T_P_high μ c 1 1 _ le_rfl]; dsimp [L1] at hq; omega)
    rwa [Q_one] at hz
  obtain ⟨hE', hH', hF'⟩ :=
    hw_Fb hS.hEF hS.hHF hS.hFF (b := L1) (by dsimp [L1]; omega) hE hH hFhigh
  have hL : ∀ q, μ.length + c + 2 ≤ q → F q y = 0 :=
    fun q hq => hFhigh q (by dsimp [L1]; omega)
  have hL' : ∀ q, μ.length + c + 2 ≤ q → F q (F L1 y) = 0 :=
    fun q hq => hF' q (by dsimp [L1]; omega)
  have e1 : μ.length + c + 2 - 1 = L1 := by simp [L1]
  have e2 : μ.length + c + 2 - 2 = μ.length + c := by omega
  have htop : (F L1 ^ 2) y = 0 := by
    have ht := Q_top hS.hFF hL 2
    rw [e1] at ht
    rw [← ht]
    refine hR 2 _ L1 (by omega) ?_
    change 1 + 2 * (μ.length + c + 1) + T (μ.length + c + 1) (P μ c 1 1) ≤ _
    rw [show μ.length + c + 1 = μ.length + (c + 1) by omega,
      T_P_mid μ c 1 1 (c + 1) le_rfl]
    omega
  intro r s k hr h
  change Q F r s (F L1 y) = 0
  by_cases hk : k ≤ μ.length + c
  · have hT := (T_minus μ c 1 (b := 1) le_rfl k).1 hk
    have hX := shift_iter hS.hEF hS.hHF hS.hHE hS.hFF hS.hEE
      k (T k (P μ c 1 1)) L1 (by dsimp [L1]; omega) 1 y
      hE hH hFhigh
      (fun r s hr h => X_zero_of_Q hS.hEF hS.hHF hS.hFF hE hH hr (hR r s k hr h))
      r s hr (by omega)
    simp only [pow_one] at hX
    exact Q_zero_of_X hS.hEF hS.hHF hS.hFF hE' hH' hr hX
  · have hT := (T_minus μ c 1 (b := 1) le_rfl k).2 (by omega)
    have hrk : r * (μ.length + c + 1) ≤ r * k :=
      Nat.mul_le_mul_left r (by omega)
    have hmem := Q_div hS.hFF hL' r 1 s (by rw [e2]; nlinarith)
    rw [e1, pow_one, ← Module.End.mul_apply, ← pow_two, htop, Fspan_zero] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem

/-- Removing the last two parts one gives the same-root CV relations of the
last-mode descendant. The prefix need not satisfy any extra shape hypothesis. -/
theorem cvrel_trailing_ones (μ : List ℕ) (j : ℕ) (hj : 2 ≤ j)
    (hS : SL2 E H F) (hE : ∀ s, E s y = 0)
    (hH : ∀ p, 1 ≤ p → H p y = 0)
    (hR : CVRel F (μ ++ List.replicate j 1) y) :
    CVRel F (μ ++ List.replicate (j - 2) 1) (F (μ.length + j - 1) y) := by
  have hP : P μ (j - 2) 1 1 = μ ++ List.replicate j 1 := by
    simp only [P, ← List.replicate_succ', show j - 2 + 1 + 1 = j by omega]
  have hPm : Pm μ (j - 2) 1 1 = μ ++ List.replicate (j - 2) 1 := by
    simp [Pm]
  have hR' : CVRel F (P μ (j - 2) 1 1) y := by rwa [hP]
  have h := cvrel_kernel_last_one μ (j - 2) hS hE hH hR'
  rw [hPm, show μ.length + (j - 2) + 1 = μ.length + j - 1 by omega] at h
  exact h

end

end VOA.DeligneAudit.CVsl2

#print axioms VOA.DeligneAudit.CVsl2.cvrel_kernel_last_one
#print axioms VOA.DeligneAudit.CVsl2.cvrel_trailing_ones
