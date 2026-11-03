import VOA.DeligneAudit.D4FusionContactAllMCountResearchCartanQuadratic

/-! # Only the nearest middle pair survives the refined Cartan shift

This is an actual derivation statement on the strict middle subspace.
It supplies the finite color-space boundary for the refined wheel's
leading polynomial, without presuming its normal-form coverage.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

/-- The finite color space at the two adjacent top modes. -/
def nearestTopSpan : Submodule ℂ (MvPolynomial (Vars m) ℂ) :=
  Submodule.span ℂ (Set.range fun x : Fin 9 × Fin 9 =>
    modeX m x.1 b.top.val * modeX m x.2 (b.top.val-1))

theorem nearest_top_product_mem (i j : Fin 9) :
    modeX m i b.top.val * modeX m j (b.top.val-1) ∈ nearestTopSpan b :=
  Submodule.subset_span ⟨(i,j),rfl⟩

/-- Among strict middle modes, only p+1 can survive shift q-p-1. -/
theorem refinement_modeX (i : Fin 9) (r : ℕ) (hr : b.lower.val < r) :
    modeX m i (b.top.val-b.lower.val-1+r) =
      if r = b.lower.val + 1 then modeX m i b.top.val else 0 := by
  have hlt := b.lt
  have hlast := b.last
  by_cases he : r = b.lower.val + 1
  · have hs : b.top.val-b.lower.val-1+r = b.top.val := by omega
    rw [hs,if_pos he]
  · have hs : ¬ b.top.val-b.lower.val-1+r < m := by omega
    rw [if_neg he,modeX,dif_neg hs]

theorem h0Deriv_middle_X (x : Vars m) (hx : b.lower.val < x.2.val) :
    g0Deriv m 0 (refinementMode b).val (MvPolynomial.X x) =
      if x.2.val = b.lower.val + 1 then
        (h0Weight x.1 : ℂ) • modeX m x.1 b.top.val else 0 := by
  have hh := h0Deriv_modeX m (refinementMode b).val x.2.val x.1
  simp only [modeX,dif_pos x.2.isLt,Fin.eta] at hh
  rw [hh]
  change (h0Weight x.1 : ℂ) • modeX m x.1
    (b.top.val-b.lower.val-1+x.2.val) = _
  rw [refinement_modeX b x.1 x.2.val hx]
  split_ifs <;> simp

/-- The complementary mode is q-1 whenever a middle mode can be hit. -/
theorem middle_mode_complement (z : MiddlePair b)
    (hz : z.left.2.val = b.lower.val + 1) : z.right.2.val = b.top.val-1 := by
  have := z.mode_sum
  omega

theorem h0_middle_product_mem (z : MiddlePair b) :
    MvPolynomial.X z.right * g0Deriv m 0 (refinementMode b).val
      (MvPolynomial.X z.left) ∈ nearestTopSpan b := by
  rw [h0Deriv_middle_X b z.left z.left_lower]
  by_cases hz : z.left.2.val = b.lower.val + 1
  · rw [if_pos hz,mul_smul_comm,mul_comm]
    have he : MvPolynomial.X z.right = modeX m z.right.1 (b.top.val-1) := by
      rw [← middle_mode_complement b z hz]
      simp only [modeX,dif_pos z.right.2.isLt,Fin.eta]
    rw [he]
    exact (nearestTopSpan b).smul_mem _ (nearest_top_product_mem b z.left.1 z.right.1)
  · rw [if_neg hz,mul_zero]
    exact (nearestTopSpan b).zero_mem

/-- Every surviving middle correction lies in the same adjacent-top color space. -/
theorem h0Deriv_middle_nearest {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ middleSpan b) :
    g0Deriv m 0 (refinementMode b).val p ∈ nearestTopSpan b := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨z,rfl⟩ := hp
      rw [(g0Deriv m 0 (refinementMode b).val).leibniz]
      simp only [smul_eq_mul]
      apply (nearestTopSpan b).add_mem
      · exact h0_middle_product_mem b {
          left := z.right, right := z.left,
          left_lower := z.right_lower, left_upper := z.right_upper,
          right_lower := z.left_lower, right_upper := z.left_upper,
          mode_sum := by simpa only [Nat.add_comm] using z.mode_sum}
      · exact h0_middle_product_mem b z
  | zero => rw [map_zero]; exact (nearestTopSpan b).zero_mem
  | add p q _ _ ihp ihq => simpa only [map_add] using (nearestTopSpan b).add_mem ihp ihq
  | smul a p _ ih =>
      simpa only [Derivation.map_smul] using (nearestTopSpan b).smul_mem a ih

theorem h0Deriv_middleSeed_nearest :
    g0Deriv m 0 (refinementMode b).val (middleSeed b) ∈ nearestTopSpan b :=
  h0Deriv_middle_nearest b (middleSeed_mem b)

end

#print axioms refinement_modeX
#print axioms h0Deriv_middle_nearest
#print axioms h0Deriv_middleSeed_nearest

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
