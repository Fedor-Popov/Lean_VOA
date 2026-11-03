import VOA.DeligneAudit.D4FusionContactAllMCountResearchCurrentWheel

/-! # Middle-mode correction subspace

This is a linear subspace, not an ideal. Constant Levi derivations
preserve it and every positive shift q-p annihilates it. The grouped
coefficient decomposition is proved without separating source seeds.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

structure MiddlePair where
  left : Vars m
  right : Vars m
  left_lower : b.lower.val < left.2.val
  left_upper : left.2.val < b.top.val
  right_lower : b.lower.val < right.2.val
  right_upper : right.2.val < b.top.val
  mode_sum : left.2.val + right.2.val = b.lower.val + b.top.val

def middleSpan : Submodule ℂ (MvPolynomial (Vars m) ℂ) :=
  Submodule.span ℂ (Set.range fun z : MiddlePair b =>
    MvPolynomial.X z.left * MvPolynomial.X z.right)

theorem middle_product_mem (z : MiddlePair b) :
    MvPolynomial.X z.left * MvPolynomial.X z.right ∈ middleSpan b :=
  Submodule.subset_span ⟨z,rfl⟩

theorem g0Deriv_X_constant (g : Fin 10) (x : Vars m) :
    g0Deriv m g 0 (MvPolynomial.X x) =
      ∑ j : Fin 9, contactF (zeroIndex g) (radIndex x.1) (radIndex j) •
        MvPolynomial.X (j,x.2) := by
  simp [g0Deriv,g0Image,modeX,x.2.isLt]

theorem g0Deriv_middle (g : Fin 10) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ middleSpan b) : g0Deriv m g 0 p ∈ middleSpan b := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨z,rfl⟩ := hp
      rw [(g0Deriv m g 0).leibniz]
      simp only [smul_eq_mul,g0Deriv_X_constant,Finset.mul_sum,mul_smul_comm]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro j _
        exact (middleSpan b).smul_mem _ (middle_product_mem b
          {z with right := (j,z.right.2)})
      · apply Submodule.sum_mem
        intro j _
        exact (middleSpan b).smul_mem _ (middle_product_mem b
          {left := z.right, right := (j,z.left.2),
           left_lower := z.right_lower, left_upper := z.right_upper,
           right_lower := z.left_lower, right_upper := z.left_upper,
           mode_sum := by simpa only [Nat.add_comm] using z.mode_sum})
  | zero => rw [map_zero]; exact (middleSpan b).zero_mem
  | add p q _ _ ihp ihq => simpa only [map_add] using (middleSpan b).add_mem ihp ihq
  | smul a p _ ih => simpa only [Derivation.map_smul] using (middleSpan b).smul_mem a ih

theorem g0Deriv_X_middle_zero (g : Fin 10) (x : Vars m)
    (hx : b.lower.val < x.2.val) :
    g0Deriv m g (b.top.val-b.lower.val) (MvPolynomial.X x) = 0 := by
  have hh : ¬ b.top.val-b.lower.val+x.2.val < m := by
    have := b.last
    have := b.lt
    omega
  simp [g0Deriv,g0Image,modeX,hh]

theorem g0Deriv_middle_zero (g : Fin 10) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ middleSpan b) :
    g0Deriv m g (b.top.val-b.lower.val) p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨z,rfl⟩ := hp
      rw [(g0Deriv m g (b.top.val-b.lower.val)).leibniz,
        g0Deriv_X_middle_zero b g z.left z.left_lower,
        g0Deriv_X_middle_zero b g z.right z.right_lower]
      simp
  | zero => exact map_zero _
  | add p q _ _ ihp ihq => simp only [map_add,ihp,ihq,add_zero]
  | smul a p _ ih => simp only [Derivation.map_smul,ih,smul_zero]

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.g0Deriv_middle
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.g0Deriv_middle_zero
