import VOA.DeligneAudit.SL4TGrassmannian

/-! # The Grassmannian presentation has an augmentation and is nontrivial -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Evaluation of every positive elementary generator at zero. -/
def symAugmentation : SymPoly →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun _ => 0)

theorem symAugmentation_elementary (j : ℕ) (hj : 0 < j) :
    symAugmentation (elementary j) = 0 := by
  cases j with
  | zero => omega
  | succ j => simp [symAugmentation, elementary]

theorem symAugmentation_complete (j : ℕ) (hj : 0 < j) :
    symAugmentation (complete j) = 0 := by
  cases j with
  | zero => omega
  | succ j =>
      rw [complete_succ, map_neg, map_sum]
      simp only [map_mul, symAugmentation_elementary _ (Nat.zero_lt_succ _),
        mul_zero, zero_mul, Finset.sum_const_zero, neg_zero]

theorem grassIdeal_le_ker_augmentation (d T : ℕ) :
    grassIdeal d T ≤ RingHom.ker symAugmentation.toRingHom := by
  apply sup_le
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro j hj
    exact symAugmentation_elementary j (by omega)
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro j hj
    exact symAugmentation_complete j (by omega)

/-- The scalar augmentation of the Grassmannian quotient. -/
def grassAugmentation (d T : ℕ) : GrassRing d T →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (grassIdeal d T) symAugmentation
    (fun _ hp => grassIdeal_le_ker_augmentation d T hp)

theorem grass_nontrivial (d T : ℕ) : Nontrivial (GrassRing d T) :=
  (grassAugmentation d T).toRingHom.domain_nontrivial

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.grassAugmentation
#print axioms VOA.DeligneAudit.SL4T.grass_nontrivial
