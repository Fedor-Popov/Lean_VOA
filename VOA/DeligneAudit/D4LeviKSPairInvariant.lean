import VOA.DeligneAudit.D4LeviKSFamiliesUnconditional
import VOA.DeligneAudit.D4LeviKSPairRestriction

/-! The basic symmetric power sums in the PAIR restriction kernel. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def pairedXPsum (a b c r : ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  ∑ y : Fin b, X (Sum.inl (Sum.inl y)) ^ r

noncomputable def sourceYPsum (a b c r : ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  ∑ y : Fin b, X (Sum.inr (Sum.inl y)) ^ r

noncomputable def targetYPsum (a b c r : ℕ) :
    MvPolynomial (PairTarget a b c) ℂ :=
  ∑ y : Fin b, X (Sum.inr (Sum.inl y)) ^ r

theorem pairRestriction_pairedXPsum (a b c r : ℕ) :
    pairRestriction a b c (pairedXPsum a b c r) =
      targetYPsum a b c r := by
  simp [pairedXPsum, targetYPsum, pairRestriction_paired_X]

theorem pairRestriction_sourceYPsum (a b c r : ℕ) :
    pairRestriction a b c (sourceYPsum a b c r) =
      targetYPsum a b c r := by
  simp [sourceYPsum, targetYPsum, pairRestriction_Y]

/-- The difference of the two paired power sums is a concrete element of
    the unrestricted substitution kernel. -/
theorem pairRestriction_psum_difference_zero (a b c r : ℕ) :
    pairRestriction a b c
      (pairedXPsum a b c r - sourceYPsum a b c r) = 0 := by
  rw [map_sub, pairRestriction_pairedXPsum, pairRestriction_sourceYPsum, sub_self]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_pairedXPsum
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_sourceYPsum
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_psum_difference_zero
