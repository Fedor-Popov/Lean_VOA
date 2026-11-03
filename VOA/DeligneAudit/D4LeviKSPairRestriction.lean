import VOA.DeligneAudit.D4LeviKSWordCoeff

/-! The polynomial substitution underlying the D4 PAIR restriction. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

/-- Before taking symmetric invariants, the X slots consist of `b` paired
    slots and `a` unpaired slots. The other slots carry Y and Z modes. -/
abbrev PairSource (a b c : ℕ) := (Fin b ⊕ Fin a) ⊕ (Fin b ⊕ Fin c)

abbrev PairTarget (a b c : ℕ) := Fin a ⊕ (Fin b ⊕ Fin c)

/-- Restriction sends the paired X variables and the Y variables to the
    same target variables. Unpaired X and Z retain their own variables. -/
def pairVariable (a b c : ℕ) : PairSource a b c → PairTarget a b c
  | Sum.inl (Sum.inl y) => Sum.inr (Sum.inl y)
  | Sum.inl (Sum.inr x) => Sum.inl x
  | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl y)
  | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)

theorem pairVariable_surjective (a b c : ℕ) :
    Function.Surjective (pairVariable a b c) := by
  intro t
  rcases t with x | yz
  · exact ⟨Sum.inl (Sum.inr x), rfl⟩
  · rcases yz with y | z
    · exact ⟨Sum.inr (Sum.inl y), rfl⟩
    · exact ⟨Sum.inr (Sum.inr z), rfl⟩

/-- The word-level restriction map before imposing separately symmetric
    mode slots. -/
noncomputable def pairRestriction (a b c : ℕ) :
    MvPolynomial (PairSource a b c) ℂ →ₐ[ℂ]
      MvPolynomial (PairTarget a b c) ℂ :=
  rename (pairVariable a b c)

theorem pairRestriction_surjective (a b c : ℕ) :
    Function.Surjective (pairRestriction a b c) := by
  exact rename_surjective (pairVariable a b c) (pairVariable_surjective a b c)

theorem pairRestriction_paired_X (a b c : ℕ) (y : Fin b) :
    pairRestriction a b c (X (Sum.inl (Sum.inl y))) =
      X (Sum.inr (Sum.inl y)) := by
  simp [pairRestriction, pairVariable]

theorem pairRestriction_Y (a b c : ℕ) (y : Fin b) :
    pairRestriction a b c (X (Sum.inr (Sum.inl y))) =
      X (Sum.inr (Sum.inl y)) := by
  simp [pairRestriction, pairVariable]

theorem pairRestriction_unpaired_X (a b c : ℕ) (x : Fin a) :
    pairRestriction a b c (X (Sum.inl (Sum.inr x))) = X (Sum.inl x) := by
  simp [pairRestriction, pairVariable]

theorem pairRestriction_Z (a b c : ℕ) (z : Fin c) :
    pairRestriction a b c (X (Sum.inr (Sum.inr z))) =
      X (Sum.inr (Sum.inr z)) := by
  simp [pairRestriction, pairVariable]

theorem pairRestriction_paired_modes (a b c : ℕ) (y : Fin b) (r s : ℕ) :
    pairRestriction a b c
        (X (Sum.inl (Sum.inl y)) ^ r *
          X (Sum.inr (Sum.inl y)) ^ s) =
      X (Sum.inr (Sum.inl y)) ^ (r + s) := by
  rw [map_mul, map_pow, map_pow,
    pairRestriction_paired_X, pairRestriction_Y, ← pow_add]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairVariable_surjective
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_surjective
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_paired_X
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_Y
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_unpaired_X
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_Z
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_paired_modes
