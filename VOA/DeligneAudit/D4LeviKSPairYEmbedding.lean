import VOA.DeligneAudit.D4LeviKSPairRecolourIter

/-! The Y-free source alphabet and its PAIR substitution. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

abbrev PairXZ (a b c : ℕ) := (Fin b ⊕ Fin a) ⊕ Fin c

def pairXZSource (a b c : ℕ) : PairXZ a b c → PairSource a b c
  | Sum.inl x => Sum.inl x
  | Sum.inr z => Sum.inr (Sum.inr z)

def pairXZTarget (a b c : ℕ) : PairXZ a b c → PairTarget a b c
  | Sum.inl (Sum.inl y) => Sum.inr (Sum.inl y)
  | Sum.inl (Sum.inr x) => Sum.inl x
  | Sum.inr z => Sum.inr (Sum.inr z)

theorem pairVariable_comp_xz (a b c : ℕ) :
    pairVariable a b c ∘ pairXZSource a b c = pairXZTarget a b c := by
  funext t
  rcases t with (y | x) | z <;> rfl

theorem pairRestriction_xz (a b c : ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairRestriction a b c (rename (pairXZSource a b c) Q) =
      rename (pairXZTarget a b c) Q := by
  rw [pairRestriction, rename_rename, pairVariable_comp_xz]

noncomputable def pairYMonomial (a b c : ℕ) (γ : Fin b → ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  ∏ y : Fin b, X (Sum.inr (Sum.inl y)) ^ γ y

noncomputable def pairPairedXZMonomial (a b c : ℕ) (γ : Fin b → ℕ) :
    MvPolynomial (PairXZ a b c) ℂ :=
  ∏ y : Fin b, X (Sum.inl (Sum.inl y)) ^ γ y

theorem pairRestriction_yMonomial (a b c : ℕ) (γ : Fin b → ℕ) :
    pairRestriction a b c (pairYMonomial a b c γ) =
      rename (pairXZTarget a b c) (pairPairedXZMonomial a b c γ) := by
  simp [pairYMonomial, pairPairedXZMonomial, pairRestriction_Y,
    pairXZTarget]

/-- Restriction combines the Y modes with the paired X modes after the
    Y variables have been split from an XZ polynomial. -/
theorem pairRestriction_y_xz (a b c : ℕ) (γ : Fin b → ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairRestriction a b c
        (pairYMonomial a b c γ * rename (pairXZSource a b c) Q) =
      rename (pairXZTarget a b c)
        (pairPairedXZMonomial a b c γ * Q) := by
  rw [map_mul, pairRestriction_yMonomial, pairRestriction_xz, map_mul]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairVariable_comp_xz
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_xz
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_yMonomial
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_y_xz
