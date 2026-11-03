import VOA.DeligneAudit.D4LeviKSPairYSplit

/-! Match the Y coefficient expansion with the PAIR restriction map. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

def pairYSlot (a b c : ℕ) (y : Fin b) : PairSource a b c :=
  Sum.inr (Sum.inl y)

def pairPairedXZSlot (a b c : ℕ) (y : Fin b) : PairXZ a b c :=
  Sum.inl (Sum.inl y)

theorem pairVariable_ySlot (a b c : ℕ) :
    pairVariable a b c ∘ pairYSlot a b c =
      pairXZTarget a b c ∘ pairPairedXZSlot a b c := by
  funext y
  rfl

noncomputable def pairPairedXZFinsuppMonomial
    (a b c : ℕ) (d : Fin b →₀ ℕ) :
    MvPolynomial (PairXZ a b c) ℂ :=
  rename (pairPairedXZSlot a b c) (monomial d 1)

theorem pairRestriction_yFinsupp (a b c : ℕ) (d : Fin b →₀ ℕ) :
    pairRestriction a b c (pairYFinsuppMonomial a b c d) =
      rename (pairXZTarget a b c)
        (pairPairedXZFinsuppMonomial a b c d) := by
  simp only [pairRestriction, pairYFinsuppMonomial,
    pairPairedXZFinsuppMonomial, pairYSlot, pairPairedXZSlot,
    rename_rename]
  congr 1

theorem pairRestriction_yFinsupp_xz (a b c : ℕ) (d : Fin b →₀ ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairRestriction a b c
        (pairYFinsuppMonomial a b c d * rename (pairXZSource a b c) Q) =
      rename (pairXZTarget a b c)
        (pairPairedXZFinsuppMonomial a b c d * Q) := by
  rw [map_mul, pairRestriction_yFinsupp, pairRestriction_xz, map_mul]

/-- PAIR restriction of any source polynomial is computed on its finite
    Y coefficient expansion by shifting the paired X modes. -/
theorem pairRestriction_y_decomposition (a b c : ℕ)
    (P : MvPolynomial (PairSource a b c) ℂ) :
    pairRestriction a b c P =
      ∑ d ∈ (pairSplitAlgebra a b c P).support,
        rename (pairXZTarget a b c)
          (pairPairedXZFinsuppMonomial a b c d *
            coeff d (pairSplitAlgebra a b c P)) := by
  conv_lhs => rw [pairY_decomposition a b c P]
  simp only [map_sum, pairRestriction_yFinsupp_xz]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairVariable_ySlot
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_yFinsupp
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_yFinsupp_xz
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_y_decomposition
