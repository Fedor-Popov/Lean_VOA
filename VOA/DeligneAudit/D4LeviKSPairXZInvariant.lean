import VOA.DeligneAudit.D4LeviKSPairXZCount

/-! The Y coefficients retain the X swaps needed by recolouring. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

theorem pairYCoeff_swap_xz (a b c : ℕ)
    (s t : Fin b ⊕ Fin a)
    (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) (d : Fin b →₀ ℕ) :
    rename (Equiv.swap (Sum.inl s) (Sum.inl t))
        (coeff d (pairSplitAlgebra a b c P)) =
      coeff d (pairSplitAlgebra a b c P) := by
  rw [← Equiv.Perm.sumCongr_swap_refl]
  exact pairYCoeff_rename_x a b c (Equiv.swap s t) P hP d

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairYCoeff_swap_xz
