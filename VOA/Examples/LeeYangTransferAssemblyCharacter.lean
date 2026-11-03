import VOA.Examples.LeeYangTransferAssemblyAffine

/-! # The explicit finite Lee--Yang refined character coefficient

The coefficient is defined by bounded multiplicity tuples, so it does not
assume a basis, or assign a finite cardinal to an unspecified infinite space.
The equality with the actual PBW-flag dimension, `LeeYangPBWCharacter`, is proved downstream
(`leeYangPBWCharacter_iff_lowerBound.mpr leeYangRRLowerBound_holds`).
-/
namespace VOA.LeeYangTransferAssembly
open VirSimple VirGoodFil LeeYang
open scoped BigOperators
noncomputable section

abbrev LeeYangWeight (n : ℤ) := (virasoroSimple leeYangC).grading n

/-- Coefficient of `z^(r(r+1)) / product (1-z^j), 1 ≤ j ≤ r`.
The finite tuples record the multiplicity of each part `j+1`; the bound on
each multiplicity is harmless because the total weight is `n`. -/
def gapTwoCoefficient (n : ℤ) (r : ℕ) : ℕ := by
  classical
  exact Fintype.card {a : Fin r → Fin (n.toNat + 1) //
    ((r * (r + 1) + ∑ j : Fin r, (j.val + 1) * (a j).val : ℕ) : ℤ) = n}

/-- Same character in the Kähler coordinate `j=2R`, zero at odd or negative `j`. -/
def leadingCoefficient (n j : ℤ) : ℕ :=
  if 0 ≤ j ∧ j % 2 = 0 then gapTwoCoefficient n (j.toNat / 2) else 0

theorem leadingCoefficient_odd (n : ℤ) (p : ℕ) :
    leadingCoefficient n (2 * (p : ℤ) + 1) = 0 := by
  unfold leadingCoefficient
  rw [if_neg]
  omega

/-- [I] The vacuum Lee--Yang PBW-length character, at every weight
and every cumulative length, with an explicitly defined finite coefficient.
Proved: `LeeYangCharacter.leeYangPBWCharacter_iff_lowerBound.mpr`
`RRLower.leeYangRRLowerBound_holds` (`LeeYangCharacterReduction.lean`, `LYGramRank.lean`). -/
def LeeYangPBWCharacter : Prop :=
  ∀ (n : ℤ) (p : ℕ),
    Module.finrank ℂ ((virGradedFlag leeYangC).pieceIn p n) =
      ∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), leadingCoefficient n j

/-- The constant term is the single empty partition. -/
theorem gapTwoCoefficient_vacuum : gapTwoCoefficient 0 0 = 1 := by
  classical
  simp [gapTwoCoefficient]

end
end VOA.LeeYangTransferAssembly
