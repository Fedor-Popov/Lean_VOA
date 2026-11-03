import VOA.DeligneAudit.DeligneFusionCVRectStarIdeal
import VOA.DeligneAudit.DeligneFusionCVRectFamily

/-!
# The canonical three-color variables and the no-left-site quotient

The leaf colors are x and z, with y the shared center. When no x site
remains, an explicit variable permutation identifies the coefficient
quotient with the already defined two-color family. This is an actual
algebra equivalence, without a mixed CV or PBW presentation assumption.
-/

namespace VOA.DeligneAudit.A2.CVRectStarBase

open CVRectStarIdeal CVRectIntegrationIdeal CVRectIntegrationOrder
open CVRectZero CVRectSplit CVRectFamily

noncomputable section

abbrev StarRing (L N R : ℕ) := MvPolynomial (Fin L ⊕ (Fin N ⊕ Fin R)) ℂ

def starX (L N R : ℕ) : PowerSeries (StarRing L N R) :=
  ∑ i : Fin L, PowerSeries.C (MvPolynomial.X (Sum.inl i)) *
    PowerSeries.X ^ (L - 1 - i.val)

def starY (L N R : ℕ) : PowerSeries (StarRing L N R) :=
  ∑ j : Fin N, PowerSeries.C (MvPolynomial.X (Sum.inr (Sum.inl j))) *
    PowerSeries.X ^ (N - 1 - j.val)

def starZ (L N R : ℕ) : PowerSeries (StarRing L N R) :=
  ∑ k : Fin R, PowerSeries.C (MvPolynomial.X (Sum.inr (Sum.inr k))) *
    PowerSeries.X ^ (R - 1 - k.val)

/-- A vanished leaf current removes its powers from the entire ideal. -/
theorem coefficientIdeal3_zero_left {R : Type*} [CommRing R]
    (Y Z : PowerSeries R) (right center : List ℕ) :
    coefficientIdeal3 0 Y Z (starOrder [] right center) =
      coefficientIdeal Z Y (familyOrder right center) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨p, q, r, j, hj, rfl⟩
    by_cases hp : p = 0
    · subst p
      apply Ideal.subset_span
      refine ⟨r, q, j, ?_, ?_⟩
      · simpa [starOrder, familyOrder, excess, Nat.add_comm] using hj
      · simp [mul_comm]
    · simp [zero_pow hp]
  · apply Ideal.span_le.mpr
    rintro P ⟨r, q, j, hj, rfl⟩
    apply Ideal.subset_span
    refine ⟨0, q, r, j, ?_, ?_⟩
    · simpa [starOrder, familyOrder, excess, Nat.add_comm] using hj
    · simp [mul_comm]

/-- With no left variable, z becomes the old selected color and y the
old common color. All retained indices and their reversal are unchanged. -/
def baseIndex (M N : ℕ) :
    (Fin 0 ⊕ (Fin N ⊕ Fin M)) ≃ (Fin M ⊕ Fin N) where
  toFun
    | Sum.inl i => Fin.elim0 i
    | Sum.inr (Sum.inl j) => Sum.inr j
    | Sum.inr (Sum.inr k) => Sum.inl k
  invFun
    | Sum.inl k => Sum.inr (Sum.inr k)
    | Sum.inr j => Sum.inr (Sum.inl j)
  left_inv x := by
    cases x with
    | inl i => exact Fin.elim0 i
    | inr x => cases x <;> rfl
  right_inv x := by cases x <;> rfl

def baseVars (M N : ℕ) : StarRing 0 N M ≃ₐ[ℂ] CVRectFamily.Ring M N :=
  MvPolynomial.renameEquiv ℂ (baseIndex M N)

@[simp] theorem baseVars_X_y (M N : ℕ) (j : Fin N) :
    baseVars M N (MvPolynomial.X (Sum.inr (Sum.inl j))) =
      MvPolynomial.X (Sum.inr j) := by
  simp [baseVars, baseIndex, MvPolynomial.renameEquiv_apply]

@[simp] theorem baseVars_X_z (M N : ℕ) (k : Fin M) :
    baseVars M N (MvPolynomial.X (Sum.inr (Sum.inr k))) =
      MvPolynomial.X (Sum.inl k) := by
  simp [baseVars, baseIndex, MvPolynomial.renameEquiv_apply]

theorem baseVars_starX (M N : ℕ) :
    PowerSeries.map (baseVars M N).toRingHom (starX 0 N M) = 0 := by
  simp [starX]

theorem baseVars_starY (M N : ℕ) :
    PowerSeries.map (baseVars M N).toRingHom (starY 0 N M) = reverseRight M N := by
  simp [starY, reverseRight]

theorem baseVars_starZ (M N : ℕ) :
    PowerSeries.map (baseVars M N).toRingHom (starZ 0 N M) = reverseLeft M N := by
  simp [starZ, reverseLeft]

/-- Equality of the full actual ideals under the canonical variable
permutation, including every multiplied coefficient relation. -/
theorem baseCoefficientIdeal_map (M N : ℕ) (right center : List ℕ) :
    Ideal.map (baseVars M N).toRingHom
        (coefficientIdeal3 (starX 0 N M) (starY 0 N M) (starZ 0 N M)
          (starOrder [] right center)) =
      CVRectFamily.ideal M N right center := by
  rw [coefficientIdeal3_map, baseVars_starX, baseVars_starY, baseVars_starZ,
    coefficientIdeal3_zero_left]
  rfl

/-- The canonical no-left-site star quotient is the actual old family,
not merely a quotient of it in one direction. -/
def zeroLeftEquiv (right center : List ℕ) :
    (StarRing 0 (right.length + center.length) right.length ⧸
      coefficientIdeal3 (starX 0 (right.length + center.length) right.length)
        (starY 0 (right.length + center.length) right.length)
        (starZ 0 (right.length + center.length) right.length)
        (starOrder [] right center)) ≃ₐ[ℂ] Family right center :=
  Ideal.quotientEquivAlg _ _ (baseVars right.length (right.length + center.length))
    (baseCoefficientIdeal_map right.length (right.length + center.length) right center).symm

end

end VOA.DeligneAudit.A2.CVRectStarBase

#print axioms VOA.DeligneAudit.A2.CVRectStarBase.coefficientIdeal3_zero_left
#print axioms VOA.DeligneAudit.A2.CVRectStarBase.baseCoefficientIdeal_map
#print axioms VOA.DeligneAudit.A2.CVRectStarBase.zeroLeftEquiv
