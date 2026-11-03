import VOA.DeligneAudit.DeligneFusionCVRectSplit
import VOA.DeligneAudit.DeligneFusionCVRectIdealMap
import VOA.DeligneAudit.DeligneFusionCVRectZero

/-!
# Actual finite-variable maps for zero-capacity sites

The smaller variables embed by `Fin.castSucc`. Projection kills precisely the
highest retained variables. Under projection the affected reversed currents
acquire one outer-variable factor, giving the actual zero-site ideal removal.
-/

namespace VOA.DeligneAudit.A2.CVRectEliminate

open VOA.DeligneAudit.A2.CVRectSplit
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectZero

noncomputable section

abbrev VarsRing (M N : ℕ) := MvPolynomial (Fin M ⊕ Fin N) ℂ

/-- Retain the old coordinates when adding a highest mode in both colors. -/
def sectionBoth (M N : ℕ) : VarsRing M N →ₐ[ℂ] VarsRing (M + 1) (N + 1) :=
  MvPolynomial.rename (Sum.map Fin.castSucc Fin.castSucc)

/-- Retain the old coordinates when adding a highest mode only in the right color. -/
def sectionRight (M N : ℕ) : VarsRing M N →ₐ[ℂ] VarsRing M (N + 1) :=
  MvPolynomial.rename (Sum.map id Fin.castSucc)

/-- Remove both highest retained variables by evaluating them at zero. -/
def projectBoth (M N : ℕ) : VarsRing (M + 1) (N + 1) →ₐ[ℂ] VarsRing M N :=
  MvPolynomial.aeval fun x => match x with
    | Sum.inl i => Fin.lastCases 0 (fun j => MvPolynomial.X (Sum.inl j)) i
    | Sum.inr i => Fin.lastCases 0 (fun j => MvPolynomial.X (Sum.inr j)) i

/-- Remove only the highest retained right-color variable. -/
def projectRight (M N : ℕ) : VarsRing M (N + 1) →ₐ[ℂ] VarsRing M N :=
  MvPolynomial.aeval fun x => match x with
    | Sum.inl i => MvPolynomial.X (Sum.inl i)
    | Sum.inr i => Fin.lastCases 0 (fun j => MvPolynomial.X (Sum.inr j)) i

@[simp] theorem sectionBoth_X_left (M N : ℕ) (i : Fin M) :
    sectionBoth M N (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inl i.castSucc) := by
  simp [sectionBoth]

@[simp] theorem sectionBoth_X_right (M N : ℕ) (i : Fin N) :
    sectionBoth M N (MvPolynomial.X (Sum.inr i)) = MvPolynomial.X (Sum.inr i.castSucc) := by
  simp [sectionBoth]

@[simp] theorem sectionRight_X_left (M N : ℕ) (i : Fin M) :
    sectionRight M N (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inl i) := by
  simp [sectionRight]

@[simp] theorem sectionRight_X_right (M N : ℕ) (i : Fin N) :
    sectionRight M N (MvPolynomial.X (Sum.inr i)) = MvPolynomial.X (Sum.inr i.castSucc) := by
  simp [sectionRight]

@[simp] theorem projectBoth_X_left (M N : ℕ) (i : Fin M) :
    projectBoth M N (MvPolynomial.X (Sum.inl i.castSucc)) = MvPolynomial.X (Sum.inl i) := by
  simp [projectBoth]

@[simp] theorem projectBoth_X_right (M N : ℕ) (i : Fin N) :
    projectBoth M N (MvPolynomial.X (Sum.inr i.castSucc)) = MvPolynomial.X (Sum.inr i) := by
  simp [projectBoth]

@[simp] theorem projectBoth_X_left_last (M N : ℕ) :
    projectBoth M N (MvPolynomial.X (Sum.inl (Fin.last M))) = 0 := by simp [projectBoth]

@[simp] theorem projectBoth_X_right_last (M N : ℕ) :
    projectBoth M N (MvPolynomial.X (Sum.inr (Fin.last N))) = 0 := by simp [projectBoth]

@[simp] theorem projectRight_X_left (M N : ℕ) (i : Fin M) :
    projectRight M N (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inl i) := by
  simp [projectRight]

@[simp] theorem projectRight_X_right (M N : ℕ) (i : Fin N) :
    projectRight M N (MvPolynomial.X (Sum.inr i.castSucc)) = MvPolynomial.X (Sum.inr i) := by
  simp [projectRight]

@[simp] theorem projectRight_X_right_last (M N : ℕ) :
    projectRight M N (MvPolynomial.X (Sum.inr (Fin.last N))) = 0 := by simp [projectRight]

theorem projectBoth_sectionBoth (M N : ℕ) :
    (projectBoth M N).comp (sectionBoth M N) = AlgHom.id ℂ (VarsRing M N) := by
  ext x
  cases x <;> simp

theorem projectRight_sectionRight (M N : ℕ) :
    (projectRight M N).comp (sectionRight M N) = AlgHom.id ℂ (VarsRing M N) := by
  ext x
  cases x <;> simp

theorem projectBoth_surjective (M N : ℕ) : Function.Surjective (projectBoth M N) := by
  intro p
  exact ⟨sectionBoth M N p, DFunLike.congr_fun (projectBoth_sectionBoth M N) p⟩

theorem projectRight_surjective (M N : ℕ) : Function.Surjective (projectRight M N) := by
  intro p
  exact ⟨sectionRight M N p, DFunLike.congr_fun (projectRight_sectionRight M N) p⟩

/-- The highest retained left variable is the constant reversed coefficient. -/
theorem coeff_zero_reverseLeft (M N : ℕ) :
    PowerSeries.coeff 0 (reverseLeft (M + 1) N) = MvPolynomial.X (Sum.inl (Fin.last M)) := by
  unfold reverseLeft
  rw [map_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, Nat.sub_self, ↓reduceIte, mul_one]
  have hz : (∑ i : Fin M,
      MvPolynomial.X (Sum.inl i.castSucc) * (if 0 = M - i.val then 1 else 0) :
        VarsRing (M + 1) N) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬ 0 = M - i.val := by omega
    simp [hi]
  rw [hz, zero_add]

/-- The highest retained right variable is the constant reversed coefficient. -/
theorem coeff_zero_reverseRight (M N : ℕ) :
    PowerSeries.coeff 0 (reverseRight M (N + 1)) = MvPolynomial.X (Sum.inr (Fin.last N)) := by
  unfold reverseRight
  rw [map_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, Nat.sub_self, ↓reduceIte, mul_one]
  have hz : (∑ i : Fin N,
      MvPolynomial.X (Sum.inr i.castSucc) * (if 0 = N - i.val then 1 else 0) :
        VarsRing M (N + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬ 0 = N - i.val := by omega
    simp [hi]
  rw [hz, zero_add]

theorem projectBoth_reverseLeft (M N : ℕ) :
    PowerSeries.map (projectBoth M N).toRingHom (reverseLeft (M + 1) (N + 1)) =
      PowerSeries.X * reverseLeft M N := by
  unfold reverseLeft
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_castSucc]
  simp only [show ∀ p, (projectBoth M N).toRingHom p = projectBoth M N p from fun _ => rfl,
    projectBoth_X_left_last, map_zero, zero_mul, add_zero, projectBoth_X_left,
    Fin.val_castSucc, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show M - i.val = (M - 1 - i.val) + 1 by omega, pow_succ]
  ring

theorem projectBoth_reverseRight (M N : ℕ) :
    PowerSeries.map (projectBoth M N).toRingHom (reverseRight (M + 1) (N + 1)) =
      PowerSeries.X * reverseRight M N := by
  unfold reverseRight
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_castSucc]
  simp only [show ∀ p, (projectBoth M N).toRingHom p = projectBoth M N p from fun _ => rfl,
    projectBoth_X_right_last, map_zero, zero_mul, add_zero, projectBoth_X_right,
    Fin.val_castSucc, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show N - i.val = (N - 1 - i.val) + 1 by omega, pow_succ]
  ring

theorem projectRight_reverseLeft (M N : ℕ) :
    PowerSeries.map (projectRight M N).toRingHom (reverseLeft M (N + 1)) =
      reverseLeft M N := by
  unfold reverseLeft
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    show ∀ p, (projectRight M N).toRingHom p = projectRight M N p from fun _ => rfl,
    projectRight_X_left]

theorem projectRight_reverseRight (M N : ℕ) :
    PowerSeries.map (projectRight M N).toRingHom (reverseRight M (N + 1)) =
      PowerSeries.X * reverseRight M N := by
  unfold reverseRight
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_castSucc]
  simp only [show ∀ p, (projectRight M N).toRingHom p = projectRight M N p from fun _ => rfl,
    projectRight_X_right_last, map_zero, zero_mul, add_zero, projectRight_X_right,
    Fin.val_castSucc, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show N - i.val = (N - 1 - i.val) + 1 by omega, pow_succ]
  ring

/-- Zero two-color capacity removes both highest variables from the actual image ideal. -/
theorem projectBoth_ideal (M N : ℕ) (two one : List ℕ) :
    Ideal.map (projectBoth M N).toRingHom
      (coefficientIdeal (reverseLeft (M + 1) (N + 1)) (reverseRight (M + 1) (N + 1))
        (familyOrder (0 :: two) one)) =
      coefficientIdeal (reverseLeft M N) (reverseRight M N) (familyOrder two one) := by
  rw [CVRectIdealMap.coefficientIdeal_map, projectBoth_reverseLeft, projectBoth_reverseRight,
    coefficientIdeal_active_zero]

/-- Zero one-color capacity removes only the highest right variable from the actual image ideal. -/
theorem projectRight_ideal (M N : ℕ) (two one : List ℕ) :
    Ideal.map (projectRight M N).toRingHom
      (coefficientIdeal (reverseLeft M (N + 1)) (reverseRight M (N + 1))
        (familyOrder two (0 :: one))) =
      coefficientIdeal (reverseLeft M N) (reverseRight M N) (familyOrder two one) := by
  rw [CVRectIdealMap.coefficientIdeal_map, projectRight_reverseLeft, projectRight_reverseRight,
    coefficientIdeal_inactive_zero]

end
end VOA.DeligneAudit.A2.CVRectEliminate

#print axioms VOA.DeligneAudit.A2.CVRectEliminate.projectBoth_ideal
#print axioms VOA.DeligneAudit.A2.CVRectEliminate.projectRight_ideal
#print axioms VOA.DeligneAudit.A2.CVRectEliminate.coeff_zero_reverseLeft
#print axioms VOA.DeligneAudit.A2.CVRectEliminate.coeff_zero_reverseRight
