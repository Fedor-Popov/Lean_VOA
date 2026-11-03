import VOA.DeligneAudit.DeligneFusionCVRectStarBase

/-! # Actual removal of the highest x and y variables in the star family -/

namespace VOA.DeligneAudit.A2.CVRectStarEliminate

open CVRectStarBase

noncomputable section

def sectionXY (L N R : ℕ) : StarRing L N R →ₐ[ℂ] StarRing (L + 1) (N + 1) R :=
  MvPolynomial.rename (Sum.map Fin.castSucc (Sum.map Fin.castSucc id))

def projectXY (L N R : ℕ) : StarRing (L + 1) (N + 1) R →ₐ[ℂ] StarRing L N R :=
  MvPolynomial.aeval fun x => match x with
    | Sum.inl i => Fin.lastCases 0 (fun j => MvPolynomial.X (Sum.inl j)) i
    | Sum.inr (Sum.inl i) =>
        Fin.lastCases 0 (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) i
    | Sum.inr (Sum.inr k) => MvPolynomial.X (Sum.inr (Sum.inr k))

@[simp] theorem sectionXY_X_x (L N R : ℕ) (i : Fin L) :
    sectionXY L N R (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i.castSucc) := by simp [sectionXY]

@[simp] theorem sectionXY_X_y (L N R : ℕ) (j : Fin N) :
    sectionXY L N R (MvPolynomial.X (Sum.inr (Sum.inl j))) =
      MvPolynomial.X (Sum.inr (Sum.inl j.castSucc)) := by simp [sectionXY]

@[simp] theorem sectionXY_X_z (L N R : ℕ) (k : Fin R) :
    sectionXY L N R (MvPolynomial.X (Sum.inr (Sum.inr k))) =
      MvPolynomial.X (Sum.inr (Sum.inr k)) := by simp [sectionXY]

@[simp] theorem projectXY_X_x (L N R : ℕ) (i : Fin L) :
    projectXY L N R (MvPolynomial.X (Sum.inl i.castSucc)) =
      MvPolynomial.X (Sum.inl i) := by simp [projectXY]

@[simp] theorem projectXY_X_y (L N R : ℕ) (j : Fin N) :
    projectXY L N R (MvPolynomial.X (Sum.inr (Sum.inl j.castSucc))) =
      MvPolynomial.X (Sum.inr (Sum.inl j)) := by simp [projectXY]

@[simp] theorem projectXY_X_z (L N R : ℕ) (k : Fin R) :
    projectXY L N R (MvPolynomial.X (Sum.inr (Sum.inr k))) =
      MvPolynomial.X (Sum.inr (Sum.inr k)) := by simp [projectXY]

@[simp] theorem projectXY_X_x_last (L N R : ℕ) :
    projectXY L N R (MvPolynomial.X (Sum.inl (Fin.last L))) = 0 := by simp [projectXY]

@[simp] theorem projectXY_X_y_last (L N R : ℕ) :
    projectXY L N R (MvPolynomial.X (Sum.inr (Sum.inl (Fin.last N)))) = 0 := by
  simp [projectXY]

theorem projectXY_sectionXY (L N R : ℕ) :
    (projectXY L N R).comp (sectionXY L N R) = AlgHom.id ℂ (StarRing L N R) := by
  ext x
  cases x with
  | inl i => simp
  | inr x => cases x <;> simp

theorem projectXY_surjective (L N R : ℕ) : Function.Surjective (projectXY L N R) := by
  intro p
  exact ⟨sectionXY L N R p, DFunLike.congr_fun (projectXY_sectionXY L N R) p⟩

theorem coeff_zero_starX (L N R : ℕ) :
    PowerSeries.coeff 0 (starX (L + 1) N R) = MvPolynomial.X (Sum.inl (Fin.last L)) := by
  unfold starX
  rw [map_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, Nat.sub_self, ↓reduceIte, mul_one]
  have hz : (∑ i : Fin L,
      MvPolynomial.X (Sum.inl i.castSucc) * (if 0 = L - i.val then 1 else 0) :
        StarRing (L + 1) N R) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬ 0 = L - i.val := by omega
    simp [hi]
  rw [hz, zero_add]

theorem coeff_zero_starY (L N R : ℕ) :
    PowerSeries.coeff 0 (starY L (N + 1) R) =
      MvPolynomial.X (Sum.inr (Sum.inl (Fin.last N))) := by
  unfold starY
  rw [map_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, Nat.sub_self, ↓reduceIte, mul_one]
  have hz : (∑ j : Fin N,
      MvPolynomial.X (Sum.inr (Sum.inl j.castSucc)) *
        (if 0 = N - j.val then 1 else 0) : StarRing L (N + 1) R) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : ¬ 0 = N - j.val := by omega
    simp [hj]
  rw [hz, zero_add]

theorem projectXY_starX (L N R : ℕ) :
    PowerSeries.map (projectXY L N R).toRingHom (starX (L + 1) (N + 1) R) =
      PowerSeries.X * starX L N R := by
  unfold starX
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_castSucc]
  simp only [show ∀ p, (projectXY L N R).toRingHom p = projectXY L N R p from fun _ => rfl,
    projectXY_X_x_last, map_zero, zero_mul, add_zero, projectXY_X_x,
    Fin.val_castSucc, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show L - i.val = (L - 1 - i.val) + 1 by omega, pow_succ]
  ring

theorem projectXY_starY (L N R : ℕ) :
    PowerSeries.map (projectXY L N R).toRingHom (starY (L + 1) (N + 1) R) =
      PowerSeries.X * starY L N R := by
  unfold starY
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_castSucc]
  simp only [show ∀ p, (projectXY L N R).toRingHom p = projectXY L N R p from fun _ => rfl,
    projectXY_X_y_last, map_zero, zero_mul, add_zero, projectXY_X_y,
    Fin.val_castSucc, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show N - j.val = (N - 1 - j.val) + 1 by omega, pow_succ]
  ring

theorem projectXY_starZ (L N R : ℕ) :
    PowerSeries.map (projectXY L N R).toRingHom (starZ (L + 1) (N + 1) R) = starZ L N R := by
  unfold starZ
  simp

end

end VOA.DeligneAudit.A2.CVRectStarEliminate

#print axioms VOA.DeligneAudit.A2.CVRectStarEliminate.projectXY_surjective
#print axioms VOA.DeligneAudit.A2.CVRectStarEliminate.projectXY_starX
#print axioms VOA.DeligneAudit.A2.CVRectStarEliminate.projectXY_starY
