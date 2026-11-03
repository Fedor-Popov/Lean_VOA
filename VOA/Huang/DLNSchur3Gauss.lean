import VOA.Huang.DLNSchur3Matrices

/-! # The two unit-pivot charts

Over a prime-power residue ring at least one first-column entry is a unit.
This is different from the field Bruhat decomposition: a nonzero lower-left
entry need not be a unit.
-/

namespace VOA.Huang.DLNSchur

section Matrices

variable {R : Type*} [CommRing R]

/-- Gaussian factorization when the top-left entry is a unit. -/
theorem gauss_of_unit_top_left (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (u : Rˣ) (hu : g 0 0 = u) :
    g = lowerRoot (g 1 0 * (↑u⁻¹ : R)) * torus u *
      upperRoot (g 0 1 * (↑u⁻¹ : R)) := by
  have hd : (u : R) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hu] using g.2
  have he : g 1 1 = g 1 0 * g 0 1 * (↑u⁻¹ : R) + (↑u⁻¹ : R) := by
    calc
      g 1 1 = (↑u⁻¹ : R) * ((u : R) * g 1 1) := by simp [← mul_assoc]
      _ = g 1 0 * g 0 1 * (↑u⁻¹ : R) + (↑u⁻¹ : R) := by
        linear_combination (↑u⁻¹ : R) * hd
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, torus, upperRoot, Matrix.mul_apply, Fin.sum_univ_two,
      hu, he, mul_assoc, mul_comm, mul_left_comm]

/-- Gaussian factorization when the lower-left entry is a unit. -/
theorem gauss_of_unit_lower_left (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (u : Rˣ) (hu : g 1 0 = u) :
    g = upperRoot (g 0 0 * (↑u⁻¹ : R)) * weyl (-u⁻¹) *
      upperRoot (g 1 1 * (↑u⁻¹ : R)) := by
  have hd : g 0 0 * g 1 1 - g 0 1 * (u : R) = 1 := by
    simpa only [Matrix.det_fin_two, hu] using g.2
  have he : g 0 1 = g 0 0 * g 1 1 * (↑u⁻¹ : R) - (↑u⁻¹ : R) := by
    calc
      g 0 1 = (↑u⁻¹ : R) * (g 0 1 * (u : R)) := by
        simp [mul_comm, mul_left_comm]
      _ = g 0 0 * g 1 1 * (↑u⁻¹ : R) - (↑u⁻¹ : R) := by
        linear_combination -(↑u⁻¹ : R) * hd
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperRoot, weyl, Matrix.mul_apply, Fin.sum_univ_two,
      hu, he, mul_assoc, mul_comm, sub_eq_add_neg, add_comm]

end Matrices

/-- In the first column of an `SL₂` matrix over a prime-power ring, one entry is a unit. -/
theorem first_column_unit_primePower {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k))) :
    IsUnit (g 0 0) ∨ IsUnit (g 1 0) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra h
  push Not at h
  have ha : p ∣ (g 0 0).val := by
    have := h.1
    rw [← ZMod.natCast_zmod_val (g 0 0), ZMod.isUnit_natCast_iff_not_dvd_pow hp hk] at this
    exact not_not.mp this
  have hc : p ∣ (g 1 0).val := by
    have := h.2
    rw [← ZMod.natCast_zmod_val (g 1 0), ZMod.isUnit_natCast_iff_not_dvd_pow hp hk] at this
    exact not_not.mp this
  let r := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)
  have hra : r (g 0 0) = 0 := by
    rw [← ZMod.natCast_zmod_val (g 0 0), map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr ha
  have hrc : r (g 1 0) = 0 := by
    rw [← ZMod.natCast_zmod_val (g 1 0), map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hc
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.2
  have := congrArg r hd
  simp [hra, hrc] at this

/-- A concrete obstruction to using the two field Bruhat cells over a local ring. -/
theorem lower_five_mod_twentyFive_nonzero_nonunit :
    lowerRoot (5 : ZMod 25) 1 0 ≠ 0 ∧ ¬ IsUnit (lowerRoot (5 : ZMod 25) 1 0) := by
  change (5 : ZMod 25) ≠ 0 ∧ ¬ IsUnit (5 : ZMod 25)
  constructor
  · decide
  · exact (ZMod.isUnit_iff_coprime 5 25).not.mpr (by decide)

/-- The proposed field-style `B ∪ B w U` decomposition fails already modulo 25. -/
theorem lower_five_mod_twentyFive_not_bruhat :
    ¬ (lowerRoot (5 : ZMod 25) 1 0 = 0 ∨
      ∃ (b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 25)) (t : ZMod 25),
        b 1 0 = 0 ∧ lowerRoot 5 = b * weyl 1 * upperRoot t) := by
  rintro (h | ⟨b, t, hb, he⟩)
  · exact lower_five_mod_twentyFive_nonzero_nonunit.1 h
  · have hd : b 0 0 * b 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, hb, mul_zero, sub_zero] using b.2
    let u : (ZMod 25)ˣ := ⟨b 1 1, b 0 0, by simpa only [mul_comm] using hd, hd⟩
    have hentry : (5 : ZMod 25) = -b 1 1 := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 25) => g 1 0) he
      simpa [lowerRoot, weyl, upperRoot, Matrix.mul_apply, Fin.sum_univ_two, hb] using this
    apply lower_five_mod_twentyFive_nonzero_nonunit.2
    change IsUnit (5 : ZMod 25)
    rw [hentry]
    exact u.isUnit.neg

end VOA.Huang.DLNSchur
