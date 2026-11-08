import VOA.Moonshine.MoonshineCNHyperbolicCentralScalar

/-! # Full Virasoro relations of the hyperbolic Sugawara operators

The mixed relations force the Virasoro defect to be scalar. Its vacuum
coefficient is the explicitly evaluated finite contraction sum.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial

def hypSugawaraVirasoroDefect (κ ell : ℂ) (m n : ℤ) : Module.End ℂ hypFock :=
  ⁅hypSugawara κ ell m, hypSugawara κ ell n⁆ - ((m : ℂ) - n) • hypSugawara κ ell (m + n)

theorem hypSugawaraVirasoroDefect_commutes (κ ell : ℂ) (m n : ℤ) (a : Fin 2) (k : ℤ) :
    ⁅hypSugawaraVirasoroDefect κ ell m n, hypOscillator a (if a = 0 then κ else ell) k⁆ = 0 := by
  rw [hypSugawaraVirasoroDefect, sub_lie, lie_lie, smul_lie]
  simp only [hypSugawara_oscillator_comm, lie_smul]
  rw [show m + (n + k) = m + n + k by omega,
    show n + (m + k) = m + n + k by omega]
  simp only [smul_smul, ← sub_smul]
  have hc : -(k : ℂ) * -((n + k : ℤ) : ℂ) -
      -(k : ℂ) * -((m + k : ℤ) : ℂ) - ((m : ℂ) - n) * -(k : ℂ) = 0 := by
    push_cast
    ring
  rw [hc, zero_smul]

theorem hypSugawaraVirasoroDefect_scalar (κ ell : ℂ) (m n : ℤ) :
    hypSugawaraVirasoroDefect κ ell m n =
      coeff 0 (hypSugawaraVirasoroDefect κ ell m n 1) • LinearMap.id := by
  apply hypCommutant_scalar _ (fun a => if a = 0 then κ else ell)
  intro a k _
  exact sub_eq_zero.mp (hypSugawaraVirasoroDefect_commutes κ ell m n a k)

theorem hypSugawara_zero_constantCoeff (κ ell : ℂ) (p : hypFock) :
    constantCoeff (hypSugawara κ ell 0 p) = (κ * ell) * constantCoeff p := by
  simpa only [hypSugawara_zero_vacuum, LinearMap.map_smul₂, hypForm_one, smul_eq_mul]
    using (hypForm_sugawara_zero_adjoint κ ell 1 p).symm

theorem hypSugawara_vacuum_constant (κ ell : ℂ) (n : ℤ) :
    constantCoeff (hypSugawara κ ell n 1) = if n = 0 then κ * ell else 0 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    rw [hypSugawara_negative_constantCoeff, if_neg (by omega)]
  · simp [hypSugawara_zero_vacuum]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
    rw [hypSugawara_positive_vacuum, map_zero, if_neg (by omega)]

theorem hypSugawaraVirasoroDefect_constant (κ ell : ℂ) (m n : ℤ) :
    constantCoeff (hypSugawaraVirasoroDefect κ ell m n 1) =
      if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * 2 else 0 := by
  simp only [hypSugawaraVirasoroDefect, Ring.lie_def, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_sub, constantCoeff_smul, smul_eq_mul]
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, m = -(i + 1 : ℤ) := ⟨(-m - 1).toNat, by omega⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · rw [hypSugawara_negative_constantCoeff]
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
      rw [hypSugawara_negative_constantCoeff, hypSugawara_vacuum_constant,
        if_neg (by omega), if_neg (by omega)]
      ring
    · rw [hypSugawara_negative_constantCoeff, hypSugawara_zero_constantCoeff,
        hypSugawara_negative_constantCoeff, hypSugawara_vacuum_constant,
        if_neg (by omega), if_neg (by omega)]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
      rw [hypSugawara_negative_constantCoeff, hypSugawara_positive_negative_constant,
        hypSugawara_vacuum_constant]
      by_cases h : i = j
      · subst j
        simp only [neg_add_cancel, if_true, Int.cast_neg, Int.cast_add,
          Int.cast_natCast, Int.cast_one]
        ring
      · rw [if_neg (Ne.symm h), if_neg (by omega), if_neg (by omega)]
        ring
  · rcases lt_trichotomy n 0 with hn | rfl | hn
    · rw [hypSugawara_zero_constantCoeff, hypSugawara_zero_vacuum, map_smul,
        constantCoeff_smul, hypSugawara_vacuum_constant, hypSugawara_vacuum_constant,
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    · simp [hypSugawara_zero_vacuum]
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
      simp only [hypSugawara_positive_vacuum, map_zero, hypSugawara_zero_vacuum,
        map_smul, smul_zero, zero_sub, hypSugawara_vacuum_constant]
      rw [if_neg (by omega), if_neg (by omega)]
      ring
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, m = (i + 1 : ℤ) := ⟨(m - 1).toNat, by omega⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
      rw [hypSugawara_positive_negative_constant, hypSugawara_negative_constantCoeff,
        hypSugawara_vacuum_constant]
      by_cases h : i = j
      · subst j
        simp only [add_neg_cancel, if_true, Int.cast_add, Int.cast_natCast,
          Int.cast_one, Int.cast_neg]
        ring
      · rw [if_neg h, if_neg (by omega), if_neg (by omega)]
        ring
    · simp only [hypSugawara_zero_vacuum, map_smul, hypSugawara_positive_vacuum,
        smul_zero, map_zero, hypSugawara_vacuum_constant]
      rw [if_neg (by omega), if_neg (by omega)]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
      simp only [hypSugawara_positive_vacuum, map_zero, hypSugawara_vacuum_constant]
      rw [if_neg (by omega), if_neg (by omega)]
      ring

/-- The concrete operators satisfy Virasoro at central charge exactly two. -/
theorem hypSugawara_virasoro (κ ell : ℂ) (m n : ℤ) :
    hypSugawara κ ell m * hypSugawara κ ell n -
      hypSugawara κ ell n * hypSugawara κ ell m =
      ((m : ℂ) - n) • hypSugawara κ ell (m + n) +
        if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * 2) • 1 else 0 := by
  have h := hypSugawaraVirasoroDefect_scalar κ ell m n
  change hypSugawaraVirasoroDefect κ ell m n =
    constantCoeff (hypSugawaraVirasoroDefect κ ell m n 1) • LinearMap.id at h
  rw [hypSugawaraVirasoroDefect_constant] at h
  change hypSugawara κ ell m * hypSugawara κ ell n -
    hypSugawara κ ell n * hypSugawara κ ell m -
    ((m : ℂ) - n) • hypSugawara κ ell (m + n) = _ at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, add_comm]
  split_ifs <;> simp
  rfl

end VOA.Moonshine.ConwayNorton
