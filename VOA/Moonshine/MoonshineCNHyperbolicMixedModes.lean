import VOA.Moonshine.MoonshineCNHyperbolicSugawaraAdjoint

/-! # All signed Sugawara--oscillator commutators -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial

theorem hypForm_separates_left (p q : hypFock)
    (h : ∀ r, hypForm p r = hypForm q r) : p = q := by
  apply sub_eq_zero.mp
  by_contra hn
  obtain ⟨r, hr⟩ := hypForm_nondegenerate (p - q) hn
  apply hr
  rw [map_sub, LinearMap.sub_apply, h, sub_self]

theorem hypSugawara_positive_oscillator_comm (κ ell : ℂ) (j : ℕ)
    (a : Fin 2) (n : ℤ) :
    ⁅hypSugawara κ ell (j + 1 : ℤ), hypOscillator a (if a = 0 then κ else ell) n⁆ =
      -(n : ℂ) • hypOscillator a (if a = 0 then κ else ell) (n + (j + 1)) := by
  apply LinearMap.ext
  intro p
  apply hypForm_separates_left
  intro q
  have hc := LinearMap.congr_fun
    (hypSugawara_negative_oscillator_comm κ ell j a (-n)) q
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Int.cast_neg, neg_neg] at hc
  have he : hypOscillator a (if a = 0 then κ else ell) (-n)
        (hypSugawara κ ell (-(j + 1 : ℤ)) q) -
      hypSugawara κ ell (-(j + 1 : ℤ))
        (hypOscillator a (if a = 0 then κ else ell) (-n) q) =
      -(n : ℂ) • hypOscillator a (if a = 0 then κ else ell) (-(n + (j + 1))) q := by
    rw [← neg_sub, hc, ← neg_smul]
    rw [show -n - (j + 1) = -(n + (j + 1) : ℤ) by omega]
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, map_sub, LinearMap.map_smul₂]
  rw [hypForm_sugawara_adjoint, hypForm_oscillator_adjoint,
    hypForm_oscillator_adjoint, hypForm_sugawara_adjoint]
  rw [← map_sub, he, map_smul, hypForm_oscillator_adjoint]

theorem hypSugawara_zero_creation (κ ell : ℂ) (v : ℕ × Fin 2) (p : hypFock) :
    hypSugawara κ ell 0 (X v * p) - X v * hypSugawara κ ell 0 p =
      (v.1 + 1 : ℂ) • (X v * p) := by
  rw [hypSugawara_zero, hypSugawara_zero, Derivation.leibniz, hypEnergyDerivation_X]
  simp only [smul_eq_mul, smul_eq_C_mul]
  ring

theorem hypSugawara_zero_pderiv (κ ell : ℂ) (t : ℕ) (a : Fin 2) (p : hypFock) :
    hypSugawara κ ell 0 (pderiv (t, a) p) - pderiv (t, a) (hypSugawara κ ell 0 p) =
      -(t + 1 : ℂ) • pderiv (t, a) p := by
  have hd := congrArg (fun D : Derivation ℂ hypFock hypFock => D p)
    (hypRaisingDerivation_pderiv_comm 0 t a)
  simp only [Derivation.commutator_apply, Nat.zero_le, if_true, Nat.sub_zero,
    Derivation.smul_apply] at hd
  rw [hypSugawara_zero, hypSugawara_zero, map_add, Derivation.map_smul]
  change (κ * ell) • pderiv (t, a) p + hypRaisingDerivation 0 (pderiv (t, a) p) -
    ((κ * ell) • pderiv (t, a) p + pderiv (t, a) (hypRaisingDerivation 0 p)) = _
  rw [add_sub_add_left_eq_sub, hd]

theorem hypSugawara_zero_oscillator_comm (κ ell : ℂ) (a : Fin 2) (n : ℤ) :
    ⁅hypSugawara κ ell 0, hypOscillator a (if a = 0 then κ else ell) n⁆ =
      -(n : ℂ) • hypOscillator a (if a = 0 then κ else ell) n := by
  apply LinearMap.ext
  intro p
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = -(t + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    rw [hypOscillator_negative_apply, hypOscillator_negative_apply, hypSugawara_zero_creation]
    simp
  · simp only [hypOscillator_zero, LinearMap.smul_apply, LinearMap.id_apply,
      map_smul, sub_self, Int.cast_zero, neg_zero, zero_smul]
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = (t + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
    rw [hypOscillator_positive_apply, hypOscillator_positive_apply,
      map_smul, ← smul_sub, hypSugawara_zero_pderiv]
    simp only [smul_smul, Int.cast_add, Int.cast_natCast, Int.cast_one]
    congr 1
    ring

/-- The complete mixed relation, including zero oscillator index and all momenta. -/
theorem hypSugawara_oscillator_comm (κ ell : ℂ) (m : ℤ) (a : Fin 2) (n : ℤ) :
    ⁅hypSugawara κ ell m, hypOscillator a (if a = 0 then κ else ell) n⁆ =
      -(n : ℂ) • hypOscillator a (if a = 0 then κ else ell) (m + n) := by
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j + 1 : ℤ) := ⟨(-m - 1).toNat, by omega⟩
    simpa only [sub_eq_add_neg, add_comm] using hypSugawara_negative_oscillator_comm κ ell j a n
  · simpa only [zero_add] using hypSugawara_zero_oscillator_comm κ ell a n
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j + 1 : ℤ) := ⟨(m - 1).toNat, by omega⟩
    simpa only [add_comm] using hypSugawara_positive_oscillator_comm κ ell j a n

end VOA.Moonshine.ConwayNorton
