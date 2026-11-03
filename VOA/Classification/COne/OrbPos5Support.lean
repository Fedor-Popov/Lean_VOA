import VOA.Classification.COne.OrbPos5Conformal

/-! # Torus eigenspace support of the constructed all-state fractional fields -/

namespace VOA.Classification.COne.OrbPos5
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 LatMod

noncomputable def phase (n : ℕ) (b : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * b / n)

noncomputable def torusUnit (n : ℕ) (a : ℤ) : ℂˣ :=
  Units.mk0 (phase n a) (Complex.exp_ne_zero _)

noncomputable def shiftAut (n : ℕ) (a : ℤ) : Aut (V2m 1 le_rfl) :=
  charU 1 le_rfl (torusUnit n a)

theorem phase_eq_iff {n : ℕ} (hn : 0 < n) (b c : ℤ) :
    phase n b = phase n c ↔ (b-c) % (n : ℤ) = 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have ht : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [phase, phase, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    have hr : (b : ℂ)/n = (c : ℂ)/n + k := by
      apply mul_left_cancel₀ ht
      linear_combination hk
    have hz : (b : ℂ) - c = (n : ℂ)*k := by
      field_simp at hr
      linear_combination hr
    have hi : b-c = (n : ℤ)*k := by exact_mod_cast hz
    exact Int.emod_eq_zero_of_dvd ⟨k, hi⟩
  · intro h
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨k, ?_⟩
    have hz : (b : ℂ) - c = (n : ℂ)*k := by exact_mod_cast hk
    field_simp
    linear_combination hz

theorem shiftAut_latState (n : ℕ) (a β : ℤ) (p : Osc) :
    shiftAut n a (latStateGen (latP 1) p β) =
      phase n (a*β) • latStateGen (latP 1) p β := by
  rw [shiftAut, charU_latStateGen]
  simp only [Units.val_zpow_eq_zpow_val, ci]
  change ((torusUnit n a : ℂˣ) : ℂ)^β • latStateGen (latP 1) p β = _
  change (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * a / n))^β •
    latStateGen (latP 1) p β = _
  rw [← Complex.exp_int_mul]
  congr 2
  push_cast
  ring

/-- The chosen denominator is a period; exact order is not asserted for
non-coprime numerators. -/
theorem shiftAut_pow {n : ℕ} (hn : 0 < n) (a : ℤ) : shiftAut n a ^ n = 1 := by
  have hu : torusUnit n a ^ n = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    change (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * a / n))^n = 1
    rw [← Complex.exp_nat_mul]
    have hp : phase n ((n : ℤ)*a) = phase n 0 :=
      (phase_eq_iff hn _ _).mpr (by simp)
    simpa only [phase, Int.cast_mul, Int.cast_natCast, Int.cast_zero, mul_zero,
      zero_div, Complex.exp_zero, show (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * a / n) =
        2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ)*a) / n by ring] using hp
  exact (map_pow (charU 1 le_rfl) (torusUnit n a) n).symm.trans
    (by rw [hu, map_one]; rfl)

/-- Covariance of the actual field map under the torus automorphism. -/
theorem shiftedY_covariance {n : ℕ} (hn : 0 < n) (a j ℓ : ℤ) (u : Space) :
    shiftedY n a j (shiftAut n a u) ℓ = phase n ℓ • shiftedY n a j u ℓ := by
  let ev : Modes →ₗ[ℂ] Module.End ℂ Space := LinearMap.proj ℓ
  have he : (ev.comp (shiftedY n a j)).comp (shiftAut n a).toLinearEquiv.toLinearMap =
      phase n ℓ • (ev.comp (shiftedY n a j)) := by
    apply LinearMap.ext_on_range (latStateGen_span (latP 1))
    rintro ⟨p, β⟩
    change ℤ at β
    change shiftedY n a j (shiftAut n a (latStateGen (latP 1) p β)) ℓ =
      phase n ℓ • shiftedY n a j (latStateGen (latP 1) p β) ℓ
    rw [shiftAut_latState, map_smul, Pi.smul_apply, shiftedY_latState]
    by_cases h : (ℓ-a*β) % (n : ℤ) = 0
    · rw [(phase_eq_iff hn ℓ (a*β)).mpr h]
    · rw [sectorField_support n a j β ℓ p h, smul_zero, smul_zero]
  exact congrArg (fun f : Space →ₗ[ℂ] Module.End ℂ Space => f u) he

/-- The precise support field of `TwistedModule`, for all lattice states. -/
theorem shiftedY_support {n : ℕ} (hn : 0 < n) (a j : ℤ) (r : ℕ) (u : Space)
    (hu : u ∈ (shiftAut n a).twistedEigenspace n r) (ℓ : ℤ)
    (hℓ : (ℓ + r) % (n : ℤ) ≠ 0) : shiftedY n a j u ℓ = 0 := by
  have he : shiftAut n a u = phase n (-(r : ℤ)) • u := by
    rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff] at hu
    convert hu using 2
    simp only [phase, Int.cast_neg, Int.cast_natCast]
    congr 1
    ring
  have hc := shiftedY_covariance hn a j ℓ u
  rw [he, map_smul, Pi.smul_apply] at hc
  have hne : phase n (-(r : ℤ)) - phase n ℓ ≠ 0 := by
    intro hz
    have hp := (phase_eq_iff hn ℓ (-(r : ℤ))).mp (sub_eq_zero.mp hz).symm
    exact hℓ (by simpa using hp)
  have hz : (phase n (-(r : ℤ)) - phase n ℓ) • shiftedY n a j u ℓ = 0 := by
    rw [sub_smul, hc, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hne

end VOA.Classification.COne.OrbPos5
