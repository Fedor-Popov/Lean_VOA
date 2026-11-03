import VOA.DeligneAudit.DeligneFusionCVPolarization

/-!
# Three-color polarization from one highest-root coefficient

This is an abstract current-operator identity. The current families satisfy
the displayed commutators, and two raising operators kill the vector. One
vanishing highest-root coefficient then gives every ordered three-color
coefficient of the same total power and current degree. No mixed-current
vanishing or leading-ideal premise is assumed.
-/

namespace VOA.DeligneAudit.A2.CVPolarizationThree

open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.Garland

noncomputable section

section Ring

variable {A : Type*} [Ring A] {E P Y Z : A}

/-- A commuting prefix is unchanged by polarization of the following factors. -/
theorem prefixed_power_commutator (hEP : E * P = P * E)
    (hEY : E * Y - Y * E = Z) (hEZ : E * Z = Z * E)
    (hYZ : Y * Z = Z * Y) (r q : ℕ) :
    E * (P * (Z ^ r * Y ^ (q + 1))) - (P * (Z ^ r * Y ^ (q + 1))) * E =
      (q + 1) • (P * (Z ^ (r + 1) * Y ^ q)) := by
  have h := CVPolarization.mixed_power_commutator hEY hEZ hYZ r q
  calc
    E * (P * (Z ^ r * Y ^ (q + 1))) - (P * (Z ^ r * Y ^ (q + 1))) * E =
        P * (E * (Z ^ r * Y ^ (q + 1)) - (Z ^ r * Y ^ (q + 1)) * E) := by
          rw [← mul_assoc E P, hEP]
          noncomm_ring
    _ = P * ((q + 1) • (Z ^ (r + 1) * Y ^ q)) := by rw [h]
    _ = (q + 1) • (P * (Z ^ (r + 1) * Y ^ q)) := by rw [mul_smul_comm]

end Ring

section Current

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (X Y Z : ℕ → Module.End ℂ V)

/-- Ordered first-root, highest-root, second-root coefficient. -/
def threeCoeff (p q r s : ℕ) : Module.End ℂ V :=
  PowerSeries.coeff s (Fs X ^ p * Fs Y ^ q * Fs Z ^ r)

theorem threeCoeff_commutator (E : Module.End ℂ V)
    (hEY : ∀ k, E * Y k - Y k * E = Z k)
    (hEX : ∀ k, E * X k = X k * E)
    (hEZ : ∀ k, E * Z k = Z k * E)
    (hYZ : ∀ k l, Y k * Z l = Z l * Y k) (p q r s : ℕ) :
    E * threeCoeff X Y Z p (q + 1) r s - threeCoeff X Y Z p (q + 1) r s * E =
      (q + 1) • threeCoeff X Y Z p q (r + 1) s := by
  have hEYs : PowerSeries.C E * Fs Y - Fs Y * PowerSeries.C E = Fs Z := by
    apply PowerSeries.ext
    intro k
    simpa only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      Fs, PowerSeries.coeff_mk] using hEY k
  have hEXs : PowerSeries.C E * Fs X = Fs X * PowerSeries.C E := by
    apply PowerSeries.ext
    intro k
    simpa only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      Fs, PowerSeries.coeff_mk] using hEX k
  have hEZs : PowerSeries.C E * Fs Z = Fs Z * PowerSeries.C E := by
    apply PowerSeries.ext
    intro k
    simpa only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      Fs, PowerSeries.coeff_mk] using hEZ k
  have hYZs : Fs Y * Fs Z = Fs Z * Fs Y := current_series_commute hYZ
  have hEP : PowerSeries.C E * Fs X ^ p = Fs X ^ p * PowerSeries.C E :=
    (show Commute (PowerSeries.C E) (Fs X) from hEXs).pow_right p
  have h := prefixed_power_commutator hEP hEYs hEZs hYZs r q
  have hZY1 : Fs Z ^ r * Fs Y ^ (q + 1) = Fs Y ^ (q + 1) * Fs Z ^ r :=
    ((show Commute (Fs Y) (Fs Z) from hYZs).pow_pow (q + 1) r).symm
  have hZY2 : Fs Z ^ (r + 1) * Fs Y ^ q = Fs Y ^ q * Fs Z ^ (r + 1) :=
    ((show Commute (Fs Y) (Fs Z) from hYZs).pow_pow q (r + 1)).symm
  rw [hZY1, hZY2] at h
  have hc := congrArg (PowerSeries.coeff s) h
  simp only [map_sub, map_nsmul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_C] at hc
  simpa only [threeCoeff, mul_assoc] using hc

/-- A single highest-root current coefficient polarizes to every three-color
coefficient of the same total power. The original currents need only satisfy
the stated cross-family commutators. -/
theorem threeCoeff_zero_of_Q (E₂ E₁ : Module.End ℂ V)
    (hE₂Y : ∀ k, E₂ * Y k - Y k * E₂ = X k)
    (hE₂X : ∀ k, E₂ * X k = X k * E₂)
    (hYX : ∀ k l, Y k * X l = X l * Y k)
    (hE₁Y : ∀ k, E₁ * Y k - Y k * E₁ = Z k)
    (hE₁X : ∀ k, E₁ * X k = X k * E₁)
    (hE₁Z : ∀ k, E₁ * Z k = Z k * E₁)
    (hYZ : ∀ k l, Y k * Z l = Z l * Y k)
    {w : V} (hE₂w : E₂ w = 0) (hE₁w : E₁ w = 0)
    {d s : ℕ} (hQ : Q Y d s w = 0) :
    ∀ p q r, p + q + r = d → threeCoeff X Y Z p q r s w = 0 := by
  intro p q r
  induction r generalizing q with
  | zero =>
      intro hd
      have hm := CVPolarization.mixedCoeff_zero_of_Q Y X E₂ hE₂Y hE₂X hYX
        hE₂w hQ p q (by omega)
      simpa only [threeCoeff, pow_zero, mul_one, CVPolarization.mixedCoeff] using hm
  | succ r ih =>
      intro hd
      have hp := ih (q + 1) (by omega)
      have hc := congrArg (fun T : Module.End ℂ V => T w)
        (threeCoeff_commutator X Y Z E₁ hE₁Y hE₁X hE₁Z hYZ p q r s)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        hp, hE₁w, map_zero, sub_self] at hc
      have hz : (q + 1) • (threeCoeff X Y Z p q (r + 1) s w) = 0 := hc.symm
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at hz
      exact hz.resolve_left (by exact_mod_cast Nat.succ_ne_zero q)

end Current

end

end VOA.DeligneAudit.A2.CVPolarizationThree

#print axioms VOA.DeligneAudit.A2.CVPolarizationThree.threeCoeff_commutator
#print axioms VOA.DeligneAudit.A2.CVPolarizationThree.threeCoeff_zero_of_Q
