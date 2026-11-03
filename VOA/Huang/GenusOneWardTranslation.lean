import VOA.Modularity.SqModeWeight
import VOA.Modularity.SquareBracketWitt

/-!
# Square-bracket coefficients of `L[−1]a`

Zhu's coefficients `c(k,m,i) = [w^{i−m}]((1+w)^{k−1} u^m)` satisfy
`−(i+1) c(k+1,m,i+1) + k c(k,m,i) = −m c(k,m−1,i)` for all integers `m,i`.
With `(L₋₁a)₍ᵢ₎ = −i a₍ᵢ₋₁₎` this is `(L[−1]a)[m] = −m a[m−1]` for
`L[−1]a = L₋₁a + k a`, `a ∈ V_k`. The proof is the power-series identity
`m P + w P′ = k w P' + m P''` reduced to `(1+w)(u + w u′) = 1`.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA PowerSeries

/-- The power-series form of the translation identity. -/
theorem translation_powerSeries (k : ℕ) (m : ℤ) :
    (m : PowerSeries ℂ) * ((↑(onePlusXUnit ^ ((k : ℤ))) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ)) +
        PowerSeries.X * derivativeFun ((↑(onePlusXUnit ^ ((k : ℤ))) : PowerSeries ℂ) * (↑(uUnit ^ m) : PowerSeries ℂ)) =
      (k : PowerSeries ℂ) * PowerSeries.X * ((↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) *
          (↑(uUnit ^ m) : PowerSeries ℂ)) +
        (m : PowerSeries ℂ) * ((↑(onePlusXUnit ^ ((k : ℤ) - 1)) : PowerSeries ℂ) *
          (↑(uUnit ^ (m - 1)) : PowerSeries ℂ)) := by
  rw [derivativeFun_mul, derivativeFun_onePlusXUnit_zpow, derivativeFun_uUnit_zpow]
  have hE : (↑(onePlusXUnit ^ ((k : ℤ))) : PowerSeries ℂ) =
      ↑(onePlusXUnit ^ ((k : ℤ) - 1)) * (1 + PowerSeries.X : PowerSeries ℂ) := by
    rw [← onePlusXUnit_coe, ← Units.val_mul, ← zpow_add_one]
    congr 2
    ring
  have hU : (↑(uUnit ^ m) : PowerSeries ℂ) = ↑(uUnit ^ (m - 1)) * uSeries := by
    rw [← uUnit_coe, ← Units.val_mul, ← zpow_add_one]
    congr 2
    ring
  have hode := uSeries_ODE
  rw [hE, hU]
  simp only [smul_eq_mul]
  have hk : ((k : ℤ) : PowerSeries ℂ) = (k : PowerSeries ℂ) := by norm_cast
  rw [hk]
  linear_combination ((m : PowerSeries ℂ) * ↑(onePlusXUnit ^ ((k : ℤ) - 1)) *
    (↑(uUnit ^ (m - 1)) : PowerSeries ℂ)) * hode

/-- **The translation identity for Zhu's square-bracket coefficients.** -/
theorem sqBracketCoeffZ_translation (k : ℕ) (m i : ℤ) :
    -((i : ℂ) + 1) * sqBracketCoeffZ (k + 1) m (i + 1) + (k : ℂ) * sqBracketCoeffZ k m i =
      -(m : ℂ) * sqBracketCoeffZ k (m - 1) i := by
  have hk1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
  unfold sqBracketCoeffZ
  rw [hk1]
  rcases lt_trichotomy (i + 1) m with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    have h1 : (i + 1 - m).toNat = 0 := by omega
    have h2 : (i - (m - 1)).toNat = 0 := by omega
    rw [h1, h2, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      map_mul, map_mul, constantCoeff_unit_zpow _ constantCoeff_onePlusX,
      constantCoeff_unit_zpow _ constantCoeff_uUnit,
      constantCoeff_unit_zpow _ constantCoeff_onePlusX,
      constantCoeff_unit_zpow _ constantCoeff_uUnit]
    have : (i : ℂ) + 1 = m := by exact_mod_cast h
    rw [this]
    ring
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    obtain ⟨r, hr⟩ : ∃ r : ℕ, i - m = r := ⟨(i - m).toNat, by omega⟩
    have h1 : (i + 1 - m).toNat = r + 1 := by omega
    have h2 : (i - m).toNat = r := by omega
    have h3 : (i - (m - 1)).toNat = r + 1 := by omega
    rw [h1, h2, h3]
    have hc := congrArg (PowerSeries.coeff (R := ℂ) (r + 1)) (translation_powerSeries k m)
    have hmC : ∀ (n : ℕ) (a : ℤ) (f : PowerSeries ℂ),
        PowerSeries.coeff (R := ℂ) n ((a : PowerSeries ℂ) * f) =
          (a : ℂ) * PowerSeries.coeff (R := ℂ) n f := by
      intro n a f
      rw [show ((a : PowerSeries ℂ)) = PowerSeries.C (a : ℂ) by simp, coeff_C_mul]
    have hkC : ∀ (n : ℕ) (f : PowerSeries ℂ),
        PowerSeries.coeff (R := ℂ) n ((k : PowerSeries ℂ) * f) =
          (k : ℂ) * PowerSeries.coeff (R := ℂ) n f := by
      intro n f
      rw [show ((k : PowerSeries ℂ)) = PowerSeries.C (k : ℂ) by simp, coeff_C_mul]
    rw [map_add, map_add, coeff_X_mul_derivativeFun, mul_assoc (k : PowerSeries ℂ),
      hmC, hmC, hkC, coeff_succ_X_mul] at hc
    have hi : (i : ℂ) = (m : ℂ) + r := by
      have : i = m + r := by omega
      rw [this]; push_cast; ring
    rw [hi]
    push_cast at hc ⊢
    linear_combination -hc

end VOA.Huang.GenusOneWard
