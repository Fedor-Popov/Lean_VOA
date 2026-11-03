/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4DemazureS

/-!
# The Demazure operator `B` on the shifted kernel (layer 6a)

`B = π_{s_θ} π₀`, with `π_{s_θ}` the composite of `π_{α_i}` along `2,1,3,2,4,2,3,1,2`.

**`Bop_kernel`**: there is `Y ∈ S` with `(1 - q⁻¹z^θ) Y = P₀ - q⁻²z^{2θ} P_θ` and
`B[M(qs)] · (1-t)(1-qt)D₊D₋ = M · π_{s_θ} Y`.

This is the formal content of the paper's reduction of `B[K(q²t)]/K(t)` to the finite polynomial
`F = π_{s_θ}[(P₀ - q⁻²z^{2θ}P_θ)/(1 - q⁻¹z^θ)]`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- The reduced word for `s_θ`, as indices into `rootV`, first letter applied first. -/
def wordS : List (Fin 4) := [1, 0, 2, 1, 3, 1, 2, 0, 1]

/-- `π_{s_θ}` on `S`. -/
def piThetaS (F : S) : S := wordS.foldl (fun G i => smap (piR (rootV i)) G) F

/-- `B = π_{s_θ} π₀` on `S`. -/
def Bop (F : S) : S := piThetaS (smap pi0R F)

/-- `(1-t)(1-qt)D₊D₋`. -/
def denS : S := Tden * Dp * Dm

/-- `N = P₀ - q⁻²z^{2θ}P_θ`. -/
def NS : S := P0S - C (mon ((2 : ℤ) • thetaV) (qq ^ (-2 : ℤ))) * PthetaS

/-! ## Units -/

theorem constantCoeff_liftS (f : PowerSeries Kq) :
    constantCoeff (liftS f) = algebraMap Kq R (constantCoeff f) := by
  rw [liftS, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]

theorem constantCoeff_rescale' (a : R) (f : S) : constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

theorem constantCoeff_EInv (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    constantCoeff (EInv c v k hk) = 1 := by
  rw [EInv, constantCoeff_expand, constantCoeff_rescale', constantCoeff_liftS, eInv,
    ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp [qpoch]
  rfl

theorem constantCoeff_EPos (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    constantCoeff (EPos c v k hk) = 1 := by
  rw [EPos, constantCoeff_expand, constantCoeff_rescale', constantCoeff_liftS, ePos,
    ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp [qpoch]
  rfl

theorem constantCoeff_kernelM : constantCoeff kernelM = 1 := by
  rw [kernelM, tFactors, hyperFactors_eq, prodE, map_mul, map_mul, map_mul, constantCoeff_EPos,
    constantCoeff_EPos, constantCoeff_EPos, map_list_prod, List.map_map]
  simp [Function.comp_def, constantCoeff_EInv]

theorem constantCoeff_one_sub_smul (v : V) (c : Kq) (k : ℕ) (hk : k ≠ 0) :
    constantCoeff (1 - mon v c • X ^ k : S) = 1 := by
  rw [smul_eq_C_mul, map_sub, map_one, map_mul, constantCoeff_C, map_pow, constantCoeff_X,
    zero_pow hk, mul_zero, sub_zero]

theorem constantCoeff_denS : constantCoeff denS = 1 := by
  simp only [denS, Tden, Dp, Dm, map_mul]
  rw [constantCoeff_one_sub_smul _ _ 2 two_ne_zero, constantCoeff_one_sub_smul _ _ 2 two_ne_zero,
    constantCoeff_one_sub_smul _ _ 2 two_ne_zero, constantCoeff_one_sub_smul _ _ 2 two_ne_zero,
    constantCoeff_one_sub_smul _ _ 2 two_ne_zero, constantCoeff_one_sub_smul _ _ 2 two_ne_zero]
  ring

theorem isUnit_kernelM : IsUnit kernelM := by
  rw [isUnit_iff_constantCoeff, constantCoeff_kernelM]; exact isUnit_one

theorem isUnit_denS : IsUnit denS := by
  rw [isUnit_iff_constantCoeff, constantCoeff_denS]; exact isUnit_one

/-! ## Invariance of the denominator -/

theorem map_domHom_one_sub_smul (f : V →+ V) (v : V) (c : Kq) (k : ℕ) :
    PowerSeries.map (domHom f : R →+* R) (1 - mon v c • X ^ k) = 1 - mon (f v) c • X ^ k := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_sub, map_one, map_mul, map_C, map_pow, map_X]
  rw [show ((domHom f : R →+* R) (mon v c)) = mon (f v) c from domHom_mon f v c]

theorem map_domHom_denS (α : V) :
    PowerSeries.map (domHom (reflV α) : R →+* R) denS = denS := by
  have h0 : reflV α 0 = 0 := map_zero _
  have h2 : reflV α (2 • xv) = 2 • xv :=
    reflV_of_dotZ α _ (by simp [dotZ, xv, Fin.succ_ne_zero])
  have h3 : reflV α ((-2 : ℤ) • xv) = (-2 : ℤ) • xv :=
    reflV_of_dotZ α _ (by simp [dotZ, xv, Fin.succ_ne_zero])
  simp only [denS, Tden, Dp, Dm, map_mul, map_domHom_one_sub_smul, h0, h2, h3]

theorem map_domHom_rescale (f : V →+ V) (a : Kq) (F : S) :
    PowerSeries.map (domHom f : R →+* R) (rescale (algebraMap Kq R a) F) =
      rescale (algebraMap Kq R a) (PowerSeries.map (domHom f : R →+* R) F) := by
  rw [← rescale_map]
  congr 2
  exact (domHom f).commutes a

/-! ## `π_{s_θ}` is linear over `W`-invariant multipliers -/

theorem piThetaS_mul_of_inv (g F : S)
    (hg : ∀ i : Fin 4, PowerSeries.map (domHom (reflV (rootV i)) : R →+* R) g = g) :
    piThetaS (g * F) = g * piThetaS F := by
  have hne : ∀ i : Fin 4, rootV i ≠ 0 := by decide
  unfold piThetaS
  generalize F = F₀
  suffices ∀ (w : List (Fin 4)) (G : S),
      w.foldl (fun G i => smap (piR (rootV i)) G) (g * G) =
        g * w.foldl (fun G i => smap (piR (rootV i)) G) G from this wordS F₀
  intro w
  induction w with
  | nil => intro G; rfl
  | cons i w ih =>
      intro G
      simp only [List.foldl_cons]
      rw [piS_mul_of_inv (rootV i) (hne i) g G (hg i), ih]

/-- A ring endomorphism fixing a unit fixes its inverse. -/
theorem map_inv_of_fix (φ : S →+* S) (d : Sˣ) (h : φ d = d) : φ ↑d⁻¹ = ↑d⁻¹ := by
  have h1 : φ (d : S) * φ ↑d⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  rw [h] at h1
  calc φ ↑d⁻¹ = (↑d⁻¹ * d) * φ ↑d⁻¹ := by rw [Units.inv_mul, one_mul]
    _ = ↑d⁻¹ * (d * φ ↑d⁻¹) := by ring
    _ = ↑d⁻¹ := by rw [h1, mul_one]

/-- **The Demazure step on the kernel.** -/
theorem Bop_kernel : ∃ Y : S, C (1 - mon thetaV qq⁻¹) * Y = NS ∧
    Bop (rescale (algebraMap Kq R qq) kernelM) * denS = kernelM * piThetaS Y := by
  set Mq := rescale (algebraMap Kq R qq) kernelM with hMq
  set m := mon thetaV qq⁻¹
  set m2 := mon ((2 : ℤ) • thetaV) (qq ^ (-2 : ℤ))
  set P := smap pi0R Mq with hP
  -- the division formula, with `s_θ`-invariance and the two ratio identities
  have hrefl : PowerSeries.map (domHom (reflV thetaV) : R →+* R) Mq = Mq := by
    rw [hMq, map_domHom_rescale, map_reflTheta_kernelM]
  have hdiv : C (1 - m) * P = Mq - C m2 *
      PowerSeries.map (twist chiTheta qq⁻¹ (inv_ne_zero qq_ne_zero) : R →+* R) Mq := by
    rw [hP, pi0S_div, hrefl]
  have hkey : C (1 - m) * (P * denS) = kernelM * NS := by
    have h1 := rescale_kernelM
    have h2 := thetaShift_kernelM
    rw [← denS, ← hMq] at h1 h2
    rw [← mul_assoc, hdiv, sub_mul, mul_assoc, h2, h1, NS]
    ring
  obtain ⟨u, hu⟩ := isUnit_kernelM
  obtain ⟨d, hd⟩ := isUnit_denS
  refine ⟨P * denS * ↑u⁻¹, ?_, ?_⟩
  · rw [← mul_assoc, hkey, ← hu, mul_comm (u : S), mul_assoc, Units.mul_inv, mul_one]
  · -- `P = g · Y` with the `W`-invariant `g = M · den⁻¹`
    have hg : ∀ i : Fin 4, PowerSeries.map (domHom (reflV (rootV i)) : R →+* R)
        (kernelM * ↑d⁻¹) = kernelM * ↑d⁻¹ := by
      intro i
      rw [map_mul, map_reflRoot_kernelM]
      congr 1
      apply map_inv_of_fix
      rw [hd]; exact map_domHom_denS _
    have hPY : P = (kernelM * ↑d⁻¹) * (P * denS * ↑u⁻¹) := by
      rw [← hd, ← hu]
      calc P = P * ((d : S) * ↑d⁻¹) * ((u : S) * ↑u⁻¹) := by
            rw [Units.mul_inv, Units.mul_inv, mul_one, mul_one]
        _ = _ := by ring
    have hB : Bop Mq = (kernelM * ↑d⁻¹) * piThetaS (P * denS * ↑u⁻¹) := by
      rw [Bop, ← hP]
      nth_rewrite 1 [hPY]
      exact piThetaS_mul_of_inv _ _ hg
    rw [hB, ← hd]
    calc kernelM * ↑d⁻¹ * piThetaS (P * ↑d * ↑u⁻¹) * ↑d
        = kernelM * (↑d⁻¹ * ↑d) * piThetaS (P * ↑d * ↑u⁻¹) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.Bop_kernel
end AxiomAudit
