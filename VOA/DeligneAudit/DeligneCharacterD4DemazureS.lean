/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Demazure

/-!
# Demazure operators on `S = R⟦s⟧` and Weyl invariance of the kernel (layer 5b)

* `smap ℓ`: a `𝕜`-linear map of `R` applied coefficientwise in `s`;
* `piS_div`, `pi0S_div`: the division formulas in `S`;
* `piS_mul_of_inv`: `π_α (g F) = g π_α F` for `s_α`-invariant `g` (cancellation in the domain `S`);
* `map_domHom_kernelM`: the kernel is invariant under the simple reflections and `s_θ`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- Apply a `𝕜`-linear map of `R` to every `s`-coefficient. -/
def smap (ℓ : R →ₗ[Kq] R) (F : S) : S := mk fun n => ℓ (coeff n F)

theorem coeff_smap (ℓ : R →ₗ[Kq] R) (F : S) (n : ℕ) : coeff n (smap ℓ F) = ℓ (coeff n F) :=
  coeff_mk _ _

theorem piS_div (α : V) (F : S) :
    C (1 - mon (-α) 1) * smap (piR α) F =
      F - C (mon (-α) 1) * PowerSeries.map (domHom (reflV α) : R →+* R) F := by
  ext n : 1
  rw [coeff_C_mul, coeff_smap, piR_div, map_sub, coeff_C_mul, coeff_map]
  rfl

theorem pi0S_div (F : S) :
    C (1 - mon thetaV qq⁻¹) * smap pi0R F =
      F - C (mon ((2 : ℤ) • thetaV) (qq ^ (-2 : ℤ))) *
        PowerSeries.map (twist chiTheta qq⁻¹ (inv_ne_zero qq_ne_zero) : R →+* R)
          (PowerSeries.map (domHom (reflV thetaV) : R →+* R) F) := by
  ext n : 1
  rw [coeff_C_mul, coeff_smap, pi0R_div, map_sub, coeff_C_mul, coeff_map, coeff_map]
  rfl

theorem mon_ne_one (v : V) (hv : v ≠ 0) : mon v 1 ≠ 1 := by
  intro h
  have : mon v 1 = mon 0 1 := h
  exact hv ((Finsupp.single_left_inj one_ne_zero).mp this)

theorem C_one_sub_mon_ne_zero (v : V) (c : Kq) (hv : v ≠ 0) :
    (C (1 - mon v c) : S) ≠ 0 := by
  intro h
  have h' := congrArg constantCoeff h
  rw [constantCoeff_C, map_zero, sub_eq_zero] at h'
  have : mon 0 1 = mon v c := h'
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp this with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hv h1.symm
  · exact one_ne_zero h1

/-- `π_α` is linear over `s_α`-invariant multipliers. -/
theorem piS_mul_of_inv (α : V) (hα : α ≠ 0) (g F : S)
    (hg : PowerSeries.map (domHom (reflV α) : R →+* R) g = g) :
    smap (piR α) (g * F) = g * smap (piR α) F := by
  have hne : (C (1 - mon (-α) 1) : S) ≠ 0 :=
    C_one_sub_mon_ne_zero (-α) 1 (neg_ne_zero.mpr hα)
  apply mul_left_cancel₀ hne
  rw [piS_div, map_mul, hg,
    show C (1 - mon (-α) 1) * (g * smap (piR α) F) = g * (C (1 - mon (-α) 1) * smap (piR α) F)
      by ring, piS_div]
  ring

/-! ## Weyl invariance of `M` -/

theorem map_domHom_liftS (f : V →+ V) (F : PowerSeries Kq) :
    PowerSeries.map (domHom f : R →+* R) (liftS F) = liftS F := by
  rw [liftS, ← RingHom.comp_apply, ← PowerSeries.map_comp]
  congr 2
  exact (domHom f).comp_algebraMap

theorem map_domHom_EInv (f : V →+ V) (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    PowerSeries.map (domHom f : R →+* R) (EInv c v k hk) = EInv c (f v) k hk := by
  rw [EInv, EInv, map_expand, ← rescale_map, map_domHom_liftS]
  rw [show ((domHom f : R →+* R) (mon v c)) = mon (f v) c from domHom_mon f v c]

theorem map_domHom_EPos (f : V →+ V) (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    PowerSeries.map (domHom f : R →+* R) (EPos c v k hk) = EPos c (f v) k hk := by
  rw [EPos, EPos, map_expand, ← rescale_map, map_domHom_liftS]
  rw [show ((domHom f : R →+* R) (mon v c)) = mon (f v) c from domHom_mon f v c]

/-- The simple roots of `D₄` in `V`. -/
def rootV : Fin 4 → V
  | 0 => zv 0 - zv 1
  | 1 => zv 1 - zv 2
  | 2 => zv 2 - zv 3
  | 3 => zv 2 + zv 3

theorem hyperVecs_perm_root (i : Fin 4) : (hyperVecs.map (reflV (rootV i))).Perm hyperVecs := by
  fin_cases i <;> decide

theorem hyperVecs_perm_theta : (hyperVecs.map (reflV thetaV)).Perm hyperVecs := by decide

theorem reflV_of_dotZ (α v : V) (h : dotZ v α = 0) : reflV α v = v := by
  rw [reflV_apply, h, zero_smul, sub_zero]

theorem map_domHom_kernelM (α : V)
    (hperm : (hyperVecs.map (reflV α)).Perm hyperVecs) :
    PowerSeries.map (domHom (reflV α) : R →+* R) kernelM = kernelM := by
  have h2 : dotZ (2 • xv) α = 0 := by simp [dotZ, xv, Fin.succ_ne_zero]
  have h3 : dotZ ((-2 : ℤ) • xv) α = 0 := by simp [dotZ, xv, Fin.succ_ne_zero]
  rw [kernelM, tFactors, hyperFactors_eq, map_mul, map_mul, map_mul, map_domHom_EPos,
    map_domHom_EPos, map_domHom_EPos, map_zero, reflV_of_dotZ α _ h2, reflV_of_dotZ α _ h3]
  congr 1
  unfold prodE
  rw [map_list_prod, List.map_map]
  have : (fun v => PowerSeries.map (domHom (reflV α) : R →+* R) (EInv 1 v 1 one_ne_zero)) =
      fun v => EInv 1 (reflV α v) 1 one_ne_zero := by
    funext v; exact map_domHom_EInv _ _ _ _ _
  simp only [Function.comp_def]
  rw [this, show (hyperVecs.map fun x => EInv 1 (reflV α x) 1 one_ne_zero) =
    (hyperVecs.map (reflV α)).map (fun v => EInv 1 v 1 one_ne_zero) by rw [List.map_map]; rfl]
  exact (hperm.map _).prod_eq

theorem map_reflRoot_kernelM (i : Fin 4) :
    PowerSeries.map (domHom (reflV (rootV i)) : R →+* R) kernelM = kernelM :=
  map_domHom_kernelM _ (hyperVecs_perm_root i)

theorem map_reflTheta_kernelM :
    PowerSeries.map (domHom (reflV thetaV) : R →+* R) kernelM = kernelM :=
  map_domHom_kernelM _ hyperVecs_perm_theta

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.piS_mul_of_inv
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.pi0S_div
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.map_reflRoot_kernelM
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.map_reflTheta_kernelM
end AxiomAudit
