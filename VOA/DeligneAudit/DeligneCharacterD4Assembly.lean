/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Bridge

/-!
# Assembly of the D₄ recursion (layer 7, part 1): commutation lemmas

* `smap` commutes with `𝕜`-scalars, powers of `s`, and `rescale`;
* the constant-term functionals commute with the Demazure operators (`ctFun_piR`, `ctFun_pi0R`), since
  the latter act on `z` and the former on `x`; hence `smap ctTheta ∘ B = B ∘ smap ctTheta`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-! ## `smap` -/

theorem smap_add (ℓ : R →ₗ[Kq] R) (F G : S) : smap ℓ (F + G) = smap ℓ F + smap ℓ G := by
  ext n : 1; simp [coeff_smap]

theorem smap_sub (ℓ : R →ₗ[Kq] R) (F G : S) : smap ℓ (F - G) = smap ℓ F - smap ℓ G := by
  ext n : 1; simp [coeff_smap]

theorem smap_C_mul (ℓ : R →ₗ[Kq] R) (a : Kq) (F : S) :
    smap ℓ (C (algebraMap Kq R a) * F) = C (algebraMap Kq R a) * smap ℓ F := by
  ext n : 1
  rw [coeff_smap, coeff_C_mul, coeff_C_mul, coeff_smap, ← Algebra.smul_def, ← Algebra.smul_def,
    map_smul]

theorem smap_X_pow_mul (ℓ : R →ₗ[Kq] R) (k : ℕ) (F : S) :
    smap ℓ (X ^ k * F) = X ^ k * smap ℓ F := by
  ext n : 1
  rw [coeff_smap, coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs <;> simp [coeff_smap]

theorem smap_rescale (ℓ : R →ₗ[Kq] R) (a : Kq) (F : S) :
    smap ℓ (rescale (algebraMap Kq R a) F) = rescale (algebraMap Kq R a) (smap ℓ F) := by
  ext n : 1
  rw [coeff_smap, coeff_rescale, coeff_rescale, coeff_smap, ← map_pow, ← Algebra.smul_def,
    ← Algebra.smul_def, map_smul]

theorem smap_comp (ℓ ℓ' : R →ₗ[Kq] R) (F : S) : smap ℓ (smap ℓ' F) = smap (ℓ ∘ₗ ℓ') F := by
  ext n : 1; simp [coeff_smap]

/-! ## `x`-forgetting is compatible with the `z`-operators -/

theorem killX_apply_zero (v : V) : killX v 0 = 0 := by simp [killX]

theorem killX_sub_smul (v α : V) (hα : α 0 = 0) (k : ℤ) :
    killX (v - k • α) = killX v - k • α := by
  ext i
  by_cases h : i = 0
  · subst h; simp [killX, hα]
  · simp [killX, h, Function.update]

theorem killX_add_smul (v α : V) (hα : α 0 = 0) (k : ℤ) :
    killX (v + k • α) = killX v + k • α := by
  ext i
  by_cases h : i = 0
  · subst h; simp [killX, hα]
  · simp [killX, h, Function.update]

theorem dotZ_killX (v w : V) : dotZ (killX v) w = dotZ v w := by
  simp [dotZ, killX, Function.update, Fin.succ_ne_zero]

theorem ctFun_piStr (θf : ℤ → Kq) (α v : V) (hα : α 0 = 0) :
    ctFun θf (piStr α v) = θf (-(v 0)) • piStr α (killX v) := by
  unfold piStr
  rw [dotZ_killX]
  split_ifs
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ctFun_mon, killX_sub_smul v α hα, smul_mon, mul_one, one_mul]
    simp [hα]
  · rw [map_neg, map_sum, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ctFun_mon, killX_add_smul v α hα, smul_mon, mul_one, one_mul]
    simp [hα]

theorem ctFun_pi0Str (θf : ℤ → Kq) (v : V) :
    ctFun θf (pi0Str v) = θf (-(v 0)) • pi0Str (killX v) := by
  have hθ : thetaV 0 = 0 := by decide
  unfold pi0Str
  rw [dotZ_killX]
  split_ifs
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ctFun_mon, killX_add_smul v thetaV hθ, smul_mon]
    simp [hθ, mul_comm]
  · rw [map_neg, map_sum, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ctFun_mon, killX_sub_smul v thetaV hθ, smul_mon]
    simp [hθ, mul_comm]

theorem ctFun_piR (θf : ℤ → Kq) (α : V) (hα : α 0 = 0) :
    ctFun θf ∘ₗ piR α = piR α ∘ₗ ctFun θf := by
  apply Finsupp.lhom_ext
  intro v c
  change ctFun θf (piR α (mon v c)) = piR α (ctFun θf (mon v c))
  rw [piR_mon, map_smul, ctFun_piStr θf α v hα, ctFun_mon, piR_mon, smul_smul]

theorem ctFun_pi0R (θf : ℤ → Kq) : ctFun θf ∘ₗ pi0R = pi0R ∘ₗ ctFun θf := by
  apply Finsupp.lhom_ext
  intro v c
  change ctFun θf (pi0R (mon v c)) = pi0R (ctFun θf (mon v c))
  rw [pi0R_mon, map_smul, ctFun_pi0Str θf v, ctFun_mon, pi0R_mon, smul_smul]

theorem rootV_zero (i : Fin 4) : rootV i 0 = 0 := by fin_cases i <;> decide

/-- **`CT_x` commutes with `B`.** -/
theorem smap_ct_Bop (θf : ℤ → Kq) (F : S) : smap (ctFun θf) (Bop F) = Bop (smap (ctFun θf) F) := by
  unfold Bop piThetaS
  have h0 : smap (ctFun θf) (smap pi0R F) = smap pi0R (smap (ctFun θf) F) := by
    rw [smap_comp, smap_comp, ctFun_pi0R]
  rw [← h0]
  generalize smap pi0R F = G
  generalize wordS = w
  induction w generalizing G with
  | nil => rfl
  | cons i w ih =>
      simp only [List.foldl_cons]
      rw [ih, smap_comp, smap_comp, ctFun_piR θf _ (rootV_zero i)]

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.smap_ct_Bop
end AxiomAudit
