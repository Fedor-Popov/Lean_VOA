/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTopSource

/-!
# Top-level zero modes on `T⁺`: the twisted side of (R-top)

The weight-2 letters of `V₀⁺` act on the top level `(T⁺)₂ = h(−½) ⊗ T` of the Leech twisted
module by explicit finite formulas.  This file derives them from the library's twisted module
(`latticeTwistedModule`, its twisted Jacobi identity and the twisted vertex operator `YTL`), first
for a general even unimodular lattice and then, by transport along `rank Λ = 24`, for
`leechTwistedModule`.

## Main results (general lattice `L`)
* `YML_quadSt` — `o(h_a(−1)h_b(−1)𝟙)(h_c(−½) ⊗ t) = (δ_ab/8) h_c ⊗ t + ½δ_bc h_a ⊗ t + ½δ_ac h_b ⊗ t`,
  from the twisted Jacobi identity at `ℓ = −1`, `k = m = 1`; the `δ_ab/8` is
  `−C(½,2) = 1/8`, the vacuum term.
* `YML_echg_X` — for `|α|² = 4`: `o(e^α)(h_c ⊗ t) = 2⁻⁴ (h_c − 2α_c α(−½)) ⊗ e_α t`
  (the degree-0 coefficient `DD_zero_X` of `E⁻E⁺`).
* `YML_echg_neg_two` — `o(e^{−α}) = o(e^α)` on `(T⁺)` (even modes).
* `cast_YM_*`, `leechYM_quad`, `leechYM_echg_X`, `leechYM_echg_neg_two` — the Leech versions.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Unconditional.  
Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.IntegralLattice
open VOA.LatGen HeisenbergN MvPolynomial TwistedHeisenberg
open VOA.Moonshine.LatticeTwisted VOA.Moonshine.Extraspecial
open Module (End)
open Submodule
open scoped TensorProduct

section General

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

theorem thetaAut_hgen (a : Fin (rank L)) : thetaAut L hEven hPos (hgen L a) = -hgen L a := by
  change thetaLat L ((X (0, a) : FockN (rank L)) ⊗ₜ[ℂ] eGen L 0) = -((X (0, a) : FockN (rank L)) ⊗ₜ[ℂ] eGen L 0)
  rw [thetaLat_tmul, sigmaN_X, neg_zero, TensorProduct.neg_tmul]

theorem modeT_one_X (a c : Fin (rank L)) :
    modeT (rank L) a 1 (X (0, c)) = if a = c then (1 / 2 : ℂ) • (1 : FockT (rank L)) else 0 := by
  have h := modeT_annihilation (rank L) a 0 (X (0, c))
  rw [show (2 * ((0 : ℕ) : ℤ) + 1) = 1 by norm_num] at h
  rw [h, pderiv_X]
  by_cases hac : a = c
  · subst hac; simp
  · rw [if_neg hac, Pi.single_apply, if_neg (by intro h; exact hac (Prod.ext_iff.mp h).2.symm)]
    simp

theorem modeT_pos_X {k : ℤ} (hk : Odd k) (hk3 : 3 ≤ k) (a c : Fin (rank L)) :
    modeT (rank L) a k (X (0, c)) = 0 := by
  rw [modeT_apply_pos _ _ hk (by omega), pderiv_X, Pi.single_apply, if_neg]
  · simp
  · intro h
    have := (Prod.ext_iff.mp h).1
    simp only [varT] at this
    rw [abs_of_pos (by omega : (0 : ℤ) < k)] at this
    omega

theorem modeT_neg_one (a : Fin (rank L)) (p : FockT (rank L)) :
    modeT (rank L) a (-1) p = X (0, a) * p := by
  have h := modeT_creation (rank L) a 0 p
  rwa [show (-(2 * ((0 : ℕ) : ℤ) + 1)) = -1 by norm_num] at h

theorem cbinom_half_two : cbinom ((1 : ℂ) / 2) 2 = -1 / 8 := by
  simp [cbinom, Finset.prod_range_succ]
  norm_num

/-- **The twisted zero mode of `h_a(−1)h_b(−1)𝟙` on `h_c(−½) ⊗ t`**:
`o(h_a h_b)(h_c ⊗ t) = (δ_ab/8) h_c ⊗ t + ½δ_bc h_a ⊗ t + ½δ_ac h_b ⊗ t`. -/
theorem YML_quadSt (a b c : Fin (rank L)) (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    YML L hEven hU (quadSt L hEven hPos a b) 2 ((X (0, c) : FockT (rank L)) ⊗ₜ t)
      = ((if a = b then (1 / 8 : ℂ) else 0) • (X (0, c) : FockT (rank L))
          + (if b = c then (1 / 2 : ℂ) else 0) • X (0, a)
          + (if a = c then (1 / 2 : ℂ) else 0) • X (0, b)) ⊗ₜ t := by
  have hmem : hgen L a ∈ (thetaAut L hEven hPos).twistedEigenspace 2 1 :=
    TwistedCyclic.mem_twistedEigenspace_one (thetaAut_hgen L hEven hPos a)
  have J := (latticeTwistedModule L hEven hU hPos).jacobi 1 (hgen L a) hmem (hgen L b)
    ((X (0, c) : FockT (rank L)) ⊗ₜ t) (-1) 1 1 (by norm_num)
  simp only [latticeTwistedModule_YM] at J
  have hT : ∀ (d : Fin (rank L)) (k : ℤ) (y : FockT (rank L)),
      YML L hEven hU (hgen L d) k (y ⊗ₜ t) = modeT (rank L) d k y ⊗ₜ t := by
    intro d k y
    rw [InvForm.YML_hgen L hEven hU hPos]; rfl
  have hHH : ∀ i : ℕ, 3 ≤ i → (latticeVOAGen L hEven hPos).smul (hgen L a) (-1 + (i : ℤ)) (hgen L b) = 0 := by
    intro i hi
    rw [smul_hgen_hgen_nonneg L hEven hPos a b (by omega), if_neg (by omega)]
  rw [finsum_eq_single _ (0 : ℤ) (by
      intro i hi
      rcases lt_or_gt_of_ne hi with hneg | hpos
      · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
      · have h0 : ∀ d : Fin (rank L), YML L hEven hU (hgen L d) (1 + i * ((2 : ℕ) : ℤ))
            ((X (0, c) : FockT (rank L)) ⊗ₜ t) = 0 := by
          intro d
          rw [hT, modeT_pos_X L ⟨i, by push_cast; ring⟩ (by push_cast; omega), TensorProduct.zero_tmul]
        rw [h0, h0, map_zero, map_zero, smul_zero, sub_zero, smul_zero])] at J
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 3) _ (by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hi
      rw [hHH i (by omega), map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero])] at J
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at J
  have e1 : (-1 * ((2 : ℕ) : ℤ) + 1 - 0 * ((2 : ℕ) : ℤ)) = -1 := by norm_num
  have e2 : (1 + 0 * ((2 : ℕ) : ℤ)) = 1 := by norm_num
  have e3 : (1 + 1 - ((0 : ℕ) : ℤ) * ((2 : ℕ) : ℤ)) = 2 := by norm_num
  have e4 : (-1 + ((0 : ℕ) : ℤ)) = -1 := by norm_num
  have e5 : (-1 + ((1 : ℕ) : ℤ)) = 0 := by norm_num
  have e6 : (-1 + ((2 : ℕ) : ℤ)) = 1 := by norm_num
  have e7 : (1 + 1 - ((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ)) = -2 := by norm_num
  rw [e1, e2, e3, e4, e5, e6, e7] at J
  have v1 : ∀ d : Fin (rank L), YML L hEven hU (hgen L d) 1 ((X (0, c) : FockT (rank L)) ⊗ₜ t)
      = (if d = c then (1 / 2 : ℂ) • (1 : FockT (rank L)) else 0) ⊗ₜ t := by
    intro d; rw [hT, modeT_one_X]
  have v2 : ∀ (d : Fin (rank L)) (y : FockT (rank L)), YML L hEven hU (hgen L d) (-1) (y ⊗ₜ t)
      = (X (0, d) * y) ⊗ₜ t := by
    intro d y; rw [hT, modeT_neg_one]
  have v3 : (latticeVOAGen L hEven hPos).smul (hgen L a) 0 (hgen L b) = 0 := by
    rw [smul_hgen_hgen_nonneg L hEven hPos a b le_rfl, if_neg (by omega)]
  have v4 : (latticeVOAGen L hEven hPos).smul (hgen L a) 1 (hgen L b)
      = if a = b then latVacuumGen L else 0 := by
    rw [smul_hgen_hgen_nonneg L hEven hPos a b zero_le_one]
    simp
  rw [v1, v1, v2, v2, v3, v4, map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero, add_zero,
    cbinom_zero, one_smul, negOnePow, negOnePow, cbz_zero, if_pos (show _root_.Even (0 : ℤ) by decide),
    if_neg (show ¬ _root_.Even (-1 : ℤ) by decide)] at J
  simp only [Int.cast_one, Nat.cast_ofNat] at J
  rw [cbinom_half_two] at J
  have hvac : YML L hEven hU (latVacuumGen L) (-2) = 1 := by rw [YML_vacuum, if_pos rfl]
  have J' : YML L hEven hU (quadSt L hEven hPos a b) 2 ((X (0, c) : FockT (rank L)) ⊗ₜ t)
      = ((X (0, a) * if b = c then (1 / 2 : ℂ) • (1 : FockT (rank L)) else 0) ⊗ₜ[ℂ] t
          + (X (0, b) * if a = c then (1 / 2 : ℂ) • (1 : FockT (rank L)) else 0) ⊗ₜ[ℂ] t)
        + (1 / 8 : ℂ) • (YML L hEven hU (if a = b then latVacuumGen L else 0) (-2))
          ((X (0, c) : FockT (rank L)) ⊗ₜ t) := by
    rw [quadSt]
    rw [← sub_eq_iff_eq_add] at J
    rw [← J]
    simp only [one_mul, neg_smul, one_smul, sub_neg_eq_add]
    module
  rw [J']
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, hvac, Module.End.one_apply]
    subst hab
    by_cases hac : a = c
    · subst hac
      simp only [if_true, mul_smul_comm, mul_one, TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
      module
    · simp only [if_neg hac, mul_zero, TensorProduct.zero_tmul, zero_add,
        add_zero, ← TensorProduct.smul_tmul', zero_smul]
  · rw [if_neg hab, if_neg hab, map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero, add_zero]
    by_cases hbc : b = c <;> by_cases hac : a = c
    · exact absurd (hac.trans hbc.symm) hab
    · subst hbc
      simp only [if_true, if_neg hac, mul_smul_comm, mul_one, mul_zero, TensorProduct.zero_tmul,
        add_zero, zero_smul, ← TensorProduct.smul_tmul', zero_add]
    · subst hac
      simp only [if_true, if_neg hbc, mul_smul_comm, mul_one, mul_zero, TensorProduct.zero_tmul,
        add_zero, zero_smul, ← TensorProduct.smul_tmul', zero_add]
    · simp only [if_neg hbc, if_neg hac, mul_zero, TensorProduct.zero_tmul, add_zero, zero_smul]

theorem sM_one' {r : ℕ} (v : Fin r → ℂ) : sM v 1 = (2 : ℂ) • vVarT v 0 := by
  rw [sM, nexp_succ]
  simp [dM]

/-- `E⁻E⁺(−v)` at degree `0` on `h_c(−½)`: `h_c − 2 v_c v(−½)`. -/
theorem DD_zero_X {r : ℕ} (v : Fin r → ℂ) (c : Fin r) :
    DD v 0 (X (0, c)) = X (0, c) - (2 * v c) • vVarT v 0 := by
  have h := DD_X_mul v (0, c) 0 (1 : FockT r)
  rw [mul_one] at h
  rw [h, InvForm.DD_one, InvForm.DD_one]
  simp only [zero_add, Nat.cast_zero]
  rw [show sMz v 0 = 1 by simp [sMz], show ((2 : ℤ) * 0 + 1) = ((1 : ℕ) : ℤ) by norm_num,
    sMz_natCast, sM_one', mul_one, smul_smul, mul_comm (2 : ℂ)]

include hPos in
/-- **The twisted zero mode of `e^α` (`|α|² = 4`) on `h_c(−½) ⊗ t`**:
`o(e^α)(h_c ⊗ t) = 2⁻⁴ (h_c − 2α_c α(−½)) ⊗ e_α t`. -/
theorem YML_echg_X (α : L.carrier) (hα : L.form α α = 4) (c : Fin (rank L))
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    YML L hEven hU (echg L α) 2 ((X (0, c) : FockT (rank L)) ⊗ₜ t)
      = (2 : ℂ) ^ (-(4 : ℤ)) • ((X (0, c) - (2 * chargeCoord L α c) • vVarT (chargeCoord L α) 0)
          ⊗ₜ eT L hEven hU α t) := by
  rw [InvForm.YML_echg L hEven hU hPos, YTL, YTg_tmul, hα,
    show (-2 - 2 + 4 : ℤ) = 0 by norm_num, DD_zero_X]

include hPos in
/-- On even modes `e^{−α}` acts like `e^α`: `Y^T(e^{−α})₍k/2₎ = (−1)^k Y^T(e^α)₍k/2₎`. -/
theorem YML_echg_neg_two (α : L.carrier) :
    YML L hEven hU (echg L (-α)) 2 = YML L hEven hU (echg L α) 2 := by
  rw [InvForm.YML_echg L hEven hU hPos, InvForm.YML_echg L hEven hU hPos, YTL_neg]
  norm_num

theorem cast_YM_quadSt {r : ℕ} (h : rank L = r) (a b : Fin (rank L)) (c : Fin r)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM
        (quadSt L hEven hPos a b) 2 ((X (0, c) : FockT r) ⊗ₜ t)
      = ((if a = b then (1 / 8 : ℂ) else 0) • (X (0, c) : FockT r)
          + (if Fin.cast h b = c then (1 / 2 : ℂ) else 0) • X (0, Fin.cast h a)
          + (if Fin.cast h a = c then (1 / 2 : ℂ) else 0) • X (0, Fin.cast h b)) ⊗ₜ t := by
  subst h
  simp only [Fin.cast_eq_self]
  exact YML_quadSt L hEven hU hPos a b c t

theorem cast_YM_echg_X {r : ℕ} (h : rank L = r) (α : L.carrier) (hα : L.form α α = 4) (c : Fin r)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM
        (echg L α) 2 ((X (0, c) : FockT r) ⊗ₜ t)
      = (2 : ℂ) ^ (-(4 : ℤ)) • ((X (0, c) - (2 * chargeCoord L α (Fin.cast h.symm c)) •
          vVarT (fun i => chargeCoord L α (Fin.cast h.symm i)) 0) ⊗ₜ eT L hEven hU α t) := by
  subst h
  simp only [Fin.cast_eq_self]
  exact YML_echg_X L hEven hU hPos α hα c t

theorem cast_YM_echg_neg_two {r : ℕ} (h : rank L = r) (α : L.carrier) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (echg L (-α)) 2
      = (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (echg L α) 2 := by
  subst h
  exact YML_echg_neg_two L hEven hU hPos α

end General

/-! ## The Leech twisted module -/

/-- `X_{(0,c)}` read in the Leech Fock space, `c : Fin (rank Λ)`. -/
noncomputable abbrev cc (a : Fin (rank leech)) : Fin 24 := Fin.cast leech_rank a

theorem leechYM_quad (a b : Fin (rank leech)) (c : Fin 24) (t : TLeechT) :
    leechTwistedModule.YM (qL a b) 2 ((X (0, c) : FockT 24) ⊗ₜ t)
      = ((if a = b then (1 / 8 : ℂ) else 0) • (X (0, c) : FockT 24)
          + (if cc b = c then (1 / 2 : ℂ) else 0) • X (0, cc a)
          + (if cc a = c then (1 / 2 : ℂ) else 0) • X (0, cc b)) ⊗ₜ t :=
  cast_YM_quadSt leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank a b c t

/-- The charge coordinates of `α ∈ Λ` in the twisted Fock space `S[θ]` (`Fin 24`). -/
noncomputable def chT (α : leech.carrier) : Fin 24 → ℂ := fun i => chargeCoord leech α (Fin.cast leech_rank.symm i)

theorem leechYM_echg_X (α : leech.carrier) (hα : leech.form α α = 4) (c : Fin 24) (t : TLeechT) :
    leechTwistedModule.YM (echg leech α) 2 ((X (0, c) : FockT 24) ⊗ₜ t)
      = (2 : ℂ) ^ (-(4 : ℤ)) • ((X (0, c) - (2 * chT α c) • vVarT (chT α) 0)
          ⊗ₜ eT leech leech_even leech_isUnit_det_gramMat α t) :=
  cast_YM_echg_X leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank α hα c t

theorem leechYM_echg_neg_two (α : leech.carrier) :
    leechTwistedModule.YM (echg leech (-α)) 2 = leechTwistedModule.YM (echg leech α) 2 :=
  cast_YM_echg_neg_two leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank α

end VOA.Moonshine.SigmaTop
