/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelBox

/-!
# Serre–Stark S4-5: the Fricke involution on θ-type forms

First building block of the level analysis (`SerreStarkLevelBox24`, route step (a) of the S4 plan):

* `fricke N f τ = f(−1/(Nτ)) θ(Nτ/4) / θ(−1/(Nτ))`, which on `ℍ` equals
  `(−iNτ/2)^{−1/2} f(−1/(Nτ))` (`fricke_eq_cpow`; Serre–Stark's `W(N)` up to the constant
  `(N/4)^{1/4}`);
* `mobius_frickeConj`: `W γ W⁻¹ ∈ Γ₁(N)` for `γ ∈ Γ₁(N)` (`W = (0 −1; N 0)`);
* `isThetaTypeForm_fricke`: for `24 ∣ N`, `W` maps θ-type forms of level `N` to θ-type forms of
  level `N` (multiplier law via `θ(N·/4) = θ_{0,1,N/4}` being θ-type of level `N`; holomorphy via
  the zero-freeness of `θ`; cusp bounds via column reduction and `cusp_bound_of_le`).
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-- The Fricke transform `f ↦ f(−1/(Nτ)) θ(Nτ/4)/θ(−1/(Nτ))`. -/
def fricke (N : ℕ) (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  f (-1 / (N * τ)) * thetaRef (N * τ / 4) / thetaRef (-1 / (N * τ))

theorem im_neg_inv_pos {N : ℕ} (hN : 0 < N) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (-1 / ((N : ℂ) * τ)).im := by
  have hNτ : 0 < ((N : ℂ) * τ).im := by
    have e : ((N : ℂ) * τ).im = N * τ.im := by simp
    rw [e]; exact mul_pos (Nat.cast_pos.2 hN) hτ
  have hne : (N : ℂ) * τ ≠ 0 := fun h => by rw [h] at hNτ; simp at hNτ
  rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hNτ (Complex.normSq_pos.2 hne)

theorem im_mul_div_four_pos {N : ℕ} (hN : 0 < N) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < ((N : ℂ) * τ / 4).im := by
  have e : ((N : ℂ) * τ / 4).im = N * τ.im / 4 := by simp
  rw [e]
  have : (0 : ℝ) < N := Nat.cast_pos.2 hN
  positivity

/-- `θ(tτ) = θ_{0,1,t}(τ)`. -/
theorem thetaRef_mul (t : ℝ) (τ : ℂ) : thetaRef (t * τ) = rankOneTheta 0 1 t τ := by
  rw [thetaRef, rankOneTheta, rankOneTheta]
  refine tsum_congr fun m => ?_
  simp only [rankOneThetaTerm]
  congr 1
  push_cast
  ring

/-- `θ(−1/(Nτ)) = (−iNτ/2)^{1/2} θ(Nτ/4)`. -/
theorem thetaRef_neg_inv {N : ℕ} (hN : 0 < N) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef (-1 / (N * τ)) = (-I * (N * τ / 2)) ^ (1 / 2 : ℂ) * thetaRef (N * τ / 4) := by
  have hNτ : 0 < ((N : ℂ) * τ).im := by
    have e : ((N : ℂ) * τ).im = N * τ.im := by simp
    rw [e]; exact mul_pos (Nat.cast_pos.2 hN) hτ
  have h := rankOneTheta_zero_one_S (t := 1) one_pos hNτ
  have e1 : thetaRef (-1 / (N * τ)) = rankOneTheta 0 1 1 (-1 / (N * τ)) := rfl
  have e2 : thetaRef (N * τ / 4) = rankOneTheta 0 1 (1 / (4 * 1)) (N * τ) := by
    rw [← thetaRef_mul]; congr 1; push_cast; ring
  rw [e1, h, e2]
  congr 2
  push_cast; ring

theorem fricke_eq_cpow {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    fricke N f τ = f (-1 / (N * τ)) / (-I * (N * τ / 2)) ^ (1 / 2 : ℂ) := by
  have hθ : thetaRef (N * τ / 4) ≠ 0 := thetaRef_ne_zero_of_im_pos (im_mul_div_four_pos hN hτ)
  rw [fricke, thetaRef_neg_inv hN hτ]
  field_simp

/-- The conjugate `W γ W⁻¹ = (d, −c/N; −N b, a)` of `γ ∈ Γ₁(N)`. -/
def frickeConj {N : ℕ} (γ : SL(2, ℤ)) (c' : ℤ) (hc : γ 1 0 = N * c') : SL(2, ℤ) :=
  ⟨!![γ 1 1, -c'; -(N * γ 0 1), γ 0 0], by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this; exact this
    rw [Matrix.det_fin_two_of]
    rw [hc] at hdet
    linear_combination hdet⟩

theorem frickeConj_mem {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) (c' : ℤ)
    (hc : γ 1 0 = N * c') : frickeConj γ c' hc ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa [frickeConj] using hγ.2.1
  · simpa [frickeConj] using hγ.1
  · simp [frickeConj]

theorem mobius_frickeConj {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) (c' : ℤ) (hc : γ 1 0 = N * c')
    {τ : ℂ} (hτ : 0 < τ.im) :
    -1 / ((N : ℂ) * mobius γ τ) = mobius (frickeConj γ c' hc) (-1 / (N * τ)) := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hden : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := denom_ne_zero γ hτ
  -- `a τ + b ≠ 0` (the top row of `γ` is nonzero)
  have hnum : (γ 0 0 : ℂ) * τ + γ 0 1 ≠ 0 := by
    intro h
    have him : ((γ 0 0 : ℂ) * τ + γ 0 1).im = (γ 0 0 : ℝ) * τ.im := by simp
    rw [h, Complex.zero_im] at him
    have ha : (γ 0 0 : ℝ) = 0 := by
      rcases mul_eq_zero.1 him.symm with h' | h'
      · exact h'
      · exact absurd h' hτ.ne'
    have ha' : γ 0 0 = 0 := by exact_mod_cast ha
    have hb : (γ 0 1 : ℂ) = 0 := by rw [ha'] at h; simpa using h
    have hb' : γ 0 1 = 0 := by exact_mod_cast hb
    have hdet := γ.2
    rw [Matrix.det_fin_two, ha', hb'] at hdet
    simp at hdet
  have hc' : (γ 1 0 : ℂ) = N * c' := by exact_mod_cast hc
  have hτN : (N : ℂ) * τ ≠ 0 := mul_ne_zero hN0 hτ0
  have e00 : (frickeConj γ c' hc) 0 0 = γ 1 1 := rfl
  have e01 : (frickeConj γ c' hc) 0 1 = -c' := rfl
  have e10 : (frickeConj γ c' hc) 1 0 = -(N * γ 0 1) := rfl
  have e11 : (frickeConj γ c' hc) 1 1 = γ 0 0 := rfl
  have e1 : (γ 1 1 : ℂ) * (-1 / (N * τ)) + ((-c' : ℤ) : ℂ) =
      -((γ 1 0 : ℂ) * τ + γ 1 1) / (N * τ) := by
    rw [hc']; push_cast; field_simp; ring
  have e2 : ((-(N * γ 0 1) : ℤ) : ℂ) * (-1 / (N * τ)) + (γ 0 0 : ℂ) =
      ((γ 0 0 : ℂ) * τ + γ 0 1) / τ := by
    push_cast; field_simp; ring
  rw [mobius, mobius, e00, e01, e10, e11, e1, e2]
  field_simp

/-- `θ(N τ / 4)` satisfies the θ multiplier law of level `N` (`24 ∣ N`). -/
theorem thetaQuarter_law {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef (N * mobius γ τ / 4) * thetaRef τ = thetaRef (mobius γ τ) * thetaRef (N * τ / 4) := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  obtain ⟨k, hk⟩ := h4
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; omega
    · exact h
  have hθ := isThetaTypeForm_rankOneTheta h24 0 (r := 1) (t := k) one_pos hk0
    (by rw [hk]; ring_nf; exact dvd_refl _)
  have e : ∀ z : ℂ, thetaRef ((N : ℂ) * z / 4) = rankOneTheta 0 1 (k : ℝ) z := by
    intro z
    rw [← thetaRef_mul]; congr 1; rw [hk]; push_cast; ring
  rw [e, e]
  exact hθ.multiplier γ hγ τ hτ

/-- **The Fricke involution preserves θ-type forms of level `N`** (`24 ∣ N`). -/
theorem isThetaTypeForm_fricke {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) : IsThetaTypeForm N (fricke N f) := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · -- holomorphy
    have hW : DifferentiableOn ℂ (fun τ : ℂ => -1 / ((N : ℂ) * τ)) upperSet := by
      intro τ hτ
      have hτ0 : (N : ℂ) * τ ≠ 0 := mul_ne_zero hN0 (fun h => by
        have : (0 : ℝ) < τ.im := hτ; rw [h] at this; simp at this)
      exact ((differentiableAt_const _).div (differentiableAt_const _ |>.mul differentiableAt_id)
        hτ0).differentiableWithinAt
    have hWmaps : Set.MapsTo (fun τ : ℂ => -1 / ((N : ℂ) * τ)) upperSet upperSet :=
      fun τ hτ => im_neg_inv_pos hN hτ
    have hQ : DifferentiableOn ℂ (fun τ : ℂ => (N : ℂ) * τ / 4) upperSet :=
      ((differentiable_const _).mul differentiable_id |>.div_const _).differentiableOn
    have hQmaps : Set.MapsTo (fun τ : ℂ => (N : ℂ) * τ / 4) upperSet upperSet :=
      fun τ hτ => im_mul_div_four_pos hN hτ
    refine ((hf.holo.comp hW hWmaps).mul (differentiableOn_thetaRef.comp hQ hQmaps)).div
      (differentiableOn_thetaRef.comp hW hWmaps) fun τ hτ =>
        thetaRef_ne_zero_of_im_pos (im_neg_inv_pos hN hτ)
  · -- the multiplier law
    intro γ hγ τ hτ
    have hc : (N : ℤ) ∣ γ 1 0 := by
      have := ((CongruenceSubgroup.Gamma1_mem N γ).1 hγ).2.2
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    obtain ⟨c', hc'⟩ := hc
    set γ' := frickeConj γ c' hc'
    have hγ' : γ' ∈ CongruenceSubgroup.Gamma1 N := frickeConj_mem hγ c' hc'
    have hgτ : 0 < (mobius γ τ).im := im_mobius_pos γ hτ
    set w := -1 / ((N : ℂ) * τ) with hw
    have hwpos : 0 < w.im := im_neg_inv_pos hN hτ
    have hconj : -1 / ((N : ℂ) * mobius γ τ) = mobius γ' w := mobius_frickeConj hN γ c' hc' hτ
    have hlaw := hf.multiplier γ' hγ' w hwpos
    have hq := thetaQuarter_law hN h24 hγ hτ
    have hθw : thetaRef w ≠ 0 := thetaRef_ne_zero_of_im_pos hwpos
    have hθγ'w : thetaRef (mobius γ' w) ≠ 0 :=
      thetaRef_ne_zero_of_im_pos (im_mobius_pos γ' hwpos)
    simp only [fricke]
    rw [hconj, ← hw]
    field_simp
    linear_combination (thetaRef (N * mobius γ τ / 4) * thetaRef τ) * hlaw +
      (f w * thetaRef (mobius γ' w)) * hq
  · -- cusp bounds
    intro δ₀
    set a := δ₀ 0 0
    set b := δ₀ 0 1
    set c := δ₀ 1 0
    set d := δ₀ 1 1
    have hdet₀ : a * d - b * c = 1 := by
      have := δ₀.2; rw [Matrix.det_fin_two] at this; exact this
    set X : Matrix (Fin 2) (Fin 2) ℤ := !![-c, -d; (N : ℤ) * a, (N : ℤ) * b] with hX
    have hXdet : X.det = N := by
      rw [hX, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * hdet₀
    obtain ⟨δ, U, hXU, hU10, hU00, hU11, hUdet⟩ :=
      exists_SL_mul_upper X (by rw [hXdet]; exact_mod_cast hN)
    have hεpos : (0 : ℝ) < 1 / N := by positivity
    obtain ⟨C, hC⟩ := IsThetaTypeForm.cusp_bound_of_le h4 hN hf δ hεpos
    refine ⟨max C 0 * Real.sqrt 2, fun τ hτ1 => ?_⟩
    have hτ : 0 < τ.im := by linarith
    set σ := mobius δ₀ τ with hσ
    have hσpos : 0 < σ.im := im_mobius_pos δ₀ hτ
    have hden : (c : ℂ) * τ + d ≠ 0 := denom_ne_zero δ₀ hτ
    have hnum : (a : ℂ) * τ + b ≠ 0 := by
      intro h
      have him : ((a : ℂ) * τ + b).im = (a : ℝ) * τ.im := by simp
      rw [h, Complex.zero_im] at him
      have ha : (a : ℝ) = 0 := by
        rcases mul_eq_zero.1 him.symm with h' | h'
        · exact h'
        · exact absurd h' hτ.ne'
      have ha' : a = 0 := by exact_mod_cast ha
      have hb : (b : ℂ) = 0 := by rw [ha'] at h; simpa using h
      have hb' : b = 0 := by exact_mod_cast hb
      rw [ha', hb'] at hdet₀; simp at hdet₀
    -- `−1/(Nσ) = X τ = δ (U τ)`
    have hU11ne : (U 1 1 : ℂ) ≠ 0 := by exact_mod_cast hU11.ne'
    have hdenU : denZ U τ ≠ 0 := by
      simp only [denZ, hU10]; push_cast; simpa using hU11ne
    set w := mobZ U τ with hwdef
    have hwval : w = ((U 0 0 : ℂ) * τ + U 0 1) / U 1 1 := by
      rw [hwdef, mobZ, hU10]; push_cast; ring
    have hwim : 1 / (N : ℝ) ≤ w.im := by
      rw [hwval]
      have e : (((U 0 0 : ℂ) * τ + U 0 1) / U 1 1).im = (U 0 0 : ℝ) * τ.im / U 1 1 := by
        rw [div_eq_mul_inv, ← Complex.ofReal_intCast (U 1 1)]
        simp [Complex.mul_im]
        field_simp
      rw [e]
      have hu0 : (1 : ℝ) ≤ U 0 0 := by exact_mod_cast hU00
      have hu1 : (U 1 1 : ℝ) ≤ N := by
        have : U 1 1 ≤ U 0 0 * U 1 1 := le_mul_of_one_le_left hU11.le hU00
        rw [hUdet, hXdet] at this; exact_mod_cast this
      have hu1p : (0 : ℝ) < U 1 1 := by exact_mod_cast hU11
      have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
      rw [div_le_div_iff₀ hNr hu1p]
      have h1 : (1 : ℝ) ≤ U 0 0 * τ.im := by nlinarith
      have h2 : (N : ℝ) ≤ U 0 0 * τ.im * N := by nlinarith
      linarith
    have hXτ : -1 / ((N : ℂ) * σ) = mobius δ w := by
      rw [← mobZ_SL, hwdef, ← mobZ_mul _ _ hdenU, ← hXU, hσ]
      simp only [mobius, mobZ, hX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      push_cast
      field_simp
      ring
    have hdenX : (δ 1 0 : ℂ) * w + δ 1 1 = N * ((a : ℂ) * τ + b) / U 1 1 := by
      have h1 := denZ_mul (δ : Matrix (Fin 2) (Fin 2) ℤ) U hdenU
      rw [← hXU] at h1
      have h2 : denZ X τ = N * ((a : ℂ) * τ + b) := by
        simp only [denZ, hX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
        push_cast; ring
      have h3 : denZ U τ = U 1 1 := by simp [denZ, hU10]
      rw [h2, h3] at h1
      have : denZ (δ : Matrix (Fin 2) (Fin 2) ℤ) w = (δ 1 0 : ℂ) * w + δ 1 1 := rfl
      rw [← this, eq_div_iff hU11ne, h1]
    have hb := hC w hwim
    rw [← hXτ, hdenX] at hb
    -- the norm of the Fricke factor
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [fricke_eq_cpow hN f hσpos, norm_div, hhalf, norm_cpow_real]
    -- assemble
    have hσval : σ = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d) := rfl
    set A := ‖(a : ℂ) * τ + b‖ with hA
    set D := ‖(c : ℂ) * τ + d‖ with hD
    have hApos : 0 < A := norm_pos_iff.2 hnum
    have hDpos : 0 < D := norm_pos_iff.2 hden
    have hfac : ‖-I * ((N : ℂ) * σ / 2)‖ = N * A / (2 * D) := by
      rw [hσval, norm_mul, norm_neg, norm_I, one_mul, norm_div, norm_mul, norm_div,
        Complex.norm_natCast, Complex.norm_ofNat]
      ring
    have hbnd : ‖N * ((a : ℂ) * τ + b) / U 1 1‖ ≤ N * A := by
      rw [norm_div, norm_mul, Complex.norm_natCast, ← hA]
      have hu1 : (1 : ℝ) ≤ ‖(U 1 1 : ℂ)‖ := by
        rw [Complex.norm_intCast]
        have : (1 : ℝ) ≤ (U 1 1 : ℝ) := by exact_mod_cast hU11
        rw [abs_of_pos (by linarith)]; exact this
      exact div_le_self (by positivity) hu1
    rw [hfac]
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have hpos : 0 < (N * A / (2 * D)) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    rw [div_le_iff₀ hpos]
    calc ‖f (-1 / ((N : ℂ) * σ))‖
        ≤ C * ‖N * ((a : ℂ) * τ + b) / U 1 1‖ ^ (1 / 2 : ℝ) := hb
      _ ≤ max C 0 * (N * A) ^ (1 / 2 : ℝ) := by
          refine mul_le_mul (le_max_left _ _) ?_ (by positivity) (le_max_right _ _)
          exact Real.rpow_le_rpow (norm_nonneg _) hbnd (by norm_num)
      _ = max C 0 * Real.sqrt 2 * D ^ (1 / 2 : ℝ) * (N * A / (2 * D)) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, mul_assoc (max C 0), mul_assoc (max C 0)]
          congr 1
          rw [← Real.mul_rpow (by norm_num) hDpos.le, ← Real.mul_rpow (by positivity)
            (by positivity)]
          congr 1
          field_simp

/-! ## `W² = (4/N)^{1/2}` -/

theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  have hrz : (r : ℂ) * z ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hr.ne') hz
  rw [cpow_def_of_ne_zero hrz, cpow_def_of_ne_zero (ofReal_ne_zero.2 hr.ne'),
    cpow_def_of_ne_zero hz, log_ofReal_mul hr hz, ← Complex.exp_add, ofReal_log hr.le]
  ring_nf

/-- **`W` is an involution up to the constant `(4/N)^{1/2}`.** -/
theorem fricke_fricke {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    fricke N (fricke N f) τ = ((4 / N : ℝ) : ℂ) ^ (1 / 2 : ℂ) * f τ := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w := -1 / ((N : ℂ) * τ) with hw
  have hwpos : 0 < w.im := im_neg_inv_pos hN hτ
  have hww : -1 / ((N : ℂ) * w) = τ := by rw [hw]; field_simp
  have hNw : (N : ℂ) * w / 4 = -1 / ((4 : ℕ) * τ) := by rw [hw]; push_cast; field_simp
  have h4τ : ((4 : ℕ) : ℂ) * τ / 4 = τ := by push_cast; ring
  have hθ4 := thetaRef_neg_inv (N := 4) (by norm_num) hτ
  rw [h4τ] at hθ4
  have hθN := thetaRef_neg_inv hN hτ
  rw [← hw] at hθN
  have hθτ : thetaRef τ ≠ 0 := thetaRef_ne_zero_of_im_pos hτ
  have hθq : thetaRef ((N : ℂ) * τ / 4) ≠ 0 :=
    thetaRef_ne_zero_of_im_pos (im_mul_div_four_pos hN hτ)
  have hz : -I * ((N : ℂ) * τ / 2) ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.2 I_ne_zero) (div_ne_zero (mul_ne_zero hN0 hτ0) two_ne_zero)
  have hsplit : -I * (((4 : ℕ) : ℂ) * τ / 2) = ((4 / N : ℝ) : ℂ) * (-I * ((N : ℂ) * τ / 2)) := by
    push_cast; field_simp
  have hcp : (-I * (((4 : ℕ) : ℂ) * τ / 2)) ^ (1 / 2 : ℂ) =
      ((4 / N : ℝ) : ℂ) ^ (1 / 2 : ℂ) * (-I * ((N : ℂ) * τ / 2)) ^ (1 / 2 : ℂ) := by
    rw [hsplit, ofReal_mul_cpow (by positivity) hz]
  have hcz : (-I * ((N : ℂ) * τ / 2)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; tauto
  simp only [fricke]
  rw [← hw, hww, hNw, hθ4, hθN, hcp]
  field_simp
  have hcz' : (-(I * (N : ℂ) * τ / 2)) ^ (1 / 2 : ℂ) ≠ 0 := by convert hcz using 2; ring
  rw [mul_div_assoc, div_self hcz', mul_one]

end SSHecke

end VOA.Classification.COne
