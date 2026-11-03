/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Inputs
import VOA.Classification.COne.GapsClassical
import VOA.Classification.COne.GapsPaper
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Towards `ISerreStark` (S1)

Staged reduction of the Serre–Stark input `ISerreStark`. Proved here (no project axiom):

* `IsThetaTypeForm.submodule`: θ-type forms of level `N` form a `ℂ`-subspace;
* `IsThetaTypeForm.add_one`, `IsThetaTypeForm.exists_qExpansion`: periodicity on all of `ℍ`
  (identity theorem) and an integral-power `q`-expansion `f = Σ_{n ≥ 0} aₙ qⁿ`;
* `thetaSqLaw_of_mem_Gamma1`: the weight-one law `θ(γτ)² = (cτ + d) θ(τ)²` on `Γ₁(N)`,
  `4 ∣ N` (S-transformation squared for `U_m = (1 0; 4m 1)`, Euclidean descent with balanced
  remainders for `Γ₁(4)`);
* `IsThetaTypeForm.weight_one`: `f θ` is a weight-one form for `Γ₁(N)` with trivial multiplier;
* `iSerreStark_of_theoremA : SerreStarkTheoremA → ISerreStark`: the published character form
  (Serre–Stark Theorem A, basis `θ_{ψ,t}`) implies the residue-class form used by GR.

The remaining residual is `SerreStarkTheoremA`, Serre–Stark's Theorem A verbatim.
-/

open Complex Filter Topology Function
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos ofComplex_apply_of_im_nonpos qExpansion
  IsBoundedAtImInfty isBoundedAtImInfty_iff hasSum_qExpansion)
open scoped Manifold UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

/-! ## 1. The reference theta function -/

/-- `θ(τ) = ϑ(2τ)` with Mathlib's `jacobiTheta τ = Σ_n e^{πi n² τ}`. -/
theorem thetaRef_eq_jacobiTheta (τ : ℂ) : thetaRef τ = jacobiTheta (2 * τ) := by
  rw [thetaRef, rankOneTheta, jacobiTheta]
  refine tsum_congr fun m => ?_
  rw [rankOneThetaTerm]
  congr 1
  push_cast
  ring

theorem exp_neg_pi_lt_third : Real.exp (-Real.pi) < 1 / 3 := by
  have h1 := Real.add_one_le_exp Real.pi
  have h2 := Real.pi_gt_three
  have hpos := Real.exp_pos Real.pi
  rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ hpos (by norm_num)]
  linarith

/-- `‖θ(τ) - 1‖ < 1` for `Im τ ≥ 1/2`. -/
theorem norm_thetaRef_sub_one_lt {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) : ‖thetaRef τ - 1‖ < 1 := by
  have h2 : 0 < (2 * τ).im := by
    simp only [mul_im, re_ofNat, im_ofNat, zero_mul, add_zero]
    linarith
  rw [thetaRef_eq_jacobiTheta]
  refine (norm_jacobiTheta_sub_one_le h2).trans_lt ?_
  set x := Real.exp (-Real.pi * (2 * τ).im) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 / 3 := by
    refine lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) exp_neg_pi_lt_third
    have : (2 * τ).im = 2 * τ.im := by simp
    rw [this]
    nlinarith [Real.pi_pos]
  rw [div_mul_eq_mul_div, div_lt_one (by linarith)]
  linarith

theorem thetaRef_ne_zero {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) : thetaRef τ ≠ 0 := by
  intro h
  have := norm_thetaRef_sub_one_lt hτ
  rw [h, zero_sub, norm_neg, norm_one] at this
  exact lt_irrefl _ this

/-- `θ(τ + 1) = θ(τ)`. -/
theorem thetaRef_add_one (τ : ℂ) : thetaRef (τ + 1) = thetaRef τ := by
  have h := rankOneTheta_T 0 1 1 τ
  simpa [thetaRef] using h

/-! ## 2. θ-type forms: linear structure, periodicity, q-expansion -/

/-- The upper half plane as a subset of `ℂ`. -/
abbrev upperSet : Set ℂ := {z : ℂ | 0 < z.im}

theorem isPreconnected_upperSet : IsPreconnected upperSet :=
  (Complex.isConnected_of_upperHalfPlane (r := 0) subset_rfl
    (fun _ hz => Set.mem_setOf.mpr (le_of_lt hz))).isPreconnected

/-- The translation `T = [[1,1],[0,1]]`. -/
def matT : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem matT_mem_Gamma1 (N : ℕ) : matT ∈ CongruenceSubgroup.Gamma1 N := by
  simp [matT]

theorem mobius_matT (τ : ℂ) : mobius matT τ = τ + 1 := by
  simp [mobius, matT]

namespace IsThetaTypeForm

variable {N : ℕ}

theorem zero : IsThetaTypeForm N (fun _ => 0) where
  holo := differentiableOn_const 0
  multiplier _ _ _ _ := by simp
  cusps _ := ⟨0, fun _ _ => by simp⟩

theorem add {f g : ℂ → ℂ} (hf : IsThetaTypeForm N f) (hg : IsThetaTypeForm N g) :
    IsThetaTypeForm N (f + g) where
  holo := hf.holo.add hg.holo
  multiplier γ hγ τ hτ := by
    simp only [Pi.add_apply, add_mul, mul_add, hf.multiplier γ hγ τ hτ, hg.multiplier γ hγ τ hτ]
  cusps γ := by
    obtain ⟨C, hC⟩ := hf.cusps γ
    obtain ⟨D, hD⟩ := hg.cusps γ
    refine ⟨C + D, fun τ hτ => ?_⟩
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC τ hτ) (hD τ hτ))

theorem smul {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) (c : ℂ) :
    IsThetaTypeForm N (c • f) where
  holo := hf.holo.const_smul c
  multiplier γ hγ τ hτ := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hf.multiplier γ hγ τ hτ]
    ring
  cusps γ := by
    obtain ⟨C, hC⟩ := hf.cusps γ
    refine ⟨‖c‖ * C, fun τ hτ => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC τ hτ) (norm_nonneg c)

/-- The space of holomorphic θ-type weight-`½` forms for `Γ₁(N)`. -/
def submodule (N : ℕ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | IsThetaTypeForm N f}
  zero_mem' := zero
  add_mem' hf hg := add hf hg
  smul_mem' c _ hf := smul hf c

/-- `f(τ + 1) = f(τ)` for `Im τ ≥ 1/2` (cancel `θ`, which does not vanish there). -/
theorem add_one_of_half_le {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) {τ : ℂ}
    (hτ : 1 / 2 ≤ τ.im) : f (τ + 1) = f τ := by
  have h := hf.multiplier matT (matT_mem_Gamma1 N) τ (by linarith)
  rw [mobius_matT, thetaRef_add_one] at h
  exact mul_right_cancel₀ (thetaRef_ne_zero hτ) (h.trans (mul_comm _ _))

/-- **Periodicity.** A θ-type form satisfies `f(τ + 1) = f(τ)` on the whole upper half plane
(identity theorem from `Im τ ≥ 1/2`). -/
theorem add_one {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) {τ : ℂ} (hτ : 0 < τ.im) :
    f (τ + 1) = f τ := by
  set g : ℂ → ℂ := fun z => f (z + 1) - f z with hg
  have hmaps : Set.MapsTo (fun z : ℂ => z + 1) upperSet upperSet := fun z hz => by
    simpa using hz
  have hgd : DifferentiableOn ℂ g upperSet :=
    (hf.holo.comp ((differentiableOn_id).add_const 1) hmaps).sub hf.holo
  have hga : AnalyticOnNhd ℂ g upperSet := hgd.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hI : (Complex.I : ℂ) ∈ upperSet := by simp
  have hev : g =ᶠ[𝓝 Complex.I] 0 := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.im} := isOpen_lt continuous_const continuous_im
    filter_upwards [hopen.mem_nhds (by simp; norm_num)] with z hz
    simp only [hg, Pi.zero_apply, sub_eq_zero]
    exact hf.add_one_of_half_le (le_of_lt hz)
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_upperSet hI hev hτ
  simpa [hg, sub_eq_zero] using this

/-- `f` is bounded on `Im τ ≥ 1`. -/
theorem bounded {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖f τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.cusps 1
  exact ⟨C, fun τ hτ => by simpa [mobius_one] using hC τ hτ⟩

/-- **q-expansion.** A θ-type form has a `q`-expansion with only non-negative integer powers:
`f(τ) = Σ_{n ≥ 0} a_n qⁿ`, `q = e^{2πiτ}`. -/
theorem exists_qExpansion {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) :
    ∃ a : ℕ → ℂ, ∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => a n * cexp (2 * Real.pi * I * n * τ)) (f τ) := by
  set g : ℍ → ℂ := fun τ => f τ with hg
  have hper : Periodic (g ∘ ofComplex) 1 := by
    intro w
    change g (ofComplex (w + ((1 : ℝ) : ℂ))) = g (ofComplex w)
    rw [Complex.ofReal_one]
    by_cases hw : 0 < w.im
    · have hw' : 0 < (w + 1).im := by simpa using hw
      rw [ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
      exact hf.add_one hw
    · have hw' : (w + 1).im ≤ 0 := by simpa using hw
      rw [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos (not_lt.mp hw)]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine hf.holo.congr fun z hz => ?_
    simp [hg, ofComplex_apply_of_im_pos hz]
  have hbdd : IsBoundedAtImInfty g := by
    rw [isBoundedAtImInfty_iff]
    obtain ⟨C, hC⟩ := hf.bounded
    exact ⟨C, 1, fun z hz => hC z hz⟩
  refine ⟨fun n => (qExpansion 1 g).coeff n, fun τ hτ => ?_⟩
  have h := hasSum_qExpansion one_pos hper hhol hbdd ⟨τ, hτ⟩
  convert h using 2 with n
  · rw [smul_eq_mul, Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

end IsThetaTypeForm

/-! ## 3. The weight-one law of `θ²` on `Γ₁(4)`

`θ(γτ)² = (cτ + d) θ(τ)²` for `γ = (a b; c d)` with `4 ∣ c`, `d ≡ 1 (mod 4)`. Proof: the law is
multiplicative, holds for `T^n` and for `U_m = (1 0; 4m 1)` (by the `S`-transformation, squared,
so that no branch of the square root intervenes), and every such `γ` is a product of these
(Euclidean descent on `|c|`). -/

/-- The law `θ(γτ)² = (cτ + d) θ(τ)²`. -/
def ThetaSqLaw (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  ∀ τ : ℂ, 0 < τ.im → thetaRef (mobius γ τ) ^ 2 = ((γ 1 0 : ℂ) * τ + γ 1 1) * thetaRef τ ^ 2

theorem denom_ne_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by
  intro h
  have him : ((γ 1 0 : ℂ) * τ + γ 1 1).im = (γ 1 0 : ℝ) * τ.im := by simp
  rw [h, zero_im] at him
  have hc : (γ 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.mp him.symm with h' | h'
    · exact h'
    · exact absurd h' hτ.ne'
  have hc' : γ 1 0 = 0 := by exact_mod_cast hc
  have hre : ((γ 1 0 : ℂ) * τ + γ 1 1) = (γ 1 1 : ℂ) := by rw [hc']; simp
  rw [hre] at h
  have hd : γ 1 1 = 0 := by exact_mod_cast h
  have := γ.det_coe
  rw [Matrix.det_fin_two, hc', hd] at this
  simp at this

theorem mobius_apply (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) :
    mobius γ τ = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := rfl

/-- The automorphy factor is a cocycle. -/
theorem denom_mul (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    (((γ * δ) 1 0 : ℤ) : ℂ) * τ + ((γ * δ) 1 1 : ℤ) =
      ((γ 1 0 : ℂ) * mobius δ τ + γ 1 1) * ((δ 1 0 : ℂ) * τ + δ 1 1) := by
  have hd := denom_ne_zero δ hτ
  rw [mobius_apply, add_mul, mul_assoc, div_mul_cancel₀ _ hd, Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem ThetaSqLaw.mul {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : ThetaSqLaw γ)
    (hδ : ThetaSqLaw δ) : ThetaSqLaw (γ * δ) := by
  intro τ hτ
  rw [mobius_mul _ _ hτ, hγ _ (im_mobius_pos δ hτ), hδ τ hτ, denom_mul γ δ hτ]
  ring

theorem thetaSqLaw_T_zpow (n : ℤ) : ThetaSqLaw (ModularGroup.T ^ n) := by
  intro τ _
  rw [mobius_T_zpow, thetaRef_add_int]
  simp [ModularGroup.coe_T_zpow]

/-- `θ(τ/4)` is the series `Σ q^{n²/4}`. -/
theorem rankOneTheta_quarter (τ : ℂ) : rankOneTheta 0 1 (1 / 4) τ = thetaRef (τ / 4) := by
  rw [thetaRef, rankOneTheta, rankOneTheta]
  refine tsum_congr fun m => ?_
  simp only [rankOneThetaTerm]
  congr 1
  push_cast
  ring

/-- The `S`-transformation of `θ`, squared: `θ(-1/τ)² = (-iτ/2) θ(τ/4)²`. -/
theorem thetaRef_S_sq {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef (-1 / τ) ^ 2 = (-I * (τ / 2)) * thetaRef (τ / 4) ^ 2 := by
  have h := rankOneTheta_zero_one_S (t := 1) one_pos hτ
  rw [show (1 : ℝ) / (4 * 1) = 1 / 4 by norm_num, rankOneTheta_quarter] at h
  have h' : thetaRef (-1 / τ) = (-I * (τ / 2)) ^ (1 / 2 : ℂ) * thetaRef (τ / 4) := by
    rw [thetaRef]
    simpa using h
  rw [h', mul_pow, one_div, cpow_ofNat_inv_pow]

/-- `U_m = (1 0; 4m 1)`. -/
def matU (m : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; 4 * m, 1], by simp [Matrix.det_fin_two]⟩

theorem mobius_matU (m : ℤ) (τ : ℂ) : mobius (matU m) τ = τ / (4 * (m : ℂ) * τ + 1) := by
  simp [mobius, matU]

theorem thetaSqLaw_U (m : ℤ) : ThetaSqLaw (matU m) := by
  intro τ hτ
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hden : 4 * (m : ℂ) * τ + 1 ≠ 0 := by
    simpa [matU] using denom_ne_zero (matU m) hτ
  set w : ℂ := -1 / τ + ((-(4 * m) : ℤ) : ℂ) with hw
  have hinv : 0 < (-1 / τ).im := by
    have := im_mobius_pos ModularGroup.S hτ
    rwa [mobius_S] at this
  have hwim : 0 < w.im := by simpa [hw] using hinv
  have hw0 : w ≠ 0 := fun h => by simp [h] at hwim
  have h4τ : 0 < (4 * τ).im := by simp; linarith
  have hweq : w = -(4 * (m : ℂ) * τ + 1) / τ := by
    rw [hw]; push_cast; field_simp; ring
  have hmob : mobius (matU m) τ = -1 / w := by
    rw [mobius_matU, hweq]
    field_simp
  have hw4 : w / 4 = -1 / (4 * τ) + ((-m : ℤ) : ℂ) := by
    rw [hw]; push_cast; field_simp
  have hwτ : w * τ = -(4 * (m : ℂ) * τ + 1) := by
    rw [hweq]; field_simp
  clear_value w
  have h1 := thetaRef_S_sq hwim
  have h2 := thetaRef_S_sq h4τ
  rw [hmob, h1, hw4, thetaRef_add_int, h2, show 4 * τ / 4 = τ by ring]
  simp only [matU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  linear_combination (-thetaRef τ ^ 2) * hwτ + (w * τ * thetaRef τ ^ 2) * I_sq

theorem matU_mul_neg (m : ℤ) : matU m * matU (-m) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matU, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_T_zpow_one_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (k : ℤ) :
    (γ * ModularGroup.T ^ k) 1 0 = γ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem mul_T_zpow_one_one (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (k : ℤ) :
    (γ * ModularGroup.T ^ k) 1 1 = γ 1 1 + γ 1 0 * k := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem mul_matU_one_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℤ) :
    (γ * matU m) 1 0 = γ 1 0 + 4 * m * γ 1 1 := by
  simp [matU, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem mul_matU_one_one (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℤ) :
    (γ * matU m) 1 1 = γ 1 1 := by
  simp [matU, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- Balanced division: `d + c k` can be brought into `[-|c|/2, |c|/2]`. -/
theorem exists_balanced (c d : ℤ) (hc : c ≠ 0) :
    ∃ k : ℤ, 2 * (d + c * k) ≤ c.natAbs ∧ -(c.natAbs : ℤ) ≤ 2 * (d + c * k) := by
  have h1 := Int.emod_add_mul_ediv d c
  have h2 := Int.emod_nonneg d hc
  have h3 := Int.emod_lt d hc
  generalize d % c = r at *
  generalize d / c = q at *
  rcases Int.natAbs_eq c with h | h
  · by_cases hr : 2 * r ≤ c.natAbs
    · exact ⟨-q, by nlinarith, by nlinarith⟩
    · exact ⟨-q - 1, by nlinarith, by nlinarith⟩
  · by_cases hr : 2 * r ≤ c.natAbs
    · exact ⟨-q, by nlinarith, by nlinarith⟩
    · exact ⟨-q + 1, by nlinarith, by nlinarith⟩

theorem descent_arith (c d₁ P j : ℤ) (hc : c = 4 * j) (hd₁ : d₁ % 4 = 1)
    (hk1 : 2 * d₁ ≤ c.natAbs) (hk2 : -(c.natAbs : ℤ) ≤ 2 * d₁)
    (hm1 : 2 * (c + 4 * P) ≤ (4 * d₁).natAbs) (hm2 : -((4 * d₁).natAbs : ℤ) ≤ 2 * (c + 4 * P)) :
    (c + 4 * P).natAbs < c.natAbs := by
  omega

/-- The base of the descent: `c = 0`, `d ≡ 1 (mod 4)` forces `γ = T^b`. -/
theorem eq_T_zpow_of_c_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : γ 1 0 = 0)
    (hd : γ 1 1 % 4 = 1) : γ = ModularGroup.T ^ (γ 0 1) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd1 : γ 1 1 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have ha1 : γ 0 0 = 1 := by rw [hd1, mul_one] at hdet; exact hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ha1, hd1, hc]

/-- **Descent.** `θ(γτ)² = (cτ + d) θ(τ)²` for every `γ` with `4 ∣ c`, `d ≡ 1 (mod 4)`. -/
theorem thetaSqLaw_of_four_dvd : ∀ (n : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ),
    (γ 1 0).natAbs = n → 4 ∣ γ 1 0 → γ 1 1 % 4 = 1 → ThetaSqLaw γ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro γ hn hc4 hd4
  by_cases hc0 : γ 1 0 = 0
  · rw [eq_T_zpow_of_c_zero γ hc0 hd4]
    exact thetaSqLaw_T_zpow _
  obtain ⟨k, hk1, hk2⟩ := exists_balanced (γ 1 0) (γ 1 1) hc0
  obtain ⟨γ₁, hγ₁⟩ : ∃ g, g = γ * ModularGroup.T ^ k := ⟨_, rfl⟩
  have hc₁ : γ₁ 1 0 = γ 1 0 := by rw [hγ₁]; exact mul_T_zpow_one_zero γ k
  have hd₁ : γ₁ 1 1 = γ 1 1 + γ 1 0 * k := by rw [hγ₁]; exact mul_T_zpow_one_one γ k
  obtain ⟨j, hj⟩ := hc4
  have hd₁4 : γ₁ 1 1 % 4 = 1 := by
    rw [hd₁, hj, mul_assoc, Int.add_mul_emod_self_left]; exact hd4
  have hd₁0 : 4 * γ₁ 1 1 ≠ 0 := by omega
  obtain ⟨m, hm1, hm2⟩ := exists_balanced (4 * γ₁ 1 1) (γ 1 0) hd₁0
  obtain ⟨γ₂, hγ₂⟩ : ∃ g, g = γ₁ * matU m := ⟨_, rfl⟩
  have hc₂ : γ₂ 1 0 = γ 1 0 + 4 * (γ₁ 1 1 * m) := by
    rw [hγ₂, mul_matU_one_zero, hc₁]; ring
  have hd₂ : γ₂ 1 1 = γ₁ 1 1 := by rw [hγ₂]; exact mul_matU_one_one γ₁ m
  rw [mul_assoc] at hm1 hm2
  rw [← hd₁] at hk1 hk2
  have hlt : (γ₂ 1 0).natAbs < n := by
    rw [← hn, hc₂]
    exact descent_arith _ _ _ j hj hd₁4 hk1 hk2 hm1 hm2
  have h₂ : ThetaSqLaw γ₂ := ih _ hlt γ₂ rfl
    (by rw [hc₂, hj]; exact ⟨j + γ₁ 1 1 * m, by ring⟩) (by rw [hd₂]; exact hd₁4)
  have hγ : γ = γ₂ * matU (-m) * ModularGroup.T ^ (-k) := by
    rw [hγ₂, mul_assoc γ₁, matU_mul_neg, mul_one, hγ₁, mul_assoc, ← zpow_add, add_neg_cancel,
      zpow_zero, mul_one]
  rw [hγ]
  refine (h₂.mul (thetaSqLaw_U _)).mul (thetaSqLaw_T_zpow _)

/-- `θ(γτ)² = (cτ + d) θ(τ)²` on `Γ₁(N)`, `4 ∣ N`. -/
theorem thetaSqLaw_of_mem_Gamma1 {N : ℕ} (hN : 4 ∣ N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) : ThetaSqLaw γ := by
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨-, hd, hc⟩ := hγ
  have hN' : (4 : ℤ) ∣ (N : ℤ) := by exact_mod_cast hN
  have hc' : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hc
  have hd' : (N : ℤ) ∣ 1 - γ 1 1 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 1 1) 1 N).mp (by simpa using hd)
    exact this
  refine thetaSqLaw_of_four_dvd _ γ rfl (hN'.trans hc') ?_
  obtain ⟨e, he⟩ := hN'.trans hd'
  omega

/-! ### The weight-one form `f θ` -/

theorem differentiableOn_thetaRef : DifferentiableOn ℂ thetaRef upperSet := by
  intro τ hτ
  have h2 : 0 < (2 * τ).im := by
    have : (2 * τ).im = 2 * τ.im := by simp
    rw [this]; exact mul_pos two_pos hτ
  have hfun : thetaRef = fun z => jacobiTheta (2 * z) := funext thetaRef_eq_jacobiTheta
  rw [hfun]
  exact ((differentiableAt_jacobiTheta h2).comp τ
    ((differentiableAt_id).const_mul 2)).differentiableWithinAt

theorem differentiableOn_mobius (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    DifferentiableOn ℂ (mobius γ) upperSet := by
  intro τ hτ
  have hfun : mobius γ = fun z => ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) :=
    funext (mobius_apply γ)
  rw [hfun]
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (((differentiableAt_id).const_mul _).add_const _).div
    (((differentiableAt_id).const_mul _).add_const _) (denom_ne_zero γ hτ)

/-- **Weight one.** For `4 ∣ N` and a θ-type form `f` of level `N`, the product `F = f θ` is a
weight-one form for `Γ₁(N)` with trivial multiplier: `F(γτ) = (cτ + d) F(τ)`. (On `Im τ > ½`
this is the θ-multiplier law times the `θ²` law, cancelling `θ(τ) ≠ 0`; it then holds on all of
`ℍ` by the identity theorem, so no non-vanishing of `θ` on `ℍ` is needed.) -/
theorem IsThetaTypeForm.weight_one {N : ℕ} (h4 : 4 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) {τ : ℂ}
    (hτ : 0 < τ.im) :
    f (mobius γ τ) * thetaRef (mobius γ τ) =
      ((γ 1 0 : ℂ) * τ + γ 1 1) * (f τ * thetaRef τ) := by
  set g : ℂ → ℂ := fun z => f (mobius γ z) * thetaRef (mobius γ z) -
    ((γ 1 0 : ℂ) * z + γ 1 1) * (f z * thetaRef z) with hg
  have hmaps : Set.MapsTo (mobius γ) upperSet upperSet := fun z hz => im_mobius_pos γ hz
  have hgd : DifferentiableOn ℂ g upperSet := by
    refine ((hf.holo.comp (differentiableOn_mobius γ) hmaps).mul
      (differentiableOn_thetaRef.comp (differentiableOn_mobius γ) hmaps)).sub ?_
    exact (((differentiableOn_id).const_mul _).add_const _).mul
      (hf.holo.mul differentiableOn_thetaRef)
  have hga : AnalyticOnNhd ℂ g upperSet :=
    hgd.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hI : (Complex.I : ℂ) ∈ upperSet := by simp
  have hev : g =ᶠ[𝓝 Complex.I] 0 := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.im} := isOpen_lt continuous_const continuous_im
    filter_upwards [hopen.mem_nhds (by simp; norm_num)] with z hz
    have hz0 : 0 < z.im := lt_trans (by norm_num) hz
    have hθ := thetaRef_ne_zero (le_of_lt hz)
    have hm := hf.multiplier γ hγ z hz0
    have hs := thetaSqLaw_of_mem_Gamma1 h4 hγ z hz0
    simp only [hg, Pi.zero_apply, sub_eq_zero]
    refine mul_right_cancel₀ hθ ?_
    linear_combination thetaRef (mobius γ z) * hm + f z * hs
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_upperSet hI hev hτ
  simpa [hg, sub_eq_zero] using this

/-! ## 4. Serre–Stark's character theta series -/

/-- Serre–Stark's theta series `θ_{ψ,t}(τ) = Σ_{n ∈ ℤ} ψ(n) q^{t n²}` for a Dirichlet character
`ψ` modulo `r`. -/
def charTheta (r : ℕ) (ψ : DirichletCharacter ℂ r) (t : ℝ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ψ (n : ZMod r) * thetaExp t τ n

/-- Over a full set of residues, `ψ(j)·[n ≡ j]` picks out `ψ(n)`. -/
theorem sum_range_char_ite (r : ℕ) (hr : 0 < r) (ψ : DirichletCharacter ℂ r) (n : ℤ) (x : ℂ) :
    ∑ j ∈ Finset.range r, ψ (j : ZMod r) * (if n ≡ (j : ℤ) [ZMOD r] then x else 0) =
      ψ (n : ZMod r) * x := by
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have hmod0 : 0 ≤ n % r := Int.emod_nonneg n hr'.ne'
  have hmodr : n % r < r := Int.emod_lt_of_pos n hr'
  set j₀ : ℕ := (n % r).toNat with hj₀
  have hj₀z : (j₀ : ℤ) = n % r := Int.toNat_of_nonneg hmod0
  have hj₀mem : j₀ ∈ Finset.range r := by
    rw [Finset.mem_range]; omega
  rw [Finset.sum_eq_single_of_mem j₀ hj₀mem]
  · have hc : n ≡ (j₀ : ℤ) [ZMOD r] := by rw [hj₀z]; exact (Int.mod_modEq n r).symm
    rw [if_pos hc]
    congr 2
    rw [show ((j₀ : ℕ) : ZMod r) = ((j₀ : ℤ) : ZMod r) by push_cast; rfl, hj₀z, ZMod.intCast_mod]
  · intro j hj hne
    rw [if_neg, mul_zero]
    intro hc
    apply hne
    have hjr : (j : ℤ) < r := by exact_mod_cast Finset.mem_range.mp hj
    have h1 : (j : ℤ) % r = n % r := hc.symm
    rw [Int.emod_eq_of_lt (by positivity) hjr] at h1
    omega

/-- `θ_{ψ,t} = Σ_{j mod r} ψ(j) θ_{j,r,t}`. -/
theorem charTheta_eq_sum (r : ℕ) (hr : 0 < r) (ψ : DirichletCharacter ℂ r) {t : ℝ} (ht : 0 < t)
    {τ : ℂ} (hτ : 0 < τ.im) :
    charTheta r ψ t τ = ∑ j ∈ Finset.range r, ψ (j : ZMod r) * rankOneTheta j r t τ := by
  have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have H : HasSum (fun n : ℤ => ∑ j ∈ Finset.range r,
      ψ (j : ZMod r) * (if n ≡ (j : ℤ) [ZMOD r] then thetaExp t τ n else 0))
      (∑ j ∈ Finset.range r, ψ (j : ZMod r) * rankOneTheta j r t τ) :=
    hasSum_sum fun j _ => (hasSum_rankOneTheta_ite (j : ℤ) hr0 ht hτ).mul_left _
  rw [charTheta, ← H.tsum_eq]
  exact tsum_congr fun n => (sum_range_char_ite r hr ψ n _).symm

/-! ## 5. The residual: Serre–Stark's Theorem A in its published form -/

/-- **Serre–Stark, Theorem A (Γ₁(N) form).** For `4 ∣ N`, every holomorphic θ-type weight-`½`
form for `Γ₁(N)` is a finite linear combination of the series
`θ_{ψ,t}(τ) = Σ_{n∈ℤ} ψ(n) q^{t n²}` with `ψ` an even primitive Dirichlet character of
conductor `r` and `4 r² t ∣ N`.

*Source.* J.-P. Serre and H. M. Stark, *Modular forms of weight 1/2*, Modular Functions of One
Variable VI, LNM 627 (1977), 27–67: Theorem A (the `θ_{ψ,t}`, `(ψ, t) ∈ Ω(N, χ)`, form a basis of
`M_{1/2}(Γ₀(N), χ)`) together with the decomposition `M_{1/2}(Γ₁(N)) = ⊕_χ M_{1/2}(Γ₀(N), χ)`
over even characters `χ` mod `N`. Only the spanning half of "basis" is asserted here.

This is the statement of the source verbatim (characters, not residue classes); the passage
to the `θ_{n₀,r,t}` of `ISerreStark` is `iSerreStark_of_theoremA`, proved below. -/
def SerreStarkTheoremA : Prop :=
  ∀ (N : ℕ) (f : ℂ → ℂ), 0 < N → 4 ∣ N → IsThetaTypeForm N f →
    ∃ (m : ℕ) (r t : Fin m → ℕ) (ψ : ∀ i, DirichletCharacter ℂ (r i)) (c : Fin m → ℂ),
      (∀ i, (ψ i).IsPrimitive ∧ (ψ i).Even ∧ 1 ≤ t i ∧ 4 * t i * r i ^ 2 ∣ N) ∧
      ∀ τ : ℂ, 0 < τ.im → f τ = ∑ i, c i * charTheta (r i) (ψ i) (t i) τ

/-- **Reduction.** Serre–Stark's Theorem A (character form) implies `ISerreStark`. -/
theorem iSerreStark_of_theoremA (hA : SerreStarkTheoremA) : ISerreStark := by
  intro N f hN h4 hf
  obtain ⟨m, r, t, ψ, c, hcond, hfe⟩ := hA N f hN h4 hf
  have hr : ∀ i, 0 < r i := fun i => by
    rcases Nat.eq_zero_or_pos (r i) with h | h
    · have := (hcond i).2.2.2
      rw [h] at this
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_dvd_iff] at this
      omega
    · exact h
  -- the index triples `(j, r_i, t_i)`
  let q : (i : Fin m) → ℕ → ℤ × ℕ × ℕ := fun i j => ((j : ℤ), r i, t i)
  let s : Finset (ℤ × ℕ × ℕ) :=
    Finset.univ.biUnion fun i => (Finset.range (r i)).image (q i)
  let coef : ℤ × ℕ × ℕ → ℂ := fun p =>
    ∑ i, ∑ j ∈ Finset.range (r i), if q i j = p then c i * ψ i (j : ZMod (r i)) else 0
  have hmem : ∀ i, ∀ j ∈ Finset.range (r i), q i j ∈ s := fun i j hj =>
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hj⟩
  refine ⟨s, coef, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨hr i, (hcond i).2.2.1, by
      have := (hcond i).2.2.2
      simpa [q, mul_comm, mul_left_comm, mul_assoc] using this⟩
  · intro τ hτ
    rw [hfe τ hτ]
    have hexp : ∀ i, c i * charTheta (r i) (ψ i) (t i) τ =
        ∑ j ∈ Finset.range (r i), c i * ψ i (j : ZMod (r i)) *
          rankOneTheta (q i j).1 (q i j).2.1 (q i j).2.2 τ := by
      intro i
      have ht : (0 : ℝ) < t i := by exact_mod_cast (hcond i).2.2.1
      rw [charTheta_eq_sum (r i) (hr i) (ψ i) ht hτ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [q]
      ring
    simp_rw [hexp]
    simp only [coef, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq s (q i j) (fun p => c i * ψ i (j : ZMod (r i)) *
      rankOneTheta p.1 p.2.1 p.2.2 τ), if_pos (hmem i j hj)]

end VOA.Classification.COne
