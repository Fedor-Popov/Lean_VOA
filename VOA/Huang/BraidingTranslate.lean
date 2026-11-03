/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.BraidingBinomial
import VOA.Huang.AssocTarget

/-!
# Skew-symmetry of iterates, analytically

For a strongly rational `V`, irreducible modules and an intertwiner `𝒴̃` of type `(Q / P₂ P₁)`,
put `𝒴₄ := Ω₀(𝒴̃)` (type `(Q / P₁ P₂)`, `𝒴₄(w₁,z₀)w₂ = e^{z₀L₋₁}𝒴̃(w₂, e^{πi}z₀)w₁`).  Then for
real `0 < x`, `2x < y` (`iterValue_skew`):

`⟨f, 𝒴₃(𝒴₄(w₁, x)w₂, y)w₃⟩ = ⟨f, 𝒴₃(𝒴̃(w₂, −x)w₁, y + x)w₃⟩`

(single-coset values `AssocTarget.iterValue`, principal powers; `(−x)^s = x^s e^{πis}`).  This is
the analytic content of `𝒴₃(e^{xL₋₁}v, y) = 𝒴₃(v, y + x)` for the infinite sum `v = 𝒴̃(w₂,−x)w₁`.
Since every intertwiner is `Ω₀` of another one (`skewModes_skewModes`), the identity applies to
every iterate (`iterValue_eq_skew`).

## Proof
* `Y_Lm1_pow`: `𝒴₃(n)(L₋₁ʲ v) = (∏_{i<j} −(n−i)) 𝒴₃(n−j) v` (the `L₋₁`-derivative property);
* `iterCoeff_skew`: the iterate coefficients of `Ω_c(𝒴̃)` are `c(ν₀−k) Σ_{j≤k} C(n, j) d_{k−j}`
  in terms of those of `𝒴̃` (the `j > k` terms vanish below the base);
* `BraidingBinomial.tsum_skew_translate` with the absolute convergence of the `𝒴̃` iterate
  at radii `(x, y − x)` (`HuangODEContra.summable_iterTerm_of_moduleC2Input`).

## Status
No `sorry`, no new axioms.  Unconditional for strongly rational `V` (the summability input is the
proved `ModuleC2Input` + Huang's ODEs).
-/

namespace VOA.Huang.BraidingSkew

open VOA VOA.SkewIntertwiner VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Algebra: iterate coefficients of `Ω_c(𝒴̃)` -/

section Coeff

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

theorem Y_Lm1_pow {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}
    {Y : IntertwiningModes M₅ M₃ M₄} (hY : IsIntertwiningOperator A₅ A₃ A₄ Y) (j : ℕ) (n : ℂ)
    (v : M₅) :
    Y n ((Lm1 A₅.toWeakModule ^ j) v)
      = (∏ i ∈ Finset.range j, (-(n - i))) • Y (n - j) v := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := hY.L_neg_one ((Lm1 A₅.toWeakModule ^ j) v) n
      have hL : Lm1 A₅.toWeakModule ((Lm1 A₅.toWeakModule ^ j) v)
          = A₅.Lm1 ((Lm1 A₅.toWeakModule ^ j) v) := rfl
      rw [hL, h, ih, smul_smul, Finset.prod_range_succ' (fun i => -(n - (i : ℂ))) j]
      rw [show n - 1 - (j : ℂ) = n - ((j + 1 : ℕ) : ℂ) by push_cast; ring]
      congr 1
      rw [mul_comm]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        push_cast; ring
      · simp

/-- `(−1)ʲ/j! · ∏_{i<j} −(n−i) = C(n, j)`. -/
theorem sc_mul_prod (n : ℂ) (j : ℕ) :
    sc j * ∏ i ∈ Finset.range j, (-(n - i)) = bc n j := by
  rw [sc, bc, Finset.prod_neg, Finset.card_range, div_eq_inv_mul]
  have h : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination ((j.factorial : ℂ)⁻¹ * ∏ i ∈ Finset.range j, (n - i)) * h

/-- **Iterate coefficients of `Ω_c(𝒴̃)`**: below a base `ν₀` of `𝒴̃` on `(w₂, w₁)`,
`⟨f, 𝒴₃(n)(Ω_c𝒴̃(ν₀−k) w₁ w₂) w₃⟩ = c(ν₀−k) Σ_{j≤k} C(n,j) ⟨f, 𝒴₃(n−j)(𝒴̃(ν₀−(k−j)) w₂ w₁) w₃⟩`. -/
theorem iterCoeff_skew {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}
    {Y₃ : IntertwiningModes M₅ M₃ M₄} (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    {Yt : IntertwiningModes M₂ M₁ M₅} (hYt : Trunc Yt) (c : ℂ → ℂ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) {ν₀ : ℂ} (hb : IsBase Yt w₂ w₁ ν₀) (k : ℕ) (n : ℂ) :
    iterCoeff Y₃ (skewModes (Lm1 A₅.toWeakModule) c Yt) f w₁ w₂ w₃ (ν₀ - k) n
      = c (ν₀ - k) * ∑ j ∈ Finset.range (k + 1),
          bc n j * iterCoeff Y₃ Yt f w₂ w₁ w₃ (ν₀ - ((k - j : ℕ) : ℂ)) (n - j) := by
  have hK : ∀ j : ℕ, k + 1 ≤ j → Yt (ν₀ - k + j) w₂ w₁ = 0 := by
    intro j hj
    have := hb (j - (k + 1))
    rwa [show ν₀ + (((j - (k + 1) : ℕ) : ℂ) + 1) = ν₀ - k + j by
      rw [Nat.cast_sub hj]; push_cast; ring] at this
  rw [iterCoeff, skewModes_apply hYt, sSum_eq_sum (k + 1) hK, map_smul, LinearMap.smul_apply,
    map_smul, smul_eq_mul, map_sum, LinearMap.sum_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [sTerm, map_smul, LinearMap.smul_apply, Y_Lm1_pow hY₃, LinearMap.smul_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, sc_mul_prod, iterCoeff,
    Nat.cast_sub (by omega : j ≤ k), show ν₀ - k + j = ν₀ - ((k : ℂ) - j) by ring]

end Coeff

/-! ## The analytic identity -/

section Value

/-- **Skew-symmetry of iterates (analytic form).**  For a strongly rational `V`,
irreducible modules, intertwiners `𝒴₃` of type `(P₄ / Q P₃)` and `𝒴̃` of type `(Q / P₂ P₁)`,
homogeneous `wᵢ ∈ Pᵢ(αᵢ)`, `f` supported at `h₄`, and real `0 < x`, `2x < y`:
`⟨f, 𝒴₃(Ω₀𝒴̃(w₁, x)w₂, y)w₃⟩ = ⟨f, 𝒴₃(𝒴̃(w₂, −x)w₁, y + x)w₃⟩`
(single-coset values, principal powers). -/
theorem iterValue_skew (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier}
    {Yt : IntertwiningModes P₂.carrier P₁.carrier Q.carrier}
    (hY₃ : IsIntertwiningOperator Q.isMod P₃.isMod P₄.isMod Y₃)
    (hYt : IsIntertwiningOperator P₂.isMod P₁.isMod Q.isMod Yt)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {x y : ℝ} (hx : 0 < x) (hxy : 2 * x < y) :
    iterValue Y₃ (skewModes (Lm1 Q.isMod.toWeakModule) omegaPhase Yt) f w₁ w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h) x y
      = iterValue Y₃ Yt f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h)
          (-(x : ℂ)) ((y + x : ℝ) : ℂ) := by
  set σ := α₁ + α₂ + α₃ - h₄ - 2 with hσ
  set ν₀ := α₁ + α₂ - 1 - Q.h with hν
  have hb : IsBase Yt w₂ w₁ ν₀ := by
    have := isBase_canonical Q hYt h₂ h₁
    rwa [show α₂ + α₁ - 1 - Q.h = ν₀ by rw [hν]; ring] at this
  have htr := trunc_of_isIntertwining hYt
  set d : ℕ → ℂ := fun p => iterCoeff Y₃ Yt f w₂ w₁ w₃ (ν₀ - p) (σ - ν₀ + p) with hd
  -- the summability input: the `𝒴̃` iterate at radii `(x, y − x)`
  have hS : Summable fun p : ℕ => ‖d p * ((y - x : ℝ) : ℂ) ^ (-(σ - ν₀ + p) - 1)
      * (x : ℂ) ^ (-(ν₀ - p) - 1)‖ := by
    have hyx : ‖(x : ℂ)‖ < ‖((y - x : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hx, abs_of_pos (by linarith)]
      linarith
    have := VOA.Huang.HuangODEContra.summable_iterTerm_of_moduleC2Input
      VOA.Huang.BuhlSpanning.moduleC2Input_holds hV i₂ i₁ i₃ i₄ Q.isMod hY₃ hYt h₂ h₁ h₃ hf hb
      (z₀ := (x : ℂ)) (z₂ := ((y - x : ℝ) : ℂ)) (by exact_mod_cast hx.ne') hyx
    rwa [show α₂ + α₁ + α₃ - h₄ - 2 = σ by rw [hσ]; ring] at this
  have hL : ∀ k : ℕ, iterCoeff Y₃ (skewModes (Lm1 Q.isMod.toWeakModule) omegaPhase Yt) f
      w₁ w₂ w₃ (ν₀ - k) (σ - ν₀ + k)
      = omegaPhase (ν₀ - k) * ∑ j ∈ Finset.range (k + 1), bc (σ - ν₀ + k) j * d (k - j) := by
    intro k
    rw [iterCoeff_skew hY₃ htr omegaPhase f w₁ w₂ w₃ hb k]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [hd]
    dsimp only
    rw [Nat.cast_sub (by omega : j ≤ k), show σ - ν₀ + (k : ℂ) - j = σ - ν₀ + ((k : ℂ) - j) by
      ring]
  have key := tsum_skew_translate (d := d) (a := σ - ν₀) (ν := ν₀) hx hxy hS
  rw [iterValue, iterValue]
  simp_rw [hL]
  rw [key]

/-- **Every iterate is a translated, skewed iterate**: for any intertwiner `𝒴₄` of type
`(Q / P₁ P₂)`, with `𝒴̃ := Ω_{1/ω}(𝒴₄)` of type `(Q / P₂ P₁)` (so that `Ω₀(𝒴̃) = 𝒴₄`), and real
`0 < x`, `2x < y`: `⟨f, 𝒴₃(𝒴₄(w₁, x)w₂, y)w₃⟩ = ⟨f, 𝒴₃(𝒴̃(w₂, −x)w₁, y + x)w₃⟩`. -/
theorem iterValue_eq_skew (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier}
    (hY₃ : IsIntertwiningOperator Q.isMod P₃.isMod P₄.isMod Y₃)
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod Q.isMod Y₄)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {x y : ℝ} (hx : 0 < x) (hxy : 2 * x < y) :
    iterValue Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h) x y
      = iterValue Y₃ (skewModes (Lm1 Q.isMod.toWeakModule) (fun n => (omegaPhase n)⁻¹) Y₄)
          f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h)
          (-(x : ℂ)) ((y + x : ℝ) : ℂ) := by
  have hc' : ∀ n, (fun n => (omegaPhase n)⁻¹) (n + 1) = -(fun n => (omegaPhase n)⁻¹) n :=
    fun n => by simp only [omegaPhase_succ, inv_neg]
  have hc'0 : ∀ n, (fun n => (omegaPhase n)⁻¹) n ≠ 0 := fun n => inv_ne_zero (omegaPhase_ne_zero n)
  have hYt := isIntertwiningOperator_skewModes hY₄ hc' hc'0
  have hback : skewModes (Lm1 Q.isMod.toWeakModule) omegaPhase
      (skewModes (Lm1 Q.isMod.toWeakModule) (fun n => (omegaPhase n)⁻¹) Y₄) = Y₄ :=
    skewModes_skewModes hc' (fun n => mul_inv_cancel₀ (omegaPhase_ne_zero n))
      (trunc_of_isIntertwining hY₄)
  have := iterValue_skew hV i₁ i₂ i₃ i₄ hY₃ hYt h₁ h₂ h₃ hf hx hxy
  rwa [hback] at this

end Value

end VOA.Huang.BraidingSkew
