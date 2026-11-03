/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkCusp
import VOA.Classification.COne.WeilKernel

/-!
# Serre–Stark, stage S2-3: the theta series are θ-type forms (the "easy half")

For `24 ∣ N` and `4 t r² ∣ N` (`r, t ≥ 1`):

* `isThetaTypeForm_rankOneTheta`: `θ_{n₀,r,t}` is a θ-type form of level `N`;
* `isThetaTypeForm_charTheta`: Serre–Stark's `θ_{ψ,t} = Σ_n ψ(n) q^{t n²}` is a θ-type form of
  level `N`, for every Dirichlet character `ψ` mod `r`.

The multiplier law comes from the unconditional theta Galois law (`WeilGalois.thetaGaloisLaw`,
GR Prop 3.8) at `ℓ = 1`, after writing `γ ∈ Γ₁(N)` as `δ Tᵇ` with `δ ∈ Γ(N)`; the cusp condition
from `rankOneTheta_cusp_bound`. (`24 ∣ N` is where the `η`-normalised law applies; it is the case
used by the classification, whose levels are multiples of `24`.)
-/

open Complex Filter Topology

noncomputable section

namespace VOA.Classification.COne

/-- `θ_{n₀,r,t}(τ + b) = θ_{n₀,r,t}(τ)` for integers `b` and integer `t`. -/
theorem rankOneTheta_add_int (n₀ : ℤ) (r t : ℕ) (τ : ℂ) (b : ℤ) :
    rankOneTheta n₀ r t (τ + b) = rankOneTheta n₀ r t τ := by
  have hper : Function.Periodic (rankOneTheta n₀ r t) 1 := fun τ => by
    have := rankOneTheta_T n₀ r t τ
    rwa [Int.cast_natCast] at this
  simpa using hper.int_mul b τ

theorem differentiableOn_rankOneTheta (n₀ : ℤ) {r t : ℕ} (hr : 0 < r) (ht : 0 < t) :
    DifferentiableOn ℂ (rankOneTheta n₀ r t) upperSet := by
  intro τ hτ
  have hfun : rankOneTheta n₀ r t = fun z =>
      cexp (2 * Real.pi * I * (t : ℝ) * (n₀ : ℂ) ^ 2 * z) *
        jacobiTheta₂ (2 * (t : ℝ) * (r : ℤ) * n₀ * z) (2 * (t : ℝ) * ((r : ℤ) : ℂ) ^ 2 * z) :=
    funext (rankOneTheta_eq_jacobiTheta₂ n₀ r t)
  rw [hfun]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine ((differentiableAt_id.const_mul _).cexp).mul ?_
  have him : 0 < (2 * ((t : ℕ) : ℝ) * (((r : ℕ) : ℤ) : ℂ) ^ 2 * τ).im :=
    im_two_mul_sq_mul_pos (by exact_mod_cast hr.ne') (by exact_mod_cast ht) hτ
  have hJ := (hasFDerivAt_jacobiTheta₂ (2 * ((t : ℕ) : ℝ) * ((r : ℕ) : ℤ) * n₀ * τ)
    him).differentiableAt
  have hg : DifferentiableAt ℂ (fun z : ℂ => (2 * ((t : ℕ) : ℝ) * ((r : ℕ) : ℤ) * n₀ * z,
      2 * ((t : ℕ) : ℝ) * (((r : ℕ) : ℤ) : ℂ) ^ 2 * z)) τ :=
    DifferentiableAt.prodMk (differentiableAt_id.const_mul _) (differentiableAt_id.const_mul _)
  exact DifferentiableAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) τ hJ hg

/-- **Multiplier law of `θ_{n₀,r,t}` on `Γ₁(N)`**, `24 ∣ N`, `4 t r² ∣ N`. -/
theorem rankOneTheta_multiplier {N : ℕ} (h24 : 24 ∣ N) (n₀ : ℤ) {r t : ℕ} (hr : 0 < r)
    (ht : 0 < t) (hdiv : 4 * t * r ^ 2 ∣ N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) {τ : ℂ} (hτ : 0 < τ.im) :
    rankOneTheta n₀ r t (mobius γ τ) * thetaRef τ =
      thetaRef (mobius γ τ) * rankOneTheta n₀ r t τ := by
  set b : ℤ := γ 0 1
  set δ := γ * ModularGroup.T ^ (-b) with hδ
  have hγδ : γ = δ * ModularGroup.T ^ b := by rw [hδ, mul_assoc, ← zpow_add, neg_add_cancel,
    zpow_zero, mul_one]
  have hδΓ : δ ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma1_mem] at hγ
    obtain ⟨h00, h11, h10⟩ := hγ
    rw [CongruenceSubgroup.Gamma_mem]
    have e : ∀ i j, δ i j = ∑ k, γ i k * (ModularGroup.T ^ (-b)) k j := fun i j => by
      rw [hδ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    simp only [e, ModularGroup.coe_T_zpow, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    refine ⟨by simp [h00], ?_, by simp [h10], by simp [h10, h11]⟩
    rw [h00]; simp [b]
  have hτb : 0 < (τ + b).im := by simpa using hτ
  have hm : mobius γ τ = mobius δ (τ + b) := by
    rw [hγδ, mobius_mul _ _ hτ, mobius_T_zpow]
  rw [CongruenceSubgroup.Gamma_mem] at hδΓ
  obtain ⟨h00, h01, h10, h11⟩ := hδΓ
  have hθ := WeilGalois.thetaGaloisLaw n₀ r t N hr ht hdiv h24 1 (Nat.coprime_one_left N) 1
    (by simp) δ (by simpa using modEq_of_zmod (by simpa using h00))
    (by simpa using modEq_of_zmod (by simpa using h11))
    (modEq_of_zmod (by simpa using h01)) (modEq_of_zmod (by simpa using h10)) (τ + b) hτb
  have hη := eta_theta_of_thetaGaloisLaw WeilGalois.thetaGaloisLaw h24
    (CongruenceSubgroup.Gamma_mem.2 ⟨h00, h01, h10, h11⟩) hτb
  simp only [Nat.cast_one, Int.cast_one, one_mul, jacobiSym.one_right] at hθ
  have hηw : ModularForm.eta (τ + b) ≠ 0 := ModularForm.eta_ne_zero hτb
  rw [hm, ← rankOneTheta_add_int n₀ r t τ b, ← thetaRef_add_int τ b]
  refine mul_right_cancel₀ hηw ?_
  linear_combination (thetaRef (τ + b)) * hθ + rankOneTheta n₀ r t (τ + b) * hη

/-- **`θ_{n₀,r,t}` is a θ-type form of level `N`** (`24 ∣ N`, `4 t r² ∣ N`, `r, t ≥ 1`). -/
theorem isThetaTypeForm_rankOneTheta {N : ℕ} (h24 : 24 ∣ N) (n₀ : ℤ) {r t : ℕ} (hr : 0 < r)
    (ht : 0 < t) (hdiv : 4 * t * r ^ 2 ∣ N) : IsThetaTypeForm N (rankOneTheta n₀ r t) where
  holo := differentiableOn_rankOneTheta n₀ hr ht
  multiplier _ hγ _ hτ := rankOneTheta_multiplier h24 n₀ hr ht hdiv hγ hτ
  cusps := rankOneTheta_cusp_bound n₀ hr ht

/-- θ-type forms only see the upper half plane. -/
theorem IsThetaTypeForm.congr {N : ℕ} {f g : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (h : ∀ τ : ℂ, 0 < τ.im → f τ = g τ) : IsThetaTypeForm N g where
  holo := hf.holo.congr fun τ hτ => (h τ hτ).symm
  multiplier γ hγ τ hτ := by
    rw [← h τ hτ, ← h _ (im_mobius_pos γ hτ)]
    exact hf.multiplier γ hγ τ hτ
  cusps γ := by
    obtain ⟨C, hC⟩ := hf.cusps γ
    exact ⟨C, fun τ hτ => by
      rw [← h _ (im_mobius_pos γ (lt_of_lt_of_le one_pos hτ))]; exact hC τ hτ⟩

theorem IsThetaTypeForm.sum {N : ℕ} {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, IsThetaTypeForm N (f i)) : IsThetaTypeForm N (∑ i ∈ s, f i) :=
  Submodule.sum_mem (IsThetaTypeForm.submodule N) hf

/-- **Serre–Stark's `θ_{ψ,t}` is a θ-type form of level `N`** (`24 ∣ N`, `4 t r² ∣ N`). -/
theorem isThetaTypeForm_charTheta {N : ℕ} (h24 : 24 ∣ N) {r t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (hdiv : 4 * t * r ^ 2 ∣ N) (ψ : DirichletCharacter ℂ r) :
    IsThetaTypeForm N (charTheta r ψ t) := by
  have hsum : IsThetaTypeForm N (∑ j ∈ Finset.range r,
      ψ (j : ZMod r) • rankOneTheta j r t) :=
    IsThetaTypeForm.sum _ fun j _ =>
      (isThetaTypeForm_rankOneTheta h24 j hr ht hdiv).smul _
  refine hsum.congr fun τ hτ => ?_
  rw [charTheta_eq_sum r hr ψ (by exact_mod_cast ht) hτ, Finset.sum_apply]
  rfl

end VOA.Classification.COne
