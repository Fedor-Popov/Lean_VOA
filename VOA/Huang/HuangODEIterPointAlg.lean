/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangODEProduct
import VOA.Modularity.QDerivProductRule

/-!
# Products at the iterate point: the formal equation

Huang, CCM 7 (2005), Thm 1.4 + Thm 2.3 at the singular point `z₂⁻¹(z₁ − z₂) = 0`, for **products**
(not iterates).  The library's product moves `HuangODEProduct.moveA … moveD` are exact identities of
power series in `x = z₂/z₁`, normalized by the total level `s` (`QT`), whose coefficients are
`xᵉ`, constants, or `x · binomSeries 1 k = x^{k+1}(1 − x)^{−k−1}` — and in each binomial term the
level drops by at least `k + 1`.  **Renormalizing by `(1 − x)^s`** (at `z₂ = 1`, `u = z₁ − z₂`:
`(1 − x)^s x^{−s} = u^s`, Huang's `(z₁ − z₂)^S` normalization at the iterate point) turns every
move into a relation with **polynomial** coefficients `ℂ[x] = ratRing 0` (`pt_mem`).

The derivative `d/dt` at `z₂ = 1`, `z₁ = 1 + e^t`, `x = (1 + e^t)⁻¹`, conjugated by
`e^{−σ t}(1 + e^t)^{−κ}`, is the formal operator `DOp κ σ Z = −(1 − X)(θZ + κZ) − σZ`
(`θ = VOA.theta`); it satisfies `DOp(X^a Q_j) ∈ span{X^a Q_j, X^{a+1} Q_j, X^a Q_{j+1}}`
(`Q_j` the renormalized series of `L₋₁^j w₂`, by `QT_Lm1`), so all its iterates on the target stay
in the finitely generated `ℂ[x]`-module, and Noetherianity gives a monic relation
(`exists_dop_relation_prodSeries`).  The analytic translation is
`Huang/HuangODEIterPointAnalytic.lean`.

## Main results
* `pull`, `X_pow_mul_mem_pull`, `X_mul_binom_mul_mem_pull` — the renormalization bookkeeping.
* `pt_mem` — Huang's Prop. 1.1/2.1 at `z₁ = z₂` for products (one variable).
* `DOp`, `DOp_X_pow_mul`, `dop_iterate_mem`, `exists_dop_relation`.
* `exists_dop_relation_prodSeries` — the coset series `G` of a product satisfies
  `DOp^m H = Σ_{k<m} r_k DOp^k H`, `r_k ∈ ℂ[x]`, `H = (1 − x)^b x^K G`, for every `κ, σ`.

## Status
No `sorry`, no new axioms.  Conditional only on graded `C₁`-data
(as `ratFuchsian_prodSeries_of_C1`).
-/

namespace VOA.Huang.HuangODEIterPoint

open VOA PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence VOA.Huang.HuangODEAlgebra
  VOA.Huang.HuangODEModes VOA.Huang.MatrixCoeff VOA.Huang.HuangODEProduct
open scoped BigOperators

universe u

/-! ## The ring `ℂ[x]` and the pulled-back module -/

theorem one_sub_X_mem : ((1 : PowerSeries ℂ) - X) ∈ ratRing 0 :=
  Subalgebra.sub_mem _ (Subalgebra.one_mem _) (X_mem_ratRing 0)

theorem one_sub_X_pow_mem (n : ℕ) : ((1 : PowerSeries ℂ) - X) ^ n ∈ ratRing 0 :=
  Subalgebra.pow_mem _ one_sub_X_mem n

/-- The `ratRing 0`-module `NN` pulled back along multiplication by `(1 − X)^s`, as a `ℂ`-space. -/
noncomputable def pull (NN : Submodule (ratRing 0) (PowerSeries ℂ)) (s : ℕ) :
    Submodule ℂ (PowerSeries ℂ) :=
  (NN.restrictScalars ℂ).comap (LinearMap.mulLeft ℂ ((1 - X) ^ s))

theorem mem_pull {NN : Submodule (ratRing 0) (PowerSeries ℂ)} {s : ℕ} {y : PowerSeries ℂ} :
    y ∈ pull NN s ↔ (1 - X) ^ s * y ∈ NN := Iff.rfl

theorem X_pow_mul_mem_pull {NN : Submodule (ratRing 0) (PowerSeries ℂ)} {s s' : ℕ}
    {q : PowerSeries ℂ} (hq : (1 - X) ^ s' * q ∈ NN) (hs : s' ≤ s) (e : ℕ) :
    X ^ e * q ∈ pull NN s := by
  rw [mem_pull]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have h : (1 - X) ^ (s' + t) * (X ^ e * q) = (X ^ e * (1 - X) ^ t) * ((1 - X) ^ s' * q) := by
    ring
  rw [h]
  exact mul_mem_of_ratRing NN (Subalgebra.mul_mem _ (X_pow_mem 0 e) (one_sub_X_pow_mem t)) hq

theorem mem_pull_of_le {NN : Submodule (ratRing 0) (PowerSeries ℂ)} {s s' : ℕ}
    {q : PowerSeries ℂ} (hq : (1 - X) ^ s' * q ∈ NN) (hs : s' ≤ s) : q ∈ pull NN s := by
  have := X_pow_mul_mem_pull hq hs 0
  rwa [pow_zero, one_mul] at this

/-- The binomial terms: `(1 − x)^{s} · x^{k+1}(1 − x)^{−k−1} · q` is polynomial times
`(1 − x)^{s'} q` once `s' + k + 1 ≤ s`. -/
theorem X_mul_binom_mul_mem_pull {NN : Submodule (ratRing 0) (PowerSeries ℂ)} {s s' : ℕ}
    {q : PowerSeries ℂ} (hq : (1 - X) ^ s' * q ∈ NN) (k : ℕ) (hs : s' + k + 1 ≤ s) :
    X * HuangODEAlgebra.binomSeries 1 k * q ∈ pull NN s := by
  rw [mem_pull]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hb := HuangODEAlgebra.binomSeries_mul (1 : ℂ) k
  rw [map_one, one_mul] at hb
  have h : (1 - X) ^ (s' + k + 1 + t) * (X * HuangODEAlgebra.binomSeries 1 k * q)
      = X * ((1 - X) ^ (k + 1) * HuangODEAlgebra.binomSeries 1 k) * (1 - X) ^ t
        * ((1 - X) ^ s' * q) := by ring
  rw [h, hb]
  have h2 : X * X ^ k * (1 - X) ^ t * ((1 - X) ^ s' * q)
      = (X ^ (k + 1) * (1 - X) ^ t) * ((1 - X) ^ s' * q) := by ring
  rw [h2]
  exact mul_mem_of_ratRing NN (Subalgebra.mul_mem _ (X_pow_mem 0 _) (one_sub_X_pow_mem t)) hq

/-! ## The operator `d/dt` at the iterate point, formally -/

theorem theta_add (F G : PowerSeries ℂ) : VOA.theta (F + G) = VOA.theta F + VOA.theta G := by
  ext n; simp [mul_add]

theorem theta_sub (F G : PowerSeries ℂ) : VOA.theta (F - G) = VOA.theta F - VOA.theta G := by
  ext n; simp [mul_sub]

theorem theta_C_mul (a : ℂ) (F : PowerSeries ℂ) :
    VOA.theta (PowerSeries.C a * F) = PowerSeries.C a * VOA.theta F := by
  ext n; simp [PowerSeries.coeff_C_mul]; ring

theorem theta_one : VOA.theta (1 : PowerSeries ℂ) = 0 := by
  ext n; simp only [theta_coeff, coeff_one, map_zero]; split_ifs with h <;> simp [h]

theorem theta_X : VOA.theta (X : PowerSeries ℂ) = X := by
  ext n; simp only [theta_coeff, coeff_X]; split_ifs with h <;> simp [h]

theorem theta_X_pow (a : ℕ) :
    VOA.theta ((X : PowerSeries ℂ) ^ a) = PowerSeries.C (a : ℂ) * X ^ a := by
  ext n; rw [theta_coeff, coeff_C_mul, coeff_X_pow]; split_ifs with h <;> simp [h]

/-- `(1 − x) θ (1 − x)^n = −n x (1 − x)^n`. -/
theorem theta_one_sub_X_pow (n : ℕ) :
    (1 - X) * VOA.theta (((1 : PowerSeries ℂ) - X) ^ n)
      = -(PowerSeries.C (n : ℂ) * X * (1 - X) ^ n) := by
  induction n with
  | zero => simp [theta_one]
  | succ n ih =>
    rw [pow_succ, theta_mul, theta_sub, theta_one, theta_X]
    push_cast
    rw [map_add, map_one]
    linear_combination (1 - X) * ih

/-- **`d/dt` at the iterate point, formally.**  At `z₂ = 1`, `z₁ = 1 + e^t`, `x = (1 + e^t)⁻¹`:
`d/dt [e^{−σt}(1 + e^t)^{−κ} Z(x)] = e^{−σt}(1 + e^t)^{−κ} (DOp κ σ Z)(x)`. -/
noncomputable def DOp (κ σ : ℂ) : PowerSeries ℂ →ₗ[ℂ] PowerSeries ℂ where
  toFun Z := -((1 - X) * (VOA.theta Z + PowerSeries.C κ * Z)) - PowerSeries.C σ * Z
  map_add' F G := by simp only [theta_add]; ring
  map_smul' a F := by
    simp only [RingHom.id_apply, PowerSeries.smul_eq_C_mul, theta_C_mul]; ring

theorem DOp_apply (κ σ : ℂ) (Z : PowerSeries ℂ) :
    DOp κ σ Z = -((1 - X) * (VOA.theta Z + PowerSeries.C κ * Z)) - PowerSeries.C σ * Z := rfl

/-- **`DOp` on a renormalized series**: if `θA = B + μA` (the `L₋₁`-step) then
`DOp(X^a (1−X)^n A)` is a constant combination of `X^a(1−X)^nA`, `X^{a+1}(1−X)^nA` and
`X^a(1−X)^{n+1}B`. -/
theorem DOp_X_pow_mul (κ σ μ : ℂ) (a n : ℕ) {A B : PowerSeries ℂ}
    (hA : VOA.theta A = B + PowerSeries.C μ * A) :
    DOp κ σ (X ^ a * ((1 - X) ^ n * A))
      = (-(a : ℂ) - μ - κ - σ) • (X ^ a * ((1 - X) ^ n * A))
        + ((a : ℂ) + n + μ + κ) • (X ^ (a + 1) * ((1 - X) ^ n * A))
        - X ^ a * ((1 - X) ^ (n + 1) * B) := by
  have hT := theta_one_sub_X_pow n
  rw [DOp_apply, theta_mul, theta_mul, theta_X_pow, hA]
  simp only [PowerSeries.smul_eq_C_mul, map_add, map_sub, map_neg, map_natCast]
  simp only [map_natCast] at hT
  linear_combination (-(X ^ a * A)) * hT

/-- All `DOp`-iterates of `X^a Q_j` stay in `NN`
(`Q_j = (1−X)^{n₀+j} A_j`, `θA_j = A_{j+1} + μ_j A_j`). -/
theorem dop_iterate_mem (NN : Submodule (ratRing 0) (PowerSeries ℂ)) (κ σ : ℂ) (n₀ : ℕ)
    (A : ℕ → PowerSeries ℂ) (μ : ℕ → ℂ)
    (hA : ∀ j, VOA.theta (A j) = A (j + 1) + PowerSeries.C (μ j) * A j)
    (hmem : ∀ j, (1 - X) ^ (n₀ + j) * A j ∈ NN) :
    ∀ i a j, (DOp κ σ)^[i] (X ^ a * ((1 - X) ^ (n₀ + j) * A j)) ∈ NN := by
  intro i
  induction i with
  | zero =>
    intro a j
    simpa using mul_mem_of_ratRing NN (X_pow_mem 0 a) (hmem j)
  | succ i ih =>
    intro a j
    rw [Function.iterate_succ_apply, DOp_X_pow_mul κ σ (μ j) a (n₀ + j) (hA j),
      show n₀ + j + 1 = n₀ + (j + 1) by ring]
    have h1 := ih a j
    have h2 := ih (a + 1) j
    have h3 := ih a (j + 1)
    rw [← Module.End.pow_apply] at h1 h2 h3 ⊢
    rw [map_sub, map_add, map_smul, map_smul]
    exact NN.sub_mem (NN.add_mem (smul_mem_of_ratRing NN _ h1) (smul_mem_of_ratRing NN _ h2)) h3

/-- **Cor. 1.3 for `DOp`**: iterates in a finitely generated `ℂ[x]`-module satisfy a monic relation
with polynomial coefficients. -/
theorem exists_dop_relation (NN : Submodule (ratRing 0) (PowerSeries ℂ)) (hN : NN.FG)
    (D : PowerSeries ℂ →ₗ[ℂ] PowerSeries ℂ) {H : PowerSeries ℂ} (hH : ∀ i, D^[i] H ∈ NN) :
    ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ k, r k ∈ ratRing 0) ∧
      D^[m] H = ∑ k ∈ Finset.range m, r k * D^[k] H := by
  haveI : Module.Finite (ratRing 0) NN := Module.Finite.iff_fg.mpr hN
  obtain ⟨m, r, hr⟩ := VOA.Huang.MatrixCoeffODE.exists_monic_relation (R := ratRing 0)
    (fun j => (⟨D^[j] H, hH j⟩ : NN))
  refine ⟨m, fun k => (r k : PowerSeries ℂ), fun k => (r k).2, ?_⟩
  have := congrArg Subtype.val hr
  simpa [Submodule.coe_sum, Subalgebra.smul_def] using this

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Product

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}
  {Y₁ : IntertwiningModes M₁ M₅ M₄} {Y₂ : IntertwiningModes M₂ M₃ M₅}

section Induction

variable {h₁ h₂ h₃ h₄ ν : ℂ} {B₁ B₂ B₃ B₄ : ℕ}

/-- **Huang's Prop. 1.1 at the iterate point, for products.**  Under graded `C₁`-cofiniteness,
every renormalized series `(1 − x)^s · QT` lies in the `ℂ[x]`-module generated by those of the
tuples of bounded levels.  Same moves as `qt_mem`; the factor `(1 − x)^s` absorbs every pole at
`x = 1` (`X_mul_binom_mul_mem_pull`). -/
theorem pt_mem (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hUB : UnifBase A₂ A₃ Y₂ h₂ h₃ ν) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hD₄ : DualC1Graded A₄ h₄ B₄)
    (NN : Submodule (ratRing 0) (PowerSeries ℂ))
    (hbase : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN) :
    ∀ (s N₁ N₂ N₃ N₄ : ℕ), N₁ + N₂ + N₃ + N₄ = s →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        (1 - X) ^ s * QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ s ∈ NN := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
  intro N₁ N₂ N₃ N₄ hs f w₁ w₂ w₃ hw₁ hw₂ hw₃
  have IH' : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ + N₂ + N₃ + N₄ < s →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN :=
    fun N₁ N₂ N₃ N₄ hlt f w₁ w₂ w₃ h1 h2 h3 => IH _ hlt N₁ N₂ N₃ N₄ rfl f w₁ w₂ w₃ h1 h2 h3
  subst hs
  refine mem_pull.mp ?_
  by_cases c1 : B₁ < N₁
  · refine Submodule.span_induction
      (p := fun x _ => QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f x w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
        ∈ pull NN (N₁ + N₂ + N₃ + N₄))
      ?_ ?_ ?_ ?_ (hC₁ N₁ c1 w₁ hw₁)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₁ + N₂ + N₃ + N₄ = (N₁ - d) + d + N₂ + N₃ + N₄ by omega,
        moveA hY₁ hY₂ hl₂ hl₃ hl₄ hUB hu f hw' hw₂ hw₃]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · refine Submodule.sum_mem _ fun i hi => ?_
        simp only [Finset.mem_range] at hi
        exact X_pow_mul_mem_pull (IH' _ _ _ _ (by omega) _ _ _ _ hw' hw₂ hw₃) (by omega) _
      · refine Submodule.sum_mem _ fun i hi => ?_
        simp only [Finset.mem_range] at hi
        exact X_pow_mul_mem_pull
          (IH' _ _ _ _ (by omega) _ _ _ _ hw' hw₂ (mode_mem_weight_nat hu hw₃ hi)) (by omega) _
      · refine Submodule.sum_mem _ fun k hk => ?_
        simp only [Finset.mem_range] at hk
        exact X_mul_binom_mul_mem_pull
          (IH' _ _ _ _ (by omega) _ _ _ _ hw' (mode_mem_weight_nat hu hw₂ hk) hw₃) k (by omega)
    · simp only []; rw [QT_zero_w₁]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [QT_add_w₁]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; rw [QT_smul_w₁]; exact Submodule.smul_mem _ a hx
  by_cases c2 : B₂ < N₂
  · refine Submodule.span_induction
      (p := fun x _ => QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ x w₃ N₄ (N₁ + N₂ + N₃ + N₄)
        ∈ pull NN (N₁ + N₂ + N₃ + N₄))
      ?_ ?_ ?_ ?_ (hC₂ N₂ c2 w₂ hw₂)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₁ + N₂ + N₃ + N₄ = N₁ + (N₂ - d) + d + N₃ + N₄ by omega,
        moveB hY₁ hY₂ hl₁ hl₃ hl₄ hUB hu f hw₁ hw' hw₃]
      refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
      · refine Submodule.sum_mem _ fun i hi => ?_
        simp only [Finset.mem_range] at hi
        exact X_pow_mul_mem_pull (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw' hw₃) (by omega) _
      · refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
        simp only [Finset.mem_range] at hk
        exact X_mul_binom_mul_mem_pull
          (IH' _ _ _ _ (by omega) _ _ _ _ (mode_mem_weight_nat hu hw₁ hk) hw' hw₃) k (by omega)
      · refine Submodule.sum_mem _ fun i hi => ?_
        simp only [Finset.mem_range] at hi
        exact mem_pull_of_le
          (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw' (mode_mem_weight_nat hu hw₃ hi)) (by omega)
    · simp only []; rw [QT_zero_w₂]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [QT_add_w₂]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; rw [QT_smul_w₂]; exact Submodule.smul_mem _ a hx
  by_cases c3 : B₃ < N₃
  · refine Submodule.span_induction
      (p := fun x _ => QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ x N₄ (N₁ + N₂ + N₃ + N₄)
        ∈ pull NN (N₁ + N₂ + N₃ + N₄))
      ?_ ?_ ?_ ?_ (hC₃ N₃ c3 w₃ hw₃)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₁ + N₂ + N₃ + N₄ = N₁ + N₂ + (N₃ - d) + d + N₄ by omega,
        moveC hY₁ hY₂ hl₁ hl₂ hl₄ hUB hu f hw₁ hw₂ hw']
      refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
      · split_ifs with hd
        · exact X_pow_mul_mem_pull (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw₂ hw') (by omega) _
        · exact Submodule.zero_mem _
      · refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
        simp only [Finset.mem_range] at hk
        exact X_pow_mul_mem_pull
          (IH' _ _ _ _ (by omega) _ _ _ _ (mode_mem_weight_nat hu hw₁ hk) hw₂ hw') (by omega) _
      · refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
        simp only [Finset.mem_range] at hk
        exact mem_pull_of_le
          (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ (mode_mem_weight_nat hu hw₂ hk) hw') (by omega)
    · simp only []; rw [QT_zero_w₃]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [QT_add_w₃]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; rw [QT_smul_w₃]; exact Submodule.smul_mem _ a hx
  by_cases c4 : B₄ < N₄
  · refine Submodule.span_induction
      (p := fun φ _ => ∀ f' : M₄ →ₗ[ℂ] ℂ, f'.domRestrict (A₄.weight (h₄ + N₄)) = φ →
        QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f' w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
          ∈ pull NN (N₁ + N₂ + N₃ + N₄))
      ?_ ?_ ?_ ?_ (hD₄ N₄ c4 f) f rfl
    · rintro φ ⟨d, m, u, g, hd1, hm, hmN, hu, rfl⟩ f' hf'
      rw [QT_congr_f hY₁ hY₂ hw₁ hw₂ hw₃ hf']
      obtain ⟨r, rfl⟩ : ∃ r, N₄ = r + (m + 1 - d) := ⟨N₄ - (m + 1 - d), by omega⟩
      rw [show N₁ + N₂ + N₃ + (r + (m + 1 - d)) = N₁ + N₂ + N₃ + r + (m + 1 - d) by ring,
        moveD hY₁ hY₂ hl₁ hl₂ hl₃ hUB hm hu g hw₁ hw₂ hw₃]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · split_ifs with h3
        · have hm3 := mode_mem_weight A₃ hu hw₃ (m : ℤ)
          have e : h₃ + (N₃ : ℂ) + ((d : ℤ) : ℂ) - ((m : ℤ) : ℂ) - 1
              = h₃ + ((N₃ - (m + 1 - d) : ℕ) : ℂ) := by
            rw [Nat.cast_sub h3, Nat.cast_sub (by omega)]; push_cast; ring
          rw [e] at hm3
          exact X_pow_mul_mem_pull (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw₂ hm3) (by omega) _
        · exact Submodule.zero_mem _
      · refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
        simp only [Finset.mem_range] at hk
        exact X_pow_mul_mem_pull
          (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ (mode_mem_weight_nat hu hw₂ hk) hw₃) (by omega) _
      · refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
        simp only [Finset.mem_range] at hk
        exact X_pow_mul_mem_pull
          (IH' _ _ _ _ (by omega) _ _ _ _ (mode_mem_weight_nat hu hw₁ hk) hw₂ hw₃) (by omega) _
    · intro f' hf'
      rw [QT_congr_f hY₁ hY₂ hw₁ hw₂ hw₃ (f' := 0) (by rw [hf']; ext; simp), QT_zero_f]
      exact Submodule.zero_mem _
    · intro φ₁ φ₂ _ _ h1 h2 f' hf'
      obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend φ₁
      have hsplit : f' = g₁ + (f' - g₁) := by abel
      rw [hsplit, QT_add_f]
      refine Submodule.add_mem _ (h1 g₁ hg₁) (h2 _ ?_)
      ext x
      have hx := LinearMap.congr_fun hf' x
      have hx1 := LinearMap.congr_fun hg₁ x
      simp only [LinearMap.domRestrict_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, Submodule.subtype_apply] at hx hx1 ⊢
      rw [hx, hx1]; ring
    · intro a φ _ h1 f' hf'
      obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend φ
      rw [QT_congr_f hY₁ hY₂ hw₁ hw₂ hw₃ (f' := a • g₁) (by
        rw [hf']; ext x
        have hx1 := LinearMap.congr_fun hg₁ x
        simp only [LinearMap.domRestrict_apply, LinearMap.smul_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx1 ⊢
        rw [hx1]), QT_smul_f]
      exact Submodule.smul_mem _ a (h1 g₁ hg₁)
  exact hbase N₁ N₂ N₃ N₄ (by omega) (by omega) (by omega) (by omega) f w₁ w₂ w₃ hw₁ hw₂ hw₃

end Induction

/-- **The product equation at the iterate point, formally.**  For FHL intertwiners
`𝒴₁ : (W₄ / W₁ M₅)`, `𝒴₂ : (M₅ / W₂ W₃)` among lowest-weight modules with graded `C₁`-data,
homogeneous `w₁, w₂, w₃`, any functional `f`, any weight `h₄'` and a base `ν₀` of the coset: with
`H = (1 − x)^b x^K G` (`G` the coset series of the product in `x = z₂/z₁`), for **every** `κ, σ`
the `DOp κ σ`-iterates of `H` satisfy a monic relation with coefficients in `ℂ[x]`.  (At `z₂ = 1`,
`x = (1 + u)⁻¹`, `u = z₁ − z₂`: polynomials in `x` are holomorphic at `u = 0` — Huang's Thm 2.3
at `z₂⁻¹(z₁ − z₂) = 0`.) -/
theorem exists_dop_relation_prodSeries {h₁ h₂ h₃ h₄ : ℂ} {B₁ B₂ B₃ B₄ : ℕ}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂)
    (hl₁ : IsLowestWeight A₁ h₁) (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃)
    (hl₄ : IsLowestWeight A₄ h₄) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hD₄ : DualC1Graded A₄ h₄ B₄)
    {α₁ α₂ α₃ h₄' : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} (f : M₄ →ₗ[ℂ] ℂ)
    (hw₁ : w₁ ∈ A₁.weight α₁) (hw₂ : w₂ ∈ A₂.weight α₂) (hw₃ : w₃ ∈ A₃.weight α₃)
    {ν₀ : ℂ} (hb : IsBase Y₂ w₂ w₃ ν₀) :
    ∃ b K : ℕ, ∀ κ σ : ℂ, ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ k, r k ∈ ratRing 0) ∧
      (DOp κ σ)^[m] ((1 - X) ^ b *
          (X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄' - 2) ν₀))
        = ∑ k ∈ Finset.range m, r k * (DOp κ σ)^[k] ((1 - X) ^ b *
          (X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄' - 2) ν₀)) := by
  classical
  have triv : prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄' - 2) ν₀ = 0 →
      ∃ b K : ℕ, ∀ κ σ : ℂ, ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ k, r k ∈ ratRing 0) ∧
        (DOp κ σ)^[m] ((1 - X) ^ b *
            (X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄' - 2) ν₀))
          = ∑ k ∈ Finset.range m, r k * (DOp κ σ)^[k] ((1 - X) ^ b *
            (X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄' - 2) ν₀)) := by
    intro h0
    refine ⟨0, 0, fun κ σ => ⟨0, fun _ => 0, fun _ => Subalgebra.zero_mem _, ?_⟩⟩
    simp [h0]
  by_cases z₁ : A₁.weight α₁ = ⊥
  · have : w₁ = 0 := by rw [z₁] at hw₁; exact (Submodule.mem_bot ℂ).mp hw₁
    subst this
    exact triv (by ext k; simp [coeff_prodSeries, prodCoeff])
  by_cases z₂ : A₂.weight α₂ = ⊥
  · have : w₂ = 0 := by rw [z₂] at hw₂; exact (Submodule.mem_bot ℂ).mp hw₂
    subst this
    exact triv (by ext k; simp [coeff_prodSeries, prodCoeff])
  by_cases z₃ : A₃.weight α₃ = ⊥
  · have : w₃ = 0 := by rw [z₃] at hw₃; exact (Submodule.mem_bot ℂ).mp hw₃
    subst this
    exact triv (by ext k; simp [coeff_prodSeries, prodCoeff])
  by_cases z₄ : A₄.weight h₄' = ⊥
  · refine triv ?_
    ext k
    rw [coeff_prodSeries, prodCoeff, map_zero]
    have hx := prod_mem_weight hY₁ hY₂ hw₁ hw₂ hw₃
      (α₁ + α₂ + α₃ - h₄' - 2 - ν₀ + k) (ν₀ - k)
    have e : α₁ + α₂ + α₃ - (α₁ + α₂ + α₃ - h₄' - 2 - ν₀ + k) - (ν₀ - k) - 2 = h₄' := by ring
    rw [e, z₄] at hx
    rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
  obtain ⟨N₁, rfl⟩ := hl₁ α₁ z₁
  obtain ⟨N₂, rfl⟩ := hl₂ α₂ z₂
  obtain ⟨N₃, rfl⟩ := hl₃ α₃ z₃
  obtain ⟨N₄, rfl⟩ := hl₄ h₄' z₄
  obtain ⟨K, hUB⟩ := exists_unifBase hY₂ h₂ h₃ ν₀ (N₁ + N₂ + N₃ + N₄)
  set ν := ν₀ - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) + K with hν
  choose T hTfin hT using fun q : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) =>
    exists_finite_span (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) (ν := ν) hY₁ hY₂
      q.1 q.2.1 q.2.2.1 q.2.2.2
  set T' : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) → Set (PowerSeries ℂ) :=
    fun q => (LinearMap.mulLeft ℂ (((1 : PowerSeries ℂ) - X) ^
      ((q.1 : ℕ) + (q.2.1 : ℕ) + (q.2.2.1 : ℕ) + (q.2.2.2 : ℕ)))) '' T q with hT'
  have hT'fin : ∀ q, (T' q).Finite := fun q => (hTfin q).image _
  set NN : Submodule (ratRing 0) (PowerSeries ℂ) := Submodule.span (ratRing 0) (⋃ q, T' q)
  have hFG : NN.FG := Submodule.fg_span (Set.finite_iUnion hT'fin)
  have hbase : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
          QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN := by
    intro N₁ N₂ N₃ N₄ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃
    set q : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) :=
      (⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩, ⟨N₄, by omega⟩) with hq
    have hmem := hT q f w₁ w₂ w₃ hw₁ hw₂ hw₃
    have hmem' : (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
        QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
          ∈ Submodule.span ℂ (T' q) := by
      rw [hT', Submodule.span_image]
      exact Submodule.mem_map_of_mem hmem
    have hle : Submodule.span ℂ (T' q) ≤ NN.restrictScalars ℂ :=
      (Submodule.span_mono (Set.subset_iUnion T' _)).trans
        (Submodule.span_le_restrictScalars ℂ (ratRing 0) _)
    exact hle hmem'
  have hall := pt_mem hY₁ hY₂ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄ NN hbase
  refine ⟨N₁ + N₂ + N₃ + N₄, K, fun κ σ => ?_⟩
  set A : ℕ → PowerSeries ℂ := fun j =>
    QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ ((⇑A₂.Lm1)^[j] w₂) w₃ N₄
      (N₁ + N₂ + N₃ + N₄ + j) with hAdef
  have hAmem : ∀ j, (1 - X) ^ (N₁ + N₂ + N₃ + N₄ + j) * A j ∈ NN := fun j =>
    hall _ N₁ (N₂ + j) N₃ N₄ (by omega) f w₁ _ w₃ hw₁ (Lm1_iterate_mem_weight hw₂ j) hw₃
  have hA : ∀ j, VOA.theta (A j)
      = A (j + 1) + PowerSeries.C (ν + ((N₁ + N₂ + N₃ + N₄ + j : ℕ) : ℂ) + 1) * A j := by
    intro j
    simp only [hAdef]
    rw [Function.iterate_succ_apply', show N₁ + N₂ + N₃ + N₄ + (j + 1)
      = N₁ + N₂ + N₃ + N₄ + j + 1 from rfl, QT_Lm1 hY₂]
    ext n
    rw [theta_coeff, map_add, coeff_thetaShift, coeff_C_mul]
    ring
  have hit := dop_iterate_mem NN κ σ (N₁ + N₂ + N₃ + N₄) A _ hA hAmem
  have hA0 : A 0 = X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃
      ((h₁ + N₁) + (h₂ + N₂) + (h₃ + N₃) - (h₄ + N₄) - 2) ν₀ := by
    simp only [hAdef, Function.iterate_zero, id, add_zero]
    exact QT_eq_X_pow_mul_prodSeries hb
  have hH : ∀ i, (DOp κ σ)^[i] ((1 - X) ^ (N₁ + N₂ + N₃ + N₄) * (X ^ K * prodSeries Y₁ Y₂ f w₁ w₂
      w₃ ((h₁ + N₁) + (h₂ + N₂) + (h₃ + N₃) - (h₄ + N₄) - 2) ν₀)) ∈ NN := by
    intro i
    have := hit i 0 0
    rwa [pow_zero, one_mul, add_zero, hA0] at this
  exact exists_dop_relation NN hFG (DOp κ σ) hH

end Product

end VOA.Huang.HuangODEIterPoint
