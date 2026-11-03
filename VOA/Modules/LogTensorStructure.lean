/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorIntertwining
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Structure of logarithmic intertwining operators: log coefficients, weights, log degree — T1

Consequences of the `L(0)`-bracket formula `IsLogIntertwining.L0_bracket`
(Huang–Lepowsky–Zhang II §3), for logarithmic intertwining operators among **weak** modules.
Write `D₁ = L₀ − α₁` on `W₁`, `D₂ = L₀ − α₂` on `W₂`, `D₃ = L₀ − μ` on `W₃` with
`μ = α₁ + α₂ − n − 1`.  Then (`shifted_bracket`)

  `D₃ (w₁)_{n;k} w₂ = (D₁w₁)_{n;k} w₂ + (w₁)_{n;k} D₂w₂ + (k+1) (w₁)_{n;k+1} w₂`.

## Main results
* `eq_zero_of_log_eq_zero` — if the `k₀`-th log coefficient `Y_{n;k₀}` vanishes identically,
  so do all `Y_{n;k}`, `k ≥ k₀`.  With `k₀ = 0`: **a logarithmic intertwining operator is
  determined by its log-free part** (`logZero`, `logZero_injective`).  With `k₀ = 1`: an
  operator with `Y_{·;1} = 0` has no logarithms at all.
* `mem_maxGenEigenspace` — the **generalized weight-shift law**: if `w₁` (resp. `w₂`) is a
  generalized `L₀`-eigenvector of eigenvalue `α₁` (resp. `α₂`), then every `(w₁)_{n;k} w₂` is a
  generalized `L₀`-eigenvector of eigenvalue `α₁ + α₂ − n − 1`.  (Pointwise induction; no
  finiteness of any kind is used.)
* `log_degree_bound` — the **logarithmic degree is bounded by the Jordan block sizes**:
  if `D₁ᵖ w₁ = 0`, `D₂^q w₂ = 0`, and `D₃ʳ` kills the generalized `μ`-eigenspace of `W₃`, then
  `(w₁)_{n;k} w₂ = 0` for `k ≥ p + q + r − 2`.  In particular, among modules on which `L₀` is
  semisimple (`p = q = r = 1`), every logarithmic intertwining operator is log-free.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.LogTensor

open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}

/-- The shifted `L₀`: `L₀ − α`. -/
abbrev L0s {M : Type*} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (α : ℂ) : End ℂ M :=
  L0 A - α • (1 : End ℂ M)

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

/-- The `L(0)`-bracket formula with eigenvalue shifts:
`D₃ (w₁)_{n;k} w₂ = (D₁w₁)_{n;k} w₂ + (w₁)_{n;k} D₂w₂ + (k+1)(w₁)_{n;k+1} w₂`,
`D₃ = L₀ − (α₁+α₂−n−1)`, `D₁ = L₀ − α₁`, `D₂ = L₀ − α₂`. -/
theorem shifted_bracket (hY : IsLogIntertwining A₁ A₂ A₃ Y) (α₁ α₂ : ℂ)
    (w₁ : M₁) (w₂ : M₂) (n : ℂ) (k : ℕ) :
    L0s A₃ (α₁ + α₂ - n - 1) (Y n k w₁ w₂)
      = Y n k (L0s A₁ α₁ w₁) w₂ + Y n k w₁ (L0s A₂ α₂ w₂)
        + ((k : ℂ) + 1) • Y n (k + 1) w₁ w₂ := by
  have h := hY.L0_bracket w₁ w₂ n k
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
    map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [sub_eq_iff_eq_add] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  simp only [sub_smul, add_smul]
  abel_nf
  simp only [neg_smul, one_smul]
  abel

/-- **Vanishing propagates up the log degree**: if `Y_{n;k₀} ≡ 0` then `Y_{n;k} ≡ 0` for every
`k ≥ k₀` (by `(k+1) Y_{n;k+1} = D₃Y_{n;k} − Y_{n;k}(D₁·,·) − Y_{n;k}(·,D₂·)`). -/
theorem eq_zero_of_log_eq_zero (hY : IsLogIntertwining A₁ A₂ A₃ Y) (n : ℂ) (k₀ : ℕ)
    (h : ∀ (w₁ : M₁) (w₂ : M₂), Y n k₀ w₁ w₂ = 0) :
    ∀ k : ℕ, k₀ ≤ k → ∀ (w₁ : M₁) (w₂ : M₂), Y n k w₁ w₂ = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    intro w₁ w₂
    have hb := hY.shifted_bracket 0 0 w₁ w₂ n k
    rw [ih, ih, ih, map_zero, zero_add, zero_add] at hb
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (smul_eq_zero.mp hb.symm).resolve_left hk

end IsLogIntertwining

/-- The **log-free part** `Y ↦ (n ↦ Y_{n;0})` of a logarithmic intertwining operator, as a linear
map. -/
noncomputable def logZero (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂) (A₃ : WeakModule W M₃) :
    LogIntertwiningOperator A₁ A₂ A₃ →ₗ[ℂ] (ℂ → M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) where
  toFun Y n := (Y : LogModes M₁ M₂ M₃) n 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A logarithmic intertwining operator is determined by its log-free part.** -/
theorem logZero_injective : Function.Injective (logZero A₁ A₂ A₃) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  apply Subtype.ext
  funext n k
  apply LinearMap.ext; intro w₁; apply LinearMap.ext; intro w₂
  have h0 : ∀ (w₁ : M₁) (w₂ : M₂), (Y : LogModes M₁ M₂ M₃) n 0 w₁ w₂ = 0 := fun w₁ w₂ => by
    have := congrFun hY n
    change (Y : LogModes M₁ M₂ M₃) n 0 = 0 at this
    rw [this]; rfl
  exact Y.2.eq_zero_of_log_eq_zero n 0 h0 k (Nat.zero_le k) w₁ w₂

/-- Finite-dimensionality of the space of logarithmic intertwining operators follows from that
of the image of the log-free part. -/
theorem finiteDimensional_of_logZero_range
    [FiniteDimensional ℂ (LinearMap.range (logZero A₁ A₂ A₃))] :
    FiniteDimensional ℂ (LogIntertwiningOperator A₁ A₂ A₃) :=
  Module.Finite.of_injective
    ((logZero A₁ A₂ A₃).rangeRestrict)
    (by
      intro x y h
      exact logZero_injective (congrArg Subtype.val h))

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

/-- The pointwise engine of the weight-shift law. -/
theorem pow_shifted_eq_zero (hY : IsLogIntertwining A₁ A₂ A₃ Y) (n α₁ α₂ : ℂ) (R : ℕ) :
    ∀ (s p q k : ℕ) (w₁ : M₁) (w₂ : M₂),
      (∀ i < p, ∀ i' < q, ∀ j : ℕ, R ≤ j →
        Y n j ((L0s A₁ α₁ ^ i) w₁) ((L0s A₂ α₂ ^ i') w₂) = 0) →
      (L0s A₁ α₁ ^ p) w₁ = 0 → (L0s A₂ α₂ ^ q) w₂ = 0 → p + q + R ≤ s + k →
      (L0s A₃ (α₁ + α₂ - n - 1) ^ s) (Y n k w₁ w₂) = 0 := by
  intro s
  induction s with
  | zero =>
    intro p q k w₁ w₂ hR hp hq hle
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [pow_zero, Module.End.one_apply] at hp; simp [hp]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [pow_zero, Module.End.one_apply] at hq; simp [hq]
    have := hR 0 hp0 0 hq0 k (by omega)
    simp only [pow_zero, Module.End.one_apply] at this
    simp [this]
  | succ s ih =>
    intro p q k w₁ w₂ hR hp hq hle
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [pow_zero, Module.End.one_apply] at hp; simp [hp]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [pow_zero, Module.End.one_apply] at hq; simp [hq]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply, hY.shifted_bracket α₁ α₂ w₁ w₂ n k, map_add, map_add,
      map_smul]
    have e1 : (L0s A₃ (α₁ + α₂ - n - 1) ^ s) (Y n k (L0s A₁ α₁ w₁) w₂) = 0 := by
      refine ih p' (q' + 1) k _ w₂ (fun i hi i' hi' j hj => ?_) ?_ hq (by omega)
      · rw [← Module.End.mul_apply, ← pow_succ]
        exact hR (i + 1) (by omega) i' hi' j hj
      · rw [← Module.End.mul_apply, ← pow_succ]; exact hp
    have e2 : (L0s A₃ (α₁ + α₂ - n - 1) ^ s) (Y n k w₁ (L0s A₂ α₂ w₂)) = 0 := by
      refine ih (p' + 1) q' k w₁ _ (fun i hi i' hi' j hj => ?_) hp ?_ (by omega)
      · rw [← Module.End.mul_apply, ← pow_succ]
        exact hR i hi (i' + 1) (by omega) j hj
      · rw [← Module.End.mul_apply, ← pow_succ]; exact hq
    have e3 : (L0s A₃ (α₁ + α₂ - n - 1) ^ s) (Y n (k + 1) w₁ w₂) = 0 :=
      ih (p' + 1) (q' + 1) (k + 1) w₁ w₂ hR hp hq (by omega)
    rw [e1, e2, e3, smul_zero, add_zero, add_zero]

/-- **Generalized weight-shift law** (HLZ II §3): for generalized `L₀`-eigenvectors
`w₁ ∈ W₁_[α₁]`, `w₂ ∈ W₂_[α₂]`, every coefficient `(w₁)_{n;k} w₂` lies in the generalized
eigenspace `W₃_[α₁+α₂−n−1]`.  Valid for arbitrary weak modules. -/
theorem mem_maxGenEigenspace (hY : IsLogIntertwining A₁ A₂ A₃ Y) {α₁ α₂ : ℂ} {w₁ : M₁}
    {w₂ : M₂} (h₁ : w₁ ∈ (L0 A₁).maxGenEigenspace α₁) (h₂ : w₂ ∈ (L0 A₂).maxGenEigenspace α₂)
    (n : ℂ) (k : ℕ) :
    Y n k w₁ w₂ ∈ (L0 A₃).maxGenEigenspace (α₁ + α₂ - n - 1) := by
  classical
  obtain ⟨p, hp⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp h₁
  obtain ⟨q, hq⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp h₂
  have hK : ∀ ii : ℕ × ℕ, ∃ K : ℕ, ∀ j : ℕ, K ≤ j →
      Y n j ((L0s A₁ α₁ ^ ii.1) w₁) ((L0s A₂ α₂ ^ ii.2) w₂) = 0 :=
    fun ii => hY.logFinite _ _ n
  choose K hK using hK
  set R : ℕ := (Finset.range p ×ˢ Finset.range q).sup K
  have hR : ∀ i < p, ∀ i' < q, ∀ j : ℕ, R ≤ j →
      Y n j ((L0s A₁ α₁ ^ i) w₁) ((L0s A₂ α₂ ^ i') w₂) = 0 := by
    intro i hi i' hi' j hj
    have hle : K (i, i') ≤ R :=
      Finset.le_sup (f := K) (Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hi'⟩)
    exact hK (i, i') j (le_trans hle hj)
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨p + q + R, hY.pow_shifted_eq_zero n α₁ α₂ R (p + q + R) p q k w₁ w₂ hR hp hq
    (by omega)⟩

/-- The pointwise engine of the log-degree bound. -/
theorem log_vanish (hY : IsLogIntertwining A₁ A₂ A₃ Y) (n α₁ α₂ : ℂ) (r : ℕ)
    (hr : ∀ y ∈ (L0 A₃).maxGenEigenspace (α₁ + α₂ - n - 1),
      (L0s A₃ (α₁ + α₂ - n - 1) ^ r) y = 0) :
    ∀ (k t p q : ℕ) (w₁ : M₁) (w₂ : M₂),
      (L0s A₁ α₁ ^ p) w₁ = 0 → (L0s A₂ α₂ ^ q) w₂ = 0 → r + p + q ≤ t + k + 2 →
      (L0s A₃ (α₁ + α₂ - n - 1) ^ t) (Y n k w₁ w₂) = 0 := by
  intro k
  induction k with
  | zero =>
    intro t p q w₁ w₂ hp hq hle
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [pow_zero, Module.End.one_apply] at hp; simp [hp]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [pow_zero, Module.End.one_apply] at hq; simp [hq]
    have hm := hY.mem_maxGenEigenspace
      ((Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨p, hp⟩)
      ((Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨q, hq⟩) n 0
    rw [show t = (t - r) + r by omega, pow_add, Module.End.mul_apply, hr _ hm, map_zero]
  | succ k ih =>
    intro t p q w₁ w₂ hp hq hle
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [pow_zero, Module.End.one_apply] at hp; simp [hp]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [pow_zero, Module.End.one_apply] at hq; simp [hq]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hb := hY.shifted_bracket α₁ α₂ w₁ w₂ n k
    have hsmul : ((k : ℂ) + 1) • Y n (k + 1) w₁ w₂
        = L0s A₃ (α₁ + α₂ - n - 1) (Y n k w₁ w₂)
          - Y n k (L0s A₁ α₁ w₁) w₂ - Y n k w₁ (L0s A₂ α₂ w₂) := by
      rw [hb]; abel
    have e0 : (L0s A₃ (α₁ + α₂ - n - 1) ^ t) (L0s A₃ (α₁ + α₂ - n - 1) (Y n k w₁ w₂)) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ]
      exact ih (t + 1) (p' + 1) (q' + 1) w₁ w₂ hp hq (by omega)
    have e1 : (L0s A₃ (α₁ + α₂ - n - 1) ^ t) (Y n k (L0s A₁ α₁ w₁) w₂) = 0 :=
      ih t p' (q' + 1) _ w₂ (by rw [← Module.End.mul_apply, ← pow_succ]; exact hp) hq
        (by omega)
    have e2 : (L0s A₃ (α₁ + α₂ - n - 1) ^ t) (Y n k w₁ (L0s A₂ α₂ w₂)) = 0 :=
      ih t (p' + 1) q' w₁ _ hp (by rw [← Module.End.mul_apply, ← pow_succ]; exact hq)
        (by omega)
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have : ((k : ℂ) + 1) • (L0s A₃ (α₁ + α₂ - n - 1) ^ t) (Y n (k + 1) w₁ w₂) = 0 := by
      rw [← map_smul, hsmul, map_sub, map_sub, e0, e1, e2, sub_zero, sub_zero]
    exact (smul_eq_zero.mp this).resolve_left hk

/-- **The logarithmic degree is bounded by the Jordan block sizes** (HLZ II §3): if
`(L₀ − α₁)ᵖ w₁ = 0`, `(L₀ − α₂)^q w₂ = 0` and `(L₀ − μ)ʳ` vanishes on the generalized
`μ`-eigenspace of `W₃` (`μ = α₁ + α₂ − n − 1`), then `(w₁)_{n;k} w₂ = 0` whenever
`k + 2 ≥ p + q + r`. -/
theorem log_degree_bound (hY : IsLogIntertwining A₁ A₂ A₃ Y) {n α₁ α₂ : ℂ} {r p q k : ℕ}
    (hr : ∀ y ∈ (L0 A₃).maxGenEigenspace (α₁ + α₂ - n - 1),
      (L0s A₃ (α₁ + α₂ - n - 1) ^ r) y = 0)
    {w₁ : M₁} {w₂ : M₂} (hp : (L0s A₁ α₁ ^ p) w₁ = 0) (hq : (L0s A₂ α₂ ^ q) w₂ = 0)
    (hk : p + q + r ≤ k + 2) :
    Y n k w₁ w₂ = 0 := by
  have := hY.log_vanish n α₁ α₂ r hr k 0 p q w₁ w₂ hp hq (by omega)
  simpa using this

/-- **No logarithms among `L₀`-eigenvectors into an `L₀`-semisimple target**: if `w₁, w₂` are honest
`L₀`-eigenvectors and `L₀` is semisimple on the generalized `μ`-eigenspace of `W₃`, then
`(w₁)_{n;k} w₂ = 0` for every `k ≥ 1`. -/
theorem log_eq_zero_of_eigen (hY : IsLogIntertwining A₁ A₂ A₃ Y) {n α₁ α₂ : ℂ}
    (hss : ∀ y ∈ (L0 A₃).maxGenEigenspace (α₁ + α₂ - n - 1),
      L0 A₃ y = (α₁ + α₂ - n - 1) • y)
    {w₁ : M₁} {w₂ : M₂} (h₁ : L0 A₁ w₁ = α₁ • w₁) (h₂ : L0 A₂ w₂ = α₂ • w₂)
    {k : ℕ} (hk : 1 ≤ k) :
    Y n k w₁ w₂ = 0 :=
  hY.log_degree_bound (α₁ := α₁) (α₂ := α₂) (r := 1) (p := 1) (q := 1)
    (fun y hy => by
      rw [pow_one, LinearMap.sub_apply, hss y hy, LinearMap.smul_apply, Module.End.one_apply,
        sub_self])
    (by rw [pow_one, LinearMap.sub_apply, h₁, LinearMap.smul_apply, Module.End.one_apply,
        sub_self])
    (by rw [pow_one, LinearMap.sub_apply, h₂, LinearMap.smul_apply, Module.End.one_apply,
        sub_self])
    (by omega)

end IsLogIntertwining

end VOA.LogTensor
