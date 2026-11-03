/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.Intertwining
import VOA.Modules.C2RigidGraded
import VOA.Core.FLM

/-!
# Logarithmic intertwining operators (Huang–Lepowsky–Zhang II, Def. 3.10) — stage T1

For weak `V`-modules `W₁, W₂, W₃`, a **logarithmic intertwining operator of type `(W₃ / W₁ W₂)`**
is a linear map `𝒴 : W₁ ⊗ W₂ → W₃[log x]{x}`,

  `𝒴(w₁, x) w₂ = ∑_{n ∈ ℂ} ∑_{k ∈ ℕ} (w₁)_{n;k} w₂ x^{-n-1} (log x)^k`,

such that

1. **lower truncation** (HLZ II (3.18)): for all `w₁, w₂, n`, `(w₁)_{n+m;k} w₂ = 0` for `m ∈ ℕ`
   sufficiently large, *independently of `k`*;
2. the **Jacobi identity** (HLZ II (3.19))
   `x₀⁻¹δ((x₁-x₂)/x₀) Y₃(v,x₁)𝒴(w₁,x₂)w₂ − x₀⁻¹δ((x₂-x₁)/(-x₀)) 𝒴(w₁,x₂)Y₂(v,x₁)w₂`
   `= x₂⁻¹δ((x₁-x₀)/x₂) 𝒴(Y₁(v,x₀)w₁, x₂)w₂`;
3. the **`L(−1)`-derivative property** (HLZ II (3.20)): `𝒴(L(−1)w₁, x) = d/dx 𝒴(w₁, x)`.

## Encoding (and why it is faithful)

* **Modes.** `LogModes W₁ W₂ W₃ := ℂ → ℕ → (W₁ →ₗ W₂ →ₗ W₃)` with
  `Y n k w₁ w₂ = (w₁)_{n;k} w₂`, the coefficient of `x^{-n-1} (log x)^k`.
* **Target space `W₃[log x]{x}`.**  The coefficient of each `x^{-n-1}` is a *polynomial* in
  `log x`: for fixed `(w₁, w₂, n)` only finitely many `k` give a nonzero coefficient
  (`logFinite`).  This is part of the codomain in HLZ, so it is a field here.
* **Truncation** is HLZ's, uniform in `k` (`∃ N, ∀ m ≥ N, ∀ k, …`).
* **`L(−1)`-derivative.**  `d/dx (x^{-n-1}(log x)^k) = (-n-1) x^{-n-2}(log x)^k + k x^{-n-2}(log x)^{k-1}`,
  so the coefficient of `x^{-n-1}(log x)^k` of `d/dx 𝒴(w₁,x)` is
  `−n (w₁)_{n-1;k} + (k+1)(w₁)_{n-1;k+1}`.  Hence
  `(L(−1)w₁)_{n;k} = −n (w₁)_{n−1;k} + (k+1) (w₁)_{n−1;k+1}`, with `L(−1) = ω₍₀₎` on `W₁`.
* **Jacobi.**  The delta functions involve only integral powers of `x₀, x₁, x₂` and no `log`;
  so the coefficient of `(log x₂)^k` of (3.19) is the non-logarithmic Jacobi identity for the
  `k`-th component.  In modes (coefficient of `x₀^{-ℓ-1} x₁^{-m-1} x₂^{-n-1} (log x₂)^k`) this is
  exactly the form used in `VOA/Huang/Intertwining.lean` (FHL), at each `k`.

The definition is stated for **weak modules** (HLZ use generalized modules; only the vertex
operators enter the axioms).  It specializes to `GWModule`s (`GWLogIntertwiningOperator`), to
`LogVModule`s and to `OrdVModule`s through their `toWeakModule`.

## Main declarations
* `LogModes`, `Lm1`, `L0`.
* `IsLogIntertwining A₁ A₂ A₃ Y` — HLZ II Def. 3.10.
* `logIntertwiningSpace A₁ A₂ A₃ : Submodule ℂ (LogModes M₁ M₂ M₃)`, its carrier
  `LogIntertwiningOperator A₁ A₂ A₃`; the `GWModule` version `GWLogIntertwiningOperator`.
* `IsLogIntertwining.commutator` — the commutator formula (Jacobi at `ℓ = 0`), per `k`.
* `IsLogIntertwining.L0_bracket` — the **`L(0)`-bracket formula**
  `L₀ (w₁)_{n;k} w₂ − (L₀w₁)_{n;k} w₂ − (w₁)_{n;k} L₀w₂ = (−n−1)(w₁)_{n;k}w₂ + (k+1)(w₁)_{n;k+1}w₂`,
  the source of all logarithmic structure (HLZ II §3, the `L(0)`-conjugation property in modes).

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

/-- The **mode data** of a would-be logarithmic intertwining operator
`𝒴(·,x) : W₁ → Hom(W₂,W₃)[log x]{x}`: `Y n k w₁ w₂ = (w₁)_{n;k} w₂`, the coefficient of
`x^{-n-1} (log x)^k` (HLZ II (3.17)). -/
abbrev LogModes (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] :=
  ℂ → ℕ → (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃)

/-- `L(−1) = ω₍₀₎` on a weak module. -/
abbrev Lm1 {M : Type*} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) : End ℂ M :=
  mode (A.YM W.conformalVector) 0

/-- `L(0) = ω₍₁₎` on a weak module. -/
abbrev L0 {M : Type*} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) : End ℂ M :=
  mode (A.YM W.conformalVector) 1

/-- **Logarithmic intertwining operator of type `(W₃ / W₁ W₂)`** (Huang–Lepowsky–Zhang II,
Def. 3.10), on mode data `Y n k w₁ w₂ = (w₁)_{n;k} w₂`.  See the module docstring for the
coefficient extraction. -/
structure IsLogIntertwining (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) (Y : LogModes M₁ M₂ M₃) : Prop where
  /-- The codomain is `W₃[log x]{x}`: each coefficient of `x^{-n-1}` is a polynomial in `log x`. -/
  logFinite : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Y n k w₁ w₂ = 0
  /-- **Lower truncation** (HLZ II (3.18)), uniform in `k`. -/
  truncation : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ m : ℤ, N ≤ m → ∀ k : ℕ,
    Y (n + m) k w₁ w₂ = 0
  /-- **`L(−1)`-derivative** (HLZ II (3.20)):
  `(L(−1)w₁)_{n;k} = −n (w₁)_{n−1;k} + (k+1)(w₁)_{n−1;k+1}`. -/
  L_neg_one : ∀ (w₁ : M₁) (n : ℂ) (k : ℕ),
    Y n k (Lm1 A₁ w₁) = (-n) • Y (n - 1) k w₁ + ((k : ℂ) + 1) • Y (n - 1) (k + 1) w₁
  /-- **Jacobi identity** (HLZ II (3.19)), coefficient of
  `x₀^{-ℓ-1} x₁^{-m-1} x₂^{-n-1} (log x₂)^k`. -/
  jacobi : ∀ (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ) (k : ℕ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) k w₁ w₂)
          - negOnePow ℓ • Y (ℓ + n - i) k w₁ (mode (A₂.YM u) (m + i) w₂)))
      = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) k (mode (A₁.YM u) (ℓ + i) w₁) w₂

namespace IsLogIntertwining

variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}

/-- The left summand of the Jacobi identity (at log degree `k`). -/
noncomputable def jacL (A₂ : WeakModule W M₂) (A₃ : WeakModule W M₃)
    (Y : LogModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ) (k : ℕ) (i : ℤ) :
    M₃ :=
  (negOnePow i * cbz ℓ i) •
    (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) k w₁ w₂)
      - negOnePow ℓ • Y (ℓ + n - i) k w₁ (mode (A₂.YM u) (m + i) w₂))

/-- The right summand of the Jacobi identity (at log degree `k`). -/
noncomputable def jacR (A₁ : WeakModule W M₁) (Y : LogModes M₁ M₂ M₃) (u : 𝒱)
    (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ) (k : ℕ) (i : ℤ) : M₃ :=
  cbz m i • Y (m + n - i) k (mode (A₁.YM u) (ℓ + i) w₁) w₂

theorem jacL_add (Y₁ Y₂ : LogModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (k : ℕ) (i : ℤ) :
    jacL A₂ A₃ (Y₁ + Y₂) u w₁ w₂ ℓ m n k i
      = jacL A₂ A₃ Y₁ u w₁ w₂ ℓ m n k i + jacL A₂ A₃ Y₂ u w₁ w₂ ℓ m n k i := by
  simp only [jacL, Pi.add_apply, LinearMap.add_apply, map_add]
  module

theorem jacR_add (Y₁ Y₂ : LogModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (k : ℕ) (i : ℤ) :
    jacR A₁ (Y₁ + Y₂) u w₁ w₂ ℓ m n k i
      = jacR A₁ Y₁ u w₁ w₂ ℓ m n k i + jacR A₁ Y₂ u w₁ w₂ ℓ m n k i := by
  simp only [jacR, Pi.add_apply, LinearMap.add_apply, smul_add]

theorem jacL_smul (c : ℂ) (Y : LogModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (k : ℕ) (i : ℤ) :
    jacL A₂ A₃ (c • Y) u w₁ w₂ ℓ m n k i = c • jacL A₂ A₃ Y u w₁ w₂ ℓ m n k i := by
  simp only [jacL, Pi.smul_apply, LinearMap.smul_apply, map_smul]
  module

theorem jacR_smul (c : ℂ) (Y : LogModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (k : ℕ) (i : ℤ) :
    jacR A₁ (c • Y) u w₁ w₂ ℓ m n k i = c • jacR A₁ Y u w₁ w₂ ℓ m n k i := by
  simp only [jacR, Pi.smul_apply, LinearMap.smul_apply]
  rw [smul_comm]

/-- Finite support of the left Jacobi summand. -/
theorem jacL_support_finite {Y : LogModes M₁ M₂ M₃}
    (htr : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ m : ℤ, N ≤ m → ∀ k : ℕ,
      Y (n + m) k w₁ w₂ = 0)
    (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ) (k : ℕ) :
    (Function.support (jacL A₂ A₃ Y u w₁ w₂ ℓ m n k)).Finite := by
  obtain ⟨N₁, hN₁⟩ := htr w₁ w₂ n
  obtain ⟨N₂, hN₂⟩ := A₂.truncation u w₂
  refine (Set.finite_Ico (0 : ℤ) (max N₁ (N₂ - m))).subset (fun i hi => ?_)
  simp only [Function.mem_support] at hi
  simp only [Set.mem_Ico]
  by_contra hcon
  apply hi
  rcases lt_or_ge i 0 with hneg | hnn
  · simp [jacL, cbz_apply_neg ℓ hneg]
  · have hge : max N₁ (N₂ - m) ≤ i := by
      by_contra h; exact hcon ⟨hnn, not_le.mp h⟩
    have h1 : Y (n + i) k w₁ w₂ = 0 := hN₁ i (le_trans (le_max_left _ _) hge) k
    have h2 : mode (A₂.YM u) (m + i) w₂ = 0 :=
      hN₂ (m + i) (by have := le_trans (le_max_right _ _) hge; omega)
    simp only [jacL, h1, h2, map_zero, smul_zero, sub_zero]

/-- Finite support of the right Jacobi summand. -/
theorem jacR_support_finite (Y : LogModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (k : ℕ) :
    (Function.support (jacR A₁ Y u w₁ w₂ ℓ m n k)).Finite := by
  obtain ⟨N, hN⟩ := A₁.truncation u w₁
  refine (Set.finite_Ico (0 : ℤ) (N - ℓ)).subset (fun i hi => ?_)
  simp only [Function.mem_support] at hi
  simp only [Set.mem_Ico]
  by_contra hcon
  apply hi
  rcases lt_or_ge i 0 with hneg | hnn
  · simp [jacR, cbz_apply_neg m hneg]
  · have h : mode (A₁.YM u) (ℓ + i) w₁ = 0 := hN (ℓ + i) (by
      by_contra h; exact hcon ⟨hnn, by omega⟩)
    simp only [jacR, h, map_zero, LinearMap.zero_apply, smul_zero]

/-- The **commutator formula** (Jacobi at `ℓ = 0`), at every log degree `k`:
`u₍ₘ₎ (w₁)_{n;k} w₂ − (w₁)_{n;k} u₍ₘ₎ w₂ = ∑ᵢ C(m,i) (u₍ᵢ₎ w₁)_{m+n−i;k} w₂`. -/
theorem commutator {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y)
    (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (m : ℤ) (n : ℂ) (k : ℕ) :
    mode (A₃.YM u) m (Y n k w₁ w₂) - Y n k w₁ (mode (A₂.YM u) m w₂)
      = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) k (mode (A₁.YM u) i w₁) w₂ := by
  have h := hY.jacobi u w₁ w₂ 0 m n k
  rw [finsum_eq_single _ (0 : ℤ)] at h
  · simpa [cbz_zero_left, negOnePow] using h
  · intro i hi
    simp [cbz_zero_left, hi]

/-- `C(1, i)` is `1` at `i = 0, 1` and `0` elsewhere. -/
theorem cbz_one_eq (i : ℤ) : cbz 1 i = if i = 0 ∨ i = 1 then 1 else 0 := by
  rcases lt_trichotomy i 0 with h | h | h
  · rw [cbz_apply_neg 1 h, if_neg (by omega)]
  · subst h; simp
  · rcases eq_or_lt_of_le (show (1 : ℤ) ≤ i by omega) with h1 | h1
    · subst h1
      rw [if_pos (Or.inr rfl), cbz_pascal 1 1, show (1 : ℤ) - 1 = 0 by ring, cbz_zero,
        cbz_lt (le_refl 0) (by norm_num)]
      ring
    · rw [cbz_lt (by norm_num) h1, if_neg (by omega)]

/-- The commutator formula with `u = ω`, `m = 1`:
`L₀ (w₁)_{n;k} w₂ − (w₁)_{n;k} L₀ w₂ = (L₋₁w₁)_{n+1;k} w₂ + (L₀w₁)_{n;k} w₂`. -/
theorem L0_commutator {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y)
    (w₁ : M₁) (w₂ : M₂) (n : ℂ) (k : ℕ) :
    L0 A₃ (Y n k w₁ w₂) - Y n k w₁ (L0 A₂ w₂)
      = Y (n + 1) k (Lm1 A₁ w₁) w₂ + Y n k (L0 A₁ w₁) w₂ := by
  have h := hY.commutator W.conformalVector w₁ w₂ 1 n k
  rw [finsum_eq_sum_of_support_subset _ (s := ({0, 1} : Finset ℤ)) (by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hc
    exact hi (by rw [cbz_one_eq, if_neg hc, zero_smul])),
    Finset.sum_insert (by norm_num), Finset.sum_singleton, cbz_one_eq, cbz_one_eq,
    if_pos (Or.inl rfl), if_pos (Or.inr rfl), one_smul, one_smul] at h
  rw [h, show ((1 : ℤ) : ℂ) + n - ((0 : ℤ) : ℂ) = n + 1 by push_cast; ring,
    show ((1 : ℤ) : ℂ) + n - ((1 : ℤ) : ℂ) = n by push_cast; ring]

/-- **The `L(0)`-bracket formula** (HLZ II §3; the `L(0)`-conjugation property in modes):
`L₀ (w₁)_{n;k} w₂ − (L₀w₁)_{n;k} w₂ − (w₁)_{n;k} L₀w₂ = (−n−1)(w₁)_{n;k}w₂ + (k+1)(w₁)_{n;k+1}w₂`.
This is the only place where logarithms enter: `(k+1)`-times the next log coefficient is the
failure of `(w₁)_{n;k}` to shift `L₀`-eigenvalues by `−n−1`. -/
theorem L0_bracket {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y)
    (w₁ : M₁) (w₂ : M₂) (n : ℂ) (k : ℕ) :
    L0 A₃ (Y n k w₁ w₂) - Y n k (L0 A₁ w₁) w₂ - Y n k w₁ (L0 A₂ w₂)
      = (-n - 1) • Y n k w₁ w₂ + ((k : ℂ) + 1) • Y n (k + 1) w₁ w₂ := by
  have h := hY.L0_commutator w₁ w₂ n k
  have hL := hY.L_neg_one w₁ (n + 1) k
  rw [show n + 1 - 1 = n by ring] at hL
  rw [hL] at h
  simp only [LinearMap.add_apply, LinearMap.smul_apply] at h
  have : L0 A₃ (Y n k w₁ w₂) - Y n k (L0 A₁ w₁) w₂ - Y n k w₁ (L0 A₂ w₂)
      = (L0 A₃ (Y n k w₁ w₂) - Y n k w₁ (L0 A₂ w₂)) - Y n k (L0 A₁ w₁) w₂ := by abel
  rw [this, h, neg_add, sub_eq_add_neg (-n) 1, add_smul]
  abel_nf

end IsLogIntertwining

/-! ## The space of logarithmic intertwining operators -/

/-- The `ℂ`-vector space of logarithmic intertwining operators of type `(W₃ / W₁ W₂)`. -/
noncomputable def logIntertwiningSpace (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) : Submodule ℂ (LogModes M₁ M₂ M₃) where
  carrier := {Y | IsLogIntertwining A₁ A₂ A₃ Y}
  zero_mem' := by
    refine ⟨fun _ _ _ => ⟨0, fun _ _ => rfl⟩, fun _ _ _ => ⟨0, fun _ _ _ => rfl⟩,
      fun _ _ _ => by simp, ?_⟩
    intro u w₁ w₂ ℓ m n k
    simp
  add_mem' := by
    intro Y₁ Y₂ (h₁ : IsLogIntertwining A₁ A₂ A₃ Y₁) (h₂ : IsLogIntertwining A₁ A₂ A₃ Y₂)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w₁ w₂ n
      obtain ⟨K₁, hK₁⟩ := h₁.logFinite w₁ w₂ n
      obtain ⟨K₂, hK₂⟩ := h₂.logFinite w₁ w₂ n
      refine ⟨max K₁ K₂, fun k hk => ?_⟩
      simp [hK₁ k (le_trans (le_max_left _ _) hk), hK₂ k (le_trans (le_max_right _ _) hk)]
    · intro w₁ w₂ n
      obtain ⟨N₁, hN₁⟩ := h₁.truncation w₁ w₂ n
      obtain ⟨N₂, hN₂⟩ := h₂.truncation w₁ w₂ n
      refine ⟨max N₁ N₂, fun m hm k => ?_⟩
      simp [hN₁ m (le_trans (le_max_left _ _) hm) k, hN₂ m (le_trans (le_max_right _ _) hm) k]
    · intro w₁ n k
      simp only [Pi.add_apply, LinearMap.add_apply, h₁.L_neg_one, h₂.L_neg_one, smul_add]
      abel
    · intro u w₁ w₂ ℓ m n k
      have e1 := h₁.jacobi u w₁ w₂ ℓ m n k
      have e2 := h₂.jacobi u w₁ w₂ ℓ m n k
      change ∑ᶠ i, IsLogIntertwining.jacL A₂ A₃ (Y₁ + Y₂) u w₁ w₂ ℓ m n k i
        = ∑ᶠ i, IsLogIntertwining.jacR A₁ (Y₁ + Y₂) u w₁ w₂ ℓ m n k i
      simp only [IsLogIntertwining.jacL_add, IsLogIntertwining.jacR_add]
      rw [finsum_add_distrib (IsLogIntertwining.jacL_support_finite h₁.truncation ..)
          (IsLogIntertwining.jacL_support_finite h₂.truncation ..),
        finsum_add_distrib
          (IsLogIntertwining.jacR_support_finite (A₁ := A₁) Y₁ u w₁ w₂ ℓ m n k)
          (IsLogIntertwining.jacR_support_finite (A₁ := A₁) Y₂ u w₁ w₂ ℓ m n k)]
      exact congrArg₂ (· + ·) e1 e2
  smul_mem' := by
    intro c Y (h : IsLogIntertwining A₁ A₂ A₃ Y)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w₁ w₂ n
      obtain ⟨K, hK⟩ := h.logFinite w₁ w₂ n
      exact ⟨K, fun k hk => by simp [hK k hk]⟩
    · intro w₁ w₂ n
      obtain ⟨N, hN⟩ := h.truncation w₁ w₂ n
      exact ⟨N, fun m hm k => by simp [hN m hm k]⟩
    · intro w₁ n k
      simp only [Pi.smul_apply, LinearMap.smul_apply, h.L_neg_one, smul_add,
        smul_comm c (-n), smul_comm c ((k : ℂ) + 1)]
    · intro u w₁ w₂ ℓ m n k
      have e := h.jacobi u w₁ w₂ ℓ m n k
      change ∑ᶠ i, IsLogIntertwining.jacL A₂ A₃ (c • Y) u w₁ w₂ ℓ m n k i
        = ∑ᶠ i, IsLogIntertwining.jacR A₁ (c • Y) u w₁ w₂ ℓ m n k i
      simp only [IsLogIntertwining.jacL_smul, IsLogIntertwining.jacR_smul]
      rw [← smul_finsum' c (IsLogIntertwining.jacL_support_finite h.truncation ..),
        ← smul_finsum' c
          (IsLogIntertwining.jacR_support_finite (A₁ := A₁) Y u w₁ w₂ ℓ m n k)]
      exact congrArg (c • ·) e

theorem mem_logIntertwiningSpace {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : LogModes M₁ M₂ M₃} :
    Y ∈ logIntertwiningSpace A₁ A₂ A₃ ↔ IsLogIntertwining A₁ A₂ A₃ Y := Iff.rfl

/-- The type of logarithmic intertwining operators of type `(W₃ / W₁ W₂)`, a `ℂ`-vector space. -/
abbrev LogIntertwiningOperator (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) :=
  ↥(logIntertwiningSpace A₁ A₂ A₃)

/-- Logarithmic intertwining operators among **graded weak modules** (`C2Rigid.GWModule`: the
grading-restricted generalized modules of HLZ, e.g. every finite-length module of a `C₂`-cofinite
VOA via `C2Rigid.gwOfFiniteLength`). -/
abbrev GWLogIntertwiningOperator {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module ℂ X₁]
    [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃]
    (N₁ : C2Rigid.GWModule W X₁) (N₂ : C2Rigid.GWModule W X₂) (N₃ : C2Rigid.GWModule W X₃) :=
  LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule

/-- The **logarithmic fusion rule** `N^{W₃}_{W₁W₂} := dim_ℂ` of the space of logarithmic
intertwining operators.  ⚠ `Module.finrank` is `0` on an infinite-dimensional space; read it
together with a `FiniteDimensional` hypothesis. -/
noncomputable def logFusionRule (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) : ℕ :=
  Module.finrank ℂ (logIntertwiningSpace A₁ A₂ A₃)

end VOA.LogTensor
