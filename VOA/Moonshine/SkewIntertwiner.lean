/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Translation
import VOA.Modules.Fusion

/-!
# The skew-symmetry intertwiner of a module

For any VOA `𝒱` and any weak `𝒱`-module `M`, the **skew-symmetry operator**

  `W(t,z)φ = e^{zL₋₁} Y_M(φ,−z) t`  (`t ∈ M`, `φ ∈ 𝒱`),

in modes (library conventions: `mode f n = f (−n−1)`, `u₍ₙ₎ = mode (Y u) n`)

  `W(t)₍ₙ₎φ = ∑_{i≥0} (−1)^{n+i+1}/i! · L₋₁ⁱ(φ₍ₙ₊ᵢ₎ᴹ t)`  (`wMode`),

is an intertwining operator of type `(M; M, 𝒱)` (FHL §5.4; DGM CMP 1996, eqs. (3.8)–(3.14)).
This is the module analogue of `Core.Skew.skewDist` (the case `M = 𝒱`). It is the M8b
input to the moonshine block field: for `M = (V_Λ^T)^+` it is the untwisted→twisted block
(instantiated in `Moonshine.SkewLeech`).

## Main results

* `Lm1 A := ω₍₀₎ᴹ`; `act_Lm1`: `u₍ₚ₎(L₋₁x) = L₋₁(u₍ₚ₎x) + p·u₍ₚ₋₁₎x` (from the module Jacobi
  identity and `act_T_covariance`); `act_Lm1_pow_expand` (the `e^{zL₋₁}` conjugation).
* `wMode`, `wModeLin`, `Wsk A t : FormalDist (𝒱 →ₗ[ℂ] M)` (`mode_Wsk`).
* `Wsk_vacuum` — `W(t,z)𝟙 = e^{zL₋₁}t`.
* `Wsk_deriv` — `W(L₋₁t,z) = ∂_z W(t,z)` (`wMode_Lm1`: `W(L₋₁t)₍ₙ₎ = −n W(t)₍ₙ₋₁₎`).
* `wMode_comm` — the intertwining commutator formula for **all** `m ∈ ℤ`:
  `u₍ₘ₎ᴹ W(t)₍ₙ₎φ − W(t)₍ₙ₎(u₍ₘ₎φ) = ∑_{r<J} C(m,r) W(u₍ᵣ₎ᴹt)₍ₘ₊ₙ₋ᵣ₎φ`.
* `Wsk_local` / `Wsk_local_of_bound` — `(z₁−z₂)ᴶ [Y_M(u,z₁)W(t,z₂) − W(t,z₂)Y(u,z₁)] = 0`,
  with `J` the truncation order of `u` on `t` (independent of the test vector).
* `skewIntertwiner A : Intertwiner A (adjointModule W) A` (`Modules.Fusion`).

## Proof route

No vacuum/Goddard argument is available for a module, so the commutator is proved directly:
expand `u₍ₘ₎ L₋₁ⁱ` by `act_Lm1_pow_expand`, reindex the resulting double sum
(`act_wMode_expand`), and collapse the inner sum with the module iterate formula
`module_iterate0` (the `m_J = 0` slice of the module Jacobi identity; `iterate_sum`,
`inner_collapse`). This is the mode form of
`e^{−zL₋₁}u₍ₘ₎e^{zL₋₁} = ∑ₖ C(m,k)zᵏu₍ₘ₋ₖ₎` + `Res_{x₁}` of the Jacobi identity. All sums are
finite `Finset.range K` sums with one bound `K` chosen past every truncation. Locality then
follows from the commutator formula via the jump distributions `jumpDist` (Pascal:
`(z₁−z₂)·jumpDist (j+1) = jumpDist j`, `(z₁−z₂)·jumpDist 0 = 0`).

## Status

`sorry`-free; every declaration `#print axioms`-clean with
`[propext, Classical.choice, Quot.sound]` (no `VOA.pbw`). Unconditional: the only input is a
`WeakModule` (resp. `OrdVModule` for `skewIntertwiner`).

Not done: the full three-variable intertwining Jacobi identity for `W` (the commutator
formula plus locality is what reconstruction consumes); associativity-type statements for
`W`; the adjoint `W̄` (M8c).
-/

namespace VOA

namespace SkewIntertwiner

open Module (End)
open scoped BigOperators
open VertexOperatorAlgebra

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## §1. The module translation operator and its commutation with modes -/

/-- The module translation operator `L₋₁ᴹ = ω₍₀₎ᴹ`. -/
noncomputable def Lm1 (A : WeakModule W M) : End ℂ M := mode (A.YM W.conformalVector) 0

theorem smul_omega_zero (u : 𝒱) : W.smul W.conformalVector 0 u = W.L (-1) u := by
  rw [L_def, PreVertexAlgebra.smul_def]; norm_num

/-- The module commutator formula with `ℓ = 0`, `m = 0`:
`u₍₀₎ᴹ v₍ₙ₎ᴹ x − v₍ₙ₎ᴹ u₍₀₎ᴹ x = (u₍₀₎v)₍ₙ₎ᴹ x`. -/
theorem act_comm_zero (A : WeakModule W M) (u v : 𝒱) (n : ℤ) (x : M) :
    A.act u 0 (A.act v n x) - A.act v n (A.act u 0 x) = A.act (W.smul u 0 v) n x := by
  have hj := A.jacobi u v x 0 0 n
  have hl : (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (mode (A.YM u) (0 + 0 - i) (mode (A.YM v) (n + i) x)
          - negOnePow 0 • mode (A.YM v) (0 + n - i) (mode (A.YM u) (0 + i) x)))
      = A.act u 0 (A.act v n x) - A.act v n (A.act u 0 x) := by
    rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp [negOnePow]
  have hr : (∑ᶠ i : ℤ, cbz 0 i • mode (A.YM (W.smul u (0 + i) v)) (0 + n - i) x)
      = A.act (W.smul u 0 v) n x := by
    rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
    simp
  rw [← hl, ← hr]; exact hj

/-- **The `(Comm)` relation on the module**: `u₍ₚ₎ᴹ(L₋₁x) = L₋₁(u₍ₚ₎ᴹ x) + p·u₍ₚ₋₁₎ᴹ x`. -/
theorem act_Lm1 (A : WeakModule W M) (u : 𝒱) (p : ℤ) (x : M) :
    A.act u p (Lm1 A x) = Lm1 A (A.act u p x) + p • A.act u (p - 1) x := by
  have h := act_comm_zero A W.conformalVector u p x
  rw [smul_omega_zero, act_T_covariance] at h
  have hL : ∀ y, Lm1 A y = A.act W.conformalVector 0 y := fun y => rfl
  rw [hL, hL]
  have : (p : ℂ) • A.act u (p - 1) x = p • A.act u (p - 1) x := by
    rw [← Int.cast_smul_eq_zsmul ℂ]
  rw [← this]
  linear_combination (norm := module) -h

/-- **The master `e^{zL₋₁}`-conjugation of a fixed module mode** (module mirror of
`smul_Tpow_expand`): `u₍ₚ₎ᴹ(L₋₁ᵏx) = ∑_{r≤k} C(k,r)·p^{(r)}·L₋₁ᵏ⁻ʳ(u₍ₚ₋ᵣ₎ᴹ x)`. -/
theorem act_Lm1_pow_expand (A : WeakModule W M) (c : 𝒱) (p : ℤ) (k : ℕ) (u : M) :
    A.act c p ((Lm1 A ^ k) u)
      = ∑ r ∈ Finset.range (k + 1),
          (mcoeff p k r) • ((Lm1 A ^ (k - r)) (A.act c (p - (r : ℤ)) u)) := by
  induction k generalizing p with
  | zero =>
      rw [Finset.sum_range_one]; simp [mcoeff, fallI]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, act_Lm1, ih, ih (p - 1)]
      set Φ : ℕ → M := fun r => (Lm1 A ^ ((k + 1) - r)) (A.act c (p - (r : ℤ)) u)
        with hΦ
      have hA : Lm1 A
            (∑ r ∈ Finset.range (k + 1),
              (mcoeff p k r) • ((Lm1 A ^ (k - r)) (A.act c (p - (r : ℤ)) u)))
          = ∑ r ∈ Finset.range (k + 2), (mcoeff p k r) • Φ r := by
        rw [map_sum, Finset.sum_range_succ (fun r => (mcoeff p k r) • Φ r) (k + 1),
          show (mcoeff p k (k + 1)) = 0 by
            rw [mcoeff, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul],
          zero_smul, add_zero]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        rw [map_zsmul, hΦ]
        congr 1
        show Lm1 A ((Lm1 A ^ (k - r)) (A.act c (p - (r : ℤ)) u))
          = (Lm1 A ^ ((k + 1) - r)) (A.act c (p - (r : ℤ)) u)
        rw [← Module.End.mul_apply, ← pow_succ', show (k + 1) - r = (k - r) + 1 by omega]
      have hB : p • (∑ r ∈ Finset.range (k + 1),
              (mcoeff (p - 1) k r) • ((Lm1 A ^ (k - r)) (A.act c ((p - 1) - (r : ℤ)) u)))
          = ∑ r ∈ Finset.range (k + 2),
              (if r = 0 then (0 : ℤ) else p * mcoeff (p - 1) k (r - 1)) • Φ r := by
        rw [Finset.smul_sum,
          Finset.sum_range_succ' (fun r => (if r = 0 then (0 : ℤ)
            else p * mcoeff (p - 1) k (r - 1)) • Φ r) (k + 1),
          if_pos rfl, zero_smul, add_zero]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        rw [if_neg (Nat.succ_ne_zero r),
          show (r + 1 - 1) = r from by omega, smul_smul, hΦ]
        show (p * mcoeff (p - 1) k r) •
            (Lm1 A ^ (k - r)) (A.act c ((p - 1) - (r : ℤ)) u)
          = (p * mcoeff (p - 1) k r) •
            (Lm1 A ^ ((k + 1) - (r + 1))) (A.act c (p - ((r + 1 : ℕ) : ℤ)) u)
        rw [Nat.succ_sub_succ, show (p - ((r + 1 : ℕ) : ℤ)) = (p - 1) - (r : ℤ) by push_cast; ring]
      rw [hA, hB, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_range] at hr
      rw [← add_smul]
      congr 1
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rw [if_pos rfl, add_zero]
        simp only [mcoeff, Nat.choose_zero_right, fallI_zero]
      · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
        rw [if_neg (Nat.succ_ne_zero q), Nat.add_sub_cancel,
          mcoeff, mcoeff, mcoeff,
          show p * ((k.choose q : ℤ) * fallI (p - 1) q)
              = (k.choose q : ℤ) * (p * fallI (p - 1) q) by ring,
          mul_fallI_pred, Nat.choose_succ_succ, Nat.cast_add, add_mul]
        ring

/-! ## §2. The skew operator `W(t,z)φ = e^{zL₋₁} Y_M(φ,−z) t` -/

/-- The `i`-th summand of `W(t)₍ₙ₎φ`: `(1/i!)(−1)^{n+i+1} L₋₁ⁱ(φ₍ₙ₊ᵢ₎ᴹ t)`. -/
noncomputable def wTerm (A : WeakModule W M) (t : M) (n : ℤ) (φ : 𝒱) (i : ℕ) : M :=
  (((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) • ((Lm1 A ^ i) (A.act φ (n + i) t))

/-- **The skew mode** `W(t)₍ₙ₎φ = ∑ᵢ (1/i!)(−1)^{n+i+1} L₋₁ⁱ(φ₍ₙ₊ᵢ₎ᴹ t)`, the `z^{−n−1}`
coefficient of `e^{zL₋₁} Y_M(φ,−z) t`. -/
noncomputable def wMode (A : WeakModule W M) (t : M) (n : ℤ) (φ : 𝒱) : M :=
  ∑ᶠ i : ℕ, wTerm A t n φ i

theorem wTerm_eq_zero (A : WeakModule W M) {t : M} {n : ℤ} {φ : 𝒱} {i : ℕ}
    (h : A.act φ (n + i) t = 0) : wTerm A t n φ i = 0 := by
  rw [wTerm, h, map_zero, smul_zero]

/-- A truncation bound for `φ` on `t`, in the `ℕ`-offset form used by the skew sums. -/
theorem exists_bound (A : WeakModule W M) (t : M) (n : ℤ) (φ : 𝒱) :
    ∃ K : ℕ, ∀ i : ℕ, K ≤ i → A.act φ (n + i) t = 0 := by
  obtain ⟨N, hN⟩ := A.truncation φ t
  exact ⟨(N - n).toNat, fun i hi => hN _ (by omega)⟩

/-- The skew mode as a finite sum, for any bound `K` past the truncation. -/
theorem wMode_eq_sum (A : WeakModule W M) {t : M} {n : ℤ} {φ : 𝒱} (K : ℕ)
    (hK : ∀ i : ℕ, K ≤ i → A.act φ (n + i) t = 0) :
    wMode A t n φ = ∑ i ∈ Finset.range K, wTerm A t n φ i := by
  rw [wMode]
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  rw [Function.mem_support] at hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hi (wTerm_eq_zero A (hK i (by omega)))

/-! ## §3. Vacuum, translation, linearity -/

/-- **Vacuum property** in modes: `W(t)₍ₙ₎𝟙 = L₋₁^{−n−1} t / (−n−1)!` for `n ≤ −1`, else `0`;
i.e. `W(t,z)𝟙 = e^{zL₋₁} t`. -/
theorem wMode_vacuum (A : WeakModule W M) (t : M) (n : ℤ) :
    wMode A t n W.vacuum
      = if n ≤ -1 then (((-n - 1).toNat.factorial : ℂ)⁻¹) • (Lm1 A ^ (-n - 1).toNat) t
        else 0 := by
  split_ifs with hn
  · rw [wMode, finsum_eq_single _ (-n - 1).toNat (fun i hi => ?_)]
    · rw [wTerm, WeakModule.act_vacuum, if_pos (by omega),
        show n + (((-n - 1).toNat : ℕ) : ℤ) + 1 = 0 by omega]
      simp [negOnePow]
    · rw [wTerm, WeakModule.act_vacuum, if_neg (by omega), map_zero, smul_zero]
  · rw [wMode]
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    rw [wTerm, WeakModule.act_vacuum, if_neg (by omega), map_zero, smul_zero]

theorem act_smul_left (A : WeakModule W M) (c : ℂ) (u : 𝒱) (n : ℤ) (x : M) :
    A.act (c • u) n x = c • A.act u n x := by
  simp only [WeakModule.act_def, map_smul, mode_smul, LinearMap.smul_apply]

/-- The telescoping summand used for the translation property. -/
noncomputable def derivTel (A : WeakModule W M) (t : M) (n : ℤ) (φ : 𝒱) : ℕ → M
  | 0 => 0
  | (j + 1) => (((j.factorial : ℂ)⁻¹) * negOnePow (n + (j : ℤ) + 1)) •
      ((Lm1 A ^ (j + 1)) (A.act φ (n + (j : ℤ)) t))

theorem derivTel_step (A : WeakModule W M) (t : M) (n : ℤ) (φ : 𝒱) (i : ℕ) :
    wTerm A (Lm1 A t) n φ i - (-(n : ℂ)) • wTerm A t (n - 1) φ i
      = derivTel A t n φ (i + 1) - derivTel A t n φ i := by
  have hc : ∀ (p : ℤ) (y : M), A.act φ p (Lm1 A y) = Lm1 A (A.act φ p y)
      + (p : ℂ) • A.act φ (p - 1) y := by
    intro p y; rw [act_Lm1, Int.cast_smul_eq_zsmul]
  have hpow : ∀ (k : ℕ) (y : M), (Lm1 A ^ k) (Lm1 A y) = (Lm1 A ^ (k + 1)) y := by
    intro k y; rw [pow_succ, Module.End.mul_apply]
  rw [wTerm, wTerm, hc, map_add, map_smul, hpow, show n - 1 + (i : ℤ) = n + (i : ℤ) - 1 by ring]
  set P := A.act φ (n + (i : ℤ)) t
  set Q := A.act φ (n + (i : ℤ) - 1) t
  rcases i with _ | j
  · have h1 : negOnePow (n + ((0 : ℕ) : ℤ) + 1) = - negOnePow n := by
      rw [show n + ((0 : ℕ) : ℤ) + 1 = n + 1 by push_cast; ring, negOnePow_succ]
    have h2 : negOnePow (n + ((0 : ℕ) : ℤ) - 1 + 1) = negOnePow n := by
      congr 1; push_cast; ring
    simp only [derivTel, h1, h2, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Module.End.one_apply, zero_add, sub_zero]
    match_scalars <;> ring
  · set e := negOnePow (n + (j : ℤ))
    have h1 : negOnePow (n + ((j + 1 : ℕ) : ℤ) + 1) = e := by
      rw [show n + ((j + 1 : ℕ) : ℤ) + 1 = (n + (j : ℤ)) + 1 + 1 by push_cast; ring,
        negOnePow_succ, negOnePow_succ, neg_neg]
    have h2 : negOnePow (n + ((j + 1 : ℕ) : ℤ) - 1 + 1) = -e := by
      rw [show n + ((j + 1 : ℕ) : ℤ) - 1 + 1 = (n + (j : ℤ)) + 1 by push_cast; ring,
        negOnePow_succ]
    have h3 : negOnePow (n + (j : ℤ) + 1) = -e := by rw [negOnePow_succ]
    have hQ : A.act φ (n + (j : ℤ)) t = Q := by
      simp only [Q]; congr 1; push_cast; ring
    have hP : A.act φ (n + ((j + 1 : ℕ) : ℤ)) t = P := rfl
    simp only [derivTel, h1, h2, h3, hQ]
    rw [show n + ((j + 1 : ℕ) : ℤ) = n + (j : ℤ) + 1 by push_cast; ring] at hP ⊢
    rw [hP]
    have hf : (((j + 1).factorial : ℂ)) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    rw [hf]
    match_scalars <;> (field_simp; try ring)

/-- **Translation property** in modes: `W(L₋₁t)₍ₙ₎ = −n · W(t)₍ₙ₋₁₎`, i.e.
`W(L₋₁t, z) = ∂_z W(t, z)`. -/
theorem wMode_Lm1 (A : WeakModule W M) (t : M) (n : ℤ) (φ : 𝒱) :
    wMode A (Lm1 A t) n φ = (-(n : ℂ)) • wMode A t (n - 1) φ := by
  obtain ⟨N, hN⟩ := A.truncation φ t
  set K : ℕ := (N - n + 1).toNat + 1 with hKdef
  have h1 : ∀ i : ℕ, K ≤ i → A.act φ (n + i) (Lm1 A t) = 0 := by
    intro i hi
    rw [act_Lm1, WeakModule.act_def, WeakModule.act_def, hN _ (by omega), hN _ (by omega),
      map_zero, smul_zero, add_zero]
  have h2 : ∀ i : ℕ, K ≤ i → A.act φ (n - 1 + i) t = 0 := by
    intro i hi; rw [WeakModule.act_def]; exact hN _ (by omega)
  rw [wMode_eq_sum A K h1, wMode_eq_sum A K h2, Finset.smul_sum, ← sub_eq_zero,
    ← Finset.sum_sub_distrib]
  simp_rw [derivTel_step]
  rw [Finset.sum_range_sub, hKdef]
  simp only [derivTel, sub_zero]
  rw [WeakModule.act_def, hN _ (by omega), map_zero, smul_zero]

/-! ### Linearity -/

theorem wTerm_add_left (A : WeakModule W M) (t : M) (n : ℤ) (φ ψ : 𝒱) (i : ℕ) :
    wTerm A t n (φ + ψ) i = wTerm A t n φ i + wTerm A t n ψ i := by
  simp only [wTerm, WeakModule.act_add_left, map_add, smul_add]

theorem wTerm_smul_left (A : WeakModule W M) (t : M) (n : ℤ) (c : ℂ) (φ : 𝒱) (i : ℕ) :
    wTerm A t n (c • φ) i = c • wTerm A t n φ i := by
  simp only [wTerm, act_smul_left, map_smul]; rw [smul_comm]

theorem wTerm_add_right (A : WeakModule W M) (t s : M) (n : ℤ) (φ : 𝒱) (i : ℕ) :
    wTerm A (t + s) n φ i = wTerm A t n φ i + wTerm A s n φ i := by
  simp only [wTerm, WeakModule.act_add_right, map_add, smul_add]

theorem wTerm_smul_right (A : WeakModule W M) (c : ℂ) (t : M) (n : ℤ) (φ : 𝒱) (i : ℕ) :
    wTerm A (c • t) n φ i = c • wTerm A t n φ i := by
  simp only [wTerm, WeakModule.act_smul_right, map_smul]; rw [smul_comm]

theorem wMode_add_left (A : WeakModule W M) (t : M) (n : ℤ) (φ ψ : 𝒱) :
    wMode A t n (φ + ψ) = wMode A t n φ + wMode A t n ψ := by
  obtain ⟨K₁, h₁⟩ := exists_bound A t n φ
  obtain ⟨K₂, h₂⟩ := exists_bound A t n ψ
  have h₃ : ∀ i : ℕ, K₁ + K₂ ≤ i → A.act (φ + ψ) (n + i) t = 0 := by
    intro i hi; rw [WeakModule.act_add_left, h₁ i (by omega), h₂ i (by omega), add_zero]
  rw [wMode_eq_sum A (K₁ + K₂) h₃, wMode_eq_sum A (K₁ + K₂) (fun i hi => h₁ i (by omega)),
    wMode_eq_sum A (K₁ + K₂) (fun i hi => h₂ i (by omega)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => wTerm_add_left A t n φ ψ i

theorem wMode_smul_left (A : WeakModule W M) (t : M) (n : ℤ) (c : ℂ) (φ : 𝒱) :
    wMode A t n (c • φ) = c • wMode A t n φ := by
  obtain ⟨K, h⟩ := exists_bound A t n φ
  have h' : ∀ i : ℕ, K ≤ i → A.act (c • φ) (n + i) t = 0 := by
    intro i hi; rw [act_smul_left, h i hi, smul_zero]
  rw [wMode_eq_sum A K h', wMode_eq_sum A K h, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => wTerm_smul_left A t n c φ i

theorem wMode_add_right (A : WeakModule W M) (t s : M) (n : ℤ) (φ : 𝒱) :
    wMode A (t + s) n φ = wMode A t n φ + wMode A s n φ := by
  obtain ⟨K₁, h₁⟩ := exists_bound A t n φ
  obtain ⟨K₂, h₂⟩ := exists_bound A s n φ
  have h₃ : ∀ i : ℕ, K₁ + K₂ ≤ i → A.act φ (n + i) (t + s) = 0 := by
    intro i hi; rw [WeakModule.act_add_right, h₁ i (by omega), h₂ i (by omega), add_zero]
  rw [wMode_eq_sum A (K₁ + K₂) h₃, wMode_eq_sum A (K₁ + K₂) (fun i hi => h₁ i (by omega)),
    wMode_eq_sum A (K₁ + K₂) (fun i hi => h₂ i (by omega)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => wTerm_add_right A t s n φ i

theorem wMode_smul_right (A : WeakModule W M) (c : ℂ) (t : M) (n : ℤ) (φ : 𝒱) :
    wMode A (c • t) n φ = c • wMode A t n φ := by
  obtain ⟨K, h⟩ := exists_bound A t n φ
  have h' : ∀ i : ℕ, K ≤ i → A.act φ (n + i) (c • t) = 0 := by
    intro i hi; rw [WeakModule.act_smul_right, h i hi, smul_zero]
  rw [wMode_eq_sum A K h', wMode_eq_sum A K h, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => wTerm_smul_right A c t n φ i

theorem wMode_zero_right (A : WeakModule W M) (n : ℤ) (φ : 𝒱) : wMode A 0 n φ = 0 := by
  rw [wMode]
  refine finsum_eq_zero_of_forall_eq_zero fun i => wTerm_eq_zero A ?_
  exact WeakModule.act_zero_right A φ _

/-- **Lower truncation of `W`**: `W(t)₍ₙ₎φ = 0` for `n ≫ 0`. -/
theorem wMode_truncation (A : WeakModule W M) (t : M) (φ : 𝒱) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → wMode A t n φ = 0 := by
  obtain ⟨N, hN⟩ := A.truncation φ t
  refine ⟨N, fun n hn => ?_⟩
  rw [wMode]
  refine finsum_eq_zero_of_forall_eq_zero fun i => wTerm_eq_zero A ?_
  rw [WeakModule.act_def]; exact hN _ (by omega)

/-- `W(t)₍ₙ₎` as a linear map `𝒱 →ₗ M`. -/
noncomputable def wModeLin (A : WeakModule W M) (t : M) (n : ℤ) : 𝒱 →ₗ[ℂ] M where
  toFun := wMode A t n
  map_add' := wMode_add_left A t n
  map_smul' := wMode_smul_left A t n

@[simp] theorem wModeLin_apply (A : WeakModule W M) (t : M) (n : ℤ) (φ : 𝒱) :
    wModeLin A t n φ = wMode A t n φ := rfl

/-- **The skew field** `W(t,z) = ∑ₙ W(t)₍ₙ₎ z^{−n−1} ∈ Hom(𝒱, M)⟦z^±⟧`,
`W(t,z)φ = e^{zL₋₁} Y_M(φ,−z) t`. -/
noncomputable def Wsk (A : WeakModule W M) (t : M) : FormalDist (𝒱 →ₗ[ℂ] M) :=
  fun k => wModeLin A t (-k - 1)

theorem mode_Wsk (A : WeakModule W M) (t : M) (n : ℤ) :
    mode (Wsk A t) n = wModeLin A t n := by
  rw [mode_apply, Wsk, show -(-n - 1) - 1 = n by ring]

/-- **`Wsk_vacuum`**: `W(t,z)𝟙 = e^{zL₋₁} t`, coefficientwise
(`z^k`-coefficient `L₋₁ᵏ t / k!` for `k ≥ 0`, zero for `k < 0`). -/
theorem Wsk_vacuum (A : WeakModule W M) (t : M) (k : ℤ) :
    Wsk A t k W.vacuum
      = if 0 ≤ k then ((k.toNat.factorial : ℂ)⁻¹) • (Lm1 A ^ k.toNat) t else 0 := by
  show wMode A t (-k - 1) W.vacuum = _
  rw [wMode_vacuum, show -(-k - 1) - 1 = k by ring]
  by_cases hk : 0 ≤ k
  · rw [if_pos (by omega), if_pos hk]
  · rw [if_neg (by omega), if_neg hk]

/-- **`Wsk_deriv`**: `W(L₋₁t, z) = ∂_z W(t, z)`. -/
theorem Wsk_deriv (A : WeakModule W M) (t : M) :
    Wsk A (Lm1 A t) = deriv (Wsk A t) := by
  funext k
  refine LinearMap.ext fun φ => ?_
  rw [deriv_apply]
  show wMode A (Lm1 A t) (-k - 1) φ = ((k + 1 : ℤ) • wModeLin A t (-(k + 1) - 1)) φ
  rw [wMode_Lm1, LinearMap.smul_apply, wModeLin_apply, ← Int.cast_smul_eq_zsmul ℂ,
    show -k - 1 - 1 = -(k + 1) - 1 by ring]
  push_cast; ring_nf

/-! ## §4. The intertwining commutator formula -/

theorem sum_range_shift {X : Type*} [AddCommMonoid X] (h : ℕ → X) (K r : ℕ)
    (h0 : ∀ i, i < r → h i = 0) (h1 : ∀ i, K ≤ i → h i = 0) :
    ∑ i ∈ Finset.range K, h i = ∑ a ∈ Finset.range K, h (a + r) := by
  have e1 := Finset.sum_range_add h r K
  have e2 := Finset.sum_range_add h K r
  rw [Finset.sum_eq_zero (fun i hi => h0 i (Finset.mem_range.1 hi)), zero_add] at e1
  rw [Finset.sum_eq_zero (s := Finset.range r) (f := fun a => h (K + a))
    (fun a _ => h1 _ (Nat.le_add_right K a)), add_zero] at e2
  rw [← e2, add_comm, e1]
  exact Finset.sum_congr rfl fun a _ => by rw [add_comm]

theorem scalar_reindex (n m : ℤ) (a r : ℕ) :
    (((a + r).factorial : ℂ)⁻¹ * negOnePow (n + ((a + r : ℕ) : ℤ) + 1))
        * (((mcoeff m (a + r) r : ℤ)) : ℂ)
      = ((a.factorial : ℂ)⁻¹ * negOnePow (n + a + r + 1)) * gBinom m r := by
  have hfac := Nat.add_choose_mul_factorial_mul_factorial a r
  have hfacC : (((a + r).choose r : ℕ) : ℂ) * (a.factorial : ℂ) * (r.factorial : ℂ)
      = ((a + r).factorial : ℂ) := by exact_mod_cast hfac
  have ha : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hr : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have har : ((a + r).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a + r)
  have hC : (((a + r).choose r : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left r a)).ne'
  rw [mcoeff, fallI, gBinom, show n + ((a + r : ℕ) : ℤ) + 1 = n + a + r + 1 by push_cast; ring]
  push_cast
  rw [← hfacC]
  field_simp

/-- Step 1 of the commutator: `u₍ₘ₎ᴹ W(t)₍ₙ₎φ` as a double sum over `(a, r)`. -/
theorem act_wMode_expand (A : WeakModule W M) (u : 𝒱) (m : ℤ) (t : M) (n : ℤ) (φ : 𝒱)
    (K : ℕ) (hK : ∀ i : ℕ, K ≤ i → A.act φ (n + i) t = 0) :
    A.act u m (wMode A t n φ) = ∑ a ∈ Finset.range K, ∑ r ∈ Finset.range K,
      (((a.factorial : ℂ)⁻¹ * negOnePow (n + a + r + 1)) * gBinom m r) •
        (Lm1 A ^ a) (A.act u (m - r) (A.act φ (n + ((a + r : ℕ) : ℤ)) t)) := by
  rw [wMode_eq_sum A K hK]
  set g : ℕ → ℕ → M := fun r i =>
    (((i.factorial : ℂ)⁻¹ * negOnePow (n + i + 1)) * ((mcoeff m i r : ℤ) : ℂ)) •
      (Lm1 A ^ (i - r)) (A.act u (m - r) (A.act φ (n + i) t)) with hg
  have h1 : A.act u m (∑ i ∈ Finset.range K, wTerm A t n φ i)
      = ∑ i ∈ Finset.range K, ∑ r ∈ Finset.range K, g r i := by
    rw [WeakModule.act_def, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [wTerm, map_smul, ← WeakModule.act_def, act_Lm1_pow_expand, Finset.smul_sum]
    rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega : i + 1 ≤ K)) (fun r _ hr => ?_)]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [hg]; dsimp only
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    · rw [Finset.mem_range] at hr
      rw [mcoeff, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_smul,
        smul_zero]
  rw [h1, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_range_shift (g r) K r]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hg]; dsimp only
    rw [scalar_reindex, Nat.add_sub_cancel]
  · intro i hi
    rw [hg]; dsimp only
    rw [mcoeff, Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, zero_mul, Int.cast_zero, mul_zero,
      zero_smul]
  · intro i hi
    rw [hg]; dsimp only
    rw [hK i hi, WeakModule.act_zero_right, map_zero, smul_zero]

theorem finsum_int_eq_sum_range {X : Type*} [AddCommMonoid X] (f : ℤ → X) (K : ℕ)
    (h : ∀ i : ℤ, f i ≠ 0 → 0 ≤ i ∧ i < K) :
    ∑ᶠ i : ℤ, f i = ∑ r ∈ Finset.range K, f r := by
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range K).image (fun r : ℕ => (r : ℤ)))]
  · rw [Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
  · intro i hi
    obtain ⟨h0, hK⟩ := h i hi
    rw [Finset.coe_image, Finset.coe_range]
    exact ⟨i.toNat, by simp; omega, show ((i.toNat : ℕ) : ℤ) = i by omega⟩

/-- Step 2: the module iterate formula, as a finite sum. -/
theorem iterate_sum (A : WeakModule W M) (u φ : 𝒱) (t : M) (m q : ℤ) (K : ℕ)
    (h1 : ∀ i : ℕ, K ≤ i → A.act φ (q + i) t = 0) (h2 : ∀ i : ℕ, K ≤ i → A.act u i t = 0) :
    ∑ r ∈ Finset.range K, (negOnePow r * gBinom m r) • A.act u (m - r) (A.act φ (q + r) t)
      = A.act (W.smul u m φ) q t
        + ∑ r ∈ Finset.range K, (negOnePow r * gBinom m r * negOnePow m) •
            A.act φ (m + q - r) (A.act u r t) := by
  have hit := module_iterate0 A u φ t m q
  simp only [← WeakModule.act_def] at hit
  rw [finsum_int_eq_sum_range _ K] at hit
  · rw [hit, ← sub_eq_iff_eq_add, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cbz_apply_nonneg m (by omega), Int.toNat_natCast, smul_sub, smul_smul,
      show m + q - (r : ℤ) = m + q - (r : ℤ) from rfl]
  · intro i hi
    by_contra hc
    apply hi
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [cbz_apply_neg m hneg, mul_zero, zero_smul]
    · have hK : (K : ℤ) ≤ i := by omega
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) := ⟨i.toNat, by omega⟩
      rw [h1 j (by exact_mod_cast hK), WeakModule.act_zero_right, h2 j (by exact_mod_cast hK),
        WeakModule.act_zero_right, smul_zero, sub_zero, smul_zero]

theorem exists_bound_fin (J : ℕ) (P : ℕ → ℕ → Prop)
    (hmono : ∀ r K K', K ≤ K' → P r K → P r K') (h : ∀ r, ∃ K, P r K) :
    ∃ K, ∀ r, r < J → P r K := by
  induction J with
  | zero => exact ⟨0, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ J ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨K', hK'⟩ := h J
      refine ⟨K + K', fun r hr => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
      · exact hmono r K _ (Nat.le_add_right K K') (hK r hr)
      · exact hmono r K' _ (Nat.le_add_left K' K) hK'

/-- The per-`a` collapse: the inner `r`-sum of `act_wMode_expand` is the `a`-th term of
`W(t)₍ₙ₎(u₍ₘ₎φ)` plus the `a`-th terms of `∑ᵣ C(m,r) W(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎φ`. -/
theorem inner_collapse (A : WeakModule W M) (u : 𝒱) (m : ℤ) (t : M) (n : ℤ) (φ : 𝒱)
    (K a : ℕ) (h1 : ∀ i : ℕ, K ≤ i → A.act φ (n + a + i) t = 0)
    (h2 : ∀ i : ℕ, K ≤ i → A.act u i t = 0) :
    ∑ r ∈ Finset.range K,
      (((a.factorial : ℂ)⁻¹ * negOnePow (n + a + r + 1)) * gBinom m r) •
        (Lm1 A ^ a) (A.act u (m - r) (A.act φ (n + ((a + r : ℕ) : ℤ)) t))
      = wTerm A t n (W.smul u m φ) a
        + ∑ r ∈ Finset.range K, gBinom m r • wTerm A (A.act u r t) (m + n - r) φ a := by
  have hL : ∑ r ∈ Finset.range K,
      (((a.factorial : ℂ)⁻¹ * negOnePow (n + a + r + 1)) * gBinom m r) •
        (Lm1 A ^ a) (A.act u (m - r) (A.act φ (n + ((a + r : ℕ) : ℤ)) t))
      = (((a.factorial : ℂ)⁻¹) * negOnePow (n + a + 1)) • (Lm1 A ^ a)
          (∑ r ∈ Finset.range K, (negOnePow r * gBinom m r) •
            A.act u (m - r) (A.act φ ((n + a) + r) t)) := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, smul_smul, show n + ((a + r : ℕ) : ℤ) = (n + a) + r by push_cast; ring,
      show n + (a : ℤ) + r + 1 = (n + a + 1) + r by ring, negOnePow_add']
    congr 1; ring
  rw [hL, iterate_sum A u φ t m (n + a) K h1 h2, map_add, smul_add, map_sum, Finset.smul_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun r _ => ?_)
  · rw [wTerm, map_smul, smul_smul, smul_smul,
      show m + (n + (a : ℤ)) - r = m + n - r + a by ring]
    congr 1
    have hs : negOnePow (m + n - (r : ℤ) + a + 1)
        = negOnePow (n + a + 1) * negOnePow r * negOnePow m := by
      rw [show m + n - (r : ℤ) + a + 1 = (n + a + 1) + (-(r : ℤ)) + m by ring,
        negOnePow_add' ((n + a + 1) + (-(r : ℤ))) m, negOnePow_add' (n + a + 1) (-(r : ℤ)),
        negOnePow_neg']
    rw [hs]
    ring

/-- **The intertwining commutator formula** for the skew operator (type `(M; M, 𝒱)`):
for `J` past the truncation of `u` on `t`,
`u₍ₘ₎ᴹ W(t)₍ₙ₎φ − W(t)₍ₙ₎(u₍ₘ₎φ) = ∑_{r<J} C(m,r) W(u₍ᵣ₎ᴹt)₍ₘ₊ₙ₋ᵣ₎φ`, for **all** `m ∈ ℤ`. -/
theorem wMode_comm (A : WeakModule W M) (u : 𝒱) (m : ℤ) (t : M) (n : ℤ) (φ : 𝒱) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → A.act u j t = 0) :
    A.act u m (wMode A t n φ) - wMode A t n (W.smul u m φ)
      = ∑ r ∈ Finset.range J, gBinom m r • wMode A (A.act u r t) (m + n - r) φ := by
  obtain ⟨K₁, h₁⟩ := exists_bound A t n φ
  obtain ⟨K₂, h₂⟩ := exists_bound A t n (W.smul u m φ)
  obtain ⟨K₃, h₃⟩ := exists_bound_fin J
    (fun r K => ∀ i : ℕ, K ≤ i → A.act φ (m + n - r + i) (A.act u r t) = 0)
    (fun r K K' hKK' hP i hi => hP i (le_trans hKK' hi))
    (fun r => exists_bound A (A.act u r t) (m + n - r) φ)
  set K := K₁ + K₂ + K₃ + J with hK
  have hb₁ : ∀ i : ℕ, K ≤ i → A.act φ (n + i) t = 0 := fun i hi => h₁ i (by omega)
  have hb₂ : ∀ i : ℕ, K ≤ i → A.act (W.smul u m φ) (n + i) t = 0 := fun i hi => h₂ i (by omega)
  have hbJ : ∀ i : ℕ, K ≤ i → A.act u i t = 0 := fun i hi => hJ i (by omega)
  have hb₃ : ∀ r : ℕ, ∀ i : ℕ, K ≤ i →
      A.act φ (m + n - r + i) (A.act u r t) = 0 := by
    intro r i hi
    by_cases hr : r < J
    · exact h₃ r hr i (by omega)
    · rw [hJ r (by omega), WeakModule.act_zero_right]
  rw [act_wMode_expand A u m t n φ K hb₁, wMode_eq_sum A K hb₂]
  rw [Finset.sum_congr rfl fun a _ => inner_collapse A u m t n φ K a
      (fun i hi => by rw [show n + (a : ℤ) + i = n + ((a + i : ℕ) : ℤ) by push_cast; ring];
                      exact hb₁ _ (by omega)) hbJ]
  rw [Finset.sum_add_distrib, add_sub_cancel_left, Finset.sum_comm]
  rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega : J ≤ K))
    (fun r _ hr => by
      rw [Finset.mem_range, not_lt] at hr
      rw [hJ r hr, wMode_zero_right, smul_zero])]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.smul_sum, wMode_eq_sum A K (hb₃ r)]

/-! ## §5. Locality of `Y_M(u, z₁)` and `W(t, z₂)` -/

section Jump

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- The jump distribution `C(−z₁-index−1, j)·g(a+b)` — the coefficient pattern of
`g(z₂) ∂^{(j)}δ`-type terms. -/
noncomputable def jumpDist (j : ℕ) (g : ℤ → X) : FormalDist₂ X :=
  fun a b => gBinom (-a - 1) j • g (a + b)

theorem mulBySub_jumpDist_zero (g : ℤ → X) : mulBySub (jumpDist 0 g) = 0 := by
  ext a b
  rw [mulBySub_apply]
  simp only [jumpDist, gBinom_zero, one_smul]
  rw [show a - 1 + b = a + (b - 1) by ring, sub_self]; rfl

theorem mulBySub_jumpDist_succ (j : ℕ) (g : ℤ → X) :
    mulBySub (jumpDist (j + 1) g) = jumpDist j (fun k => g (k - 1)) := by
  ext a b
  rw [mulBySub_apply]
  simp only [jumpDist]
  rw [show a - 1 + b = a + b - 1 by ring, show a + (b - 1) = a + b - 1 by ring, ← sub_smul,
    show -(a - 1) - 1 = (-a - 1) + 1 by ring, gBinom_pascal_up]
  congr 1; ring

theorem mulBySubPow_jumpDist (j : ℕ) (g : ℤ → X) : mulBySubPow (j + 1) (jumpDist j g) = 0 := by
  induction j generalizing g with
  | zero => rw [mulBySubPow_succ', mulBySubPow_zero, LinearMap.id_apply, mulBySub_jumpDist_zero]
  | succ k ih => rw [mulBySubPow_succ', mulBySub_jumpDist_succ, ih]

theorem mulBySubPow_eq_zero_of_le {f : FormalDist₂ X} {N N' : ℕ} (hN : N ≤ N')
    (h : mulBySubPow N f = 0) : mulBySubPow N' f = 0 := by
  induction N', hN using Nat.le_induction with
  | base => exact h
  | succ n _ ih => rw [mulBySubPow_succ, LinearMap.comp_apply, ih, map_zero]

omit [Module ℂ X] in
theorem fd2_finset_sum_apply (J : ℕ) (g : ℕ → FormalDist₂ X) (a b : ℤ) :
    (∑ s ∈ Finset.range J, g s) a b = ∑ s ∈ Finset.range J, g s a b := by
  induction J with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]; rfl

end Jump

/-- The commutator distribution `[Y_M(u,z₁), W(t,z₂)]` as a two-variable distribution with
values in `Hom(𝒱, M)`: coefficient of `z₁ᵃz₂ᵇ` is `Y_M(u)ₐ ∘ W(t)_b − W(t)_b ∘ Y(u)ₐ`. -/
noncomputable def wBracket (A : WeakModule W M) (u : 𝒱) (t : M) : FormalDist₂ (𝒱 →ₗ[ℂ] M) :=
  fun a b => (A.YM u a).comp (Wsk A t b) - (Wsk A t b).comp (W.Y u a)

/-- The commutator distribution is a finite sum of jump distributions. -/
theorem wBracket_eq_sum (A : WeakModule W M) (u : 𝒱) (t : M) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → A.act u j t = 0) :
    wBracket A u t = ∑ r ∈ Finset.range J,
      jumpDist r (fun k => wModeLin A (A.act u r t) (-k - 2 - r)) := by
  refine FormalDist₂.ext fun a b => ?_
  rw [fd2_finset_sum_apply]
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.sum_apply]
  have hc := wMode_comm A u (-a - 1) t (-b - 1) φ J hJ
  have h1 : A.act u (-a - 1) (wMode A t (-b - 1) φ) = A.YM u a (wMode A t (-b - 1) φ) := by
    rw [WeakModule.act_def, mode_apply, show -(-a - 1) - 1 = a by ring]
  have h2 : W.smul u (-a - 1) φ = W.Y u a φ := by
    rw [PreVertexAlgebra.smul_def, mode_apply, show -(-a - 1) - 1 = a by ring]
  rw [h1, h2] at hc
  show A.YM u a (wMode A t (-b - 1) φ) - wMode A t (-b - 1) (W.Y u a φ) = _
  rw [hc]
  refine Finset.sum_congr rfl fun r _ => ?_
  show _ = (gBinom (-a - 1) r • wModeLin A (A.act u r t) (-(a + b) - 2 - r)) φ
  rw [LinearMap.smul_apply, wModeLin_apply, show -a - 1 + (-b - 1) - (r : ℤ)
    = -(a + b) - 2 - r by ring]

/-- **`Wsk_local`**: `Y_M(u, z₁)` and `W(t, z₂)` are mutually local:
`(z₁ − z₂)ᴶ [Y_M(u,z₁) W(t,z₂) − W(t,z₂) Y(u,z₁)] = 0` for any `J` past the truncation of
`u` on `t` (the order depends only on `u` and `t`, not on the test vector). -/
theorem Wsk_local_of_bound (A : WeakModule W M) (u : 𝒱) (t : M) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → A.act u j t = 0) :
    mulBySubPow J (wBracket A u t) = 0 := by
  rw [wBracket_eq_sum A u t J hJ, map_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.mem_range] at hr
  exact mulBySubPow_eq_zero_of_le (by omega : r + 1 ≤ J) (mulBySubPow_jumpDist r _)

theorem Wsk_local (A : WeakModule W M) (u : 𝒱) (t : M) :
    ∃ N : ℕ, mulBySubPow N (wBracket A u t) = 0 := by
  obtain ⟨N, hN⟩ := A.truncation u t
  exact ⟨N.toNat, Wsk_local_of_bound A u t N.toNat fun j hj => hN _ (by omega)⟩

/-! ## §6. Packaging as an intertwining operator of type `(M; M, 𝒱)` (Gannon Def. 6.1.9) -/

/-- `W(·)₍ₙ₎(·)` as a bilinear map `M →ₗ 𝒱 →ₗ M`. -/
noncomputable def wBil (A : WeakModule W M) (n : ℤ) : M →ₗ[ℂ] 𝒱 →ₗ[ℂ] M :=
  LinearMap.mk₂ ℂ (fun t φ => wMode A t n φ)
    (fun t s φ => wMode_add_right A t s n φ) (fun c t φ => wMode_smul_right A c t n φ)
    (fun t φ ψ => wMode_add_left A t n φ ψ) (fun c t φ => wMode_smul_left A t n c φ)

@[simp] theorem wBil_apply (A : WeakModule W M) (n : ℤ) (t : M) (φ : 𝒱) :
    wBil A n t φ = wMode A t n φ := rfl

open Classical in
/-- The `ℂ`-indexed mode data of the skew intertwiner: `W(t)₍ₙ₎` at integer `s = n`, and `0`
at non-integral `s` (all weights involved are integral). -/
noncomputable def skModes (A : WeakModule W M) (s : ℂ) : M →ₗ[ℂ] 𝒱 →ₗ[ℂ] M :=
  if h : ∃ n : ℤ, (n : ℂ) = s then wBil A (Classical.choose h) else 0

theorem skModes_int (A : WeakModule W M) (n : ℤ) : skModes A (n : ℂ) = wBil A n := by
  have h : ∃ k : ℤ, (k : ℂ) = (n : ℂ) := ⟨n, rfl⟩
  rw [skModes, dif_pos h]
  congr 1
  exact_mod_cast Classical.choose_spec h

theorem skModes_nonint (A : WeakModule W M) {s : ℂ} (h : ∀ n : ℤ, (n : ℂ) ≠ s) :
    skModes A s = 0 := by
  rw [skModes, dif_neg (fun ⟨n, hn⟩ => h n hn)]

section Fusion

variable {M' : Type u} [AddCommGroup M'] [Module ℂ M']

/-- **The skew intertwiner** `W` of type `(M; M, 𝒱)` (Gannon Def. 6.1.9; FHL §5.4,
DGM (3.8)): `W(t,z)φ = e^{zL₋₁} Y_M(φ,−z) t`, for any `𝒱`-module `M`. -/
noncomputable def skewIntertwiner (A : OrdVModule W M') :
    Intertwiner A (adjointModule W) A where
  modes := skModes A.toWeakModule
  truncation t φ := by
    obtain ⟨N, hN⟩ := wMode_truncation A.toWeakModule t φ
    refine ⟨(N : ℝ), fun s hs => ?_⟩
    by_cases hint : ∃ n : ℤ, (n : ℂ) = s
    · obtain ⟨n, rfl⟩ := hint
      rw [skModes_int, wBil_apply]
      refine hN n ?_
      have : (N : ℝ) ≤ (n : ℝ) := by simpa using hs
      exact_mod_cast this
    · rw [skModes_nonint A.toWeakModule (fun n hn => hint ⟨n, hn⟩)]; rfl
  isIntertwiner := by
    show intertwiningDefect A (adjointModule W) A (skModes A.toWeakModule) = 0
    funext a p s t φ
    simp only [intertwiningDefect, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    by_cases hint : ∃ n : ℤ, (n : ℂ) = s
    · obtain ⟨n, rfl⟩ := hint
      obtain ⟨J, hJ⟩ := A.truncation a t
      have hc := wMode_comm A.toWeakModule a p t n φ J.toNat
        (fun j hj => hJ _ (by omega))
      rw [sub_eq_zero, skModes_int, wBil_apply, wBil_apply]
      have hB : (adjointModule W).toWeakModule.act a p φ = W.smul a p φ := rfl
      rw [hB, hc]
      rw [finsum_eq_sum_of_support_subset _ (s := Finset.range J.toNat) (fun j hj => ?_)]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [intertwinerSummand, cbz_apply_nonneg p (by omega), Int.toNat_natCast,
          show ((n : ℂ) + (p : ℂ) - (r : ℂ)) = (((n + p - r : ℤ)) : ℂ) by push_cast; ring,
          skModes_int, wBil_apply, show p + n - (r : ℤ) = n + p - r by ring]
      · rw [Function.mem_support] at hj
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hge
        apply hj
        rw [intertwinerSummand, show A.toWeakModule.act a (j : ℤ) t = 0 from hJ _ (by omega),
          map_zero, LinearMap.zero_apply, smul_zero]
    · have hz : ∀ k : ℤ, skModes A.toWeakModule (s + k) = 0 := by
        intro k
        refine skModes_nonint A.toWeakModule fun n hn => hint ⟨n - k, ?_⟩
        push_cast; rw [hn]; ring
      rw [skModes_nonint A.toWeakModule (fun n hn => hint ⟨n, hn⟩)]
      simp only [LinearMap.zero_apply, sub_zero]
      rw [WeakModule.act_zero_right, zero_sub, neg_eq_zero]
      refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
      rw [intertwinerSummand, show s + (p : ℂ) - (j : ℂ) = s + ((p - j : ℤ) : ℂ) by push_cast; ring,
        hz, LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]

/-- The modes of `skewIntertwiner` at integral `s = n` are `W(t)₍ₙ₎φ`. -/
theorem skewIntertwiner_modes (A : OrdVModule W M') (n : ℤ) (t : M') (φ : 𝒱) :
    (skewIntertwiner A).modes (n : ℂ) t φ = wMode A.toWeakModule t n φ := by
  show skModes A.toWeakModule (n : ℂ) t φ = _
  rw [skModes_int, wBil_apply]

end Fusion

end SkewIntertwiner

end VOA
