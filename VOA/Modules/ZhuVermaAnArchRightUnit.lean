/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUnits
import VOA.Foundations.IotaZExpansion

/-!
# The `A_n(𝒱)` RIGHT unit law: `[a]·[𝟙] = [a]` (Dong–Li–Mason Thm 2.3).

The companion file `ZhuVermaAnArchUnits.lean` discharges the LEFT unit `[𝟙]·[a] = [a]` at the
SHARP representative level (`𝟙 *ₙ a = a` exactly).  The RIGHT unit is genuinely subtler: for
`n ≥ 1`, `a *ₙ 𝟙` is **not** `a` on the nose — the FZ expansion produces translate residuals
`a₍−1−t₎𝟙 = (Lᵗ₋₁ a)/t!` with `t ≥ 1` which are only congruent to `a` *modulo* `O_n`.  This file
proves `a *ₙ 𝟙 ≡ a (mod OnFull)`, i.e. `AnFull.RightUnitLaw W n (anIdeal_holds W n)`.

## Mathematical content (DLM Thm 2.3; the residual lands in `O^L`)

For homogeneous `a ∈ 𝒱_k`, `leftProd_homogeneous` gives
`a *ₙ 𝟙 = ∑_{j≤n}(−1)^j C(j+n,n) ∑_{i≤k+n} C(k+n,i)·a₍i−(n+j+1)₎𝟙`.
By creation (VA2/`creation_pow`): modes `≥ 0` kill the vacuum; mode `−1` gives `a`; mode `−1−t`
(`t ≥ 1`) gives `(Lᵗ₋₁a)/t!`.  Working in the quotient `AnFull = 𝒱/OnFull`, the key coset relation
is `[L₋₁ x] = −w·[x]` for `x ∈ 𝒱_w` (because `(L₋₁+L₀)x ∈ O^L ⊆ OnFull`, `L₀x = w·x`).  Iterating,
`[a₍−1−t₎𝟙] = C(−k, t)·[a]` (the generalized binomial `cbz (−k) t`).  Substituting and applying the
generalized-binomial **Vandermonde** `∑_i C(k+n,i)·C(−k, n+j−i) = C(n, n+j)` collapses the inner
`i`-sum to `C(n, n+j)`, which is `0` for `j ≥ 1` and `1` for `j = 0`; so `[a *ₙ 𝟙] = [a]`.

(Verified exact on the rank-1 free boson, all `n, k`; scalar `∑_j (−1)^j C(j+n,n) C(n,n+j) = 1`.)

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `mkAnFull_Lgen_eq_zero` — `[(L₋₁+L₀)x] = 0` in `AnFull`.
* `mkAnFull_L_neg_one_homog` — `[L₋₁ x] = −w·[x]` for `x ∈ 𝒱_w`.
* `mkAnFull_Tpow_homog` — `[Lᵗ₋₁ a] = (∏_{s<t}(−(k+s)))·[a]` for `a ∈ 𝒱_k`.
* `mkAnFull_smul_vacuum_homog` — `[a₍m₎𝟙] = C(−k, −m−1)·[a]` for `a ∈ 𝒱_k`, all modes `m`.
* `leftProd_vacuum_right_homog` — `[a *ₙ 𝟙] = [a]` for homogeneous `a` (Vandermonde collapse).
* `AnFull.rightUnitLaw_holds` — `AnFull.RightUnitLaw W n (anIdeal_holds W n)`, i.e. `[a]·[𝟙]=[a]`.
* `AnFull.mulU_vacuum_right` — `[a]·[𝟙]=[a]` for the unconditional product `AnFull.mulU`.

With `AnFull.leftUnitLaw_holds` (companion file), `[𝟙]` is a two-sided unit of `Aₙ(𝒱)`.

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (`q-alg/9612010`), Thm 2.3; Frenkel–Zhu, Duke 66 (1992);
Zhu, J. AMS 9 (1996); Gannon §5.3.2 Thm 5.3.4 (cf. `ZhuAlgebra.zhuMul_vacuum_right`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `O^L`-coset relations for translates. -/

/-- The `(L₋₁+L₀)`-generator class vanishes in `AnFull = 𝒱/OnFull`. -/
theorem mkAnFull_Lgen_eq_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x : 𝒱) :
    mkAnFull W n (W.L (-1) x + W.L 0 x) = 0 := by
  rw [mkAnFull_apply, Submodule.Quotient.mk_eq_zero]
  exact Lgen_mem_OnFull W n x

/-- **Translate coset (homogeneous).**  For `x ∈ 𝒱_w`, `[L₋₁ x] = −w·[x]` in `AnFull`.
Immediate from `[(L₋₁+L₀)x] = 0` and `L₀ x = w·x`. -/
theorem mkAnFull_L_neg_one_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {w : ℤ} {x : 𝒱}
    (hx : x ∈ W.grading w) :
    mkAnFull W n (W.L (-1) x) = (-(w : ℂ)) • mkAnFull W n x := by
  have h0 := mkAnFull_Lgen_eq_zero W n x
  rw [map_add, W.L_zero_grading x hx, map_smul] at h0
  -- h0 : [L₋₁ x] + w • [x] = 0
  have : mkAnFull W n (W.L (-1) x) = -((w : ℂ) • mkAnFull W n x) := by
    rw [eq_neg_iff_add_eq_zero]; exact h0
  rw [this, neg_smul]

/-- T-form of the translate coset: `[T x] = −w·[x]` for `x ∈ 𝒱_w` (since `T = L₋₁`). -/
theorem mkAnFull_T_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {w : ℤ} {x : 𝒱}
    (hx : x ∈ W.grading w) :
    mkAnFull W n (W.toPreVertexAlgebra.T x) = (-(w : ℂ)) • mkAnFull W n x := by
  rw [show W.toPreVertexAlgebra.T x = W.L (-1) x from by rw [T_eq_Lneg1]]
  exact mkAnFull_L_neg_one_homog W n hx

/-- `Tᵗ` raises the grading by `t`: `Tᵗ a ∈ 𝒱_{k+t}` for `a ∈ 𝒱_k`. -/
theorem Tpow_mem_grading (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (t : ℕ) :
    (W.toPreVertexAlgebra.T ^ t) a ∈ W.grading (k + (t : ℤ)) := by
  induction t with
  | zero => simpa using ha
  | succ p ihp =>
      rw [pow_succ', Module.End.mul_apply,
        show k + ((p + 1 : ℕ) : ℤ) = (k + (p : ℤ)) + 1 from by push_cast; ring]
      exact W.toPreVertexAlgebra.T_mem_grading ihp

/-- **Iterated translate coset.**  For `a ∈ 𝒱_k`, `[Lᵗ₋₁ a] = (∏_{s<t}(−(k+s)))·[a]` in `AnFull`.
Here `Lᵗ₋₁ = Tᵗ` (`T_eq_Lneg1`); proved by induction on `t`, using `Tˢ a ∈ 𝒱_{k+s}`. -/
theorem mkAnFull_Tpow_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (t : ℕ) :
    mkAnFull W n ((W.toPreVertexAlgebra.T ^ t) a)
      = (∏ s ∈ Finset.range t, (-((k : ℂ) + (s : ℂ)))) • mkAnFull W n a := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', Module.End.mul_apply,
        mkAnFull_T_homog W n (Tpow_mem_grading W ha t), ih, smul_smul,
        Finset.prod_range_succ]
      push_cast
      ring_nf

/-! ## The mode-on-vacuum coset value. -/

/-- **Mode-on-vacuum coset.**  For `a ∈ 𝒱_k` and any mode `m`,
`[a₍m₎𝟙] = C(−k, −m−1)·[a]` in `AnFull`.  Modes `m ≥ 0` give `0` (creation: `a₍m₎𝟙 = 0`, and
`cbz` vanishes at the negative index `−m−1`); mode `m = −1−t` gives `(Lᵗ₋₁a)/t! ≡ C(−k,t)·a`. -/
theorem mkAnFull_smul_vacuum_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (m : ℤ) :
    mkAnFull W n (W.smul a m W.vacuum) = cbz (-k) (-m - 1) • mkAnFull W n a := by
  rcases lt_or_ge m 0 with hm | hm
  · -- m ≤ −1: write m = −1−t, t = −m−1 ≥ 0; use creation_pow.
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = -(t : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
    rw [show -(-(t : ℤ) - 1) - 1 = (t : ℤ) from by ring]
    rw [cbz_apply_nonneg (-k) (by omega), show (t : ℤ).toNat = t from by omega]
    rw [creation_pow W a t, map_smul, mkAnFull_Tpow_homog W n ha t, smul_smul]
    congr 1
    -- ((t!)⁻¹) * ∏_{s<t}(−(k+s)) = gBinom (−k) t = (∏_{i<t}((−k)−i))/t!
    rw [gBinom]
    rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero t)]
    rw [mul_comm, ← mul_assoc]
    rw [mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero t : ((t.factorial : ℂ)) ≠ 0)]
    rw [one_mul]
    refine Finset.prod_congr rfl fun s _ => ?_
    push_cast; ring
  · -- m ≥ 0: vacuum killed; cbz index −m−1 < 0.
    rw [PreVertexAlgebra.smul_vacuum_nonneg _ _ hm, map_zero,
      cbz_apply_neg (-k) (by omega), zero_smul]

/-! ## The finite-range generalized-binomial Vandermonde core. -/

/-- **Finite-range Vandermonde.**  For `k ≥ 0` (so `(k+n).toNat = k+n` and `cbz(k+n,·)` truncates),
`∑_{i ≤ k+n} C(k+n,i)·C(−k, (n+j)−i) = C(n, n+j)`.  Convert the finite range to the `ℤ`-finsum
(the summand is supported in `[0, k+n]`) and apply `cbz_vandermonde` with `(k+n)+(−k) = n`. -/
theorem cbz_vandermonde_range (k : ℤ) (hk : 0 ≤ k) (n j : ℕ) :
    (∑ i ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
        cbz (k + (n : ℤ)) i * cbz (-k) ((n : ℤ) + (j : ℤ) - i))
      = cbz (n : ℤ) ((n : ℤ) + (j : ℤ)) := by
  have hconv : (∑ᶠ i : ℤ, cbz (k + (n : ℤ)) i * cbz (-k) ((n : ℤ) + (j : ℤ) - i))
      = ∑ g ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
          cbz (k + (n : ℤ)) ((0 : ℤ) + (g : ℤ)) * cbz (-k) ((n : ℤ) + (j : ℤ) - ((0 : ℤ) + g)) := by
    refine finsum_window
      (fun i : ℤ => cbz (k + (n : ℤ)) i * cbz (-k) ((n : ℤ) + (j : ℤ) - i))
      0 ((k + (n : ℤ)).toNat + 1) ?_
    intro i hi
    simp only [ne_eq, mul_eq_zero, not_or] at hi
    obtain ⟨hi1, _⟩ := hi
    -- support: cbz(k+n,i) ≠ 0 forces 0 ≤ i ≤ k+n
    refine ⟨?_, ?_⟩
    · by_contra hlt
      exact hi1 (cbz_apply_neg (k + (n : ℤ)) (by omega))
    · -- i ≤ k+n, so i < (k+n).toNat + 1
      by_contra hge
      simp only [not_lt] at hge
      have hibig : (k + (n : ℤ)) < i := by
        have : (k + (n : ℤ)).toNat + 1 ≤ i := by omega
        omega
      refine hi1 ?_
      -- gBinom (k+n) (i.toNat) = 0 since i.toNat > k+n ≥ 0
      rw [cbz_apply_nonneg (k + (n : ℤ)) (by omega), gBinom]
      rw [Finset.prod_eq_zero (i := (k + (n : ℤ)).toNat)
          (Finset.mem_range.mpr (by omega)) ?_, zero_div]
      have : (((k + (n : ℤ)).toNat : ℤ) : ℂ) = ((k + (n : ℤ) : ℤ) : ℂ) := by
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k + (n : ℤ))]
      push_cast at this ⊢
      rw [this]; ring
  have hv : cbz (n : ℤ) ((n : ℤ) + (j : ℤ))
      = ∑ᶠ i : ℤ, cbz (k + (n : ℤ)) i * cbz (-k) ((n : ℤ) + (j : ℤ) - i) := by
    rw [show (cbz (n : ℤ) ((n : ℤ) + (j : ℤ)))
          = cbz ((k + (n : ℤ)) + (-k)) ((n : ℤ) + (j : ℤ)) from by congr 1; ring]
    exact (cbz_mul_vandermonde (k + (n : ℤ)) (-k) ((n : ℤ) + (j : ℤ))).symm
  rw [hv, hconv]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 2 <;> ring

/-! ## The homogeneous right-unit coset identity (Vandermonde collapse). -/

/-- **Right unit on homogeneous `a`.**  `[a *ₙ 𝟙] = [a]` in `AnFull`.  Expand by
`leftProd_homogeneous`; replace each `[a₍m₎𝟙]` by `cbz (−k) (−m−1)·[a]`; the inner `i`-sum is the
generalized-binomial Vandermonde `∑_i C(k+n,i)·C(−k,(n+j)−i) = C(n,n+j)`, which is `δ_{j,0}` over
`j ∈ {0,…,n}`. -/
theorem leftProd_vacuum_right_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) :
    mkAnFull W n (leftProd W n a W.vacuum) = mkAnFull W n a := by
  -- If `k < 0`, the grade is trivial so `a = 0` and both sides vanish.
  rcases lt_or_ge k 0 with hk | hk
  · have ha0 : a = 0 := by
      have : a ∈ (⊥ : Submodule ℂ 𝒱) := W.positivity k hk ▸ ha
      simpa using this
    subst ha0
    rw [leftProd_zero_left]
  -- Now `k ≥ 0`.
  rw [leftProd_homogeneous W n ha W.vacuum, map_sum]
  -- Each j-summand collapses (via the finite Vandermonde) to `(−1)^j C(j+n,n) C(n,n+j) • [a]`.
  have hj : ∀ j ∈ Finset.range (n + 1),
      mkAnFull W n (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
          ∑ i ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
            cbz (k + (n : ℤ)) i • W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) W.vacuum)
        = (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) * cbz (n : ℤ) ((n : ℤ) + (j : ℤ)))
          • mkAnFull W n a := by
    intro j _
    rw [map_smul, map_sum]
    -- inner sum of [a₍i−(n+j+1)₎𝟙]
    have hinner : ∀ i ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
        mkAnFull W n (cbz (k + (n : ℤ)) i • W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) W.vacuum)
          = (cbz (k + (n : ℤ)) i * cbz (-k) ((n : ℤ) + (j : ℤ) - i)) • mkAnFull W n a := by
      intro i _
      rw [map_smul, mkAnFull_smul_vacuum_homog W n ha, smul_smul]
      congr 2
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_smul, cbz_vandermonde_range k hk n j,
      smul_smul]
  rw [Finset.sum_congr rfl hj, ← Finset.sum_smul]
  -- the j-sum `∑_j (−1)^j C(j+n,n) C(n,n+j)` collapses to `1` (only `j = 0` survives).
  rw [show (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) * cbz (n : ℤ) ((n : ℤ) + (j : ℤ))) = 1 from ?_,
    one_smul]
  rw [Finset.sum_eq_single 0]
  · -- j = 0 term: (−1)^0 C(n,n) C(n,n) = 1.
    simp only [Nat.cast_zero, pow_zero, zero_add, one_mul, add_zero]
    rw [cbz_natCast_eq_choose (le_refl n), Nat.choose_self, Nat.cast_one, mul_one]
  · -- j ≥ 1: C(n, n+j) = 0.
    intro j _ hj0
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have htoNat : ((n : ℤ) + (j : ℤ)).toNat = n + j := by omega
    have : cbz (n : ℤ) ((n : ℤ) + (j : ℤ)) = 0 := by
      rw [cbz_apply_nonneg (n : ℤ) (by omega), gBinom, htoNat]
      rw [Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr (by omega)) (by push_cast; ring),
        zero_div]
    rw [this, mul_zero]
  · intro hcontra
    exact absurd (Finset.mem_range.mpr (by omega)) hcontra

/-! ## The RIGHT unit law on `Aₙ(𝒱)`. -/

/-- **`[𝟙]` is a right unit in `Aₙ(𝒱)`.**  `AnFull.RightUnitLaw W n (anIdeal_holds W n)`:
`[a]·[𝟙] = [a]` for every class.  Reduce `a` to homogeneous via `reduce_homogeneous`, then apply
`leftProd_vacuum_right_homog`. -/
theorem AnFull.rightUnitLaw_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AnFull.RightUnitLaw W n (anIdeal_holds W n) := by
  intro a
  rw [AnFull.mul_mk]
  refine reduce_homogeneous W
    (P := fun a => mkAnFull W n (leftProd W n a W.vacuum) = mkAnFull W n a) ?_ ?_ ?_ a
  · intro k a ha; exact leftProd_vacuum_right_homog W n ha
  · simp only [leftProd_zero_left]
  · intro x y hx hy
    rw [leftProd_add_left, map_add, map_add, hx, hy]

/-- `[a]·[𝟙] = [a]` stated directly for the unconditional product `AnFull.mulU`. -/
@[simp] theorem AnFull.mulU_vacuum_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    AnFull.mulU W n (mkAnFull W n a) (mkAnFull W n W.vacuum) = mkAnFull W n a := by
  rw [AnFull.mulU, AnFull.rightUnitLaw_holds]

/-!
## Status

**Axiom-clean (`[propext, Classical.choice, Quot.sound]`):**
* `mkAnFull_Lgen_eq_zero`, `mkAnFull_L_neg_one_homog`, `mkAnFull_T_homog`, `Tpow_mem_grading`,
  `mkAnFull_Tpow_homog` — the `O^L`-coset calculus for `L₋₁`/`T` translates.
* `mkAnFull_smul_vacuum_homog` — `[a₍m₎𝟙] = C(−k, −m−1)·[a]` for `a ∈ 𝒱_k`.
* `cbz_vandermonde_range` — the finite-range generalized-binomial Vandermonde
  `∑_{i ≤ k+n} C(k+n,i)·C(−k,(n+j)−i) = C(n, n+j)` (`k ≥ 0`).
* `leftProd_vacuum_right_homog` — `[a *ₙ 𝟙] = [a]` for homogeneous `a`.
* `AnFull.rightUnitLaw_holds` — `AnFull.RightUnitLaw W n (anIdeal_holds W n)`, i.e. `[a]·[𝟙]=[a]`.
* `AnFull.mulU_vacuum_right` — the same for the unconditional product `AnFull.mulU`.

Together with `AnFull.leftUnitLaw_holds` (`ZhuVermaAnArchUnits.lean`), `[𝟙]` is the **two-sided
unit** of `Aₙ(𝒱) = 𝒱/Oₙ(𝒱)`.
-/

end VOA

/-
`#print axioms` gate (all `[propext, Classical.choice, Quot.sound]`; NO `pbw`, NO `sorryAx`):

  #print axioms VOA.AnFull.rightUnitLaw_holds
  #print axioms VOA.AnFull.mulU_vacuum_right
  #print axioms VOA.leftProd_vacuum_right_homog
  #print axioms VOA.cbz_vandermonde_range
  #print axioms VOA.mkAnFull_smul_vacuum_homog
-/
