/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnIdeal

/-!
# The `A_n(𝒱)` unit law: `[𝟙]` is the identity (Dong–Li–Mason Thm 2.3).

The file `ZhuVermaAnArchAnIdeal.lean` proves the unconditional 2-sided ideal
`anIdeal_holds : AnIdeal W n` and hence the well-defined product `AnFull.mulU` on `Aₙ(𝒱)`.
This file discharges the **LEFT unit law** `[𝟙]·[a] = [a]` (`AnFull.LeftUnitLaw`) at the SHARP
representative level: `𝟙 *ₙ a = a` **exactly** (not just mod `Oₙ`), and packages it as the
`Prop` `AnFull.LeftUnitLaw W n (anIdeal_holds W n)`.

## Mathematical content (the LEFT unit is exact)

The vacuum `𝟙 = W.vacuum` is homogeneous of grade `0`.  Expanding `leftProd W n 𝟙 a` via
`leftProd_homogeneous` (with `k = 0`) gives the FZ double sum

  `∑_{j=0}^{n} (-1)^j C(j+n,n) · ∑_{i=0}^{n} C(n,i) · 𝟙₍i-(n+j+1)₎ a`.

By VA2 (`smul_vacuum_left`), `𝟙₍m₎ a = δ_{m,-1} a`, so the mode survives only when
`i - (n+j+1) = -1`, i.e. `i = n + j`.  With `0 ≤ i ≤ n` and `0 ≤ j ≤ n` this forces `j = 0` and
`i = n`, and the surviving coefficient is `(-1)^0 C(n,n) · C(n,n) = 1`.  Hence `𝟙 *ₙ a = a`.

This is the depth-`n` lift of the `n = 0` Zhu unit `zhuMul_vacuum_left`.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `leftProd_vacuum_left` — the SHARP representative identity `𝟙 *ₙ a = a`.
* `AnFull.leftUnitLaw_holds` — `AnFull.LeftUnitLaw W n (anIdeal_holds W n)`
  (`[𝟙]·[a] = [a]` in `Aₙ`).
* `AnFull.mulU_vacuum_left` — `[𝟙]·[a] = [a]` for `AnFull.mulU` directly.

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (`q-alg/9612010`), Thm 2.3; Frenkel–Zhu, Duke 66 (1992);
Zhu, J. AMS 9 (1996); Gannon §5.3.2 Thm 5.3.4 (cf. `ZhuAlgebra.zhuMul_vacuum_left`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The SHARP left unit `𝟙 *ₙ a = a` (exact, not merely mod `Oₙ`). -/

/-- **Left unit (sharp).**  The vacuum is a *strict* left unit for the FZ product `*ₙ = leftProd`:
`𝟙 *ₙ a = a` **exactly**, for every `a` and every level `n`.  (The depth-`n` lift of the `n = 0`
Zhu unit `zhuMul_vacuum_left`.)  Proof: the vacuum is homogeneous of grade `0`, so
`leftProd_homogeneous` exhibits `𝟙 *ₙ a` as a double sum `∑_j ∑_i …·𝟙₍i-(n+j+1)₎a`; VA2 kills every
mode except `i - (n+j+1) = -1`, i.e. only the `j = 0, i = n` term survives with coefficient `1`. -/
theorem leftProd_vacuum_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    leftProd W n W.vacuum a = a := by
  rw [leftProd_homogeneous W n W.vacuum_mem a]
  -- Outer sum over `j`; only `j = 0` survives (inner sum is `0` for `j ≥ 1`).
  rw [Finset.sum_eq_single (0 : ℕ)]
  · -- The `j = 0` term: scalar `(-1)^0 · C(0+n,n) = 1`.
    simp only [Nat.cast_zero, pow_zero, zero_add, one_mul]
    rw [cbz_natCast_eq_choose (le_refl n), Nat.choose_self, Nat.cast_one, one_smul]
    -- Inner sum over `i ∈ range (n+1)`; only `i = n` survives, with `mode = -1`.
    rw [Finset.sum_eq_single (n : ℕ)]
    · -- `i = n`: `C(n,n) = 1` and `𝟙₍n-(n+0+1)₎a = 𝟙₍-1₎a = a`.
      rw [cbz_natCast_eq_choose (le_refl n), Nat.choose_self, Nat.cast_one, one_smul,
        show ((n : ℤ) - ((n : ℤ) + (0 : ℤ) + 1)) = (-1 : ℤ) from by ring,
        PreVertexAlgebra.smul_vacuum_left, if_pos rfl]
    · -- `i ≠ n` in range: mode index `i - (n+0+1) ≠ -1`, so `𝟙₍·₎a = 0`.
      intro i hi hin
      have hir : (i : ℕ) ≤ n := by
        have := Finset.mem_range.mp hi
        omega
      rw [show ((i : ℤ) - ((n : ℤ) + (0 : ℤ) + 1)) = (i : ℤ) - (n : ℤ) - 1 from by ring]
      rw [PreVertexAlgebra.smul_vacuum_left, if_neg (by
        have : (i : ℤ) ≠ (n : ℤ) := by exact_mod_cast hin
        omega), smul_zero]
    · -- `i = n` is in range `n+1`.
      intro hcontra
      exact absurd (Finset.mem_range.mpr (by omega)) hcontra
  · -- `j ≠ 0` in range: the whole inner sum vanishes (no `i ∈ {0,…,n}` reaches mode `-1`).
    intro j hj hj0
    have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hjr : j ≤ n := by
      have := Finset.mem_range.mp hj
      omega
    refine smul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun i hi => ?_
    have hir : (i : ℕ) ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    -- mode index `i - (n+j+1)`; need `≠ -1`, i.e. `i ≠ n+j`.  But `i ≤ n < n+j`.
    rw [PreVertexAlgebra.smul_vacuum_left, if_neg (by
      have : (i : ℤ) ≤ (n : ℤ) := by exact_mod_cast hir
      have : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hjpos
      omega), smul_zero]
  · -- `j = 0` is in range `n+1`.
    intro hcontra
    exact absurd (Finset.mem_range.mpr (by omega)) hcontra

/-! ## The LEFT unit law on `Aₙ(𝒱)`. -/

/-- **`[𝟙]` is a left unit in `Aₙ(𝒱)`.**  `AnFull.LeftUnitLaw W n (anIdeal_holds W n)`:
`[𝟙] · [a] = [a]` for every class.  Immediate from the sharp representative identity
`leftProd_vacuum_left` (which is exact, so descends trivially to the quotient). -/
theorem AnFull.leftUnitLaw_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AnFull.LeftUnitLaw W n (anIdeal_holds W n) := by
  intro a
  rw [AnFull.mul_mk, leftProd_vacuum_left]

/-- `[𝟙] · [a] = [a]` stated directly for the unconditional product `AnFull.mulU`. -/
@[simp] theorem AnFull.mulU_vacuum_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    AnFull.mulU W n (mkAnFull W n W.vacuum) (mkAnFull W n a) = mkAnFull W n a := by
  rw [AnFull.mulU, AnFull.leftUnitLaw_holds]

/-!
## Status

**Axiom-clean (`[propext, Classical.choice, Quot.sound]`):**
* `leftProd_vacuum_left` — the SHARP left unit `𝟙 *ₙ a = a` (exact, all `n`); depth-`n` lift of
  `zhuMul_vacuum_left`.
* `AnFull.leftUnitLaw_holds` — `AnFull.LeftUnitLaw W n (anIdeal_holds W n)`, i.e. `[𝟙]·[a]=[a]` in
  `Aₙ(𝒱)`.
* `AnFull.mulU_vacuum_left` — the same for the unconditional product `AnFull.mulU`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.leftProd_vacuum_left
  #print axioms VOA.AnFull.leftUnitLaw_holds
  #print axioms VOA.AnFull.mulU_vacuum_left
-/
