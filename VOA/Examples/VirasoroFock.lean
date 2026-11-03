/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergVirasoro
import VOA.Examples.HeisenbergCentral
import VOA.Foundations.VirasoroModule

/-!
# The linear-dilaton free-boson realization of `Vir(c)`

The **background-charge** (Feigin–Fuks / linear-dilaton) modification of the level-`1` free-boson
Sugawara modes: `Lₙ^λ = Lₙ + λ(n+1)aₙ`.  These obey the Virasoro relation with central charge
`c = 1 − 12λ²` — so for **any** `c ∈ ℂ` the choice `λ = √((1−c)/12)` gives a concrete Virasoro
representation of central charge `c` on the free-boson Fock space, with a manifestly-nonzero
highest-weight vacuum.  This is the pbw-free witness that the universal vacuum module `VirUniv c` is
nontrivial (`Foundations/VirasoroModule`): the universal map `VirUniv c → Fock` sends
`|0⟩ ↦ 1 ≠ 0`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

namespace VOA

open Module (End)

/-! ## §A  The linear-dilaton modes `Lₙ^λ = Lₙ + λ(n+1)aₙ`. -/

/-- The **linear-dilaton (background-charge) Virasoro mode** `Lₙ^λ = Lₙ + λ(n+1)aₙ` on the level-`1`
free-boson Fock space (`λ` the background charge). -/
noncomputable def Lld (lam : ℂ) (n : ℤ) : End ℂ Fock :=
  Lvir 1 n + (lam * ((n : ℂ) + 1)) • osc 1 n

/-- **The linear-dilaton Virasoro relation**, central charge `c = 1 − 12λ²`:
`[Lₘ^λ, Lₙ^λ] = (m−n)L_{m+n}^λ + δ_{m+n,0}·(m³−m)/12·(1−12λ²)`. -/
theorem Lld_virasoro (lam : ℂ) (m n : ℤ) :
    Lld lam m * Lld lam n - Lld lam n * Lld lam m
      = ((m : ℂ) - n) • Lld lam (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * (1 - 12 * lam ^ 2) else 0)
            • (LinearMap.id : End ℂ Fock) := by
  -- expand the bracket into the four sub-commutators
  have hexpand : Lld lam m * Lld lam n - Lld lam n * Lld lam m
      = (Lvir 1 m * Lvir 1 n - Lvir 1 n * Lvir 1 m)
        + (lam * ((n : ℂ) + 1)) • (Lvir 1 m * osc 1 n - osc 1 n * Lvir 1 m)
        + (lam * ((m : ℂ) + 1)) • (osc 1 m * Lvir 1 n - Lvir 1 n * osc 1 m)
        + ((lam * ((m : ℂ) + 1)) * (lam * ((n : ℂ) + 1)))
            • (osc 1 m * osc 1 n - osc 1 n * osc 1 m) := by
    simp only [Lld, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module
  -- the [osc, Lvir] cross bracket, rewritten as `+m • osc_{m+n}`
  have hBC : osc 1 m * Lvir 1 n - Lvir 1 n * osc 1 m = (m : ℂ) • osc 1 (m + n) := by
    have h := L_comm_osc 1 one_ne_zero n m
    rw [add_comm n m] at h
    rw [← neg_sub, h]
    module
  rw [hexpand, L_virasoro 1 one_ne_zero m n, L_comm_osc 1 one_ne_zero m n, hBC, osc_comm 1 m n]
  -- combine: match the `Lvir`, `osc`, and central `id` pieces
  by_cases hmn : m + n = 0
  · obtain rfl : n = -m := by omega
    have h0 : m + -m = (0 : ℤ) := by ring
    rw [if_pos h0, if_pos h0, if_pos h0, h0, Lld, osc_zero]
    push_cast
    module
  · rw [if_neg hmn, if_neg hmn, if_neg hmn, Lld]
    push_cast
    module

/-! ## §B  The highest-weight vacuum and its nonvanishing. -/

/-- The linear-dilaton modes annihilate the vacuum for `n ≥ -1`: `Lₙ^λ|0⟩ = 0`
(the coefficient `λ(n+1)` kills the `n = -1` oscillator term, and `Lₙ|0⟩ = 0` for `n ≥ -1`). -/
theorem Lld_vacuum (lam : ℂ) {n : ℤ} (hn : -1 ≤ n) : Lld lam n vacuum = 0 := by
  rw [Lld, LinearMap.add_apply, Lvir_vacuum 1 hn, LinearMap.smul_apply]
  rcases eq_or_lt_of_le hn with h | h
  · -- n = -1: coefficient `λ(n+1) = 0`
    rw [← h]
    norm_num
  · -- n ≥ 0: `aₙ|0⟩ = 0`
    rw [osc_vacuum 1 n (by omega), smul_zero, zero_add]

/-- The free-boson vacuum is nonzero (`|0⟩ = 1 ≠ 0` in the polynomial Fock space). -/
theorem vacuum_ne_zero : (vacuum : Fock) ≠ 0 := by
  rw [vacuum]; exact one_ne_zero

end VOA
