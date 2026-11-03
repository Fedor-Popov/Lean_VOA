/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Examples.VirasoroGrading
import VOA.Examples.VirasoroSpanning
import VOA.Examples.VirasoroNonvanishing
import VOA.Examples.VirasoroVOA

/-!
# The Lee–Yang singular vector, derived

The `(2,5)` Virasoro minimal model ("Lee–Yang") is the smallest nontrivial minimal model, with
central charge `c = 1 - 6(2-5)²/(2·5) = -22/5` and a singular vector at **level 4** in the
universal vacuum module `V(c,0) = VirUniv c = U(𝔙𝔦𝔯)/J(c)`.

Nothing here is quoted from the literature: the central charge is *derived*.  We identify the
level-4 subspace, impose `L₁s = L₂s = 0` on a general level-4 vector `s = α L₋₂²|0⟩ + β L₋₄|0⟩`,
and find that the resulting `2 × 2` homogeneous system

    3α + 5β = 0 ,      (c + 8)α + 6β = 0

has a nonzero solution **iff** its determinant `3·6 - 5(c+8) = -(5c+22)` vanishes, i.e. iff
`c = -22/5`.  The singular vector is then `5 L₋₂²|0⟩ - 3 L₋₄|0⟩`.

## Main results

* `energyVir_eq_four_iff`, `gradingVir_four` — the level-4 subspace of `VirUniv c` is spanned by
  `L₋₂L₋₂|0⟩` and `L₋₄|0⟩`; the naive third candidate collapses (`Lop_neg_three_neg_one_vac`).
* `Lop_one_comb`, `Lop_two_comb` — the two singularity equations
  `L₁s = (3α+5β)L₋₃|0⟩` and `L₂s = ((c+8)α+6β)L₋₂|0⟩`.
* `Lop_pos_ann` — `L₁` and `L₂` generate the positive part: `L₁s = L₂s = 0 ⟹ Lₙs = 0` for `n ≥ 1`.
* `level4_indep`, `L2vac_ne_zero`, `L3vac_ne_zero` — `pbw`-free nonvanishing and independence, via
  the linear-dilaton free-boson realization of `Examples/VirasoroNonvanishing`.
* `exists_level4_singular_iff` — **a nonzero level-4 singular vector exists iff `c = -22/5`.**
* `minimalCentralCharge_leeYang` — `minimalCentralCharge 2 5 = -22/5`, matching the derivation.
* `leeYangSingular` — the explicit vector `5L₋₂²|0⟩ - 3L₋₄|0⟩` of `VirUniv (-22/5)`, together with
  `leeYangSingular_ne_zero`, `leeYangSingular_annihilated`, `leeYangSingular_L0`,
  `leeYangSingular_ne_smul_vacVec`, `leeYangSubmodule_ne_bot`.

## Convention note

Everything here is stated for `VirModule.VirUniv c`, which is the **universal**
vacuum module `V(c,0) = U(𝔙𝔦𝔯)/J(c)`, not the simple quotient (`L(c,0)` denotes the
*simple* quotient).  Every statement of this file is about the universal object: `L2vac`, `L3vac`, `L2L2vac`, `L4vac`, `gradingVir_four`,
`level4_indep`, `exists_level4_singular_iff` and `leeYangSingular` all live in `V(c,0)`.  That is
the point of the file: `leeYangSingular ≠ 0` in `V(-22/5,0)` is exactly what makes the simple
quotient `L(-22/5,0)` differ from `V(-22/5,0)`.

`sorry`-free, no new axioms, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LeeYang

open VOA
open VOA.VirModule
open Module (End)
open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra
open MvPolynomial (X aeval)

/-! ## §0  A scalar-cancellation helper. -/

/-- In a `ℂ`-module a nonzero scalar cancels. -/
theorem eq_zero_of_smul_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {t : ℂ} {v : V}
    (ht : t ≠ 0) (h : t • v = 0) : v = 0 := by
  have h2 := congrArg (fun w : V => t⁻¹ • w) h
  simpa [smul_smul, inv_mul_cancel₀ ht] using h2

/-! ## §1  The level-4 subspace of the vacuum module.

In `VirUniv c` one has `L₋₁|0⟩ = 0`, so the only creation words of energy `4` are `[2]` (giving
`L₋₄|0⟩`) and `[0,0]` (giving `L₋₂L₋₂|0⟩`).  The naive third candidate `L₋₃L₋₁|0⟩` collapses. -/

variable (c : ℂ)

/-- `L₋₂|0⟩` (`= ω`, the conformal vector). -/
noncomputable def L2vac : VirUniv c := Lop c (-2) (vacVec c)

/-- `L₋₃|0⟩`, the level-3 state. -/
noncomputable def L3vac : VirUniv c := Lop c (-3) (vacVec c)

/-- `L₋₂L₋₂|0⟩`, the first level-4 state. -/
noncomputable def L2L2vac : VirUniv c := Lop c (-2) (Lop c (-2) (vacVec c))

/-- `L₋₄|0⟩`, the second level-4 state. -/
noncomputable def L4vac : VirUniv c := Lop c (-4) (vacVec c)

/-- **The `L₋₃L₋₁|0⟩` collapse**: in the vacuum module `L₋₁|0⟩ = 0`, so this naive level-4
candidate vanishes and the level-4 space is only two-dimensional. -/
theorem Lop_neg_three_neg_one_vac : Lop c (-3) (Lop c (-1) (vacVec c)) = 0 := by
  rw [Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ -1), map_zero]

/-- The creation words of energy `4` are exactly `[2]` and `[0,0]` (each entry `i` contributes
`i + 2 ≥ 2`, so a word of energy `4` has length `1` or `2`). -/
theorem energyVir_eq_four {ws : List ℕ} (h : energyVir ws = 4) : ws = [2] ∨ ws = [0, 0] := by
  match ws with
  | [] => exact absurd h (by decide)
  | [i] =>
      rw [energyVir_cons, energyVir_nil] at h
      have hi : i = 2 := by omega
      exact Or.inl (by rw [hi])
  | [i, j] =>
      rw [energyVir_cons, energyVir_cons, energyVir_nil] at h
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      exact Or.inr (by rw [hi, hj])
  | (i :: j :: k :: rest) =>
      exfalso
      rw [energyVir_cons, energyVir_cons, energyVir_cons] at h
      omega

/-- The energy-`4` words, as an iff. -/
theorem energyVir_eq_four_iff (ws : List ℕ) : energyVir ws = 4 ↔ ws = [2] ∨ ws = [0, 0] := by
  refine ⟨fun h => energyVir_eq_four h, ?_⟩
  rintro (rfl | rfl) <;> rfl

theorem negWordVir_two : negWordVir c [2] = L4vac c := by
  have h : (-((2 : ℕ) : ℤ) - 2) = -4 := by norm_num
  rw [negWordVir_cons, negWordVir_nil, h, L4vac]

theorem negWordVir_zero_zero : negWordVir c [0, 0] = L2L2vac c := by
  have h : (-((0 : ℕ) : ℤ) - 2) = -2 := by norm_num
  rw [negWordVir_cons, negWordVir_cons, negWordVir_nil, h, L2L2vac]

/-- **The level-4 subspace** of `VirUniv c` is spanned by `L₋₂L₋₂|0⟩` and `L₋₄|0⟩`. -/
theorem gradingVir_four : gradingVir c 4 = Submodule.span ℂ {L2L2vac c, L4vac c} := by
  rw [gradingVir]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ws, hen, rfl⟩
    have h4 : energyVir ws = 4 := by exact_mod_cast hen
    rcases energyVir_eq_four h4 with rfl | rfl
    · exact Or.inr (negWordVir_two c)
    · exact Or.inl (negWordVir_zero_zero c)
  · rintro (rfl | rfl)
    · exact ⟨[0, 0], by norm_num [energyVir], negWordVir_zero_zero c⟩
    · exact ⟨[2], by norm_num [energyVir], negWordVir_two c⟩

theorem L2L2vac_mem_grading : L2L2vac c ∈ gradingVir c 4 := by
  rw [gradingVir_four]
  exact Submodule.subset_span (Set.mem_insert _ _)

theorem L4vac_mem_grading : L4vac c ∈ gradingVir c 4 := by
  rw [gradingVir_four]
  exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

/-! ## §2  The Virasoro commutator in applied form. -/

/-- The Virasoro relation, applied to a vector:
`Lₘ(Lₙ w) = Lₙ(Lₘ w) + (m-n)L_{m+n} w + δ_{m+n,0}((m³-m)/12)c·w`. -/
theorem Lop_apply_comm (m n : ℤ) (w : VirUniv c) :
    Lop c m (Lop c n w)
      = Lop c n (Lop c m w) + ((m : ℂ) - n) • Lop c (m + n) w
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * c else 0) • w := by
  have h := congrArg (fun T : End ℂ (VirUniv c) => T w) (Lop_bracket c m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  rw [eq_add_of_sub_eq h]
  module

/-! ## §3  The Virasoro modes on the level-≤4 states.

Pure Virasoro bookkeeping: `Lₙ|0⟩ = 0` for `n ≥ -1` kills every boundary term, and the only
central contribution is the `c/2` inside `[L₂, L₋₂]`. -/

/-- `L₋₁L₋₂|0⟩ = L₋₃|0⟩`. -/
theorem Lop_neg_one_L2vac : Lop c (-1) (L2vac c) = L3vac c := by
  have h := Lop_apply_comm c (-1) (-2) (vacVec c)
  rw [if_neg (by norm_num : ¬((-1 : ℤ) + -2 = 0)), zero_smul,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ -1), map_zero,
    show (-1 : ℤ) + -2 = -3 from by norm_num] at h
  push_cast at h
  simp only [L2vac, L3vac]
  rw [h]
  module

/-- `L₀L₋₂|0⟩ = 2L₋₂|0⟩` (the conformal vector has weight `2`). -/
theorem Lop_zero_L2vac : Lop c 0 (L2vac c) = (2 : ℂ) • L2vac c := by
  have h := Lop_apply_comm c 0 (-2) (vacVec c)
  rw [if_neg (by norm_num : ¬((0 : ℤ) + -2 = 0)), zero_smul,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
    show (0 : ℤ) + -2 = -2 from by norm_num] at h
  push_cast at h
  simp only [L2vac]
  rw [h]
  module

/-- `L₁L₋₂|0⟩ = 0`. -/
theorem Lop_one_L2vac : Lop c 1 (L2vac c) = 0 := by
  have h := Lop_apply_comm c 1 (-2) (vacVec c)
  rw [if_neg (by norm_num : ¬((1 : ℤ) + -2 = 0)), zero_smul,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 1), map_zero,
    show (1 : ℤ) + -2 = -1 from by norm_num,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ -1), smul_zero] at h
  simp only [L2vac]
  rw [h]
  module

/-- `L₂L₋₂|0⟩ = (c/2)|0⟩` — the central term, the only place the central charge enters. -/
theorem Lop_two_L2vac : Lop c 2 (L2vac c) = (c / 2) • vacVec c := by
  have h := Lop_apply_comm c 2 (-2) (vacVec c)
  rw [if_pos (by norm_num : (2 : ℤ) + -2 = 0),
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 2), map_zero,
    show (2 : ℤ) + -2 = 0 from by norm_num,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 0), smul_zero] at h
  push_cast at h
  simp only [L2vac]
  rw [h]
  module

/-- `L₁L₋₂L₋₂|0⟩ = 3L₋₃|0⟩`. -/
theorem Lop_one_L2L2vac : Lop c 1 (L2L2vac c) = (3 : ℂ) • L3vac c := by
  have h := Lop_apply_comm c 1 (-2) (L2vac c)
  rw [Lop_one_L2vac, map_zero, if_neg (by norm_num : ¬((1 : ℤ) + -2 = 0)), zero_smul,
    show (1 : ℤ) + -2 = -1 from by norm_num, Lop_neg_one_L2vac] at h
  push_cast at h
  simp only [L2vac, L2L2vac, L3vac] at h ⊢
  rw [h]
  module

/-- `L₁L₋₄|0⟩ = 5L₋₃|0⟩`. -/
theorem Lop_one_L4vac : Lop c 1 (L4vac c) = (5 : ℂ) • L3vac c := by
  have h := Lop_apply_comm c 1 (-4) (vacVec c)
  rw [if_neg (by norm_num : ¬((1 : ℤ) + -4 = 0)), zero_smul,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 1), map_zero,
    show (1 : ℤ) + -4 = -3 from by norm_num] at h
  push_cast at h
  simp only [L4vac, L3vac]
  rw [h]
  module

/-- `L₂L₋₂L₋₂|0⟩ = (c+8)L₋₂|0⟩` — the coefficient in which the central charge survives. -/
theorem Lop_two_L2L2vac : Lop c 2 (L2L2vac c) = (c + 8) • L2vac c := by
  have h := Lop_apply_comm c 2 (-2) (L2vac c)
  rw [if_pos (by norm_num : (2 : ℤ) + -2 = 0), Lop_two_L2vac,
    show (2 : ℤ) + -2 = 0 from by norm_num, Lop_zero_L2vac, map_smul] at h
  push_cast at h
  simp only [L2vac, L2L2vac] at h ⊢
  rw [h]
  module

/-- `L₂L₋₄|0⟩ = 6L₋₂|0⟩`. -/
theorem Lop_two_L4vac : Lop c 2 (L4vac c) = (6 : ℂ) • L2vac c := by
  have h := Lop_apply_comm c 2 (-4) (vacVec c)
  rw [if_neg (by norm_num : ¬((2 : ℤ) + -4 = 0)), zero_smul,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 2), map_zero,
    show (2 : ℤ) + -4 = -2 from by norm_num] at h
  push_cast at h
  simp only [L4vac, L2vac]
  rw [h]
  module

/-- `L₀L₋₂L₋₂|0⟩ = 4L₋₂L₋₂|0⟩`. -/
theorem Lop_zero_L2L2vac : Lop c 0 (L2L2vac c) = (4 : ℂ) • L2L2vac c := by
  have h := Lop_apply_comm c 0 (-2) (L2vac c)
  rw [if_neg (by norm_num : ¬((0 : ℤ) + -2 = 0)), zero_smul, Lop_zero_L2vac,
    show (0 : ℤ) + -2 = -2 from by norm_num, map_smul] at h
  push_cast at h
  simp only [L2vac, L2L2vac] at h ⊢
  rw [h]
  module

/-- `L₀L₋₄|0⟩ = 4L₋₄|0⟩`. -/
theorem Lop_zero_L4vac : Lop c 0 (L4vac c) = (4 : ℂ) • L4vac c := by
  have h := Lop_apply_comm c 0 (-4) (vacVec c)
  rw [if_neg (by norm_num : ¬((0 : ℤ) + -4 = 0)), zero_smul,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
    show (0 : ℤ) + -4 = -4 from by norm_num] at h
  push_cast at h
  simp only [L4vac]
  rw [h]
  module

/-! ## §4  The two singularity equations. -/

/-- **The `L₁` equation.**  For `s = α L₋₂²|0⟩ + β L₋₄|0⟩`, `L₁ s = (3α + 5β) L₋₃|0⟩`. -/
theorem Lop_one_comb (α β : ℂ) :
    Lop c 1 (α • L2L2vac c + β • L4vac c) = (3 * α + 5 * β) • L3vac c := by
  rw [map_add, map_smul, map_smul, Lop_one_L2L2vac, Lop_one_L4vac]
  module

/-- **The `L₂` equation.**  For `s = α L₋₂²|0⟩ + β L₋₄|0⟩`, `L₂ s = ((c+8)α + 6β) L₋₂|0⟩`. -/
theorem Lop_two_comb (α β : ℂ) :
    Lop c 2 (α • L2L2vac c + β • L4vac c) = ((c + 8) * α + 6 * β) • L2vac c := by
  rw [map_add, map_smul, map_smul, Lop_two_L2L2vac, Lop_two_L4vac]
  module

/-- Every level-4 vector is an `L₀`-eigenvector of eigenvalue `4`. -/
theorem Lop_zero_comb (α β : ℂ) :
    Lop c 0 (α • L2L2vac c + β • L4vac c) = (4 : ℂ) • (α • L2L2vac c + β • L4vac c) := by
  rw [map_add, map_smul, map_smul, Lop_zero_L2L2vac, Lop_zero_L4vac]
  module

/-! ## §5  `L₁` and `L₂` generate the positive part.

For `n ≥ 3` one has `[L₁, L_{n-1}] = (2-n)Lₙ` with `2-n ≠ 0` and no central term (since
`1 + (n-1) = n ≠ 0`), so `L₁s = L₂s = 0` propagates upwards. -/

/-- Two-step induction behind `Lop_pos_ann`. -/
theorem Lop_pos_ann_aux {s : VirUniv c} (h1 : Lop c 1 s = 0) (h2 : Lop c 2 s = 0) (m : ℕ) :
    Lop c ((m : ℤ) + 1) s = 0 ∧ Lop c ((m : ℤ) + 2) s = 0 := by
  induction m with
  | zero => exact ⟨by simpa using h1, by simpa using h2⟩
  | succ k ih =>
      constructor
      · rw [show ((k + 1 : ℕ) : ℤ) + 1 = (k : ℤ) + 2 from by push_cast; ring]
        exact ih.2
      · have hb := Lop_apply_comm c 1 ((k : ℤ) + 2) s
        rw [ih.2, h1, map_zero, map_zero, zero_add,
          if_neg (by omega : ¬((1 : ℤ) + ((k : ℤ) + 2) = 0)), zero_smul, add_zero,
          show (1 : ℤ) + ((k : ℤ) + 2) = (k : ℤ) + 3 from by ring] at hb
        have hne : (((1 : ℤ) : ℂ) - (((k : ℤ) + 2 : ℤ) : ℂ)) ≠ 0 := by
          have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
          have hrw : (((1 : ℤ) : ℂ) - (((k : ℤ) + 2 : ℤ) : ℂ)) = -((k + 1 : ℕ) : ℂ) := by
            push_cast; ring
          rw [hrw]
          exact neg_ne_zero.mpr hk
        rw [show ((k + 1 : ℕ) : ℤ) + 2 = (k : ℤ) + 3 from by push_cast; ring]
        exact eq_zero_of_smul_eq_zero hne hb.symm

/-- **`L₁` and `L₂` generate**: `L₁s = L₂s = 0 ⟹ Lₙ s = 0` for every `n ≥ 1`. -/
theorem Lop_pos_ann {s : VirUniv c} (h1 : Lop c 1 s = 0) (h2 : Lop c 2 s = 0) {n : ℤ}
    (hn : 1 ≤ n) : Lop c n s = 0 := by
  have h := (Lop_pos_ann_aux c h1 h2 (n - 1).toNat).1
  rwa [show (((n - 1).toNat : ℤ) + 1) = n from by omega] at h

/-! ## §6  `pbw`-free nonvanishing, via the linear-dilaton free boson.

`Examples/VirasoroNonvanishing` realizes **every** central charge `c = 1 - 12λ²` on the free-boson
Fock space `Fock = ℂ[X₀,X₁,…]` (with `Xᵢ ↔ a₋ᵢ₋₁`).  The universal map `U(𝔙𝔦𝔯) → End Fock` kills
the vacuum ideal `J(c)`, so every relation in `VirUniv c` becomes a polynomial identity, which we
test by evaluating the variables.  This gives two-dimensionality of the level-4 space with no PBW
input. -/

section FockCalc

/-- `|0⟩ = 1` in the polynomial Fock space. -/
theorem vacuum_one : (vacuum : Fock) = 1 := rfl

/-- `a₋₁ p = X₀ · p`. -/
theorem osc_m1 (p : Fock) : osc 1 (-1) p = X 0 * p := by
  rw [osc_apply_neg 1 (by norm_num) p]; norm_num

/-- `a₋₂ p = X₁ · p`. -/
theorem osc_m2 (p : Fock) : osc 1 (-2) p = X 1 * p := by
  rw [osc_apply_neg 1 (by norm_num) p]; norm_num

/-- The generic creation rule `a₋ᵢ₋₁ p = Xᵢ · p`. -/
theorem osc_X (i : ℕ) (p : Fock) : osc 1 (-(i : ℤ) - 1) p = X i * p := by
  have hi : (-(-(i : ℤ) - 1) - 1).toNat = i := by omega
  rw [osc_apply_neg 1 (by omega) p, hi]

/-- Moving `L₋₁` past a creation operator: `L₋₁(Xᵢ y) = (i+1)X_{i+1} y + Xᵢ L₋₁ y`. -/
theorem Lvir_m1_X (i j : ℕ) (hj : j = i + 1) (y : Fock) :
    Lvir 1 (-1) (X i * y) = ((i : ℂ) + 1) • (X j * y) + X i * Lvir 1 (-1) y := by
  subst hj
  have h := Lvir_osc 1 one_ne_zero (-1) (-(i : ℤ) - 1) y
  rw [show (-1 : ℤ) + (-(i : ℤ) - 1) = -((i + 1 : ℕ) : ℤ) - 1 from by push_cast; ring] at h
  rw [osc_X i y, osc_X (i + 1) y, osc_X i (Lvir 1 (-1) y)] at h
  rw [h, show (-((-(i : ℤ) - 1 : ℤ) : ℂ)) = (i : ℂ) + 1 from by push_cast; ring]

/-- Moving `L₋₂` past a creation operator: `L₋₂(Xᵢ y) = (i+1)X_{i+2} y + Xᵢ L₋₂ y`. -/
theorem Lvir_m2_X (i j : ℕ) (hj : j = i + 2) (y : Fock) :
    Lvir 1 (-2) (X i * y) = ((i : ℂ) + 1) • (X j * y) + X i * Lvir 1 (-2) y := by
  subst hj
  have h := Lvir_osc 1 one_ne_zero (-2) (-(i : ℤ) - 1) y
  rw [show (-2 : ℤ) + (-(i : ℤ) - 1) = -((i + 2 : ℕ) : ℤ) - 1 from by push_cast; ring] at h
  rw [osc_X i y, osc_X (i + 2) y, osc_X i (Lvir 1 (-2) y)] at h
  rw [h, show (-((-(i : ℤ) - 1 : ℤ) : ℂ)) = (i : ℂ) + 1 from by push_cast; ring]

/-! ### The base values on `|0⟩ = 1`. -/

theorem Lvir_one_m1 : Lvir 1 (-1) (1 : Fock) = 0 := Lvir_vacuum 1 (by norm_num)

theorem Lvir_one_m2 : Lvir 1 (-2) (1 : Fock) = (2⁻¹ : ℂ) • ((X 0 : Fock) * X 0) := by
  have h : Lvir 1 (-2) (1 : Fock) = VOA.ω 1 := Lvir_neg_two_vacuum 1
  rw [h, VOA.ω, osc_m1, osc_m1, vacuum_one, mul_one]
  norm_num

/-! ### `L₋₁` and `L₋₂` on the low monomials. -/

theorem fock_B0 : Lvir 1 (-1) (X 0 : Fock) = X 1 := by
  have h := Lvir_m1_X 0 1 rfl (1 : Fock)
  rw [mul_one, mul_one, Lvir_one_m1, mul_zero, add_zero] at h
  rw [h]; norm_num

theorem fock_B1 : Lvir 1 (-1) (X 1 : Fock) = (2 : ℂ) • (X 2 : Fock) := by
  have h := Lvir_m1_X 1 2 rfl (1 : Fock)
  rw [mul_one, mul_one, Lvir_one_m1, mul_zero, add_zero] at h
  rw [h]; norm_num

theorem fock_B2 : Lvir 1 (-1) (X 2 : Fock) = (3 : ℂ) • (X 3 : Fock) := by
  have h := Lvir_m1_X 2 3 rfl (1 : Fock)
  rw [mul_one, mul_one, Lvir_one_m1, mul_zero, add_zero] at h
  rw [h]; norm_num

theorem fock_B3 : Lvir 1 (-1) ((X 0 : Fock) * X 0) = (2 : ℂ) • ((X 0 : Fock) * X 1) := by
  have h := Lvir_m1_X 0 1 rfl (X 0 : Fock)
  rw [fock_B0, mul_comm (X 1 : Fock) (X 0 : Fock)] at h
  rw [h]; push_cast; module

theorem fock_B4 :
    Lvir 1 (-1) ((X 0 : Fock) * X 1) = (X 1 : Fock) * X 1 + (2 : ℂ) • ((X 0 : Fock) * X 2) := by
  have h := Lvir_m1_X 0 1 rfl (X 1 : Fock)
  rw [fock_B1, mul_smul_comm] at h
  rw [h]; push_cast; module

theorem fock_C0 :
    Lvir 1 (-2) (X 0 : Fock) = X 2 + (2⁻¹ : ℂ) • ((X 0 : Fock) * (X 0 * X 0)) := by
  have h := Lvir_m2_X 0 2 rfl (1 : Fock)
  rw [mul_one, mul_one, Lvir_one_m2, mul_smul_comm] at h
  rw [h]; push_cast; module

theorem fock_C1 :
    Lvir 1 (-2) (X 1 : Fock)
      = (2 : ℂ) • (X 3 : Fock) + (2⁻¹ : ℂ) • ((X 1 : Fock) * (X 0 * X 0)) := by
  have h := Lvir_m2_X 1 3 rfl (1 : Fock)
  rw [mul_one, mul_one, Lvir_one_m2, mul_smul_comm] at h
  rw [h]; push_cast; module

theorem fock_C2 :
    Lvir 1 (-2) ((X 0 : Fock) * X 0)
      = (2 : ℂ) • ((X 0 : Fock) * X 2) + (2⁻¹ : ℂ) • ((X 0 : Fock) * (X 0 * (X 0 * X 0))) := by
  have h := Lvir_m2_X 0 2 rfl (X 0 : Fock)
  rw [fock_C0, mul_add, mul_smul_comm, mul_comm (X 2 : Fock) (X 0 : Fock)] at h
  rw [h]; push_cast; module

/-! ### The linear-dilaton modes on `|0⟩`. -/

theorem Lld_apply (lam : ℂ) (n : ℤ) (p : Fock) :
    Lld lam n p = Lvir 1 n p + (lam * ((n : ℂ) + 1)) • osc 1 n p := by
  simp only [Lld, LinearMap.add_apply, LinearMap.smul_apply]

theorem Lld_m1 (lam : ℂ) (q : Fock) : Lld lam (-1) q = Lvir 1 (-1) q := by
  have h : lam * (((-1 : ℤ) : ℂ) + 1) = 0 := by push_cast; ring
  rw [Lld_apply, h, zero_smul, add_zero]

theorem Lld_m2 (lam : ℂ) (q : Fock) : Lld lam (-2) q = Lvir 1 (-2) q + (-lam) • (X 1 * q) := by
  have h : lam * (((-2 : ℤ) : ℂ) + 1) = -lam := by push_cast; ring
  rw [Lld_apply, h, osc_m2]

/-- The Virasoro relation on `Fock`, applied to a vector. -/
theorem Lld_comm_apply (lam : ℂ) (m n : ℤ) (p : Fock) :
    Lld lam m (Lld lam n p)
      = Lld lam n (Lld lam m p) + ((m : ℂ) - n) • Lld lam (m + n) p
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * (1 - 12 * lam ^ 2) else 0) • p := by
  have h := congrArg (fun T : End ℂ Fock => T p) (Lld_virasoro lam m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [eq_add_of_sub_eq h]
  module

theorem Lld_one_m1 (lam : ℂ) : Lld lam (-1) (1 : Fock) = 0 := Lld_vacuum lam (by norm_num)

/-- `L₋₂^λ|0⟩ = ½X₀² - λX₁`. -/
theorem fock_d2 (lam : ℂ) :
    Lld lam (-2) (1 : Fock) = (2⁻¹ : ℂ) • ((X 0 : Fock) * X 0) + (-lam) • (X 1 : Fock) := by
  rw [Lld_m2, Lvir_one_m2, mul_one]

/-- `L₋₃^λ|0⟩ = X₀X₁ - 2λX₂`, from `[L₋₁,L₋₂] = L₋₃`. -/
theorem fock_d3 (lam : ℂ) :
    Lld lam (-3) (1 : Fock) = (X 0 : Fock) * X 1 + (-(2 * lam)) • (X 2 : Fock) := by
  have hc := Lld_comm_apply lam (-1) (-2) (1 : Fock)
  rw [if_neg (by norm_num : ¬((-1 : ℤ) + -2 = 0)), zero_smul, add_zero,
    Lld_one_m1, map_zero, zero_add, show (-1 : ℤ) + -2 = -3 from by norm_num,
    show (((-1 : ℤ) : ℂ) - ((-2 : ℤ) : ℂ)) = 1 from by push_cast; ring, one_smul] at hc
  rw [← hc, fock_d2, Lld_m1, map_add, map_smul, map_smul, fock_B3, fock_B1, smul_smul, smul_smul]
  have e1 : (2⁻¹ : ℂ) * 2 = 1 := by norm_num
  have e2 : (-lam : ℂ) * 2 = -(2 * lam) := by ring
  rw [e1, one_smul, e2]

/-- `L₋₄^λ|0⟩ = ½X₁² + X₀X₂ - 3λX₃`, from `[L₋₁,L₋₃] = 2L₋₄`. -/
theorem fock_d4 (lam : ℂ) :
    Lld lam (-4) (1 : Fock)
      = (2⁻¹ : ℂ) • ((X 1 : Fock) * X 1) + (X 0 : Fock) * X 2 + (-(3 * lam)) • (X 3 : Fock) := by
  have hc := Lld_comm_apply lam (-1) (-3) (1 : Fock)
  rw [if_neg (by norm_num : ¬((-1 : ℤ) + -3 = 0)), zero_smul, add_zero,
    Lld_one_m1, map_zero, zero_add, show (-1 : ℤ) + -3 = -4 from by norm_num,
    show (((-1 : ℤ) : ℂ) - ((-3 : ℤ) : ℂ)) = 2 from by push_cast; ring] at hc
  have hcomp : Lld lam (-1) (Lld lam (-3) (1 : Fock))
      = (X 1 : Fock) * X 1 + (2 : ℂ) • ((X 0 : Fock) * X 2) + (-(6 * lam)) • (X 3 : Fock) := by
    rw [fock_d3, Lld_m1, map_add, map_smul, fock_B4, fock_B2, smul_smul]
    have e3 : (-(2 * lam) : ℂ) * 3 = -(6 * lam) := by ring
    rw [e3]
  rw [hcomp] at hc
  have hhalf : Lld lam (-4) (1 : Fock) = (2⁻¹ : ℂ) • ((2 : ℂ) • Lld lam (-4) (1 : Fock)) := by
    rw [smul_smul]; norm_num
  rw [hhalf, ← hc]
  module

set_option maxHeartbeats 1000000 in
-- the closing `module` call normalizes a five-monomial linear combination with `λ`-dependent
-- coefficients, which exceeds the default heartbeat budget
/-- `L₋₂^λL₋₂^λ|0⟩ = ¼X₀⁴ + X₀X₂ - λX₁X₀² - 2λX₃ + λ²X₁²`.  The `¼X₀⁴` coefficient is what makes
the Lee–Yang vector nonzero. -/
theorem fock_b (lam : ℂ) :
    Lld lam (-2) (Lld lam (-2) (1 : Fock))
      = (4⁻¹ : ℂ) • ((X 0 : Fock) * (X 0 * (X 0 * X 0)))
        + (X 0 : Fock) * X 2
        + (-lam) • ((X 1 : Fock) * (X 0 * X 0))
        + (-(2 * lam)) • (X 3 : Fock)
        + (lam ^ 2) • ((X 1 : Fock) * X 1) := by
  rw [fock_d2, Lld_m2, map_add, map_smul, map_smul, fock_C2, fock_C1, mul_add, mul_smul_comm,
    mul_smul_comm]
  module

/-! ### Evaluation functionals separating the level-4 states. -/

/-- `X₀ ↦ 1`, every other variable `↦ 0`. -/
noncomputable def ev0 : Fock →ₐ[ℂ] ℂ := aeval (fun i : ℕ => if i = 0 then (1 : ℂ) else 0)

/-- `X₁ ↦ 1`, every other variable `↦ 0`. -/
noncomputable def ev1 : Fock →ₐ[ℂ] ℂ := aeval (fun i : ℕ => if i = 1 then (1 : ℂ) else 0)

/-- `X₀, X₁ ↦ 1`, every other variable `↦ 0`. -/
noncomputable def ev01 : Fock →ₐ[ℂ] ℂ := aeval (fun i : ℕ => if i ≤ 1 then (1 : ℂ) else 0)

theorem ev0_d2 (lam : ℂ) : ev0 (Lld lam (-2) (1 : Fock)) = 2⁻¹ := by
  rw [fock_d2]
  simp only [ev0, map_add, map_smul, map_mul, MvPolynomial.aeval_X, smul_eq_mul]
  norm_num

theorem ev01_d3 (lam : ℂ) : ev01 (Lld lam (-3) (1 : Fock)) = 1 := by
  rw [fock_d3]
  simp only [ev01, map_add, map_smul, map_mul, MvPolynomial.aeval_X, smul_eq_mul]
  norm_num

theorem ev0_d4 (lam : ℂ) : ev0 (Lld lam (-4) (1 : Fock)) = 0 := by
  rw [fock_d4]
  simp only [ev0, map_add, map_smul, map_mul, MvPolynomial.aeval_X, smul_eq_mul]
  norm_num

theorem ev1_d4 (lam : ℂ) : ev1 (Lld lam (-4) (1 : Fock)) = 2⁻¹ := by
  rw [fock_d4]
  simp only [ev1, map_add, map_smul, map_mul, MvPolynomial.aeval_X, smul_eq_mul]
  norm_num

theorem ev0_b (lam : ℂ) : ev0 (Lld lam (-2) (Lld lam (-2) (1 : Fock))) = 4⁻¹ := by
  rw [fock_b]
  simp only [ev0, map_add, map_smul, map_mul, MvPolynomial.aeval_X, smul_eq_mul]
  norm_num

theorem ev1_b (lam : ℂ) : ev1 (Lld lam (-2) (Lld lam (-2) (1 : Fock))) = lam ^ 2 := by
  rw [fock_b]
  simp only [ev1, map_add, map_smul, map_mul, MvPolynomial.aeval_X, smul_eq_mul]
  norm_num

end FockCalc

/-! ### Transfer of relations from `VirUniv c` to `Fock`. -/

/-- The vacuum ideal `J(c)` is annihilated at the free-boson vacuum. -/
theorem evAlg_vacIdeal {c₀ lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c₀) {w : UVir}
    (hw : w ∈ vacIdeal c₀) : evAlg lam w vacuum = 0 := by
  induction hw using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨n, hn, rfl⟩ | rfl
      · rw [evAlg, lift_ι_apply, linDilRho_L]; exact Lld_vacuum lam hn
      · rw [evAlg, map_sub, lift_ι_apply, linDilRho_C, AlgHom.commutes,
          Algebra.algebraMap_eq_smul_one, hlam, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.smul_apply, LinearMap.id_apply, Module.End.one_apply, sub_self]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul r a _ ha =>
      rw [show (r • a : UVir) = r * a from rfl, map_mul, Module.End.mul_apply, ha, map_zero]

/-- A `U(𝔙𝔦𝔯)`-element vanishing in `VirUniv c` vanishes at the free-boson vacuum. -/
theorem evAlg_of_mk_eq_zero {c₀ lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c₀) {a : UVir}
    (h : (Submodule.Quotient.mk a : VirUniv c₀) = 0) : evAlg lam a vacuum = 0 :=
  evAlg_vacIdeal hlam ((Submodule.Quotient.mk_eq_zero _).mp h)

theorem evAlg_one (lam : ℂ) : evAlg lam (1 : UVir) vacuum = (1 : Fock) := by
  rw [map_one, Module.End.one_apply]
  rfl

theorem evAlg_L_mul (lam : ℂ) (n : ℤ) (a : UVir) :
    evAlg lam (ι ℂ (L n) * a) vacuum = Lld lam n (evAlg lam a vacuum) := by
  rw [map_mul, Module.End.mul_apply, evAlg, lift_ι_apply, linDilRho_L]

theorem L2vac_mk : L2vac c = Submodule.Quotient.mk (ι ℂ (L (-2)) * 1) := rfl
theorem L3vac_mk : L3vac c = Submodule.Quotient.mk (ι ℂ (L (-3)) * 1) := rfl
theorem L4vac_mk : L4vac c = Submodule.Quotient.mk (ι ℂ (L (-4)) * 1) := rfl
theorem L2L2vac_mk : L2L2vac c = Submodule.Quotient.mk (ι ℂ (L (-2)) * (ι ℂ (L (-2)) * 1)) := rfl

theorem mk_lin (α β : ℂ) (a b : UVir) :
    α • (Submodule.Quotient.mk a : VirUniv c) + β • (Submodule.Quotient.mk b : VirUniv c)
      = Submodule.Quotient.mk (α • a + β • b) := rfl

/-- **`L₋₂|0⟩ ≠ 0`** (`pbw`-free): its Fock image `½X₀² - λX₁` evaluates to `½` at `X₀ = 1`. -/
theorem L2vac_ne_zero : L2vac c ≠ 0 := by
  obtain ⟨lam, hlam⟩ := exists_lam c
  intro h
  have h0 : evAlg lam (ι ℂ (L (-2)) * 1) vacuum = 0 :=
    evAlg_of_mk_eq_zero hlam (by rw [← L2vac_mk c]; exact h)
  rw [evAlg_L_mul, evAlg_one] at h0
  have hev := congrArg ev0 h0
  rw [ev0_d2, map_zero] at hev
  norm_num at hev

/-- **`L₋₃|0⟩ ≠ 0`** (`pbw`-free): its Fock image `X₀X₁ - 2λX₂` evaluates to `1` at `X₀ = X₁ = 1`. -/
theorem L3vac_ne_zero : L3vac c ≠ 0 := by
  obtain ⟨lam, hlam⟩ := exists_lam c
  intro h
  have h0 : evAlg lam (ι ℂ (L (-3)) * 1) vacuum = 0 :=
    evAlg_of_mk_eq_zero hlam (by rw [← L3vac_mk c]; exact h)
  rw [evAlg_L_mul, evAlg_one] at h0
  have hev := congrArg ev01 h0
  rw [ev01_d3, map_zero] at hev
  norm_num at hev

/-- **The level-4 space is two-dimensional** (`pbw`-free): `L₋₂L₋₂|0⟩` and `L₋₄|0⟩` are linearly
independent for every central charge — the `ev0`/`ev1` matrix is `[[¼,0],[λ²,½]]`. -/
theorem level4_indep {α β : ℂ} (h : α • L2L2vac c + β • L4vac c = 0) : α = 0 ∧ β = 0 := by
  obtain ⟨lam, hlam⟩ := exists_lam c
  have hz : evAlg lam (α • (ι ℂ (L (-2)) * (ι ℂ (L (-2)) * 1)) + β • (ι ℂ (L (-4)) * 1))
      vacuum = 0 := by
    apply evAlg_of_mk_eq_zero hlam
    rw [← mk_lin c, ← L2L2vac_mk c, ← L4vac_mk c]
    exact h
  rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, evAlg_L_mul, evAlg_L_mul, evAlg_L_mul, evAlg_one] at hz
  have e0 := congrArg ev0 hz
  have e1 := congrArg ev1 hz
  rw [map_add, map_smul, map_smul, ev0_b, ev0_d4, map_zero, smul_eq_mul, smul_eq_mul] at e0
  rw [map_add, map_smul, map_smul, ev1_b, ev1_d4, map_zero, smul_eq_mul, smul_eq_mul] at e1
  have hα : α = 0 := by linear_combination (4 : ℂ) * e0
  exact ⟨hα, by linear_combination (2 : ℂ) * e1 - 2 * lam ^ 2 * hα⟩

/-- Contrapositive form: a nonzero coefficient pair gives a nonzero level-4 vector. -/
theorem level4_comb_ne_zero {α β : ℂ} (h : ¬(α = 0 ∧ β = 0)) :
    α • L2L2vac c + β • L4vac c ≠ 0 := fun hz => h (level4_indep c hz)

/-! ## §7  The determinant condition **is** `c = -22/5`. -/

/-- The `2 × 2` determinant of the singularity system `3α + 5β = 0`, `(c+8)α + 6β = 0`. -/
theorem singular_det (c : ℂ) : 3 * 6 - 5 * (c + 8) = -(5 * c + 22) := by ring

/-- The homogeneous system has a nonzero solution **iff** `c = -22/5`. -/
theorem system_nontrivial_iff (c : ℂ) :
    (∃ α β : ℂ, ¬(α = 0 ∧ β = 0) ∧ 3 * α + 5 * β = 0 ∧ (c + 8) * α + 6 * β = 0)
      ↔ c = -22 / 5 := by
  constructor
  · rintro ⟨α, β, hne, h1, h2⟩
    have hβ : β = -(3 / 5) * α := by linear_combination (1 / 5 : ℂ) * h1
    rw [hβ] at h2
    have hfac : α * (c + 22 / 5) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp hfac with hα | hc
    · exact absurd ⟨hα, by rw [hβ, hα]; ring⟩ hne
    · linear_combination hc
  · rintro rfl
    refine ⟨5, -3, ?_, by norm_num, by norm_num⟩
    rintro ⟨h5, -⟩
    norm_num at h5

/-- **The Lee–Yang derivation.**  A *nonzero* level-4 vector of `VirUniv c` killed by `L₁` and `L₂`
exists **iff** the central charge is `-22/5`.  The central charge is therefore a theorem, not an
input: it is forced by the vanishing of the `2 × 2` determinant `3·6 - 5(c+8) = -(5c+22)`. -/
theorem exists_level4_singular_iff (c : ℂ) :
    (∃ α β : ℂ, α • L2L2vac c + β • L4vac c ≠ 0
        ∧ Lop c 1 (α • L2L2vac c + β • L4vac c) = 0
        ∧ Lop c 2 (α • L2L2vac c + β • L4vac c) = 0)
      ↔ c = -22 / 5 := by
  rw [← system_nontrivial_iff c]
  constructor
  · rintro ⟨α, β, hne, h1, h2⟩
    refine ⟨α, β, fun hz => hne (by rw [hz.1, hz.2, zero_smul, zero_smul, add_zero]), ?_, ?_⟩
    · rw [Lop_one_comb] at h1
      by_contra hc
      exact L3vac_ne_zero c (eq_zero_of_smul_eq_zero hc h1)
    · rw [Lop_two_comb] at h2
      by_contra hc
      exact L2vac_ne_zero c (eq_zero_of_smul_eq_zero hc h2)
  · rintro ⟨α, β, hne, h1, h2⟩
    exact ⟨α, β, level4_comb_ne_zero c hne, by rw [Lop_one_comb, h1, zero_smul],
      by rw [Lop_two_comb, h2, zero_smul]⟩

/-- The derived central charge agrees with the minimal-model formula at `(p,q) = (2,5)`. -/
theorem minimalCentralCharge_leeYang : minimalCentralCharge 2 5 = -22 / 5 := by
  norm_num [minimalCentralCharge]

/-! ## §8  The Lee–Yang singular vector. -/

/-- **The Lee–Yang central charge** `c = 1 - 6(2-5)²/(2·5) = -22/5`, derived in
`exists_level4_singular_iff`. -/
noncomputable def leeYangC : ℂ := -22 / 5

theorem leeYangC_eq_minimalCentralCharge :
    leeYangC = ((minimalCentralCharge 2 5 : ℚ) : ℂ) := by
  simp only [leeYangC, minimalCentralCharge_leeYang]
  push_cast
  ring

/-- **The Lee–Yang singular vector** `s = 5L₋₂²|0⟩ - 3L₋₄|0⟩` of the universal vacuum module
`V(-22/5, 0)`.  The coefficients are integers — the system `3α+5β = 0`, `(c+8)α+6β = 0` has the
primitive solution `(5,-3)` — which matters downstream, since the deformation argument does
Gaussian elimination over `ℚ`. -/
noncomputable def leeYangSingular : VirUniv leeYangC :=
  (5 : ℂ) • L2L2vac leeYangC + (-3 : ℂ) • L4vac leeYangC

/-- `L₁ s = 0`. -/
theorem leeYangSingular_L1 : Lop leeYangC 1 leeYangSingular = 0 := by
  rw [leeYangSingular, Lop_one_comb]
  rw [show (3 * (5 : ℂ) + 5 * (-3)) = 0 from by norm_num, zero_smul]

/-- `L₂ s = 0`. -/
theorem leeYangSingular_L2 : Lop leeYangC 2 leeYangSingular = 0 := by
  rw [leeYangSingular, Lop_two_comb]
  rw [show ((leeYangC + 8) * (5 : ℂ) + 6 * (-3)) = 0 from by simp only [leeYangC]; norm_num,
    zero_smul]

/-- **`s` is singular**: every positive Virasoro mode annihilates it. -/
theorem leeYangSingular_annihilated {n : ℤ} (hn : 1 ≤ n) :
    Lop leeYangC n leeYangSingular = 0 :=
  Lop_pos_ann leeYangC leeYangSingular_L1 leeYangSingular_L2 hn

/-- `s` has conformal weight `4`. -/
theorem leeYangSingular_L0 : Lop leeYangC 0 leeYangSingular = (4 : ℂ) • leeYangSingular := by
  rw [leeYangSingular, Lop_zero_comb]

/-- `s` lies in the level-4 subspace. -/
theorem leeYangSingular_mem_grading : leeYangSingular ∈ gradingVir leeYangC 4 :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (L2L2vac_mem_grading leeYangC))
    (Submodule.smul_mem _ _ (L4vac_mem_grading leeYangC))

/-- **`s ≠ 0`** — the crux, `pbw`-free: its free-boson image has `X₀⁴`-coefficient `5/4`. -/
theorem leeYangSingular_ne_zero : leeYangSingular ≠ 0 := by
  refine level4_comb_ne_zero leeYangC ?_
  rintro ⟨h5, -⟩
  norm_num at h5

/-- **`s` is not proportional to the vacuum** — it has conformal weight `4` and the vacuum weight
`0`, so `4s = L₀s = 0` would force `s = 0`. -/
theorem leeYangSingular_ne_smul_vacVec (μ : ℂ) : leeYangSingular ≠ μ • vacVec leeYangC := by
  intro h
  have h0 : Lop leeYangC 0 leeYangSingular = 0 := by
    rw [h, map_smul, Lop_vacuum leeYangC (by norm_num : (-1 : ℤ) ≤ 0), smul_zero]
  rw [leeYangSingular_L0] at h0
  exact leeYangSingular_ne_zero (eq_zero_of_smul_eq_zero (by norm_num : (4 : ℂ) ≠ 0) h0)

/-- `s` is not in the vacuum line: `V(-22/5,0)` has a level-4 vector that is not a multiple of the
vacuum and is annihilated by the whole positive part of `𝔙𝔦𝔯`. -/
theorem leeYangSingular_notMem_span_vacVec : leeYangSingular ∉ (ℂ ∙ vacVec leeYangC) := by
  intro h
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h
  exact leeYangSingular_ne_smul_vacVec μ hμ.symm

/-! ## §9  The submodule generated by `s` — what is and is not proved here.

* **Proved** (`leeYangSubmodule_ne_bot`): the `U(𝔙𝔦𝔯)`-submodule generated by `s` is nonzero, since
  it contains `s ≠ 0`.
* **Not proved here**: that this submodule is *proper*.  Properness says `U(𝔙𝔦𝔯)·s` misses `|0⟩`,
  i.e. that `U(𝔙𝔦𝔯)·s = U(𝔙𝔦𝔯₋)·s` lives in conformal weights `≥ 4`.  Establishing it needs a
  straightening argument based at `s` — the analogue of `Examples/VirasoroSpanning.negSpanVir_eq_top`
  with the vacuum replaced by `s`, and with words in *all* negative modes (unlike the vacuum case,
  `L₋₁s ≠ 0`) — together with the fact that such words raise the `L₀`-eigenvalue.  Only with that
  in hand does one get `L(-22/5,0) ≠ V(-22/5,0)`.  `Core/QuotientVOA` quotients a VOA by a *given*
  graded ideal, so it does not by itself supply the missing properness step. -/

/-- The `U(𝔙𝔦𝔯)`-submodule of `V(-22/5,0)` generated by the Lee–Yang singular vector. -/
noncomputable def leeYangSubmodule : Submodule UVir (VirUniv leeYangC) :=
  Submodule.span UVir {leeYangSingular}

/-- The submodule generated by `s` is nonzero. -/
theorem leeYangSubmodule_ne_bot : leeYangSubmodule ≠ ⊥ := by
  intro h
  apply leeYangSingular_ne_zero
  have hmem : leeYangSingular ∈ leeYangSubmodule := Submodule.mem_span_singleton_self _
  rw [h] at hmem
  simpa using hmem

end VOA.LeeYang
