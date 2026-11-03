/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Locality
import VOA.Foundations.Parity
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# The `bc` ghost system — parity **without** half-integer moding

Two mutually conjugate odd fields `b(z)`, `c(z)` with integer-moded canonical
anticommutation relations

  `b₍ₘ₎c₍ₙ₎ + c₍ₙ₎b₍ₘ₎ = δ_{m+n+1,0}`,   `{b,b} = {c,c} = 0`.

This is the **Axis B without Axis A** corner of the super-convention test suite
(Axis A: half-integer moding; Axis B: odd parity): the fields are odd (so every locality here is at `ε = -1`), but
their conformal weights are integers, so nothing about half-integer moding is involved.
Together with `Examples.BetaGamma` (Axis A without Axis B) and `Examples.FreeFermion` (both),
it is the empirical check that the two generalizations really are independent — that neither
axis was accidentally built to presuppose the other.

## Construction

The same Clifford contraction that gives the free fermion, on a mode space with **two**
families of generators: `b` is created by the `inl` generators and annihilated by contraction
against the `inr` functionals, and `c` the other way round.  The cross-pairing is what makes
`b` and `c` conjugate to each other rather than to themselves, which is exactly the
difference between a `bc` system and two free fermions.

## References
* Friedan–Martinec–Shenker, *Conformal invariance, supersymmetry and string theory*,
  Nucl. Phys. B271 (1986); Kac, *VA for Beginners* §3.6; Gannon §5.2.2.
-/

namespace VOA

namespace BCGhosts

open CliffordAlgebra

/-- Two families of modes: `inl` carries `b`-creations, `inr` carries `c`-creations. -/
noncomputable abbrev ModeSpace := (ℕ ⊕ ℕ) →₀ ℂ

/-- The zero quadratic form, making the Clifford algebra an exterior algebra. -/
noncomputable abbrev Qzero : QuadraticForm ℂ ModeSpace := 0

/-- The ghost Fock space. -/
noncomputable abbrev Fock := CliffordAlgebra Qzero

/-- Exterior multiplication by a generator. -/
noncomputable def creOn (i : ℕ ⊕ ℕ) : Module.End ℂ Fock :=
  LinearMap.mulLeft ℂ (ι Qzero (Finsupp.single i (1 : ℂ)))

/-- Contraction against a coordinate functional. -/
noncomputable def annOn (i : ℕ ⊕ ℕ) : Module.End ℂ Fock := contractLeft (Finsupp.lapply i)

/-! ## The generic anticommutation relations -/

theorem creOn_anticomm (i j : ℕ ⊕ ℕ) (x : Fock) :
    creOn i (creOn j x) + creOn j (creOn i x) = 0 := by
  show ι Qzero _ * (ι Qzero _ * x) + ι Qzero _ * (ι Qzero _ * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ι_mul_ι_add_swap]
  simp [QuadraticMap.polar]

theorem annOn_anticomm (i j : ℕ ⊕ ℕ) (x : Fock) :
    annOn i (annOn j x) + annOn j (annOn i x) = 0 := by
  simp only [annOn]
  rw [contractLeft_comm]
  exact neg_add_cancel _

theorem annOn_creOn_anticomm (i j : ℕ ⊕ ℕ) (x : Fock) :
    annOn i (creOn j x) + creOn j (annOn i x) = (if i = j then (1 : ℂ) else 0) • x := by
  simp only [annOn, creOn, LinearMap.mulLeft_apply]
  rw [contractLeft_ι_mul]
  rw [show (Finsupp.lapply i : ModeSpace →ₗ[ℂ] ℂ) (Finsupp.single j (1 : ℂ))
        = (if i = j then (1 : ℂ) else 0) by
      simp [Finsupp.lapply_apply, Finsupp.single_apply, eq_comm]]
  abel

/-! ## The two fields -/

/-- `b`: created by the `inl` generators, annihilated against the `inr` functionals.

⚠ **Not a field.**  As a `FormalDist`, the argument `n` is the `z`-exponent (coefficient of
`zⁿ`), not the mode index; this definition puts creation operators at every negative exponent,
so for each nonzero `x` the coefficient applied to `x` is nonzero for infinitely many
negative `n`: the series is **not lower-truncated**
(certificate `L17Cert.freeFermion_psi_not_isField`, `Notes/Textbook/certificates/L17_Checks.lean`,
for `psi`; the same indexing is used for `bfield`, `cfield`).  The (anti)commutation relations below
are statements about the operator family `n ↦ bfield n` and are unaffected. -/
noncomputable def bfield : FormalDist (Module.End ℂ Fock) :=
  fun n => if 0 ≤ n then annOn (Sum.inr n.toNat) else creOn (Sum.inl (-n - 1).toNat)

/-- `c`: created by the `inr` generators, annihilated against the `inl` functionals.  ⚠ Same
indexing as `bfield`: **not lower-truncated**, hence not a field (see `bfield`). -/
noncomputable def cfield : FormalDist (Module.End ℂ Fock) :=
  fun n => if 0 ≤ n then annOn (Sum.inl n.toNat) else creOn (Sum.inr (-n - 1).toNat)

/-- **`b` anticommutes with itself.**  Both its creation and annihilation modes live on
different sides of the mode space, so no cross term survives. -/
theorem bfield_anticomm (m n : ℤ) :
    bfield m * bfield n + bfield n * bfield m = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, bfield, LinearMap.zero_apply]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;> simp only [hm, hn, if_true, if_false]
  · exact annOn_anticomm _ _ x
  · rw [annOn_creOn_anticomm, if_neg (by simp), zero_smul]
  · rw [add_comm, annOn_creOn_anticomm, if_neg (by simp), zero_smul]
  · exact creOn_anticomm _ _ x

/-- **`c` anticommutes with itself**, for the same reason. -/
theorem cfield_anticomm (m n : ℤ) :
    cfield m * cfield n + cfield n * cfield m = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, cfield, LinearMap.zero_apply]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;> simp only [hm, hn, if_true, if_false]
  · exact annOn_anticomm _ _ x
  · rw [annOn_creOn_anticomm, if_neg (by simp), zero_smul]
  · rw [add_comm, annOn_creOn_anticomm, if_neg (by simp), zero_smul]
  · exact creOn_anticomm _ _ x

/-- **The `bc` canonical anticommutation relation**: `{b₍ₘ₎, c₍ₙ₎} = δ_{m+n+1,0}`. -/
theorem bc_anticomm (m n : ℤ) :
    bfield m * cfield n + cfield n * bfield m = if m + n + 1 = 0 then 1 else 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, bfield, cfield]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;> simp only [hm, hn, if_true, if_false]
  · -- both annihilation: no pairing, and `m + n + 1 ≥ 1`
    rw [if_neg (by omega)]
    simpa using annOn_anticomm _ _ x
  · -- `b` annihilates on `inr`, `c` creates on `inr`: this is the pairing
    rw [annOn_creOn_anticomm]
    by_cases h : m + n + 1 = 0
    · rw [if_pos h, if_pos (by simp; omega : (Sum.inr m.toNat : ℕ ⊕ ℕ) = Sum.inr (-n - 1).toNat)]
      simp
    · rw [if_neg h, if_neg (by simp; omega : ¬(Sum.inr m.toNat : ℕ ⊕ ℕ) = Sum.inr (-n - 1).toNat)]
      simp
  · -- `b` creates on `inl`, `c` annihilates on `inl`: the pairing, other order
    rw [add_comm, annOn_creOn_anticomm]
    by_cases h : m + n + 1 = 0
    · rw [if_pos h, if_pos (by simp; omega : (Sum.inl n.toNat : ℕ ⊕ ℕ) = Sum.inl (-m - 1).toNat)]
      simp
    · rw [if_neg h, if_neg (by simp; omega : ¬(Sum.inl n.toNat : ℕ ⊕ ℕ) = Sum.inl (-m - 1).toNat)]
      simp
  · -- both creation: `m + n + 1 ≤ -1`
    rw [if_neg (by omega)]
    simpa using creOn_anticomm _ _ x

/-! ## Super-locality -/

/-- `b` is `ε`-local with itself at `ε = -1` (its anticommutator vanishes identically). -/
theorem bfield_localε : Localε (-1) bfield bfield :=
  localε_neg_one_of_anticomm 0 (by simpa using bfield_anticomm)

/-- `c` is `ε`-local with itself at `ε = -1`. -/
theorem cfield_localε : Localε (-1) cfield cfield :=
  localε_neg_one_of_anticomm 0 (by simpa using cfield_anticomm)

/-- **`b` and `c` are `ε`-local at `ε = -1`** — the Koszul sign of two odd fields.  This is
super-locality (VA4) for the `bc` system, with integer moding throughout. -/
theorem bc_localε : Localε (-1) bfield cfield :=
  localε_neg_one_of_anticomm 1 bc_anticomm

/-- Restated with the Koszul sign: both `b` and `c` are odd. -/
theorem bc_localε_koszul : Localε (koszul 1 1) bfield cfield := by
  rw [koszul_one_one]; exact bc_localε

end BCGhosts

end VOA
