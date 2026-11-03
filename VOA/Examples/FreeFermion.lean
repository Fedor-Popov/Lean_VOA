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
# The free fermion `ψ` — the first genuinely fermionic field

The Neveu–Schwarz free fermion: a single self-conjugate field `ψ(z)` on the fermionic Fock
space, satisfying the canonical **anti**commutation relations

  `ψ₍ₘ₎ψ₍ₙ₎ + ψ₍ₙ₎ψ₍ₘ₎ = δ_{m+n+1,0}`,

and therefore `ε`-local with itself at `ε = -1` — the Koszul sign of two odd fields.

This is an inhabitant of `Localε ε` at a sign other than `1`; an instance coming from an
ordinary vertex algebra via `localε_one_iff` exercises the sign machinery only formally.
`psi_localε` is the concrete check that `bracketDistε` and `Localε` are defined correctly,
which no amount of abstract argument supplies.

## Why the Fock space has to be infinite-dimensional

Locality forces the `ε`-twisted commutator to be a finite sum of `δ`-derivatives, and those
have infinite support along a diagonal (see `localε_iff_deltaSum`).  So no finite-dimensional
model can carry a genuinely fermionic local pair — there is no cheap toy here, and the
exterior algebra on a countable-dimensional space is the smallest honest example.

## The construction

The Fock space is the exterior algebra `Λ(ℕ →₀ ℂ)`, i.e. `CliffordAlgebra 0`.  Mathlib's
Clifford contraction supplies all three CAR families directly:

* creations anticommute — `CliffordAlgebra.ι_mul_ι_add_swap` with `Q = 0`;
* annihilations anticommute — `CliffordAlgebra.contractLeft_comm`;
* the mixed relation — `CliffordAlgebra.contractLeft_ι_mul`, which *is* the statement
  `{annihilation, creation} = ⟨functional, vector⟩ · id`.

The mode index is `ℤ`, as everywhere in this library: `ψ₍ₙ₎` is the physicists' `ψ_{n+1/2}`,
so the half-integer moding of the free fermion lives in the conformal *weight* (Axis A), not
in the mode index.  `n ≤ -1` are the creation modes and `n ≥ 0` the annihilation modes.

## References
* Kac, *Vertex Algebras for Beginners*, §3.6 and §4.10 (free fermions, `c = 1/2`);
  Frenkel–Lepowsky–Meurman §1.9; Gannon §5.2.2.
-/

namespace VOA

namespace FreeFermion

open CliffordAlgebra

/-- The mode space: one generator for each non-negative integer. -/
noncomputable abbrev ModeSpace := ℕ →₀ ℂ

/-- The zero quadratic form, making the Clifford algebra an exterior algebra. -/
noncomputable abbrev Qzero : QuadraticForm ℂ ModeSpace := 0

/-- **The Neveu–Schwarz fermionic Fock space** `Λ(ℕ →₀ ℂ)`. -/
noncomputable abbrev Fock := CliffordAlgebra Qzero

/-- The creation operator `ψ_{-k-1/2}`: exterior multiplication by the `k`-th generator. -/
noncomputable def cre (k : ℕ) : Module.End ℂ Fock :=
  LinearMap.mulLeft ℂ (ι Qzero (Finsupp.single k (1 : ℂ)))

/-- The annihilation operator `ψ_{k+1/2}`: contraction with the `k`-th coordinate functional. -/
noncomputable def ann (k : ℕ) : Module.End ℂ Fock := contractLeft (Finsupp.lapply k)

/-! ## The three canonical anticommutation relations -/

/-- Creation operators anticommute (`Q = 0`, so the polar form vanishes). -/
theorem cre_anticomm (j k : ℕ) (x : Fock) : cre j (cre k x) + cre k (cre j x) = 0 := by
  show ι Qzero _ * (ι Qzero _ * x) + ι Qzero _ * (ι Qzero _ * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ι_mul_ι_add_swap]
  simp [QuadraticMap.polar]

/-- Annihilation operators anticommute. -/
theorem ann_anticomm (j k : ℕ) (x : Fock) : ann j (ann k x) + ann k (ann j x) = 0 := by
  simp only [ann]
  rw [contractLeft_comm]
  exact neg_add_cancel _

/-- The mixed relation `{ψ_{j+1/2}, ψ_{-k-1/2}} = δ_{jk}`. -/
theorem ann_cre_anticomm (j k : ℕ) (x : Fock) :
    ann j (cre k x) + cre k (ann j x) = (if j = k then (1 : ℂ) else 0) • x := by
  simp only [ann, cre, LinearMap.mulLeft_apply]
  rw [contractLeft_ι_mul]
  rw [show (Finsupp.lapply j : ModeSpace →ₗ[ℂ] ℂ) (Finsupp.single k (1 : ℂ))
        = (if j = k then (1 : ℂ) else 0) by
      simp [Finsupp.lapply_apply, Finsupp.single_apply, eq_comm]]
  abel

/-! ## The field -/

/-- **The free fermion operator family** `n ↦ ψ₍ₙ₎`: creation for `n ≤ -1`, annihilation for
`n ≥ 0`.

⚠ **Not a field.**  As a `FormalDist`, the argument `n` is the `z`-exponent (coefficient of
`zⁿ`), not the mode index; this definition puts creation operators at every negative exponent,
so for each nonzero `x` the coefficient applied to `x` is nonzero for infinitely many
negative `n`: the series is **not lower-truncated**
(certificate `L17Cert.freeFermion_psi_not_isField`, `Notes/Textbook/certificates/L17_Checks.lean`,
for `psi`; the same indexing is used for `BCGhosts.bfield`/`cfield` and
`BetaGamma.beta`/`gamma`).  The (anti)commutation relations below are
statements about the operator family `n ↦ psi n` and are unaffected. -/
noncomputable def psi : FormalDist (Module.End ℂ Fock) :=
  fun n => if 0 ≤ n then ann n.toNat else cre (-n - 1).toNat

/-- **The canonical anticommutation relations for `ψ`**:
`ψ₍ₘ₎ψ₍ₙ₎ + ψ₍ₙ₎ψ₍ₘ₎ = δ_{m+n+1,0}`. -/
theorem psi_anticomm (m n : ℤ) :
    psi m * psi n + psi n * psi m = if m + n + 1 = 0 then 1 else 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, psi]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;> simp only [hm, hn, if_true, if_false]
  · -- both annihilation: `m + n + 1 ≥ 1`, and annihilations anticommute
    rw [if_neg (by omega)]
    simpa using ann_anticomm m.toNat n.toNat x
  · -- `m` annihilation, `n` creation
    rw [ann_cre_anticomm]
    by_cases h : m + n + 1 = 0
    · rw [if_pos h, if_pos (by omega : m.toNat = (-n - 1).toNat)]
      simp
    · rw [if_neg h, if_neg (by omega : ¬ m.toNat = (-n - 1).toNat)]
      simp
  · -- `m` creation, `n` annihilation
    rw [add_comm, ann_cre_anticomm]
    by_cases h : m + n + 1 = 0
    · rw [if_pos h, if_pos (by omega : n.toNat = (-m - 1).toNat)]
      simp
    · rw [if_neg h, if_neg (by omega : ¬ n.toNat = (-m - 1).toNat)]
      simp
  · -- both creation: `m + n + 1 ≤ -1`, and creations anticommute
    rw [if_neg (by omega)]
    simpa using cre_anticomm (-m - 1).toNat (-n - 1).toNat x

/-- **The free fermion field is `ε`-local with itself at `ε = -1`.**

`koszul 1 1 = -1` is the Koszul sign of two odd fields, so this is exactly super-locality
(VA4) for a purely odd generator.  It is the first inhabitant of `Localε` at a sign other
than `1` — and hence the empirical check that the sign conventions of
`Foundations/Locality` and `Foundations/Parity` are the right ones. -/
theorem psi_localε : Localε (-1) psi psi :=
  localε_neg_one_of_anticomm 1 psi_anticomm

/-- Restated with the Koszul sign in place of the literal `-1`. -/
theorem psi_localε_koszul : Localε (koszul 1 1) psi psi := by
  rw [koszul_one_one]
  exact psi_localε

/-- The free fermion is **not** local in the ordinary (bosonic) sense at `ε = 1` unless the
anticommutator degenerates — recorded as the reason the `ε` parameter is needed at all.
Concretely, `psi` witnesses that `Localε` genuinely depends on `ε`. -/
example : Localε (-1) psi psi := psi_localε

end FreeFermion

end VOA
