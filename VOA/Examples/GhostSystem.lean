/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionInstance

/-!
# The `bc` ghost system as a vertex superalgebra

Two mutually conjugate **odd** fields `b(z)`, `c(z)` of conformal weights `(λ, 1-λ)`, with the
canonical anticommutation relations

  `{b₍ₘ₎, c₍ₙ₎} = δ_{m+n+1,0}`,   `{b₍ₘ₎, b₍ₙ₎} = {c₍ₘ₎, c₍ₙ₎} = 0`.

This is the second tensor factor of the Drinfeld–Sokolov BRST complex: for `sl₂` with the
principal nilpotent one needs a **single** `bc` pair at `λ = 1`, i.e. `b` of weight `1` and `c`
of weight `0`, whose central charge is `c = -2`.

## ⚠ Why this file exists and does not build on `Examples.BCGhosts`

`Examples/BCGhosts.lean` sets

  `bfield n = if 0 ≤ n then annOn (inr n.toNat) else creOn (inl (-n-1).toNat)`,

i.e. it puts the **annihilation** modes at non-negative `z`-exponent.  That is inverted relative
to the convention used everywhere else in this library (`Examples/SymplecticFermion`,
`Examples/FreeFermion`, `Examples/LatticeFields`, …): `FormalDist` is indexed by the
`z`-**exponent**, `a(z) = ∑ⱼ aⱼ zʲ` with `mode a m = a (-m-1)`, so *creation* modes `a₍₋k₋₁₎` sit
at `j = k ≥ 0` and *annihilation* modes `a₍k₎` at `j = -k-1 ≤ -1`.  With the inverted orientation
`bfield` is **not** `IsField` (lower truncation fails: `bfield j` for `j ≪ 0` is a creation
operator, which never annihilates anything), so `BCGhosts` cannot feed reconstruction, cannot
carry a `T`, and cannot become a vertex superalgebra.  Its `Localε` statements are correct as
stated — locality is orientation-blind — but nothing further can be built on them.  Everything
below is built from scratch in the correct orientation.

## Reuse of the symplectic-fermion Fock space

The *underlying vector space* of the `bc` system is the exterior algebra
`Λ((ℕ × Fin 2) →₀ ℂ)` on one creation mode per (level, species) pair — literally the same vector
space that `Examples/SymplecticFermion` builds, since a symplectic fermion pair also has two
species of odd creation modes.  We therefore reuse `SympFerm.FockSF` together with the pieces of
that development that are statements about the *Clifford algebra* and not about the symplectic
vertex structure:

| reused | what it is |
| --- | --- |
| `FockSF`, `creBase`, `annBase`, and the three Clifford CARs | exterior algebra and contraction |
| `contractLeft_mul'`, `contractLeft_high_eq_zero` | odd derivation; lower truncation |
| `T`, `T_creBase`, `T_annBase` | the mode-shift derivation `L₋₁` |
| `stWordSF`, `stWordSF_span`, `stWordSF_parity_split` | monomials, spanning, Clifford `ℤ/2` |

What is **not** reused is the vertex-algebra structure: `SympFerm.chi` pairs a species with
itself through the symplectic form and carries a factor of the mode number (giving order-2
locality, a `δ'` OPE), whereas the `bc` fields below pair `b` with `c` with a bare `δ` (order-1
locality).  The two vertex superalgebra structures on this one vector space are genuinely
different — for instance the `bc` system at `λ = 1` has `c = -2` but is **not** the symplectic
fermion algebra: it has a `ℤ`-grading by ghost number that the symplectic pair does not.

## Independence of `λ`

The mode algebra, the fields, locality, lower truncation, the translation operator and the ghost
number are all **independent of `λ`**: in a vertex algebra `Y(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}` regardless
of conformal weight, so `λ` enters only through the *weight grading* and through the choice of
conformal vector.  Accordingly everything up to and including the vertex operator `YGh` below is
stated once, with no `λ` anywhere.

## What is here

* §1 the `bc` pairing, creation/annihilation operators, and the three CAR families;
* §2 the fields `bfield`, `cfield` in the **correct** orientation, their anticommutator,
  lower truncation (`IsField`), and `ε`-locality at `ε = -1 = koszul 1 1`;
* §3 translation covariance for the reused `T`;
* §4 a reusable dual-number construction of derivations of the Fock algebra, and the **ghost
  number** grading `ghostGrading : ℤ → Submodule ℂ FockSF` (`b` carries `-1`, `c` carries `+1`),
  an honest internal direct sum, together with its reduction mod `2` to the parity;
* §5 the word fields, and the vertex operator `YGh` produced by `reconstructε`;
* §6 the conformal weight grading **at `λ = 1`** (`b` of weight `1`, `c` of weight `0`), as an
  internal direct sum with finite-dimensional pieces — the finiteness needs a genuinely new
  ingredient here, namely that a creation monomial with a repeated mode vanishes, because at
  `λ = 1` the mode `c₍₋₁₎` has weight `0` and so weight alone does not bound the word length;
* §7 the `SuperVertexAlgebra` instance `bcGhostSVA`;
* §8 the central charge `c(λ) = -2(6λ² - 6λ + 1)`, the ghost stress tensor
  `L(z) = -λ :b ∂c: + (1-λ) :(∂b) c:`, and the Virasoro relation as a **statement**
  (`IsGhostVirasoro`) — a `Prop`, deliberately *not* a theorem, since the mode computation is not
  carried out here.

## References
* Friedan–Martinec–Shenker, Nucl. Phys. **B271** (1986) 93, §2;
* Kac, *Vertex Algebras for Beginners*, §3.6 and §5.10;
* Frenkel–Kac–Wakimoto, Comm. Math. Phys. **147** (1992) 295, for the BRST/DS setting.
-/

namespace VOA.Ghost

open CliffordAlgebra
open VOA.SympFerm
open VOA.Reconstruction
open Module (End)
open scoped DualNumber

/-! ## §1  The `bc` pairing and the mode operators

Species `0` is `b`, species `1` is `c`.  The generator `(k, a)` of the mode space is the creation
mode `a₍₋k₋₁₎`; the annihilation mode `a₍k₎` contracts against the generator of the **conjugate**
species at the same level, which is what makes `b` and `c` conjugate to each other rather than
each to itself. -/

/-- The `bc` pairing `ωᵃᵇ`: `1` when the species differ, `0` when they agree.  Unlike the
symplectic form of `Examples/SymplecticFermion` it is **symmetric**, since `{b,c} = {c,b}`. -/
def ghPair (a b : Fin 2) : ℂ := if b = a + 1 then 1 else 0

@[simp] theorem ghPair_self (a : Fin 2) : ghPair a a = 0 := by
  fin_cases a <;>
    simp [ghPair, show ((0 : Fin 2) + 1 = 1) from rfl, show ((1 : Fin 2) + 1 = 0) from rfl]

theorem ghPair_symm (a b : Fin 2) : ghPair b a = ghPair a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [ghPair, show ((1 : Fin 2) + 1 = 0) from rfl, show ((0 : Fin 2) + 1 = 1) from rfl]

@[simp] theorem ghPair_bc : ghPair 0 1 = 1 := by
  rw [ghPair, if_pos (show (1 : Fin 2) = 0 + 1 from by decide)]

@[simp] theorem ghPair_cb : ghPair 1 0 = 1 := by rw [ghPair_symm, ghPair_bc]

/-- The creation operator `a₍₋k₋₁₎`: exterior multiplication by the generator `(k, a)`. -/
noncomputable def creGh (a : Fin 2) (k : ℕ) : End ℂ FockSF := creBase (k, a)

/-- The annihilation operator `a₍k₎` for `k ≥ 0`: contraction against the **conjugate** species'
generator at level `k`.  This single index shift `a ↦ a + 1` is the whole difference between a
`bc` system and two decoupled free fermions. -/
noncomputable def annGh (a : Fin 2) (k : ℕ) : End ℂ FockSF := annBase (k, a + 1)

theorem creGh_anticomm (a b : Fin 2) (j k : ℕ) (x : FockSF) :
    creGh a j (creGh b k x) + creGh b k (creGh a j x) = 0 :=
  creBase_anticomm _ _ x

theorem annGh_anticomm (a b : Fin 2) (m n : ℕ) (x : FockSF) :
    annGh a m (annGh b n x) + annGh b n (annGh a m x) = 0 :=
  annBase_anticomm _ _ x

/-- **The mixed canonical anticommutation relation**
`{a₍m₎, b₍₋k₋₁₎} = δ_{m,k} · ωᵃᵇ`: a bare Kronecker `δ`, with **no** factor of the mode number.
That is what makes the `bc` locality order `1` rather than `2`. -/
theorem annGh_creGh_anticomm (a b : Fin 2) (m k : ℕ) (x : FockSF) :
    annGh a m (creGh b k x) + creGh b k (annGh a m x)
      = (if m = k then ghPair a b else 0) • x := by
  have h : annBase ((m, a + 1) : ℕ × Fin 2) (creBase ((k, b) : ℕ × Fin 2) x)
      + creBase ((k, b) : ℕ × Fin 2) (annBase ((m, a + 1) : ℕ × Fin 2) x)
      = (if ((m, a + 1) : ℕ × Fin 2) = (k, b) then (1 : ℂ) else 0) • x :=
    annBase_creBase_anticomm _ _ x
  rw [show annGh a m = annBase ((m, a + 1) : ℕ × Fin 2) from rfl,
    show creGh b k = creBase ((k, b) : ℕ × Fin 2) from rfl, h]
  congr 1
  have hiff : (((m, a + 1) : ℕ × Fin 2) = (k, b)) ↔ (m = k ∧ b = a + 1) := by
    rw [Prod.ext_iff]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  by_cases hmk : m = k
  · by_cases hab : b = a + 1
    · rw [if_pos (hiff.mpr ⟨hmk, hab⟩), if_pos hmk, ghPair, if_pos hab]
    · rw [if_neg (fun hc => hab (hiff.mp hc).2), if_pos hmk, ghPair, if_neg hab]
  · rw [if_neg (fun hc => hmk (hiff.mp hc).1), if_neg hmk]

/-! ## §2  The fields

`FormalDist` is indexed by the `z`-exponent, so `ghField a j = a₍₋j₋₁₎`: **creation for `j ≥ 0`**,
annihilation for `j ≤ -1`.  This is the orientation `Examples/BCGhosts` gets backwards. -/

/-- **The ghost field** `a(z) = ∑ₙ a₍ₙ₎ z^{-n-1}`, as a formal distribution indexed by the
`z`-exponent: creation at `j ≥ 0`, annihilation at `j ≤ -1`. -/
noncomputable def ghField (a : Fin 2) : FormalDist (End ℂ FockSF) :=
  fun j => if 0 ≤ j then creGh a j.toNat else annGh a (-j - 1).toNat

/-- The antighost `b(z)`, of conformal weight `λ`. -/
noncomputable def bfield : FormalDist (End ℂ FockSF) := ghField 0

/-- The ghost `c(z)`, of conformal weight `1 - λ`. -/
noncomputable def cfield : FormalDist (End ℂ FockSF) := ghField 1

/-- **The canonical anticommutation relations for the ghost fields**, in `z`-exponent
indexing: `{aⱼ, b_k} = δ_{j+k+1,0} · ωᵃᵇ`.  A bare `δ` (contrast `SympFerm.chi_anticomm`, which
carries a factor of the mode and so produces a `δ`-derivative). -/
theorem ghField_anticomm (a b : Fin 2) (j k : ℤ) :
    ghField a j * ghField b k + ghField b k * ghField a j
      = (if j + k + 1 = 0 then ghPair a b else 0) • (1 : End ℂ FockSF) := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, ghField, LinearMap.smul_apply,
    Module.End.one_apply]
  by_cases hj : 0 ≤ j <;> by_cases hk : 0 ≤ k <;> simp only [hj, hk, if_true, if_false]
  · -- both creation: `j + k + 1 ≥ 1`
    rw [if_neg (by omega), zero_smul]
    exact creGh_anticomm a b j.toNat k.toNat x
  · -- `j` creation, `k` annihilation
    rw [add_comm, annGh_creGh_anticomm]
    by_cases h : j + k + 1 = 0
    · rw [if_pos h, if_pos (show (-k - 1).toNat = j.toNat by omega), ghPair_symm]
    · rw [if_neg h, if_neg (show ¬ ((-k - 1).toNat = j.toNat) by omega)]
  · -- `j` annihilation, `k` creation
    rw [annGh_creGh_anticomm]
    by_cases h : j + k + 1 = 0
    · rw [if_pos h, if_pos (show (-j - 1).toNat = k.toNat by omega)]
    · rw [if_neg h, if_neg (show ¬ ((-j - 1).toNat = k.toNat) by omega)]
  · -- both annihilation: `j + k + 1 ≤ -1`
    rw [if_neg (by omega), zero_smul]
    exact annGh_anticomm a b (-j - 1).toNat (-k - 1).toNat x

/-- `{b(z), c(w)}` is the `δ`-function: the defining `bc` relation. -/
theorem bc_anticomm (j k : ℤ) :
    bfield j * cfield k + cfield k * bfield j
      = (if j + k + 1 = 0 then (1 : ℂ) else 0) • (1 : End ℂ FockSF) := by
  rw [bfield, cfield, ghField_anticomm, ghPair_bc]

/-- `b` anticommutes with itself. -/
theorem bb_anticomm (j k : ℤ) : bfield j * bfield k + bfield k * bfield j = 0 := by
  rw [bfield, ghField_anticomm, ghPair_self]
  simp

/-- `c` anticommutes with itself. -/
theorem cc_anticomm (j k : ℤ) : cfield j * cfield k + cfield k * cfield j = 0 := by
  rw [cfield, ghField_anticomm, ghPair_self]
  simp

/-- **The ghost fields are `ε`-local at `ε = -1`, with order 1.**  The anticommutator is a
bare `δ`, so the free-field criterion `localε_neg_one_of_anticomm` applies directly. -/
theorem ghField_localε (a b : Fin 2) : Localε (-1) (ghField a) (ghField b) := by
  refine localε_neg_one_of_anticomm (ghPair a b • (1 : End ℂ FockSF)) (fun m n => ?_)
  rw [ghField_anticomm]
  by_cases h : m + n + 1 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_smul]

/-- Restated with the Koszul sign in place of the literal `-1`, matching super-VA4: both `b` and
`c` are odd. -/
theorem ghField_localε_koszul (a b : Fin 2) : Localε (koszul 1 1) (ghField a) (ghField b) := by
  rw [koszul_one_one]; exact ghField_localε a b

/-- **The ghost fields are fields** (lower truncation, VA5).  This is exactly what the
inverted orientation of `Examples/BCGhosts` destroys: with creation at `j ≪ 0` no truncation
bound exists. -/
theorem ghField_isField (a : Fin 2) : IsField (ghField a) := by
  intro x
  obtain ⟨N, hN⟩ := contractLeft_high_eq_zero x
  refine ⟨-(N : ℤ) - 1, fun j hj => ?_⟩
  change ghField a j x = 0
  rw [ghField, if_neg (by omega : ¬ (0 ≤ j))]
  change annBase (((-j - 1).toNat, a + 1) : ℕ × Fin 2) x = 0
  rw [annBase, hN ((-j - 1).toNat) (by omega) (a + 1)]

/-! ### Creation from the vacuum -/

/-- **VA3 base**: `a(z)|0⟩` has constant term the generating state `a₍₋₁₎|0⟩`. -/
@[simp] theorem ghField_zero_vac (a : Fin 2) :
    ghField a 0 vacSF = ι QSF (Finsupp.single ((0, a) : ℕ × Fin 2) (1 : ℂ)) := by
  rw [ghField, if_pos le_rfl]
  change creBase (Int.toNat 0, a) vacSF = _
  rw [creBase]
  change ι QSF (Finsupp.single ((Int.toNat 0, a) : ℕ × Fin 2) (1 : ℂ)) * (1 : FockSF) = _
  rw [mul_one]
  norm_num

/-- **VA3 regularity**: `a(z)|0⟩` has no negative powers — the annihilation half kills the
vacuum, since contraction annihilates `1`. -/
@[simp] theorem ghField_neg_vac (a : Fin 2) (q : ℤ) (hq : q < 0) : ghField a q vacSF = 0 := by
  rw [ghField, if_neg (by omega : ¬ (0 ≤ q))]
  change annBase (((-q - 1).toNat, a + 1) : ℕ × Fin 2) vacSF = 0
  rw [annBase]
  change contractLeft (Finsupp.lapply (((-q - 1).toNat, a + 1) : ℕ × Fin 2)) (1 : FockSF) = 0
  rw [contractLeft_one]

/-! ## §3  Translation covariance

`DCovariant T a` is `[T, aₘ] = (m+1)•a_{m+1}`, a statement about *vertex-algebra* modes and hence
independent of `λ`.  The operator `T = L₋₁` is the mode-shift derivation of
`Examples/SymplecticFermionT`, reused verbatim: it is defined by `χ_{-k-1} ↦ (k+1)·χ_{-k-2}` on
the mode space, which in `z`-exponent indexing is the same shift for any pairing. -/

/-- **The ghost fields are `T`-covariant** — the last `reconstructε` hypothesis at generator
level.  Both halves are read off `SympFerm.T_creBase` / `SympFerm.T_annBase`; the mode `j = -1`
(the ghost zero mode `a₍₀₎`) is the boundary case where both sides vanish. -/
theorem ghField_DCovariant (a : Fin 2) : DCovariant T (ghField a) := by
  intro m
  by_cases hm : 0 ≤ m
  · -- creation side
    have h1 : ghField a m = creBase ((m.toNat, a) : ℕ × Fin 2) := by rw [ghField, if_pos hm]; rfl
    have h2 : ghField a (m + 1) = creBase (((m + 1).toNat, a) : ℕ × Fin 2) := by
      rw [ghField, if_pos (by omega : (0 : ℤ) ≤ m + 1)]; rfl
    rw [h1, h2, T_creBase, show ((m.toNat, a) : ℕ × Fin 2).1 + 1 = (m + 1).toNat by omega,
      ← Int.cast_smul_eq_zsmul ℂ (m + 1)]
    congr 1
    rw [show ((m.toNat : ℕ) : ℂ) = (m : ℂ) by exact_mod_cast Int.toNat_of_nonneg hm]
    push_cast
    ring
  · -- annihilation side
    have h1 : ghField a m = annBase (((-m - 1).toNat, a + 1) : ℕ × Fin 2) := by
      rw [ghField, if_neg hm]; rfl
    by_cases hm1 : m = -1
    · have hk : ((-m - 1).toNat : ℕ) = 0 := by omega
      rw [h1, hk, T_annBase, Nat.cast_zero, zero_smul, neg_zero,
        show m + 1 = 0 from by omega, zero_smul]
    · have hm2 : m ≤ -2 := by omega
      have h2 : ghField a (m + 1) = annBase ((((-m - 1).toNat - 1), a + 1) : ℕ × Fin 2) := by
        rw [ghField, if_neg (by omega : ¬ (0 ≤ m + 1))]
        have hidx : (-(m + 1) - 1).toNat = (-m - 1).toNat - 1 := by omega
        rw [hidx]; rfl
      rw [h1, h2, T_annBase, ← neg_smul, ← Int.cast_smul_eq_zsmul ℂ (m + 1)]
      congr 1
      have hc : (((-m - 1).toNat : ℕ) : ℂ) = -(m : ℂ) - 1 := by
        have h : (((-m - 1).toNat : ℕ) : ℤ) = -m - 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h
      rw [hc]
      push_cast
      ring

/-! ## §4  Derivations of the Fock algebra, and the ghost number

Building a **derivation** of a Clifford algebra from a linear map on the generating space is not
in Mathlib — `CliffordAlgebra.lift` produces *algebra maps*.  The standard device recovers one
from the other: an algebra map into the dual numbers `A[ε]` is exactly a pair (algebra map,
derivation along it), so `derivOf f := snd ∘ (lift ⟨v ↦ (ι v, ι (f v))⟩)`.  The Clifford
condition is free at `Q = 0`: the `fst` entry is `ι_sq_scalar` and the `snd` entry is the polar
form, and both vanish.

`Examples/SymplecticFermionT` and `Examples/SymplecticFermionGrading` each perform this
construction once, for one specific `f`.  Here it is done **once for all `f`**, because the ghost
system needs it twice: for the ghost-number operator (§4) and for the conformal weight operator
(any `λ`).  The interface `derivOf_mul` / `derivOf_one` / `derivOf_ι` is complete, so `dnHom` is
sealed with `attribute [irreducible]` — the `T` file records two 35-minute elaboration blowups
caused by leaving a `CliffordAlgebra.lift` application transparent. -/

/-- The generator map into dual numbers, `v ↦ (ι v, ι (f v))`. -/
noncomputable def dnGen (f : SFModes →ₗ[ℂ] SFModes) : SFModes →ₗ[ℂ] FockSF[ε] where
  toFun v := TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (f v))
  map_add' u v := by
    simp only [map_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  map_smul' c v := by
    simp only [RingHom.id_apply, map_smul, TrivSqZeroExt.inl_smul, TrivSqZeroExt.inr_smul,
      smul_add]

@[simp] theorem dnGen_fst (f : SFModes →ₗ[ℂ] SFModes) (v : SFModes) :
    (dnGen f v).fst = ι QSF v := by
  change (TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (f v))).fst = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

@[simp] theorem dnGen_snd (f : SFModes →ₗ[ℂ] SFModes) (v : SFModes) :
    (dnGen f v).snd = ι QSF (f v) := by
  change (TrivSqZeroExt.inl (ι QSF v) + TrivSqZeroExt.inr (ι QSF (f v))).snd = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

/-- The Clifford condition, free at `Q = 0`. -/
theorem dnGen_sq (f : SFModes →ₗ[ℂ] SFModes) (v : SFModes) :
    dnGen f v * dnGen f v = algebraMap ℂ FockSF[ε] (QSF v) := by
  have hQ : QSF v = 0 := rfl
  rw [hQ, map_zero]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, dnGen_fst, ι_sq_scalar]
    change (algebraMap ℂ FockSF) (QSF v) = (0 : FockSF[ε]).fst
    rw [hQ, map_zero]; rfl
  · rw [TrivSqZeroExt.snd_mul, dnGen_fst, dnGen_snd]
    change (ι QSF v) * (ι QSF (f v)) + (ι QSF (f v)) * (ι QSF v) = (0 : FockSF[ε]).snd
    rw [ι_mul_ι_add_swap]
    change (algebraMap ℂ FockSF) (QuadraticMap.polar (⇑QSF) v (f v)) = 0
    rw [show QuadraticMap.polar (⇑QSF) v (f v) = 0 by simp [QuadraticMap.polar], map_zero]

/-- The algebra map whose `ε`-component is the derivation extending `f`. -/
noncomputable def dnHom (f : SFModes →ₗ[ℂ] SFModes) : FockSF →ₐ[ℂ] FockSF[ε] :=
  CliffordAlgebra.lift QSF ⟨dnGen f, dnGen_sq f⟩

@[simp] theorem dnHom_ι (f : SFModes →ₗ[ℂ] SFModes) (v : SFModes) :
    dnHom f (ι QSF v) = dnGen f v := by
  rw [dnHom, CliffordAlgebra.lift_ι_apply]

theorem dnHom_fst (f : SFModes →ₗ[ℂ] SFModes) (x : FockSF) : (dnHom f x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ FockSF FockSF).comp (dnHom f) = AlgHom.id ℂ FockSF := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext; intro v
    change (dnHom f (ι QSF v)).fst = ι QSF v
    rw [dnHom_ι, dnGen_fst]
  exact congrArg (fun (g : FockSF →ₐ[ℂ] FockSF) => g x) h

/-- **The even derivation of the Fock algebra extending `f`.** -/
noncomputable def derivOf (f : SFModes →ₗ[ℂ] SFModes) : Module.End ℂ FockSF where
  toFun x := (dnHom f x).snd
  map_add' x y := by simp only [map_add, TrivSqZeroExt.snd_add]
  map_smul' c x := by simp only [RingHom.id_apply, map_smul, TrivSqZeroExt.snd_smul]

@[simp] theorem derivOf_apply (f : SFModes →ₗ[ℂ] SFModes) (x : FockSF) :
    derivOf f x = (dnHom f x).snd := rfl

/-- **Leibniz**: `TrivSqZeroExt.snd_mul` *is* the derivation property. -/
theorem derivOf_mul (f : SFModes →ₗ[ℂ] SFModes) (x y : FockSF) :
    derivOf f (x * y) = x * derivOf f y + derivOf f x * y := by
  rw [derivOf_apply, map_mul, TrivSqZeroExt.snd_mul, dnHom_fst, dnHom_fst]
  rfl

@[simp] theorem derivOf_one (f : SFModes →ₗ[ℂ] SFModes) : derivOf f (1 : FockSF) = 0 := by
  rw [derivOf_apply, map_one]; rfl

@[simp] theorem derivOf_ι (f : SFModes →ₗ[ℂ] SFModes) (v : SFModes) :
    derivOf f (ι QSF v) = ι QSF (f v) := by
  rw [derivOf_apply, dnHom_ι, dnGen_snd]

attribute [irreducible] dnHom

/-! ### Diagonal derivations

The only derivations needed are the ones diagonal in the mode basis: `p ↦ w p · p`.  Their value
on a creation monomial is the *sum* of the weights of its letters — which, once the letters are
given charges `±1`, is the ghost number. -/

/-- The diagonal map `p ↦ (w p) · p` on mode space. -/
noncomputable def diagMap (w : ℕ × Fin 2 → ℂ) : SFModes →ₗ[ℂ] SFModes :=
  Finsupp.lsum ℂ fun p =>
    LinearMap.toSpanSingleton ℂ SFModes ((w p) • Finsupp.single p (1 : ℂ))

@[simp] theorem diagMap_single (w : ℕ × Fin 2 → ℂ) (p : ℕ × Fin 2) (c : ℂ) :
    diagMap w (Finsupp.single p c) = c • ((w p) • Finsupp.single p (1 : ℂ)) := by
  simp [diagMap]

theorem derivOf_diag_gen (w : ℕ × Fin 2 → ℂ) (p : ℕ × Fin 2) :
    derivOf (diagMap w) (ι QSF (Finsupp.single p (1 : ℂ)))
      = (w p) • ι QSF (Finsupp.single p (1 : ℂ)) := by
  rw [derivOf_ι, diagMap_single, one_smul, map_smul]

/-- **A creation monomial is an eigenvector of every diagonal derivation**, with eigenvalue the
sum of the weights of its letters.  A bare induction on the word: the Leibniz rule turns "the
operator is a derivation" into "weights add". -/
theorem derivOf_diag_stWordSF (w : ℕ × Fin 2 → ℂ) (l : SFWord) :
    derivOf (diagMap w) (stWordSF l) = ((l.map w).sum) • stWordSF l := by
  induction l with
  | nil => rw [stWordSF_nil, derivOf_one, List.map_nil, List.sum_nil, zero_smul]
  | cons p rest ih =>
      rw [stWordSF_cons, derivOf_mul, ih, derivOf_diag_gen, mul_smul_comm, smul_mul_assoc,
        ← add_smul, List.map_cons, List.sum_cons]
      congr 1
      ring

/-! ### The ghost number -/

/-- The ghost charge of a species: the antighost `b` carries `-1`, the ghost `c` carries `+1`. -/
def ghCharge (a : Fin 2) : ℤ := if a = 0 then -1 else 1

@[simp] theorem ghCharge_b : ghCharge 0 = -1 := by rw [ghCharge, if_pos rfl]

@[simp] theorem ghCharge_c : ghCharge 1 = 1 := by
  rw [ghCharge, if_neg (show ¬ ((1 : Fin 2) = 0) from by decide)]

/-- Every ghost charge is odd — this is what makes ghost number refine the parity. -/
theorem ghCharge_odd (a : Fin 2) : ((ghCharge a : ℤ) : ZMod 2) = 1 := by
  have h : ghCharge a = -1 ∨ ghCharge a = 1 := by
    rw [ghCharge]
    by_cases ha : a = 0
    · exact Or.inl (if_pos ha)
    · exact Or.inr (if_neg ha)
  rcases h with h | h <;> rw [h]
  · rw [Int.cast_neg, Int.cast_one]; decide
  · rw [Int.cast_one]

/-- **The ghost-number operator `N_gh`**: the even derivation of the Fock algebra which scales
each creation mode by its ghost charge. -/
noncomputable def Ngh : Module.End ℂ FockSF :=
  derivOf (diagMap (fun p => ((ghCharge p.2 : ℤ) : ℂ)))

/-- The ghost number of a creation monomial: `#c - #b`. -/
def ghNum (l : SFWord) : ℤ := (l.map fun p => ghCharge p.2).sum

@[simp] theorem ghNum_nil : ghNum [] = 0 := rfl

@[simp] theorem ghNum_cons (p : ℕ × Fin 2) (rest : SFWord) :
    ghNum (p :: rest) = ghCharge p.2 + ghNum rest := by
  simp [ghNum]

/-- An integer-valued list sum commutes with the cast into `ℂ`. -/
theorem sum_map_intCast (g : ℕ × Fin 2 → ℤ) (l : SFWord) :
    (l.map fun p => ((g p : ℤ) : ℂ)).sum = (((l.map g).sum : ℤ) : ℂ) := by
  induction l with
  | nil => simp
  | cons p rest ih => simp only [List.map_cons, List.sum_cons, ih, Int.cast_add]

/-- **Creation monomials are `N_gh`-eigenvectors**, with eigenvalue their ghost number. -/
theorem Ngh_stWordSF (l : SFWord) : Ngh (stWordSF l) = ((ghNum l : ℤ) : ℂ) • stWordSF l := by
  rw [Ngh, derivOf_diag_stWordSF, sum_map_intCast]
  rfl

/-- **Ghost number refines the parity**: mod `2`, the ghost number is the length of the word,
which is the Clifford parity.  This is the compatibility the BRST differential needs — the
differential has ghost number `+1` and is therefore odd. -/
theorem ghNum_mod_two (l : SFWord) : ((ghNum l : ℤ) : ZMod 2) = ((l.length : ℕ) : ZMod 2) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      rw [ghNum_cons, List.length_cons, Int.cast_add, ih, Nat.cast_add, Nat.cast_one,
        ghCharge_odd]
      exact add_comm 1 _

/-- The words of ghost number `n`. -/
def ghWordsAt (n : ℤ) : Set SFWord := {l : SFWord | ghNum l = n}

/-- **The ghost-number grading of the Fock space.**  The BRST route to `W`-algebras needs the
BRST current to be graded by this, so it is exposed as a full internal decomposition rather than
merely as the operator `Ngh`. -/
noncomputable def ghostGrading (n : ℤ) : Submodule ℂ FockSF :=
  Submodule.span ℂ (stWordSF '' ghWordsAt n)

theorem stWordSF_mem_ghostGrading (l : SFWord) : stWordSF l ∈ ghostGrading (ghNum l) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- The vacuum has ghost number `0` — it is the empty word. -/
theorem vacSF_mem_ghostGrading : vacSF ∈ ghostGrading 0 := by
  have h := stWordSF_mem_ghostGrading []
  rwa [ghNum_nil, stWordSF_nil] at h

theorem ghostGrading_le_eigenspace (n : ℤ) :
    ghostGrading n ≤ Module.End.eigenspace Ngh ((n : ℤ) : ℂ) := by
  rw [ghostGrading, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ghNum l = n := hl
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Ngh_stWordSF, hl']

/-- **The ghost-number pieces are independent** — they sit inside the eigenspaces of the single
operator `N_gh`, reindexed along the injection `ℤ ↪ ℂ`. -/
theorem ghostGrading_iSupIndep : iSupIndep ghostGrading := by
  have h := (Module.End.eigenspaces_iSupIndep Ngh).comp
    (f := fun n : ℤ => ((n : ℤ) : ℂ)) Int.cast_injective
  exact h.mono (fun n => ghostGrading_le_eigenspace n)

theorem ghostGrading_iSup_eq_top : ⨆ n : ℤ, ghostGrading n = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← stWordSF_span, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact le_iSup ghostGrading (ghNum l) (stWordSF_mem_ghostGrading l)

/-- **The ghost Fock space is the internal direct sum of its ghost-number spaces.** -/
theorem ghostGrading_isInternal : DirectSum.IsInternal ghostGrading :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ghostGrading_iSupIndep ghostGrading_iSup_eq_top

/-- The ghost-number grading refines the Clifford parity: the ghost-number-`n` piece is contained
in the parity-`n mod 2` piece. -/
theorem ghostGrading_le_evenOdd (n : ℤ) :
    ghostGrading n ≤ evenOdd QSF ((n : ℤ) : ZMod 2) := by
  rw [ghostGrading, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ghNum l = n := hl
  rw [SetLike.mem_coe, ← hl', ghNum_mod_two]
  exact stWordSF_mem_evenOdd l

/-- `N_gh` is an even derivation of the Fock algebra — ghost numbers add under multiplication of
states, which is the whole content of the grading. -/
theorem Ngh_mul (x y : FockSF) : Ngh (x * y) = x * Ngh y + Ngh x * y := derivOf_mul _ x y

@[simp] theorem Ngh_vac : Ngh vacSF = 0 := derivOf_one _

@[simp] theorem ghNum_single (p : ℕ × Fin 2) : ghNum [p] = ghCharge p.2 := by
  rw [ghNum_cons, ghNum_nil, add_zero]

/-- A one-letter word creates the corresponding Clifford generator. -/
theorem stWordSF_singleton (p : ℕ × Fin 2) :
    stWordSF [p] = ι QSF (Finsupp.single p (1 : ℂ)) := by
  rw [stWordSF_cons, stWordSF_nil, mul_one]

/-- **Sign check**: `c₍₋₁₎|0⟩` has ghost number `+1`. -/
theorem c_mem_ghostGrading_one :
    ι QSF (Finsupp.single ((0, 1) : ℕ × Fin 2) (1 : ℂ)) ∈ ghostGrading 1 := by
  have h := stWordSF_mem_ghostGrading [((0, 1) : ℕ × Fin 2)]
  rwa [stWordSF_singleton, show ghNum [((0, 1) : ℕ × Fin 2)] = 1 from by decide] at h

/-- **Sign check**: `b₍₋₁₎|0⟩` has ghost number `-1`. -/
theorem b_mem_ghostGrading_neg_one :
    ι QSF (Finsupp.single ((0, 0) : ℕ × Fin 2) (1 : ℂ)) ∈ ghostGrading (-1) := by
  have h := stWordSF_mem_ghostGrading [((0, 0) : ℕ × Fin 2)]
  rwa [stWordSF_singleton, show ghNum [((0, 0) : ℕ × Fin 2)] = -1 from by decide] at h

/-! ## §5  Word fields and the vertex operator

Exactly the pattern of `Examples/SymplecticFermionWords`: scaled derivatives of the generator
fields, iterated super normal-ordered products over words, and `reconstructε`.  A word of length
`n` has parity `n`, so two word fields are `ε`-local at `koszul n m` and the product forming a
word of length `n+1` is taken at `koszul 1 n`.

The creation monomials are the **same** `stWordSF` as in the symplectic case — the Fock space and
its creation operators are shared — so `stWordSF_span` and `stWordSF_parity_split` are reused
verbatim as `reconstructε`'s `hspan` and `hparity`. -/

/-- The **scaled generator field** `(k!)⁻¹ ∂_z^k a(z)`, whose `z⁰`-coefficient is the creation
mode `a₍₋k₋₁₎`. -/
noncomputable def ghGenField (a : Fin 2) (k : ℕ) : FormalDist (End ℂ FockSF) :=
  (k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (ghField a))

theorem ghGenField_isField (a : Fin 2) (k : ℕ) : IsField (ghGenField a k) := by
  intro x
  obtain ⟨B, hB⟩ := (ghField_isField a).deriv_iterate k x
  exact ⟨B, fun n hn => by
    change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (ghField a)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

theorem ghGenField_localε (a b : Fin 2) (j k : ℕ) :
    Localε (-1) (ghGenField a j) (ghGenField b k) := by
  have h : Localε (-1) ((VOA.deriv^[j]) (ghField a))
      ((VOA.deriv^[k]) (ghField b)) :=
    ((ghField_localε a b).deriv_iterate_left j).deriv_iterate_right k
  exact Localε.smul_right (by norm_num) _ (Localε.smul_left _ _ h)

theorem ghGenField_DCovariant (a : Fin 2) (k : ℕ) : DCovariant T (ghGenField a k) :=
  Reconstruction.DCovariant.smul ((k.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate (ghField_DCovariant a) k)

theorem ghGenField_vacuum_neg (a : Fin 2) (k : ℕ) {q : ℤ} (hq : q < 0) :
    ghGenField a k q vacSF = 0 := by
  change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (ghField a)) q) vacSF = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range k, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (k : ℤ) < 0
  · rw [ghField_neg_vac a (q + (k : ℤ)) hqi, smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The generator field's `z⁰`-coefficient is `ghField` at index `k` — i.e. the creation mode
`a₍₋k₋₁₎`.  The factorial cancels against the falling factorial from `∂^k`. -/
theorem ghGenField_zero (a : Fin 2) (k : ℕ) : (ghGenField a k) 0 = ghField a (k : ℤ) := by
  change (k.factorial : ℂ)⁻¹ • ((VOA.deriv^[k] (ghField a)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range k, ((0 : ℤ) + 1 + (m : ℤ))) = (k.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (k.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul,
    show (0 : ℤ) + (k : ℤ) = (k : ℤ) from by ring]

theorem ghGenField_zero_vac (a : Fin 2) (k : ℕ) :
    ghGenField a k 0 vacSF = ι QSF (Finsupp.single ((k, a) : ℕ × Fin 2) (1 : ℂ)) := by
  rw [ghGenField_zero, ghField, if_pos (by positivity)]
  change creBase (((k : ℤ)).toNat, a) vacSF = _
  rw [creBase, Int.toNat_natCast]
  change ι QSF (Finsupp.single ((k, a) : ℕ × Fin 2) (1 : ℂ)) * (1 : FockSF) = _
  rw [mul_one]

/-! ### Word fields -/

/-- The iterated super normal-ordered product over a word, with its field witness. -/
noncomputable def YwordGhF : SFWord → { f : FormalDist (End ℂ FockSF) // IsField f }
  | [] => ⟨idField, idField_isField⟩
  | (p :: rest) =>
      let q := YwordGhF rest
      ⟨nprodε (koszul 1 (rest.length : ZMod 2)) (ghGenField_isField p.2 p.1) q.2,
       IsField.nprodε _ (ghGenField_isField p.2 p.1) q.2⟩

/-- The word field. -/
noncomputable def YwordGh (l : SFWord) : FormalDist (End ℂ FockSF) := (YwordGhF l).1

theorem YwordGh_isField (l : SFWord) : IsField (YwordGh l) := (YwordGhF l).2

@[simp] theorem YwordGh_nil : YwordGh [] = idField := rfl

theorem YwordGh_cons (p : ℕ × Fin 2) (rest : SFWord) :
    YwordGh (p :: rest)
      = nprodε (koszul 1 (rest.length : ZMod 2)) (ghGenField_isField p.2 p.1)
        (YwordGh_isField rest) := rfl

/-- A generator field is `koszul 1 (len l)`-local with every word field. -/
theorem ghGenField_localε_Yword (a : Fin 2) (k : ℕ) :
    ∀ l : SFWord, Localε (koszul 1 (l.length : ZMod 2)) (ghGenField a k) (YwordGh l)
  | [] => by
      rw [YwordGh_nil]
      simpa using (localε_one_iff _ _).mpr (Local_idField_right (ghGenField a k))
  | (p :: rest) => by
      have ih := ghGenField_localε_Yword a k rest
      have hstep :
          Localε (koszul 1 1 * koszul (rest.length : ZMod 2) 1)
            (YwordGh (p :: rest)) (ghGenField a k) := by
        rw [YwordGh_cons]
        exact dong_negε (koszul_mul_self 1 (rest.length : ZMod 2))
          (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
          (ghGenField_localε_Yword p.2 p.1 rest)
          (by simpa using ghGenField_localε p.2 a p.1 k)
          (by rw [koszul_comm]; exact Localε.symm (koszul_mul_self 1 _) ih)
      have hsign : koszul 1 1 * koszul (rest.length : ZMod 2) 1
          = koszul 1 (((p :: rest).length : ℕ) : ZMod 2) := by
        rw [← koszul_add_left, koszul_comm]
        congr 1
        push_cast [List.length_cons]
        ring
      rw [hsign] at hstep
      exact Localε.symm (koszul_mul_self _ _) hstep

/-- **Word fields are pairwise `ε`-local at the Koszul sign of their lengths.** -/
theorem YwordGh_localε : ∀ l₁ l₂ : SFWord,
    Localε (koszul (l₁.length : ZMod 2) (l₂.length : ZMod 2)) (YwordGh l₁) (YwordGh l₂)
  | [], l₂ => by
      rw [YwordGh_nil]
      simpa using (localε_one_iff _ _).mpr (Local_idField_left (YwordGh l₂))
  | (p :: rest), l₂ => by
      have hstep :
          Localε (koszul 1 (l₂.length : ZMod 2) * koszul (rest.length : ZMod 2)
              (l₂.length : ZMod 2)) (YwordGh (p :: rest)) (YwordGh l₂) := by
        rw [YwordGh_cons]
        exact dong_negε (koszul_mul_self 1 (rest.length : ZMod 2))
          (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
          (ghGenField_localε_Yword p.2 p.1 rest)
          (ghGenField_localε_Yword p.2 p.1 l₂)
          (YwordGh_localε rest l₂)
      have hsign : koszul 1 (l₂.length : ZMod 2)
            * koszul (rest.length : ZMod 2) (l₂.length : ZMod 2)
          = koszul (((p :: rest).length : ℕ) : ZMod 2) (l₂.length : ZMod 2) := by
        rw [← koszul_add_left]
        congr 1
        push_cast [List.length_cons]
        ring
      rw [hsign] at hstep
      exact hstep

theorem YwordGh_DCovariant : ∀ l : SFWord, DCovariant T (YwordGh l)
  | [] => by rw [YwordGh_nil]; exact DCovariant_idField T
  | (p :: rest) => by
      rw [YwordGh_cons]
      exact DCovariant.nprodε _ (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
        (ghGenField_DCovariant p.2 p.1) (YwordGh_DCovariant rest)

/-- **Creation tower (power-series part)**: `(YwordGh l)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordGh_vacuum_neg (l : SFWord) : ∀ {q : ℤ}, q < 0 → (YwordGh l) q vacSF = 0 := by
  induction l with
  | nil =>
      intro q hq
      rw [YwordGh_nil]
      change (if q = 0 then (LinearMap.id : End ℂ FockSF) else 0) vacSF = 0
      rw [if_neg (by omega : ¬ q = 0)]; rfl
  | cons p rest ih =>
      intro q hq
      rw [YwordGh_cons]
      exact nprodε_vacuum_neg_gen _ (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
        vacSF (fun s hs => ghGenField_vacuum_neg p.2 p.1 hs) (fun s hs => ih hs) hq

/-- **Creation tower (base)**: the word field creates its monomial from the vacuum.  The
monomials are the same `stWordSF` as in the symplectic-fermion case, because the creation
operators are the same. -/
theorem YwordGh_vacuum_base (l : SFWord) : (YwordGh l) 0 vacSF = stWordSF l := by
  induction l with
  | nil =>
      rw [YwordGh_nil]
      change (if (0 : ℤ) = 0 then (LinearMap.id : End ℂ FockSF) else 0) vacSF = stWordSF []
      rw [if_pos rfl]; rfl
  | cons p rest ih =>
      rw [YwordGh_cons,
        nprodε_vacuum_base_gen _ (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
          vacSF (fun s hs => ghGenField_vacuum_neg p.2 p.1 hs)
          (fun s hs => YwordGh_vacuum_neg rest hs),
        ih, ghGenField_zero, stWordSF_cons, ghField, if_pos (by positivity)]
      change creBase (((p.1 : ℕ) : ℤ).toNat, p.2) (stWordSF rest)
        = ι QSF (Finsupp.single p (1 : ℂ)) * stWordSF rest
      rw [creBase, Int.toNat_natCast]
      rfl

/-! ### The vertex operator -/

/-- **The `bc`-ghost vertex operator exists.**  `reconstructε` applied to the ghost word
fields, with `par := fun l => (l.length : ZMod 2)`.

`hspan` and `hparity` are `SympFerm.stWordSF_span` and `SympFerm.stWordSF_parity_split`: they are
statements about the Clifford algebra and its creation monomials, which the two theories share.
`hTvac` is `SympFerm.T_one`, because `vacSF` is by definition the algebra unit `1`. -/
theorem YGh_exists :
    ∃ YA : FockSF →ₗ[ℂ] FormalDist (End ℂ FockSF),
      (∀ l : SFWord, YA (stWordSF l) = YwordGh l) ∧
      (∀ u : FockSF, IsField (YA u)) ∧
      (∀ (p q : ZMod 2) (c d : SFWord →₀ ℂ),
          (∀ i ∈ c.support, ((i.length : ℕ) : ZMod 2) = p) →
          (∀ j ∈ d.support, ((j.length : ℕ) : ZMod 2) = q) →
          Localε (koszul p q) (YA (Finsupp.linearCombination ℂ stWordSF c))
            (YA (Finsupp.linearCombination ℂ stWordSF d))) ∧
      (∀ u : FockSF, (YA u) 0 vacSF = u) ∧
      (∀ u : FockSF, ∀ q : ℤ, q < 0 → (YA u) q vacSF = 0) ∧
      (∀ u : FockSF, DCovariant T (YA u)) :=
  reconstructε vacSF stWordSF YwordGh T (fun l : SFWord => ((l.length : ℕ) : ZMod 2))
    stWordSF_span stWordSF_parity_split YwordGh_isField YwordGh_localε
    YwordGh_vacuum_base (fun l _q hq => YwordGh_vacuum_neg l hq)
    T_one YwordGh_DCovariant

/-- **The vertex operator of the `bc`-ghost vertex superalgebra**, defined on all of the Fock
space. -/
noncomputable def YGh : FockSF →ₗ[ℂ] FormalDist (End ℂ FockSF) := YGh_exists.choose

theorem YGh_word (l : SFWord) : YGh (stWordSF l) = YwordGh l :=
  YGh_exists.choose_spec.1 l

theorem YGh_isField (u : FockSF) : IsField (YGh u) :=
  YGh_exists.choose_spec.2.1 u

/-- **Koszul locality** (VA4, super form), in the shape `reconstructε` produces. -/
theorem YGh_localε (p q : ZMod 2) (c d : SFWord →₀ ℂ)
    (hc : ∀ i ∈ c.support, ((i.length : ℕ) : ZMod 2) = p)
    (hd : ∀ j ∈ d.support, ((j.length : ℕ) : ZMod 2) = q) :
    Localε (koszul p q) (YGh (Finsupp.linearCombination ℂ stWordSF c))
      (YGh (Finsupp.linearCombination ℂ stWordSF d)) :=
  YGh_exists.choose_spec.2.2.1 p q c d hc hd

/-- **Creation** (VA3): `Y(u,z)|0⟩ = u + O(z)`. -/
theorem YGh_creation (u : FockSF) : (YGh u) 0 vacSF = u :=
  YGh_exists.choose_spec.2.2.2.1 u

/-- **Creation, singular part** (VA3). -/
theorem YGh_creation_neg (u : FockSF) {q : ℤ} (hq : q < 0) : (YGh u) q vacSF = 0 :=
  YGh_exists.choose_spec.2.2.2.2.1 u q hq

/-- **Translation covariance**: `[T, Y(u,z)] = ∂_z Y(u,z)`. -/
theorem YGh_DCovariant (u : FockSF) : DCovariant T (YGh u) :=
  YGh_exists.choose_spec.2.2.2.2.2 u

/-- The vacuum's vertex operator is the identity field. -/
theorem YGh_vacuum : YGh vacSF = idField := by
  have h := YGh_word []
  rwa [stWordSF_nil, YwordGh_nil] at h

/-- The state `a₍₋k₋₁₎|0⟩` carries the scaled generator field `(k!)⁻¹ ∂^k a(z)`. -/
theorem YGh_single (p : ℕ × Fin 2) :
    YGh (ι QSF (Finsupp.single p (1 : ℂ))) = YwordGh [p] := by
  have h := YGh_word [p]
  rwa [stWordSF_cons, stWordSF_nil, mul_one] at h

/-! ## §6  The conformal weight grading at `λ = 1`

`λ` finally enters.  With `b` of weight `λ` and `c` of weight `1-λ`, the state `a₍₋k₋₁₎|0⟩` has
weight `k + h_a`, so at `λ = 1` the weights are **natural numbers**: `b₍₋k₋₁₎|0⟩` has weight
`k + 1` and `c₍₋k₋₁₎|0⟩` has weight `k`.

The grading is built exactly as in `Examples/SymplecticFermionGrading`: as the eigenspace
decomposition of a single weight operator `L₀`, which is what makes independence free.

### The new ingredient: `c₍₋₁₎` has weight `0`

For symplectic fermions every creation mode has weight `≥ 1`, so a weight-`n` word has length
`≤ n` and only finitely many words have a given weight.  At `λ = 1` that fails: `c₍₋₁₎` has weight
`0`, so `[(0,1), (0,1), …]` are infinitely many words of weight `0`.  The finite dimensionality of
the weight spaces is nevertheless true, because all but finitely many of those words are
**zero**: a product of Clifford generators with a repeated factor vanishes when `Q = 0`.  That
fact (`stWordSF_eq_zero_of_not_nodup`) is proved here, and the weight-`h` space is then rewritten
as the span of the *duplicate-free* words of weight `h`, of which there are finitely many by a
pigeonhole on the finite alphabet of admissible modes. -/

/-- The conformal weight of the two ghost species **at `λ = 1`**: `b` has weight `1`, `c` has
weight `0`.  At general `λ` these are `λ` and `1-λ`; the value `λ = 1` — the one Drinfeld–Sokolov
reduction of `sl₂` needs — is also the one that makes the weights natural numbers. -/
def ghWt : Fin 2 → ℕ := fun a => if a = 0 then 1 else 0

@[simp] theorem ghWt_b : ghWt 0 = 1 := by decide

@[simp] theorem ghWt_c : ghWt 1 = 0 := by decide

/-- `λ + (1 - λ) = 1`: the two conjugate weights add to `1`.  This is what makes the ghost field
`a(z)` shift the conformal weight by exactly `h_a + j` at `z`-exponent `j` on **both** the
creation and the annihilation branch. -/
theorem ghWt_add_succ (a : Fin 2) : ghWt a + ghWt (a + 1) = 1 := by fin_cases a <;> decide

/-- The conformal weight of the creation mode indexed by `p = (k, a)`, namely `k + h_a`. -/
def ghModeWt (p : ℕ × Fin 2) : ℕ := p.1 + ghWt p.2

/-- The conformal weight of a creation monomial. -/
def ghWeight (l : SFWord) : ℕ := (l.map ghModeWt).sum

@[simp] theorem ghWeight_nil : ghWeight [] = 0 := rfl

@[simp] theorem ghWeight_cons (p : ℕ × Fin 2) (rest : SFWord) :
    ghWeight (p :: rest) = ghModeWt p + ghWeight rest := by
  simp [ghWeight]

/-- A natural-number list sum commutes with the cast into `ℂ`. -/
theorem sum_map_natCast (g : ℕ × Fin 2 → ℕ) (l : SFWord) :
    (l.map fun p => ((g p : ℕ) : ℂ)).sum = (((l.map g).sum : ℕ) : ℂ) := by
  induction l with
  | nil => simp
  | cons p rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add]

/-- **The weight operator `L₀`** of the ghost system at `λ = 1`. -/
noncomputable def L0Gh : Module.End ℂ FockSF :=
  derivOf (diagMap (fun p => ((ghModeWt p : ℕ) : ℂ)))

/-- **Every creation monomial is an `L₀`-eigenvector**, with eigenvalue its weight. -/
theorem L0Gh_stWordSF (l : SFWord) :
    L0Gh (stWordSF l) = ((ghWeight l : ℕ) : ℂ) • stWordSF l := by
  rw [L0Gh, derivOf_diag_stWordSF, sum_map_natCast]
  rfl

/-! ### Creation monomials with a repeated mode vanish -/

/-- At `Q = 0` a Clifford generator squares to zero. -/
theorem ι_sq_zero (v : SFModes) : ι QSF v * ι QSF v = 0 := by
  rw [ι_sq_scalar]
  change (algebraMap ℂ FockSF) (QSF v) = 0
  rw [show QSF v = 0 from rfl, map_zero]

/-- At `Q = 0` two Clifford generators anticommute. -/
theorem ι_mul_ι_eq_neg (v w : SFModes) : ι QSF v * ι QSF w = -(ι QSF w * ι QSF v) := by
  have h := ι_mul_ι_add_swap (Q := QSF) v w
  rw [show QuadraticMap.polar (⇑QSF) v w = 0 by simp [QuadraticMap.polar], map_zero] at h
  rw [eq_neg_iff_add_eq_zero]
  exact h

/-- Multiplying a word by a generator that already occurs in it gives `0`: move the new factor
past the word until it meets its twin, at the cost of a sign each time. -/
theorem ι_mul_stWordSF_eq_zero (p : ℕ × Fin 2) (l : SFWord) :
    p ∈ l → ι QSF (Finsupp.single p (1 : ℂ)) * stWordSF l = 0 := by
  induction l with
  | nil => intro hp; exact absurd hp (List.not_mem_nil)
  | cons q rest ih =>
      intro hp
      rw [stWordSF_cons]
      by_cases hpq : p = q
      · subst hpq
        rw [← mul_assoc, ι_sq_zero, zero_mul]
      · have hp' : p ∈ rest := by
          rcases List.mem_cons.mp hp with h | h
          · exact absurd h hpq
          · exact h
        rw [← mul_assoc, ι_mul_ι_eq_neg, neg_mul, mul_assoc, ih hp', mul_zero, neg_zero]

/-- **A creation monomial with a repeated mode is zero.**  This is what rescues finite
dimensionality once weight-`0` modes exist. -/
theorem stWordSF_eq_zero_of_not_nodup (l : SFWord) : ¬ l.Nodup → stWordSF l = 0 := by
  induction l with
  | nil => intro hl; exact absurd List.nodup_nil hl
  | cons q rest ih =>
      intro hl
      rw [stWordSF_cons]
      by_cases hq : q ∈ rest
      · exact ι_mul_stWordSF_eq_zero q rest hq
      · have hr : ¬ rest.Nodup := fun h => hl (List.nodup_cons.mpr ⟨hq, h⟩)
        rw [ih hr, mul_zero]

/-! ### The grading -/

/-- The words of conformal weight `h`. -/
def ghWtWordsAt (h : ℂ) : Set SFWord := {l : SFWord | (ghWeight l : ℂ) = h}

/-- **The conformal weight grading of the ghost Fock space at `λ = 1`.** -/
noncomputable def gradingGh (h : ℂ) : Submodule ℂ FockSF :=
  Submodule.span ℂ (stWordSF '' ghWtWordsAt h)

theorem stWordSF_mem_gradingGh (l : SFWord) : stWordSF l ∈ gradingGh (ghWeight l : ℂ) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

theorem vacSF_mem_gradingGh : vacSF ∈ gradingGh 0 := by
  have h := stWordSF_mem_gradingGh []
  rwa [ghWeight_nil, Nat.cast_zero, stWordSF_nil] at h

/-- **Weight check**: at `λ = 1`, `b₍₋₁₎|0⟩` has conformal weight `1`. -/
theorem b_mem_gradingGh_one :
    ι QSF (Finsupp.single ((0, 0) : ℕ × Fin 2) (1 : ℂ)) ∈ gradingGh 1 := by
  have h := stWordSF_mem_gradingGh [((0, 0) : ℕ × Fin 2)]
  rwa [stWordSF_singleton, show ghWeight [((0, 0) : ℕ × Fin 2)] = 1 from by decide,
    Nat.cast_one] at h

/-- **Weight check**: at `λ = 1`, `c₍₋₁₎|0⟩` has conformal weight `0` — this is the weight-`0`
mode that forces the duplicate-free rewriting above. -/
theorem c_mem_gradingGh_zero :
    ι QSF (Finsupp.single ((0, 1) : ℕ × Fin 2) (1 : ℂ)) ∈ gradingGh 0 := by
  have h := stWordSF_mem_gradingGh [((0, 1) : ℕ × Fin 2)]
  rwa [stWordSF_singleton, show ghWeight [((0, 1) : ℕ × Fin 2)] = 0 from by decide,
    Nat.cast_zero] at h

theorem gradingGh_le_eigenspace (h : ℂ) : gradingGh h ≤ Module.End.eigenspace L0Gh h := by
  rw [gradingGh, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((ghWeight l : ℕ) : ℂ) = h := hl
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, L0Gh_stWordSF, hl']

theorem gradingGh_iSupIndep : iSupIndep gradingGh :=
  (Module.End.eigenspaces_iSupIndep L0Gh).mono gradingGh_le_eigenspace

theorem gradingGh_iSup_eq_top : ⨆ h : ℂ, gradingGh h = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← stWordSF_span, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact le_iSup gradingGh ((ghWeight l : ℕ) : ℂ) (stWordSF_mem_gradingGh l)

/-- **The ghost Fock space is the internal direct sum of its conformal weight spaces.** -/
theorem gradingGh_isInternal : DirectSum.IsInternal gradingGh :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    gradingGh_iSupIndep gradingGh_iSup_eq_top

/-! ### Finite dimensionality -/

/-- Every letter of a word contributes its own weight to the total. -/
theorem ghModeWt_le_of_mem {l : SFWord} {p : ℕ × Fin 2} (hp : p ∈ l) : ghModeWt p ≤ ghWeight l := by
  induction l with
  | nil => exact absurd hp (List.not_mem_nil)
  | cons q rest ih =>
      rw [ghWeight_cons]
      rcases List.mem_cons.mp hp with h | h
      · subst h; omega
      · have := ih h; omega

/-- **Only finitely many duplicate-free words have a given weight.**  Weight `n` bounds every
level occurring in the word by `n` (since `ghModeWt (k,a) ≥ k`), so all letters come from the
finite alphabet `Fin (n+1) × Fin 2`; duplicate-freeness then bounds the length by the size of
that alphabet. -/
theorem ghWordsNodup_nat_finite (n : ℕ) :
    {l : SFWord | ghWeight l = n ∧ l.Nodup}.Finite := by
  refine Set.Finite.subset
    ((List.finite_length_le (Fin (n + 1) × Fin 2)
        (Fintype.card (Fin (n + 1) × Fin 2))).image
      fun l' : List (Fin (n + 1) × Fin 2) => l'.map fun q => ((q.1 : ℕ), q.2)) ?_
  rintro l ⟨hw, hnd⟩
  obtain ⟨l', hl'⟩ := exists_finList (n := n + 1) l fun p hp => by
    have h := ghModeWt_le_of_mem hp
    rw [ghModeWt] at h
    omega
  refine ⟨l', ?_, hl'⟩
  have hndl' : l'.Nodup :=
    List.Nodup.of_map (fun q : Fin (n + 1) × Fin 2 => ((q.1 : ℕ), q.2)) (by rw [hl']; exact hnd)
  change l'.length ≤ Fintype.card (Fin (n + 1) × Fin 2)
  exact hndl'.length_le_card

theorem ghWordsNodupAt_finite (h : ℂ) :
    {l : SFWord | (ghWeight l : ℂ) = h ∧ l.Nodup}.Finite := by
  by_cases hn : ∃ n : ℕ, (n : ℂ) = h
  · obtain ⟨n, rfl⟩ := hn
    refine (ghWordsNodup_nat_finite n).subset fun l hl => ?_
    exact ⟨Nat.cast_injective hl.1, hl.2⟩
  · refine Set.Finite.subset Set.finite_empty fun l hl => ?_
    exact absurd ⟨ghWeight l, hl.1⟩ hn

/-- The weight-`h` space is already spanned by the **duplicate-free** words of weight `h`: the
rest of the words are zero. -/
theorem gradingGh_eq_span_nodup (h : ℂ) :
    gradingGh h = Submodule.span ℂ (stWordSF '' {l : SFWord | (ghWeight l : ℂ) = h ∧ l.Nodup}) := by
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [gradingGh, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : ((ghWeight l : ℕ) : ℂ) = h := hl
    by_cases hnd : l.Nodup
    · exact Submodule.subset_span ⟨l, ⟨hl', hnd⟩, rfl⟩
    · rw [SetLike.mem_coe, stWordSF_eq_zero_of_not_nodup l hnd]
      exact Submodule.zero_mem _
  · rintro _ ⟨l, hl, rfl⟩
    exact ⟨l, hl.1, rfl⟩

/-- **Every conformal weight space is finite dimensional.** -/
theorem gradingGh_finrank (h : ℂ) : FiniteDimensional ℂ (gradingGh h) := by
  rw [gradingGh_eq_span_nodup]
  exact FiniteDimensional.span_of_finite ℂ ((ghWordsNodupAt_finite h).image stWordSF)

/-! ## §7  The `SuperVertexAlgebra` instance

The two compatibility axioms VA1 (`grading_mode`) and VA1′ (`parity_mode`) are traced through the
construction of `YGh` exactly as `Examples/SymplecticFermionInstance` does it: the basic Clifford
operators are graded, hence so are the ghost fields, hence — because weights and parities *add*
under the super normal-ordered product — so are the word fields; and being a graded field is a
linear condition on the state, so it propagates along the linear extension `YGh`.

The parity half is reused wholesale from `Examples/SymplecticFermionInstance`: `ParField`, its
closure lemmas, and the identification `evenOdd QSF r = span (stWordSF '' {|l| ≡ r})` are all
statements about the shared Clifford algebra. -/

/-- A **graded field of conformal weight `D`** for the ghost weight grading: the `zʲ`-coefficient
sends `𝒱_w` into `𝒱_{D+w+j}`. -/
def WtFieldGh (f : FormalDist (End ℂ FockSF)) (D : ℂ) : Prop :=
  ∀ (j : ℤ) (w : ℂ) (x : FockSF), x ∈ gradingGh w → f j x ∈ gradingGh (D + w + (j : ℂ))

theorem idField_WtFieldGh : WtFieldGh idField 0 := by
  intro j w x hx
  rw [idField_apply]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, LinearMap.id_apply,
      show (0 : ℂ) + w + (((0 : ℤ)) : ℂ) = w from by push_cast; ring]
    exact hx
  · rw [if_neg hj, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem WtFieldGh.smul (c : ℂ) {f : FormalDist (End ℂ FockSF)} {D : ℂ} (hf : WtFieldGh f D) :
    WtFieldGh (c • f) D := by
  intro j w x hx
  change c • (f j x) ∈ _
  exact Submodule.smul_mem _ _ (hf j w x hx)

/-- **Weights add under the super normal product**: the two shifts `Da + m` and `Db + (s - m)`
compose to `Da + Db + s`, the `m` cancelling. -/
theorem WtFieldGh.nprod (eps : ℂ) {a b : FormalDist (End ℂ FockSF)} (ha : IsField a)
    (hb : IsField b) {Da Db : ℂ} (hga : WtFieldGh a Da) (hgb : WtFieldGh b Db) :
    WtFieldGh (nprodε eps ha hb) (Da + Db) := by
  intro s w x hx
  rw [nprodε_apply]
  refine finsum_mem_submodule _ _ (normalOrderedε_diag_support_finite eps ha hb s x) (fun m => ?_)
  rw [normalOrderedε_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    change a m (b (s - m) x) ∈ _
    have hb' := hgb (s - m) w x hx
    have ha' := hga m (Db + w + (((s - m : ℤ)) : ℂ)) _ hb'
    rwa [show Da + (Db + w + (((s - m : ℤ)) : ℂ)) + ((m : ℤ) : ℂ)
        = Da + Db + w + ((s : ℤ) : ℂ) from by push_cast; ring] at ha'
  · rw [if_neg h0, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    change b (s - m) (a m x) ∈ _
    have ha' := hga m w x hx
    have hb' := hgb (s - m) (Da + w + ((m : ℤ) : ℂ)) _ ha'
    rwa [show Db + (Da + w + ((m : ℤ) : ℂ)) + (((s - m : ℤ)) : ℂ)
        = Da + Db + w + ((s : ℤ) : ℂ) from by push_cast; ring] at hb'

/-! ### The Clifford operators are graded for the ghost weight -/

theorem creBase_mapsTo_gradingGh (p : ℕ × Fin 2) (w : ℂ) :
    gradingGh w ≤ (gradingGh (w + ((ghModeWt p : ℕ) : ℂ))).comap (creBase p) := by
  rw [gradingGh, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((ghWeight l : ℕ) : ℂ) = w := hl
  subst hl'
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [creBase_stWordSF,
    show ((ghWeight l : ℕ) : ℂ) + ((ghModeWt p : ℕ) : ℂ) = ((ghWeight (p :: l) : ℕ) : ℂ) from by
      rw [ghWeight_cons]; push_cast; ring]
  exact stWordSF_mem_gradingGh (p :: l)

theorem creBase_mem_gradingGh (p : ℕ × Fin 2) {w : ℂ} {x : FockSF} (hx : x ∈ gradingGh w) :
    creBase p x ∈ gradingGh (w + ((ghModeWt p : ℕ) : ℂ)) :=
  creBase_mapsTo_gradingGh p w hx

/-- Contraction lowers the conformal weight by the weight of the mode it removes.  Induction on
the word, through the Leibniz recursion `annBase_stWordSF_cons`. -/
theorem annBase_stWordSF_mem_gradingGh (p : ℕ × Fin 2) (l : SFWord) :
    annBase p (stWordSF l) ∈ gradingGh (((ghWeight l : ℕ) : ℂ) - ((ghModeWt p : ℕ) : ℂ)) := by
  induction l with
  | nil => rw [annBase_stWordSF_nil]; exact Submodule.zero_mem _
  | cons q rest ih =>
      rw [annBase_stWordSF_cons]
      refine Submodule.sub_mem _ ?_ ?_
      · by_cases h : p = q
        · subst h
          rw [if_pos rfl, one_smul,
            show ((ghWeight (p :: rest) : ℕ) : ℂ) - ((ghModeWt p : ℕ) : ℂ)
                = ((ghWeight rest : ℕ) : ℂ) from by rw [ghWeight_cons]; push_cast; ring]
          exact stWordSF_mem_gradingGh rest
        · rw [if_neg h, zero_smul]
          exact Submodule.zero_mem _
      · rw [show ι QSF (Finsupp.single q (1 : ℂ)) * annBase p (stWordSF rest)
              = creBase q (annBase p (stWordSF rest)) from by rw [creBase, LinearMap.mulLeft_apply],
          show ((ghWeight (q :: rest) : ℕ) : ℂ) - ((ghModeWt p : ℕ) : ℂ)
              = (((ghWeight rest : ℕ) : ℂ) - ((ghModeWt p : ℕ) : ℂ)) + ((ghModeWt q : ℕ) : ℂ) from
            by rw [ghWeight_cons]; push_cast; ring]
        exact creBase_mem_gradingGh q ih

theorem annBase_mapsTo_gradingGh (p : ℕ × Fin 2) (w : ℂ) :
    gradingGh w ≤ (gradingGh (w - ((ghModeWt p : ℕ) : ℂ))).comap (annBase p) := by
  rw [gradingGh, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((ghWeight l : ℕ) : ℂ) = w := hl
  subst hl'
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  exact annBase_stWordSF_mem_gradingGh p l

theorem annBase_mem_gradingGh (p : ℕ × Fin 2) {w : ℂ} {x : FockSF} (hx : x ∈ gradingGh w) :
    annBase p x ∈ gradingGh (w - ((ghModeWt p : ℕ) : ℂ)) :=
  annBase_mapsTo_gradingGh p w hx

/-- **`a(z)` is a graded field of conformal weight `h_a`.**  Both branches use `ghWt_add_succ`:
on the annihilation branch the mode removed is of the *conjugate* species, whose weight is
`1 - h_a`, and the missing `1` is exactly the `+1` in `j ↦ -j-1`. -/
theorem ghField_mem_gradingGh (a : Fin 2) (j : ℤ) {w : ℂ} {x : FockSF} (hx : x ∈ gradingGh w) :
    ghField a j x ∈ gradingGh (((ghWt a : ℕ) : ℂ) + w + (j : ℂ)) := by
  have hsum : ((ghWt a : ℕ) : ℂ) + ((ghWt (a + 1) : ℕ) : ℂ) = 1 := by
    rw [← Nat.cast_add, ghWt_add_succ, Nat.cast_one]
  by_cases hj : 0 ≤ j
  · have hcast : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hj]
    have hgh : ghField a j x = creBase ((j.toNat, a) : ℕ × Fin 2) x := by
      rw [ghField, if_pos hj]; rfl
    rw [hgh, show ((ghWt a : ℕ) : ℂ) + w + (j : ℂ)
        = w + ((ghModeWt ((j.toNat, a) : ℕ × Fin 2) : ℕ) : ℂ) from by
      rw [ghModeWt, Nat.cast_add]
      change ((ghWt a : ℕ) : ℂ) + w + (j : ℂ) = w + (((j.toNat : ℕ) : ℂ) + ((ghWt a : ℕ) : ℂ))
      rw [hcast]; ring]
    exact creBase_mem_gradingGh _ hx
  · have hcast : (((-j - 1).toNat : ℕ) : ℂ) = -(j : ℂ) - 1 := by
      have h : (((-j - 1).toNat : ℕ) : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h
    have hgh : ghField a j x = annBase (((-j - 1).toNat, a + 1) : ℕ × Fin 2) x := by
      rw [ghField, if_neg hj]; rfl
    rw [hgh, show ((ghWt a : ℕ) : ℂ) + w + (j : ℂ)
        = w - ((ghModeWt (((-j - 1).toNat, a + 1) : ℕ × Fin 2) : ℕ) : ℂ) from by
      rw [ghModeWt, Nat.cast_add]
      change ((ghWt a : ℕ) : ℂ) + w + (j : ℂ)
        = w - ((((-j - 1).toNat : ℕ) : ℂ) + ((ghWt (a + 1) : ℕ) : ℂ))
      rw [hcast]
      linear_combination hsum]
    exact annBase_mem_gradingGh _ hx

/-- **`a(z)` is odd**: every coefficient flips the Clifford parity. -/
theorem ghField_mem_evenOdd (a : Fin 2) (j : ℤ) {r : ZMod 2} {x : FockSF}
    (hx : x ∈ evenOdd QSF r) : ghField a j x ∈ evenOdd QSF (1 + r) := by
  by_cases hj : 0 ≤ j
  · have hgh : ghField a j x = creBase ((j.toNat, a) : ℕ × Fin 2) x := by
      rw [ghField, if_pos hj]; rfl
    rw [hgh, add_comm]
    exact creBase_mem_evenOdd _ hx
  · have hgh : ghField a j x = annBase (((-j - 1).toNat, a + 1) : ℕ × Fin 2) x := by
      rw [ghField, if_neg hj]; rfl
    rw [hgh, add_comm]
    exact annBase_mem_evenOdd _ hx

/-! ### Graded word fields -/

theorem ghGenField_WtFieldGh (a : Fin 2) (k : ℕ) :
    WtFieldGh (ghGenField a k) ((k : ℂ) + ((ghWt a : ℕ) : ℂ)) := by
  intro j w x hx
  change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (ghField a)) j) x ∈ _
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range k, (j + 1 + (i : ℤ))), LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [show ((k : ℂ) + ((ghWt a : ℕ) : ℂ)) + w + ((j : ℤ) : ℂ)
      = ((ghWt a : ℕ) : ℂ) + w + (((j + (k : ℤ)) : ℤ) : ℂ) from by push_cast; ring]
  exact ghField_mem_gradingGh a (j + (k : ℤ)) hx

theorem ghGenField_ParField (a : Fin 2) (k : ℕ) : ParField (ghGenField a k) 1 := by
  intro j r x hx
  change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (ghField a)) j) x ∈ _
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range k, (j + 1 + (i : ℤ))), LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (ghField_mem_evenOdd a (j + (k : ℤ)) hx)

/-- **VA1 for the word fields**: the word field of `l` is a graded field of weight `l`. -/
theorem YwordGh_WtFieldGh (l : SFWord) : WtFieldGh (YwordGh l) ((ghWeight l : ℕ) : ℂ) := by
  induction l with
  | nil =>
      rw [YwordGh_nil, ghWeight_nil, Nat.cast_zero]
      exact idField_WtFieldGh
  | cons p rest ih =>
      rw [YwordGh_cons,
        show ((ghWeight (p :: rest) : ℕ) : ℂ)
            = (((p.1 : ℕ) : ℂ) + ((ghWt p.2 : ℕ) : ℂ)) + ((ghWeight rest : ℕ) : ℂ) from by
          rw [ghWeight_cons, ghModeWt]; push_cast; ring]
      exact WtFieldGh.nprod _ (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
        (ghGenField_WtFieldGh p.2 p.1) ih

/-- **VA1′ for the word fields**: a word of length `n` is a product of `n` odd fields. -/
theorem YwordGh_ParField (l : SFWord) : ParField (YwordGh l) ((l.length : ℕ) : ZMod 2) := by
  induction l with
  | nil =>
      rw [YwordGh_nil, List.length_nil, Nat.cast_zero]
      exact idField_ParField
  | cons p rest ih =>
      rw [YwordGh_cons,
        show (((p :: rest).length : ℕ) : ZMod 2) = 1 + ((rest.length : ℕ) : ZMod 2) from by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]]
      exact ParField.nprod _ (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
        (ghGenField_ParField p.2 p.1) ih

/-! ### Transport along `YGh` -/

/-- The states whose vertex operator is a graded field of weight `D`. -/
noncomputable def wtStatesGh (D : ℂ) : Submodule ℂ FockSF where
  carrier := {u : FockSF | WtFieldGh (YGh u) D}
  add_mem' := by
    intro u v hu hv j w x hx
    rw [map_add]
    change (YGh u) j x + (YGh v) j x ∈ _
    exact Submodule.add_mem _ (hu j w x hx) (hv j w x hx)
  zero_mem' := by
    intro j w x _
    rw [map_zero]
    change (0 : FockSF) ∈ _
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c u hu j w x hx
    rw [map_smul]
    change c • ((YGh u) j x) ∈ _
    exact Submodule.smul_mem _ _ (hu j w x hx)

/-- The states whose vertex operator has definite parity `s`. -/
noncomputable def parStatesGh (s : ZMod 2) : Submodule ℂ FockSF where
  carrier := {u : FockSF | ParField (YGh u) s}
  add_mem' := by
    intro u v hu hv j r x hx
    rw [map_add]
    change (YGh u) j x + (YGh v) j x ∈ _
    exact Submodule.add_mem _ (hu j r x hx) (hv j r x hx)
  zero_mem' := by
    intro j r x _
    rw [map_zero]
    change (0 : FockSF) ∈ _
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c u hu j r x hx
    rw [map_smul]
    change c • ((YGh u) j x) ∈ _
    exact Submodule.smul_mem _ _ (hu j r x hx)

theorem gradingGh_le_wtStatesGh (h : ℂ) : gradingGh h ≤ wtStatesGh h := by
  rw [gradingGh, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((ghWeight l : ℕ) : ℂ) = h := hl
  subst hl'
  have hw : WtFieldGh (YGh (stWordSF l)) ((ghWeight l : ℕ) : ℂ) := by
    rw [YGh_word]; exact YwordGh_WtFieldGh l
  exact hw

theorem evenOdd_le_parStatesGh (s : ZMod 2) : evenOdd QSF s ≤ parStatesGh s := by
  rw [evenOdd_eq_parityPieceSF, parityPieceSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((l.length : ℕ) : ZMod 2) = s := hl
  subst hl'
  have hp : ParField (YGh (stWordSF l)) ((l.length : ℕ) : ZMod 2) := by
    rw [YGh_word]; exact YwordGh_ParField l
  exact hp

/-- **VA1, field form.** -/
theorem YGh_WtFieldGh {h : ℂ} {u : FockSF} (hu : u ∈ gradingGh h) : WtFieldGh (YGh u) h :=
  gradingGh_le_wtStatesGh h hu

/-- **VA1′, field form.** -/
theorem YGh_ParField {p : ZMod 2} {u : FockSF} (hu : u ∈ evenOdd QSF p) : ParField (YGh u) p :=
  evenOdd_le_parStatesGh p hu

/-- **The `bc`-ghost super vertex algebra at `λ = 1`.**

Weight grading and finiteness from §6, parity grading from Mathlib's Clifford `ℤ/2`-grading, the
vertex operator from `reconstructε` (§5), and the two compatibility axioms from §7.

Spin–statistics fails here, as it must for a `bc` system: `b₍₋₁₎|0⟩` is odd of integer weight
`1`.  The extra structure the ghost system has over the symplectic fermions is the `ℤ`-grading
`ghostGrading` of §4, which is not part of the `SuperVertexAlgebra` data. -/
noncomputable def bcGhostSVA : SuperVertexAlgebra FockSF where
  grading := gradingGh
  isInternal := gradingGh_isInternal
  finrank := gradingGh_finrank
  parity := evenOdd QSF
  parity_isInternal := evenOdd_isInternal
  Y := YGh
  vacuum := vacSF
  vacuum_mem := vacSF_mem_gradingGh
  vacuum_parity := vacSF_mem_evenOdd
  grading_mode := by
    intro h k u hu v hv n
    have hmode := YGh_WtFieldGh hu (-n - 1) k v hv
    rwa [show h + k + (((-n - 1 : ℤ)) : ℂ) = h + k - (n : ℂ) - 1 from by push_cast; ring] at hmode
  parity_mode := by
    intro p q u hu v hv n
    exact YGh_ParField hu (-n - 1) q v hv
  vacuum_Y := by rw [YGh_vacuum, idFieldSF_eq_one]
  creation := by
    intro u
    refine ⟨?_, fun n hn => ?_⟩
    · have hidx : mode (YGh u) (-1) vacSF = (YGh u) 0 vacSF := by rw [mode_apply]; norm_num
      rw [hidx]
      exact YGh_creation u
    · rw [mode_apply]
      exact YGh_creation_neg u (by omega)
  locality := by
    intro p q u hu v hv
    rw [evenOdd_eq_parityPieceSF, parityPieceSF] at hu hv
    obtain ⟨c, hcs, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hu
    obtain ⟨d, hds, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hv
    have hc : ∀ i ∈ c.support, ((i.length : ℕ) : ZMod 2) = p := fun i hi =>
      (Finsupp.mem_supported ℂ c).mp hcs (Finset.mem_coe.mpr hi)
    have hd : ∀ j ∈ d.support, ((j.length : ℕ) : ZMod 2) = q := fun j hj =>
      (Finsupp.mem_supported ℂ d).mp hds (Finset.mem_coe.mpr hj)
    exact YGh_localε p q c d hc hd
  regularity := by
    intro u v
    obtain ⟨B, hB⟩ := YGh_isField u v
    refine ⟨-B, fun n hn => ?_⟩
    rw [mode_apply]
    exact hB (-n - 1) (by omega)

/-! ## §8  The stress tensor and the central charge

`L(z) = -λ :b(z) ∂c(z): + (1-λ) :(∂b)(z) c(z):` is the ghost stress tensor at parameter `λ`, and
its central charge is `c(λ) = -2(6λ² - 6λ + 1)`.  At `λ = 1` — the value Drinfeld–Sokolov
reduction of `sl₂` uses — this is `c = -2`, matching the Virasoro anomaly of the `sl₂` BRST
complex against `c_sug = 3k/(k+2)` and the `W`-algebra value `13 - 6(k+2) - 6/(k+2)`.

**What is and is not proved here.**  The field `LghField` is *defined*, and shown to be a field.
The Virasoro relation itself is stated as a `Prop` (`IsGhostVirasoro`) and **not proved**: the
mode computation is the analogue of `Examples/SymplecticFermionVirasoroA`/`B`, some 1550 lines,
and is not done here.  Nothing below is a theorem with a hole. -/

/-- **The central charge of a `bc` system of weights `(λ, 1-λ)`**: `c = -2(6λ² - 6λ + 1)`. -/
def ghostCentralCharge (lam : ℂ) : ℂ := -2 * (6 * lam ^ 2 - 6 * lam + 1)

/-- At `λ = 1` (`b` of weight `1`, `c` of weight `0`) the central charge is `-2`. -/
@[simp] theorem ghostCentralCharge_one : ghostCentralCharge 1 = -2 := by
  rw [ghostCentralCharge]; ring

/-- At `λ = 2` (the string-theory reparametrisation ghosts) the central charge is `-26`. -/
theorem ghostCentralCharge_two : ghostCentralCharge 2 = -26 := by
  rw [ghostCentralCharge]; ring

/-- The central charge is symmetric under `λ ↔ 1-λ`, i.e. under exchanging `b` and `c`. -/
theorem ghostCentralCharge_symm (lam : ℂ) :
    ghostCentralCharge (1 - lam) = ghostCentralCharge lam := by
  rw [ghostCentralCharge, ghostCentralCharge]; ring

/-- **The ghost stress tensor** `L(z) = -λ :b(z) ∂c(z): + (1-λ) :(∂b)(z) c(z):`, at the odd/odd
Koszul sign `ε = koszul 1 1 = -1`. -/
noncomputable def LghField (lam : ℂ) : FormalDist (End ℂ FockSF) :=
  (-lam) • nprodε (-1) (ghField_isField 0) ((ghField_isField 1).deriv)
    + (1 - lam) • nprodε (-1) ((ghField_isField 0).deriv) (ghField_isField 1)

theorem LghField_isField (lam : ℂ) : IsField (LghField lam) := by
  intro x
  obtain ⟨B1, h1⟩ := IsField.nprodε (-1) (ghField_isField 0) ((ghField_isField 1).deriv) x
  obtain ⟨B2, h2⟩ := IsField.nprodε (-1) ((ghField_isField 0).deriv) (ghField_isField 1) x
  refine ⟨min B1 B2, fun n hn => ?_⟩
  have e : LghField lam n x
      = (-lam) • ((nprodε (-1) (ghField_isField 0) ((ghField_isField 1).deriv)) n x)
        + (1 - lam) • ((nprodε (-1) ((ghField_isField 0).deriv) (ghField_isField 1)) n x) := rfl
  rw [e, h1 n (lt_of_lt_of_le hn (min_le_left _ _)), h2 n (lt_of_lt_of_le hn (min_le_right _ _)),
    smul_zero, smul_zero, add_zero]

/-- **The Virasoro modes of the ghost system**: `L` has conformal weight `2`, so `Lₙ` sits at
`z`-exponent `-n-2`. -/
noncomputable def Lgh (lam : ℂ) (n : ℤ) : End ℂ FockSF := LghField lam (-n - 2)

theorem Lgh_def (lam : ℂ) (n : ℤ) : Lgh lam n = LghField lam (-n - 2) := rfl

/-- **The target statement** for the `bc` system, stated as a `Prop` and deliberately left
unproved: the ghost modes close on the Virasoro algebra with central charge
`c(λ) = -2(6λ² - 6λ + 1)`.

`IsGhostVirasoro 1` is the `c = -2` statement that the Drinfeld–Sokolov reduction of `sl₂`
consumes.  Proving it is the exact analogue of `Examples/SymplecticFermionVirasoroA`/`B` for the
`bc` pairing; the pieces it needs — the mode formula, the double-contraction anomaly, and the
"commutes with all creation operators + kills the vacuum ⟹ scalar" lemma — are all in place in
those files. -/
def IsGhostVirasoro (lam : ℂ) : Prop :=
  ∀ m n : ℤ, Lgh lam m * Lgh lam n - Lgh lam n * Lgh lam m
    = ((m : ℂ) - (n : ℂ)) • Lgh lam (m + n)
      + (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * ghostCentralCharge lam else 0)
          • (1 : End ℂ FockSF)

end VOA.Ghost
