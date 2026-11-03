/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionSpan
import VOA.Examples.SymplecticFermionParity

/-!
# The vertex operator `YSF` of the symplectic-fermion vertex superalgebra

This is where the super-reconstruction layer pays off.  Everything the abstract theorem
`reconstructε` asks for has been proved on the symplectic-fermion side in the preceding files:

| `reconstructε` hypothesis | symplectic-fermion witness | file |
| --- | --- | --- |
| `hspan`   | `stWordSF_span`         | `SymplecticFermionSpan` |
| `hparity` | `stWordSF_parity_split` | `SymplecticFermionParity` |
| `hfield`  | `YwordSF_isField`       | `SymplecticFermionWords` |
| `hlocal`  | `YwordSF_localε`        | `SymplecticFermionWords` |
| `hcre0`   | `YwordSF_vacuum_base`   | `SymplecticFermionWords` |
| `hcreneg` | `YwordSF_vacuum_neg`    | `SymplecticFermionWords` |
| `hTvac`   | `T_one`                 | `SymplecticFermionT` |
| `hTcov`   | `YwordSF_DCovariant`    | `SymplecticFermionWords` |

so the only work left is plumbing: instantiate, then unpack the six-fold existential into named
declarations that downstream files can cite one at a time.

## The parity function

`par := fun l => (l.length : ZMod 2)`.  A word of length `n` is a product of `n` odd Clifford
generators, so its parity is `n mod 2`; this is the *only* choice compatible with
`YwordSF_localε`, which delivers `ε`-locality exactly at `koszul (len l₁) (len l₂)`.

Note that the parity is **not** determined by the conformal weight here: `χᵃ_{-k-1}|0⟩` has
weight `k+1`, an integer in *both* parities, so spin-statistics fails for symplectic fermions.
That is why the parity has to be carried around as independent data rather than read off the
grading, and why the eventual `ℂ`-grading → `ℤ`-grading transfer is gated on a separate
integrality hypothesis.

## Why the statements below are left in their raw shape

The locality conjunct in particular is phrased in terms of `Finsupp.linearCombination` over
parity-homogeneous supports rather than as a statement about two states of definite parity.
That is the form `reconstructε` produces, and it is the form that carries the information: the
sign `koszul p q` is a property of the *combination*, and the hypothesis that each support is
parity-pure is what makes a single sign apply at all.  Converting it into a statement about
`ParityGrading` components is a separate step and belongs with the file that builds the grading,
not here — reshaping it here would only force that file to unreshape it.
-/

namespace VOA.SympFerm

open VOA
open CliffordAlgebra
open Module (End)
open VOA.Reconstruction

/-! ## §1  The existence statement -/

/-- **The symplectic-fermion vertex operator exists.**  `reconstructε` applied to the word
fields: `vac := vacSF`, `st := stWordSF`, `fld := YwordSF`, `T := T`, and the length parity
`par := fun l => (l.length : ZMod 2)`.

All eight hypotheses are discharged by the named theorems tabulated in the module docstring;
`T_one` serves as `hTvac` because `vacSF` is by definition the algebra unit `1 : FockSF`. -/
theorem YSF_exists :
    ∃ YA : FockSF →ₗ[ℂ] FormalDist (End ℂ FockSF),
      (∀ l : SFWord, YA (stWordSF l) = YwordSF l) ∧
      (∀ u : FockSF, IsField (YA u)) ∧
      (∀ (p q : ZMod 2) (c d : SFWord →₀ ℂ),
          (∀ i ∈ c.support, ((i.length : ℕ) : ZMod 2) = p) →
          (∀ j ∈ d.support, ((j.length : ℕ) : ZMod 2) = q) →
          Localε (koszul p q) (YA (Finsupp.linearCombination ℂ stWordSF c))
            (YA (Finsupp.linearCombination ℂ stWordSF d))) ∧
      (∀ u : FockSF, (YA u) 0 vacSF = u) ∧
      (∀ u : FockSF, ∀ q : ℤ, q < 0 → (YA u) q vacSF = 0) ∧
      (∀ u : FockSF, DCovariant T (YA u)) :=
  reconstructε vacSF stWordSF YwordSF T (fun l : SFWord => ((l.length : ℕ) : ZMod 2))
    stWordSF_span stWordSF_parity_split YwordSF_isField YwordSF_localε
    YwordSF_vacuum_base (fun l _q hq => YwordSF_vacuum_neg l hq)
    T_one YwordSF_DCovariant

/-! ## §2  The vertex operator and its six properties

`Classical.choice` through `Exists.choose`.  Naming each conjunct separately is not cosmetic:
downstream every one of them is used in a different place — `YSF_word` to compute on generators,
`YSF_isField` and `YSF_localeps` to feed the superalgebra axioms, `YSF_creation` and
`YSF_creation_neg` for the vacuum axioms, `YSF_DCovariant` for the translation operator. -/

/-- **The vertex operator of the symplectic-fermion vertex superalgebra**, defined on *all* of
`FockSF` (not just on the creation monomials).  It is the unique linear extension of the word
fields, which is exactly what `reconstructε` constructs: linearity plus `YSF_word` pins it down
because `stWordSF_span` says the words exhaust the space. -/
noncomputable def YSF : FockSF →ₗ[ℂ] FormalDist (End ℂ FockSF) := YSF_exists.choose

/-- **`YSF` restricts to the word fields on the creation monomials.**  The defining property:
the abstract operator agrees with the concrete normal-ordered products we built by hand. -/
theorem YSF_word (l : SFWord) : YSF (stWordSF l) = YwordSF l :=
  YSF_exists.choose_spec.1 l

/-- **Every `YSF u` is a field** (VA5 regularity): applied to a fixed state it has only finitely
many nonvanishing negative modes. -/
theorem YSF_isField (u : FockSF) : IsField (YSF u) :=
  YSF_exists.choose_spec.2.1 u

/-- **Koszul locality** (VA4, super form).  Two states presented as parity-homogeneous
combinations of creation monomials — `c` supported in parity `p`, `d` in parity `q` — have
`ε`-local vertex operators at the Koszul sign `koszul p q`.

Kept exactly as `reconstructε` produces it; see the module docstring for why. -/
theorem YSF_localε (p q : ZMod 2) (c d : SFWord →₀ ℂ)
    (hc : ∀ i ∈ c.support, ((i.length : ℕ) : ZMod 2) = p)
    (hd : ∀ j ∈ d.support, ((j.length : ℕ) : ZMod 2) = q) :
    Localε (koszul p q) (YSF (Finsupp.linearCombination ℂ stWordSF c))
      (YSF (Finsupp.linearCombination ℂ stWordSF d)) :=
  YSF_exists.choose_spec.2.2.1 p q c d hc hd

/-- **Creation** (VA3): `Y(u,z)|0⟩ = u + O(z)`, i.e. the `z⁰` mode returns the state. -/
theorem YSF_creation (u : FockSF) : (YSF u) 0 vacSF = u :=
  YSF_exists.choose_spec.2.2.2.1 u

/-- **Creation, singular part** (VA3): `Y(u,z)|0⟩` has no pole — every strictly negative mode
kills the vacuum. -/
theorem YSF_creation_neg (u : FockSF) {q : ℤ} (hq : q < 0) : (YSF u) q vacSF = 0 :=
  YSF_exists.choose_spec.2.2.2.2.1 u q hq

/-- **Translation covariance**: `[T, u₍ₘ₎] = (m+1)·u₍ₘ₊₁₎` for every state `u`, i.e.
`[T, Y(u,z)] = ∂_z Y(u,z)`.  With `T_one` this is the pair of conditions that make `T` the
translation operator `L₋₁` of the superalgebra. -/
theorem YSF_DCovariant (u : FockSF) : DCovariant T (YSF u) :=
  YSF_exists.choose_spec.2.2.2.2.2 u

/-! ## §3  Immediate consequences

Two one-liners that will be wanted immediately and would otherwise be re-derived at every use
site. -/

/-- The vacuum's vertex operator is the identity field: the empty word is the vacuum, and
`YwordSF [] = idField`. -/
theorem YSF_vacuum : YSF vacSF = idField := by
  have h := YSF_word []
  rwa [stWordSF_nil, YwordSF_nil] at h

/-- The generator `χᵃ_{-k-1}|0⟩` carries the scaled generator field `(k!)⁻¹ ∂^k χᵃ`, because a
length-one word is a single generator field normal-ordered against the identity. -/
theorem YSF_single (p : ℕ × Fin 2) :
    YSF (ι QSF (Finsupp.single p (1 : ℂ))) = YwordSF [p] := by
  have h := YSF_word [p]
  rwa [stWordSF_cons, stWordSF_nil, mul_one] at h

end VOA.SympFerm
