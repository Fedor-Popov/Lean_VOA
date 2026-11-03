/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionVOA
import VOA.Core.SuperEvenPart

/-!
# The triplet algebra `W(2)` at `p = 2`

`tripletW2 : VertexOperatorAlgebra (evenOdd QSF 0)` — an honest **bosonic** vertex operator
algebra of central charge `c = -2`, obtained as the **even part of the symplectic-fermion super
vertex operator algebra**.

This is the `p = 2` member of the triplet family `W(p)`, the standard first example of a
logarithmic (`C₂`-cofinite but non-rational) conformal field theory.  Every ingredient is
already in the library:

* `Examples.SymplecticFermionVOA` supplies `sympFermSVOA : SuperVertexOperatorAlgebra FockSF`
  with `c = -2`;
* `Core.SuperEvenPart` supplies `SuperVertexOperatorAlgebra.evenPartVOA`, the `ℂ`-graded →
  `ℤ`-graded transfer that turns the parity-`0` subalgebra of a super VOA into a bosonic VOA.

So the whole content of this file is **discharging the one hypothesis** that transfer needs —
integrality of the weights — plus recording what the resulting object looks like.

## No lattice, no background charge, no screening

The usual construction of `W(p)` starts from a rank-one lattice vertex algebra with a
background charge and cuts out the kernel of a screening operator.  None of that appears here.
At `p = 2` the triplet algebra is simply the even part of a free (symplectic-fermion) theory,
and that is the route taken: `sympFermSVOA` is built from Clifford generators, and `W(2)` is
its `ZMod 2`-even subspace.  Nothing in this file mentions a lattice, an exponential vertex
operator, or a screening charge.

## Why integrality is free here (target (b))

`SuperVertexOperatorAlgebra.evenPartVOA` is deliberately **gated** on

`∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0`,

and that gate is not decoration: it fails in general.  Half-integer weights genuinely occur in
super vertex algebras (the doublet-type example that motivates `SuperNearVOA` has generators of
weight `5/2`), so a `ℂ`-grading is *not* automatically a `ℤ`-grading and the transfer cannot be
made unconditional.

For symplectic fermions it is nevertheless immediate, and for a reason worth stating precisely.
The generator `χᵃ` has conformal weight `1`, so the creation mode `χᵃ_{-k-1}` raises the weight
by `k + 1` and the word state `stWordSF l` has weight `sfWeight l = ∑ᵢ (kᵢ + 1) ∈ ℕ`.  Hence
**every** weight occurring in `FockSF` is a non-negative *integer* — in **both** parities.

That last clause is the interesting one.  Spin–statistics *fails* for symplectic fermions: the
odd fields `χᵃ` have integer weight `1`, not half-integer weight, which is exactly why the
symplectic-fermion theory is a genuinely super object with no `ℤ`-grading-by-parity, and also
exactly why the integrality hypothesis is trivial for it.  We do not have to look at the even
part at all: the ambient algebra already has no non-integral weight
(`gradingSF_eq_bot_of_not_intCast`), so a fortiori neither does `𝒱₀̄`.

## Main results

* `gradingSF_eq_bot_of_not_intCast` — no non-integer conformal weight occurs in `FockSF`.
* `sympFermSVOA_integralWeights` — (b), the hypothesis in the exact shape `evenPartVOA` wants.
* `tripletW2` — (a), the bosonic vertex operator algebra `W(2) = (FockSF)₀̄`.
* `tripletW2_centralCharge : tripletW2.centralCharge = -2` — (c).
* `evenPartSF_eq_span` — (d), the concrete description: `W(2)` is the span of the word states
  of **even length**, i.e. of the states created by an even number of fermionic modes.
* `tripletW2_grading_one : tripletW2.grading 1 = ⊥` — a sanity check with real content:
  `W(2)` has **no states of conformal weight 1**, since the weight-`1` states of `FockSF` are
  the `χᵃ_{-1}|0⟩`, which are odd.  (This is what makes `W(2)` interesting: after the vacuum
  the first states are `ω` at weight `2`, and the triplet of generators `W^a` sits at weight
  `3`.)
* `tripletW2_vacuum_ne_zero`, `tripletW2_conformalVector_ne_zero` — non-degeneracy, so that
  none of the above is a statement about the zero algebra: `W(2)` contains `|0⟩ ≠ 0` at
  weight `0` and `ω ≠ 0` at weight `2`, with nothing in between.

## References
* Kausch, *Symplectic fermions*, Nucl. Phys. B583 (2000) 513; Gaberdiel–Kausch, *A rational
  logarithmic conformal field theory*; Adamović–Milas on `W(p)`.
* `Core.SuperEvenPart` for the transfer this file uses.
-/

namespace VOA.SympFerm

open VOA
open CliffordAlgebra

/-! ## §1  Integrality: `FockSF` has no non-integral conformal weights

`sfWordsAt h` is by definition the set of words `l` with `(sfWeight l : ℂ) = h`, and
`sfWeight l` is a natural number.  So a non-integral `h` is attained by no word at all, and the
weight-`h` piece — the span of the weight-`h` word states — is `⊥`. -/

/-- No word has a non-integral weight: `sfWeight l` is a natural number, so if `h` is not the
cast of an integer then no word sits at weight `h`. -/
theorem sfWordsAt_eq_empty_of_not_intCast {h : ℂ} (hh : ¬ ∃ n : ℤ, (n : ℂ) = h) :
    sfWordsAt h = ∅ := by
  ext l
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hl
  have hc : ((sfWeight l : ℕ) : ℂ) = h := hl
  exact hh ⟨(sfWeight l : ℤ), by exact_mod_cast hc⟩

/-- **Every conformal weight of `FockSF` is an integer.**  Strictly stronger than what the
even part needs, and stronger than `positivity`: it holds in *both* parities, because
spin–statistics fails here and the odd fields `χᵃ` have integer weight `1`. -/
theorem gradingSF_eq_bot_of_not_intCast {h : ℂ} (hh : ¬ ∃ n : ℤ, (n : ℂ) = h) :
    gradingSF h = ⊥ := by
  rw [gradingSF, sfWordsAt_eq_empty_of_not_intCast hh, Set.image_empty, Submodule.span_empty]

/-- **The integrality hypothesis of `SuperVertexOperatorAlgebra.evenPartVOA`**, in the exact
shape that definition consumes.

The hypothesis is stated about the even part only, because that is all the transfer needs and
all that is true for the doublet.  Here it is proved without ever looking at the parity: the
ambient algebra already has no non-integral weight. -/
theorem sympFermSVOA_integralWeights (h : ℂ) (hh : ¬ ∃ n : ℤ, (n : ℂ) = h) :
    ∀ x ∈ sympFermSVOA.parity 0, x ∈ sympFermSVOA.grading h → x = 0 := by
  intro x _ hx
  have hx' : x ∈ gradingSF h := hx
  rw [gradingSF_eq_bot_of_not_intCast hh, Submodule.mem_bot] at hx'
  exact hx'

/-! ## §2  The triplet algebra `W(2)` -/

/-- **The triplet vertex operator algebra `W(2)`**: the even part of the
symplectic-fermion super VOA, as a genuinely bosonic, `ℤ`-graded `VertexOperatorAlgebra`.

Assembled from
* `sympFermSVOA` (`Examples.SymplecticFermionVOA`), the super VOA at `c = -2`, and
* `SuperVertexOperatorAlgebra.evenPartVOA` (`Core.SuperEvenPart`), the even-part transfer,

with the transfer's sole hypothesis discharged by `sympFermSVOA_integralWeights`.  The two
CFT-type conditions are inherited automatically: `positivity` already holds in the ambient
algebra (word weights are natural numbers) and `𝒱₀ = ℂ|0⟩` restricts to the even part because
the vacuum is even.

No lattice, no background charge, no screening operator. -/
noncomputable def tripletW2 : VertexOperatorAlgebra (evenOdd QSF 0) :=
  sympFermSVOA.evenPartVOA sympFermSVOA_integralWeights

/-- **The central charge of `W(2)` is `-2`**, inherited from the symplectic fermions: the
even part keeps the ambient conformal vector `ωSF`, hence the ambient Virasoro relation and the
ambient central charge. -/
@[simp] theorem tripletW2_centralCharge : tripletW2.centralCharge = -2 := rfl

/-- The vacuum of `W(2)` is the symplectic-fermion vacuum. -/
@[simp] theorem tripletW2_vacuum_coe :
    ((tripletW2.vacuum : evenOdd QSF 0) : FockSF) = vacSF := rfl

/-- The conformal vector of `W(2)` is `ωSF = -χ⁰₋₁χ¹₋₁|0⟩`, which is even (a two-letter word)
and therefore really does lie in the even part. -/
@[simp] theorem tripletW2_conformalVector_coe :
    ((tripletW2.conformalVector : evenOdd QSF 0) : FockSF) = ωSF := rfl

/-- The vertex operators of `W(2)` are the symplectic-fermion ones, restricted. -/
@[simp] theorem tripletW2_Y_coe (u : evenOdd QSF 0) (k : ℤ) (x : evenOdd QSF 0) :
    ((tripletW2.Y u k x : evenOdd QSF 0) : FockSF) = YSF u k x := rfl

/-- The `n`-th products of `W(2)` are the ambient ones. -/
@[simp] theorem tripletW2_smul_coe (u : evenOdd QSF 0) (n : ℤ) (v : evenOdd QSF 0) :
    ((tripletW2.smul u n v : evenOdd QSF 0) : FockSF) = mode (YSF u) n v := rfl

/-- **The `ℤ`-grading of `W(2)`** is the even part of the ambient weight space at the same
(integer) weight.  This is the transfer at work: the ambient index was `ℂ`. -/
@[simp] theorem tripletW2_grading (n : ℤ) :
    tripletW2.grading n = (gradingSF (n : ℂ)).comap (evenOdd QSF 0).subtype := rfl

/-- The Virasoro modes of `W(2)` are the symplectic-fermion `LSF n`, restricted.  So every
`Lₙ`-computation done on the super side — in particular `LSF_virasoro` at `c = -2` — is
available verbatim inside `W(2)`. -/
theorem tripletW2_L_coe (n : ℤ) (x : evenOdd QSF 0) :
    ((tripletW2.L n x : evenOdd QSF 0) : FockSF) = LSF n x := by
  rw [LSF_eq_mode]
  rfl

/-! ## §3  What `W(2)` is, concretely: the even-length words (target (d))

`evenOdd_eq_parityPieceSF` identifies the Clifford parity grading with the *length* grading of
the words.  At parity `0` that says: the even part is spanned by the states obtained from the
vacuum by an **even number** of fermionic creation modes. -/

/-- The parity-`0` words are the words of even length. -/
theorem sfWordsOfParity_zero : sfWordsOfParity (0 : ZMod 2) = {l : SFWord | Even l.length} := by
  ext l
  exact ZMod.natCast_eq_zero_iff_even

/-- **`W(2)` is the span of the even-length word states.**

`χ^{a₁}_{-k₁-1} ⋯ χ^{aₙ}_{-kₙ-1}|0⟩` lies in `W(2)` exactly when `n` is even.  The lowest such
states are `|0⟩` (`n = 0`) and, at `n = 2`, the weight-`2` state `ωSF` together with the rest of
the two-fermion sector. -/
theorem evenPartSF_eq_span :
    (evenOdd QSF (0 : ZMod 2) : Submodule ℂ FockSF)
      = Submodule.span ℂ (stWordSF '' {l : SFWord | Even l.length}) := by
  rw [evenOdd_eq_parityPieceSF, parityPieceSF, sfWordsOfParity_zero]

/-- An even-length word state belongs to `W(2)`. -/
theorem stWordSF_mem_evenPart {l : SFWord} (hl : Even l.length) :
    stWordSF l ∈ evenOdd QSF (0 : ZMod 2) := by
  have h := stWordSF_mem_evenOdd l
  rwa [ZMod.natCast_eq_zero_iff_even.mpr hl] at h

/-! ## §4  `W(2)` has no states of conformal weight `1`

A sanity check that is not bookkeeping: it says the even part is a *proper* subalgebra whose
low-lying spectrum differs from the ambient one.  The weight-`1` states of `FockSF` are the
`χᵃ_{-1}|0⟩`, one-letter words, hence odd; nothing of weight `1` survives to `W(2)`.

Combined with `vacuum_grade` (`W(2)₀ = ℂ|0⟩`) this pins the bottom of the spectrum: after the
vacuum the next state of `W(2)` is `ω` at weight `2`. -/

/-- A word of weight `1` has exactly one letter: each letter contributes at least `1`, and the
empty word has weight `0`. -/
theorem length_eq_one_of_sfWeight_eq_one {l : SFWord} (h : sfWeight l = 1) : l.length = 1 := by
  have hle := sfWeight_length_le l
  rw [h] at hle
  interval_cases hlen : l.length
  · exact absurd (by rw [List.eq_nil_of_length_eq_zero hlen] at h; exact h) (by decide)
  · rfl

/-- The weight-`1` subspace of `FockSF` is purely **odd**. -/
theorem gradingSF_one_le_evenOdd_one : gradingSF 1 ≤ evenOdd QSF (1 : ZMod 2) := by
  rw [gradingSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hc : ((sfWeight l : ℕ) : ℂ) = 1 := hl
  have h1 : sfWeight l = 1 := by exact_mod_cast hc
  have hmem := stWordSF_mem_evenOdd l
  rw [length_eq_one_of_sfWeight_eq_one h1, Nat.cast_one] at hmem
  exact hmem

/-- **`W(2)` has no conformal weight-`1` states.**  The ambient weight-`1` space is odd
(`gradingSF_one_le_evenOdd_one`) and the two parities are disjoint, so the even part meets it
in `0`. -/
theorem tripletW2_grading_one : tripletW2.grading 1 = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx' : (x : FockSF) ∈ gradingSF (((1 : ℤ) : ℂ)) := hx
  rw [Int.cast_one] at hx'
  have hodd : (x : FockSF) ∈ evenOdd QSF (1 : ZMod 2) := gradingSF_one_le_evenOdd_one hx'
  have heven : (x : FockSF) ∈ evenOdd QSF (0 : ZMod 2) := x.2
  have hdis := evenOdd_disjoint_succ (0 : ZMod 2)
  rw [zero_add] at hdis
  exact (Submodule.mem_bot ℂ).mpr
    (Subtype.ext (Submodule.disjoint_def.mp hdis _ heven hodd))

/-! ## §5  Non-degeneracy

Every statement above would be vacuously true of the zero algebra: `c = -2` says nothing if the
Virasoro modes act on `0`, and `W(2)₁ = ⊥` says nothing if `W(2) = ⊥`.  So we record that
`W(2)` is nonzero, and in fact strictly larger than `ℂ|0⟩`. -/

/-- The conformal vector is nonzero: `L₂ω = -|0⟩ ≠ 0` (`LSF_two_omega`), so `ω = 0` would
force `|0⟩ = 0`. -/
theorem omega_ne_zero : ωSF ≠ 0 := by
  intro h
  have h2 : (-vacSF : FockSF) = 0 := by rw [← LSF_two_omega, h, map_zero]
  exact one_ne_zero (neg_eq_zero.mp h2)

/-- **`W(2)` is not the zero algebra**: its vacuum is the Clifford unit `1 ≠ 0`. -/
theorem tripletW2_vacuum_ne_zero : tripletW2.vacuum ≠ 0 := by
  intro h
  have hc : (vacSF : FockSF) = 0 := by
    rw [← tripletW2_vacuum_coe, h, ZeroMemClass.coe_zero]
  exact one_ne_zero hc

/-- **`W(2)` is strictly larger than `ℂ|0⟩`**: it contains the nonzero weight-`2` state `ω`,
whereas `vacuum_grade` confines the weight-`0` states to `ℂ|0⟩` and `tripletW2_grading_one`
empties weight `1`.  So `W(2)` really is a nontrivial extension of the vacuum module, with `ω`
the first state above it. -/
theorem tripletW2_conformalVector_ne_zero : tripletW2.conformalVector ≠ 0 := by
  intro h
  have hc : (ωSF : FockSF) = 0 := by
    rw [← tripletW2_conformalVector_coe, h, ZeroMemClass.coe_zero]
  exact omega_ne_zero hc

end VOA.SympFerm
