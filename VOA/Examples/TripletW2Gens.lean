/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TripletW2
import VOA.Examples.TripletTTNull
import VOA.Modules.FiniteGenerationProof

/-!
# Abe's four strong generators of the triplet `W(2) = SF(1)⁺`

Abe, *A `ℤ₂`-orbifold model of the symplectic fermionic vertex operator superalgebra*,
Math. Z. **255** (2007) 755–792 (`arXiv:math/0503472`), **Cor. 3.8**: for `d = 1` the even part
`SF(1)⁺ = W(2)` is *strongly generated* by

  `ω = e₍₋₁₎f`,  `E = e₍₋₂₎e`,  `H = ½(e₍₋₂₎f + f₍₋₂₎e)`,  `F = f₍₋₂₎f`,

where `e, f` are the two symplectic fermions (weight `1`, odd).  This file **constructs those
four states inside `tripletW2`** and proves everything about them that does not need the
`C₂`-relations of Abe §3.3.

## Main results

* `abeSFe`, `abeSFf` — the two symplectic fermions as states of `FockSF`, and
  `letter_smul_letter` — the **master product formula**
  `(χᵃ₋₁|0⟩)₍₋ₖ₋₁₎(χᵇ₋₁|0⟩) = χᵃ₋ₖ₋₁χᵇ₋₁|0⟩`, proved from the reconstruction
  (`YSF_word` + `YwordSF_singleton`: a one-letter word carries the bare generator field
  `χᵃ(z)`, so its modes are literally the `chiM a n`).  Every identification below is this
  formula at `k = 0` and `k = 1`.
* `abeOmega`, `abeE`, `abeH`, `abeF` — Abe's four generators as elements of the subtype
  `evenOdd QSF 0` carrying `tripletW2`, together with `abeOmega_eq`, `abeE_eq`, `abeH_eq`,
  `abeF_eq` identifying each with the corresponding **ambient `n`-th product** of `e` and `f`.
  `abeOmega` is *not* a new state: it is `tripletW2.conformalVector`, and `abeOmega_eq` is the
  theorem `e₍₋₁₎f = ωSF` (see the normalisation remark below).
* `abeOmega_mem_grading_two`, `abeE/H/F_mem_grading_three` — the weights: `ω ∈ W(2)₂` and
  `E, H, F ∈ W(2)₃`.
* `abeGen_linearIndependent` — the four weight-`3` states `Gᵃᵇ = χᵃ₋₂χᵇ₋₁|0⟩` are
  **linearly independent**, hence `dim W(2)₃ ≥ 4`; and
  `abeGens_linearIndependent` — `ω, E, H, F` are linearly independent in `W(2)`.
  Both are proved by an explicit dual pairing `sfPair a b = χᵃ₂ ∘ χᵇ₁` built only from the CAR
  (`chiM_swap`), which kills weight `2` and is nondegenerate on weight `3`.
  In particular `abeE_ne_zero`, `abeH_ne_zero`, `abeF_ne_zero`, `abeGen_ne_zero`.
* `abeGens` — the generating **set** `{ω, E, H, F}`, `abeGens_homog` — its members are
  homogeneous (the hypothesis `hShom` of `iterProdSpan_eq_top`), `abeGens_finite`.
* `abeE_eq_neg_Wminus`, `abeF_eq_neg_Wplus`, `abeH_eq_neg_half_Wzero` — **Abe's `E, H, F`
  are the repo's triplet** `W⁻, W⁺, W⁰` of `Examples.TripletTTNull`, up to sign and a factor
  `½`.  So the two constructions are one triplet, not two, and `TripletTTNull`'s
  `LSF_one_WplusSF` (primarity) and `triplet_and_descendant_indep` transfer verbatim.
* `StrongGenAbe`, `SpanModO₂Abe`, `AbeSpanningEleven` — the three *named, unproved* `Prop`s that
  the repo's two entry points consume; see "Which shape" below.
* `c2Cofinite_of_abeSpanningEleven` — **`C2Cofinite tripletW2` from Abe Prop. 3.11 alone**,
  proved: no strong generation, no nilpotency, no `A₂`-algebra structure.

## ⚠ Normalisation: which fermion is `e`

The repo fixes the symplectic form by `sfOmega a b = ⟨χᵃ, χᵇ⟩` with `sfOmega 0 1 = 1`,
`sfOmega 1 0 = -1`, and fixes the conformal vector as `ωSF = -χ⁰₋₁χ¹₋₁|0⟩`
(`SymplecticFermionVirasoroA.ωSF`).  Abe's `ω = e₍₋₁₎f` therefore forces

  `e = χ¹₋₁|0⟩`,  `f = χ⁰₋₁|0⟩`,  i.e. `⟨e, f⟩ = sfOmega 1 0 = -1`,

and that is the identification taken here (`abeSFe`, `abeSFf`); with it `abeOmega_eq` reads
`e₍₋₁₎f = ωSF` **on the nose**.  The opposite labelling `e = χ⁰, f = χ¹` gives
`e₍₋₁₎f = -ωSF` (recorded as `letter_zero_one_smul_neg_one`), which would put a rival `ω` into
the file; it is *not* used.  Under the swap `e ↔ f` one has `E ↔ F` and `H ↦ H`, so the set
`{ω, E, H, F}` and every statement below are unaffected up to that relabelling.

## ⚠ Which shape do the repo's entry points want?  (they differ, and it matters)

* `Modules.FiniteGenerationProof.iterProdSpan_eq_top` **consumes**
  `⊤ = span ℂ S ⊔ O₂ W` (plus homogeneity of `S`) and **produces** `iterProdSpan W S = ⊤`.
* `Examples.TripletW2Nilpotent.c2Cofinite_of_span_sup_O₂` **consumes**
  `span ℂ F ⊔ O₂ W = ⊤` for finite `F` and **produces** `C2Cofinite W` outright.
* The nilpotency engine (`c2Cofinite_of_iterProdSpan_of_isNilpotent`) **consumes**
  `iterProdSpan W (range g) = ⊤` plus nilpotency of the classes `[gᵢ]`.

So both hypothesis-shapes are `span ⊔ O₂ = ⊤`, and on that shape `c2Cofinite_of_span_sup_O₂` is
strictly shorter: it needs no strong generation and no nilpotency.  **But the two are fed
different sets, and only one of the two is true here.**

* `SpanModO₂Abe` — `⊤ = span ℂ {ω, E, H, F} ⊔ O₂` — is the shape `iterProdSpan_eq_top` wants,
  but for these four generators it is **expected to be false**, and it is *not* formalised here
  in either direction.  Reason: it would give `dim A₂(W(2)) ≤ 4`, while the weight bookkeeping
  recorded in `Examples.TripletW2C2Direct` (finding (a)) counts `dim A₂(W(2)) ≥ 9` — classes
  `𝟙, ω, Wᵃ (3), ω², ωWᵃ (3)`.  That count is *their* calculation, cited not re-proved.  The
  `Prop` is named here only so that `strongGenAbe_of_spanModO₂` records the implication and
  that `StrongGenAbe` cannot usefully be obtained this way.
* `AbeSpanningEleven` — the same shape for Abe's **eleven-element** spanning set
  `{𝟙, ω, ω², ω³, ω⁴, E, ωE, H, ωH, F, ωF}` (Abe Prop. 3.11) — is Abe's actual statement, and it
  feeds `c2Cofinite_of_span_sup_O₂` (here: `c2Cofinite_of_abeSpanningEleven`) directly.
* `StrongGenAbe` — `iterProdSpan tripletW2 {ω, E, H, F} = ⊤` (Abe Prop. 3.7 / Cor. 3.8) — is what
  the *nilpotency* route needs.

So the honest summary is: on a *shared* hypothesis `span F ⊔ O₂ = ⊤` the nilpotency engine is
redundant (`c2Cofinite_of_span_sup_O₂` is six lines), but the two routes are fed **different**
`F`, and the four-generator instance is not the one that is true.  `AbeSpanningEleven` — eleven
elements, no nilpotency, no strong generation — is the shorter target, and it is the one this
file wires up.

## Status

Every declaration in this file is proved: no `sorry`, no `admit`, no `native_decide`, no new
axiom (the theorem `VOA.pbw` is not used).  `StrongGenAbe`,
`SpanModO₂Abe` and `AbeSpanningEleven` are `def`s of type `Prop` — *statements*, deliberately
unproved, and no
theorem here depends on them.

`abeGen a b` is definitionally `⟨stWordSF [(1,a),(0,b)], _⟩`, hence defeq to `gW a b` of
`Examples/TripletW2Nilpotent`; that file is **not** imported here, to keep this file independent
of a module under concurrent development.

### ⚠ What is *not* settled here

"Is the triplet really a triplet?" has two readings; only the first is settled below.

1. **In `W(2)₃`** — *proved*: `abeGen_linearIndependent`, `abeGens_indep`.  The four `Gᵃᵇ` are
   independent vectors of `W(2)`, so `E, H, F` really are three independent states and
   `ω, E, H, F` four.  In particular `dim_ℂ W(2)₃ ≥ 4`.
   ⚠ **Overlap disclosed**: `Examples.TripletTTNull.triplet_and_descendant_indep` already proves
   the weight-`3` independence in the basis `W⁺, W⁰, W⁻, L₋₁ω`, by a different device (its
   augmentation functionals `wordCoeff`).  §5 here is an independent re-derivation in Abe's
   basis `ω, E, H, F` — a different family (ours contains the weight-`2` vector `ω`, theirs the
   weight-`3` vector `L₋₁ω`) — from the CAR alone.  §5b reconciles the two.
2. **In `A₂(W(2))₃`** — *not proved*: that the classes `[G⁰⁰], [G¹¹], [G⁰¹]` stay independent
   modulo `O₂(W(2))`.  That needs the upper bound `O₂(W(2))₃ ≤ ℂ·L₋₁ω`, for which one still
   needs (i) extraction of a single graded component of `O₂` — the repo has
   `Modules.FiniteGeneration.O₂_eq_span_homGen` and `gen_mem_grading`, but no projection of
   `O₂ ⊓ 𝒱ₙ` onto the degree-`n` homogeneous generators — (ii) `W(2)₂ = ℂ·ω`, and (iii) the
   vacuum products `𝟙₍₋₂₎v = 0`, `u₍₋₂₎𝟙 = L₋₁u`, together with `tripletW2_grading_one`.
   Reading 2 is what would make the lower bound `dim A₂(W(2)) ≥ 9` rigorous.  It is open, and
   nothing here is stated as if it were closed.  (The weight-`4` half of that lower bound *is*
   closed elsewhere: `Examples.TripletTTNull.omega_sq_not_mem_O₂` proves `[ω]² ≠ 0` in
   `A₂(W(2))`.)

## References
* T. Abe, Math. Z. 255 (2007) 755–792 = `arXiv:math/0503472`, Prop. 2.2, Prop. 3.7, Cor. 3.8,
  Thm 3.9, Prop. 3.11.
* `Examples.TripletW2` (`tripletW2`, `tripletW2_grading`, `tripletW2_conformalVector_coe`);
  `Examples.SymplecticFermionVirasoroA` (`chiM`, `chiM_swap`, `ωSF`, `YwordSF_singleton`).
-/

namespace VOA.AbeGens

open VOA
open VOA.SympFerm
open CliffordAlgebra

/-! ## §1  One-letter words carry the bare fermion field

A one-letter word field is `nprodε` of the generator field against `idField`, which collapses
(`YwordSF_singleton`) to the generator field itself.  At level `k = 0` that generator field is
literally `chi a`, so the modes of the state `χᵃ₋₁|0⟩` are the modes `chiM a n`.  This is the
only place where the reconstruction is touched; everything downstream is the CAR. -/

/-- The vertex operator of the weight-`1` state `χᵃ₋₁|0⟩` is the bare fermion field `χᵃ(z)`. -/
theorem YSF_letter (a : Fin 2) : YSF (stWordSF [((0 : ℕ), a)]) = chi a := by
  rw [YSF_word, YwordSF_singleton]
  simp [sfGenField]

/-- Hence its `n`-th product operator is the mode `χᵃ_n`. -/
theorem mode_YSF_letter (a : Fin 2) (n : ℤ) :
    mode (YSF (stWordSF [((0 : ℕ), a)])) n = chiM a n := by
  rw [mode_apply, YSF_letter, chi_eq_chiM]
  congr 1
  ring

/-- A creation mode prepends a letter to a word state. -/
theorem chiM_cons (a : Fin 2) (k : ℕ) (l : SFWord) :
    chiM a (-(k : ℤ) - 1) (stWordSF l) = stWordSF ((k, a) :: l) := by
  rw [chiM_eq_creBase, creBase, LinearMap.mulLeft_apply, stWordSF_cons]

/-- **The master product formula**: `(χᵃ₋₁|0⟩)₍₋ₖ₋₁₎(χᵇ₋₁|0⟩) = χᵃ₋ₖ₋₁χᵇ₋₁|0⟩`.

All four of Abe's generators are instances of this: `ω` at `k = 0`, and `E, H, F` at `k = 1`. -/
theorem letter_smul_letter (a b : Fin 2) (k : ℕ) :
    mode (YSF (stWordSF [((0 : ℕ), a)])) (-(k : ℤ) - 1) (stWordSF [((0 : ℕ), b)])
      = stWordSF [(k, a), (0, b)] := by
  rw [mode_YSF_letter, chiM_cons]

/-! ## §2  Anticommutativity of the two-letter words -/

/-- The Clifford generators anticommute: `QSF = 0`, so the polarisation vanishes. -/
theorem abe_ι_anticomm (v w : SFModes) :
    ι QSF v * ι QSF w = -(ι QSF w * ι QSF v) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := QSF) v w
  rw [show QuadraticMap.polar (⇑QSF) v w = 0 from by simp [QuadraticMap.polar], map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Swapping the two letters of a two-letter word state flips the sign. -/
theorem stWordSF_swap_two (p q : ℕ × Fin 2) : stWordSF [p, q] = -stWordSF [q, p] := by
  simp only [stWordSF_cons, stWordSF_nil, mul_one]
  exact abe_ι_anticomm _ _

/-- Every two-letter word state is **even**, so it lies in `W(2) = (FockSF)₀̄`. -/
theorem stWord_two_mem_even (p q : ℕ × Fin 2) :
    stWordSF [p, q] ∈ evenOdd QSF (0 : ZMod 2) :=
  stWordSF_mem_evenPart ⟨1, rfl⟩

/-! ## §3  The two symplectic fermions `e` and `f`

Abe's `e, f` are the two odd weight-`1` states.  The labelling is forced by his `ω = e₍₋₁₎f`
together with the repo's `ωSF = -χ⁰₋₁χ¹₋₁|0⟩`: see the normalisation remark in the module
docstring.  Neither `e` nor `f` lies in `W(2)`; only their products do. -/

/-- Abe's symplectic fermion `e = χ¹₋₁|0⟩` (odd, weight `1`). -/
noncomputable def abeSFe : FockSF := stWordSF [((0 : ℕ), (1 : Fin 2))]

/-- Abe's symplectic fermion `f = χ⁰₋₁|0⟩` (odd, weight `1`). -/
noncomputable def abeSFf : FockSF := stWordSF [((0 : ℕ), (0 : Fin 2))]

/-- **`e₍₋₁₎f = ωSF`** — Abe's conformal vector is the repo's, on the nose.  This is what
pins the labelling `e = χ¹`, `f = χ⁰`; it is the reason no rival `ω` is introduced. -/
theorem abe_e_neg_one_f : mode (YSF abeSFe) (-1) abeSFf = ωSF := by
  have h := letter_smul_letter 1 0 0
  rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num] at h
  rw [abeSFe, abeSFf, h, stWordSF_swap_two ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2))]
  rfl

/-- The **opposite** labelling, recorded for the record: `(χ⁰₋₁|0⟩)₍₋₁₎(χ¹₋₁|0⟩) = -ωSF`.  Taking
`e = χ⁰, f = χ¹` would make Abe's `ω = e₍₋₁₎f` the *negative* of the repo's conformal vector. -/
theorem letter_zero_one_smul_neg_one :
    mode (YSF (stWordSF [((0 : ℕ), (0 : Fin 2))])) (-1) (stWordSF [((0 : ℕ), (1 : Fin 2))])
      = -ωSF := by
  have h := letter_smul_letter 0 1 0
  rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num] at h
  rw [h]
  exact (neg_neg _).symm

/-- `e₍₋₂₎e = χ¹₋₂χ¹₋₁|0⟩`. -/
theorem abe_e_neg_two_e :
    mode (YSF abeSFe) (-2) abeSFe = stWordSF [((1 : ℕ), (1 : Fin 2)), (0, 1)] := by
  have h := letter_smul_letter 1 1 1
  rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num] at h
  rw [abeSFe, h]

/-- `f₍₋₂₎f = χ⁰₋₂χ⁰₋₁|0⟩`. -/
theorem abe_f_neg_two_f :
    mode (YSF abeSFf) (-2) abeSFf = stWordSF [((1 : ℕ), (0 : Fin 2)), (0, 0)] := by
  have h := letter_smul_letter 0 0 1
  rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num] at h
  rw [abeSFf, h]

/-- `e₍₋₂₎f = χ¹₋₂χ⁰₋₁|0⟩`. -/
theorem abe_e_neg_two_f :
    mode (YSF abeSFe) (-2) abeSFf = stWordSF [((1 : ℕ), (1 : Fin 2)), (0, 0)] := by
  have h := letter_smul_letter 1 0 1
  rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num] at h
  rw [abeSFe, abeSFf, h]

/-- `f₍₋₂₎e = χ⁰₋₂χ¹₋₁|0⟩`. -/
theorem abe_f_neg_two_e :
    mode (YSF abeSFf) (-2) abeSFe = stWordSF [((1 : ℕ), (0 : Fin 2)), (0, 1)] := by
  have h := letter_smul_letter 0 1 1
  rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num] at h
  rw [abeSFe, abeSFf, h]

/-! ## §4  Abe's four strong generators inside `W(2)` -/

/-- The four weight-`3` even states `Gᵃᵇ = χᵃ₋₂χᵇ₋₁|0⟩` of `W(2)`.

Definitionally `⟨stWordSF [(1,a),(0,b)], _⟩`, hence defeq to `gW a b` of
`Examples/TripletW2Nilpotent` (not imported here). -/
noncomputable def abeGen (a b : Fin 2) : evenOdd QSF (0 : ZMod 2) :=
  ⟨stWordSF [(1, a), (0, b)], stWord_two_mem_even _ _⟩

@[simp] theorem abeGen_coe (a b : Fin 2) :
    ((abeGen a b : evenOdd QSF (0 : ZMod 2)) : FockSF) = stWordSF [(1, a), (0, b)] := rfl

/-- **Abe's `ω = e₍₋₁₎f`** — *the* conformal vector of `tripletW2`, not a new state
(`abe_e_neg_one_f`). -/
noncomputable def abeOmega : evenOdd QSF (0 : ZMod 2) := tripletW2.conformalVector

/-- **Abe's `E = e₍₋₂₎e`**. -/
noncomputable def abeE : evenOdd QSF (0 : ZMod 2) := abeGen 1 1

/-- **Abe's `F = f₍₋₂₎f`**. -/
noncomputable def abeF : evenOdd QSF (0 : ZMod 2) := abeGen 0 0

/-- **Abe's `H = ½(e₍₋₂₎f + f₍₋₂₎e)`**. -/
noncomputable def abeH : evenOdd QSF (0 : ZMod 2) :=
  (2⁻¹ : ℂ) • (abeGen 1 0 + abeGen 0 1)

@[simp] theorem abeOmega_coe :
    ((abeOmega : evenOdd QSF (0 : ZMod 2)) : FockSF) = ωSF := rfl

@[simp] theorem abeE_coe :
    ((abeE : evenOdd QSF (0 : ZMod 2)) : FockSF) = stWordSF [((1 : ℕ), (1 : Fin 2)), (0, 1)] :=
  rfl

@[simp] theorem abeF_coe :
    ((abeF : evenOdd QSF (0 : ZMod 2)) : FockSF) = stWordSF [((1 : ℕ), (0 : Fin 2)), (0, 0)] :=
  rfl

@[simp] theorem abeH_coe :
    ((abeH : evenOdd QSF (0 : ZMod 2)) : FockSF)
      = (2⁻¹ : ℂ) • (stWordSF [((1 : ℕ), (1 : Fin 2)), (0, 0)]
          + stWordSF [((1 : ℕ), (0 : Fin 2)), (0, 1)]) := rfl

/-! ### The identifications with Abe Cor. 3.8 -/

/-- `ω = e₍₋₁₎f`. -/
theorem abeOmega_eq :
    ((abeOmega : evenOdd QSF (0 : ZMod 2)) : FockSF) = mode (YSF abeSFe) (-1) abeSFf :=
  abe_e_neg_one_f.symm

/-- `E = e₍₋₂₎e`. -/
theorem abeE_eq :
    ((abeE : evenOdd QSF (0 : ZMod 2)) : FockSF) = mode (YSF abeSFe) (-2) abeSFe :=
  abe_e_neg_two_e.symm

/-- `F = f₍₋₂₎f`. -/
theorem abeF_eq :
    ((abeF : evenOdd QSF (0 : ZMod 2)) : FockSF) = mode (YSF abeSFf) (-2) abeSFf :=
  abe_f_neg_two_f.symm

/-- `H = ½(e₍₋₂₎f + f₍₋₂₎e)`. -/
theorem abeH_eq :
    ((abeH : evenOdd QSF (0 : ZMod 2)) : FockSF)
      = (2⁻¹ : ℂ) • (mode (YSF abeSFe) (-2) abeSFf + mode (YSF abeSFf) (-2) abeSFe) := by
  rw [abeH_coe, abe_e_neg_two_f, abe_f_neg_two_e]

/-! ### Conformal weights: `ω` at `2`, and `E, H, F` at `3` -/

/-- `Gᵃᵇ` has conformal weight `3`: the word `[(1,a),(0,b)]` has `sfWeight = 2 + 1 = 3`. -/
theorem abeGen_mem_grading_three (a b : Fin 2) : abeGen a b ∈ tripletW2.grading 3 := by
  have h : stWordSF [(1, a), (0, b)] ∈ gradingSF ((sfWeight [(1, a), (0, b)] : ℕ) : ℂ) :=
    stWordSF_mem_gradingSF _
  rw [tripletW2_grading 3]
  simpa only [Submodule.mem_comap, Submodule.coe_subtype, abeGen_coe,
    show sfWeight [(1, a), (0, b)] = 3 from rfl, Nat.cast_ofNat, Int.cast_ofNat] using h

/-- `ω ∈ W(2)₂` — the VOA axiom `conformal_mem`. -/
theorem abeOmega_mem_grading_two : abeOmega ∈ tripletW2.grading 2 :=
  tripletW2.conformalVector_mem_grading_two

/-- `E ∈ W(2)₃`. -/
theorem abeE_mem_grading_three : abeE ∈ tripletW2.grading 3 := abeGen_mem_grading_three 1 1

/-- `F ∈ W(2)₃`. -/
theorem abeF_mem_grading_three : abeF ∈ tripletW2.grading 3 := abeGen_mem_grading_three 0 0

/-- `H ∈ W(2)₃`. -/
theorem abeH_mem_grading_three : abeH ∈ tripletW2.grading 3 :=
  Submodule.smul_mem _ _
    (Submodule.add_mem _ (abeGen_mem_grading_three 1 0) (abeGen_mem_grading_three 0 1))

/-! ## §5  A dual pairing: the generators are nonzero and linearly independent

Everything in this section is pure CAR (`chiM_swap`, `chiM_vacuum`): no vertex operator, no
grading argument, no dimension count.  The pairing

  `Φᵃᵇ = χᵃ₂ ∘ χᵇ₁ : FockSF → FockSF`

lowers the conformal weight by `3`, hence lands in `ℂ|0⟩` on weight-`3` states, **annihilates
every weight-`2` state** (in particular `ω`), and is **nondegenerate** on the four `Gᵃᵇ`:

  `Φ^{a'b'}(Gᵃᵇ) = -2 ⟨χ^{a'}, χᵃ⟩ ⟨χ^{b'}, χᵇ⟩ |0⟩`,

which for `a' = a+1`, `b' = b+1` is `∓2|0⟩ ≠ 0` and vanishes for every other `Gᵃᵇ`.  That is a
genuine dual basis, so the four `Gᵃᵇ` are independent and `dim W(2)₃ ≥ 4`. -/

/-- `χᵇ_1` on a weight-`1` state: `χᵇ₁ χᶜ₋₁|0⟩ = ⟨χᵇ, χᶜ⟩ |0⟩`. -/
theorem chiM_one_letter (b c : Fin 2) :
    chiM b 1 (stWordSF [((0 : ℕ), c)]) = sfOmega b c • vacSF := by
  have hw : stWordSF [((0 : ℕ), c)] = chiM c (-1) vacSF := by
    have h := chiM_cons c 0 []
    rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num] at h
    exact h.symm
  rw [hw, chiM_swap, chiM_vacuum b (by norm_num), map_zero, neg_zero, zero_add, carC_apply,
    if_pos (by norm_num)]
  norm_num

/-- `χᵃ_2` **kills** every weight-`1` state: the CAR scalar is gated on `2 + (-1) = 0`. -/
theorem chiM_two_letter (a c : Fin 2) : chiM a 2 (stWordSF [((0 : ℕ), c)]) = 0 := by
  have hw : stWordSF [((0 : ℕ), c)] = chiM c (-1) vacSF := by
    have h := chiM_cons c 0 []
    rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num] at h
    exact h.symm
  rw [hw, chiM_swap, chiM_vacuum a (by norm_num), map_zero, neg_zero, zero_add, carC_apply,
    if_neg (by norm_num), zero_smul]

/-- `χᵃ_2` on the level-one state: `χᵃ₂ χᶜ₋₂|0⟩ = 2⟨χᵃ, χᶜ⟩|0⟩`. -/
theorem chiM_two_letter_lvl_one (a c : Fin 2) :
    chiM a 2 (stWordSF [((1 : ℕ), c)]) = (2 * sfOmega a c) • vacSF := by
  have hw : stWordSF [((1 : ℕ), c)] = chiM c (-2) vacSF := by
    have h := chiM_cons c 1 []
    rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num] at h
    exact h.symm
  rw [hw, chiM_swap, chiM_vacuum a (by norm_num), map_zero, neg_zero, zero_add, carC_apply,
    if_pos (by norm_num)]
  norm_num

/-- `χᵇ'_1` on `Gᵃᵇ`: it contracts the *second* letter and leaves `-⟨χᵇ', χᵇ⟩ χᵃ₋₂|0⟩`. -/
theorem chiM_one_gen (b' a b : Fin 2) :
    chiM b' 1 (stWordSF [((1 : ℕ), a), (0, b)])
      = (-sfOmega b' b) • stWordSF [((1 : ℕ), a)] := by
  have hw : stWordSF [((1 : ℕ), a), (0, b)] = chiM a (-2) (stWordSF [((0 : ℕ), b)]) := by
    have h := chiM_cons a 1 [((0 : ℕ), b)]
    rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num] at h
    exact h.symm
  have hlvl : stWordSF [((1 : ℕ), a)] = chiM a (-2) vacSF := by
    have h := chiM_cons a 1 []
    rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num] at h
    exact h.symm
  rw [hw, chiM_swap, carC_apply, if_neg (by norm_num), zero_smul, add_zero, chiM_one_letter,
    hlvl, map_smul, ← neg_smul]

/-- `χᵇ'_1` on a **weight-`2`** two-letter state: the result is a combination of weight-`1`
states, each of which `χᵃ'_2` then kills. -/
theorem chiM_one_two_letters (b' c d : Fin 2) :
    chiM b' 1 (stWordSF [((0 : ℕ), c), (0, d)])
      = (-sfOmega b' d) • stWordSF [((0 : ℕ), c)] + sfOmega b' c • stWordSF [((0 : ℕ), d)] := by
  have hw : stWordSF [((0 : ℕ), c), (0, d)] = chiM c (-1) (stWordSF [((0 : ℕ), d)]) := by
    have h := chiM_cons c 0 [((0 : ℕ), d)]
    rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num] at h
    exact h.symm
  have hlet : stWordSF [((0 : ℕ), c)] = chiM c (-1) vacSF := by
    have h := chiM_cons c 0 []
    rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num] at h
    exact h.symm
  rw [hw, chiM_swap, carC_apply, if_pos (by norm_num), chiM_one_letter, map_smul, hlet]
  norm_num

/-- **The pairing** `Φᵃᵇ = χᵃ₂ ∘ χᵇ₁`, as a `ℂ`-linear endomorphism of `FockSF`. -/
noncomputable def sfPair (a b : Fin 2) : Module.End ℂ FockSF := chiM a 2 * chiM b 1

theorem sfPair_apply (a b : Fin 2) (x : FockSF) :
    sfPair a b x = chiM a 2 (chiM b 1 x) := rfl

/-- **Nondegeneracy on weight `3`**: `Φ^{a'b'}(Gᵃᵇ) = -2⟨χ^{a'},χᵃ⟩⟨χ^{b'},χᵇ⟩|0⟩`. -/
theorem sfPair_gen (a' b' a b : Fin 2) :
    sfPair a' b' (stWordSF [((1 : ℕ), a), (0, b)])
      = (-(2 * sfOmega a' a * sfOmega b' b)) • vacSF := by
  rw [sfPair_apply, chiM_one_gen, map_smul, chiM_two_letter_lvl_one, smul_smul]
  congr 1
  ring

/-- **The pairing kills weight `2`** (two-letter words at level `0`). -/
theorem sfPair_two_letters (a' b' c d : Fin 2) :
    sfPair a' b' (stWordSF [((0 : ℕ), c), (0, d)]) = 0 := by
  rw [sfPair_apply, chiM_one_two_letters, map_add, map_smul, map_smul, chiM_two_letter,
    chiM_two_letter, smul_zero, smul_zero, add_zero]

/-- In particular `Φ^{a'b'}(ω) = 0`. -/
theorem sfPair_omega (a' b' : Fin 2) : sfPair a' b' ωSF = 0 := by
  change sfPair a' b' (-(stWordSF [((0 : ℕ), (0 : Fin 2)), (0, 1)])) = 0
  rw [map_neg, sfPair_two_letters, neg_zero]

/-! ### The computational core, and the two independence statements -/

/-- **The core**: in `FockSF` the only vanishing combination of `ω` and the four `Gᵃᵇ` is
the trivial one.  Proved by applying the four pairings `Φ^{a+1,b+1}`, each of which sees exactly
one `Gᵃᵇ` and is blind to `ω`; `ω ≠ 0` then finishes. -/
theorem coeff_eq_zero_of_comb (c : Fin 2 × Fin 2 → ℂ) (c₀ : ℂ)
    (h : c₀ • ωSF + ∑ p : Fin 2 × Fin 2, c p • stWordSF [((1 : ℕ), p.1), (0, p.2)] = 0) :
    c₀ = 0 ∧ ∀ p : Fin 2 × Fin 2, c p = 0 := by
  have key : ∀ a' b' : Fin 2,
      (∑ p : Fin 2 × Fin 2, c p * (-(2 * sfOmega a' p.1 * sfOmega b' p.2))) = 0 := by
    intro a' b'
    have h1 : sfPair a' b'
        (c₀ • ωSF + ∑ p : Fin 2 × Fin 2, c p • stWordSF [((1 : ℕ), p.1), (0, p.2)]) = 0 := by
      rw [h, map_zero]
    rw [map_add, map_smul, sfPair_omega, smul_zero, zero_add, map_sum] at h1
    simp only [map_smul, sfPair_gen, smul_smul] at h1
    rw [← Finset.sum_smul] at h1
    rcases smul_eq_zero.1 h1 with h3 | h3
    · exact h3
    · exact absurd h3 one_ne_zero
  have hc : ∀ p : Fin 2 × Fin 2, c p = 0 := by
    rintro ⟨i, j⟩
    have h1 := key (i + 1) (j + 1)
    rw [Fintype.sum_prod_type] at h1
    simp only [Fin.sum_univ_two] at h1
    fin_cases i <;> fin_cases j <;>
      simpa [sfOmega, sfSign, show ((0 : Fin 2) + 1 = 1) from rfl,
        show ((1 : Fin 2) + 1 = 0) from rfl] using h1
  refine ⟨?_, hc⟩
  have hzero : (∑ p : Fin 2 × Fin 2, c p • stWordSF [((1 : ℕ), p.1), (0, p.2)]) = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [hc p, zero_smul]
  rw [hzero, add_zero] at h
  rcases smul_eq_zero.1 h with h3 | h3
  · exact h3
  · exact absurd h3 omega_ne_zero

/-! ### Nonvanishing -/

/-- Each `Gᵃᵇ = χᵃ₋₂χᵇ₋₁|0⟩` is a **nonzero** vector of `FockSF`. -/
theorem stWord_gen_ne_zero (a b : Fin 2) : stWordSF [((1 : ℕ), a), (0, b)] ≠ 0 := by
  intro h
  have h1 := sfPair_gen (a + 1) (b + 1) a b
  rw [h, map_zero] at h1
  have h2 : (-(2 * sfOmega (a + 1) a * sfOmega (b + 1) b)) = 0 := by
    rcases smul_eq_zero.1 h1.symm with h3 | h3
    · exact h3
    · exact absurd h3 one_ne_zero
  revert h2
  fin_cases a <;> fin_cases b <;>
    simp [sfOmega, sfSign, show ((0 : Fin 2) + 1 = 1) from rfl,
      show ((1 : Fin 2) + 1 = 0) from rfl]

/-- `Gᵃᵇ ≠ 0` inside `W(2)`. -/
theorem abeGen_ne_zero (a b : Fin 2) : abeGen a b ≠ 0 := by
  intro h
  refine stWord_gen_ne_zero a b ?_
  have h1 := congrArg (fun z : evenOdd QSF (0 : ZMod 2) => (z : FockSF)) h
  simpa using h1

/-- `E ≠ 0`. -/
theorem abeE_ne_zero : abeE ≠ 0 := abeGen_ne_zero 1 1

/-- `F ≠ 0`. -/
theorem abeF_ne_zero : abeF ≠ 0 := abeGen_ne_zero 0 0

/-- `ω ≠ 0` — the repo's `tripletW2_conformalVector_ne_zero`. -/
theorem abeOmega_ne_zero : abeOmega ≠ 0 := tripletW2_conformalVector_ne_zero

/-- `H ≠ 0`.  `Φ⁰¹` sees the `G¹⁰` half of `H` and is blind to the `G⁰¹` half. -/
theorem abeH_ne_zero : abeH ≠ 0 := by
  intro h
  have hc : ((abeH : evenOdd QSF (0 : ZMod 2)) : FockSF) = 0 := by
    have h1 := congrArg (fun z : evenOdd QSF (0 : ZMod 2) => (z : FockSF)) h
    simpa using h1
  rw [abeH_coe] at hc
  have h2 := congrArg (fun x : FockSF => sfPair 0 1 x) hc
  simp only [map_smul, map_add, map_zero, sfPair_gen] at h2
  rw [← add_smul, smul_smul] at h2
  rcases smul_eq_zero.1 h2 with h3 | h3
  · revert h3
    simp [sfOmega, sfSign]
  · exact absurd h3 one_ne_zero

/-! ### Linear independence -/

/-- **The four `Gᵃᵇ` are linearly independent**, hence `dim_ℂ W(2)₃ ≥ 4`.  Combined with the
count `dim W(2)₃ = 4` (four even weight-`3` word states) they are a **basis** of `W(2)₃`. -/
theorem abeGen_linearIndependent :
    LinearIndependent ℂ (fun p : Fin 2 × Fin 2 => abeGen p.1 p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum p
  have hc : (∑ q : Fin 2 × Fin 2, g q • stWordSF [((1 : ℕ), q.1), (0, q.2)]) = (0 : FockSF) := by
    have h1 := congrArg (fun z : evenOdd QSF (0 : ZMod 2) => (z : FockSF)) hsum
    simpa using h1
  exact (coeff_eq_zero_of_comb g 0 (by rw [zero_smul, zero_add]; exact hc)).2 p

/-- **Abe's four generators are linearly independent**, in explicit form.

This is the statement a previous audit flagged as *claimed but unproved*: it says the three
weight-`3` generators `E, H, F` really are three independent states (and not, say, two
independent ones plus a multiple), and that `ω` is independent of them. -/
theorem abeGens_indep (c₀ c₁ c₂ c₃ : ℂ)
    (h : c₀ • abeOmega + c₁ • abeE + c₂ • abeH + c₃ • abeF = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  have hc : c₀ • ωSF + c₁ • stWordSF [((1 : ℕ), (1 : Fin 2)), (0, 1)]
      + c₂ • ((2⁻¹ : ℂ) • (stWordSF [((1 : ℕ), (1 : Fin 2)), (0, 0)]
          + stWordSF [((1 : ℕ), (0 : Fin 2)), (0, 1)]))
      + c₃ • stWordSF [((1 : ℕ), (0 : Fin 2)), (0, 0)] = (0 : FockSF) := by
    have h1 := congrArg (fun z : evenOdd QSF (0 : ZMod 2) => (z : FockSF)) h
    simpa using h1
  set c : Fin 2 × Fin 2 → ℂ := fun p => ![![c₃, c₂ * 2⁻¹], ![c₂ * 2⁻¹, c₁]] p.1 p.2 with hcdef
  have hsum : c₀ • ωSF + ∑ p : Fin 2 × Fin 2, c p • stWordSF [((1 : ℕ), p.1), (0, p.2)]
      = (0 : FockSF) := by
    rw [Fintype.sum_prod_type]
    simp only [hcdef, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hc]
    module
  obtain ⟨h0, hall⟩ := coeff_eq_zero_of_comb c c₀ hsum
  have h11 := hall (1, 1)
  have h00 := hall (0, 0)
  have h10 := hall (1, 0)
  simp only [hcdef, Matrix.cons_val_zero, Matrix.cons_val_one] at h11 h00 h10
  refine ⟨h0, h11, ?_, h00⟩
  have h2 : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
  exact (mul_eq_zero.1 h10).resolve_right h2

/-- The same, as a `LinearIndependent` statement about the family `![ω, E, H, F]`. -/
theorem abeGens_linearIndependent :
    LinearIndependent ℂ ![abeOmega, abeE, abeH, abeF] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  rw [Fin.sum_univ_four] at hsum
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons] at hsum
  obtain ⟨h0, h1, h2, h3⟩ := abeGens_indep (g 0) (g 1) (g 2) (g 3) hsum
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-! ## §5b  Abe's generators **are** the repo's triplet `W⁺, W⁰, W⁻`

`Examples.TripletTTNull` independently constructs the weight-`3` triplet as
`W⁺ = u₀₀`, `W⁰ = u₀₁ + u₁₀`, `W⁻ = u₁₁` with `u_{ab} = sfWgen a b = χᵃ₋₁χᵇ₋₂|0⟩`, proves them
nonzero and **primary** (`LSF_one_WplusSF` etc.), and proves
`triplet_and_descendant_indep : W⁺, W⁰, W⁻, L₋₁ω` independent.  Abe's `E, H, F` are those same
states up to sign and one factor of `½` — the two orderings `χᵃ₋₁χᵇ₋₂` and `χᵃ₋₂χᵇ₋₁` differ by
the Clifford sign (`stWordSF_swap_two`).  Recording the dictionary here means the two
constructions are not two rival triplets. -/

/-- `u_{ab} = χᵃ₋₁χᵇ₋₂|0⟩ = -Gᵇᵃ`: the two letter orderings differ by the Clifford sign. -/
theorem sfWgen_eq_neg_abeGen (a b : Fin 2) :
    sfWgen a b = -((abeGen b a : evenOdd QSF (0 : ZMod 2)) : FockSF) := by
  rw [sfWgen, abeGen_coe, stWordSF_swap_two ((0 : ℕ), a) ((1 : ℕ), b)]

/-- **`E = -W⁻`**. -/
theorem abeE_eq_neg_Wminus : abeE = -Wminus := by
  apply Subtype.ext
  rw [abeE_coe]
  change _ = -WminusSF
  rw [WminusSF, sfWgen_eq_neg_abeGen, neg_neg, abeGen_coe]

/-- **`F = -W⁺`**. -/
theorem abeF_eq_neg_Wplus : abeF = -Wplus := by
  apply Subtype.ext
  rw [abeF_coe]
  change _ = -WplusSF
  rw [WplusSF, sfWgen_eq_neg_abeGen, neg_neg, abeGen_coe]

/-- **`H = -½W⁰`**. -/
theorem abeH_eq_neg_half_Wzero : abeH = (-2⁻¹ : ℂ) • Wzero := by
  apply Subtype.ext
  rw [abeH_coe]
  change _ = (-2⁻¹ : ℂ) • WzeroSF
  rw [WzeroSF, sfWgen_eq_neg_abeGen, sfWgen_eq_neg_abeGen, abeGen_coe, abeGen_coe]
  module

/-! ## §6  The generating set, and the two shapes the repo's entry points consume

Nothing in this section is proved *about* `W(2)` beyond §5; it fixes the **targets**.  The three
`Prop`s below are the statements the two in-repo entry points consume, spelled for `W(2)`, so
that the right one can be targeted.  See the module docstring for which is true. -/

/-- Abe's generating **set** `{ω, E, H, F}` (Cor. 3.8). -/
noncomputable def abeGens : Set (evenOdd QSF (0 : ZMod 2)) := {abeOmega, abeE, abeH, abeF}

/-- The same, as a family indexed by `Fin 4` — the shape the nilpotency engine consumes
(`c2Cofinite_of_iterProdSpan_of_isNilpotent` wants `Set.range g` for a finite `ι`). -/
noncomputable def abeGenFam : Fin 4 → evenOdd QSF (0 : ZMod 2) := ![abeOmega, abeE, abeH, abeF]

theorem range_abeGenFam : Set.range abeGenFam = abeGens := by
  ext x
  simp only [abeGenFam, abeGens, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem abeGens_finite : abeGens.Finite := by
  unfold abeGens
  exact Set.toFinite _

/-- **The generators are homogeneous** — the hypothesis `hShom` of `iterProdSpan_eq_top`,
discharged: `ω` at weight `2`, `E, H, F` at weight `3`. -/
theorem abeGens_homog : ∀ s ∈ abeGens, IsHomog tripletW2 s := by
  intro s hs
  simp only [abeGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨2, abeOmega_mem_grading_two⟩
  · exact ⟨3, abeE_mem_grading_three⟩
  · exact ⟨3, abeH_mem_grading_three⟩
  · exact ⟨3, abeF_mem_grading_three⟩

/-- `ω⋅x = ω₍₋₁₎x`, the product of the Poisson algebra `A₂(W(2))` on representatives. -/
noncomputable def abeMulOmega (x : evenOdd QSF (0 : ZMod 2)) : evenOdd QSF (0 : ZMod 2) :=
  tripletW2.smul abeOmega (-1) x

/-- `ωⁿ` on representatives: `ω⁰ = |0⟩`, `ω^{n+1} = ω₍₋₁₎ωⁿ`. -/
noncomputable def abeOmegaPow : ℕ → evenOdd QSF (0 : ZMod 2)
  | 0 => tripletW2.vacuum
  | (n + 1) => abeMulOmega (abeOmegaPow n)

/-- **Abe's eleven-element spanning set** (Prop. 3.11):
`{𝟙, ω, ω², ω³, ω⁴, E, ωE, H, ωH, F, ωF}`.  Abe's `dim T⁺/C₂(T⁺) ≤ 11` is exactly the assertion
that its span covers `W(2)` modulo `O₂`. -/
noncomputable def abeSpanEleven : Set (evenOdd QSF (0 : ZMod 2)) :=
  {abeOmegaPow 0, abeOmegaPow 1, abeOmegaPow 2, abeOmegaPow 3, abeOmegaPow 4,
    abeE, abeMulOmega abeE, abeH, abeMulOmega abeH, abeF, abeMulOmega abeF}

theorem abeSpanEleven_finite : abeSpanEleven.Finite := by
  unfold abeSpanEleven
  exact Set.toFinite _

/-- **(H1) Strong generation, Abe Prop. 3.7 / Cor. 3.8** — the shape the *nilpotency* route
consumes (`adjoin_mk₂_image_eq_top`, `c2Cofinite_of_iterProdSpan_of_isNilpotent`).  Not proved
here. -/
def StrongGenAbe : Prop := iterProdSpan tripletW2 abeGens = ⊤

/-- **The shape `iterProdSpan_eq_top` consumes**, for the four generators.

⚠ **Expected to be false**, and not formalised here in either direction: it would force
`dim A₂(W(2)) ≤ 4`, against the count `dim A₂(W(2)) ≥ 9` recorded (not re-proved here) in
`Examples.TripletW2C2Direct`.  Named only so that `strongGenAbe_of_spanModO₂` puts the
implication on record and nobody tries to obtain `StrongGenAbe` this way. -/
def SpanModO₂Abe : Prop :=
  (⊤ : Submodule ℂ (evenOdd QSF (0 : ZMod 2))) = Submodule.span ℂ abeGens ⊔ O₂ tripletW2

/-- **(H1′) Abe Prop. 3.11**, in the shape `c2Cofinite_of_span_sup_O₂` consumes: the eleven
classes span `A₂(W(2))` as a **vector space**.  This is the true statement, and the shorter
target of the two.  Not proved here. -/
def AbeSpanningEleven : Prop :=
  (⊤ : Submodule ℂ (evenOdd QSF (0 : ZMod 2))) = Submodule.span ℂ abeSpanEleven ⊔ O₂ tripletW2

/-- The bridge `iterProdSpan_eq_top` provides — with `abeGens_homog` discharged here.  Its
hypothesis is `SpanModO₂Abe`, which is expected to be false for these four generators; that is
precisely why the strong-generation route cannot be short-circuited through them. -/
theorem strongGenAbe_of_spanModO₂ (h : SpanModO₂Abe) : StrongGenAbe :=
  iterProdSpan_eq_top tripletW2 abeGens abeGens_homog h

/-- **`C₂`-cofiniteness of `W(2)` from Abe Prop. 3.11 alone** — no strong generation, no
nilpotency, no `A₂`-algebra structure.  `A₂(W(2))` is a linear image of the finite-dimensional
`span ℂ abeSpanEleven`.

(The same six-line argument is `Examples.TripletW2Nilpotent.c2Cofinite_of_span_sup_O₂`; it is
repeated here so that this file does not import a module under concurrent development.) -/
theorem c2Cofinite_of_abeSpanningEleven (h : AbeSpanningEleven) : C2Cofinite tripletW2 := by
  haveI : FiniteDimensional ℂ (Submodule.span ℂ abeSpanEleven) :=
    FiniteDimensional.span_of_finite ℂ abeSpanEleven_finite
  refine Module.Finite.of_surjective
    ((mk₂ tripletW2).comp (Submodule.span ℂ abeSpanEleven).subtype) ?_
  intro p
  obtain ⟨x, rfl⟩ := mk₂_surjective tripletW2 p
  have hx : x ∈ Submodule.span ℂ abeSpanEleven ⊔ O₂ tripletW2 := by rw [← h]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨⟨y, hy⟩, ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_add,
    (mk₂_eq_zero_iff tripletW2).2 hz, add_zero]

end VOA.AbeGens
