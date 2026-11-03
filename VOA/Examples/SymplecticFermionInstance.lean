/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionY
import VOA.Examples.SymplecticFermionGrading
import VOA.Core.SuperVertexAlgebra

/-!
# The symplectic-fermion **super vertex algebra**

`sympFermSVA : SuperVertexAlgebra FockSF` — the first `SuperVertexAlgebra` in the library, and
therefore the first thing that actually exercises the parity axis rather than merely declaring it.

## What was already available, and what had to be proved here

Four of the twelve fields were handed over ready-made:

| field | source |
| --- | --- |
| `grading`, `isInternal`, `finrank` | `Examples.SymplecticFermionGrading` |
| `Y`, `vacuum_Y`, `creation`, `locality`, `regularity` | `Examples.SymplecticFermionY` |

The two **compatibility axioms** `grading_mode` (VA1) and `parity_mode` (VA1′) were not, and they
are the mathematical content of this file.  They say that the modes `u₍ₙ₎` respect the two
gradings:

* `grading_mode`: `u ∈ 𝒱_h`, `v ∈ 𝒱_k` ⟹ `u₍ₙ₎v ∈ 𝒱_{h+k-n-1}`;
* `parity_mode`:  `u ∈ 𝒱_p̄`, `v ∈ 𝒱_q̄` ⟹ `u₍ₙ₎v ∈ 𝒱_{p+q}`.

Neither is formal.  `reconstructε` produces `Y` as an abstract linear extension of the word fields
and says *nothing* about how its coefficients move the gradings; that information has to be traced
back through the construction, coefficient by coefficient.

## The route: graded fields

Both axioms are proved by the same three-step pattern, which is the one
`Examples/HeisenbergNVertex` uses on the bosonic side.

1. **The basic Clifford operators are graded.**  `creBase p` (exterior multiplication by the
   generator at `p`) raises the conformal weight by `p.1 + 1` and flips the parity; `annBase p`
   (contraction at `p`) *lowers* the weight by `p.1 + 1` and also flips the parity.  Creation is
   immediate.  Contraction is not: it is an odd derivation, so on a word it produces a
   Leibniz-type alternating sum, and the statement is proved by induction on the word
   (`annBase_stWordSF_cons`).  No Clifford-algebra induction occurs anywhere in this file.

2. **From words to submodules.**  Step 1 gives the statements on `stWordSF l` only.  For the
   weight grading that is enough by construction, since `gradingSF h` *is* the span of the
   weight-`h` words.  For the parity grading it is not: `evenOdd QSF r` is Mathlib's Clifford
   `ℤ/2`-grading, defined by generators-and-products, with no reference to our words.  So we first
   prove `evenOdd QSF r = span (stWordSF '' {l | |l| ≡ r})` — the two families are each contained
   in the other's total, and the lattice lemma
   `eq_of_le_of_iSupIndep_of_iSup_eq_top` upgrades "contained and spanning" to "equal".

3. **Propagation through the construction of `Y`.**  `WtField f D` ("the `zʲ`-coefficient of `f`
   raises the weight by `D + j`") and `ParField f s` ("every coefficient shifts the parity by `s`")
   are stable under scalars and — the one real computation — under the super normal-ordered
   product `nprodε`, where the two weights (resp. parities) simply add.  Since `YwordSF` is built
   by iterating `nprodε` over a word, induction gives `WtField (YwordSF l) (sfWeight l)` and
   `ParField (YwordSF l) |l|`.  Finally `YSF` is *linear*, and being a graded field is a linear
   condition on the state, so `{u | WtField (YSF u) D}` is a submodule; it contains all the
   weight-`D` words, hence all of `gradingSF D`.

## Why the parity is genuinely independent data

`chi` has conformal weight `1` and is odd, so `χᵃ_{-k-1}|0⟩` has weight `k+1` — an *integer* in
both parities.  Spin-statistics therefore fails here: `SpinStatistics sympFermSVA` does not hold,
which is exactly why `SuperVertexAlgebra` keeps `grading` and `parity` as two unlinked fields.
(The refutation itself is not formalized below — nothing needs it — but note that no field of this
file ever relates the two gradings, which is what makes the instance go through.)
-/

namespace VOA.SympFerm

open VOA
open CliffordAlgebra
open Module (End)

/-! ## §1  The parity grading as a `SuperVertexAlgebra` datum

`CliffordAlgebra.evenOdd` is already an internal direct sum — Mathlib's `GradedAlgebra` instance
supplies the `DirectSum.Decomposition`.  The work in this section is the *identification* of the
Clifford grading with the span of the length-graded words, which is what lets every later
statement about `evenOdd` be checked on words. -/

/-- **The parity decomposition of the Fock space.**  Immediate from Mathlib's
`CliffordAlgebra.gradedAlgebra` instance: a `GradedAlgebra` is in particular a
`DirectSum.Decomposition`, and a decomposition is an internal direct sum. -/
theorem evenOdd_isInternal : DirectSum.IsInternal (evenOdd QSF) :=
  DirectSum.Decomposition.isInternal (evenOdd QSF)

/-- The even and odd parts are independent — the half of `evenOdd_isInternal` used below. -/
theorem evenOdd_iSupIndep : iSupIndep (evenOdd QSF) := by
  classical
  exact ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
    (evenOdd QSF)).mp evenOdd_isInternal).1

/-- The words of parity `r`, i.e. of length `≡ r (mod 2)`. -/
def sfWordsOfParity (r : ZMod 2) : Set SFWord := {l : SFWord | ((l.length : ℕ) : ZMod 2) = r}

/-- The span of the parity-`r` words.  A priori only *contained* in `evenOdd QSF r`; the next
theorem shows the containment is an equality. -/
noncomputable def parityPieceSF (r : ZMod 2) : Submodule ℂ FockSF :=
  Submodule.span ℂ (stWordSF '' sfWordsOfParity r)

theorem parityPieceSF_le_evenOdd (r : ZMod 2) : parityPieceSF r ≤ evenOdd QSF r := by
  rw [parityPieceSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((l.length : ℕ) : ZMod 2) = r := hl
  rw [SetLike.mem_coe, ← hl']
  exact stWordSF_mem_evenOdd l

theorem parityPieceSF_iSup_eq_top : ⨆ r : ZMod 2, parityPieceSF r = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← stWordSF_span, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact le_iSup parityPieceSF ((l.length : ℕ) : ZMod 2)
    (Submodule.subset_span ⟨l, rfl, rfl⟩)

/-- **The Clifford parity grading is the length grading of the words.**

This is the bridge the whole parity half of the file rests on.  `evenOdd QSF r` is defined in
Mathlib by generators and products and knows nothing about `stWordSF`; without this identification
every parity statement would have to be re-proved by Clifford induction.  The proof is the
lattice lemma `eq_of_le_of_iSupIndep_of_iSup_eq_top`: the word spans sit inside the `evenOdd` pieces, the word spans already exhaust the
whole algebra, and the `evenOdd` pieces are independent — so no room is left over. -/
theorem evenOdd_eq_parityPieceSF (r : ZMod 2) : evenOdd QSF r = parityPieceSF r :=
  (eq_of_le_of_iSupIndep_of_iSup_eq_top parityPieceSF_le_evenOdd evenOdd_iSupIndep
    parityPieceSF_iSup_eq_top r).symm

/-- The vacuum is even: it is the algebra unit, which is graded of degree `0`. -/
theorem vacSF_mem_evenOdd : vacSF ∈ evenOdd QSF 0 :=
  SetLike.one_mem_graded (evenOdd QSF)

/-- `x + 1 + 1 = x` in `ZMod 2` — applying two odd operators returns to the original parity. -/
theorem zmod_two_add_one_add_one (x : ZMod 2) : x + 1 + 1 = x := by
  rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]

/-! ## §2  The basic Clifford operators are graded

`creBase p` multiplies by the generator at `p`, `annBase p` contracts against it.  Creation is
trivial in both gradings; annihilation needs an induction on words, because contraction is an odd
derivation and so does not act on a product one factor at a time. -/

theorem creBase_stWordSF (p : ℕ × Fin 2) (l : SFWord) :
    creBase p (stWordSF l) = stWordSF (p :: l) := by
  rw [creBase, LinearMap.mulLeft_apply, stWordSF_cons]

/-- Creation raises the conformal weight by the weight `p.1 + 1` of the generator it adds.
Checked on the spanning words, where it is the statement that prefixing a letter adds that
letter's weight. -/
theorem creBase_mapsTo_gradingSF (p : ℕ × Fin 2) (w : ℂ) :
    gradingSF w ≤ (gradingSF (w + ((p.1 : ℂ) + 1))).comap (creBase p) := by
  rw [gradingSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((sfWeight l : ℕ) : ℂ) = w := hl
  subst hl'
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [creBase_stWordSF,
    show ((sfWeight l : ℕ) : ℂ) + ((p.1 : ℂ) + 1) = ((sfWeight (p :: l) : ℕ) : ℂ) from by
      rw [sfWeight_cons]; push_cast; ring]
  exact stWordSF_mem_gradingSF (p :: l)

theorem creBase_mem_gradingSF (p : ℕ × Fin 2) {w : ℂ} {x : FockSF} (hx : x ∈ gradingSF w) :
    creBase p x ∈ gradingSF (w + ((p.1 : ℂ) + 1)) :=
  creBase_mapsTo_gradingSF p w hx

/-- Creation is odd: multiplying by a generator flips the parity. -/
theorem creBase_mem_evenOdd (p : ℕ × Fin 2) {r : ZMod 2} {x : FockSF} (hx : x ∈ evenOdd QSF r) :
    creBase p x ∈ evenOdd QSF (r + 1) := by
  rw [creBase, LinearMap.mulLeft_apply, add_comm]
  exact SetLike.mul_mem_graded (ι_mem_evenOdd_one QSF _) hx

/-- The coordinate functional at `p` evaluated on the generator at `q`. -/
theorem lapply_single_eq (p q : ℕ × Fin 2) :
    (Finsupp.lapply p : SFModes →ₗ[ℂ] ℂ) (Finsupp.single q (1 : ℂ))
      = (if p = q then (1 : ℂ) else 0) := by
  simp [Finsupp.lapply_apply, Finsupp.single_apply, eq_comm]

/-- **Contraction peels one letter off a word.**  The Leibniz rule for the odd derivation
`annBase p`: either it hits the head letter (producing the Kronecker `δ` and the tail) or it slips
past it, picking up the sign that makes contraction odd.  This single recursion is what makes both
grading statements for `annBase` inductions on words rather than Clifford inductions. -/
theorem annBase_stWordSF_cons (p q : ℕ × Fin 2) (rest : SFWord) :
    annBase p (stWordSF (q :: rest))
      = (if p = q then (1 : ℂ) else 0) • stWordSF rest
        - ι QSF (Finsupp.single q (1 : ℂ)) * annBase p (stWordSF rest) := by
  rw [stWordSF_cons, annBase, contractLeft_ι_mul, lapply_single_eq]

theorem annBase_stWordSF_nil (p : ℕ × Fin 2) : annBase p (stWordSF []) = 0 := by
  rw [stWordSF_nil, annBase, contractLeft_one]

/-- **Contraction lowers the conformal weight by the weight of the mode it removes.**  Induction
on the word: the head term drops exactly the letter `p` (whose weight is `p.1 + 1`), and the tail
term reinstates the head letter's weight on top of the inductive hypothesis. -/
theorem annBase_stWordSF_mem_gradingSF (p : ℕ × Fin 2) (l : SFWord) :
    annBase p (stWordSF l) ∈ gradingSF (((sfWeight l : ℕ) : ℂ) - ((p.1 : ℂ) + 1)) := by
  induction l with
  | nil => rw [annBase_stWordSF_nil]; exact Submodule.zero_mem _
  | cons q rest ih =>
      rw [annBase_stWordSF_cons]
      refine Submodule.sub_mem _ ?_ ?_
      · by_cases h : p = q
        · subst h
          rw [if_pos rfl, one_smul,
            show ((sfWeight (p :: rest) : ℕ) : ℂ) - ((p.1 : ℂ) + 1)
                = ((sfWeight rest : ℕ) : ℂ) from by rw [sfWeight_cons]; push_cast; ring]
          exact stWordSF_mem_gradingSF rest
        · rw [if_neg h, zero_smul]
          exact Submodule.zero_mem _
      · rw [show ι QSF (Finsupp.single q (1 : ℂ)) * annBase p (stWordSF rest)
              = creBase q (annBase p (stWordSF rest)) from by rw [creBase, LinearMap.mulLeft_apply],
          show ((sfWeight (q :: rest) : ℕ) : ℂ) - ((p.1 : ℂ) + 1)
              = (((sfWeight rest : ℕ) : ℂ) - ((p.1 : ℂ) + 1)) + ((q.1 : ℂ) + 1) from by
            rw [sfWeight_cons]; push_cast; ring]
        exact creBase_mem_gradingSF q ih

/-- **Contraction is odd.**  Same induction: the head term drops a letter, the tail term adds one
back on top of an already-flipped parity, and `1 + 1 = 0` in `ZMod 2` closes both. -/
theorem annBase_stWordSF_mem_evenOdd (p : ℕ × Fin 2) (l : SFWord) :
    annBase p (stWordSF l) ∈ evenOdd QSF (((l.length : ℕ) : ZMod 2) + 1) := by
  induction l with
  | nil => rw [annBase_stWordSF_nil]; exact Submodule.zero_mem _
  | cons q rest ih =>
      have hlen : (((q :: rest).length : ℕ) : ZMod 2) + 1 = ((rest.length : ℕ) : ZMod 2) := by
        rw [List.length_cons, Nat.cast_add, Nat.cast_one, zmod_two_add_one_add_one]
      rw [annBase_stWordSF_cons, hlen]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (stWordSF_mem_evenOdd rest)) ?_
      rw [show ι QSF (Finsupp.single q (1 : ℂ)) * annBase p (stWordSF rest)
            = creBase q (annBase p (stWordSF rest)) from by rw [creBase, LinearMap.mulLeft_apply],
        ← zmod_two_add_one_add_one ((rest.length : ℕ) : ZMod 2)]
      exact creBase_mem_evenOdd q ih

theorem annBase_mapsTo_gradingSF (p : ℕ × Fin 2) (w : ℂ) :
    gradingSF w ≤ (gradingSF (w - ((p.1 : ℂ) + 1))).comap (annBase p) := by
  rw [gradingSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((sfWeight l : ℕ) : ℂ) = w := hl
  subst hl'
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  exact annBase_stWordSF_mem_gradingSF p l

theorem annBase_mem_gradingSF (p : ℕ × Fin 2) {w : ℂ} {x : FockSF} (hx : x ∈ gradingSF w) :
    annBase p x ∈ gradingSF (w - ((p.1 : ℂ) + 1)) :=
  annBase_mapsTo_gradingSF p w hx

theorem annBase_mapsTo_evenOdd (p : ℕ × Fin 2) (r : ZMod 2) :
    evenOdd QSF r ≤ (evenOdd QSF (r + 1)).comap (annBase p) := by
  rw [evenOdd_eq_parityPieceSF, parityPieceSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((l.length : ℕ) : ZMod 2) = r := hl
  subst hl'
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  exact annBase_stWordSF_mem_evenOdd p l

theorem annBase_mem_evenOdd (p : ℕ × Fin 2) {r : ZMod 2} {x : FockSF} (hx : x ∈ evenOdd QSF r) :
    annBase p x ∈ evenOdd QSF (r + 1) :=
  annBase_mapsTo_evenOdd p r hx

/-! ## §3  The generator field `χ` is graded

`chi a j` is creation for `j ≥ 0` and (a multiple of) contraction for `j < 0`, so §2 covers both
halves.  The uniform statement is that `chi a j` shifts the weight by `1 + j`: `χ` has conformal
weight `1`, and the `zʲ`-coefficient of a weight-`d` field shifts the weight by `d + j`.

The mode `j = -1` needs its own line: there `annSF` carries the scalar `0` (the symplectic pairing
has a factor of the mode number), so `chi a (-1) = 0` and the weight bookkeeping — which would
otherwise be off by one, since `Int.toNat` truncates — is vacuous. -/

/-- **`χᵃ(z)` is a graded field of conformal weight `1`.** -/
theorem chi_mem_gradingSF (a : Fin 2) (j : ℤ) {w : ℂ} {x : FockSF} (hx : x ∈ gradingSF w) :
    chi a j x ∈ gradingSF (1 + w + (j : ℂ)) := by
  by_cases hj : 0 ≤ j
  · have hcast : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hj]
    have hchi : chi a j x = creBase (j.toNat, a) x := by rw [chi, if_pos hj]; rfl
    rw [hchi, show (1 : ℂ) + w + (j : ℂ) = w + ((((j.toNat, a) : ℕ × Fin 2).1 : ℂ) + 1) from by
      change (1 : ℂ) + w + (j : ℂ) = w + (((j.toNat : ℕ) : ℂ) + 1)
      rw [hcast]; ring]
    exact creBase_mem_gradingSF (j.toNat, a) hx
  · rw [not_le] at hj
    by_cases hj1 : j = -1
    · have hz : chi a j x = 0 := by
        rw [chi, if_neg (by omega : ¬ (0 ≤ j)), annSF, LinearMap.smul_apply]
        change ((((-j - 1).toNat : ℂ) * sfSign a) • annBase ((-j - 1).toNat - 1, a + 1) x) = 0
        rw [show ((-j - 1).toNat : ℕ) = 0 from by omega]
        norm_num
      rw [hz]
      exact Submodule.zero_mem _
    · have hle : j ≤ -2 := by omega
      have hchi : chi a j x
          = ((((-j - 1).toNat : ℂ) * sfSign a) • annBase ((-j - 1).toNat - 1, a + 1) x) := by
        rw [chi, if_neg (by omega : ¬ (0 ≤ j)), annSF, LinearMap.smul_apply]
      have hcast : (((((-j - 1).toNat - 1 : ℕ) : ℕ) : ℂ) + 1) = -(j : ℂ) - 1 := by
        have hz : (((-j - 1).toNat - 1 : ℕ) : ℤ) = -j - 2 := by omega
        rw [← Int.cast_natCast, hz]
        push_cast; ring
      rw [hchi]
      refine Submodule.smul_mem _ _ ?_
      rw [show (1 : ℂ) + w + (j : ℂ)
          = w - (((((-j - 1).toNat - 1, a + 1) : ℕ × Fin 2).1 : ℂ) + 1) from by
        change (1 : ℂ) + w + (j : ℂ) = w - ((((-j - 1).toNat - 1 : ℕ) : ℂ) + 1)
        rw [hcast]; ring]
      exact annBase_mem_gradingSF _ hx

/-- **`χᵃ(z)` is odd**: every coefficient flips the parity, creation and annihilation alike. -/
theorem chi_mem_evenOdd (a : Fin 2) (j : ℤ) {r : ZMod 2} {x : FockSF} (hx : x ∈ evenOdd QSF r) :
    chi a j x ∈ evenOdd QSF (1 + r) := by
  by_cases hj : 0 ≤ j
  · have hchi : chi a j x = creBase (j.toNat, a) x := by rw [chi, if_pos hj]; rfl
    rw [hchi, add_comm]
    exact creBase_mem_evenOdd (j.toNat, a) hx
  · have hchi : chi a j x
        = ((((-j - 1).toNat : ℂ) * sfSign a) • annBase ((-j - 1).toNat - 1, a + 1) x) := by
      rw [chi, if_neg hj, annSF, LinearMap.smul_apply]
    rw [hchi, add_comm]
    exact Submodule.smul_mem _ _ (annBase_mem_evenOdd _ hx)

/-! ## §4  Graded fields, and their stability under the super normal product

`WtField f D` and `ParField f s` are the field-level forms of VA1 and VA1′.  The point of the
section is that both are preserved by everything used to build `YwordSF`: scalars, `∂_z`, and the
super normal-ordered product `nprodε`, under which the weights (resp. parities) add. -/

/-- A **graded field of conformal weight `D`**: the `zʲ`-coefficient sends `𝒱_w` into
`𝒱_{D+w+j}`.  Setting `j = -n-1` turns this into VA1, `u₍ₙ₎ : 𝒱_w → 𝒱_{D+w-n-1}`. -/
def WtField (f : (End ℂ FockSF)⟦z^±⟧) (D : ℂ) : Prop :=
  ∀ (j : ℤ) (w : ℂ) (x : FockSF), x ∈ gradingSF w → f j x ∈ gradingSF (D + w + (j : ℂ))

/-- A **field of parity `s`**: every coefficient shifts the parity by `s`.  Unlike the weight, the
parity does not depend on the coefficient index — there is no `ℤ`-grading on the mode index. -/
def ParField (f : (End ℂ FockSF)⟦z^±⟧) (s : ZMod 2) : Prop :=
  ∀ (j : ℤ) (r : ZMod 2) (x : FockSF), x ∈ evenOdd QSF r → f j x ∈ evenOdd QSF (s + r)

theorem idField_WtField : WtField idField 0 := by
  intro j w x hx
  rw [idField_apply]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, LinearMap.id_apply,
      show (0 : ℂ) + w + (((0 : ℤ)) : ℂ) = w from by push_cast; ring]
    exact hx
  · rw [if_neg hj, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem idField_ParField : ParField idField 0 := by
  intro j r x hx
  rw [idField_apply]
  by_cases hj : j = 0
  · rw [if_pos hj, LinearMap.id_apply, zero_add]
    exact hx
  · rw [if_neg hj, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem WtField.smul (c : ℂ) {f : (End ℂ FockSF)⟦z^±⟧} {D : ℂ} (hf : WtField f D) :
    WtField (c • f) D := by
  intro j w x hx
  change c • (f j x) ∈ _
  exact Submodule.smul_mem _ _ (hf j w x hx)

theorem ParField.smul (c : ℂ) {f : (End ℂ FockSF)⟦z^±⟧} {s : ZMod 2} (hf : ParField f s) :
    ParField (c • f) s := by
  intro j r x hx
  change c • (f j x) ∈ _
  exact Submodule.smul_mem _ _ (hf j r x hx)

/-- A finite-support `finsum` of elements of a submodule lies in the submodule.  Needed because
`nprodε` is defined as a `finsum` over the mode index. -/
theorem finsum_mem_submodule {ι : Type*} (S : Submodule ℂ FockSF) (g : ι → FockSF)
    (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) : (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- **Weights add under the super normal product.**  Each summand of `:a(z)b(z):` is
`aₘ ∘ b_{s-m}` or (up to the Koszul scalar) `b_{s-m} ∘ aₘ`; either way the two shifts `Da + m`
and `Db + (s-m)` compose to `Da + Db + s`, the `m` cancelling.  That is the whole content. -/
theorem WtField.nprod (ε : ℂ) {a b : (End ℂ FockSF)⟦z^±⟧} (ha : IsField a) (hb : IsField b)
    {Da Db : ℂ} (hga : WtField a Da) (hgb : WtField b Db) :
    WtField (nprodε ε ha hb) (Da + Db) := by
  intro s w x hx
  rw [nprodε_apply]
  refine finsum_mem_submodule _ _ (normalOrderedε_diag_support_finite ε ha hb s x) (fun m => ?_)
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

/-- **Parities add under the super normal product** — the same bookkeeping with no index to
cancel. -/
theorem ParField.nprod (ε : ℂ) {a b : (End ℂ FockSF)⟦z^±⟧} (ha : IsField a) (hb : IsField b)
    {sa sb : ZMod 2} (hga : ParField a sa) (hgb : ParField b sb) :
    ParField (nprodε ε ha hb) (sa + sb) := by
  intro s r x hx
  rw [nprodε_apply]
  refine finsum_mem_submodule _ _ (normalOrderedε_diag_support_finite ε ha hb s x) (fun m => ?_)
  rw [normalOrderedε_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    change a m (b (s - m) x) ∈ _
    have hb' := hgb (s - m) r x hx
    have ha' := hga m (sb + r) _ hb'
    rwa [show sa + (sb + r) = sa + sb + r from by ring] at ha'
  · rw [if_neg h0, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    change b (s - m) (a m x) ∈ _
    have ha' := hga m r x hx
    have hb' := hgb (s - m) (sa + r) _ ha'
    rwa [show sb + (sa + r) = sa + sb + r from by ring] at hb'

/-- The scaled generator field `(k!)⁻¹ ∂^k χᵃ` has conformal weight `k + 1`: differentiating once
raises the weight by one, matching the weight `k+1` of the mode `χᵃ_{-k-1}` it creates. -/
theorem sfGenField_WtField (a : Fin 2) (k : ℕ) : WtField (sfGenField a k) ((k : ℂ) + 1) := by
  intro j w x hx
  change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (chi a)) j) x ∈ _
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range k, (j + 1 + (i : ℤ))), LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [show ((k : ℂ) + 1) + w + ((j : ℤ) : ℂ) = 1 + w + (((j + (k : ℤ)) : ℤ) : ℂ) from by
    push_cast; ring]
  exact chi_mem_gradingSF a (j + (k : ℤ)) hx

/-- Derivatives and scalars do not change parity, so the generator fields are odd. -/
theorem sfGenField_ParField (a : Fin 2) (k : ℕ) : ParField (sfGenField a k) 1 := by
  intro j r x hx
  change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (chi a)) j) x ∈ _
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range k, (j + 1 + (i : ℤ))), LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (chi_mem_evenOdd a (j + (k : ℤ)) hx)

/-- **The word field of `l` is a graded field of the weight of `l`** — the field-level VA1 for
the spanning family.  Induction on the word through `WtField.nprod`. -/
theorem YwordSF_WtField (l : SFWord) : WtField (YwordSF l) ((sfWeight l : ℕ) : ℂ) := by
  induction l with
  | nil =>
      rw [YwordSF_nil, sfWeight_nil, Nat.cast_zero]
      exact idField_WtField
  | cons p rest ih =>
      rw [YwordSF_cons,
        show ((sfWeight (p :: rest) : ℕ) : ℂ) = ((p.1 : ℂ) + 1) + ((sfWeight rest : ℕ) : ℂ) from by
          rw [sfWeight_cons]; push_cast; ring]
      exact WtField.nprod _ (sfGenField_isField p.2 p.1) (YwordSF_isField rest)
        (sfGenField_WtField p.2 p.1) ih

/-- **The word field of `l` has parity the length of `l`** — a product of `|l|` odd generator
fields. -/
theorem YwordSF_ParField (l : SFWord) : ParField (YwordSF l) ((l.length : ℕ) : ZMod 2) := by
  induction l with
  | nil =>
      rw [YwordSF_nil, List.length_nil, Nat.cast_zero]
      exact idField_ParField
  | cons p rest ih =>
      rw [YwordSF_cons,
        show (((p :: rest).length : ℕ) : ZMod 2) = 1 + ((rest.length : ℕ) : ZMod 2) from by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]]
      exact ParField.nprod _ (sfGenField_isField p.2 p.1) (YwordSF_isField rest)
        (sfGenField_ParField p.2 p.1) ih

/-! ## §5  Transporting the grading statements along `YSF`

`YSF` is only characterised on the words (`YSF_word`), plus linearity.  That is enough: "the
vertex operator of `u` is a graded field of weight `D`" is a *linear* condition on `u`, so the
states satisfying it form a submodule; it contains the weight-`D` words, hence their span, which
is `gradingSF D` by definition.  The same argument runs for the parity, using §1 to know that
`evenOdd QSF s` really is the span of the parity-`s` words. -/

/-- The states whose vertex operator is a graded field of weight `D`. -/
noncomputable def wtStatesSF (D : ℂ) : Submodule ℂ FockSF where
  carrier := {u : FockSF | WtField (YSF u) D}
  add_mem' := by
    intro u v hu hv j w x hx
    rw [map_add]
    change (YSF u) j x + (YSF v) j x ∈ _
    exact Submodule.add_mem _ (hu j w x hx) (hv j w x hx)
  zero_mem' := by
    intro j w x _
    rw [map_zero]
    change (0 : FockSF) ∈ _
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c u hu j w x hx
    rw [map_smul]
    change c • ((YSF u) j x) ∈ _
    exact Submodule.smul_mem _ _ (hu j w x hx)

/-- The states whose vertex operator has definite parity `s`. -/
noncomputable def parStatesSF (s : ZMod 2) : Submodule ℂ FockSF where
  carrier := {u : FockSF | ParField (YSF u) s}
  add_mem' := by
    intro u v hu hv j r x hx
    rw [map_add]
    change (YSF u) j x + (YSF v) j x ∈ _
    exact Submodule.add_mem _ (hu j r x hx) (hv j r x hx)
  zero_mem' := by
    intro j r x _
    rw [map_zero]
    change (0 : FockSF) ∈ _
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c u hu j r x hx
    rw [map_smul]
    change c • ((YSF u) j x) ∈ _
    exact Submodule.smul_mem _ _ (hu j r x hx)

theorem gradingSF_le_wtStatesSF (h : ℂ) : gradingSF h ≤ wtStatesSF h := by
  rw [gradingSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((sfWeight l : ℕ) : ℂ) = h := hl
  subst hl'
  have : WtField (YSF (stWordSF l)) ((sfWeight l : ℕ) : ℂ) := by
    rw [YSF_word]; exact YwordSF_WtField l
  exact this

theorem evenOdd_le_parStatesSF (s : ZMod 2) : evenOdd QSF s ≤ parStatesSF s := by
  rw [evenOdd_eq_parityPieceSF, parityPieceSF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ((l.length : ℕ) : ZMod 2) = s := hl
  subst hl'
  have : ParField (YSF (stWordSF l)) ((l.length : ℕ) : ZMod 2) := by
    rw [YSF_word]; exact YwordSF_ParField l
  exact this

/-- **VA1, field form**: the vertex operator of a weight-`h` state is a graded field of weight
`h`. -/
theorem YSF_WtField {h : ℂ} {u : FockSF} (hu : u ∈ gradingSF h) : WtField (YSF u) h :=
  gradingSF_le_wtStatesSF h hu

/-- **VA1′, field form**: the vertex operator of a parity-`p` state has parity `p`. -/
theorem YSF_ParField {p : ZMod 2} {u : FockSF} (hu : u ∈ evenOdd QSF p) : ParField (YSF u) p :=
  evenOdd_le_parStatesSF p hu

/-! ## §6  Assembly -/

/-- The unit of `FormalDist` is the identity field (VA2's right-hand side). -/
theorem idFieldSF_eq_one : (idField : (End ℂ FockSF)⟦z^±⟧) = 1 := by
  funext j
  rw [idField_apply, FormalDist.one_apply]
  rfl

/-- **The symplectic-fermion super vertex algebra.**

The first `SuperVertexAlgebra` instance in the library.  Weight grading and finiteness come from
`Examples.SymplecticFermionGrading`, the parity grading is Mathlib's Clifford `ℤ/2`-grading, the
vertex operator and its vacuum/locality properties come from `reconstructε` via
`Examples.SymplecticFermionY`, and the two compatibility axioms `grading_mode` / `parity_mode` are
§§2–5 above.

`locality` deserves a word: `YSF_localε` is phrased for states presented as parity-homogeneous
`Finsupp` combinations of words, which is the shape `reconstructε` produces.  To feed it a bare
`u ∈ evenOdd QSF p` we use §1 — `evenOdd QSF p` *is* the span of the parity-`p` words — and
`Finsupp.mem_span_image_iff_linearCombination` to extract such a presentation.

Note that `SpinStatistics sympFermSVA` does **not** hold: `χᵃ_{-k-1}|0⟩` is odd of integer weight
`k+1`.  Nothing here depends on the two gradings being related, by design. -/
noncomputable def sympFermSVA : SuperVertexAlgebra FockSF where
  grading := gradingSF
  isInternal := gradingSF_isInternal
  finrank := gradingSF_finrank
  parity := evenOdd QSF
  parity_isInternal := evenOdd_isInternal
  Y := YSF
  vacuum := vacSF
  vacuum_mem := vacSF_mem
  vacuum_parity := vacSF_mem_evenOdd
  grading_mode := by
    intro h k u hu v hv n
    have hmode := YSF_WtField hu (-n - 1) k v hv
    rwa [show h + k + (((-n - 1 : ℤ)) : ℂ) = h + k - (n : ℂ) - 1 from by push_cast; ring] at hmode
  parity_mode := by
    intro p q u hu v hv n
    exact YSF_ParField hu (-n - 1) q v hv
  vacuum_Y := by rw [YSF_vacuum, idFieldSF_eq_one]
  creation := by
    intro u
    refine ⟨?_, fun n hn => ?_⟩
    · have hidx : mode (YSF u) (-1) vacSF = (YSF u) 0 vacSF := by rw [mode_apply]; norm_num
      rw [hidx]
      exact YSF_creation u
    · rw [mode_apply]
      exact YSF_creation_neg u (by omega)
  locality := by
    intro p q u hu v hv
    rw [evenOdd_eq_parityPieceSF, parityPieceSF] at hu hv
    obtain ⟨c, hcs, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hu
    obtain ⟨d, hds, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hv
    have hc : ∀ i ∈ c.support, ((i.length : ℕ) : ZMod 2) = p := fun i hi =>
      (Finsupp.mem_supported ℂ c).mp hcs (Finset.mem_coe.mpr hi)
    have hd : ∀ j ∈ d.support, ((j.length : ℕ) : ZMod 2) = q := fun j hj =>
      (Finsupp.mem_supported ℂ d).mp hds (Finset.mem_coe.mpr hj)
    exact YSF_localε p q c d hc hd
  regularity := by
    intro u v
    obtain ⟨B, hB⟩ := YSF_isField u v
    refine ⟨-B, fun n hn => ?_⟩
    rw [mode_apply]
    exact hB (-n - 1) (by omega)

end VOA.SympFerm
