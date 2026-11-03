/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Codes.Defs
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Weight enumerators

Ebeling §2.7. The **Hamming weight enumerator** of a code `C` of length `n` is

`W_C(X, Y) = ∑_{c ∈ C} X ^ (n - wt c) * Y ^ (wt c)`,

a homogeneous polynomial of degree `n`. Following signpost **S6** it is an element of
`MvPolynomial (Fin 2) ℂ` rather than a two-variable `Polynomial`, so that Chapter 5's Lee
enumerators — which need `(p+1)/2` variables — are literally the same object.

## Main definitions

* `Code.toFinset` — the codewords of `C` as a `Finset`, so that sums over `C` are `Finset` sums.
* `Code.hammingEnumerator` — `W_C`, as an element of `MvPolynomial (Fin 2) ℂ`.
* `Code.weightCount` — the weight distribution `A_i = #{c ∈ C : wt c = i}`.
* `Code.leeWeightElt`, `Code.leeWeight`, `Code.leeEnumerator` — the Lee weight and its
  enumerator, for Chapter 5.

## How to prove identities about enumerators

Do **not** fight coefficients. Prove the evaluation form `∀ f : Fin 2 → ℂ, eval f p = eval f q`
first — `Code.hammingEnumerator_eval` turns the left side into an explicit sum over codewords —
and then upgrade with `MvPolynomial.funext`, which is valid because `ℂ` is an infinite integral
domain. `Code.hammingEnumerator_ext` packages that step.

## References

Ebeling, *Lattices and Codes*, 3rd ed., §2.7.
-/

open Finset
open MvPolynomial (X eval bind₁)

namespace Code

variable {q n : ℕ}

/-! ### Codewords as a `Finset` -/

section Finite

variable [NeZero q]

/-- The codewords of `C`, as a `Finset`. `ZMod q` is finite once `q ≠ 0`, so a code is a finite
set; this is the object all the enumerator sums run over. -/
noncomputable def toFinset (C : Code q n) : Finset (Fin n → ZMod q) :=
  (Set.toFinite (C : Set (Fin n → ZMod q))).toFinset

@[simp] theorem mem_toFinset {C : Code q n} {c : Fin n → ZMod q} :
    c ∈ C.toFinset ↔ c ∈ C := Set.Finite.mem_toFinset _

@[simp] theorem coe_toFinset (C : Code q n) :
    (C.toFinset : Set (Fin n → ZMod q)) = (C : Set (Fin n → ZMod q)) :=
  Set.Finite.coe_toFinset _

theorem zero_mem_toFinset (C : Code q n) : (0 : Fin n → ZMod q) ∈ C.toFinset :=
  mem_toFinset.mpr C.zero_mem

theorem toFinset_nonempty (C : Code q n) : C.toFinset.Nonempty :=
  ⟨0, C.zero_mem_toFinset⟩

/-- The number of codewords. -/
theorem card_toFinset_pos (C : Code q n) : 0 < C.toFinset.card :=
  Finset.card_pos.mpr C.toFinset_nonempty

@[simp] theorem toFinset_bot : (⊥ : Code q n).toFinset = {0} := by
  ext c
  simp [mem_toFinset, Submodule.mem_bot]

@[simp] theorem toFinset_top : (⊤ : Code q n).toFinset = Finset.univ := by
  ext c
  simp [mem_toFinset]

/-- Over a prime field a code has `q ^ k` words, where `k` is its dimension. -/
theorem card_toFinset [Fact (Nat.Prime q)] (C : Code q n) : C.toFinset.card = q ^ C.rank := by
  have h1 : C.toFinset.card = Nat.card C := by
    have h2 := Set.ncard_eq_toFinset_card (C : Set (Fin n → ZMod q)) (Set.toFinite _)
    have h3 := Nat.card_coe_set_eq (C : Set (Fin n → ZMod q))
    show (Set.toFinite (C : Set (Fin n → ZMod q))).toFinset.card = Nat.card C
    rw [← h2, ← h3]
    rfl
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  rfl

/-! ### The Hamming weight enumerator -/

/-- The **Hamming weight enumerator** `W_C(X, Y) = ∑_{c ∈ C} X^(n - wt c) Y^(wt c)`.
Ebeling §2.7. Variable `0` is `X`, variable `1` is `Y`. -/
noncomputable def hammingEnumerator (C : Code q n) : MvPolynomial (Fin 2) ℂ :=
  ∑ c ∈ C.toFinset, X 0 ^ (n - weight c) * X 1 ^ weight c

@[simp] theorem hammingEnumerator_eval (C : Code q n) (f : Fin 2 → ℂ) :
    eval f C.hammingEnumerator = ∑ c ∈ C.toFinset, f 0 ^ (n - weight c) * f 1 ^ weight c := by
  simp [hammingEnumerator]

/-- The evaluation-first recipe: to prove two polynomials built from enumerators equal, it is
enough to check every complex evaluation. -/
theorem hammingEnumerator_ext {p r : MvPolynomial (Fin 2) ℂ}
    (h : ∀ f : Fin 2 → ℂ, eval f p = eval f r) : p = r :=
  MvPolynomial.funext h

@[simp] theorem hammingEnumerator_bot :
    (⊥ : Code q n).hammingEnumerator = X 0 ^ n := by
  simp [hammingEnumerator]

/-- Evaluating at `X = Y = 1` counts the codewords. -/
theorem hammingEnumerator_eval_one (C : Code q n) :
    eval (fun _ => (1 : ℂ)) C.hammingEnumerator = (C.toFinset.card : ℂ) := by
  simp

/-! ### The weight distribution -/

/-- `weightCount C i` is Ebeling's `A_i`: the number of codewords of weight exactly `i`. -/
noncomputable def weightCount (C : Code q n) (i : ℕ) : ℕ :=
  (C.toFinset.filter fun c => weight c = i).card

theorem weightCount_zero (C : Code q n) : C.weightCount 0 = 1 := by
  rw [weightCount]
  have : (C.toFinset.filter fun c => weight c = 0) = {0} := by
    ext c
    simp only [Finset.mem_filter, mem_toFinset, Finset.mem_singleton, weight_eq_zero]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ C.zero_mem, h⟩⟩
  rw [this, Finset.card_singleton]

theorem sum_weightCount (C : Code q n) :
    ∑ i ∈ Finset.range (n + 1), C.weightCount i = C.toFinset.card :=
  (Finset.card_eq_sum_card_fiberwise
    (fun c _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (weight_le c)))).symm

/-- The enumerator, written through the weight distribution `A_i`. Ebeling §2.7. -/
theorem hammingEnumerator_eq_sum_weightCount (C : Code q n) :
    C.hammingEnumerator
      = ∑ i ∈ Finset.range (n + 1), C.weightCount i • (X (R := ℂ) 0 ^ (n - i) * X 1 ^ i) := by
  have hmap : ∀ c ∈ C.toFinset, weight c ∈ Finset.range (n + 1) :=
    fun c _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (weight_le c))
  rw [hammingEnumerator, ← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∀ c ∈ (C.toFinset.filter fun c => weight c = i),
      X (R := ℂ) (0 : Fin 2) ^ (n - weight c) * X 1 ^ weight c
        = X (0 : Fin 2) ^ (n - i) * X 1 ^ i :=
    fun c hc => by rw [(Finset.mem_filter.mp hc).2]
  calc ∑ c ∈ (C.toFinset.filter fun c => weight c = i),
          X (R := ℂ) (0 : Fin 2) ^ (n - weight c) * X 1 ^ weight c
      = ∑ _c ∈ (C.toFinset.filter fun c => weight c = i),
          X (R := ℂ) (0 : Fin 2) ^ (n - i) * X 1 ^ i := Finset.sum_congr rfl h1
    _ = C.weightCount i • (X (R := ℂ) (0 : Fin 2) ^ (n - i) * X 1 ^ i) := Finset.sum_const _

/-! ### The Lee weight and its enumerator (Chapter 5)

Ebeling §5.2 uses the Lee weight over `𝔽_p` with `p` odd. The enumerator is indexed by
`Fin (q / 2 + 1)`, which for odd `q` is exactly the `(p+1)/2` variables of the book — see
`Code.leeIndex_eq_of_odd`. Indexing by `q / 2 + 1` rather than `(q+1)/2` is what makes the bound
`leeWeightElt a < q / 2 + 1` true for *every* `q`, not just the odd ones. -/

/-- The **Lee weight** of a single letter: its distance to `0` around the cycle `ZMod q`. -/
def leeWeightElt (a : ZMod q) : ℕ := min a.val (q - a.val)

/-- The **Lee weight** of a word: the sum of the Lee weights of its letters. -/
def leeWeight (c : Fin n → ZMod q) : ℕ := ∑ i, leeWeightElt (c i)

theorem leeWeightElt_lt (a : ZMod q) : leeWeightElt a < q / 2 + 1 := by
  have hlt : a.val < q := ZMod.val_lt a
  rw [leeWeightElt]
  omega

/-- For odd `q` the index set `Fin (q / 2 + 1)` used here is the book's `(q+1)/2` variables. -/
theorem leeIndex_eq_of_odd (hq : Odd q) : q / 2 + 1 = (q + 1) / 2 := by
  obtain ⟨m, rfl⟩ := hq
  omega

omit [NeZero q] in
@[simp] theorem leeWeightElt_zero : leeWeightElt (0 : ZMod q) = 0 := by
  simp [leeWeightElt, ZMod.val_zero]

omit [NeZero q] in
@[simp] theorem leeWeight_zero : leeWeight (0 : Fin n → ZMod q) = 0 := by
  simp [leeWeight]

/-- The **Lee weight enumerator**: the monomial of a codeword records, for each `j`, how many of
its letters have Lee weight `j`. Ebeling §5.2. -/
noncomputable def leeEnumerator (C : Code q n) : MvPolynomial (Fin (q / 2 + 1)) ℂ :=
  ∑ c ∈ C.toFinset, ∏ i : Fin n, X ⟨leeWeightElt (c i), leeWeightElt_lt (c i)⟩

theorem leeEnumerator_eval (C : Code q n) (f : Fin (q / 2 + 1) → ℂ) :
    eval f C.leeEnumerator
      = ∑ c ∈ C.toFinset, ∏ i : Fin n, f ⟨leeWeightElt (c i), leeWeightElt_lt (c i)⟩ := by
  simp [leeEnumerator]

end Finite

end Code
