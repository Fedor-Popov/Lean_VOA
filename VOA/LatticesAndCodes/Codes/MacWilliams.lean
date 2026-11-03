/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Codes.Enumerator
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The MacWilliams identity

Ebeling, Theorem 2.7: the weight enumerator of the dual code is determined by that of the code,

`|C| · W_{Cᗮ}(X, Y) = W_C(X + (q−1)Y, X − Y)`.

Following signpost **S5** this is proved by **character orthogonality**, not by the book's
theta-function derivation. The proof uses no analysis: the only input from outside algebra is the
existence of a primitive `q`-th root of unity in `ℂ`, which supplies a primitive additive
character `ZMod q → ℂ`. Consequently the code pillar never waits on Poisson summation, and the
statement holds for every `q ≥ 1`, not only for prime `q`.

## Main results

* `Code.sum_charQ_dotProduct` — character orthogonality over a code: summing `χ⟪u,v⟫` over `u ∈ C`
  gives `|C|` when `v ∈ Cᗮ` and `0` otherwise.
* `Code.fourier_weight` — the Fourier transform of `X^(n−wt) Y^(wt)` is
  `(X+(q−1)Y)^(n−wt) (X−Y)^(wt)`.
* `Code.macWilliams_eval`, `Code.macWilliams` — **Theorem 2.7**, in evaluation and polynomial form.
* `Code.enumerator_invariant` — **Corollary 2.4**: the enumerator of a binary self-dual code is
  invariant, up to the factor `2^k`, under `(X, Y) ↦ (X+Y, X−Y)`.

## References

Ebeling, *Lattices and Codes*, 3rd ed., §2.7, Theorem 2.7 and Corollary 2.4.
-/

open Finset
open MvPolynomial (X eval bind₁)
open scoped Matrix

namespace Code

variable {q n : ℕ}

/-! ### A primitive additive character of `ZMod q` with values in `ℂ` -/

section Character

variable [NeZero q]

/-- A primitive `q`-th root of unity in `ℂ`. -/
noncomputable def zetaQ (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

theorem isPrimitiveRoot_zetaQ : IsPrimitiveRoot (zetaQ q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

/-- The primitive additive character `ZMod q → ℂ`, `a ↦ ζ^a`, that drives the character proof of
MacWilliams. -/
noncomputable def charQ (q : ℕ) [NeZero q] : AddChar (ZMod q) ℂ :=
  AddChar.zmodChar q (isPrimitiveRoot_zetaQ (q := q)).pow_eq_one

theorem charQ_isPrimitive : (charQ q).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root q isPrimitiveRoot_zetaQ

theorem charQ_eq_one_iff {a : ZMod q} : charQ q a = 1 ↔ a = 0 :=
  AddChar.IsPrimitive.zmod_char_eq_one_iff q charQ_isPrimitive a

/-- A character turns a finite sum into a finite product. -/
theorem charQ_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod q) :
    charQ q (∑ i ∈ s, f i) = ∏ i ∈ s, charQ q (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem charQ_dotProduct (u v : Fin n → ZMod q) :
    charQ q (u ⬝ᵥ v) = ∏ i, charQ q (u i * v i) := by
  rw [dotProduct, charQ_sum]

/-- The sum of a nontrivial multiplicative shift of `charQ` vanishes. -/
theorem sum_charQ_mul (b : ZMod q) :
    ∑ a : ZMod q, charQ q (a * b) = if b = 0 then (q : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift b charQ_isPrimitive, ZMod.card]
  split_ifs <;> simp

end Character

/-! ### Character orthogonality over a code -/

section Orthogonality

variable [NeZero q]

open scoped Classical in
/-- **Character orthogonality over a code.** This is the whole of the analytic input to
MacWilliams, and it is pure algebra. -/
theorem sum_charQ_dotProduct (C : Code q n) (v : Fin n → ZMod q) :
    ∑ u ∈ C.toFinset, charQ q (u ⬝ᵥ v)
      = if v ∈ C.dual then (C.toFinset.card : ℂ) else 0 := by
  classical
  split_ifs with hv
  · have hterm : ∀ u ∈ C.toFinset, charQ q (u ⬝ᵥ v) = 1 := by
      intro u hu
      rw [mem_dual.mp hv u (mem_toFinset.mp hu)]
      exact AddChar.map_zero_eq_one _
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  · obtain ⟨w, hw, hwv⟩ : ∃ w ∈ C, w ⬝ᵥ v ≠ 0 := by
      by_contra hcon
      refine hv (mem_dual.mpr fun u hu => ?_)
      by_contra huv
      exact hcon ⟨u, hu, huv⟩
    have himage : C.toFinset.image (fun u => w + u) = C.toFinset := by
      ext z
      simp only [Finset.mem_image, mem_toFinset]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact C.add_mem hw hu
      · intro hz
        exact ⟨z - w, C.sub_mem hz hw, by ring⟩
    have hkey : (∑ u ∈ C.toFinset, charQ q (u ⬝ᵥ v))
        = charQ q (w ⬝ᵥ v) * ∑ u ∈ C.toFinset, charQ q (u ⬝ᵥ v) := by
      conv_lhs => rw [← himage]
      rw [Finset.sum_image (fun a _ b _ h => by simpa using h), Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by
        rw [add_dotProduct, AddChar.map_add_eq_mul]
    have hne1 : charQ q (w ⬝ᵥ v) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hwv (charQ_eq_one_iff.mp h)
    have hzero : (charQ q (w ⬝ᵥ v) - 1) * (∑ u ∈ C.toFinset, charQ q (u ⬝ᵥ v)) = 0 := by
      rw [sub_mul, one_mul, ← hkey, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left hne1

end Orthogonality

/-! ### The Fourier transform of the weight monomial -/

section Fourier

variable [NeZero q]

omit [NeZero q] in
/-- `X^(n − wt v) Y^(wt v)` written as a product over coordinates. -/
theorem prod_ite_eq_pow_weight (A B : ℂ) (v : Fin n → ZMod q) :
    ∏ i, (if v i = 0 then A else B) = A ^ (n - weight v) * B ^ weight v := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter fun i => v i = 0) = (support v)ᶜ := by
    ext i; simp [mem_support]
  have h2 : (Finset.univ.filter fun i => ¬ v i = 0) = support v := by
    ext i; simp [mem_support]
  rw [h1, h2, Finset.card_compl, Fintype.card_fin, weight_eq_card_support]

/-- **The Fourier transform of the weight monomial.** Ebeling §2.7. -/
theorem fourier_weight (A B : ℂ) (u : Fin n → ZMod q) :
    ∑ v : Fin n → ZMod q, charQ q (u ⬝ᵥ v) * (A ^ (n - weight v) * B ^ weight v)
      = (A + ((q : ℂ) - 1) * B) ^ (n - weight u) * (A - B) ^ weight u := by
  classical
  have hlocal : ∀ b : ZMod q,
      ∑ a : ZMod q, charQ q (b * a) * (if a = 0 then A else B)
        = if b = 0 then A + ((q : ℂ) - 1) * B else A - B := by
    intro b
    have hterm : ∀ a : ZMod q, charQ q (b * a) * (if a = 0 then A else B)
        = charQ q (b * a) * B + (if a = 0 then A - B else 0) := by
      intro a
      by_cases ha : a = 0
      · subst ha
        rw [mul_zero, if_pos rfl, if_pos rfl, AddChar.map_zero_eq_one]
        ring
      · rw [if_neg ha, if_neg ha]
        ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => congrArg (charQ q) (mul_comm b a)]
    rw [sum_charQ_mul, Finset.sum_ite_eq' Finset.univ (0 : ZMod q) (fun _ => A - B)]
    simp only [Finset.mem_univ, if_true]
    split_ifs <;> ring
  calc ∑ v : Fin n → ZMod q, charQ q (u ⬝ᵥ v) * (A ^ (n - weight v) * B ^ weight v)
      = ∑ v : Fin n → ZMod q, ∏ i, (charQ q (u i * v i) * (if v i = 0 then A else B)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.prod_mul_distrib, ← charQ_dotProduct, prod_ite_eq_pow_weight]
    _ = ∏ i, ∑ a : ZMod q, charQ q (u i * a) * (if a = 0 then A else B) := by
        rw [Finset.prod_univ_sum]
        exact (Finset.sum_congr (by rw [Fintype.piFinset_univ]) fun v _ => rfl).symm
    _ = ∏ i, (if u i = 0 then A + ((q : ℂ) - 1) * B else A - B) :=
        Finset.prod_congr rfl fun i _ => hlocal (u i)
    _ = (A + ((q : ℂ) - 1) * B) ^ (n - weight u) * (A - B) ^ weight u :=
        prod_ite_eq_pow_weight _ _ u

end Fourier

/-! ### The MacWilliams identity -/

section MacWilliams

variable [NeZero q]

/-- **Ebeling, Theorem 2.7 (MacWilliams), evaluation form.** -/
theorem macWilliams_eval (C : Code q n) (A B : ℂ) :
    (C.toFinset.card : ℂ) * eval ![A, B] C.dual.hammingEnumerator
      = eval ![A + ((q : ℂ) - 1) * B, A - B] C.hammingEnumerator := by
  classical
  rw [hammingEnumerator_eval, hammingEnumerator_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  symm
  calc ∑ u ∈ C.toFinset, (A + ((q : ℂ) - 1) * B) ^ (n - weight u) * (A - B) ^ weight u
      = ∑ u ∈ C.toFinset, ∑ v : Fin n → ZMod q,
          charQ q (u ⬝ᵥ v) * (A ^ (n - weight v) * B ^ weight v) :=
        Finset.sum_congr rfl fun u _ => (fourier_weight A B u).symm
    _ = ∑ v : Fin n → ZMod q, ∑ u ∈ C.toFinset,
          charQ q (u ⬝ᵥ v) * (A ^ (n - weight v) * B ^ weight v) := Finset.sum_comm
    _ = ∑ v : Fin n → ZMod q,
          (if v ∈ C.dual then (C.toFinset.card : ℂ) else 0)
            * (A ^ (n - weight v) * B ^ weight v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.sum_mul, sum_charQ_dotProduct]
    _ = ∑ v : Fin n → ZMod q,
          (if v ∈ C.dual then (C.toFinset.card : ℂ) * (A ^ (n - weight v) * B ^ weight v)
            else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : v ∈ C.dual <;> simp [hv]
    _ = ∑ v ∈ C.dual.toFinset, (C.toFinset.card : ℂ) * (A ^ (n - weight v) * B ^ weight v) := by
        rw [← Finset.sum_filter]
        congr 1
        ext v
        simp [mem_toFinset]
    _ = (C.toFinset.card : ℂ) * ∑ v ∈ C.dual.toFinset, A ^ (n - weight v) * B ^ weight v :=
        (Finset.mul_sum _ _ _).symm

theorem eval_bind₂ (f : Fin 2 → ℂ) (g : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (p : MvPolynomial (Fin 2) ℂ) : eval f (bind₁ g p) = eval (fun i => eval f (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => simp [hp]

/-- **Ebeling, Theorem 2.7 (MacWilliams).** The weight enumerator of the dual code is obtained
from that of the code by the substitution `X ↦ X + (q−1)Y`, `Y ↦ X − Y`, divided by `|C|`. -/
theorem macWilliams (C : Code q n) :
    (C.toFinset.card : ℂ) • C.dual.hammingEnumerator
      = bind₁ ![X 0 + MvPolynomial.C ((q : ℂ) - 1) * X 1, X 0 - X 1] C.hammingEnumerator := by
  refine MvPolynomial.funext fun f => ?_
  rw [eval_bind₂, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hfun : (fun i => eval f ((![X 0 + MvPolynomial.C ((q : ℂ) - 1) * X 1, X 0 - X 1]) i))
      = ![f 0 + ((q : ℂ) - 1) * f 1, f 0 - f 1] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]
  have hf : ![f 0, f 1] = f := by
    funext i
    fin_cases i <;> rfl
  have h := macWilliams_eval C (f 0) (f 1)
  rw [hf] at h
  exact h

end MacWilliams

/-! ### Corollary 2.4 -/

/-- **Ebeling, Corollary 2.4.** The weight enumerator of a binary self-dual code is invariant, up
to the factor `2^k = |C|`, under the substitution `(X, Y) ↦ (X + Y, X − Y)`. -/
theorem enumerator_invariant {n : ℕ} (C : Code 2 n) (h : C.IsSelfDual) :
    bind₁ ![X 0 + X 1, X 0 - X 1] C.hammingEnumerator
      = ((2 ^ C.rank : ℕ) : ℂ) • C.hammingEnumerator := by
  have hsub : (![X 0 + MvPolynomial.C (((2 : ℕ) : ℂ) - 1) * X 1, X 0 - X 1]
      : Fin 2 → MvPolynomial (Fin 2) ℂ) = ![X 0 + X 1, X 0 - X 1] := by
    have hC1 : MvPolynomial.C (((2 : ℕ) : ℂ) - 1) = (1 : MvPolynomial (Fin 2) ℂ) := by
      rw [show (((2 : ℕ) : ℂ) - 1) = 1 by norm_num, map_one]
    rw [hC1, one_mul]
  have hmw := macWilliams C
  rw [h, hsub] at hmw
  rw [← hmw, card_toFinset]

end Code
