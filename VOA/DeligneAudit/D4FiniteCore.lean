/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# Verified computable Laurent polynomials (generic core)

Term lists `List ((ℕ × E) × ℤ)` represent elements of a monoid algebra `ℤ[G]` through an exponent
map `toG : E → G`.  The packed key `ℕ` only orders terms; two terms are combined only when their
keys *and* exponent data agree.  Hence every evaluation lemma below holds unconditionally: list
order and key values affect efficiency only.

Provided operations (all structurally recursive, so kernel `decide` evaluates them):
`addP` (merge), `normalize` (merge sort), `negP`, `subP`, `mulPG` (product), `demPG` (an isobaric
Demazure operator along a root string), with correctness lemmas `evalG_*`.  The generic Demazure
operator `demazureG pr r` on `ℤ[G]` acts monomialwise by the `r`-string formula with pairing `pr`.
-/

namespace VOA.DeligneAudit.D4Finite.Gen

open scoped BigOperators

/-! ## Algebraic side: the generic Demazure operator -/

noncomputable section Algebraic

variable {G : Type*} [AddCommMonoid G]

/-- `π` on one monomial, for a pairing `pr` and a root-string shift `sh j e = e + j r`:
`z^e ↦ Σ_{j=0}^{n} z^{sh (-j) e}` if `n = pr e ≥ 0`, and `z^e ↦ -Σ_{j=1}^{-n-1} z^{sh j e}`
if `n < 0`. -/
def demMonoG (pr : G → ℤ) (sh : ℤ → G → G) (e : G) (c : ℤ) : AddMonoidAlgebra ℤ G :=
  if 0 ≤ pr e then
    ∑ j ∈ Finset.range ((pr e).toNat + 1), AddMonoidAlgebra.single (sh (-(j : ℤ)) e) c
  else
    -∑ j ∈ Finset.range ((-pr e).toNat - 1), AddMonoidAlgebra.single (sh ((j : ℤ) + 1) e) c

theorem demMonoG_zero (pr : G → ℤ) (sh : ℤ → G → G) (e : G) : demMonoG pr sh e 0 = 0 := by
  unfold demMonoG
  split_ifs
  · exact Finset.sum_eq_zero fun _ _ => Finsupp.single_zero _
  · rw [Finset.sum_eq_zero fun _ _ => Finsupp.single_zero _, neg_zero]

theorem demMonoG_add (pr : G → ℤ) (sh : ℤ → G → G) (e : G) (c d : ℤ) :
    demMonoG pr sh e (c + d) = demMonoG pr sh e c + demMonoG pr sh e d := by
  unfold demMonoG
  split_ifs
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [AddMonoidAlgebra.single_add]
  · rw [← neg_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by rw [AddMonoidAlgebra.single_add]

/-- The Demazure operator, extended additively. -/
def demazureG (pr : G → ℤ) (sh : ℤ → G → G) (f : AddMonoidAlgebra ℤ G) : AddMonoidAlgebra ℤ G :=
  f.sum (demMonoG pr sh)

theorem demazureG_add (pr : G → ℤ) (sh : ℤ → G → G) (f g : AddMonoidAlgebra ℤ G) :
    demazureG pr sh (f + g) = demazureG pr sh f + demazureG pr sh g :=
  Finsupp.sum_add_index' (demMonoG_zero pr sh) (demMonoG_add pr sh)

theorem demazureG_single (pr : G → ℤ) (sh : ℤ → G → G) (e : G) (c : ℤ) :
    demazureG pr sh (AddMonoidAlgebra.single e c) = demMonoG pr sh e c :=
  Finsupp.sum_single_index (demMonoG_zero pr sh e)

theorem demazureG_zero (pr : G → ℤ) (sh : ℤ → G → G) : demazureG pr sh 0 = 0 :=
  Finsupp.sum_zero_index

theorem demazureG_finset_sum {ι : Type*} (pr : G → ℤ) (sh : ℤ → G → G) (s : Finset ι)
    (F : ι → AddMonoidAlgebra ℤ G) :
    demazureG pr sh (∑ i ∈ s, F i) = ∑ i ∈ s, demazureG pr sh (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [demazureG_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, demazureG_add, ih]

omit [AddCommMonoid G] in
theorem demazureG_eq_sum (pr : G → ℤ) (sh : ℤ → G → G) (f : AddMonoidAlgebra ℤ G) :
    demazureG pr sh f = ∑ e ∈ f.support, demMonoG pr sh e (f e) := rfl

/-- Shifting a monomial by a neutral exponent `m`. -/
theorem demMonoG_shift (pr : G → ℤ) (sh : ℤ → G → G) (e m : G) (c d : ℤ)
    (hm : pr (e + m) = pr e) (hsh : ∀ j, sh j (e + m) = sh j e + m) :
    demMonoG pr sh (e + m) (c * d) = demMonoG pr sh e c * AddMonoidAlgebra.single m d := by
  unfold demMonoG
  rw [hm]
  split_ifs
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [AddMonoidAlgebra.single_mul_single, hsh]
  · rw [neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [AddMonoidAlgebra.single_mul_single, hsh]

/-- `π (f · h) = π f · h` when every monomial `m` of `h` is neutral: `pr (e + m) = pr e` and
`sh j (e + m) = sh j e + m`. -/
theorem demazureG_mul_neutral (pr : G → ℤ) (sh : ℤ → G → G) (f h : AddMonoidAlgebra ℤ G)
    (hh : ∀ m ∈ h.support, ∀ e, pr (e + m) = pr e ∧ ∀ j, sh j (e + m) = sh j e + m) :
    demazureG pr sh (f * h) = demazureG pr sh f * h := by
  rw [AddMonoidAlgebra.mul_def, Finsupp.sum, demazureG_finset_sum, demazureG_eq_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finsupp.sum, demazureG_finset_sum]
  conv_rhs => rw [← h.sum_single, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [demazureG_single, demMonoG_shift pr sh e m (f e) (h m) (hh m hm e).1 (hh m hm e).2]

end Algebraic

/-! ## Computable term lists -/

variable {E : Type}

/-- A term: `((packed key, exponent data), coefficient)`. -/
abbrev Tm (E : Type) := (ℕ × E) × ℤ

/-- Insert-merge of a term into a list, given the recursive merge of the tail. -/
def addAux [DecidableEq E] (a : Tm E) (p : List (Tm E)) (rec : List (Tm E) → List (Tm E)) :
    List (Tm E) → List (Tm E)
  | [] => a :: p
  | b :: q =>
    if a.1.1 < b.1.1 then a :: rec (b :: q)
    else if b.1.1 < a.1.1 then b :: addAux a p rec q
    else if a.1.2 = b.1.2 then
      (if a.2 + b.2 = 0 then rec q else (a.1, a.2 + b.2) :: rec q)
    else a :: rec (b :: q)

/-- Merge-addition of term lists. -/
def addP [DecidableEq E] : List (Tm E) → List (Tm E) → List (Tm E)
  | [], q => q
  | a :: p, q => addAux a p (addP p) q

def mergePairs [DecidableEq E] : List (List (Tm E)) → List (List (Tm E))
  | [] => []
  | [p] => [p]
  | p :: q :: rest => addP p q :: mergePairs rest

def iterMerge [DecidableEq E] : ℕ → List (List (Tm E)) → List (List (Tm E))
  | 0, l => l
  | n + 1, l => iterMerge n (mergePairs l)

/-- Normalize a raw term list (merge sort with combination of equal monomials). -/
def normalize [DecidableEq E] (raw : List (Tm E)) : List (Tm E) :=
  (iterMerge 24 (raw.map fun t => [t])).foldr addP []

def negP (p : List (Tm E)) : List (Tm E) := p.map fun t => (t.1, -t.2)

def subP [DecidableEq E] (p q : List (Tm E)) : List (Tm E) := addP p (negP q)

/-- Multiply a list by one term (`addX` adds exponent data; `kb` is the key bias). -/
def mulTermG (addX : E → E → E) (kb : ℕ) (t : Tm E) (p : List (Tm E)) : List (Tm E) :=
  p.map fun s => ((t.1.1 + s.1.1 - kb, addX t.1.2 s.1.2), t.2 * s.2)

/-- Product of term lists. -/
def mulPG [DecidableEq E] (addX : E → E → E) (kb : ℕ) (p q : List (Tm E)) : List (Tm E) :=
  normalize (q.map fun t => mulTermG addX kb t p).flatten

/-- The string of one term under a Demazure operator (`pr` pairing, `sh j e = e + j r`,
`kd` key increment of `r`). -/
def demTermG (pr : E → ℤ) (sh : ℤ → E → E) (kd : ℤ) (t : Tm E) : List (Tm E) :=
  if 0 ≤ pr t.1.2 then
    (List.range ((pr t.1.2).toNat + 1)).map fun (j : ℕ) =>
      ((((t.1.1 : ℤ) - (j : ℤ) * kd).toNat, sh (-(j : ℤ)) t.1.2), t.2)
  else (List.range ((-pr t.1.2).toNat - 1)).map fun (j : ℕ) =>
    ((((t.1.1 : ℤ) + ((j : ℤ) + 1) * kd).toNat, sh ((j : ℤ) + 1) t.1.2), -t.2)

def demPG [DecidableEq E] (pr : E → ℤ) (sh : ℤ → E → E) (kd : ℤ) (p : List (Tm E)) : List (Tm E) :=
  normalize (p.map (demTermG pr sh kd)).flatten

/-! ## Evaluation and correctness -/

noncomputable section Eval

variable {G : Type*} [AddCommMonoid G] (toG : E → G)

/-- The element of `ℤ[G]` represented by a term list. -/
def evalG (p : List (Tm E)) : AddMonoidAlgebra ℤ G :=
  (p.map fun t => AddMonoidAlgebra.single (toG t.1.2) t.2).sum

@[simp] theorem evalG_nil : evalG toG [] = 0 := rfl

@[simp] theorem evalG_cons (t : Tm E) (p : List (Tm E)) :
    evalG toG (t :: p) = AddMonoidAlgebra.single (toG t.1.2) t.2 + evalG toG p := by
  simp [evalG]

theorem evalG_append (p q : List (Tm E)) : evalG toG (p ++ q) = evalG toG p + evalG toG q := by
  simp [evalG]

theorem evalG_flatten (l : List (List (Tm E))) :
    evalG toG l.flatten = (l.map (evalG toG)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.flatten_cons, evalG_append, ih, List.map_cons, List.sum_cons]

theorem evalG_addAux [DecidableEq E] (a : Tm E) (p : List (Tm E)) (rec : List (Tm E) → List (Tm E))
    (hrec : ∀ r, evalG toG (rec r) = evalG toG p + evalG toG r) (q : List (Tm E)) :
    evalG toG (addAux a p rec q) = evalG toG (a :: p) + evalG toG q := by
  induction q with
  | nil => simp [addAux]
  | cons b q ih =>
      unfold addAux
      split_ifs with h1 h2 h3 h4
      · rw [evalG_cons, hrec]
        simp only [evalG_cons]
        abel
      · rw [evalG_cons, ih]
        simp only [evalG_cons]
        abel
      · rw [hrec]
        simp only [evalG_cons]
        rw [h3]
        have : AddMonoidAlgebra.single (toG b.1.2) a.2 +
            AddMonoidAlgebra.single (toG b.1.2) b.2 = 0 := by
          rw [← AddMonoidAlgebra.single_add, h4]; exact Finsupp.single_zero _
        linear_combination (-1 : AddMonoidAlgebra ℤ G) * this
      · rw [evalG_cons, hrec]
        simp only [evalG_cons]
        rw [h3, AddMonoidAlgebra.single_add]
        abel
      · rw [evalG_cons, hrec]
        simp only [evalG_cons]
        abel

theorem evalG_addP [DecidableEq E] (p q :
    List (Tm E)) : evalG toG (addP p q) = evalG toG p + evalG toG q := by
  induction p generalizing q with
  | nil => simp [addP]
  | cons a p ih => exact evalG_addAux toG a p (addP p) ih q

theorem evalG_mergePairs [DecidableEq E] (l : List (List (Tm E))) :
    ((mergePairs l).map (evalG toG)).sum = (l.map (evalG toG)).sum := by
  induction l using mergePairs.induct with
  | case1 => rfl
  | case2 p => rfl
  | case3 p q rest ih =>
      simp only [mergePairs, List.map_cons, List.sum_cons, evalG_addP, ih]
      abel

theorem evalG_iterMerge [DecidableEq E] (n : ℕ) (l : List (List (Tm E))) :
    ((iterMerge n l).map (evalG toG)).sum = (l.map (evalG toG)).sum := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [iterMerge, ih, evalG_mergePairs]

theorem evalG_foldr_addP [DecidableEq E] (l : List (List (Tm E))) :
    evalG toG (l.foldr addP []) = (l.map (evalG toG)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.foldr_cons, evalG_addP, ih, List.map_cons, List.sum_cons]

theorem evalG_normalize [DecidableEq E] (raw :
    List (Tm E)) : evalG toG (normalize raw) = evalG toG raw := by
  rw [normalize, evalG_foldr_addP, evalG_iterMerge]
  induction raw with
  | nil => rfl
  | cons t raw ih => simp only [List.map_cons, List.sum_cons, ih, evalG_cons, evalG_nil, add_zero]

theorem evalG_negP (p : List (Tm E)) : evalG toG (negP p) = -evalG toG p := by
  induction p with
  | nil => simp [negP]
  | cons t p ih =>
      simp only [negP, List.map_cons, evalG_cons] at ih ⊢
      rw [ih, neg_add, AddMonoidAlgebra.single_neg]

theorem evalG_subP [DecidableEq E] (p q :
    List (Tm E)) : evalG toG (subP p q) = evalG toG p - evalG toG q := by
  rw [subP, evalG_addP, evalG_negP, sub_eq_add_neg]

theorem evalG_mulTermG (addX : E → E → E) (hX : ∀ a b, toG (addX a b) = toG a + toG b)
    (kb : ℕ) (t : Tm E) (p : List (Tm E)) :
    evalG toG (mulTermG addX kb t p) = AddMonoidAlgebra.single (toG t.1.2) t.2 * evalG toG p := by
  induction p with
  | nil => simp [mulTermG]
  | cons s p ih =>
      simp only [mulTermG, List.map_cons, evalG_cons] at ih ⊢
      rw [ih, mul_add, AddMonoidAlgebra.single_mul_single, hX]

theorem evalG_mulPG [DecidableEq E] (addX : E → E → E) (hX : ∀ a b, toG (addX a b) = toG a + toG b)
    (kb : ℕ) (p q : List (Tm E)) :
    evalG toG (mulPG addX kb p q) = evalG toG p * evalG toG q := by
  rw [mulPG, evalG_normalize, evalG_flatten, List.map_map]
  induction q with
  | nil => simp
  | cons t q ih =>
      rw [List.map_cons, List.sum_cons, Function.comp_apply, evalG_mulTermG toG addX hX, ih,
        evalG_cons]
      ring

theorem list_range_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem evalG_map_range (n : ℕ) (k : ℕ → ℕ) (g : ℕ → E) (c : ℕ → ℤ) :
    evalG toG ((List.range n).map fun j => ((k j, g j), c j)) =
      ∑ j ∈ Finset.range n, AddMonoidAlgebra.single (toG (g j)) (c j) := by
  rw [evalG, List.map_map, ← list_range_sum]
  rfl

theorem evalG_demTermG (pr : E → ℤ) (sh : ℤ → E → E) (kd : ℤ) (prG : G → ℤ)
    (shG : ℤ → G → G) (hpr : ∀ e, pr e = prG (toG e)) (hsh : ∀ j e, toG (sh j e) = shG j (toG e))
    (t : Tm E) :
    evalG toG (demTermG pr sh kd t) = demMonoG prG shG (toG t.1.2) t.2 := by
  unfold demTermG demMonoG
  rw [hpr]
  split_ifs with h
  · rw [evalG_map_range (c := fun _ => t.2)]
    exact Finset.sum_congr rfl fun j _ => by rw [hsh]
  · rw [evalG_map_range (c := fun _ => -t.2), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hsh, AddMonoidAlgebra.single_neg]

theorem demazureG_evalG (prG : G → ℤ) (shG : ℤ → G → G) (p : List (Tm E)) :
    demazureG prG shG (evalG toG p) = (p.map fun t => demMonoG prG shG (toG t.1.2) t.2).sum := by
  induction p with
  | nil => simp [demazureG_zero]
  | cons t p ih =>
      rw [evalG_cons, demazureG_add, demazureG_single, ih, List.map_cons, List.sum_cons]

theorem evalG_demPG [DecidableEq E] (pr : E → ℤ) (sh : ℤ → E → E) (kd : ℤ) (prG : G → ℤ)
    (shG : ℤ → G → G) (hpr : ∀ e, pr e = prG (toG e)) (hsh : ∀ j e, toG (sh j e) = shG j (toG e))
    (p : List (Tm E)) :
    evalG toG (demPG pr sh kd p) = demazureG prG shG (evalG toG p) := by
  rw [demPG, evalG_normalize, evalG_flatten, List.map_map, demazureG_evalG]
  congr 1
  apply List.map_congr_left
  intro t _
  exact evalG_demTermG toG pr sh kd prG shG hpr hsh t

end Eval

end VOA.DeligneAudit.D4Finite.Gen
