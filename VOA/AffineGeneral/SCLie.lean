/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Lie algebras from sparse structure constants

A table `T : Table` lists, for basis indices `i j < N`, the bracket `⁅bᵢ, bⱼ⁆ = ∑ c • b_k` as a sparse list
of pairs `(k, c)`.  If the checks hold (`Checks`: indices in range and antisymmetry, both Boolean, and the cyclic
Jacobi identity on basis triples, obtained from the Boolean `leibOK` or, more cheaply, from sorted
triples only via `jacChunk` + `jac_of_sorted`), then `Alg N T hc`
(carrier `Fin N → ℂ`) is a complex Lie algebra.  The Leibniz identity for arbitrary vectors follows from the
basis case by trilinearity (`leibniz`).

`vec l` is the vector with sparse coordinates `l`; `lie_vec` computes brackets of such vectors by the sparse
product `brL`, so identities between explicit vectors reduce to the Boolean test `zeroL`.
-/

namespace VOA.AffineGeneral.SCLie

/-- Sparse structure constants. -/
abbrev Table : Type := List (List (List (ℕ × ℤ)))

/-- The sparse bracket `⁅bᵢ, bⱼ⁆`. -/
def entry (T : Table) (i j : ℕ) : List (ℕ × ℤ) := (T.getD i []).getD j []

/-- The `k`-th coefficient of a sparse vector. -/
def coef (l : List (ℕ × ℤ)) (k : ℕ) : ℤ := (l.map fun p => if p.1 = k then p.2 else 0).sum

/-- `c • l`. -/
def scale (c : ℤ) (l : List (ℕ × ℤ)) : List (ℕ × ℤ) := l.map fun p => (p.1, c * p.2)

/-- Sparse bracket of two sparse vectors. -/
def brL (T : Table) (l₁ l₂ : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  l₁.flatMap fun p => l₂.flatMap fun q => scale (p.2 * q.2) (entry T p.1 q.1)

/-- The Leibniz defect `⁅bᵢ,⁅bⱼ,bₗ⁆⁆ + ⁅bₗ,⁅bᵢ,bⱼ⁆⁆ - ⁅bⱼ,⁅bᵢ,bₗ⁆⁆` (the middle term is `-⁅⁅bᵢ,bⱼ⁆,bₗ⁆`). -/
def leib (T : Table) (i j l : ℕ) : List (ℕ × ℤ) :=
  brL T [(i, 1)] (entry T j l) ++ brL T [(l, 1)] (entry T i j) ++
    scale (-1) (brL T [(j, 1)] (entry T i l))

/-- All coefficients of `l` vanish. -/
def zeroL (l : List (ℕ × ℤ)) : Bool := l.all fun p => coef l p.1 = 0

def boundOK (T : Table) (N : ℕ) : Bool :=
  (List.range N).all fun i => (List.range N).all fun j => (entry T i j).all fun p => p.1 < N

def antiOK (T : Table) (N : ℕ) : Bool :=
  (List.range N).all fun i => (List.range N).all fun j => zeroL (entry T i j ++ entry T j i)

def leibOK (T : Table) (N : ℕ) : Bool :=
  (List.range N).all fun i => (List.range N).all fun j => (List.range N).all fun l =>
    zeroL (leib T i j l)

/-! ## Tables from flat rows -/

/-- Sign-magnitude decoding: `2k ↦ k`, `2k+1 ↦ -k`. -/
def decZ (z : ℕ) : ℤ := if z % 2 = 0 then ((z / 2 : ℕ) : ℤ) else -((z / 2 : ℕ) : ℤ)

/-- The pairs `(c, k)` of a flat row `j c k …` at column `j`. -/
def pairsAt (j : ℕ) : List ℕ → List (ℕ × ℤ)
  | a :: c :: k :: rest => if a = j then (c, decZ k) :: pairsAt j rest else pairsAt j rest
  | _ => []

/-- A table from flat rows (row `i` lists `j c k` for `⁅bᵢ, bⱼ⁆ ∋ k·b_c`, `k` sign-encoded).  Lookups are
lazy: `entry` decodes only the requested row and column. -/
def tableOf (N : ℕ) (rows : List (List ℕ)) : Table :=
  rows.map fun r => (List.range N).map fun j => pairsAt j r

/-! ## Chunked bound and antisymmetry checks -/

/-- Index bounds for rows `lo ≤ i < hi`. -/
def boundChunk (T : Table) (N lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun i => (List.range N).all fun j => (entry T i j).all fun p => p.1 < N

/-- Antisymmetry for rows `lo ≤ i < hi`. -/
def antiChunk (T : Table) (N lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun i => (List.range N).all fun j => zeroL (entry T i j ++ entry T j i)

theorem boundOK_of_chunks (T : Table) (N : ℕ) (h : ∀ i, i < N → ∃ lo hi, lo ≤ i ∧ i < hi ∧ boundChunk T N lo hi = true) :
    boundOK T N = true := by
  unfold boundOK
  refine List.all_eq_true.mpr fun i hi => ?_
  have hi' := List.mem_range.mp hi
  obtain ⟨lo, hi2, h1, h2, hc⟩ := h i hi'
  unfold boundChunk at hc
  exact List.all_eq_true.mp hc i (List.mem_range'_1.mpr ⟨h1, by omega⟩)

theorem antiOK_of_chunks (T : Table) (N : ℕ) (h : ∀ i, i < N → ∃ lo hi, lo ≤ i ∧ i < hi ∧ antiChunk T N lo hi = true) :
    antiOK T N = true := by
  unfold antiOK
  refine List.all_eq_true.mpr fun i hi => ?_
  have hi' := List.mem_range.mp hi
  obtain ⟨lo, hi2, h1, h2, hc⟩ := h i hi'
  unfold antiChunk at hc
  exact List.all_eq_true.mp hc i (List.mem_range'_1.mpr ⟨h1, by omega⟩)

/-- The cyclic Jacobi defect `[bᵢ,[bⱼ,bₗ]] + [bⱼ,[bₗ,bᵢ]] + [bₗ,[bᵢ,bⱼ]]`. -/
def cycJ (T : Table) (i j l : ℕ) : List (ℕ × ℤ) :=
  brL T [(i, 1)] (entry T j l) ++ brL T [(j, 1)] (entry T l i) ++ brL T [(l, 1)] (entry T i j)

/-- The cyclic Jacobi check on sorted triples `i < j < l` with `lo ≤ i < hi`. -/
def jacChunk (T : Table) (N lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun i => (List.range' (i + 1) (N - (i + 1))).all fun j =>
    (List.range' (j + 1) (N - (j + 1))).all fun l => zeroL (cycJ T i j l)

/-! ## Sparse vectors -/

@[simp] theorem coef_nil (k : ℕ) : coef [] k = 0 := rfl

theorem coef_cons (p : ℕ × ℤ) (l : List (ℕ × ℤ)) (k : ℕ) :
    coef (p :: l) k = (if p.1 = k then p.2 else 0) + coef l k := by
  simp [coef]

theorem coef_append (l₁ l₂ : List (ℕ × ℤ)) (k : ℕ) :
    coef (l₁ ++ l₂) k = coef l₁ k + coef l₂ k := by
  simp [coef]

theorem coef_scale (c : ℤ) (l : List (ℕ × ℤ)) (k : ℕ) : coef (scale c l) k = c * coef l k := by
  induction l with
  | nil => simp [scale]
  | cons p l ih =>
    simp only [scale, List.map_cons] at ih ⊢
    rw [coef_cons, coef_cons, ih]
    split_ifs <;> ring

theorem coef_flatMap {α : Type*} (l : List α) (f : α → List (ℕ × ℤ)) (k : ℕ) :
    coef (l.flatMap f) k = (l.map fun a => coef (f a) k).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, coef_append, ih]

theorem coef_eq_zero_of_zeroL {l : List (ℕ × ℤ)} (h : zeroL l = true) (k : ℕ) : coef l k = 0 := by
  by_cases hk : ∃ p ∈ l, p.1 = k
  · obtain ⟨p, hp, rfl⟩ := hk
    have := List.all_eq_true.mp h p hp
    simpa using this
  · push Not at hk
    unfold coef
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simp [hk p hp]

/-- A sparse sum against `f` equals the dense sum against the coefficients. -/
theorem sum_pairs {N : ℕ} (l : List (ℕ × ℤ)) (hl : ∀ p ∈ l, p.1 < N) (f : ℕ → ℂ) :
    (l.map fun p => (p.2 : ℂ) * f p.1).sum = ∑ m : Fin N, (coef l m : ℂ) * f m := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    have hp : p.1 < N := hl p List.mem_cons_self
    simp only [coef_cons, Int.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨p.1, hp⟩]
    · simp
    · intro b _ hb
      have : p.1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp

/-! ## The algebra -/

variable {N : ℕ} {T : Table}

/-- Structure constants as complex numbers. -/
def sc (T : Table) (i j k : ℕ) : ℂ := (coef (entry T i j) k : ℂ)

theorem bound_of' (hb : boundOK T N = true) {i j : ℕ} (hi : i < N) (hj : j < N) :
    ∀ p ∈ entry T i j, p.1 < N := by
  unfold boundOK at hb
  have h1 := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  intro p hp
  simpa using List.all_eq_true.mp h2 p hp

theorem sc_anti' (ha : antiOK T N = true) {i j : ℕ} (hi : i < N) (hj : j < N) (k : ℕ) :
    sc T i j k = -sc T j i k := by
  unfold antiOK at ha
  have h1 := List.all_eq_true.mp ha i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  have := coef_eq_zero_of_zeroL h2 k
  rw [coef_append] at this
  unfold sc
  rw [eq_neg_iff_add_eq_zero]
  exact_mod_cast this

/-- The coefficient of `[bₐ, ⁅b_b, b_c⁆]` as a dense sum. -/
theorem coef_br1 (hb : boundOK T N = true) (a b c n : Fin N) :
    (coef (brL T [((a : ℕ), 1)] (entry T b c)) n : ℂ) = ∑ m : Fin N, sc T b c m * sc T a m n := by
  have e1 : coef (brL T [((a : ℕ), 1)] (entry T b c)) n
      = ((entry T b c).map fun q => q.2 * coef (entry T a q.1) n).sum := by
    simp [brL, coef_flatMap, coef_scale]
  rw [e1, Int.cast_list_sum, List.map_map]
  have e2 := sum_pairs (entry T b c) (bound_of' hb b.2 c.2) (fun m => sc T a m n)
  simp only [sc] at e2 ⊢
  rw [← e2]
  congr 1
  apply List.map_congr_left
  intro q _
  simp

/-- The cyclic Jacobi sum in coordinates. -/
def cycK (T : Table) (N : ℕ) (i j l n : Fin N) : ℂ :=
  (∑ m : Fin N, sc T j l m * sc T i m n) + (∑ m : Fin N, sc T l i m * sc T j m n) +
    ∑ m : Fin N, sc T i j m * sc T l m n

/-- The checks making `T` a Lie algebra on `ℂ^N`: index bounds, antisymmetry, cyclic Jacobi. -/
structure Checks (N : ℕ) (T : Table) : Prop where
  bound : boundOK T N = true
  anti : antiOK T N = true
  jac : ∀ i j l n : Fin N, cycK T N i j l n = 0

theorem bound_of (hc : Checks N T) {i j : ℕ} (hi : i < N) (hj : j < N) :
    ∀ p ∈ entry T i j, p.1 < N := bound_of' hc.bound hi hj

theorem sc_anti (hc : Checks N T) {i j : ℕ} (hi : i < N) (hj : j < N) (k : ℕ) :
    sc T i j k = -sc T j i k := sc_anti' hc.anti hi hj k

/-- Cyclic Jacobi from the full Leibniz check on all basis triples. -/
theorem jac_of_leibOK (hb : boundOK T N = true) (ha : antiOK T N = true) (hl : leibOK T N = true)
    (i j l n : Fin N) : cycK T N i j l n = 0 := by
  unfold leibOK at hl
  have h1 := List.all_eq_true.mp hl i (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr j.2)
  have h3 := List.all_eq_true.mp h2 l (List.mem_range.mpr l.2)
  have hz := coef_eq_zero_of_zeroL h3 n
  rw [leib, coef_append, coef_append, coef_scale] at hz
  have hz' : (coef (brL T [((i : ℕ), 1)] (entry T j l)) n : ℂ)
      + (coef (brL T [((l : ℕ), 1)] (entry T i j)) n : ℂ)
      - (coef (brL T [((j : ℕ), 1)] (entry T i l)) n : ℂ) = 0 := by
    exact_mod_cast (by linarith : (coef (brL T [((i : ℕ), 1)] (entry T j l)) n
      + coef (brL T [((l : ℕ), 1)] (entry T i j)) n
      - coef (brL T [((j : ℕ), 1)] (entry T i l)) n) = 0)
  rw [coef_br1 hb, coef_br1 hb, coef_br1 hb] at hz'
  have hanti : ∑ m : Fin N, sc T l i m * sc T j m n = -∑ m : Fin N, sc T i l m * sc T j m n := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [sc_anti' ha l.2 i.2]; ring
  unfold cycK
  linear_combination hz' + hanti

section Alternation

variable (ha : antiOK T N = true)
include ha

theorem cycK_cyc (i j l n : Fin N) : cycK T N j l i n = cycK T N i j l n := by
  unfold cycK; ring

theorem cycK_swap (i j l n : Fin N) : cycK T N i l j n = -cycK T N i j l n := by
  unfold cycK
  have e1 : ∑ m : Fin N, sc T l j m * sc T i m n = -∑ m : Fin N, sc T j l m * sc T i m n := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [sc_anti' ha l.2 j.2]; ring
  have e2 : ∑ m : Fin N, sc T j i m * sc T l m n = -∑ m : Fin N, sc T i j m * sc T l m n := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [sc_anti' ha j.2 i.2]; ring
  have e3 : ∑ m : Fin N, sc T i l m * sc T j m n = -∑ m : Fin N, sc T l i m * sc T j m n := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [sc_anti' ha i.2 l.2]; ring
  rw [e1, e2, e3]; ring

theorem cycK_self (i l n : Fin N) : cycK T N i l l n = 0 := by
  have h := cycK_swap ha i l l n
  have : (2 : ℂ) * cycK T N i l l n = 0 := by linear_combination h
  simpa using this

theorem cycK_allPerm {a b c n : Fin N} (h : cycK T N a b c n = 0) :
    cycK T N a b c n = 0 ∧ cycK T N a c b n = 0 ∧ cycK T N b a c n = 0 ∧ cycK T N b c a n = 0 ∧
      cycK T N c a b n = 0 ∧ cycK T N c b a n = 0 := by
  have hbca : cycK T N b c a n = 0 := by rw [cycK_cyc ha, h]
  have hcab : cycK T N c a b n = 0 := by rw [cycK_cyc ha, hbca]
  have hacb : cycK T N a c b n = 0 := by rw [cycK_swap ha, h, neg_zero]
  have hbac : cycK T N b a c n = 0 := by rw [cycK_swap ha, hbca, neg_zero]
  have hcba : cycK T N c b a n = 0 := by rw [cycK_swap ha, hcab, neg_zero]
  exact ⟨h, hacb, hbac, hbca, hcab, hcba⟩

/-- **Cyclic Jacobi on sorted triples suffices** (antisymmetry gives the rest). -/
theorem jac_of_sorted (hs : ∀ i j l : Fin N, i < j → j < l → cycK T N i j l n = 0) (i j l : Fin N) :
    cycK T N i j l n = 0 := by
  by_cases e1 : i = j
  · subst e1
    have := cycK_allPerm ha (cycK_self ha l i n); tauto
  by_cases e2 : j = l
  · subst e2; exact cycK_self ha i j n
  by_cases e3 : i = l
  · subst e3
    have := cycK_allPerm ha (cycK_self ha j i n); tauto
  rcases lt_or_gt_of_ne e1 with h1 | h1 <;> rcases lt_or_gt_of_ne e2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne e3 with h3 | h3
  all_goals first
    | exact hs _ _ _ (by assumption) (by assumption)
    | (have := cycK_allPerm ha (hs i l j (by assumption) (by assumption)); tauto)
    | (have := cycK_allPerm ha (hs j i l (by assumption) (by assumption)); tauto)
    | (have := cycK_allPerm ha (hs j l i (by assumption) (by assumption)); tauto)
    | (have := cycK_allPerm ha (hs l i j (by assumption) (by assumption)); tauto)
    | (have := cycK_allPerm ha (hs l j i (by assumption) (by assumption)); tauto)
    | (exfalso; simp only [Fin.lt_def] at *; omega)

end Alternation

/-- The sorted chunks cover `0 ≤ i < N`; turn the Boolean chunk checks into sorted cyclic Jacobi. -/
theorem cycK_of_chunk (hb : boundOK T N = true) {lo hi : ℕ} (h : jacChunk T N lo hi = true)
    (i j l : Fin N) (hlo : lo ≤ i.val) (hhi : i.val < hi) (hij : i < j) (hjl : j < l) (n : Fin N) :
    cycK T N i j l n = 0 := by
  unfold jacChunk at h
  have h1 := List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨hlo, by omega⟩)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  have h3 := List.all_eq_true.mp h2 l (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  have hz := coef_eq_zero_of_zeroL h3 n
  rw [cycJ, coef_append, coef_append] at hz
  have hz' : (coef (brL T [((i : ℕ), 1)] (entry T j l)) n : ℂ)
      + (coef (brL T [((j : ℕ), 1)] (entry T l i)) n : ℂ)
      + (coef (brL T [((l : ℕ), 1)] (entry T i j)) n : ℂ) = 0 := by exact_mod_cast hz
  rw [coef_br1 hb, coef_br1 hb, coef_br1 hb] at hz'
  exact hz'

/-- Cyclic Jacobi for one row `i`, columns `jlo ≤ j < jhi` (and `j > i`), all `l > j`. -/
def jacPiece (T : Table) (N i jlo jhi : ℕ) : Bool :=
  (List.range' jlo (jhi - jlo)).all fun j =>
    !decide (i < j) || (List.range' (j + 1) (N - (j + 1))).all fun l => zeroL (cycJ T i j l)

theorem cycK_of_piece (hb : boundOK T N = true) {i jlo jhi : ℕ} (h : jacPiece T N i jlo jhi = true)
    (a j l : Fin N) (ha : a.val = i) (hj1 : jlo ≤ j.val) (hj2 : j.val < jhi) (hij : a < j) (hjl : j < l)
    (n : Fin N) : cycK T N a j l n = 0 := by
  unfold jacPiece at h
  have h1 := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨hj1, by omega⟩)
  have hij' : i < j.val := by rw [← ha]; exact hij
  simp only [hij', decide_true, Bool.not_true, Bool.false_or] at h1
  have h3 := List.all_eq_true.mp h1 l (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  have hz := coef_eq_zero_of_zeroL h3 n
  rw [cycJ, coef_append, coef_append] at hz
  have hz' : (coef (brL T [((a : ℕ), 1)] (entry T j l)) n : ℂ)
      + (coef (brL T [((j : ℕ), 1)] (entry T l a)) n : ℂ)
      + (coef (brL T [((l : ℕ), 1)] (entry T a j)) n : ℂ) = 0 := by
    rw [ha]; exact_mod_cast hz
  rw [coef_br1 hb, coef_br1 hb, coef_br1 hb] at hz'
  exact hz'

/-- The carrier `ℂ^N` (a type synonym, so that no pointwise bracket is inherited). -/
def Alg (N : ℕ) (T : Table) (_hc : Checks N T) : Type := Fin N → ℂ

variable (hc : Checks N T)

instance : AddCommGroup (Alg N T hc) := inferInstanceAs (AddCommGroup (Fin N → ℂ))
instance : Module ℂ (Alg N T hc) := inferInstanceAs (Module ℂ (Fin N → ℂ))
instance : FiniteDimensional ℂ (Alg N T hc) := inferInstanceAs (FiniteDimensional ℂ (Fin N → ℂ))

theorem finrank_alg : Module.finrank ℂ (Alg N T hc) = N := Module.finrank_fin_fun ℂ

/-- The standard basis. -/
noncomputable def basis : Module.Basis (Fin N) ℂ (Alg N T hc) := Pi.basisFun ℂ (Fin N)

theorem basis_apply (i k : Fin N) :
    ((basis hc i : Alg N T hc) : Fin N → ℂ) k = if k = i then 1 else 0 := by
  show (Pi.basisFun ℂ (Fin N) i) k = _
  rw [Pi.basisFun_apply, Pi.single_apply]

/-- The coordinate functional. -/
def coordL (n : Fin N) : Alg N T hc →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) n

theorem coordL_apply (x : Alg N T hc) (n : Fin N) : coordL hc n x = (x : Fin N → ℂ) n := rfl

theorem sum_apply' {ι : Type*} (s : Finset ι) (f : ι → Alg N T hc) (n : Fin N) :
    ((∑ i ∈ s, f i : Alg N T hc) : Fin N → ℂ) n = ∑ i ∈ s, (f i : Fin N → ℂ) n :=
  map_sum (coordL hc n) f s

theorem smul_apply' (c : ℂ) (x : Alg N T hc) (n : Fin N) :
    ((c • x : Alg N T hc) : Fin N → ℂ) n = c * (x : Fin N → ℂ) n := rfl

/-- The bracket, bilinear. -/
noncomputable def B : Alg N T hc →ₗ[ℂ] Alg N T hc →ₗ[ℂ] Alg N T hc :=
  LinearMap.mk₂ ℂ (fun x y => (fun k => ∑ i : Fin N, ∑ j : Fin N,
      (x : Fin N → ℂ) i * (y : Fin N → ℂ) j * sc T i j k : Fin N → ℂ))
    (fun x x' y => by
      funext k
      show ∑ i, ∑ j, (x i + x' i) * y j * _ = (∑ i, ∑ j, x i * y j * _) + ∑ i, ∑ j, x' i * y j * _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun c x y => by
      funext k
      show ∑ i, ∑ j, (c * x i) * y j * _ = c * ∑ i, ∑ j, x i * y j * _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]; congr 1; ext; ring)
    (fun x y y' => by
      funext k
      show ∑ i, ∑ j, x i * (y j + y' j) * _ = (∑ i, ∑ j, x i * y j * _) + ∑ i, ∑ j, x i * y' j * _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun c x y => by
      funext k
      show ∑ i, ∑ j, x i * (c * y j) * _ = c * ∑ i, ∑ j, x i * y j * _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]; congr 1; ext; ring)

theorem B_apply (x y : Alg N T hc) (k : Fin N) :
    (B hc x y : Fin N → ℂ) k = ∑ i : Fin N, ∑ j : Fin N,
      (x : Fin N → ℂ) i * (y : Fin N → ℂ) j * sc T i j k := rfl

theorem B_basis_left (i : Fin N) (y : Alg N T hc) (k : Fin N) :
    (B hc (basis hc i) y : Fin N → ℂ) k = ∑ j : Fin N, (y : Fin N → ℂ) j * sc T i j k := by
  rw [B_apply, Finset.sum_eq_single i]
  · simp [basis_apply]
  · intro b _ hb
    simp [basis_apply, hb]
  · simp

theorem B_basis_right (x : Alg N T hc) (j : Fin N) (k : Fin N) :
    (B hc x (basis hc j) : Fin N → ℂ) k = ∑ i : Fin N, (x : Fin N → ℂ) i * sc T i j k := by
  rw [B_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [basis_apply]
  · intro b _ hb
    simp [basis_apply, hb]
  · simp

theorem B_anti (x y : Alg N T hc) : B hc x y = -B hc y x := by
  funext k
  show ∑ i : Fin N, ∑ j : Fin N, (x : Fin N → ℂ) i * (y : Fin N → ℂ) j * sc T i j k
    = -∑ i : Fin N, ∑ j : Fin N, (y : Fin N → ℂ) i * (x : Fin N → ℂ) j * sc T i j k
  rw [Finset.sum_comm (f := fun i j => (y : Fin N → ℂ) i * (x : Fin N → ℂ) j * sc T i j k),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sc_anti hc i.2 j.2]
  ring

include hc in
/-- The basis Leibniz identity, in coordinates. -/
theorem leib_coord (i j l n : Fin N) :
    ∑ m : Fin N, sc T j l m * sc T i m n
      = ∑ m : Fin N, sc T i j m * sc T m l n + ∑ m : Fin N, sc T i l m * sc T j m n := by
  have hz := hc.jac i j l n
  unfold cycK at hz
  have h1 : ∑ m : Fin N, sc T l i m * sc T j m n = -∑ m : Fin N, sc T i l m * sc T j m n := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [sc_anti hc l.2 i.2]; ring
  have h2 : ∑ m : Fin N, sc T i j m * sc T l m n = -∑ m : Fin N, sc T i j m * sc T m l n := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [sc_anti hc l.2 m.2]; ring
  linear_combination hz - h1 - h2

/-! ## The Lie algebra structure -/

theorem B_self (x : Alg N T hc) : B hc x x = 0 := by
  have h := B_anti hc x x
  have h2 : (2 : ℂ) • B hc x x = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem B_basis_basis (i j : Fin N) (k : Fin N) :
    (B hc (basis hc i) (basis hc j) : Fin N → ℂ) k = sc T i j k := by
  rw [B_basis_left, Finset.sum_eq_single j]
  · simp [basis_apply]
  · intro b _ hb; simp [basis_apply, hb]
  · simp

/-- **Leibniz identity** for all vectors. -/
theorem leibniz (x y z : Alg N T hc) :
    B hc x (B hc y z) = B hc (B hc x y) z + B hc y (B hc x z) := by
  -- reduce to `z` in the basis
  suffices h : ∀ x y : Alg N T hc,
      (B hc x).comp (B hc y) = B hc (B hc x y) + (B hc y).comp (B hc x) by
    have := LinearMap.congr_fun (h x y) z
    simpa using this
  intro x y
  refine (basis hc).ext fun l => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  -- reduce to `y` in the basis
  suffices h : ∀ x : Alg N T hc, (B hc x).comp ((B hc).flip (basis hc l))
      = ((B hc).flip (basis hc l)).comp (B hc x) + (B hc).flip (B hc x (basis hc l)) by
    have := LinearMap.congr_fun (h x) y
    simpa using this
  intro x
  refine (basis hc).ext fun j => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.flip_apply]
  -- reduce to `x` in the basis
  suffices h : (B hc).flip (B hc (basis hc j) (basis hc l))
      = ((B hc).flip (basis hc l)).comp ((B hc).flip (basis hc j))
        + (B hc (basis hc j)).comp ((B hc).flip (basis hc l)) by
    have := LinearMap.congr_fun h x
    simpa using this
  refine (basis hc).ext fun i => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.flip_apply]
  funext n
  show (B hc (basis hc i) (B hc (basis hc j) (basis hc l)) : Fin N → ℂ) n
    = (B hc (B hc (basis hc i) (basis hc j)) (basis hc l) : Fin N → ℂ) n
      + (B hc (basis hc j) (B hc (basis hc i) (basis hc l)) : Fin N → ℂ) n
  rw [B_basis_left, B_basis_right, B_basis_left]
  simp only [B_basis_basis]
  have h := leib_coord hc i j l n
  rw [h]

noncomputable instance : LieRing (Alg N T hc) where
  bracket x y := B hc x y
  add_lie x y z := by show B hc (x + y) z = B hc x z + B hc y z; rw [map_add, LinearMap.add_apply]
  lie_add x y z := map_add _ _ _
  lie_self x := B_self hc x
  leibniz_lie x y z := leibniz hc x y z

noncomputable instance : LieAlgebra ℂ (Alg N T hc) where
  lie_smul c x y := map_smul (B hc x) c y

theorem lie_def (x y : Alg N T hc) : ⁅x, y⁆ = B hc x y := rfl

/-! ## Sparse vectors in the algebra -/

/-- The vector with sparse coordinates `l`. -/
def vec (l : List (ℕ × ℤ)) : Alg N T hc := fun k => (coef l k : ℂ)

/-- All indices of `l` are `< N`. -/
def inRange (N : ℕ) (l : List (ℕ × ℤ)) : Bool := l.all fun p => p.1 < N

theorem vec_eq_of_zeroL {l₁ l₂ : List (ℕ × ℤ)} (c : ℤ) (h : zeroL (l₁ ++ scale (-c) l₂) = true) :
    vec hc l₁ = (c : ℂ) • vec hc l₂ := by
  funext k
  have := coef_eq_zero_of_zeroL h k
  rw [coef_append, coef_scale] at this
  show (coef l₁ k : ℂ) = (c : ℂ) * (coef l₂ k : ℂ)
  have : coef l₁ k = c * coef l₂ k := by linarith
  exact_mod_cast this

theorem vec_eq_zero_of_zeroL {l : List (ℕ × ℤ)} (h : zeroL l = true) : vec hc l = 0 := by
  funext k
  show (coef l k : ℂ) = 0
  exact_mod_cast coef_eq_zero_of_zeroL h k

theorem basis_eq_vec (i : Fin N) : basis hc i = vec hc [((i : ℕ), 1)] := by
  funext k
  rw [basis_apply]
  show _ = (coef [((i : ℕ), 1)] k : ℂ)
  simp only [coef_cons, coef_nil, add_zero]
  by_cases h : k = i
  · subst h; simp
  · have : (i : ℕ) ≠ k := fun h' => h (Fin.ext h'.symm)
    simp [h, this]

/-- **Brackets of sparse vectors.** -/
theorem lie_vec {l₁ l₂ : List (ℕ × ℤ)} (h₁ : inRange N l₁ = true) (h₂ : inRange N l₂ = true) :
    ⁅vec hc l₁, vec hc l₂⁆ = vec hc (brL T l₁ l₂) := by
  have r₁ : ∀ p ∈ l₁, p.1 < N := fun p hp => by simpa using List.all_eq_true.mp h₁ p hp
  have r₂ : ∀ p ∈ l₂, p.1 < N := fun p hp => by simpa using List.all_eq_true.mp h₂ p hp
  funext n
  rw [lie_def]
  show ∑ i : Fin N, ∑ j : Fin N, (coef l₁ i : ℂ) * (coef l₂ j : ℂ) * sc T i j n
    = (coef (brL T l₁ l₂) n : ℂ)
  have e1 : coef (brL T l₁ l₂) n = (l₁.map fun p => p.2 * (l₂.map fun q => q.2 *
      coef (entry T p.1 q.1) n).sum).sum := by
    unfold brL
    rw [coef_flatMap]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [coef_flatMap, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q _
    rw [coef_scale]
    ring
  rw [e1, Int.cast_list_sum, List.map_map]
  have e2 := sum_pairs l₁ r₁ (fun a => ∑ j : Fin N, (coef l₂ j : ℂ) * sc T a j n)
  have e3 : ∀ a : ℕ, (l₂.map fun q => (q.2 : ℂ) * sc T a q.1 n).sum
      = ∑ j : Fin N, (coef l₂ j : ℂ) * sc T a j n := fun a => sum_pairs l₂ r₂ (fun m => sc T a m n)
  calc ∑ i : Fin N, ∑ j : Fin N, (coef l₁ i : ℂ) * (coef l₂ j : ℂ) * sc T i j n
      = ∑ i : Fin N, (coef l₁ i : ℂ) * ∑ j : Fin N, (coef l₂ j : ℂ) * sc T i j n := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (l₁.map fun p => (p.2 : ℂ) * ∑ j : Fin N, (coef l₂ j : ℂ) * sc T p.1 j n).sum := e2.symm
    _ = _ := by
        congr 1
        apply List.map_congr_left
        intro p _
        simp only [Function.comp_apply]
        rw [← e3 p.1, Int.cast_mul, Int.cast_list_sum, List.map_map]
        congr 2
        apply List.map_congr_left
        intro q _
        simp [sc]

end VOA.AffineGeneral.SCLie
