/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroGrading
import VOA.Examples.VirasoroSpanning
import VOA.Examples.VirasoroNonvanishing

/-!
# The partition basis of the Virasoro vacuum module `V(c,0)`

The creation monomials `negWordVir c [i₁,…,i_k] = L₋ᵢ₁₋₂ ⋯ L₋ᵢₖ₋₂ |0⟩` are indexed by *all* lists
of naturals, an index set which is far too big: `negWordVir c [0,2]` and `negWordVir c [2,0]`
differ by `⁅L₋₂,L₋₄⁆ = 2 L₋₆`, so the two lists name two different (and dependent) vectors.  The
redundancy is exactly the failure of the index list to be sorted.

This file removes it, and then shows nothing else is left to remove.

1. **Straightening.**  Every creation monomial is a `ℂ`-linear combination of monomials indexed by
   **weakly decreasing** lists of the *same* energy.  Since the entry `i` denotes the mode
   `L₋ᵢ₋₂`, a weakly decreasing list of energy `n` is exactly a **partition of `n` into parts
   `≥ 2`**.
2. **Independence.**  The partition-indexed monomials are linearly independent, at **every**
   central charge.  Hence `gradingVir c n` has a partition-indexed basis and
   `dim 𝒱ₙ = p₂(n)` — the input the Kac determinant needs, since a determinant is the determinant
   of a *finite* matrix.

## How independence is proved (and why degenerate `c` cannot spoil it)

Via the linear-dilaton free boson `Lₙ^λ = Lₙ^{Sug} + λ(n+1)aₙ` on `Fock = ℂ[X₀,X₁,…]` of central
charge `c = 1 − 12λ²` (`Examples/VirasoroNonvanishing`), which realises every `c`.  The point is
the **top-degree symbol**: writing `L₋ᵢ₋₂^λ = P_{i+2}·(−) + (raises polynomial degree by ≤ 1)`
with `P_{i+2} = ½ ∑_{a+b=i} X_a X_b` (`creationPoly`), the degree-`2k` part of the image of a
length-`k` word is `∏ⱼ P_{iⱼ+2}` — **independent of `λ`, hence of `c`**.  Degeneracy at the
minimal-model charges lives in the *simple quotient* `L(c,0)`, not in `V(c,0)`, and this argument
never sees it.  The symbols are then separated by the one-variable specialisation `X_p ↦ t^{Bᵖ}`
(`tSub`): base-`B` exponents are super-increasing, so the `t`-degree reads off the partition.

## Main results

* `negWordVir_swap` — the one straightening identity:
    `negWordVir c (i :: j :: rest) = negWordVir c (j :: i :: rest)`
  `  + (j - i) • negWordVir c ((i+j+2) :: rest)`, energy-preserving since `(i+2)+(j+2) = (i+j+2)+2`.
* `Lop_sorted_insert` — **the insertion lemma**: for `w` sorted, `L₋ₙ₋₂ · negWordVir c w` lies in
  the span of the sorted words of energy `energyVir (n :: w)`.  Strong induction on `energyVir w`
  alone; both recursive calls strictly decrease it.
* `negWordVir_mem_sortedSpanVir`, `gradingVir_eq_sortedSpanVir` — **the sorting lemma** and its
  graded form: `gradingVir c n` is spanned by the sorted (= partition-indexed) monomials.
* `Lvir_creation_vacuum` — `L₋ᵢ₋₂|0⟩ = P_{i+2}` in `Fock`, the explicit creation quadratic.
* `fockWordVir_sub_creationProd` — **the top-degree symbol**: `fockWordVir lam ws` differs from the
  `lam`-free product `∏ⱼ P_{iⱼ+2}` by something of strictly smaller polynomial degree.
* `fock_transfer` — a vanishing relation in `VirUniv c` becomes one in `Fock`.
* `negWordVir_coef_zero`, `sortedWord_linearIndependent` — **independence of the sorted creation
  monomials, at every central charge**.
* `negWordVir_ne_zero` — every sorted creation monomial is nonzero (so `L₋ₙ|0⟩ ≠ 0`, `n ≥ 2`).
* `gradedBasis` — **the partition-indexed basis** of `gradingVir c n`.
* `finrank_gradingVir` — `dim 𝒱ₙ = #{partitions of n into parts ≥ 2}`, with the low-level values
  `finrank_gradingVir_two/three/four/five/six` = `1, 1, 2, 2, 4`.
* `gradingVir_six_span` — the explicit level-6 spanning set, one level past brute enumeration.

## Status

`sorry`-free, axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`), **`pbw`-free**: the
theorem `VOA.pbw` is *not* used anywhere here, and is not needed
— neither of its two fields would give monomial independence in any case.

`finrank_gradingVir_four = 2` independently reproduces `LeeYangSingular.level4_indep`, and
`finrank_gradingVir_two = 1` reproduces `LeeYangSingular.L2vac_ne_zero`.

**Scope.**  This is the *universal* vacuum module `V(c,0) = U(𝔙𝔦𝔯)/J(c)`, which is free over
`U(span{L₋₂,L₋₃,…})`; it says nothing about the simple quotient `L(c,0)`, where the null vectors
actually live.  Nothing here has been done for the affine case (`Examples/AffineSl2Indep`).
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)

variable (c : ℂ)

/-! ## §1  The straightening identity. -/

/-- The Virasoro relation in applied form on `VirUniv c`:
`Lₘ(Lₙ w) = Lₙ(Lₘ w) + (m-n)·L_{m+n} w + δ_{m+n,0}·((m³-m)/12)c·w`. -/
theorem Lop_apply_bracket (m n : ℤ) (w : VirUniv c) :
    Lop c m (Lop c n w)
      = Lop c n (Lop c m w) + ((m : ℂ) - n) • Lop c (m + n) w
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * c else 0) • w := by
  have h := congrArg (fun T : End ℂ (VirUniv c) => T w) (Lop_bracket c m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  rw [eq_add_of_sub_eq h]
  module

/-- **The straightening identity.**  Transposing two adjacent creation modes costs one *merged*
monomial: `L₋ᵢ₋₂ L₋ⱼ₋₂ = L₋ⱼ₋₂ L₋ᵢ₋₂ + (j-i) L₋₍ᵢ₊ⱼ₊₂₎₋₂`.  There is no central term because
`(-i-2) + (-j-2) ≠ 0`, and all three words have the same energy since
`(i+2) + (j+2) = ((i+j+2) + 2)`. -/
theorem negWordVir_swap (i j : ℕ) (rest : List ℕ) :
    negWordVir c (i :: j :: rest)
      = negWordVir c (j :: i :: rest)
        + ((j : ℂ) - (i : ℂ)) • negWordVir c ((i + j + 2) :: rest) := by
  have h := Lop_apply_bracket c (-(i : ℤ) - 2) (-(j : ℤ) - 2) (negWordVir c rest)
  rw [if_neg (by omega : ¬((-(i : ℤ) - 2) + (-(j : ℤ) - 2) = 0)), zero_smul, add_zero,
    show (-(i : ℤ) - 2) + (-(j : ℤ) - 2) = -((i + j + 2 : ℕ) : ℤ) - 2 from by push_cast; ring,
    show ((-(i : ℤ) - 2 : ℤ) : ℂ) - ((-(j : ℤ) - 2 : ℤ) : ℂ) = (j : ℂ) - (i : ℂ) from by
      push_cast; ring] at h
  simp only [negWordVir_cons]
  exact h

/-- The energies of the three words in `negWordVir_swap` agree. -/
theorem energyVir_swap (i j : ℕ) (rest : List ℕ) :
    energyVir (i :: j :: rest) = energyVir (j :: i :: rest) ∧
      energyVir (i :: j :: rest) = energyVir ((i + j + 2) :: rest) := by
  simp only [energyVir_cons]; omega

/-! ## §2  Sorted words and their span. -/

/-- A **sorted word** is a weakly decreasing list of naturals.  Since the entry `i` denotes the
mode `L₋ᵢ₋₂`, sorted words of energy `n` are exactly the partitions of `n` into parts `≥ 2`. -/
def SortedWord (w : List ℕ) : Prop := w.Pairwise (· ≥ ·)

/-- Sortedness is decidable by comparing the finitely many natural indices. This supports the finite partition enumerations used later. -/
instance (w : List ℕ) : Decidable (SortedWord w) := by
  unfold SortedWord; infer_instance

/-- The empty word is already sorted. It represents the vacuum, the unique partition of energy zero. -/
theorem sortedWord_nil : SortedWord [] := List.Pairwise.nil

/-- A one-mode creation word is sorted automatically; there are no adjacent entries to compare. -/
theorem sortedWord_singleton (n : ℕ) : SortedWord [n] := List.pairwise_singleton _ _

/-- Removing the first creation mode from a sorted word preserves the order of all remaining modes. This supplies the shorter sorted word used in insertion induction. -/
theorem SortedWord.tail {n : ℕ} {w : List ℕ} (h : SortedWord (n :: w)) : SortedWord w :=
  (List.pairwise_cons.mp h).2

/-- The first index of a decreasing word is at least every later index. This lets the insertion proof decide whether a new creation mode is already in its correct position. -/
theorem SortedWord.head_ge {n : ℕ} {w : List ℕ} (h : SortedWord (n :: w)) :
    ∀ b ∈ w, n ≥ b := (List.pairwise_cons.mp h).1

/-- Prepending a value at least as large as the head keeps a word sorted. -/
theorem SortedWord.cons {n : ℕ} {w : List ℕ} (hw : SortedWord w)
    (h : ∀ b ∈ w, n ≥ b) : SortedWord (n :: w) :=
  List.pairwise_cons.mpr ⟨h, hw⟩

/-- The **sorted span** at energy `n`: the `ℂ`-span of the creation monomials indexed by sorted
words of energy `n` (equivalently: by partitions of `n` into parts `≥ 2`). -/
noncomputable def sortedSpanVir (n : ℕ) : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ {x | ∃ u : List ℕ, SortedWord u ∧ energyVir u = n ∧ negWordVir c u = x}

/-- A sorted creation monomial of energy n is one of the generators of the sorted span at n, so it belongs to that span without further straightening. -/
theorem negWordVir_mem_sortedSpanVir_of_sorted {u : List ℕ} (hu : SortedWord u) {n : ℕ}
    (hn : energyVir u = n) : negWordVir c u ∈ sortedSpanVir c n :=
  Submodule.subset_span ⟨u, hu, hn, rfl⟩

/-! ## §3  The insertion lemma. -/

/-- Transport of the insertion property from generators to the whole sorted span. -/
theorem sortedSpanVir_stable {N : ℕ}
    (H : ∀ w : List ℕ, energyVir w = N → SortedWord w → ∀ n : ℕ,
      Lop c (-(n : ℤ) - 2) (negWordVir c w) ∈ sortedSpanVir c (N + n + 2))
    (n : ℕ) {v : VirUniv c} (hv : v ∈ sortedSpanVir c N) :
    Lop c (-(n : ℤ) - 2) v ∈ sortedSpanVir c (N + n + 2) := by
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨u, hu, he, rfl⟩ := hy; exact H u he hu n
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **The insertion lemma.**  Applying one more creation mode `L₋ₙ₋₂` to a *sorted* monomial lands
in the span of the sorted monomials of the same (new) energy.

The induction is a strong induction on `energyVir w` **alone**, with `n` universally quantified
inside.  In the swap branch (`n < j`) the merged word `(n+j+2) :: rest` is sorted outright and
costs no recursion; the transposed word needs the insertion property at `energyVir rest` and then
again at `energyVir (n :: rest)`, both strictly below `energyVir w` — the second one precisely
because `n < j`. -/
theorem Lop_sorted_insert (N : ℕ) :
    ∀ w : List ℕ, energyVir w = N → SortedWord w → ∀ n : ℕ,
      Lop c (-(n : ℤ) - 2) (negWordVir c w) ∈ sortedSpanVir c (N + n + 2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hsort n
    match w with
    | [] =>
        have hN : N = 0 := by rw [← hw]; rfl
        subst hN
        have : Lop c (-(n : ℤ) - 2) (negWordVir c ([] : List ℕ)) = negWordVir c [n] := rfl
        rw [this]
        exact negWordVir_mem_sortedSpanVir_of_sorted c (sortedWord_singleton n)
          (by simp only [energyVir_cons, energyVir_nil]; omega)
    | (j :: rest) =>
        have hw' : (j + 2) + energyVir rest = N := by rw [← hw, energyVir_cons]
        have hstep : Lop c (-(n : ℤ) - 2) (negWordVir c (j :: rest))
            = negWordVir c (n :: j :: rest) := rfl
        rw [hstep]
        rcases Nat.lt_or_ge n j with hnj | hjn
        · -- swap
          rw [negWordVir_swap]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
          · -- the transposed word `j :: n :: rest`
            have hMlt : energyVir rest < N := by omega
            have h1 : Lop c (-(n : ℤ) - 2) (negWordVir c rest)
                ∈ sortedSpanVir c (energyVir rest + n + 2) :=
              ih _ hMlt rest rfl hsort.tail n
            have hM'lt : energyVir rest + n + 2 < N := by omega
            have h2 := sortedSpanVir_stable c (ih _ hM'lt) j h1
            have hrw : energyVir rest + n + 2 + j + 2 = N + n + 2 := by omega
            rw [hrw] at h2
            exact h2
          · -- the merged word `(n+j+2) :: rest`
            refine negWordVir_mem_sortedSpanVir_of_sorted c (SortedWord.cons hsort.tail ?_) ?_
            · intro b hb
              exact le_trans (hsort.head_ge b hb) (by omega)
            · simp only [energyVir_cons]; omega
        · -- already sorted
          refine negWordVir_mem_sortedSpanVir_of_sorted c (SortedWord.cons hsort ?_) ?_
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hjn
            · exact le_trans (hsort.head_ge b hb') hjn
          · simp only [energyVir_cons]; omega

/-! ## §4  The sorting lemma and the graded consequence. -/

/-- **The sorting lemma.**  Every creation monomial lies in the span of the *sorted* creation
monomials of the same energy. -/
theorem negWordVir_mem_sortedSpanVir (ws : List ℕ) :
    negWordVir c ws ∈ sortedSpanVir c (energyVir ws) := by
  induction ws with
  | nil =>
      exact negWordVir_mem_sortedSpanVir_of_sorted c sortedWord_nil rfl
  | cons i rest ih =>
      have h := sortedSpanVir_stable c (Lop_sorted_insert c (energyVir rest)) i ih
      have hrw : energyVir rest + i + 2 = energyVir (i :: rest) := by
        rw [energyVir_cons]; omega
      rw [hrw] at h
      exact h

/-- **The graded sorting lemma.**  The `n`-th graded piece of `VirUniv c` is spanned by the
creation monomials indexed by *sorted* words of energy `n` — i.e. by the partitions of `n` into
parts `≥ 2`. -/
theorem gradingVir_eq_sortedSpanVir (n : ℕ) : gradingVir c (n : ℤ) = sortedSpanVir c n := by
  apply le_antisymm
  · rw [gradingVir, Submodule.span_le]
    rintro x ⟨ws, hen, rfl⟩
    have hen' : energyVir ws = n := by exact_mod_cast hen
    rw [← hen']
    exact negWordVir_mem_sortedSpanVir c ws
  · rw [sortedSpanVir, Submodule.span_le]
    rintro x ⟨u, -, hen, rfl⟩
    exact Submodule.subset_span ⟨u, by exact_mod_cast hen, rfl⟩

/-! ## §5  Fock-space preliminaries: creation modes past creation operators. -/

section FockPrelim

open VOA
open MvPolynomial (X)

/-- `a₋ₖ₋₁ p = X_k · p` on the free-boson Fock space. -/
theorem osc_creation (k : ℕ) (p : Fock) : osc 1 (-(k : ℤ) - 1) p = X k * p := by
  have hk : (-(-(k : ℤ) - 1) - 1).toNat = k := by omega
  rw [osc_apply_neg 1 (by omega) p, hk]

/-- `L₋₁|0⟩ = 0` on `Fock`. -/
theorem Lvir_one_vacuum : Lvir 1 (-1) (1 : Fock) = 0 := Lvir_vacuum 1 (by norm_num)

/-- `a₋₁ p = X₀ · p`. -/
theorem osc_m1_apply (p : Fock) : osc 1 (-1) p = X 0 * p := by
  rw [osc_apply_neg 1 (by norm_num) p]; norm_num

/-- **Moving a creation mode past a creation operator**:
`L₋ₙ₋₁(Xᵢ · y) = (i+1)·X_{i+n+1}·y + Xᵢ·L₋ₙ₋₁ y`, directly from `Lvir_osc`. -/
theorem Lvir_neg_X (n i : ℕ) (y : Fock) :
    Lvir 1 (-(n : ℤ) - 1) (X i * y)
      = ((i : ℂ) + 1) • (X (i + n + 1) * y) + X i * Lvir 1 (-(n : ℤ) - 1) y := by
  have h := Lvir_osc 1 one_ne_zero (-(n : ℤ) - 1) (-(i : ℤ) - 1) y
  rw [show (-(n : ℤ) - 1) + (-(i : ℤ) - 1) = -((i + n + 1 : ℕ) : ℤ) - 1 from by push_cast; ring,
    osc_creation i y, osc_creation (i + n + 1) y, osc_creation i (Lvir 1 (-(n : ℤ) - 1) y),
    show (-((-(i : ℤ) - 1 : ℤ) : ℂ)) = (i : ℂ) + 1 from by push_cast; ring] at h
  exact h

/-- `L₋₁` on a quadratic: `L₋₁(X_a X_b) = (a+1)X_{a+1}X_b + (b+1)X_a X_{b+1}`. -/
theorem Lvir_one_XX (a b : ℕ) :
    Lvir 1 (-1) ((X a : Fock) * X b)
      = ((a : ℂ) + 1) • ((X (a + 1) : Fock) * X b) + ((b : ℂ) + 1) • ((X a : Fock) * X (b + 1)) := by
  have hb : Lvir 1 (-1) (X b : Fock) = ((b : ℂ) + 1) • (X (b + 1) : Fock) := by
    have h := Lvir_neg_X 0 b (1 : Fock)
    norm_num at h
    rw [h, Lvir_one_vacuum, mul_zero, add_zero]
  have h := Lvir_neg_X 0 a (X b : Fock)
  norm_num at h
  rw [h, hb, mul_smul_comm]

/-- The **Virasoro relation on `Fock`** at `k = 1` (the `λ = 0` case of `Lld_virasoro`). -/
theorem Lvir_virasoro (m n : ℤ) :
    Lvir 1 m * Lvir 1 n - Lvir 1 n * Lvir 1 m
      = ((m : ℂ) - n) • Lvir 1 (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * (1 - 12 * (0 : ℂ) ^ 2) else 0)
            • (LinearMap.id : Module.End ℂ Fock) := by
  have hz : ∀ j : ℤ, Lld 0 j = Lvir 1 j := by
    intro j; rw [Lld, zero_mul, zero_smul, add_zero]
  have h := Lld_virasoro 0 m n
  rw [hz, hz, hz] at h
  exact h

/-- The applied form of `[L₋₁, L₋ᵢ₋₂] = (i+1)L₋ᵢ₋₃` on `Fock`. -/
theorem Lvir_one_step (i : ℕ) (p : Fock) :
    Lvir 1 (-1) (Lvir 1 (-(i : ℤ) - 2) p)
      = Lvir 1 (-(i : ℤ) - 2) (Lvir 1 (-1) p) + ((i : ℂ) + 1) • Lvir 1 (-(i : ℤ) - 3) p := by
  have h := congrArg (fun T : Module.End ℂ Fock => T p) (Lvir_virasoro (-1) (-(i : ℤ) - 2))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [if_neg (by omega : ¬((-1 : ℤ) + (-(i : ℤ) - 2) = 0)), zero_smul, add_zero,
    show (-1 : ℤ) + (-(i : ℤ) - 2) = -(i : ℤ) - 3 from by ring,
    show ((-1 : ℤ) : ℂ) - ((-(i : ℤ) - 2 : ℤ) : ℂ) = (i : ℂ) + 1 from by push_cast; ring] at h
  rw [eq_add_of_sub_eq h]
  abel

/-! ### The creation quadratic `Pₙ` and its identification with `L₋ₙ|0⟩`. -/

/-- The **creation quadratic** `P_{i+2} := ½ ∑_{a+b=i} X_a X_b`.  It is the top-degree symbol of
the creation mode `L₋ᵢ₋₂` (Lemma `Lvir_creation_vacuum`: `P_{i+2} = L₋ᵢ₋₂|0⟩` exactly). -/
noncomputable def creationPoly (i : ℕ) : Fock :=
  (2⁻¹ : ℂ) • ∑ p ∈ Finset.range (i + 1), (X p : Fock) * X (i - p)

/-- The first creation quadratic is one half of the square of the first bosonic variable. It represents the conformal state created by L minus two. -/
theorem creationPoly_zero : creationPoly 0 = (2⁻¹ : ℂ) • ((X 0 : Fock) * X 0) := by
  rw [creationPoly, Finset.sum_range_one]

/-- **`L₋₁` raises the creation quadratic**: `L₋₁ P_{i+2} = (i+1) P_{i+3}`.  Symmetrising the two
Leibniz terms over the antidiagonal turns `∑ (a+1)X_{a+1}X_b + (b+1)X_aX_{b+1}` into
`∑_{a+b=i+1}(a + b)X_aX_b = (i+1)∑_{a+b=i+1}X_aX_b`. -/
theorem Lvir_one_creationPoly (i : ℕ) :
    Lvir 1 (-1) (creationPoly i) = ((i : ℂ) + 1) • creationPoly (i + 1) := by
  have step : ∀ p ∈ Finset.range (i + 1), Lvir 1 (-1) ((X p : Fock) * X (i - p))
      = ((p : ℂ) + 1) • ((X (p + 1) : Fock) * X (i + 1 - (p + 1)))
        + (((i - p : ℕ) : ℂ) + 1) • ((X p : Fock) * X (i + 1 - p)) := by
    intro p hp
    rw [Finset.mem_range] at hp
    have h1 : i + 1 - (p + 1) = i - p := by omega
    have h2 : i - p + 1 = i + 1 - p := by omega
    rw [h1, ← h2, Lvir_one_XX]
  have hA : ∑ p ∈ Finset.range (i + 1),
        ((p : ℂ) + 1) • ((X (p + 1) : Fock) * X (i + 1 - (p + 1)))
      = ∑ q ∈ Finset.range (i + 2), (q : ℂ) • ((X q : Fock) * X (i + 1 - q)) := by
    rw [Finset.sum_range_succ' (fun q => (q : ℂ) • ((X q : Fock) * X (i + 1 - q))) (i + 1)]
    simp only [Nat.cast_zero, zero_smul, add_zero, Nat.cast_add, Nat.cast_one]
  have hB : ∑ p ∈ Finset.range (i + 1),
        (((i - p : ℕ) : ℂ) + 1) • ((X p : Fock) * X (i + 1 - p))
      = ∑ q ∈ Finset.range (i + 2), (((i + 1 - q : ℕ) : ℂ)) • ((X q : Fock) * X (i + 1 - q)) := by
    rw [Finset.sum_range_succ (fun q => (((i + 1 - q : ℕ) : ℂ)) • ((X q : Fock) * X (i + 1 - q)))
      (i + 1)]
    rw [show i + 1 - (i + 1) = 0 from by omega, Nat.cast_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_range] at hp
    rw [show ((i + 1 - p : ℕ) : ℂ) = ((i - p : ℕ) : ℂ) + 1 from by
      have : i + 1 - p = (i - p) + 1 := by omega
      rw [this]; push_cast; ring]
  rw [creationPoly, map_smul, map_sum, Finset.sum_congr rfl step, Finset.sum_add_distrib,
    hA, hB, ← Finset.sum_add_distrib]
  have hmerge : ∑ q ∈ Finset.range (i + 2),
        ((q : ℂ) • ((X q : Fock) * X (i + 1 - q))
          + (((i + 1 - q : ℕ) : ℂ)) • ((X q : Fock) * X (i + 1 - q)))
      = ((i : ℂ) + 1) • ∑ q ∈ Finset.range (i + 2), ((X q : Fock) * X (i + 1 - q)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mem_range] at hq
    rw [← add_smul]
    congr 1
    have : (q : ℕ) + (i + 1 - q) = i + 1 := by omega
    have hc := congrArg (fun m : ℕ => (m : ℂ)) this
    push_cast at hc
    exact hc
  rw [hmerge, creationPoly, smul_comm]

/-- **The creation quadratic is exactly the descendant**: `L₋ᵢ₋₂|0⟩ = P_{i+2}`.  Induction on `i`
from `L₋₂|0⟩ = ½X₀²` using `[L₋₁, L₋ᵢ₋₂] = (i+1)L₋ᵢ₋₃`. -/
theorem Lvir_creation_vacuum (i : ℕ) : Lvir 1 (-(i : ℤ) - 2) (1 : Fock) = creationPoly i := by
  induction i with
  | zero =>
      have h : Lvir 1 (-2) (vacuum : Fock) = VOA.ω 1 := Lvir_neg_two_vacuum 1
      rw [show (vacuum : Fock) = 1 from rfl] at h
      simp only [Nat.cast_zero, neg_zero, zero_sub]
      rw [h, VOA.ω, osc_m1_apply, osc_m1_apply,
        show (vacuum : Fock) = 1 from rfl, mul_one, creationPoly_zero]
      norm_num
  | succ i ih =>
      have hstep := Lvir_one_step i (1 : Fock)
      rw [Lvir_one_vacuum, map_zero, zero_add, ih, Lvir_one_creationPoly] at hstep
      have hne : ((i : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero i
      rw [show -((i + 1 : ℕ) : ℤ) - 2 = -(i : ℤ) - 3 from by push_cast; ring]
      exact (smul_right_injective Fock hne hstep).symm

/-! ## §7  The polynomial-degree filtration on `Fock`. -/

/-- `FDeg d` — the `ℂ`-span of the products of at most `d` variables.  A hand-rolled degree
filtration: the only fact we need from it is `FDeg_totalDegree` (`p ∈ FDeg d ⟹ deg p ≤ d`), and
unlike `totalDegree` it is a *submodule*, so it is stable under the sums that appear in the
straightening induction (no cancellation bookkeeping). -/
noncomputable def FDeg (d : ℕ) : Submodule ℂ Fock :=
  Submodule.span ℂ {p : Fock | ∃ l : List ℕ, l.length ≤ d ∧ p = (l.map X).prod}

/-- Allowing more polynomial variables in each spanning monomial enlarges the filtration. A degree bound can therefore always be weakened. -/
theorem FDeg_mono {d e : ℕ} (h : d ≤ e) : FDeg d ≤ FDeg e :=
  Submodule.span_mono (by rintro p ⟨l, hl, rfl⟩; exact ⟨l, le_trans hl h, rfl⟩)

/-- A product of k bosonic variables belongs to filtration level k by the defining spanning set, including repeated variables. -/
theorem prod_mem_FDeg (l : List ℕ) : ((l.map X).prod : Fock) ∈ FDeg l.length :=
  Submodule.subset_span ⟨l, le_rfl, rfl⟩

/-- The constant polynomial 1 is the product of zero variables, so it belongs to every nonnegative filtration level. -/
theorem one_mem_FDeg (d : ℕ) : (1 : Fock) ∈ FDeg d := by
  have h := prod_mem_FDeg ([] : List ℕ)
  simp only [List.map_nil, List.prod_nil, List.length_nil] at h
  exact FDeg_mono (Nat.zero_le d) h

/-- `FDeg` is stable under multiplication by a variable, at the cost of one degree. -/
theorem mulX_mem_FDeg (i : ℕ) {d : ℕ} {p : Fock} (hp : p ∈ FDeg d) :
    (X i : Fock) * p ∈ FDeg (d + 1) := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      refine Submodule.subset_span ⟨i :: l, by simpa using hl, ?_⟩
      rw [List.map_cons, List.prod_cons]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha

/-- The ordinary total degree of a product of variables is bounded by the number of factors. This converts the hand-built spanning filtration into a standard polynomial degree estimate. -/
theorem totalDegree_prod_X (l : List ℕ) : ((l.map X).prod : Fock).totalDegree ≤ l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons]
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_X]
      omega

/-- The only property of `FDeg` we use downstream: it bounds the total degree. -/
theorem FDeg_totalDegree {d : ℕ} {p : Fock} (hp : p ∈ FDeg d) : p.totalDegree ≤ d := by
  induction hp using Submodule.span_induction with
  | mem y hy => obtain ⟨l, hl, rfl⟩ := hy; exact le_trans (totalDegree_prod_X l) hl
  | zero => simp
  | add a b _ _ ha hb => exact le_trans (MvPolynomial.totalDegree_add a b) (max_le ha hb)
  | smul r a _ ha => exact le_trans (MvPolynomial.totalDegree_smul_le r a) ha

/-- Multiplication by the creation quadratic costs exactly two degrees. -/
theorem creationPoly_mul_mem (i : ℕ) {d : ℕ} {p : Fock} (hp : p ∈ FDeg d) :
    creationPoly i * p ∈ FDeg (d + 2) := by
  rw [creationPoly, smul_mul_assoc, Finset.sum_mul]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun q _ => ?_))
  rw [mul_assoc]
  exact mulX_mem_FDeg q (mulX_mem_FDeg (i - q) hp)

/-! ## §8  The top-degree symbol of a creation word. -/

/-- The image in `Fock` of the creation monomial `negWordVir c ws`, under the linear-dilaton
realisation at background charge `lam`. -/
noncomputable def fockWordVir (lam : ℂ) : List ℕ → Fock
  | [] => 1
  | i :: ws => Lld lam (-(i : ℤ) - 2) (fockWordVir lam ws)

/-- Applying no Virasoro creation modes to the bosonic vacuum leaves the constant polynomial 1. -/
@[simp] theorem fockWordVir_nil (lam : ℂ) : fockWordVir lam [] = 1 := rfl

/-- A nonempty Fock word applies its first creation mode to the state represented by the remaining word. This exposes the recursive operator action. -/
theorem fockWordVir_cons (lam : ℂ) (i : ℕ) (ws : List ℕ) :
    fockWordVir lam (i :: ws) = Lld lam (-(i : ℤ) - 2) (fockWordVir lam ws) := rfl

/-- The **top-degree symbol** of a creation word: the product of the creation quadratics.  It is
`lam`-free — hence central-charge-free — which is exactly why degenerate central charges cannot
spoil the argument. -/
noncomputable def creationProd : List ℕ → Fock
  | [] => 1
  | i :: ws => creationPoly i * creationProd ws

/-- The leading polynomial symbol of the empty creation word is the empty product, hence 1. -/
@[simp] theorem creationProd_nil : creationProd [] = 1 := rfl

/-- The leading symbol of a word factors into the quadratic symbol of its first creation mode and the symbol of the remaining word. -/
theorem creationProd_cons (i : ℕ) (ws : List ℕ) :
    creationProd (i :: ws) = creationPoly i * creationProd ws := rfl

/-- `a₋ᵢ₋₂ p = X_{i+1}·p`, the extra background-charge term of `Lld`. -/
theorem osc_creation_two (i : ℕ) (p : Fock) :
    osc 1 (-(i : ℤ) - 2) p = X (i + 1) * p := by
  have h := osc_creation (i + 1) p
  rw [show (-((i + 1 : ℕ) : ℤ) - 1) = -(i : ℤ) - 2 from by push_cast; ring] at h
  exact h

/-- `L₋ᵢ₋₂^λ = Pᵢ₊₂·(−) + (degree-raising by at most one)`, on a product of variables. -/
theorem errLd_prod_mem (lam : ℂ) (i : ℕ) (l : List ℕ) :
    Lld lam (-(i : ℤ) - 2) ((l.map X).prod : Fock) - creationPoly i * (l.map X).prod
      ∈ FDeg (l.length + 1) := by
  have hLld : ∀ p : Fock, Lld lam (-(i : ℤ) - 2) p
      = Lvir 1 (-(i : ℤ) - 2) p + (lam * ((-(i : ℤ) - 2 : ℤ) : ℂ) + lam) • (X (i + 1) * p) := by
    intro p
    rw [Lld, LinearMap.add_apply, LinearMap.smul_apply, osc_creation_two]
    ring_nf
  induction l with
  | nil =>
      rw [List.map_nil, List.prod_nil, hLld, Lvir_creation_vacuum, mul_one, mul_one]
      have hz : creationPoly i + (lam * ((-(i : ℤ) - 2 : ℤ) : ℂ) + lam) • (X (i + 1) : Fock)
          - creationPoly i = (lam * ((-(i : ℤ) - 2 : ℤ) : ℂ) + lam) • (X (i + 1) : Fock) := by
        ring
      rw [hz]
      refine Submodule.smul_mem _ _ ?_
      have hx := mulX_mem_FDeg (i + 1) (one_mem_FDeg 0)
      rwa [mul_one] at hx
  | cons j l ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons]
      have hmove : Lvir 1 (-(i : ℤ) - 2) ((X j : Fock) * (l.map X).prod)
          = ((j : ℂ) + 1) • ((X (j + i + 2) : Fock) * (l.map X).prod)
            + X j * Lvir 1 (-(i : ℤ) - 2) (l.map X).prod := by
        have h := Lvir_neg_X (i + 1) j ((l.map X).prod : Fock)
        rw [show (-((i + 1 : ℕ) : ℤ) - 1) = -(i : ℤ) - 2 from by push_cast; ring,
          show j + (i + 1) + 1 = j + i + 2 from by omega] at h
        exact h
      have hsplit : Lld lam (-(i : ℤ) - 2) ((X j : Fock) * (l.map X).prod)
            - creationPoly i * ((X j : Fock) * (l.map X).prod)
          = ((j : ℂ) + 1) • ((X (j + i + 2) : Fock) * (l.map X).prod)
            + (lam * ((-(i : ℤ) - 2 : ℤ) : ℂ) + lam)
                • ((X (i + 1) : Fock) * ((X j : Fock) * (l.map X).prod))
            + X j * (Lvir 1 (-(i : ℤ) - 2) ((l.map X).prod : Fock)
                - creationPoly i * (l.map X).prod) := by
        rw [hLld, hmove]
        ring
      rw [hsplit]
      have hIH : Lvir 1 (-(i : ℤ) - 2) ((l.map X).prod : Fock) - creationPoly i * (l.map X).prod
          ∈ FDeg (l.length + 1) := by
        have h2 := ih
        rw [hLld] at h2
        have hrw : Lvir 1 (-(i : ℤ) - 2) ((l.map X).prod : Fock)
              - creationPoly i * (l.map X).prod
            = (Lvir 1 (-(i : ℤ) - 2) ((l.map X).prod : Fock)
                + (lam * ((-(i : ℤ) - 2 : ℤ) : ℂ) + lam) • (X (i + 1) * (l.map X).prod)
                - creationPoly i * (l.map X).prod)
              - (lam * ((-(i : ℤ) - 2 : ℤ) : ℂ) + lam) • (X (i + 1) * (l.map X).prod) := by
          ring
        rw [hrw]
        exact Submodule.sub_mem _ h2
          (Submodule.smul_mem _ _ (mulX_mem_FDeg (i + 1) (prod_mem_FDeg l)))
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.smul_mem _ _
          (FDeg_mono (by omega) (mulX_mem_FDeg (j + i + 2) (prod_mem_FDeg l)))
      · exact Submodule.smul_mem _ _
          (mulX_mem_FDeg (i + 1) (mulX_mem_FDeg j (prod_mem_FDeg l)))
      · exact mulX_mem_FDeg j hIH

/-- The degree split, on all of `FDeg d`. -/
theorem errLd_mem (lam : ℂ) (i : ℕ) {d : ℕ} {p : Fock} (hp : p ∈ FDeg d) :
    Lld lam (-(i : ℤ) - 2) p - creationPoly i * p ∈ FDeg (d + 1) := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      exact FDeg_mono (by omega) (errLd_prod_mem lam i l)
  | zero => rw [map_zero, mul_zero, sub_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
      have hs : Lld lam (-(i : ℤ) - 2) (a + b) - creationPoly i * (a + b)
          = (Lld lam (-(i : ℤ) - 2) a - creationPoly i * a)
            + (Lld lam (-(i : ℤ) - 2) b - creationPoly i * b) := by
        rw [map_add, mul_add]; ring
      rw [hs]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
      have hs : Lld lam (-(i : ℤ) - 2) (r • a) - creationPoly i * (r • a)
          = r • (Lld lam (-(i : ℤ) - 2) a - creationPoly i * a) := by
        rw [map_smul, mul_smul_comm]; module
      rw [hs]; exact Submodule.smul_mem _ r ha

/-- A creation mode raises the filtration bound by two. This is an upper
bound on degree; it does not assert that every input attains that degree. -/
theorem Lld_mem_FDeg (lam : ℂ) (i : ℕ) {d : ℕ} {p : Fock} (hp : p ∈ FDeg d) :
    Lld lam (-(i : ℤ) - 2) p ∈ FDeg (d + 2) := by
  have hs : Lld lam (-(i : ℤ) - 2) p
      = (Lld lam (-(i : ℤ) - 2) p - creationPoly i * p) + creationPoly i * p := by ring
  rw [hs]
  exact Submodule.add_mem _ (FDeg_mono (by omega) (errLd_mem lam i hp))
    (creationPoly_mul_mem i hp)

/-- A word of k Virasoro creation modes acting on the bosonic vacuum has polynomial degree at most 2k. Each mode raises the filtration bound by two; this estimate holds for every background charge. -/
theorem fockWordVir_mem_FDeg (lam : ℂ) (ws : List ℕ) :
    fockWordVir lam ws ∈ FDeg (2 * ws.length) := by
  induction ws with
  | nil => simp only [fockWordVir_nil, List.length_nil, Nat.mul_zero]; exact one_mem_FDeg 0
  | cons i rest ih =>
      rw [fockWordVir_cons, List.length_cons]
      exact FDeg_mono (by omega) (Lld_mem_FDeg lam i ih)

/-- The product of k quadratic creation symbols lies in filtration level 2k. This is the degree scale used to compare actual Fock states with their leading symbols. -/
theorem creationProd_mem_FDeg (ws : List ℕ) : creationProd ws ∈ FDeg (2 * ws.length) := by
  induction ws with
  | nil => simp only [creationProd_nil, List.length_nil, Nat.mul_zero]; exact one_mem_FDeg 0
  | cons i rest ih =>
      rw [creationProd_cons, List.length_cons]
      exact FDeg_mono (by omega) (creationPoly_mul_mem i ih)

/-- **The top-degree symbol.**  `fockWordVir lam ws` and the `lam`-free product
`creationProd ws = ∏ P_{iⱼ+2}` differ by something of strictly smaller polynomial degree. -/
theorem fockWordVir_sub_creationProd (lam : ℂ) (ws : List ℕ) :
    fockWordVir lam ws - creationProd ws ∈ FDeg (2 * ws.length - 1) := by
  induction ws with
  | nil => simp only [fockWordVir_nil, creationProd_nil, sub_self]; exact Submodule.zero_mem _
  | cons i rest ih =>
      rw [fockWordVir_cons, creationProd_cons, List.length_cons]
      have hE := errLd_mem lam i (fockWordVir_mem_FDeg lam rest)
      have hsplit : Lld lam (-(i : ℤ) - 2) (fockWordVir lam rest)
            - creationPoly i * creationProd rest
          = (Lld lam (-(i : ℤ) - 2) (fockWordVir lam rest)
              - creationPoly i * fockWordVir lam rest)
            + creationPoly i * (fockWordVir lam rest - creationProd rest) := by ring
      rw [hsplit]
      refine Submodule.add_mem _ (FDeg_mono (by omega) hE) ?_
      rcases Nat.eq_zero_or_pos rest.length with h0 | hpos
      · have hnil : rest = [] := by
          cases rest with
          | nil => rfl
          | cons a b => simp at h0
        subst hnil
        simp only [fockWordVir_nil, creationProd_nil, sub_self, mul_zero]
        exact Submodule.zero_mem _
      · exact FDeg_mono (by omega) (creationPoly_mul_mem i ih)

/-! ## §9  Separating the top symbols: a one-variable specialisation. -/

/-- The homogeneity of the creation quadratic: `P_{i+2}` is a quadratic form in the oscillators. -/
theorem creationPoly_isHomogeneous (i : ℕ) : (creationPoly i).IsHomogeneous 2 := by
  have hmem : creationPoly i ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ 2 := by
    rw [creationPoly]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun q _ => ?_))
    rw [MvPolynomial.mem_homogeneousSubmodule]
    simpa using (MvPolynomial.isHomogeneous_X ℂ q).mul (MvPolynomial.isHomogeneous_X ℂ (i - q))
  rwa [MvPolynomial.mem_homogeneousSubmodule] at hmem

/-- The leading-symbol product for a creation word is homogeneous of total degree twice the word length. Thus its entire contribution lies at one degree, separating it from the lower-degree correction to the actual Fock state. -/
theorem creationProd_isHomogeneous (ws : List ℕ) :
    (creationProd ws).IsHomogeneous (2 * ws.length) := by
  induction ws with
  | nil =>
      simp only [creationProd_nil, List.length_nil, Nat.mul_zero]
      exact MvPolynomial.isHomogeneous_one ℕ ℂ
  | cons i rest ih =>
      rw [creationProd_cons, List.length_cons]
      have h := (creationPoly_isHomogeneous i).mul ih
      rwa [show 2 + 2 * rest.length = 2 * (rest.length + 1) from by omega] at h

/-- The **one-variable specialisation** `X_p ↦ t^{Bᵖ}`.  Base-`B` exponents are super-increasing,
so the `t`-degree of a product of creation quadratics reads off the partition. -/
noncomputable def tSub (B : ℕ) : Fock →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun p : ℕ => (Polynomial.X : Polynomial ℂ) ^ (B ^ p))

/-- Specializing the Fock variables to powers of one variable turns the quadratic creation symbol into a sum of monomials. Their exponents record the two indices in each quadratic term. -/
theorem tSub_creationPoly_eq (B i : ℕ) :
    tSub B (creationPoly i)
      = (2⁻¹ : ℂ) • ∑ q ∈ Finset.range (i + 1),
          (Polynomial.X : Polynomial ℂ) ^ (B ^ q + B ^ (i - q)) := by
  rw [creationPoly, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_mul, tSub, MvPolynomial.aeval_X, MvPolynomial.aeval_X, ← pow_add]

/-- For two positive natural numbers, their sum is bounded by their product plus one. Applied to powers of the substitution base, this locates the largest exponent in a creation symbol. -/
theorem add_le_mul_add_one {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) : x + y ≤ x * y + 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = b + 1 := ⟨y - 1, by omega⟩
  nlinarith

/-- The exponent `B^q + B^{i-q}` is maximised at the endpoints of the antidiagonal. -/
theorem exponent_le (B i q : ℕ) (hB : 2 ≤ B) (hq : q ≤ i) : B ^ q + B ^ (i - q) ≤ B ^ i + 1 := by
  have hmul : B ^ q * B ^ (i - q) = B ^ i := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ B ^ q := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ B ^ (i - q) := Nat.one_le_pow _ _ (by omega)
  calc B ^ q + B ^ (i - q) ≤ B ^ q * B ^ (i - q) + 1 := add_le_mul_add_one h1 h2
    _ = B ^ i + 1 := by rw [hmul]

/-- The proposed highest coefficient of the specialized creation symbol is nonzero: an endpoint term contributes, and all contributions have the same positive coefficient, so cancellation cannot occur. -/
theorem coeff_tSub_creationPoly (B i : ℕ) (_hB : 2 ≤ B) :
    (tSub B (creationPoly i)).coeff (B ^ i + 1) ≠ 0 := by
  classical
  rw [tSub_creationPoly_eq, Polynomial.coeff_smul, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow, smul_eq_mul]
  rw [Finset.sum_boole]
  have hmem : (0 : ℕ) ∈ Finset.filter
      (fun q => B ^ i + 1 = B ^ q + B ^ (i - q)) (Finset.range (i + 1)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_zero, pow_zero]
    omega
  have hcard : (Finset.filter (fun q => B ^ i + 1 = B ^ q + B ^ (i - q))
      (Finset.range (i + 1))).card ≠ 0 := by
    intro h
    rw [Finset.card_eq_zero] at h
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty 0)
  intro hzero
  rcases mul_eq_zero.mp hzero with h | h
  · norm_num at h
  · exact hcard (by exact_mod_cast h)

/-- The specialized creation symbol has degree exactly B^i+1. The exponent estimate supplies the upper bound, and its nonzero coefficient supplies the lower bound. -/
theorem natDegree_tSub_creationPoly (B i : ℕ) (hB : 2 ≤ B) :
    (tSub B (creationPoly i)).natDegree = B ^ i + 1 := by
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero (coeff_tSub_creationPoly B i hB))
  rw [tSub_creationPoly_eq]
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun q hq => ?_⟩
  rw [Finset.mem_range] at hq
  rw [Function.comp_apply, Polynomial.natDegree_X_pow]
  exact exponent_le B i q hB (by omega)

/-- Every specialized creation symbol is a nonzero polynomial, because the coefficient at its established highest exponent survives. -/
theorem tSub_creationPoly_ne_zero (B i : ℕ) (hB : 2 ≤ B) : tSub B (creationPoly i) ≠ 0 := by
  intro h
  exact coeff_tSub_creationPoly B i hB (by rw [h, Polynomial.coeff_zero])

/-- The base-`B` value of a word: `∑ⱼ B^{iⱼ}`. -/
def wordVal (B : ℕ) (ws : List ℕ) : ℕ := (ws.map (fun i => B ^ i)).sum

/-- The empty word contributes no base-B place values, so its encoded value is zero. -/
@[simp] theorem wordVal_nil (B : ℕ) : wordVal B [] = 0 := rfl

/-- Prepending index i adds the place value B^i to the encoded value of the remaining word. -/
theorem wordVal_cons (B : ℕ) (i : ℕ) (ws : List ℕ) :
    wordVal B (i :: ws) = B ^ i + wordVal B ws := rfl

/-- Products of specialized creation symbols remain nonzero. This uses the absence of zero divisors in the polynomial ring, rather than independence of the original Virasoro words. -/
theorem tSub_creationProd_ne_zero (B : ℕ) (hB : 2 ≤ B) (ws : List ℕ) :
    tSub B (creationProd ws) ≠ 0 := by
  induction ws with
  | nil => rw [creationProd_nil, map_one]; exact one_ne_zero
  | cons i rest ih =>
      rw [creationProd_cons, map_mul]
      exact mul_ne_zero (tSub_creationPoly_ne_zero B i hB) ih

/-- The degree of a specialized product is the word length plus its base-B value. Each creation symbol contributes one extra unit in addition to its encoded index; nonvanishing permits adding the degrees. -/
theorem natDegree_tSub_creationProd (B : ℕ) (hB : 2 ≤ B) (ws : List ℕ) :
    (tSub B (creationProd ws)).natDegree = ws.length + wordVal B ws := by
  induction ws with
  | nil => rw [creationProd_nil, map_one, Polynomial.natDegree_one]; rfl
  | cons i rest ih =>
      rw [creationProd_cons, map_mul,
        Polynomial.natDegree_mul (tSub_creationPoly_ne_zero B i hB)
          (tSub_creationProd_ne_zero B hB rest),
        natDegree_tSub_creationPoly B i hB, ih, List.length_cons, wordVal_cons]
      omega

/-! ## §10  Base-`B` separation of sorted words. -/

/-- If every index in a word is at most m, each encoded term is bounded by B^m. Summing gives a bound by the word length times B^m, used to separate the largest index from smaller ones. -/
theorem wordVal_le (B m : ℕ) (hB : 2 ≤ B) :
    ∀ ws : List ℕ, (∀ x ∈ ws, x ≤ m) → wordVal B ws ≤ ws.length * B ^ m := by
  intro ws
  induction ws with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      have h1 : B ^ a ≤ B ^ m :=
        Nat.pow_le_pow_right (by omega) (h a (List.mem_cons_self ..))
      have h2 : wordVal B l ≤ l.length * B ^ m :=
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rw [wordVal_cons, List.length_cons, add_mul, one_mul]
      omega

/-- A strictly larger head strictly dominates the whole base-`B` value, as long as the base
exceeds the length. -/
theorem wordVal_head_lt (B K : ℕ) (hB : 2 ≤ B) (hKB : K < B) {a b : ℕ} {u' v' : List ℕ}
    (hv : SortedWord (b :: v')) (hlv : (b :: v').length ≤ K) (hlt : b < a) :
    wordVal B (b :: v') < wordVal B (a :: u') := by
  have hall : ∀ x ∈ (b :: v'), x ≤ b := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_rfl
    · exact hv.head_ge x hx'
  have hbound := wordVal_le B b hB (b :: v') hall
  have h1 : (b :: v').length * B ^ b ≤ K * B ^ b := Nat.mul_le_mul_right _ hlv
  have hpos : 0 < B ^ b := pow_pos (show 0 < B by omega) _
  have h2 : K * B ^ b < B ^ (b + 1) := by
    rw [pow_succ, mul_comm (B ^ b) B]
    exact (Nat.mul_lt_mul_right hpos).mpr hKB
  have h3 : B ^ (b + 1) ≤ B ^ a := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : B ^ a ≤ wordVal B (a :: u') := by rw [wordVal_cons]; omega
  omega

/-- **Base-`B` separation.**  Distinct sorted words of length at most `K < B` have distinct
base-`B` values.  (The head is determined first — a bigger head dominates the entire rest of the
word — and then one strips it and recurses.) -/
theorem wordVal_inj (B K : ℕ) (hB : 2 ≤ B) (hKB : K < B) :
    ∀ u v : List ℕ, SortedWord u → SortedWord v → u.length ≤ K → v.length ≤ K →
      wordVal B u = wordVal B v → u = v := by
  intro u
  induction u with
  | nil =>
      intro v _ _ _ _ h
      cases v with
      | nil => rfl
      | cons b v' =>
          exfalso
          rw [wordVal_nil, wordVal_cons] at h
          have : 0 < B ^ b := pow_pos (show 0 < B by omega) _
          omega
  | cons a u' ih =>
      intro v hu hv hlu hlv h
      cases v with
      | nil =>
          exfalso
          rw [wordVal_nil, wordVal_cons] at h
          have : 0 < B ^ a := pow_pos (show 0 < B by omega) _
          omega
      | cons b v' =>
          have hab : a = b := by
            rcases lt_trichotomy a b with hlt | heq | hgt
            · exact absurd h (Nat.ne_of_lt (wordVal_head_lt B K hB hKB hu hlu hlt))
            · exact heq
            · exact absurd h.symm (Nat.ne_of_lt (wordVal_head_lt B K hB hKB hv hlv hgt))
          subst hab
          have h' : wordVal B u' = wordVal B v' := by
            rw [wordVal_cons, wordVal_cons] at h; omega
          have hlu' : u'.length ≤ K := by rw [List.length_cons] at hlu; omega
          have hlv' : v'.length ≤ K := by rw [List.length_cons] at hlv; omega
          rw [ih v' hu.tail hv.tail hlu' hlv' h']

/-! ## §11  A finite family with pairwise distinct degrees is independent. -/

/-- If a finite family of nonzero polynomials has pairwise distinct `natDegree`s, then a vanishing
linear combination has all coefficients zero. -/
theorem coef_eq_zero_of_natDegree_inj {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial ℂ) (coef : ι → ℂ)
    (hne : ∀ i ∈ s, f i ≠ 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (f i).natDegree = (f j).natDegree → i = j)
    (hsum : ∑ i ∈ s, coef i • f i = 0) : ∀ i ∈ s, coef i = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁s, hi₁⟩ := hcon
  obtain ⟨i₀, hi₀T, hmax⟩ :=
    (s.filter (fun i => coef i ≠ 0)).exists_max_image (fun i => (f i).natDegree)
      ⟨i₁, Finset.mem_filter.mpr ⟨hi₁s, hi₁⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀T).1
  have hc₀ : coef i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
  have hco := congrArg (fun p : Polynomial ℂ => p.coeff (f i₀).natDegree) hsum
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_zero] at hco
  rw [Finset.sum_eq_single i₀] at hco
  · refine absurd hco (mul_ne_zero hc₀ ?_)
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (hne i₀ hi₀s)
  · intro b hb hbne
    by_cases hcb : coef b = 0
    · rw [hcb, zero_mul]
    · have hle := hmax b (Finset.mem_filter.mpr ⟨hb, hcb⟩)
      have hlt : (f b).natDegree < (f i₀).natDegree :=
        lt_of_le_of_ne hle (fun heq => hbne (hinj b hb i₀ hi₀s heq))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  · intro h; exact absurd hi₀s h

/-! ## §12  Transfer of relations from `VirUniv c` to `Fock`. -/

open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra

/-- The creation word as an element of `U(𝔙𝔦𝔯)`. -/
noncomputable def uWord : List ℕ → UVir
  | [] => 1
  | i :: ws => ι ℂ (L (-(i : ℤ) - 2)) * uWord ws

/-- The empty creation word is the identity in the universal enveloping algebra, so applying it leaves the vacuum unchanged. -/
@[simp] theorem uWord_nil : uWord [] = 1 := rfl

/-- Prepending a creation index multiplies the enveloping-algebra word on the left by its negative Virasoro generator. -/
theorem uWord_cons (i : ℕ) (ws : List ℕ) :
    uWord (i :: ws) = ι ℂ (L (-(i : ℤ) - 2)) * uWord ws := rfl

/-- A creation monomial in the universal vacuum module is the quotient class of its enveloping-algebra word. This connects concrete mode expressions to the quotient construction. -/
theorem negWordVir_eq_mk (c : ℂ) (ws : List ℕ) :
    negWordVir c ws = Submodule.Quotient.mk (uWord ws) := by
  induction ws with
  | nil => rfl
  | cons i rest ih => rw [negWordVir_cons, ih]; rfl

/-- The vacuum ideal `J(c)` is annihilated at the free-boson vacuum. -/
theorem evAlg_kills_vacIdeal {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) {w : UVir}
    (hw : w ∈ vacIdeal c) : evAlg lam w vacuum = 0 := by
  induction hw using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨n, hn, rfl⟩ | rfl
      · rw [evAlg, lift_ι_apply, linDilRho_L]; exact Lld_vacuum lam hn
      · rw [evAlg, map_sub, lift_ι_apply, linDilRho_C, AlgHom.commutes,
          Algebra.algebraMap_eq_smul_one, hlam, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.smul_apply, LinearMap.id_apply, Module.End.one_apply, sub_self]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul r a _ ha =>
      rw [show (r • a : UVir) = r * a from rfl, map_mul, Module.End.mul_apply, ha, map_zero]

/-- The free-boson representation sends left multiplication by a Virasoro generator to the corresponding operator acting on the image state. This is the representation law used to transfer creation words. -/
theorem evAlg_L_mul (lam : ℂ) (n : ℤ) (a : UVir) :
    evAlg lam (ι ℂ (L n) * a) vacuum = Lld lam n (evAlg lam a vacuum) := by
  rw [map_mul, Module.End.mul_apply, evAlg, lift_ι_apply, linDilRho_L]

/-- Evaluating an enveloping-algebra creation word on the free-boson vacuum gives exactly the recursively defined Fock creation word, with no change of normalization. -/
theorem evAlg_uWord (lam : ℂ) (ws : List ℕ) :
    evAlg lam (uWord ws) vacuum = fockWordVir lam ws := by
  induction ws with
  | nil => rw [uWord_nil, map_one, Module.End.one_apply, fockWordVir_nil]; rfl
  | cons i rest ih => rw [uWord_cons, evAlg_L_mul, ih, fockWordVir_cons]

/-- A finite linear combination of vacuum creation words is the quotient class of the same combination of enveloping-algebra words. This lets a vacuum-module relation be studied before applying the Fock representation. -/
theorem mk_sum (c : ℂ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ) :
    ∑ w ∈ s, coef w • negWordVir c w
      = Submodule.Quotient.mk (∑ w ∈ s, coef w • uWord w) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, negWordVir_eq_mk]
      rfl

/-- **The transfer.**  A vanishing `ℂ`-linear combination of creation monomials in `VirUniv c`
becomes a vanishing linear combination of their free-boson images, for any background charge
`lam` with `1 - 12 lam² = c`. -/
theorem fock_transfer {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) (s : Finset (List ℕ))
    (coef : List ℕ → ℂ) (h : ∑ w ∈ s, coef w • negWordVir c w = 0) :
    ∑ w ∈ s, coef w • fockWordVir lam w = 0 := by
  have hmem : (∑ w ∈ s, coef w • uWord w) ∈ vacIdeal c := by
    rw [← Submodule.Quotient.mk_eq_zero, ← mk_sum]
    exact h
  have h0 := evAlg_kills_vacIdeal hlam hmem
  rw [map_sum, LinearMap.sum_apply] at h0
  have hrw : ∑ w ∈ s, coef w • fockWordVir lam w
      = ∑ w ∈ s, evAlg lam (coef w • uWord w) vacuum := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [map_smul, LinearMap.smul_apply, evAlg_uWord]
  rw [hrw, h0]

/-! ## §13  Independence of the sorted creation words. -/

/-- **The top-level step.**  Among words of length exactly `K`, the top-degree symbols
`∏ⱼ P_{iⱼ+2}` have pairwise distinct `t`-degrees under the base-`(K+2)` specialisation, so their
coefficients must vanish. -/
theorem topLength_coef_zero (lam : ℂ) (K : ℕ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hsort : ∀ w ∈ s, SortedWord w) (hlen : ∀ w ∈ s, w.length ≤ K)
    (hsum : ∑ w ∈ s, coef w • fockWordVir lam w = 0) :
    ∀ w ∈ s, w.length = K → coef w = 0 := by
  classical
  have hA : ∀ w ∈ s.filter (fun w => w.length = K),
      coef w • MvPolynomial.homogeneousComponent (2 * K) (fockWordVir lam w)
        = coef w • creationProd w := by
    intro w hw
    obtain ⟨-, hwK⟩ := Finset.mem_filter.mp hw
    have hsplit : fockWordVir lam w
        = creationProd w + (fockWordVir lam w - creationProd w) := by ring
    have hhom : MvPolynomial.homogeneousComponent (2 * K) (creationProd w) = creationProd w := by
      have hmem : creationProd w ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ (2 * w.length) :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (creationProd_isHomogeneous w)
      rw [MvPolynomial.homogeneousComponent_of_mem hmem, if_pos (by rw [hwK])]
    have hzero : MvPolynomial.homogeneousComponent (2 * K)
        (fockWordVir lam w - creationProd w) = 0 := by
      rcases eq_or_ne w [] with rfl | hne
      · simp only [fockWordVir_nil, creationProd_nil, sub_self, map_zero]
      · refine MvPolynomial.homogeneousComponent_eq_zero _ _ ?_
        have hdeg := FDeg_totalDegree (fockWordVir_sub_creationProd lam w)
        have hpos : 0 < w.length := List.length_pos_iff.mpr hne
        omega
    rw [hsplit, map_add, hhom, hzero, add_zero]
  have hB : ∀ w ∈ s.filter (fun w => ¬ (w.length = K)),
      coef w • MvPolynomial.homogeneousComponent (2 * K) (fockWordVir lam w) = 0 := by
    intro w hw
    obtain ⟨hws, hwK⟩ := Finset.mem_filter.mp hw
    have hlt : w.length < K := lt_of_le_of_ne (hlen w hws) hwK
    have hdeg := FDeg_totalDegree (fockWordVir_mem_FDeg lam w)
    rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), smul_zero]
  have hproj : ∑ w ∈ s.filter (fun w => w.length = K), coef w • creationProd w = 0 := by
    have h := congrArg (MvPolynomial.homogeneousComponent (2 * K)) hsum
    rw [map_sum, map_zero] at h
    simp only [map_smul] at h
    rw [← Finset.sum_filter_add_sum_filter_not s (fun w => w.length = K)] at h
    rw [Finset.sum_eq_zero hB, add_zero, Finset.sum_congr rfl hA] at h
    exact h
  have hproj2 : ∑ w ∈ s.filter (fun w => w.length = K),
      coef w • tSub (K + 2) (creationProd w) = 0 := by
    have h := congrArg (tSub (K + 2)) hproj
    rw [map_sum, map_zero] at h
    rw [← h]
    exact (Finset.sum_congr rfl (fun w _ => by rw [map_smul])).symm
  intro w hw hwlen
  refine coef_eq_zero_of_natDegree_inj (s.filter (fun w => w.length = K))
    (fun w => tSub (K + 2) (creationProd w)) coef ?_ ?_ hproj2 w
    (Finset.mem_filter.mpr ⟨hw, hwlen⟩)
  · intro u _; exact tSub_creationProd_ne_zero (K + 2) (by omega) u
  · intro u hu v hv hdeg
    obtain ⟨hus, huK⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvs, hvK⟩ := Finset.mem_filter.mp hv
    rw [natDegree_tSub_creationProd _ (by omega), natDegree_tSub_creationProd _ (by omega),
      huK, hvK] at hdeg
    exact wordVal_inj (K + 2) K (by omega) (by omega) u v (hsort u hus) (hsort v hvs)
      (by omega) (by omega) (by omega)

/-- **Independence of the Fock images of the sorted creation words.**  Free-field independence at
*every* central charge: the top-degree symbol `∏ⱼ P_{iⱼ+2}` is `lam`-free, so degenerate central
charges (the minimal models) cannot spoil it. -/
theorem fockWordVir_coef_zero (lam : ℂ) :
    ∀ (K : ℕ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ),
      (∀ w ∈ s, SortedWord w) → (∀ w ∈ s, w.length ≤ K) →
      (∑ w ∈ s, coef w • fockWordVir lam w = 0) → ∀ w ∈ s, coef w = 0 := by
  classical
  intro K
  induction K with
  | zero =>
      intro s coef hsort hlen hsum w hw
      exact topLength_coef_zero lam 0 s coef hsort hlen hsum w hw (by
        have := hlen w hw; omega)
  | succ K ih =>
      intro s coef hsort hlen hsum w hw
      have htop := topLength_coef_zero lam (K + 1) s coef hsort hlen hsum
      by_cases hwK : w.length = K + 1
      · exact htop w hw hwK
      · set s' := s.filter (fun w => ¬ (w.length = K + 1)) with hs'
        have hzero : ∑ u ∈ s.filter (fun u => u.length = K + 1),
            coef u • fockWordVir lam u = 0 := by
          refine Finset.sum_eq_zero (fun u hu => ?_)
          obtain ⟨hus, huK⟩ := Finset.mem_filter.mp hu
          rw [htop u hus huK, zero_smul]
        have hsum' : ∑ u ∈ s', coef u • fockWordVir lam u = 0 := by
          rw [← Finset.sum_filter_add_sum_filter_not s (fun u => u.length = K + 1),
            hzero, zero_add] at hsum
          exact hsum
        refine ih s' coef (fun u hu => hsort u (Finset.mem_filter.mp hu).1) (fun u hu => ?_)
          hsum' w (Finset.mem_filter.mpr ⟨hw, hwK⟩)
        obtain ⟨hus, huK⟩ := Finset.mem_filter.mp hu
        have := hlen u hus
        omega

/-! ## §14  Independence in `VirUniv c`, and the partition-indexed graded basis. -/

/-- **The sorted creation monomials of `VirUniv c` are linearly independent**, at every central
charge `c`.  (`pbw`-free: proved through the linear-dilaton free boson, whose top-degree symbol is
background-charge-free.) -/
theorem negWordVir_coef_zero (c : ℂ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hsort : ∀ w ∈ s, SortedWord w)
    (hsum : ∑ w ∈ s, coef w • negWordVir c w = 0) : ∀ w ∈ s, coef w = 0 := by
  obtain ⟨lam, hlam⟩ := exists_lam c
  rcases s.eq_empty_or_nonempty with rfl | hne
  · intro w hw; exact absurd hw (Finset.notMem_empty w)
  · obtain ⟨w₀, -, hK⟩ := s.exists_max_image (fun w => w.length) hne
    exact fockWordVir_coef_zero lam w₀.length s coef hsort hK
      (fock_transfer hlam s coef hsum)

/-- The same, transported along any injective indexing by sorted words. -/
theorem negWordVir_coef_zero' {ι : Type*} (v : ι → List ℕ) (hinj : Function.Injective v)
    (hsortv : ∀ i, SortedWord (v i)) (c : ℂ) (s : Finset ι) (g : ι → ℂ)
    (hsum : ∑ i ∈ s, g i • negWordVir c (v i) = 0) : ∀ i ∈ s, g i = 0 := by
  classical
  have hcv : ∀ i, (Function.extend v g 0) (v i) = g i :=
    fun i => hinj.extend_apply g 0 i
  have hsum' : ∑ l ∈ s.image v, (Function.extend v g 0) l • negWordVir c l = 0 := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [hcv]
    exact hsum
  have hs : ∀ l ∈ s.image v, SortedWord l := by
    intro l hl
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
    exact hsortv j
  intro i hi
  have h := negWordVir_coef_zero c (s.image v) (Function.extend v g 0) hs hsum' (v i)
    (Finset.mem_image_of_mem v hi)
  rwa [hcv i] at h

/-- **The index type of the graded basis**: sorted words of energy `n`.  Since the entry `i`
denotes the mode `L₋ᵢ₋₂`, this is exactly the set of **partitions of `n` into parts `≥ 2`**. -/
def SortedOfEnergy (n : ℕ) : Type := {w : List ℕ // SortedWord w ∧ energyVir w = n}

/-- Equality of partition indices is decided by equality of their underlying finite lists. The proofs of sortedness and energy add no extra data. -/
instance (n : ℕ) : DecidableEq (SortedOfEnergy n) := Subtype.instDecidableEq

/-- There are finitely many sorted words of fixed energy: every entry contributes at least two to that energy. This equips the partition index set with the finite enumeration required for Gram matrices and determinants. -/
noncomputable instance sortedOfEnergyFintype (n : ℕ) : Fintype (SortedOfEnergy n) := by
  have h : {w : List ℕ | SortedWord w ∧ energyVir w = n}.Finite :=
    (finite_energyEq n).subset (fun w hw => hw.2)
  exact h.fintype

/-- The partition-indexed family inside the `n`-th graded piece. -/
noncomputable def gradedWord (c : ℂ) (n : ℕ) (w : SortedOfEnergy n) : gradingVir c (n : ℤ) :=
  ⟨negWordVir c w.1, by
    rw [gradingVir_eq_sortedSpanVir]
    exact negWordVir_mem_sortedSpanVir_of_sorted c w.2.1 w.2.2⟩

/-- Forgetting the proof that a partition word has weight n leaves precisely its original creation monomial in the universal module. -/
theorem gradedWord_val (c : ℂ) (n : ℕ) (w : SortedOfEnergy n) :
    ((gradedWord c n w : gradingVir c (n : ℤ)) : VirUniv c) = negWordVir c w.1 := rfl

/-- The partition words remain linearly independent when viewed inside their homogeneous component. A relation there is also a relation in the universal module, where the Fock-space argument already forces every coefficient to vanish. -/
theorem gradedWord_linearIndependent (c : ℂ) (n : ℕ) :
    LinearIndependent ℂ (gradedWord c n) := by
  refine LinearIndependent.of_comp (gradingVir c (n : ℤ)).subtype ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi
  refine negWordVir_coef_zero' (fun w : SortedOfEnergy n => w.1) Subtype.val_injective
    (fun w => w.2.1) c s g ?_ i hi
  have : ∑ j ∈ s, g j • negWordVir c (j : SortedOfEnergy n).1
      = ∑ j ∈ s, g j • ((gradingVir c (n : ℤ)).subtype ∘ gradedWord c n) j := rfl
  rw [this, hsum]

/-- The partition words span their entire homogeneous component. Straightening supplies the underlying spanning theorem; this proof expresses it inside the weight-space subtype. -/
theorem gradedWord_span (c : ℂ) (n : ℕ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (gradedWord c n)) := by
  have hinj : Function.Injective (gradingVir c (n : ℤ)).subtype := Subtype.val_injective
  have hmap : Submodule.map (gradingVir c (n : ℤ)).subtype
        (Submodule.span ℂ (Set.range (gradedWord c n)))
      = Submodule.map (gradingVir c (n : ℤ)).subtype ⊤ := by
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    have hset : Set.range ((gradingVir c (n : ℤ)).subtype ∘ gradedWord c n)
        = {x | ∃ u : List ℕ, SortedWord u ∧ energyVir u = n ∧ negWordVir c u = x} := by
      ext x
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨w.1, w.2.1, w.2.2, rfl⟩
      · rintro ⟨u, hu, hen, rfl⟩; exact ⟨⟨u, hu, hen⟩, rfl⟩
    rw [hset, ← sortedSpanVir, ← gradingVir_eq_sortedSpanVir]
  have := Submodule.map_injective_of_injective hinj hmap
  rw [this]

/-- **The partition-indexed graded basis of `V(c,0)`.**  For every central charge `c` and every
level `n`, the `n`-th graded piece `gradingVir c n` has a basis indexed by the sorted words of
energy `n` — that is, by the **partitions of `n` into parts `≥ 2`** — with basis vector
`L₋ᵢ₁₋₂ ⋯ L₋ᵢₖ₋₂ |0⟩`.  This is the object the Kac determinant is a determinant *of*. -/
noncomputable def gradedBasis (c : ℂ) (n : ℕ) : Module.Basis (SortedOfEnergy n) ℂ
    (gradingVir c (n : ℤ)) :=
  Module.Basis.mk (gradedWord_linearIndependent c n) (gradedWord_span c n)

/-- Evaluating the constructed partition basis at a partition gives the corresponding creation word itself. There is no hidden change of basis in the basis constructor. -/
@[simp] theorem gradedBasis_apply (c : ℂ) (n : ℕ) (w : SortedOfEnergy n) :
    gradedBasis c n w = gradedWord c n w := Module.Basis.mk_apply _ _ w

/-- **The graded dimension of `V(c,0)`**: `dim 𝒱ₙ` is the number of partitions of `n` into parts
`≥ 2`, at every central charge. -/
theorem finrank_gradingVir (c : ℂ) (n : ℕ) :
    Module.finrank ℂ (gradingVir c (n : ℤ)) = Fintype.card (SortedOfEnergy n) :=
  Module.finrank_eq_card_basis (gradedBasis c n)

/-! ## §15  The dimension count at low levels.

Sorted words of energy `n` are the partitions of `n` into parts `≥ 2` (entry `i` ↔ part `i+2`):

| `n` | partitions into parts `≥ 2` | sorted words | count |
|---|---|---|---|
| 2 | `2` | `[0]` | 1 |
| 3 | `3` | `[1]` | 1 |
| 4 | `4`, `2+2` | `[2]`, `[0,0]` | 2 |
| 5 | `5`, `3+2` | `[3]`, `[1,0]` | 2 |
| 6 | `6`, `4+2`, `3+3`, `2+2+2` | `[4]`, `[2,0]`, `[1,1]`, `[0,0,0]` | 4 |
-/

/-- An explicit finite list of all sorted words at a level computes the size of the abstract partition index set. The equivalence sends each partition to the same underlying word. -/
theorem card_sortedOfEnergy_of_eq {n : ℕ} (F : Finset (List ℕ))
    (h : ∀ w : List ℕ, (SortedWord w ∧ energyVir w = n) ↔ w ∈ F) :
    Fintype.card (SortedOfEnergy n) = F.card := by
  have e : SortedOfEnergy n ≃ {x // x ∈ F} :=
    ⟨fun w => ⟨w.1, (h w.1).mp w.2⟩, fun x => ⟨x.1, (h x.1).mpr x.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e, Fintype.card_coe]

/-- At energy two the only partition is 2, encoded by the index word [0]. Thus the universal weight-two space is generated by the conformal state. -/
theorem sortedOfEnergy_two_iff (w : List ℕ) :
    (SortedWord w ∧ energyVir w = 2) ↔ w ∈ ({[0]} : Finset (List ℕ)) := by
  constructor
  · rintro ⟨hs, he⟩
    have hlen : 2 * w.length ≤ 2 := by
      have hml := two_mul_length_le_energy w
      omega
    match w with
    | [] => simp only [energyVir_nil] at he; omega
    | [a] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have : a = 0 := by omega
        subst this; decide
    | (a :: b :: t) => simp only [List.length_cons] at hlen; omega
  · intro hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    exact ⟨by decide, rfl⟩

/-- At energy three the only allowed partition is 3, encoded by [1]. Parts of size one are excluded because the translation mode kills the vacuum. -/
theorem sortedOfEnergy_three_iff (w : List ℕ) :
    (SortedWord w ∧ energyVir w = 3) ↔ w ∈ ({[1]} : Finset (List ℕ)) := by
  constructor
  · rintro ⟨hs, he⟩
    have hlen : 2 * w.length ≤ 3 := by
      have hml := two_mul_length_le_energy w
      omega
    match w with
    | [] => simp only [energyVir_nil] at he; omega
    | [a] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have : a = 1 := by omega
        subst this; decide
    | (a :: b :: t) => simp only [List.length_cons] at hlen; omega
  · intro hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    exact ⟨by decide, rfl⟩

/-- Energy four has precisely the partitions 4 and 2+2, encoded by [2] and [0,0]. These are the two states in the level-four Gram matrix. -/
theorem sortedOfEnergy_four_iff (w : List ℕ) :
    (SortedWord w ∧ energyVir w = 4) ↔ w ∈ ({[2], [0, 0]} : Finset (List ℕ)) := by
  constructor
  · rintro ⟨hs, he⟩
    have hlen : 2 * w.length ≤ 4 := by
      have hml := two_mul_length_le_energy w
      omega
    match w with
    | [] => simp only [energyVir_nil] at he; omega
    | [a] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have : a = 2 := by omega
        subst this; decide
    | [a, b] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb; decide
    | (a :: b :: c :: t) => simp only [List.length_cons] at hlen; omega
  · intro hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩

/-- Energy five has precisely the partitions 5 and 3+2, encoded by [3] and [1,0]. Sorting removes the alternative ordering of the two-mode word. -/
theorem sortedOfEnergy_five_iff (w : List ℕ) :
    (SortedWord w ∧ energyVir w = 5) ↔ w ∈ ({[3], [1, 0]} : Finset (List ℕ)) := by
  constructor
  · rintro ⟨hs, he⟩
    have hlen : 2 * w.length ≤ 5 := by
      have hml := two_mul_length_le_energy w
      omega
    match w with
    | [] => simp only [energyVir_nil] at he; omega
    | [a] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have : a = 3 := by omega
        subst this; decide
    | [a, b] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have hab : a ≥ b := hs.head_ge b (by simp)
        have ha : a = 1 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb; decide
    | (a :: b :: c :: t) => simp only [List.length_cons] at hlen; omega
  · intro hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩

/-- Energy six has precisely the partitions 6, 4+2, 3+3 and 2+2+2. Their index words [4], [2,0], [1,1] and [0,0,0] enumerate the four basis states used for the Ising and M(2,7) Gram calculation. -/
theorem sortedOfEnergy_six_iff (w : List ℕ) :
    (SortedWord w ∧ energyVir w = 6) ↔ w ∈ ({[4], [2, 0], [1, 1], [0, 0, 0]} : Finset (List ℕ)) := by
  constructor
  · rintro ⟨hs, he⟩
    have hlen : 2 * w.length ≤ 6 := by
      have hml := two_mul_length_le_energy w
      omega
    match w with
    | [] => simp only [energyVir_nil] at he; omega
    | [a] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have : a = 4 := by omega
        subst this; decide
    | [a, b] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have hab : a ≥ b := hs.head_ge b (by simp)
        have : (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by omega
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · decide
        · decide
    | [a, b, c] =>
        simp only [energyVir_cons, energyVir_nil] at he
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        have hc : c = 0 := by omega
        subst ha; subst hb; subst hc; decide
    | (a :: b :: c :: d :: t) => simp only [List.length_cons] at hlen; omega
  · intro hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩

/-- `dim 𝒱₂ = 1` — the partition `2`. -/
theorem finrank_gradingVir_two (c : ℂ) : Module.finrank ℂ (gradingVir c 2) = 1 := by
  have h : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir c 2, card_sortedOfEnergy_of_eq _ sortedOfEnergy_two_iff]
  rfl

/-- `dim 𝒱₃ = 1` — the partition `3`. -/
theorem finrank_gradingVir_three (c : ℂ) : Module.finrank ℂ (gradingVir c 3) = 1 := by
  have h : ((3 : ℕ) : ℤ) = (3 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir c 3, card_sortedOfEnergy_of_eq _ sortedOfEnergy_three_iff]
  rfl

/-- `dim 𝒱₄ = 2` — the partitions `4` and `2+2`; matches `LeeYangSingular.level4_indep`. -/
theorem finrank_gradingVir_four (c : ℂ) : Module.finrank ℂ (gradingVir c 4) = 2 := by
  have h : ((4 : ℕ) : ℤ) = (4 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir c 4, card_sortedOfEnergy_of_eq _ sortedOfEnergy_four_iff]
  rfl

/-- `dim 𝒱₅ = 2` — the partitions `5` and `3+2`. -/
theorem finrank_gradingVir_five (c : ℂ) : Module.finrank ℂ (gradingVir c 5) = 2 := by
  have h : ((5 : ℕ) : ℤ) = (5 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir c 5, card_sortedOfEnergy_of_eq _ sortedOfEnergy_five_iff]
  rfl

/-- `dim 𝒱₆ = 4` — the partitions `6`, `4+2`, `3+3`, `2+2+2`.  This is the first level beyond the
reach of brute enumeration: the four *unsorted* index words `[4], [2,0], [0,2], [0,0,0]` name only
three independent vectors before straightening. -/
theorem finrank_gradingVir_six (c : ℂ) : Module.finrank ℂ (gradingVir c 6) = 4 := by
  have h : ((6 : ℕ) : ℤ) = (6 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir c 6, card_sortedOfEnergy_of_eq _ sortedOfEnergy_six_iff]
  rfl

/-! ## §16  Corollaries. -/

/-- Every sorted creation monomial is **nonzero**, at every central charge.  In particular
`L₋ₙ|0⟩ ≠ 0` for all `n ≥ 2`, `pbw`-free. -/
theorem negWordVir_ne_zero (c : ℂ) {w : List ℕ} (hw : SortedWord w) : negWordVir c w ≠ 0 := by
  classical
  intro hzero
  have hsum : ∑ u ∈ ({w} : Finset (List ℕ)), (1 : ℂ) • negWordVir c u = 0 := by
    rw [Finset.sum_singleton, one_smul, hzero]
  have := negWordVir_coef_zero c {w} (fun _ => 1) (by
    intro u hu; rw [Finset.mem_singleton] at hu; subst hu; exact hw) hsum w
    (Finset.mem_singleton_self w)
  exact one_ne_zero this

/-- **Global linear independence** of the partition-indexed creation monomials. -/
theorem sortedWord_linearIndependent (c : ℂ) :
    LinearIndependent ℂ (fun w : {w : List ℕ // SortedWord w} => negWordVir c w.1) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  exact negWordVir_coef_zero' (fun w : {w : List ℕ // SortedWord w} => w.1)
    Subtype.val_injective (fun w => w.2) c s g hsum i hi

/-- The **level-6 graded piece**, explicitly: the analogue of `LeeYangSingular.gradingVir_four`
one level past the reach of brute enumeration.  The four *unsorted* words of energy `6` are
`[4], [2,0], [0,2], [0,0,0]`, one too many; straightening `[0,2]` via `negWordVir_swap` leaves the
four sorted words below, and `finrank_gradingVir_six` says they are a basis. -/
theorem gradingVir_six_span (c : ℂ) :
    gradingVir c 6 = Submodule.span ℂ
      {negWordVir c [4], negWordVir c [2, 0], negWordVir c [1, 1], negWordVir c [0, 0, 0]} := by
  have h : ((6 : ℕ) : ℤ) = (6 : ℤ) := by norm_num
  rw [← h, gradingVir_eq_sortedSpanVir, sortedSpanVir]
  congr 1
  ext x
  constructor
  · rintro ⟨u, hu, hen, rfl⟩
    have hmem := (sortedOfEnergy_six_iff u).mp ⟨hu, hen⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  · intro hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨[4], by decide, rfl, rfl⟩
    · exact ⟨[2, 0], by decide, rfl, rfl⟩
    · exact ⟨[1, 1], by decide, rfl, rfl⟩
    · exact ⟨[0, 0, 0], by decide, rfl, rfl⟩

end FockPrelim

end VOA.VirModule
