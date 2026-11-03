/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroPartitionBasis

/-!
# The top symbol of a Virasoro creation word, and the Feigin–Fuchs embedding of `V(c,0)`

`Examples/VirasoroPartitionBasis` proves that the sorted creation monomials
`L₋ᵢ₁₋₂ ⋯ L₋ᵢₖ₋₂ |0⟩` are linearly independent in the universal Virasoro vacuum module
`V(c,0) = VirUniv c`, at every central charge, and assembles them into the partition-indexed
graded basis `gradedBasis`.  The engine of that proof is the **top-degree symbol** of the
linear-dilaton free-boson realisation

  `Lₙ^λ = Lₙ^{Sug} + λ(n+1)aₙ` on `Fock = ℂ[X₀,X₁,…]`,   central charge `c = 1 − 12λ²`,

but the symbol itself is used there only inside one proof and is never stated.  This file
states it, and draws the two consequences that the statement — rather than the proof — makes
available.

## The three-piece split, verified against the repository

For `n = i+2 ≥ 2` the creation mode splits, on the oscillator-degree filtration, as

  `L₋ₙ^λ  =  mult(Pₙ)  [degree +2]  +  Dₙ  [degree 0]  +  λ(1−n)·mult(X_{n−1})  [degree +1]`,

with `Pₙ = ½ ∑_{p+q=n−2} X_p X_q`.  Against the repository: `Lld lam m = Lvir 1 m + λ(m+1)·osc 1 m`
(`Examples/VirasoroFock`), so at `m = −n` the background-charge term is `λ(1−n)·a₋ₙ`, and
`osc 1 (−n) = mult(X_{n−1})` (`osc_creation_two`); the quadratic is `creationPoly i` with
`i = n−2`, and `Lvir_creation_vacuum` identifies `Pₙ = L₋ₙ|0⟩` on the nose.  **The route-finder's
normalisation is exactly the repository's**; no discrepancy.

## Main results

* `topSymbol_fockWordVir` — **the top symbol.**  For every word `ws` of length `k` and every
  background charge `λ`, the degree-`2k` homogeneous component of the Fock image of
  `L₋ᵢ₁₋₂ ⋯ L₋ᵢₖ₋₂|0⟩` is exactly `∏ⱼ P_{iⱼ+2}` — an identity with **no `λ` in it**, hence no
  central charge.  Everything below `2k` is where `λ` hides.
* `topSymbol_fockWordVir_indep`, `topSymbol_evAlg` — the same statement as an independence-of-`λ`
  assertion, and transported to `U(𝔙𝔦𝔯)` acting on the Fock vacuum.
* `sortedWords`, `mem_sortedWords` — a **computable** enumeration of the index set of the
  partition basis: `sortedWords n : Finset (List ℕ)` is the set of partitions of `n` into parts
  `≥ 2`, written as weakly decreasing lists of `part − 2`.
* `finrank_gradingVir_eq_card` — hence `dim 𝒱ₙ = (sortedWords n).card`, a number a **kernel
  computation** produces at every `n`, replacing the hand-written level-by-level enumerations.
  `card_sortedWords_le_eight` records `n = 0,…,8 ↦ 1, 0, 1, 1, 2, 2, 4, 4, 7`, and
  `finrank_gradingVir_seven/eight/twelve/sixteen` read `4, 7, 21, 55` off as dimensions.
* `sortedBasisVir` — the *global* partition basis of `V(c,0)` (all levels at once); the graded
  pieces are `gradedBasis`.
* `fockWordVir_linearIndependent` — the free-field shadow: the Fock images of the sorted words are
  independent, for every background charge.
* `evAlg_vacuum_eq_zero_iff` — **the Feigin–Fuchs embedding.**  The annihilator of the Fock
  vacuum in `U(𝔙𝔦𝔯)` is *exactly* the vacuum ideal `J(c)`:
  `evAlg λ a |0⟩ = 0 ↔ a ∈ J(c)`.  Equivalently `V(c,0) ↪ Fock`, at **every** central charge —
  including the degenerate minimal-model charges such as `c = −22/5`.
* `fockMap`, `fockMap_injective` — the same, bundled as an injective `ℂ`-linear map
  `V(c,0) →ₗ[ℂ] Fock`.

The last item is worth isolating because it is easy to expect the opposite.  A Feigin–Fuchs
*screening* map `Q : Fock → Fock` does have a kernel at degenerate `c` — that is the whole content
of the Felder complex, where `L(c,0) = ker Q / im Q` and the singular vector is a nonzero element
of `im Q`.  But the map out of the **universal** module `V(c,0)` is injective for every `c`: the
top symbol that separates the creation words is `λ`-free, so there is no charge at which it can
degenerate.  Degeneracy at the minimal models lives in the passage `V(c,0) ↠ L(c,0)`, which this
file never performs.

## Status

`sorry`-free, axiom-clean, **`pbw`-free**: the theorem `VOA.pbw`
is not used here and is not needed.  Nothing in this file re-proves anything in
`Examples/VirasoroPartitionBasis`; the independence theorem is imported.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open MvPolynomial (X)

/-! ## §1  The exact top symbol of a creation word. -/

section TopSymbol

/-- A creation word of length `k` has oscillator degree at most `2k`: each of the `k` creation
modes contributes at most a quadratic. -/
theorem totalDegree_fockWordVir_le (lam : ℂ) (ws : List ℕ) :
    (fockWordVir lam ws).totalDegree ≤ 2 * ws.length :=
  FDeg_totalDegree (fockWordVir_mem_FDeg lam ws)

/-- The `λ`-dependent part of a nonempty creation word has *strictly* smaller oscillator degree
than the word itself. -/
theorem totalDegree_fockWordVir_sub_lt {lam : ℂ} {ws : List ℕ} (hws : ws ≠ []) :
    (fockWordVir lam ws - creationProd ws).totalDegree < 2 * ws.length := by
  have hdeg := FDeg_totalDegree (fockWordVir_sub_creationProd lam ws)
  have hpos : 0 < ws.length := List.length_pos_iff.mpr hws
  omega

/-- **The top symbol.**  For a creation word `ws = [i₁,…,i_k]`, the degree-`2k` homogeneous
component of its linear-dilaton Fock image is exactly the product of creation quadratics

  `∏ⱼ P_{iⱼ+2}`,   `P_{i+2} = ½ ∑_{p+q=i} X_p X_q`.

The right-hand side contains **no `λ`**, hence no central charge: the `λ`-dependence of
`L₋ᵢ₋₂^λ = mult(P_{i+2}) + D_{i+2} + λ(−i−1)·mult(X_{i+1})` sits entirely in the two lower-degree
branches, and applying `k` modes to `|0⟩` the degree-`2k` part must take the `mult(P)` branch every
single time.  Those branches are multiplications, so they commute, which is what turns the
statement into a one-line induction on `k` (packaged upstream as
`fockWordVir_sub_creationProd`). -/
theorem topSymbol_fockWordVir (lam : ℂ) (ws : List ℕ) :
    MvPolynomial.homogeneousComponent (2 * ws.length) (fockWordVir lam ws) = creationProd ws := by
  have hsplit : fockWordVir lam ws
      = creationProd ws + (fockWordVir lam ws - creationProd ws) := by ring
  have hhom : MvPolynomial.homogeneousComponent (2 * ws.length) (creationProd ws)
      = creationProd ws := by
    have hmem : creationProd ws ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ (2 * ws.length) :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (creationProd_isHomogeneous ws)
    rw [MvPolynomial.homogeneousComponent_of_mem hmem, if_pos rfl]
  have hzero : MvPolynomial.homogeneousComponent (2 * ws.length)
      (fockWordVir lam ws - creationProd ws) = 0 := by
    rcases eq_or_ne ws [] with rfl | hne
    · simp only [fockWordVir_nil, creationProd_nil, sub_self, map_zero]
    · exact MvPolynomial.homogeneousComponent_eq_zero _ _ (totalDegree_fockWordVir_sub_lt hne)
  rw [hsplit, map_add, hhom, hzero, add_zero]

/-- **The top symbol does not see the background charge**, hence does not see the central charge
`c = 1 − 12λ²`.  This is the precise sense in which the degenerate (minimal-model) values of `c`
cannot degrade the independence argument. -/
theorem topSymbol_fockWordVir_indep (lam mu : ℂ) (ws : List ℕ) :
    MvPolynomial.homogeneousComponent (2 * ws.length) (fockWordVir lam ws)
      = MvPolynomial.homogeneousComponent (2 * ws.length) (fockWordVir mu ws) := by
  rw [topSymbol_fockWordVir, topSymbol_fockWordVir]

/-- Above the top degree there is nothing: the Fock image of a length-`k` word has no homogeneous
component in degree `> 2k`. -/
theorem homogeneousComponent_fockWordVir_eq_zero (lam : ℂ) (ws : List ℕ) {d : ℕ}
    (hd : 2 * ws.length < d) :
    MvPolynomial.homogeneousComponent d (fockWordVir lam ws) = 0 :=
  MvPolynomial.homogeneousComponent_eq_zero _ _
    (lt_of_le_of_lt (totalDegree_fockWordVir_le lam ws) hd)

/-- The top symbol, stated for the `U(𝔙𝔦𝔯)`-action on the Fock vacuum: the degree-`2k` part of
`(L₋ᵢ₁₋₂ ⋯ L₋ᵢₖ₋₂)·|0⟩` is `∏ⱼ P_{iⱼ+2}`. -/
theorem topSymbol_evAlg (lam : ℂ) (ws : List ℕ) :
    MvPolynomial.homogeneousComponent (2 * ws.length) (evAlg lam (uWord ws) vacuum)
      = creationProd ws := by
  rw [evAlg_uWord, topSymbol_fockWordVir]

end TopSymbol

/-! ## §2  The index set of the partition basis, computably.

`SortedOfEnergy n` — the sorted words of energy `n`, equivalently the partitions of `n` into parts
`≥ 2` — is the index type of `gradedBasis`, and `finrank_gradingVir` computes `dim 𝒱ₙ` as its
cardinality.  But that type carries a `Fintype` instance extracted from a `Set.Finite` proof, which
no kernel computation can evaluate, so each level had to be enumerated by hand.

This section replaces the hand enumeration by a genuinely computable one.  `sortedAux f b n`
recurses **structurally on a fuel parameter** (well-founded recursion on `n` would not reduce in
the kernel, which is the whole point), peeling off the head `i` of a weakly decreasing word: the
head may be anything with `i ≤ b` and `i + 2 ≤ n`, and the tail is a word of energy `n − i − 2`
whose entries are bounded by `i`.  Fuel `n` is always enough because each mode eats at least `2`.
-/

section Enumeration

/-- Each entry of a word is bounded by its energy: the entry `x` denotes the mode `L₋ₓ₋₂`, which
alone contributes `x + 2`. -/
theorem energyVir_ge_of_mem {x : ℕ} {w : List ℕ} (hx : x ∈ w) : x + 2 ≤ energyVir w := by
  induction w with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons i rest ih =>
      rw [energyVir_cons]
      rcases List.mem_cons.mp hx with rfl | h
      · omega
      · have := ih h; omega

/-- `sortedAux f b n` — with fuel `f`, the weakly decreasing lists of naturals of energy `n` all of
whose entries are `≤ b`.  Structural recursion on the fuel, so the kernel can evaluate it. -/
def sortedAux : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, _, n => if n = 0 then {[]} else ∅
  | f + 1, b, n =>
      if n = 0 then {[]}
      else (Finset.filter (fun i => i + 2 ≤ n) (Finset.range (b + 1))).biUnion
        (fun i => (sortedAux f i (n - i - 2)).image (fun w => i :: w))

/-- Unfolding `sortedAux` at zero fuel. -/
theorem sortedAux_zero (b n : ℕ) : sortedAux 0 b n = if n = 0 then {[]} else ∅ := rfl

/-- Unfolding `sortedAux` at positive fuel: peel off the head of the word. -/
theorem sortedAux_succ (f b n : ℕ) :
    sortedAux (f + 1) b n =
      if n = 0 then {[]}
      else (Finset.filter (fun i => i + 2 ≤ n) (Finset.range (b + 1))).biUnion
        (fun i => (sortedAux f i (n - i - 2)).image (fun w => i :: w)) := rfl

/-- **`sortedAux` is correct**, provided the fuel `f` covers the energy (`n ≤ 2f + 1`, which holds
since every mode eats at least `2`): its members are exactly the sorted words of energy `n` with
all entries `≤ b`. -/
theorem mem_sortedAux : ∀ (f b n : ℕ), n ≤ 2 * f + 1 → ∀ w : List ℕ,
    (w ∈ sortedAux f b n ↔ SortedWord w ∧ energyVir w = n ∧ ∀ x ∈ w, x ≤ b) := by
  intro f
  induction f with
  | zero =>
      intro b n hn w
      rw [sortedAux_zero]
      by_cases h0 : n = 0
      · subst h0
        rw [if_pos rfl, Finset.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨sortedWord_nil, rfl, by simp⟩
        · rintro ⟨-, he, -⟩
          exact (energyVir_eq_zero_iff w).mp he
      · rw [if_neg h0]
        constructor
        · intro h; exact absurd h (Finset.notMem_empty w)
        · rintro ⟨-, he, -⟩
          exfalso
          cases w with
          | nil => rw [energyVir_nil] at he; omega
          | cons a t => rw [energyVir_cons] at he; omega
  | succ f ih =>
      intro b n hn w
      rw [sortedAux_succ]
      by_cases h0 : n = 0
      · subst h0
        rw [if_pos rfl, Finset.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨sortedWord_nil, rfl, by simp⟩
        · rintro ⟨-, he, -⟩
          exact (energyVir_eq_zero_iff w).mp he
      · rw [if_neg h0, Finset.mem_biUnion]
        constructor
        · rintro ⟨i, hi, hw⟩
          rw [Finset.mem_filter, Finset.mem_range] at hi
          obtain ⟨hib, hin⟩ := hi
          rw [Finset.mem_image] at hw
          obtain ⟨v, hv, rfl⟩ := hw
          obtain ⟨hvs, hve, hvb⟩ := (ih i (n - i - 2) (by omega) v).mp hv
          refine ⟨hvs.cons (fun x hx => hvb x hx), ?_, ?_⟩
          · rw [energyVir_cons, hve]; omega
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | h
            · omega
            · exact le_trans (hvb x h) (by omega)
        · rintro ⟨hs, he, hb⟩
          cases w with
          | nil => rw [energyVir_nil] at he; omega
          | cons i v =>
              rw [energyVir_cons] at he
              have hib : i ≤ b := hb i (by simp)
              refine ⟨i, ?_, ?_⟩
              · rw [Finset.mem_filter, Finset.mem_range]
                exact ⟨by omega, by omega⟩
              · rw [Finset.mem_image]
                exact ⟨v, (ih i (n - i - 2) (by omega) v).mpr
                  ⟨hs.tail, by omega, fun x hx => hs.head_ge x hx⟩, rfl⟩

/-- **The partitions of `n` into parts `≥ 2`, computably.**  A member is a weakly decreasing list
`[i₁,…,i_k]` with `∑ⱼ (iⱼ + 2) = n`, i.e. the partition `(i₁+2) + ⋯ + (i_k+2) = n`; it indexes the
basis vector `L₋ᵢ₁₋₂ ⋯ L₋ᵢₖ₋₂|0⟩` of `gradingVir c n`. -/
def sortedWords (n : ℕ) : Finset (List ℕ) := sortedAux n n n

/-- `sortedWords n` is exactly the set of sorted words of energy `n`.  The entry bound is free:
an entry `x` of a word of energy `n` already satisfies `x + 2 ≤ n`. -/
theorem mem_sortedWords (n : ℕ) (w : List ℕ) :
    w ∈ sortedWords n ↔ (SortedWord w ∧ energyVir w = n) := by
  rw [sortedWords, mem_sortedAux n n n (by omega) w]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, fun x hx => ?_⟩
    have := energyVir_ge_of_mem hx
    omega

/-- The index type of the partition basis is enumerated by `sortedWords`. -/
theorem card_sortedOfEnergy_eq (n : ℕ) :
    Fintype.card (SortedOfEnergy n) = (sortedWords n).card :=
  card_sortedOfEnergy_of_eq _ (fun w => (mem_sortedWords n w).symm)

/-- **The graded dimension of `V(c,0)`, computably.**  For every central charge `c` and every
level `n`, `dim 𝒱ₙ` is the cardinality of the computable `Finset` `sortedWords n` — so the kernel
alone settles it at any level, with no hand enumeration. -/
theorem finrank_gradingVir_eq_card (c : ℂ) (n : ℕ) :
    Module.finrank ℂ (gradingVir c (n : ℤ)) = (sortedWords n).card := by
  rw [finrank_gradingVir c n, card_sortedOfEnergy_eq n]

end Enumeration


/-! ### The dimension table, by kernel computation.

`sortedWords n` counts the partitions of `n` into parts `≥ 2`; the classical value is
`p(n) − p(n−1)`.  The first entries are `1, 0, 1, 1, 2, 2, 4, 4, 7, 8, 12, 14, 21, …`, and the
level-`n` graded piece of `V(c,0)` has exactly that dimension, for every central charge.
-/

section DimensionTable

set_option maxRecDepth 100000

/-- Levels `0`–`8`: `dim 𝒱ₙ = 1, 0, 1, 1, 2, 2, 4, 4, 7`.  Levels `2`–`6` reproduce
`finrank_gradingVir_two/three/four/five/six` of `Examples/VirasoroPartitionBasis`, which were
obtained by hand enumeration; level `0` reproduces `gradingVir_zero` (`𝒱₀ = ℂ|0⟩`), and level `1`
records that there is no mode `L₋₁` acting nontrivially on the vacuum. -/
theorem card_sortedWords_le_eight :
    (sortedWords 0).card = 1 ∧ (sortedWords 1).card = 0 ∧ (sortedWords 2).card = 1 ∧
      (sortedWords 3).card = 1 ∧ (sortedWords 4).card = 2 ∧ (sortedWords 5).card = 2 ∧
      (sortedWords 6).card = 4 ∧ (sortedWords 7).card = 4 ∧ (sortedWords 8).card = 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Levels `12` and `16`: `21` and `55` partitions into parts `≥ 2`. -/
theorem card_sortedWords_twelve_sixteen :
    (sortedWords 12).card = 21 ∧ (sortedWords 16).card = 55 := ⟨rfl, rfl⟩

/-- The explicit level-`6` index set, matching `gradingVir_six_span`. -/
theorem sortedWords_six : sortedWords 6 = {[4], [2, 0], [1, 1], [0, 0, 0]} := by decide

/-- `dim 𝒱₇ = 4`: the partitions `7`, `5+2`, `4+3`, `3+2+2`. -/
theorem finrank_gradingVir_seven (c : ℂ) : Module.finrank ℂ (gradingVir c 7) = 4 := by
  have h : ((7 : ℕ) : ℤ) = (7 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir_eq_card c 7]
  rfl

/-- `dim 𝒱₈ = 7`: the first level at which two partitions have the *same length*
(`6+2` and `4+4`), which is exactly the case the evaluation functionals `ev0`/`ev1` of
`Examples/LeeYangSingular` could not separate and the top symbol can. -/
theorem finrank_gradingVir_eight (c : ℂ) : Module.finrank ℂ (gradingVir c 8) = 7 := by
  have h : ((8 : ℕ) : ℤ) = (8 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir_eq_card c 8]
  rfl

/-- `dim 𝒱₁₂ = 21`. -/
theorem finrank_gradingVir_twelve (c : ℂ) : Module.finrank ℂ (gradingVir c 12) = 21 := by
  have h : ((12 : ℕ) : ℤ) = (12 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir_eq_card c 12]
  rfl

/-- `dim 𝒱₁₆ = 55`. -/
theorem finrank_gradingVir_sixteen (c : ℂ) : Module.finrank ℂ (gradingVir c 16) = 55 := by
  have h : ((16 : ℕ) : ℤ) = (16 : ℤ) := by norm_num
  rw [← h, finrank_gradingVir_eq_card c 16]
  rfl

end DimensionTable

/-! ## §3  The Feigin–Fuchs embedding `V(c,0) ↪ Fock`.

The top symbol separates the sorted creation words *in Fock*, so the linear-dilaton realisation
does not merely detect that `V(c,0)` is nonzero — it embeds it.  Concretely: the annihilator of the
free-boson vacuum inside `U(𝔙𝔦𝔯)` is precisely the vacuum ideal `J(c)`, no larger.

The one thing to keep straight is which map this is.  A Feigin–Fuchs *screening operator*
`Q : Fock → Fock` genuinely acquires a kernel at the degenerate central charges — that is the
content of the Felder resolution, in which the singular vector of `V(c,0)` is a **nonzero** element
of `im Q` and `L(c,0) = ker Q / im Q`.  The map studied here goes the other way, out of the
*universal* module, and is injective at every `c`: its separating invariant is the `λ`-free top
symbol of §1, so there is no charge at which it can degenerate.
-/

section Embedding

/-- The sorted creation words span all of `V(c,0)`: every creation monomial lies in the span of
the sorted ones of the same energy (`negWordVir_mem_sortedSpanVir`), and the creation monomials
span (`negSpanVir_eq_top`). -/
theorem sortedWord_span_top (c : ℂ) :
    ⊤ ≤ Submodule.span ℂ
      (Set.range (fun w : {w : List ℕ // SortedWord w} => negWordVir c w.1)) := by
  rw [← negSpanVir_eq_top c, negSpanVir, Submodule.span_le]
  rintro x ⟨ws, rfl⟩
  have hle : sortedSpanVir c (energyVir ws)
      ≤ Submodule.span ℂ
        (Set.range (fun w : {w : List ℕ // SortedWord w} => negWordVir c w.1)) := by
    rw [sortedSpanVir, Submodule.span_le]
    rintro y ⟨u, hu, -, rfl⟩
    exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
  exact hle (negWordVir_mem_sortedSpanVir c ws)

/-- **The global partition basis of `V(c,0)`**, indexed by *all* sorted words at once (the graded
pieces are `gradedBasis`).  Independence is `sortedWord_linearIndependent`, spanning is
`sortedWord_span_top`. -/
noncomputable def sortedBasisVir (c : ℂ) :
    Module.Basis {w : List ℕ // SortedWord w} ℂ (VirUniv c) :=
  Module.Basis.mk (sortedWord_linearIndependent c) (sortedWord_span_top c)

/-- The abstract basis constructed from independent, spanning sorted words
evaluates to the original negative-mode word on the vacuum. This keeps
coordinate calculations tied to the actual states rather than a new carrier. -/
@[simp] theorem sortedBasisVir_apply (c : ℂ) (w : {w : List ℕ // SortedWord w}) :
    sortedBasisVir c w = negWordVir c w.1 := Module.Basis.mk_apply _ _ w

/-- Independence of the Fock images of the sorted words, with the length bound supplied
automatically (a finite set of words has a longest one). -/
theorem fockWordVir_coef_zero_of_sorted (lam : ℂ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hsort : ∀ w ∈ s, SortedWord w)
    (hsum : ∑ w ∈ s, coef w • fockWordVir lam w = 0) : ∀ w ∈ s, coef w = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · intro w hw; exact absurd hw (Finset.notMem_empty w)
  · obtain ⟨w₀, -, hK⟩ := s.exists_max_image (fun w => w.length) hne
    exact fockWordVir_coef_zero lam w₀.length s coef hsort hK hsum

/-- **The Fock images of the sorted creation words are linearly independent**, for every
background charge — the free-field shadow of `sortedWord_linearIndependent`. -/
theorem fockWordVir_linearIndependent (lam : ℂ) :
    LinearIndependent ℂ (fun w : {w : List ℕ // SortedWord w} => fockWordVir lam w.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hinj : Function.Injective (fun w : {w : List ℕ // SortedWord w} => w.1) :=
    Subtype.val_injective
  have hcv : ∀ j : {w : List ℕ // SortedWord w},
      (Function.extend (fun w : {w : List ℕ // SortedWord w} => w.1) g 0) j.1 = g j :=
    fun j => hinj.extend_apply g 0 j
  have hsum' : ∑ l ∈ s.image (fun w : {w : List ℕ // SortedWord w} => w.1),
      (Function.extend (fun w : {w : List ℕ // SortedWord w} => w.1) g 0) l
        • fockWordVir lam l = 0 := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [hcv]
    exact hsum
  have hs : ∀ l ∈ s.image (fun w : {w : List ℕ // SortedWord w} => w.1), SortedWord l := by
    intro l hl
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
    exact j.2
  have h := fockWordVir_coef_zero_of_sorted lam
    (s.image (fun w : {w : List ℕ // SortedWord w} => w.1))
    (Function.extend (fun w : {w : List ℕ // SortedWord w} => w.1) g 0) hs hsum' i.1
    (Finset.mem_image_of_mem _ hi)
  rwa [hcv i] at h

/-- Rewriting a finite combination of sorted creation monomials as the class of the corresponding
combination in `U(𝔙𝔦𝔯)`. -/
theorem mk_sum_sorted {c : ℂ} (g : {w : List ℕ // SortedWord w} → ℂ)
    (s : Finset {w : List ℕ // SortedWord w}) :
    ∑ i ∈ s, g i • negWordVir c i.1
      = Submodule.Quotient.mk (∑ i ∈ s, g i • uWord i.1) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, negWordVir_eq_mk]
      rfl

/-- **The Feigin–Fuchs embedding.**  For any background charge `λ` with `1 − 12λ² = c`, the
annihilator of the free-boson vacuum inside `U(𝔙𝔦𝔯)` is *exactly* the vacuum ideal:

  `evAlg λ a |0⟩ = 0  ↔  a ∈ J(c)`.

The inclusion `⊇` is `evAlg_kills_vacIdeal`.  For `⊆`, expand the class of `a` in the global
partition basis `sortedBasisVir`; its Fock image is the same combination of the `fockWordVir`,
which are independent by `fockWordVir_linearIndependent`, so all coefficients vanish and the class
of `a` is `0`.  Valid at **every** central charge, the degenerate minimal-model values included. -/
theorem evAlg_vacuum_eq_zero_iff {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) (a : UVir) :
    evAlg lam a vacuum = 0 ↔ a ∈ vacIdeal c := by
  classical
  refine ⟨fun h0 => ?_, fun ha => evAlg_kills_vacIdeal hlam ha⟩
  refine (Submodule.Quotient.mk_eq_zero (vacIdeal c)).mp ?_
  set b := sortedBasisVir c with hb
  set v : VirUniv c := Submodule.Quotient.mk a with hvdef
  set f := b.repr v with hfdef
  have hrep : ∑ i ∈ f.support, f i • negWordVir c i.1 = v := by
    conv_rhs => rw [← b.linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, ← hfdef]
    exact Finset.sum_congr rfl (fun i _ => by rw [hb, sortedBasisVir_apply])
  have hsub : (Submodule.Quotient.mk (a - ∑ i ∈ f.support, f i • uWord i.1) : VirUniv c) = 0 := by
    rw [Submodule.Quotient.mk_sub, ← mk_sum_sorted f f.support, hrep, ← hvdef, sub_self]
  have hz : evAlg lam (a - ∑ i ∈ f.support, f i • uWord i.1) vacuum = 0 :=
    evAlg_kills_vacIdeal hlam ((Submodule.Quotient.mk_eq_zero _).mp hsub)
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hz
  have hE : evAlg lam (∑ i ∈ f.support, f i • uWord i.1) vacuum
      = ∑ i ∈ f.support, f i • fockWordVir lam i.1 := by
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl
      (fun i _ => by rw [map_smul, LinearMap.smul_apply, evAlg_uWord])
  have hsum0 : ∑ i ∈ f.support, f i • fockWordVir lam i.1 = 0 := by
    rw [← hE, ← hz, h0]
  have hzero := (linearIndependent_iff'.mp (fockWordVir_linearIndependent lam)) f.support f hsum0
  rw [← hrep]
  exact Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_smul])

/-- The `ℂ`-linear evaluation `U(𝔙𝔦𝔯) → Fock`, `a ↦ a·|0⟩`, at background charge `λ`. -/
noncomputable def evVac (lam : ℂ) : UVir →ₗ[ℂ] Fock where
  toFun a := evAlg lam a vacuum
  map_add' a b := by rw [map_add, LinearMap.add_apply]
  map_smul' r a := by rw [map_smul, LinearMap.smul_apply]; rfl

/-- **The Feigin–Fuchs map** `Φ_c : V(c,0) →ₗ[ℂ] Fock`, `[a] ↦ a·|0⟩`, well defined because the
vacuum ideal is annihilated at the free-boson vacuum. -/
noncomputable def fockMap {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) : VirUniv c →ₗ[ℂ] Fock :=
  (((vacIdeal c).restrictScalars ℂ).liftQ (evVac lam)
      (fun _ hx => evAlg_kills_vacIdeal hlam hx)).comp
    (Submodule.Quotient.restrictScalarsEquiv ℂ (vacIdeal c)).symm.toLinearMap

/-- For a representative in the enveloping algebra, the vacuum-module map
to Fock space is its free-boson action on the Fock vacuum. The charge relation
ensures this evaluation descends to the vacuum quotient. -/
@[simp] theorem fockMap_mk {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) (a : UVir) :
    fockMap hlam (Submodule.Quotient.mk a) = evAlg lam a vacuum := rfl

/-- The Feigin–Fuchs map sends the creation monomials to the free-boson creation words. -/
theorem fockMap_negWordVir {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) (ws : List ℕ) :
    fockMap hlam (negWordVir c ws) = fockWordVir lam ws := by
  rw [negWordVir_eq_mk, fockMap_mk, evAlg_uWord]

/-- **`V(c,0)` embeds in the free-boson Fock space, at every central charge.**  In particular
at the degenerate minimal-model charges — `c = −22/5` (Lee–Yang), `c = 1/2` (Ising), `c = 0` — the
universal vacuum module still injects; degeneracy there is a statement about the *simple quotient*
`L(c,0)`, not about `V(c,0)`. -/
theorem fockMap_injective {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) :
    Function.Injective (fockMap hlam) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro v hv
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (vacIdeal c) v
  rw [fockMap_mk] at hv
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((evAlg_vacuum_eq_zero_iff hlam a).mp hv)

/-- **At every central charge, `V(c,0)` embeds in the free boson.**  The sealed form: for each
`c` there is an injective `ℂ`-linear `Φ : V(c,0) → Fock` sending `|0⟩ ↦ 1`.  The existence of a
suitable background charge is `exists_lam` (`ℂ` is algebraically closed, so `1 − 12λ² = c` always
has a solution); the `|0⟩ ↦ 1` clause certifies that `Φ` is not the zero map. -/
theorem exists_injective_fockMap (c : ℂ) :
    ∃ Φ : VirUniv c →ₗ[ℂ] Fock, Function.Injective Φ ∧ Φ (vacVec c) = 1 := by
  obtain ⟨lam, hlam⟩ := exists_lam c
  refine ⟨fockMap hlam, fockMap_injective hlam, ?_⟩
  rw [vacVec, fockMap_mk, map_one, Module.End.one_apply]
  rfl

/-- The Lee–Yang charge `c = −22/5` is not an exception: the *universal* vacuum module still
embeds.  What degenerates at `c = −22/5` is the quotient `V(−22/5,0) ↠ L(−22/5,0)`, whose kernel is
generated by the singular vector — a vector which this embedding sends to a **nonzero** element of
`Fock` (compare `leeYangSingular_ne_zero` of `Examples/LeeYangSingular`). -/
theorem exists_injective_fockMap_leeYang :
    ∃ Φ : VirUniv (-22 / 5 : ℂ) →ₗ[ℂ] Fock,
      Function.Injective Φ ∧ Φ (vacVec (-22 / 5 : ℂ)) = 1 :=
  exists_injective_fockMap _

end Embedding



end VOA.VirModule
