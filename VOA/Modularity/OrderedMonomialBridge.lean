/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BuhlSpanningProof

/-!
# Bridge: sorted generator words are the repo's `orderedMonomial`s

`Modularity.GrowthBound.orderedMonomial N gen μ u` is the colored-partition normal form

  `(gen i₁)₍₋m₁₋₁₎^{μ(i₁,m₁)} ⋯ (gen i_r)₍₋m_r₋₁₎^{μ(i_r,m_r)} u`,
  `(i₁,m₁) < ⋯ < (i_r,m_r)` in the **lexicographic** order,

built by folding over `μ.support` sorted lexicographically.  `Modularity.OrderedSpan` produces
instead the *sorted list* form `wordAct (genWord gen wt l) u` with `l` lexicographically sorted
(repeats adjacent).  This file identifies the two.

## Contents

* `foldMon` — the fold underlying `orderedMonomial`, and its congruence lemma.
* `orderedMonomial_peel` — pulling the (lex-)minimal pair `q` out of the fold:
  `orderedMonomial μ u = (gen q.1)₍₋q.2₋₁₎^{μ q} (fold over μ.support.erase q)`.
* `orderedMonomial_prepend` — the key identity: if `q` is `≤` every pair of `μ.support`,
  `orderedMonomial (μ + single q 1) u = (gen q.1)₍₋q.2₋₁₎ (orderedMonomial μ u)`.
* `wordAct_genWord_eq_orderedMonomial` — every **sorted** generator word is an
  `orderedMonomial`, with `μ` the multiplicity (count) function of the list.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The fold underlying `orderedMonomial` -/

/-- The fold underlying `orderedMonomial`, over an arbitrary list of (lex) pairs. -/
noncomputable def foldMon (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱) (μ : Fin g × ℕ →₀ ℕ)
    (u : M) (L : List (Lex (Fin g × ℕ))) : M :=
  L.foldr (fun (p : Lex (Fin g × ℕ)) (acc : M) =>
    ((⇑(mode (N.YM (gen (ofLex p).1)) (-((ofLex p).2 : ℤ) - 1)))^[μ (ofLex p)]) acc) u

theorem orderedMonomial_eq_foldMon (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱)
    (μ : Fin g × ℕ →₀ ℕ) (u : M) :
    orderedMonomial N gen μ u
      = foldMon N gen μ u ((μ.support.map toLex.toEmbedding).sort (· ≤ ·)) := rfl

@[simp] theorem foldMon_nil (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱) (μ : Fin g × ℕ →₀ ℕ)
    (u : M) : foldMon N gen μ u [] = u := rfl

@[simp] theorem foldMon_cons (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱) (μ : Fin g × ℕ →₀ ℕ)
    (u : M) (p : Lex (Fin g × ℕ)) (L : List (Lex (Fin g × ℕ))) :
    foldMon N gen μ u (p :: L)
      = ((⇑(mode (N.YM (gen (ofLex p).1)) (-((ofLex p).2 : ℤ) - 1)))^[μ (ofLex p)])
          (foldMon N gen μ u L) := rfl

/-- The fold only sees `μ` on the entries of the list. -/
theorem foldMon_congr (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱) {μ ν : Fin g × ℕ →₀ ℕ}
    (u : M) (L : List (Lex (Fin g × ℕ))) (h : ∀ p ∈ L, μ (ofLex p) = ν (ofLex p)) :
    foldMon N gen μ u L = foldMon N gen ν u L := by
  induction L with
  | nil => rfl
  | cons p t ih =>
      rw [foldMon_cons, foldMon_cons, ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
        h p (List.mem_cons_self ..)]

/-! ## Peeling the minimal pair -/

/-- **Peeling.**  If `q` is `≤` every pair of `μ.support`, the fold splits off exactly
`μ q` copies of the mode `(gen q.1)₍₋q.2₋₁₎`. -/
theorem orderedMonomial_peel (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱)
    (μ : Fin g × ℕ →₀ ℕ) (u : M) (q : Fin g × ℕ)
    (hq : ∀ r ∈ μ.support, toLex q ≤ toLex r) :
    orderedMonomial N gen μ u
      = ((⇑(mode (N.YM (gen q.1)) (-(q.2 : ℤ) - 1)))^[μ q])
          (foldMon N gen μ u (((μ.support.erase q).map toLex.toEmbedding).sort (· ≤ ·))) := by
  classical
  rw [orderedMonomial_eq_foldMon]
  by_cases hmem : q ∈ μ.support
  · -- `μ.support = insert q (μ.support.erase q)`; `Finset.sort_insert` peels the head
    have hins : μ.support.map toLex.toEmbedding
        = insert (toLex q) ((μ.support.erase q).map toLex.toEmbedding) := by
      have hmi := Finset.map_insert toLex.toEmbedding q (μ.support.erase q)
      rw [Finset.insert_erase hmem] at hmi
      exact hmi
    have hnot : toLex q ∉ (μ.support.erase q).map toLex.toEmbedding := by
      rw [Finset.mem_map]
      rintro ⟨r, hr, hrq⟩
      have : r = q := by
        have := hrq
        exact toLex.injective this
      exact (Finset.mem_erase.mp hr).1 this
    have hle : ∀ b ∈ (μ.support.erase q).map toLex.toEmbedding, toLex q ≤ b := by
      intro b hb
      rw [Finset.mem_map] at hb
      obtain ⟨r, hr, rfl⟩ := hb
      exact hq r (Finset.mem_of_mem_erase hr)
    rw [hins, Finset.sort_insert _ hle hnot, foldMon_cons]
    rfl
  · -- `q ∉ μ.support`: nothing to peel (`μ q = 0`) and the erase does nothing
    have hz : μ q = 0 := Finsupp.notMem_support_iff.mp hmem
    have herase : μ.support.erase q = μ.support := Finset.erase_eq_of_notMem hmem
    rw [herase, hz, Function.iterate_zero, id_eq]

/-- **Prepending a minimal pair.**  If `q` is `≤` every pair of `μ.support`, then adding one
more copy of `q` to `μ` is exactly applying the mode `(gen q.1)₍₋q.2₋₁₎` on the outside. -/
theorem orderedMonomial_prepend (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱)
    (μ : Fin g × ℕ →₀ ℕ) (u : M) (q : Fin g × ℕ)
    (hq : ∀ r ∈ μ.support, toLex q ≤ toLex r) :
    orderedMonomial N gen (μ + Finsupp.single q 1) u
      = mode (N.YM (gen q.1)) (-(q.2 : ℤ) - 1) (orderedMonomial N gen μ u) := by
  classical
  set ν : Fin g × ℕ →₀ ℕ := μ + Finsupp.single q 1 with hν
  have hνq : ν q = μ q + 1 := by rw [hν]; simp
  have hνr : ∀ r, r ≠ q → ν r = μ r := by
    intro r hr; rw [hν]; simp [Finsupp.single_apply, hr]
  have hsupp : ν.support = insert q μ.support := by
    ext r
    by_cases hr : r = q
    · subst hr
      simp only [Finsupp.mem_support_iff, hνq, Finset.mem_insert, true_or, iff_true]
      omega
    · rw [Finsupp.mem_support_iff, hνr r hr, Finset.mem_insert]
      simp only [hr, false_or]
      exact Finsupp.mem_support_iff.symm
  have hqν : ∀ r ∈ ν.support, toLex q ≤ toLex r := by
    intro r hr
    rw [hsupp, Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact le_rfl
    · exact hq r hr
  have herase : ν.support.erase q = μ.support.erase q := by
    rw [hsupp, Finset.erase_insert_eq_erase]
  have hfold : foldMon N gen ν u (((μ.support.erase q).map toLex.toEmbedding).sort (· ≤ ·))
      = foldMon N gen μ u (((μ.support.erase q).map toLex.toEmbedding).sort (· ≤ ·)) := by
    refine foldMon_congr N gen u _ (fun p hp => ?_)
    rw [Finset.mem_sort, Finset.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact hνr r (Finset.mem_erase.mp hr).1
  rw [orderedMonomial_peel N gen ν u q hqν, herase, hfold, hνq, Function.iterate_succ_apply',
    ← orderedMonomial_peel N gen μ u q hq]

/-! ## Sorted generator words are ordered monomials -/

/-- The multiplicity (count) function of a list of pairs. -/
noncomputable def countFinsupp {g : ℕ} : List (Fin g × ℕ) → (Fin g × ℕ →₀ ℕ)
  | [] => 0
  | q :: t => Finsupp.single q 1 + countFinsupp t

theorem countFinsupp_support_subset {g : ℕ} (l : List (Fin g × ℕ)) {r : Fin g × ℕ}
    (hr : r ∈ (countFinsupp l).support) : r ∈ l := by
  classical
  induction l with
  | nil => simp only [countFinsupp, Finsupp.support_zero] at hr; exact absurd hr (by simp)
  | cons q t ih =>
      rw [countFinsupp, Finsupp.mem_support_iff, Finsupp.add_apply] at hr
      by_cases hrq : r = q
      · exact hrq ▸ List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (ih ?_)
        rw [Finsupp.mem_support_iff]
        intro hc
        rw [hc, Finsupp.single_apply, if_neg (Ne.symm hrq), add_zero] at hr
        exact hr rfl

/-- **A sorted generator word is an ordered monomial.** -/
theorem wordAct_genWord_eq_orderedMonomial (N : OrdVModule W M) {g : ℕ} (gen : Fin g → 𝒱)
    (wt : Fin g → ℕ) (u : M) :
    ∀ (l : List (Fin g × ℕ)), OrdPairs l →
      wordAct N.toWeakModule (genWord gen wt l) u = orderedMonomial N gen (countFinsupp l) u := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [genWord_nil, wordAct_nil, countFinsupp, orderedMonomial_eq_foldMon]
      simp only [Finsupp.support_zero, Finset.map_empty, Finset.sort_empty]
      rfl
  | cons q t ih =>
      intro hl
      obtain ⟨hqt, ht⟩ := OrdPairs_of_cons hl
      have hq : ∀ r ∈ (countFinsupp t).support, toLex q ≤ toLex r :=
        fun r hr => hqt r (countFinsupp_support_subset t hr)
      rw [genWord_cons, wordAct_cons, ih ht]
      have hstep := orderedMonomial_prepend N gen (countFinsupp t) u q hq
      rw [countFinsupp, add_comm (Finsupp.single q 1) (countFinsupp t), hstep]

end VOA
