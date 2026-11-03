/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.FiniteGenerationProof
import VOA.Core.BorcherdsIdentity

/-!
# Pair closure: the generator OPE table controls the whole iterated-product span

**The reduction this file provides.**  Let `W` be a vertex operator algebra and `S` a set of
states, each **homogeneous of weight `≥ 1`**.  Write `T = iterProdSpan W S` for the span of the
iterated strictly-negative-mode words `s^{i₁}₍₋m₁₎ ⋯ s^{iₖ}₍₋mₖ₎ 𝟙`.  Then

  `iterProdSpan_smul_closed` — **if `s₍ⱼ₎t ∈ T` for all `s, t ∈ S` and all `j ≥ 0`, then
  `u₍ₙ₎v ∈ T` for ALL `u, v ∈ T` and ALL `n ∈ ℤ`.**

That is: closure of the OPE **on the generators alone** (finitely many products, since `s₍ⱼ₎t = 0`
for `j ≥ wt s + wt t` by positivity — `smul_grading_neg_eq_zero` below) already forces closure of
the span under every vertex product.  Combined with `Examples.TripletWpAmbient`'s
`strongGenWp_iff_smulClosed`, this reduces the strong-generation hypothesis `StrongGenWp p hp` of
the triplet `C₂`-cofiniteness theorem to the finite generator OPE table.

## Why the induction converges (and why length induction does not)

The naive attempts fail: peeling the left factor by the Borcherds iterate produces generator
modes `s₍ᵢ₎v` on arbitrary span members (the "key lemma" below), and proving *that* by structure
induction on `v` produces `(s₍ⱼ₎t)₍ₖ₎y` — modes of an **arbitrary** element of `T` (the
hypothesis controls no word length), so pure length induction never closes.  The convergent
measure is the De Sole–Kac one: the **sum of the conformal weights of the two factors**.  Because
every generator has weight `≥ 1`:

* peeling one letter off a word strictly lowers its weight (`wt s + m − 1 ≥ 1`);
* every non-negative product `s₍ⱼ₎t` of two generators has weight `≤ wt s + wt t − 1`, strictly
  below the weight of the two-letter word it replaces.

Both claims are run in one strong induction on `ν = wt(left) + wt(right)`:

* `GenLevel W S ν` (`genLevel_step`) — generator modes `s₍ₖ₎x` on **words** `x`, with
  `wt s + wt x ≤ ν`.  One commutator peel (`Core.Reconstruction.mode_commutator`): the crossing
  terms `(s₍ⱼ₎t)₍ₖ₋ₘ₋ⱼ₎y` land in `ProdLevel` at measure `≤ ν − 1` because `j ≥ 0, m ≥ 1`.
* `ProdLevel W S ν` (`prodLevel_step`) — arbitrary products `u₍ₙ₎v`, `u, v ∈ T` homogeneous with
  `wt u + wt v ≤ ν`.  Homogeneous members of `T` are combinations of **words of the same weight**
  (`mem_span_gradedWords`); one Borcherds-iterate peel (`Core.BorcherdsIdentity.mode_iterate`) of
  the left word leaves Family A `s₍₋ₘ₋ᵢ₎(w′₍ₙ₊ᵢ₎v)` (measure drops by `wt s + m − 1 ≥ 1`) and
  Family B `w′₍₋ₘ₊ₙ₋ᵢ₎(s₍ᵢ₎v)` (the inner factor is `GenLevel` at measure `≤ ν` — proved first
  within the same level — and the outer product has measure `≤ ν − m − i ≤ ν − 1`).

The vacuum cases are VA2/VA3 (`smul_vacuum_left`, `smul_vacuum_nonneg`); no translation lemma and
no skew-symmetry are needed.

## Main results

* `iterProdSpan_smul_closed` — the reduction stated above.
* `smul_grading_neg_eq_zero` — `a₍ₙ₎b = 0` for homogeneous `a, b` once `n ≥ wt a + wt b`
  (positivity), which makes the generator OPE table **finite**.
* `conformal_smul_conformal_mem_iterProdSpan` — the `(ω, ω)` row of any such table is **free**:
  `ω₍ⱼ₎ω ∈ T` for every `j ≥ 0`, in any VOA with `ω ∈ S`.  (`j = 0`: `Tω = ω₍₋₂₎𝟙`; `j = 1`:
  `L₀ω = 2ω`; `j = 2`: `L₁ω = 0` and `j = 3`: `L₂ω = (c/2)𝟙`, both from the Virasoro bracket on
  the vacuum; `j ≥ 4`: weight.)
* `isIterProd_exists_grading`, `mem_span_gradedWords`, `eq_zero_of_mem_grading_ne` — the graded
  bookkeeping: words are homogeneous, homogeneous members of `T` are combinations of same-weight
  words, distinct graded pieces meet in `0`.

## What this file does NOT do

It does not prove any generator OPE table.  For the triplet `W(p)` the table (16 pairs, modes
`0 ≤ j < wt g + wt h`) is a genuine deformed-lattice computation, carried as the named hypothesis
`GenPairClosedWp` in `Examples.TripletWpPairClosure`.

## Status

Every declaration is proved: `sorry`-free, `admit`-free, `native_decide`-free, and
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  The theorem
`VOA.pbw` is not used.

## References

* A. De Sole and V. Kac, *Freely generated vertex algebras and non-linear Lie conformal
  algebras*, Comm. Math. Phys. **254** (2005) 659–694 — the grading condition that makes the
  rewriting terminate is the model for the weight measure used here.
* T. Gannon, *Moonshine beyond the Monster*, §5.3.11 (spanning sets).
* D. Adamović and A. Milas, Adv. Math. **217** (2008) 2664–2699, Prop. 2.3(ii) — the statement
  this reduction feeds at `W(p)`.
-/

set_option linter.style.longLine false

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  Graded bookkeeping -/

/-- Two distinct graded pieces meet only in `0`: if `x` is in both `𝒱ₐ` and `𝒱_b` with `a ≠ b`,
then `x = 0`.  (Via the homogeneous projection `piHom`.) -/
theorem eq_zero_of_mem_grading_ne (W : VertexOperatorAlgebra 𝒱) {a b : ℤ} (hab : a ≠ b)
    {x : 𝒱} (hxa : x ∈ W.grading a) (hxb : x ∈ W.grading b) : x = 0 := by
  have h1 : piHom W a x = x := piHom_of_mem W hxa
  have h2 : piHom W a x = 0 := piHom_of_mem_ne W (Ne.symm hab) hxb
  rw [h1] at h2
  exact h2

/-- **The vanishing that makes the generator OPE table finite**: for homogeneous `a ∈ 𝒱_{da}`,
`b ∈ 𝒱_{db}` and any mode `n ≥ da + db`, the product `a₍ₙ₎b` lands in a negative graded piece,
which is `⊥` by positivity — so it vanishes. -/
theorem smul_grading_neg_eq_zero (W : VertexOperatorAlgebra 𝒱) {da db : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading da) (hb : b ∈ W.grading db) {n : ℤ} (hn : da + db ≤ n) :
    W.smul a n b = 0 := by
  have h := W.smul_mem_grading ha hb n
  rw [W.positivity (da + db - n - 1) (by omega)] at h
  exact (Submodule.mem_bot ℂ).mp h

/-- Every iterated product of homogeneous generators is homogeneous (of some weight). -/
theorem isIterProd_exists_grading (W : VertexOperatorAlgebra 𝒱) {S : Set 𝒱}
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d) {x : 𝒱}
    (hx : IsIterProd W S x) : ∃ k : ℤ, x ∈ W.grading k := by
  induction hx with
  | vacuum => exact ⟨0, W.vacuum_mem⟩
  | step s hs m _ y _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨d, _, hd⟩ := hS s hs
      refine ⟨d + k + m - 1, ?_⟩
      have h := W.smul_mem_grading hd hk (-m)
      rwa [show d + k - (-m) - 1 = d + k + m - 1 from by ring] at h

/-- **Graded decomposition of the span**: a homogeneous member of `T = iterProdSpan W S` of
weight `r` is a combination of *words of weight exactly `r`*.  (Project with `piHom r`: each word
is homogeneous, so it is either fixed or killed.) -/
theorem mem_span_gradedWords (W : VertexOperatorAlgebra 𝒱) {S : Set 𝒱}
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d) {u : 𝒱} {r : ℤ}
    (huT : u ∈ iterProdSpan W S) (hur : u ∈ W.grading r) :
    u ∈ Submodule.span ℂ {x | IsIterProd W S x ∧ x ∈ W.grading r} := by
  have hproj : piHom W r u ∈ Submodule.span ℂ {x | IsIterProd W S x ∧ x ∈ W.grading r} := by
    refine Submodule.span_induction
      (p := fun u _ => piHom W r u ∈ Submodule.span ℂ {x | IsIterProd W S x ∧ x ∈ W.grading r})
      ?_ ?_ ?_ ?_ huT
    · intro w hw
      obtain ⟨k, hk⟩ := isIterProd_exists_grading W hS hw
      by_cases hkr : k = r
      · subst hkr
        rw [piHom_of_mem W hk]
        exact Submodule.subset_span ⟨hw, hk⟩
      · rw [piHom_of_mem_ne W (Ne.symm (fun h => hkr h.symm)) hk]
        exact zero_mem _
    · simp only [map_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
    · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha
  rwa [piHom_of_mem W hur] at hproj

/-! ## §2  The two levels of the strong induction -/

/-- **Level-`ν` generator-mode claim**: every mode of every generator `s ∈ S` maps every word `x`
with `wt s + wt x ≤ ν` into `T`. -/
def GenLevel (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) (ν : ℕ) : Prop :=
  ∀ s ∈ S, ∀ ds : ℤ, s ∈ W.grading ds →
    ∀ x, IsIterProd W S x → ∀ qx : ℤ, x ∈ W.grading qx → ds + qx ≤ (ν : ℤ) →
      ∀ k : ℤ, W.smul s k x ∈ iterProdSpan W S

/-- **Level-`ν` product claim**: every product `u₍ₙ₎v` of homogeneous members of `T` with
`wt u + wt v ≤ ν` lies in `T`. -/
def ProdLevel (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) (ν : ℕ) : Prop :=
  ∀ pu qv : ℤ, pu + qv ≤ (ν : ℤ) →
    ∀ u ∈ iterProdSpan W S, u ∈ W.grading pu →
      ∀ v ∈ iterProdSpan W S, v ∈ W.grading qv →
        ∀ n : ℤ, W.smul u n v ∈ iterProdSpan W S

/-- **The generator-mode step.**  `GenLevel` at level `ν` follows from `ProdLevel` at all levels
`< ν`, by one commutator peel of the word: `s₍ₖ₎(t₍₋ₘ₎y) = t₍₋ₘ₎(s₍ₖ₎y) + ∑ⱼ C(k,j)·
(s₍ⱼ₎t)₍ₖ₋ₘ₋ⱼ₎y`.  The inner product `s₍ₖ₎y` and the crossing terms `(s₍ⱼ₎t)₍ₖ₋ₘ₋ⱼ₎y` (whose
left factor is in `T` by the pair hypothesis) all have measure `≤ ν − 1`. -/
theorem genLevel_step (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d)
    (hpair : ∀ s ∈ S, ∀ t ∈ S, ∀ j : ℤ, 0 ≤ j → W.smul s j t ∈ iterProdSpan W S)
    (ν : ℕ) (ihM : ∀ ν' : ℕ, ν' < ν → ProdLevel W S ν') :
    GenLevel W S ν := by
  intro s hs ds hds x hx qx hqx hν k
  by_cases hs0 : s = 0
  · rw [hs0, PreVertexAlgebra.smul_zero_left]
    exact zero_mem _
  have hds1 : (1 : ℤ) ≤ ds := by
    obtain ⟨d0, hd01, hd0g⟩ := hS s hs
    by_cases hdd : d0 = ds
    · omega
    · exact absurd (eq_zero_of_mem_grading_ne W hdd hd0g hds) hs0
  rcases lt_or_ge k 0 with hk | hk
  · -- negative modes of generators are word steps
    have h := smul_mem_iterProdSpan W S hs (show (1 : ℤ) ≤ -k from by omega)
      (Submodule.subset_span hx)
    rwa [neg_neg] at h
  cases hx with
  | vacuum =>
      rw [W.toPreVertexAlgebra.smul_vacuum_nonneg s hk]
      exact zero_mem _
  | step t ht m hm y hy =>
      by_cases hx0 : W.smul t (-m) y = 0
      · rw [hx0, W.toPreVertexAlgebra.smul_zero_right]
        exact zero_mem _
      obtain ⟨dt, hdt1, hdtg⟩ := hS t ht
      obtain ⟨qy, hqy⟩ := isIterProd_exists_grading W hS hy
      have hy0 : y ≠ 0 := fun h => hx0 (by rw [h, W.toPreVertexAlgebra.smul_zero_right])
      have hqy0 : (0 : ℤ) ≤ qy := by
        by_contra h
        push_neg at h
        refine hy0 ?_
        rw [W.positivity qy h] at hqy
        exact (Submodule.mem_bot ℂ).mp hqy
      have hxg' : W.smul t (-m) y ∈ W.grading (dt + qy + m - 1) := by
        have h := W.smul_mem_grading hdtg hqy (-m)
        rwa [show dt + qy - (-m) - 1 = dt + qy + m - 1 from by ring] at h
      have hqxeq : qx = dt + qy + m - 1 := by
        by_contra hne
        exact hx0 (eq_zero_of_mem_grading_ne W hne hqx hxg')
      have hν1 : 1 ≤ ν := by omega
      -- the commutator peel
      obtain ⟨N, hN⟩ := mode_commutator W s t k (-m)
      rw [Ring.lie_def] at hN
      have hy' := DFunLike.congr_fun hN y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
        LinearMap.smul_apply] at hy'
      simp only [← PreVertexAlgebra.smul_def] at hy'
      rw [eq_add_of_sub_eq hy']
      refine add_mem ?_ ?_
      · -- crossing terms (s₍ⱼ₎t)₍ₖ₋ₘ₋ⱼ₎y, measure ≤ ν − 1
        refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_)
        have hst : W.smul s ((j : ℕ) : ℤ) t ∈ iterProdSpan W S :=
          hpair s hs t ht ((j : ℕ) : ℤ) (Int.natCast_nonneg _)
        have hstg : W.smul s ((j : ℕ) : ℤ) t ∈ W.grading (ds + dt - (j : ℕ) - 1) :=
          W.smul_mem_grading hds hdtg _
        exact ihM (ν - 1) (by omega) (ds + dt - (j : ℕ) - 1) qy (by omega)
          _ hst hstg y (Submodule.subset_span hy) hqy _
      · -- t₍₋ₘ₎(s₍ₖ₎y): inner measure ds + qy ≤ ν − 1
        have hin : W.smul s k y ∈ iterProdSpan W S :=
          ihM (ν - 1) (by omega) ds qy (by omega) s (subset_iterProdSpan W S hs) hds
            y (Submodule.subset_span hy) hqy k
        exact smul_mem_iterProdSpan W S ht hm hin

/-- **The product step.**  `ProdLevel` at level `ν` follows from `ProdLevel` at all levels `< ν`
together with `GenLevel` at level `ν`: decompose both factors into words of the correct weight,
then peel the left word by the all-`ℤ` Borcherds iterate.  Family A drops the measure by the
weight of the peeled letter; Family B routes through `GenLevel ν` for the inner factor and drops
the measure for the outer product. -/
theorem prodLevel_step (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d)
    (ν : ℕ) (ihM : ∀ ν' : ℕ, ν' < ν → ProdLevel W S ν')
    (hE : GenLevel W S ν) : ProdLevel W S ν := by
  intro pu qv hν u huT hug v hvT hvg n
  have hu' := mem_span_gradedWords W hS huT hug
  refine Submodule.span_induction
    (p := fun u _ => W.smul u n v ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ hu'
  · rintro w ⟨hw, hwg⟩
    have hv' := mem_span_gradedWords W hS hvT hvg
    refine Submodule.span_induction
      (p := fun v _ => W.smul w n v ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ hv'
    · rintro y ⟨hy, hyg⟩
      -- the core: a word `w` of weight `pu` against a word `y` of weight `qv`
      cases hw with
      | vacuum =>
          rw [W.toPreVertexAlgebra.smul_vacuum_left]
          split_ifs
          · exact Submodule.subset_span hy
          · exact zero_mem _
      | step s hs m hm w' hw' =>
          by_cases hw0 : W.smul s (-m) w' = 0
          · rw [hw0, W.toPreVertexAlgebra.smul_zero_left]
            exact zero_mem _
          by_cases hy0 : y = 0
          · rw [hy0, W.toPreVertexAlgebra.smul_zero_right]
            exact zero_mem _
          obtain ⟨ds, hds1, hdsg⟩ := hS s hs
          obtain ⟨qw', hqw'⟩ := isIterProd_exists_grading W hS hw'
          have hw'0 : w' ≠ 0 := fun h => hw0 (by rw [h, W.toPreVertexAlgebra.smul_zero_right])
          have hqw'0 : (0 : ℤ) ≤ qw' := by
            by_contra h
            push_neg at h
            refine hw'0 ?_
            rw [W.positivity qw' h] at hqw'
            exact (Submodule.mem_bot ℂ).mp hqw'
          have hqv0 : (0 : ℤ) ≤ qv := by
            by_contra h
            push_neg at h
            refine hy0 ?_
            rw [W.positivity qv h] at hyg
            exact (Submodule.mem_bot ℂ).mp hyg
          have hwg' : W.smul s (-m) w' ∈ W.grading (ds + qw' + m - 1) := by
            have h := W.smul_mem_grading hdsg hqw' (-m)
            rwa [show ds + qw' - (-m) - 1 = ds + qw' + m - 1 from by ring] at h
          have hpueq : pu = ds + qw' + m - 1 := by
            by_contra hne
            exact hw0 (eq_zero_of_mem_grading_ne W hne hwg hwg')
          have hν1 : 1 ≤ ν := by omega
          rw [mode_iterate W s w' (-m) n y]
          refine finsum_mem_submodule_pd _ _ (fun i => ?_)
          refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
          · -- Family A: s₍₋ₘ₋ᵢ₎(w′₍ₙ₊ᵢ₎y)
            have hin : W.smul w' (n + (i : ℤ)) y ∈ iterProdSpan W S :=
              ihM (ν - 1) (by omega) qw' qv (by omega) w' (Submodule.subset_span hw') hqw'
                y (Submodule.subset_span hy) hyg (n + i)
            have h2 := smul_mem_iterProdSpan W S hs
              (show (1 : ℤ) ≤ m + (i : ℤ) from by omega) hin
            rwa [show -(m + (i : ℤ)) = -m - i from by ring] at h2
          · -- Family B: w′₍₋ₘ₊ₙ₋ᵢ₎(s₍ᵢ₎y)
            have hsy : W.smul s ((i : ℕ) : ℤ) y ∈ iterProdSpan W S :=
              hE s hs ds hdsg y hy qv hyg (by omega) i
            have hsyg : W.smul s ((i : ℕ) : ℤ) y ∈ W.grading (ds + qv - (i : ℕ) - 1) :=
              W.smul_mem_grading hdsg hyg _
            exact ihM (ν - 1) (by omega) qw' (ds + qv - (i : ℕ) - 1) (by omega)
              w' (Submodule.subset_span hw') hqw' _ hsy hsyg (-m + n - i)
    · simp only [W.toPreVertexAlgebra.smul_zero_right]; exact zero_mem _
    · intro a b _ _ ha hb
      simp only [W.toPreVertexAlgebra.smul_add_right]
      exact add_mem ha hb
    · intro c a _ ha
      simp only [W.toPreVertexAlgebra.smul_smul_right]
      exact Submodule.smul_mem _ c ha
  · simp only [PreVertexAlgebra.smul_zero_left]; exact zero_mem _
  · intro a b _ _ ha hb
    simp only [PreVertexAlgebra.smul_add_left]
    exact add_mem ha hb
  · intro c a _ ha
    simp only [PreVertexAlgebra.smul_smul_left]
    exact Submodule.smul_mem _ c ha

/-- All levels hold: the strong induction on the weight sum, `GenLevel ν` proved first within
each level. -/
theorem prodLevel_all (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d)
    (hpair : ∀ s ∈ S, ∀ t ∈ S, ∀ j : ℤ, 0 ≤ j → W.smul s j t ∈ iterProdSpan W S)
    (ν : ℕ) : ProdLevel W S ν := by
  induction ν using Nat.strong_induction_on with
  | _ ν ih =>
      exact prodLevel_step W S hS ν ih (genLevel_step W S hS hpair ν ih)

/-! ## §3  The reduction -/

/-- **Pair closure controls the whole span.**  If every generator is homogeneous of weight
`≥ 1` and the generator OPE closes on `T = iterProdSpan W S` — i.e. `s₍ⱼ₎t ∈ T` for all
`s, t ∈ S`, `j ≥ 0` — then `T` is closed under **all** vertex products: `u₍ₙ₎v ∈ T` for all
`u, v ∈ T`, `n ∈ ℤ`.

By `smul_grading_neg_eq_zero` the hypothesis is a **finite** table: `s₍ⱼ₎t = 0` once
`j ≥ wt s + wt t`. -/
theorem iterProdSpan_smul_closed (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d)
    (hpair : ∀ s ∈ S, ∀ t ∈ S, ∀ j : ℤ, 0 ≤ j → W.smul s j t ∈ iterProdSpan W S)
    {u : 𝒱} (hu : u ∈ iterProdSpan W S) (n : ℤ) {v : 𝒱} (hv : v ∈ iterProdSpan W S) :
    W.smul u n v ∈ iterProdSpan W S := by
  refine Submodule.span_induction
    (p := fun u _ => W.smul u n v ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ hu
  · intro w hw
    refine Submodule.span_induction
      (p := fun v _ => W.smul w n v ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ hv
    · intro y hy
      obtain ⟨pw, hpw⟩ := isIterProd_exists_grading W hS hw
      obtain ⟨qy, hqy⟩ := isIterProd_exists_grading W hS hy
      by_cases hw0 : w = 0
      · rw [hw0, PreVertexAlgebra.smul_zero_left]; exact zero_mem _
      by_cases hy0 : y = 0
      · rw [hy0, W.toPreVertexAlgebra.smul_zero_right]; exact zero_mem _
      have hpw0 : (0 : ℤ) ≤ pw := by
        by_contra h
        push_neg at h
        refine hw0 ?_
        rw [W.positivity pw h] at hpw
        exact (Submodule.mem_bot ℂ).mp hpw
      have hqy0 : (0 : ℤ) ≤ qy := by
        by_contra h
        push_neg at h
        refine hy0 ?_
        rw [W.positivity qy h] at hqy
        exact (Submodule.mem_bot ℂ).mp hqy
      exact prodLevel_all W S hS hpair (pw + qy).toNat pw qy (by omega)
        w (Submodule.subset_span hw) hpw y (Submodule.subset_span hy) hqy n
    · simp only [W.toPreVertexAlgebra.smul_zero_right]; exact zero_mem _
    · intro a b _ _ ha hb
      simp only [W.toPreVertexAlgebra.smul_add_right]
      exact add_mem ha hb
    · intro c a _ ha
      simp only [W.toPreVertexAlgebra.smul_smul_right]
      exact Submodule.smul_mem _ c ha
  · simp only [PreVertexAlgebra.smul_zero_left]; exact zero_mem _
  · intro a b _ _ ha hb
    simp only [PreVertexAlgebra.smul_add_left]
    exact add_mem ha hb
  · intro c a _ ha
    simp only [PreVertexAlgebra.smul_smul_left]
    exact Submodule.smul_mem _ c ha

/-! ## §4  The `(ω, ω)` row is free -/

/-- **The conformal self-OPE closes for free**: in any VOA whose generating set contains the
conformal vector, `ω₍ⱼ₎ω ∈ iterProdSpan W S` for every `j ≥ 0`.

`j = 0`: `ω₍₀₎ω = L₋₁ω = Tω = ω₍₋₂₎𝟙`, a word.  `j = 1`: `L₀ω = 2ω`.  `j = 2`: `L₁ω = 0` and
`j = 3`: `L₂ω = ((2³−2)/12·c)·𝟙`, both read off the Virasoro bracket `[Lⱼ₋₁, L₋₂]` on the vacuum.
`j ≥ 4`: the product sits in a negative graded piece (`wt ω + wt ω = 4`). -/
theorem conformal_smul_conformal_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hω : W.conformalVector ∈ S) (j : ℤ) (hj : 0 ≤ j) :
    W.smul W.conformalVector j W.conformalVector ∈ iterProdSpan W S := by
  have hLsmul : ∀ (k : ℤ) (x : 𝒱), W.L k x = W.smul W.conformalVector (k + 1) x :=
    fun _ _ => rfl
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j from by omega)
    with rfl | rfl | rfl | rfl | h4
  · -- j = 0 : ω₍₀₎ω = Tω = ω₍₋₂₎𝟙
    have hc := creation_pow W W.conformalVector 1
    rw [show (-((1 : ℕ) : ℤ) - 1) = -2 from by norm_num] at hc
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one] at hc
    have hT : W.smul W.conformalVector 0 W.conformalVector
        = W.toPreVertexAlgebra.T W.conformalVector := by
      rw [T_eq_Lneg1, hLsmul]
      norm_num
    rw [hT, ← hc]
    exact Submodule.subset_span
      (IsIterProd.step _ hω 2 (by norm_num) _ IsIterProd.vacuum)
  · -- j = 1 : ω₍₁₎ω = L₀ω = 2ω
    have h := W.L_zero_grading W.conformalVector W.conformal_mem
    rw [hLsmul] at h
    norm_num at h
    rw [h]
    exact Submodule.smul_mem _ _ (subset_iterProdSpan W S hω)
  · -- j = 2 : ω₍₂₎ω = L₁ω = 0
    have hbr := W.L_virasoro 1 (-2)
    rw [if_neg (by norm_num : ¬(1 + -2 : ℤ) = 0), add_zero, Ring.lie_def] at hbr
    have happ := DFunLike.congr_fun hbr W.vacuum
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at happ
    simp only [hLsmul] at happ
    norm_num at happ
    rw [W.toPreVertexAlgebra.smul_vacuum_nonneg _ (by norm_num : (0 : ℤ) ≤ 2),
      W.toPreVertexAlgebra.smul_zero_right, sub_zero] at happ
    rw [happ]
    exact zero_mem _
  · -- j = 3 : ω₍₃₎ω = L₂ω = (scalar)·𝟙
    have hbr := W.L_virasoro 2 (-2)
    rw [if_pos (by norm_num : (2 + -2 : ℤ) = 0), Ring.lie_def] at hbr
    have happ := DFunLike.congr_fun hbr W.vacuum
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply] at happ
    simp only [hLsmul] at happ
    norm_num at happ
    rw [W.toPreVertexAlgebra.smul_vacuum_nonneg _ (by norm_num : (0 : ℤ) ≤ 3),
      W.toPreVertexAlgebra.smul_vacuum_nonneg _ (by norm_num : (0 : ℤ) ≤ 1),
      W.toPreVertexAlgebra.smul_zero_right, sub_zero, smul_zero, zero_add] at happ
    rw [happ]
    exact Submodule.smul_mem _ _ (vacuum_mem_iterProdSpan W S)
  · -- j ≥ 4 : weight
    rw [smul_grading_neg_eq_zero W W.conformal_mem W.conformal_mem
      (show (2 : ℤ) + 2 ≤ j from by omega)]
    exact zero_mem _

/-! ## §5  Translation, `L₀`, and the skew transport

Three more general facts that shrink the OPE table further:

* the span is stable under the translation operator `T = L₋₁` (`[T, s₍₋ₘ₎] = m·s₍₋ₘ₋₁₎`, an
  `S`-step) — so `ω₍₀₎x = Tx ∈ T` for every `x ∈ T`, with no hypothesis at all;
* the span is stable under `L₀` (words are homogeneous, `L₀` is scalar on them) — so
  `ω₍₁₎x ∈ T`;
* **skew transport**: `u₍ₙ₎v = ∑ⱼ ±(1/j!)·Tʲ(v₍ₙ₊ⱼ₎u)` (`Core.SkewSymmetry.skew_mode`), so the
  membership of a product follows from the memberships of the *opposite* products at modes
  `≥ n`.  In particular the whole `(g, ω)` column of an OPE table follows from its `(ω, g)` row.
-/

/-- **The span is translation stable**: `L₋₁(T) ⊆ T`.  Induction on the word:
`[L₋₁, s₍₋ₘ₎] = m·s₍₋ₘ₋₁₎` (`L_comm_mode`), and both `s₍₋ₘ₎` and `s₍₋ₘ₋₁₎` are `S`-steps. -/
theorem L_neg_one_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    {x : 𝒱} (hx : x ∈ iterProdSpan W S) : W.L (-1) x ∈ iterProdSpan W S := by
  refine Submodule.span_induction
    (p := fun x _ => W.L (-1) x ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ hx
  · intro w hw
    induction hw with
    | vacuum =>
        rw [L_neg_one_vacuum]
        exact zero_mem _
    | step s hs m hm y hy ih =>
        have hc := DFunLike.congr_fun (L_comm_mode W s (-m)) y
        rw [Ring.lie_def] at hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hc
        simp only [← PreVertexAlgebra.smul_def] at hc
        -- hc : L₋₁(s₍₋ₘ₎y) − s₍₋ₘ₎(L₋₁y) = m • s₍₋ₘ₋₁₎y
        rw [eq_add_of_sub_eq hc]
        refine add_mem (zsmul_mem ?_ _) ?_
        · have h := smul_mem_iterProdSpan W S hs (show (1 : ℤ) ≤ m + 1 from by omega)
            (Submodule.subset_span hy)
          rwa [show -(m + 1) = -m - 1 from by ring] at h
        · exact smul_mem_iterProdSpan W S hs hm ih
  · simp only [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    simp only [map_add]
    exact add_mem ha hb
  · intro c a _ ha
    simp only [map_smul]
    exact Submodule.smul_mem _ c ha

/-- The span is stable under every power of the translation operator `T`. -/
theorem T_pow_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱) (j : ℕ) :
    ∀ {x : 𝒱}, x ∈ iterProdSpan W S → (W.toPreVertexAlgebra.T ^ j) x ∈ iterProdSpan W S := by
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih =>
      intro x hx
      rw [pow_succ, Module.End.mul_apply]
      refine ih ?_
      rw [T_eq_Lneg1]
      exact L_neg_one_mem_iterProdSpan W S hx

/-- **The span is `L₀`-stable** (words are homogeneous and `L₀` acts on them by a scalar). -/
theorem L_zero_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d)
    {x : 𝒱} (hx : x ∈ iterProdSpan W S) : W.L 0 x ∈ iterProdSpan W S := by
  refine Submodule.span_induction
    (p := fun x _ => W.L 0 x ∈ iterProdSpan W S) ?_ ?_ ?_ ?_ hx
  · intro w hw
    obtain ⟨k, hk⟩ := isIterProd_exists_grading W hS hw
    rw [W.L_zero_grading w hk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hw)
  · simp only [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    simp only [map_add]
    exact add_mem ha hb
  · intro c a _ ha
    simp only [map_smul]
    exact Submodule.smul_mem _ c ha

/-- `ω₍₀₎x = L₋₁x = Tx ∈ T` for every `x ∈ T` — no hypothesis needed. -/
theorem conformal_smul_zero_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    {x : 𝒱} (hx : x ∈ iterProdSpan W S) :
    W.smul W.conformalVector 0 x ∈ iterProdSpan W S :=
  L_neg_one_mem_iterProdSpan W S hx

/-- `ω₍₁₎x = L₀x ∈ T` for every `x ∈ T`. -/
theorem conformal_smul_one_mem_iterProdSpan (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hS : ∀ s ∈ S, ∃ d : ℤ, 1 ≤ d ∧ s ∈ W.grading d)
    {x : 𝒱} (hx : x ∈ iterProdSpan W S) :
    W.smul W.conformalVector 1 x ∈ iterProdSpan W S :=
  L_zero_mem_iterProdSpan W S hS hx

/-- **Skew transport**: `u₍ₙ₎v ∈ T` follows from `v₍ₖ₎u ∈ T` for all `k ≥ n`, by the
skew-symmetry mode formula and translation stability of the span.  In particular the `(g, ω)`
column of a generator OPE table follows from its `(ω, g)` row. -/
theorem smul_mem_iterProdSpan_of_skew (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (u v : 𝒱) (n : ℤ) (h : ∀ k : ℤ, n ≤ k → W.smul v k u ∈ iterProdSpan W S) :
    W.smul u n v ∈ iterProdSpan W S := by
  rw [skew_mode W u v n]
  refine finsum_mem_submodule_pd _ _ (fun j => ?_)
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
  have hv : (W.Y v) (-n - 1 - (j : ℤ)) u = W.smul v (n + (j : ℤ)) u := by
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show (-(n + (j : ℤ)) - 1 : ℤ) = -n - 1 - (j : ℤ) from by ring]
  rw [hv]
  exact T_pow_mem_iterProdSpan W S j (h (n + (j : ℤ)) (by omega))

end VOA
