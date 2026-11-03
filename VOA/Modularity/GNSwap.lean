/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNStep

/-!
# Gaberdiel–Neitzke Prop. 8, layer 6: swapping two letters drops the grade (Lemma 5)

This is the engine of GN's `N = 0` base case — the sorting step — and of the `m ≠ 0` sub-case of the
induction step.  Both work by moving a letter past its neighbour; GN Lemma 5 says the error is a
word of **strictly lower grade**.

The identity is the banked commutator formula `Core.Reconstruction.mode_commutator`:
`⁅u₍ₐ₎, v₍ᵦ₎⁆ = ∑_j C(a, j)·(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎`.  Each term replaces the *two* letters `u, v`, of total
weight `wᵤ + w_v`, by the *single* letter `u₍ⱼ₎v` of weight `wᵤ + w_v − j − 1 ≤ wᵤ + w_v − 1` — so the
grade drops by at least one.  Terms whose weight would be negative vanish by `positivity`.

## Main result

* `gnWord_swap_sub_mem` — `gnWord (p :: q :: rest) − gnWord (q :: p :: rest) ∈ ℋ^{(G)}`
  whenever `wₚ + w_q + grade rest ≤ G + 1`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Layer 6 of Prop. 8.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **GN Lemma 5 at word level: swapping two adjacent letters costs one unit of grade.** -/
theorem gnWord_swap_sub_mem (W : VertexOperatorAlgebra 𝒱) (p q : GNLetter 𝒱)
    (rest : List (GNLetter 𝒱)) (hOK : GNWordOK W (p :: q :: rest)) (G : ℕ)
    (hle : p.2.1 + q.2.1 + gnWordGrade rest ≤ G + 1) :
    gnWord W (p :: q :: rest) W.vacuum - gnWord W (q :: p :: rest) W.vacuum
      ∈ gnGradeFil W G := by
  classical
  set x : 𝒱 := gnWord W rest W.vacuum with hx
  have hrestOK : GNWordOK W rest := hOK.tail.tail
  have hpmem : p.1 ∈ W.grading (p.2.1 : ℤ) := hOK.head_mem
  have hqmem : q.1 ∈ W.grading (q.2.1 : ℤ) := hOK.tail.head_mem
  have hpidx : 1 ≤ p.2.2 := hOK.2 p (List.mem_cons_self ..)
  have hqidx : 1 ≤ q.2.2 := hOK.2 q (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- the difference is the commutator, applied to the sub-word
  have hdiff : gnWord W (p :: q :: rest) W.vacuum - gnWord W (q :: p :: rest) W.vacuum
      = ⁅mode (W.Y p.1) (-(p.2.2 : ℤ)), mode (W.Y q.1) (-(q.2.2 : ℤ))⁆ x := by
    rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    rw [gnWord_cons, gnWord_cons, gnWord_cons, gnWord_cons]
    rfl
  obtain ⟨M, hM⟩ := VertexOperatorAlgebra.mode_commutator W p.1 q.1 (-(p.2.2 : ℤ)) (-(q.2.2 : ℤ))
  rw [hdiff, hM, LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  -- the single replacement letter `p.1₍ⱼ₎q.1`
  set c : 𝒱 := W.smul p.1 ((j : ℕ) : ℤ) q.1 with hc
  have hcmem : c ∈ W.grading ((p.2.1 : ℤ) + (q.2.1 : ℤ) - ((j : ℕ) : ℤ) - 1) :=
    W.smul_mem_grading hpmem hqmem _
  by_cases hneg : (p.2.1 : ℤ) + (q.2.1 : ℤ) - ((j : ℕ) : ℤ) - 1 < 0
  · -- the replacement letter has negative weight, so it vanishes
    rw [W.positivity _ hneg, Submodule.mem_bot] at hcmem
    have hz : mode (W.Y c) (-(p.2.2 : ℤ) + -(q.2.2 : ℤ) - ((j : ℕ) : ℤ)) x = 0 := by
      show W.smul c (-(p.2.2 : ℤ) + -(q.2.2 : ℤ) - ((j : ℕ) : ℤ)) x = 0
      rw [hcmem, W.smul_zero_left]
    rw [hz]
    exact Submodule.zero_mem _
  · push_neg at hneg
    obtain ⟨w, hw⟩ : ∃ w : ℕ, ((w : ℤ)) = (p.2.1 : ℤ) + (q.2.1 : ℤ) - ((j : ℕ) : ℤ) - 1 :=
      ⟨((p.2.1 : ℤ) + (q.2.1 : ℤ) - ((j : ℕ) : ℤ) - 1).toNat, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((k : ℤ)) = (p.2.2 : ℤ) + (q.2.2 : ℤ) + ((j : ℕ) : ℤ) :=
      ⟨((p.2.2 : ℤ) + (q.2.2 : ℤ) + ((j : ℕ) : ℤ)).toNat, by omega⟩
    have hword : mode (W.Y c) (-(p.2.2 : ℤ) + -(q.2.2 : ℤ) - ((j : ℕ) : ℤ)) x
        = gnWord W ((c, w, k) :: rest) W.vacuum := by
      rw [gnWord_cons, ← hx]
      show mode (W.Y c) (-(p.2.2 : ℤ) + -(q.2.2 : ℤ) - ((j : ℕ) : ℤ)) x
        = W.smul c (-(k : ℤ)) x
      rw [W.toPreVertexAlgebra.smul_def, hk]
      congr 1
      ring
    rw [hword]
    refine word_mem_gnGradeFil W ⟨?_, ?_⟩ ?_
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · show c ∈ W.grading ((w : ℤ))
        rw [hw]
        exact hcmem
      · exact hrestOK.1 r hr'
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · show 1 ≤ k
        have h1 : (1 : ℤ) ≤ (k : ℤ) := by omega
        exact_mod_cast h1
      · exact hrestOK.2 r hr'
    · rw [gnWordGrade_cons]
      have hwle : w + 1 ≤ p.2.1 + q.2.1 := by
        have h2 : (w : ℤ) + 1 ≤ (p.2.1 : ℤ) + (q.2.1 : ℤ) := by omega
        exact_mod_cast h2
      show w + gnWordGrade rest ≤ G
      omega

/-! ## Context lemmas: applying the swap inside a word -/

theorem gnWord_append (W : VertexOperatorAlgebra 𝒱) :
    ∀ (l₁ l₂ : List (GNLetter 𝒱)) (x : 𝒱),
      gnWord W (l₁ ++ l₂) x = gnWord W l₁ (gnWord W l₂ x) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ x; rfl
  | cons p l ih => intro l₂ x; rw [List.cons_append, gnWord_cons, gnWord_cons, ih]

theorem gnWordGrade_append (l₁ l₂ : List (GNLetter 𝒱)) :
    gnWordGrade (l₁ ++ l₂) = gnWordGrade l₁ + gnWordGrade l₂ := by
  rw [gnWordGrade, gnWordGrade, gnWordGrade, List.map_append, List.sum_append]

theorem gnWord_add (W : VertexOperatorAlgebra 𝒱) :
    ∀ (l : List (GNLetter 𝒱)) (a b : 𝒱),
      gnWord W l (a + b) = gnWord W l a + gnWord W l b := by
  intro l
  induction l with
  | nil => intro a b; rfl
  | cons p l ih => intro a b; rw [gnWord_cons, ih, W.smul_add_right, gnWord_cons, gnWord_cons]

theorem gnWord_smul (W : VertexOperatorAlgebra 𝒱) :
    ∀ (l : List (GNLetter 𝒱)) (c : ℂ) (a : 𝒱),
      gnWord W l (c • a) = c • gnWord W l a := by
  intro l
  induction l with
  | nil => intro c a; rfl
  | cons p l ih => intro c a; rw [gnWord_cons, ih, W.smul_smul_right, gnWord_cons]

theorem gnWord_sub (W : VertexOperatorAlgebra 𝒱) (l : List (GNLetter 𝒱)) (a b : 𝒱) :
    gnWord W l (a - b) = gnWord W l a - gnWord W l b := by
  have h := gnWord_add W l (a - b) b
  rw [sub_add_cancel] at h
  rw [h]
  abel

theorem gnWord_zero (W : VertexOperatorAlgebra 𝒱) :
    ∀ l : List (GNLetter 𝒱), gnWord W l 0 = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons p l ih => rw [gnWord_cons, ih, W.smul_zero_right]

/-- **The filtration is stable under prepending a word, and the grades add.**  This is what
lets the swap lemma be applied *inside* a word rather than only at its head. -/
theorem gnGradeFil_prepend (W : VertexOperatorAlgebra 𝒱) {pre : List (GNLetter 𝒱)}
    (hpre : GNWordOK W pre) {G : ℕ} {y : 𝒱} (hy : y ∈ gnGradeFil W G) :
    gnWord W pre y ∈ gnGradeFil W (gnWordGrade pre + G) := by
  refine Submodule.span_induction
    (p := fun y _ => gnWord W pre y ∈ gnGradeFil W (gnWordGrade pre + G)) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨l, hOK, hg, rfl⟩
    rw [← gnWord_append]
    refine word_mem_gnGradeFil W ⟨?_, ?_⟩ ?_
    · intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact hpre.1 r h
      · exact hOK.1 r h
    · intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact hpre.2 r h
      · exact hOK.2 r h
    · rw [gnWordGrade_append]
      omega
  · show gnWord W pre 0 ∈ gnGradeFil W (gnWordGrade pre + G)
    rw [gnWord_zero]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [gnWord_add]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [gnWord_smul]
    exact Submodule.smul_mem _ _ ha

/-- **The swap, inside a context.**  Exchanging two adjacent letters anywhere in a word costs
one unit of grade — the form GN's sorting step and his `m ≠ 0` sub-case consume. -/
theorem gnWord_swap_sub_mem_ctx (W : VertexOperatorAlgebra 𝒱) (pre : List (GNLetter 𝒱))
    (p q : GNLetter 𝒱) (rest : List (GNLetter 𝒱))
    (hpre : GNWordOK W pre) (hOK : GNWordOK W (p :: q :: rest)) (G : ℕ)
    (hpreG : gnWordGrade pre ≤ G)
    (hle : gnWordGrade pre + (p.2.1 + q.2.1 + gnWordGrade rest) ≤ G + 1) :
    gnWord W (pre ++ p :: q :: rest) W.vacuum - gnWord W (pre ++ q :: p :: rest) W.vacuum
      ∈ gnGradeFil W G := by
  have hswap := gnWord_swap_sub_mem W p q rest hOK (G - gnWordGrade pre) (by omega)
  have hpp := gnGradeFil_prepend W hpre hswap
  have hsub : gnWord W pre (gnWord W (p :: q :: rest) W.vacuum
      - gnWord W (q :: p :: rest) W.vacuum)
      = gnWord W (pre ++ p :: q :: rest) W.vacuum
        - gnWord W (pre ++ q :: p :: rest) W.vacuum := by
    rw [gnWord_sub, gnWord_append, gnWord_append]
  rw [hsub] at hpp
  exact gnGradeFil_mono W (by omega) hpp

end VOA
