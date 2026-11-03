/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.C2Extraction

/-!
# High degrees fall into `C₂(𝒱)`  (Buhl 2002, Remark 3.5)

Buhl's spanning-set argument rests on three constants: `B = max wt X`, the degree `N` beyond
which `⊕_{i ≥ N} 𝒱ᵢ ⊆ C₂(𝒱)`, and `Q = max{N, 2B−1} + 1`.  The middle one is stated without
proof in his Remark 3.5; it is proved here.

## The mechanism

`O₂ W = C₂(𝒱)` is a **graded** submodule: the degree-`n` projection `piHom W n` maps it to
itself (`piHom_maps_O₂`).  So if `𝒱ₙ ⊄ O₂` for infinitely many degrees `n`, picking a witness
`xₙ ∈ 𝒱ₙ \ O₂` in each gives classes `[xₙ] ∈ A₂(𝒱)` that are **linearly independent** — a
vanishing combination is killed degree by degree by `piHom` — contradicting
`C₂`-cofiniteness (`dim A₂(𝒱) < ∞`).

## Contents

* `mk₂_linearIndependent_of_notMem` — classes of witnesses in distinct degrees are independent.
* **`exists_grading_le_O₂`** — `C2Cofinite W → ∃ N : ℕ, ∀ n ≥ N, 𝒱ₙ ≤ O₂ W`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- Witnesses in pairwise distinct degrees have linearly independent `A₂(𝒱)`-classes. -/
theorem mk₂_linearIndependent_of_notMem (W : VertexOperatorAlgebra 𝒱) {ι : Type*}
    (d : ι → ℤ) (hd : Function.Injective d) (x : ι → 𝒱)
    (hx : ∀ i, x i ∈ W.grading (d i)) (hxO : ∀ i, x i ∉ O₂ W) :
    LinearIndependent ℂ (fun i => mk₂ W (x i)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  -- `Σ_{k ∈ s} c k • x k ∈ O₂ W`
  have hmem : (∑ k ∈ s, c k • x k) ∈ O₂ W := by
    have : mk₂ W (∑ k ∈ s, c k • x k) = 0 := by
      rw [map_sum]
      simpa only [map_smul] using hc
    rwa [mk₂, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  -- project to degree `d j`
  have hproj : piHom W (d j) (∑ k ∈ s, c k • x k) = c j • x j := by
    rw [map_sum]
    rw [Finset.sum_eq_single j (fun k _ hkj => ?_) (fun hjs => absurd hj hjs)]
    · rw [map_smul, piHom_of_mem W (hx j)]
    · rw [map_smul, piHom_of_mem_ne W (fun hcon => hkj (hd hcon)) (hx k), smul_zero]
  have hO : c j • x j ∈ O₂ W := by
    rw [← hproj]; exact piHom_maps_O₂ W (d j) hmem
  by_contra hcj
  exact hxO j (by
    have := (O₂ W).smul_mem (c j)⁻¹ hO
    rwa [smul_smul, inv_mul_cancel₀ hcj, one_smul] at this)

/-- **Buhl, Remark 3.5.**  For a `C₂`-cofinite VOA all sufficiently high graded pieces lie
in `C₂(𝒱) = O₂ W`. -/
theorem exists_grading_le_O₂ (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → W.grading n ≤ O₂ W := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the bad degrees form an unbounded, hence infinite, set
  have hunb : ∀ N : ℕ, ∃ n ∈ {n : ℤ | ¬ (W.grading n ≤ O₂ W)}, (N : ℤ) ≤ n := by
    intro N
    obtain ⟨n, hn, hle⟩ := hcon N
    exact ⟨n, hle, hn⟩
  have hinf : {n : ℤ | ¬ (W.grading n ≤ O₂ W)}.Infinite := by
    intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨n, hnS, hnle⟩ := hunb (B.toNat + 1)
    have h1 : n ≤ B := hB hnS
    have h3 : B ≤ (B.toNat : ℤ) := Int.self_le_toNat B
    have h2 : ((B.toNat + 1 : ℕ) : ℤ) ≤ n := hnle
    push_cast at h2
    omega
  -- an injection `ℕ ↪ S` gives infinitely many independent classes
  obtain ⟨e⟩ : Nonempty (ℕ ↪ {n : ℤ | ¬ (W.grading n ≤ O₂ W)}) := ⟨hinf.natEmbedding⟩
  have hwit : ∀ k : ℕ, ∃ y : 𝒱, y ∈ W.grading ((e k : ℤ)) ∧ y ∉ O₂ W := by
    intro k
    have hmem : ¬ (W.grading ((e k : ℤ)) ≤ O₂ W) := (e k).2
    rw [SetLike.le_def] at hmem
    push_neg at hmem
    exact hmem
  choose x hx hxO using hwit
  have hdinj : Function.Injective (fun k : ℕ => ((e k : ℤ))) := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  have hli := mk₂_linearIndependent_of_notMem W (fun k : ℕ => ((e k : ℤ))) hdinj x hx hxO
  -- contradiction with finite-dimensionality: too many independent vectors
  haveI : FiniteDimensional ℂ (A₂ W) := hC2
  set n₀ : ℕ := Module.finrank ℂ (A₂ W) with hn₀
  have hcomp : LinearIndependent ℂ (fun i : Fin (n₀ + 1) => mk₂ W (x (i : ℕ))) :=
    hli.comp (fun i : Fin (n₀ + 1) => (i : ℕ)) (fun a b hab => Fin.ext hab)
  have hcard := hcomp.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

end VOA
