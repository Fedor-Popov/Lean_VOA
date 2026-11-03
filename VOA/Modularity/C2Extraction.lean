/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.FiniteGenerationProof

/-!
# Extracting a finite *homogeneous, positive-weight* generating family from `C₂`-cofiniteness

`C2Cofinite W` says `A₂(𝒱) = 𝒱 ⧸ O₂(𝒱)` is finite-dimensional.  This file turns that abstract
finiteness into the concrete datum consumed by the Buhl/ordered-span machinery
(`Modularity.OrderedSpan`, `Modularity.BuhlSpanningProof`): a finite family
`gen : Fin g → 𝒱` of **homogeneous** vectors of **strictly positive** conformal weights
`wt : Fin g → ℕ` with

  `⊤ = span ℂ (range gen ∪ {𝟙}) ⊔ O₂ W`.

The route is elementary:

* lift a finite spanning set of `A₂(𝒱)` along the surjection `(O₂ W).mkQ` (`comap`/`map` of the
  quotient map, `ker (O₂ W).mkQ = O₂ W`);
* replace each lift by finitely many homogeneous vectors, using
  `span_homog_eq_top` (`Modules.FiniteGeneration`) and `Submodule.mem_span_finite_of_mem_span`;
* split the resulting finite homogeneous set by degree: negative degrees give `0`
  (`W.positivity`), degree `0` lands in `ℂ ∙ 𝟙` (`W.vacuum_grade`), and the degrees `≥ 1` are
  the kept generators, recorded as pairs `(x, wt) ∈ Finset (𝒱 × ℕ)` and enumerated by
  `Finset.equivFin`.

## Status
`sorry`-free / axiom-free.

## References
* Gannon §5.3.2, Def. 5.3.5, 5.3.11a; Zhu [574]; Buhl; Gaberdiel–Neitzke.
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Lifting a finite `A₂(𝒱)`-spanning set.**  If `A₂(𝒱) = 𝒱 ⧸ O₂(𝒱)` is finite-dimensional,
there is a finite `T ⊆ 𝒱` with `⊤ = span ℂ T ⊔ O₂ W`. -/
private theorem exists_finset_span_sup_O₂ (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ T : Finset 𝒱, (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ O₂ W := by
  classical
  have hfin : Module.Finite ℂ (A₂ W) := hC2
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfin
  have hsurj : Function.Surjective (O₂ W).mkQ := Submodule.mkQ_surjective (O₂ W)
  have hlift : ∀ a : A₂ W, (O₂ W).mkQ (Function.surjInv hsurj a) = a :=
    fun a => Function.surjInv_eq hsurj a
  refine ⟨S.image (Function.surjInv hsurj), le_antisymm ?_ le_top⟩
  intro x _
  have hle : Submodule.span ℂ (S : Set (A₂ W)) ≤
      Submodule.map (O₂ W).mkQ
        (Submodule.span ℂ ((S.image (Function.surjInv hsurj) : Finset 𝒱) : Set 𝒱)) := by
    rw [Submodule.span_le]
    intro a ha
    exact ⟨Function.surjInv hsurj a, Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp ha))), hlift a⟩
  have hxs : (O₂ W).mkQ x ∈ Submodule.span ℂ (S : Set (A₂ W)) := by rw [hS]; trivial
  obtain ⟨y, hyN, hyx⟩ := hle hxs
  have hker : x - y ∈ LinearMap.ker (O₂ W).mkQ := by
    simp only [LinearMap.mem_ker, map_sub, hyx, sub_self]
  rw [Submodule.ker_mkQ] at hker
  have hxeq : x = y + (x - y) := by abel
  rw [hxeq]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hyN) (Submodule.mem_sup_right hker)

/-- **`C₂`-cofinite ⟹ a finite homogeneous positive-weight generating family mod `O₂`.**
There are `g : ℕ`, homogeneous `gen : Fin g → 𝒱` of weights `wt : Fin g → ℕ` with `wt i ≥ 1`,
such that `⊤ = span ℂ (range gen ∪ {𝟙}) ⊔ O₂ W` (Gannon §5.3.2; the input to Buhl's
ordered-monomial spanning). -/
theorem exists_homog_gen_of_C2Cofinite {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_span_sup_O₂ W hC2
  -- Step 1: replace each lift by finitely many homogeneous vectors.
  have hall : ∀ y : 𝒱, ∃ F : Finset 𝒱,
      (↑F : Set 𝒱) ⊆ {x : 𝒱 | IsHomog W x} ∧ y ∈ Submodule.span ℂ (F : Set 𝒱) := by
    intro y
    have hy : y ∈ Submodule.span ℂ {x : 𝒱 | IsHomog W x} := by
      rw [span_homog_eq_top]; trivial
    exact Submodule.mem_span_finite_of_mem_span hy
  choose F hFsub hFmem using hall
  set U : Finset 𝒱 := T.biUnion F with hU
  have hUhom : ∀ x ∈ U, IsHomog W x := by
    intro x hx
    rw [hU, Finset.mem_biUnion] at hx
    obtain ⟨y, _, hxy⟩ := hx
    exact hFsub y (Finset.mem_coe.mpr hxy)
  have hTU : (T : Set 𝒱) ⊆ (Submodule.span ℂ (U : Set 𝒱) : Set 𝒱) := by
    intro y hy
    refine Submodule.span_mono ?_ (hFmem y)
    intro z hz
    exact Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨y, Finset.mem_coe.mp hy, Finset.mem_coe.mp hz⟩)
  have hUtop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (U : Set 𝒱) ⊔ O₂ W := by
    refine le_antisymm ?_ le_top
    rw [hT]
    exact sup_le_sup_right (Submodule.span_le.mpr hTU) _
  -- Step 2: record a degree for every vector.
  have hdegex : ∀ x : 𝒱, ∃ n : ℤ, IsHomog W x → x ∈ W.grading n := by
    intro x
    by_cases h : IsHomog W x
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose deg hdeg using hdegex
  -- Step 3: keep the strictly positive degrees, as (vector, weight) pairs.
  set P : Finset (𝒱 × ℕ) :=
    (U.filter (fun x => 1 ≤ deg x)).image (fun x => (x, (deg x).toNat)) with hP
  have hPprop : ∀ p ∈ P, 1 ≤ p.2 ∧ p.1 ∈ W.grading (p.2 : ℤ) := by
    intro p hp
    rw [hP, Finset.mem_image] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [Finset.mem_filter] at hx
    obtain ⟨hxU, hx1⟩ := hx
    have hxg : x ∈ W.grading (deg x) := hdeg x (hUhom x hxU)
    refine ⟨by simpa using (by omega : 1 ≤ (deg x).toNat), ?_⟩
    have hcast : (((deg x).toNat : ℕ) : ℤ) = deg x := Int.toNat_of_nonneg (by omega)
    simpa [hcast] using hxg
  have hvac : W.grading 0 = Submodule.span ℂ ({W.vacuum} : Set 𝒱) := W.vacuum_grade
  have hUle : Submodule.span ℂ (U : Set 𝒱) ≤
      Submodule.span ℂ ((fun p : 𝒱 × ℕ => p.1) '' (P : Set (𝒱 × ℕ)) ∪ {W.vacuum}) := by
    rw [Submodule.span_le]
    intro x hxU
    have hxU' : x ∈ U := Finset.mem_coe.mp hxU
    have hxg : x ∈ W.grading (deg x) := hdeg x (hUhom x hxU')
    rcases lt_trichotomy (deg x) 0 with h | h | h
    · have hx0 : x = 0 := by
        rw [W.positivity _ h, Submodule.mem_bot] at hxg; exact hxg
      rw [hx0]; exact Submodule.zero_mem _
    · rw [h, hvac] at hxg
      refine Submodule.span_mono (fun z hz => Or.inr hz) hxg
    · have h1 : (1 : ℤ) ≤ deg x := by omega
      refine Submodule.subset_span (Or.inl ⟨(x, (deg x).toNat), ?_, rfl⟩)
      exact Finset.mem_coe.mpr
        (by rw [hP]; exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hxU', h1⟩))
  -- Step 4: enumerate `P`.
  have e : {x // x ∈ P} ≃ Fin P.card := P.equivFin
  refine ⟨P.card, fun i => ((e.symm i : 𝒱 × ℕ)).1, fun i => ((e.symm i : 𝒱 × ℕ)).2,
    fun i => (hPprop _ (e.symm i).2).1, fun i => (hPprop _ (e.symm i).2).2, ?_⟩
  have hrange : Set.range (fun i : Fin P.card => ((e.symm i : 𝒱 × ℕ)).1)
      = (fun p : 𝒱 × ℕ => p.1) '' (P : Set (𝒱 × ℕ)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e.symm i : 𝒱 × ℕ), Finset.mem_coe.mpr (e.symm i).2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨e ⟨p, Finset.mem_coe.mp hp⟩, by simp⟩
  refine le_antisymm ?_ le_top
  rw [hUtop]
  refine sup_le_sup_right ?_ _
  rw [hrange]
  exact hUle

end VOA
