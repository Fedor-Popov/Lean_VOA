/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.C2Extraction
import VOA.Modularity.SquareBracketWitt

/-!
# `C₂`-cofiniteness in the SQUARE bracket

Zhu's finiteness argument for the space of genus-one conformal blocks is run in the **square
bracket** vertex algebra `𝒱_[·]`, not the ordinary one: the block condition (ii)
(`Modularity.ZhuBlockConditions.zhuRecursion_neg_two`)

  `𝒵_M(a[−2]v) + Σ_{k ≥ 1} (2k−1)·G_{2k} ⋆ 𝒵_M(a[2k−2]v) = 0`

expresses a block on `a[−2]v` through its values on *square-bracket-lower* vectors.  So the
relevant finiteness of `𝒱` is `dim 𝒱 / C₂[𝒱] < ∞`, where

  `C₂[𝒱] = O₂sq W := span{ a[−2]v }`.

This file proves that ordinary `C₂`-cofiniteness gives it, with the **same** finite generating
family:

  `exists_homog_gen_sq_of_C2Cofinite` :
     `C2Cofinite W → ∃ g gen wt, … ∧ ⊤ = span (range gen ∪ {𝟙}) ⊔ O₂sq W`.

## The mechanism (triangularity)

`a[m]v = Σ_{i ≥ m} c(k,m,i)·a₍ᵢ₎v` with `c(k,m,m) = 1` (`sqBracketCoeffZ_of_lt`,
`sqBracketCoeffZ_diag'`).  At `m = −2` this reads

  `a[−2]v = a₍₋₂₎v + Σ_{i ≥ −1} c(k,−2,i)·a₍ᵢ₎v`,

and every correction term `a₍ᵢ₎v` with `i ≥ −1` is homogeneous of degree `≤ wt a + wt v`,
**strictly below** the degree `wt a + wt v + 1` of `a₍₋₂₎v`.  So a downward-closed induction on
the degree converts the ordinary decomposition `⊤ = span(gen ∪ {𝟙}) ⊔ O₂ W`
(`C2Extraction.exists_homog_gen_of_C2Cofinite`) into the square-bracket one.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The square-bracket `C₂` subspace -/

/-- **`C₂[𝒱] = O₂sq W`** — the span of the square-bracket products `a[−2]v` over homogeneous
`a ∈ 𝒱_p`. -/
def O₂sq (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ (p : ℕ) (a b : 𝒱), a ∈ W.grading (p : ℤ) ∧ x = vSqZ W a p (-2) b}

theorem sq_gen_mem_O₂sq (W : VertexOperatorAlgebra 𝒱) {p : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) (b : 𝒱) : vSqZ W a p (-2) b ∈ O₂sq W :=
  Submodule.subset_span ⟨p, a, b, ha, rfl⟩

/-! ## Triangularity: `a[−2]b − a₍₋₂₎b` is a combination of strictly lower degrees -/

/-- The correction term `a[−2]b − a₍₋₂₎b`, as an explicit `finsum` over the modes `i ≠ −2`. -/
noncomputable def sqDefect (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (p : ℕ) (b : 𝒱) : 𝒱 :=
  ∑ᶠ i : ℤ, (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • mode (W.Y a) i b

theorem sqDefect_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (p : ℕ) (b : 𝒱) :
    (Function.support fun i : ℤ =>
      (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • mode (W.Y a) i b).Finite := by
  refine Set.Finite.subset (sqModeZ_support_finite W a p (-2) b) (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi ⊢
  intro hc
  apply hi
  by_cases h2 : i = -2
  · rw [if_pos h2, zero_smul]
  · rw [if_neg h2, hc]

/-- **Triangularity of the square bracket at `m = −2`**:
`a[−2]b = a₍₋₂₎b + sqDefect`, the defect being supported on modes `i ≥ −1`. -/
theorem vSqZ_neg_two_eq (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (p : ℕ) (b : 𝒱) :
    vSqZ W a p (-2) b = mode (W.Y a) (-2) b + sqDefect W a p b := by
  rw [vSqZ_apply, sqDefect]
  have hsplit : ∀ i : ℤ, sqBracketCoeffZ p (-2) i • mode (W.Y a) i b
      = (if i = -2 then sqBracketCoeffZ p (-2) i • mode (W.Y a) i b else 0)
        + (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • mode (W.Y a) i b := by
    intro i
    by_cases h2 : i = -2
    · rw [if_pos h2, if_pos h2, zero_smul, add_zero]
    · rw [if_neg h2, if_neg h2, zero_add]
  rw [finsum_congr hsplit]
  have hfin1 : (Function.support fun i : ℤ =>
      (if i = -2 then sqBracketCoeffZ p (-2) i • mode (W.Y a) i b else 0)).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (-2 : ℤ)) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hne
    exact hi (if_neg hne)
  rw [finsum_add_distrib hfin1 (sqDefect_support_finite W a p b)]
  congr 1
  rw [finsum_eq_single _ (-2 : ℤ) (fun i hi => if_neg hi), if_pos rfl,
    sqBracketCoeffZ_diag' p (-2), one_smul]

/-! ## The degree induction -/

section Induction

variable (W : VertexOperatorAlgebra 𝒱)

/-- The defect lies in any submodule containing all strictly lower graded pieces. -/
theorem sqDefect_mem_of_lower {p q n : ℤ} {a b : 𝒱} (ha : a ∈ W.grading p) (hb : b ∈ W.grading q)
    (hpq : p + q + 1 = n) (hp : 0 ≤ p) (T : Submodule ℂ 𝒱)
    (hT : ∀ m : ℤ, m < n → W.grading m ≤ T) :
    sqDefect W a p.toNat b ∈ T := by
  rw [sqDefect]
  refine finsum_mem_submodule_pd _ _ (fun i => ?_)
  by_cases h2 : i = -2
  · rw [if_pos h2, zero_smul]; exact Submodule.zero_mem _
  rw [if_neg h2]
  rcases lt_or_ge i (-2 : ℤ) with hlt | hge
  · rw [sqBracketCoeffZ_of_lt _ hlt, zero_smul]; exact Submodule.zero_mem _
  · -- `i ≥ −1`: the mode lands in degree `p + q − i − 1 ≤ p + q < n`
    have hi : (-1 : ℤ) ≤ i := by omega
    refine Submodule.smul_mem _ _ ?_
    have hmem : W.smul a i b ∈ W.grading (p + q - i - 1) := W.smul_mem_grading ha hb i
    exact hT _ (by omega) hmem

/-- **The degree induction.**  If the finite family `S` spans `𝒱` modulo `O₂ W`, it also
spans it modulo `O₂sq W`. -/
theorem grading_le_span_sup_O₂sq (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) (n : ℤ) :
    W.grading n ≤ Submodule.span ℂ S ⊔ O₂sq W := by
  classical
  set T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ O₂sq W with hTdef
  -- strong induction on `n.toNat`, with the negative degrees trivial
  rcases lt_or_ge n 0 with hneg | hnn
  · rw [W.positivity n hneg]; exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hT : ∀ m : ℤ, m < (N : ℤ) → W.grading m ≤ T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · rw [W.positivity m hm0]; exact bot_le
      · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
        exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
    -- part (i): `𝒱ₙ ≤ span S ⊔ (O₂ ⊓ 𝒱ₙ)`
    refine le_trans (grading_le_span_sup_O₂_inf W S hShom htop (N : ℤ)) ?_
    refine sup_le le_sup_left ?_
    refine le_trans (O₂_inf_grading_le_span_deg W (N : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    by_cases hg0 : W.smul a (-2) b = 0
    · rw [hg0]; exact Submodule.zero_mem _
    have hp0 : 0 ≤ p := by
      by_contra hc; push_neg at hc
      exact hg0 (by rw [show a = 0 by
        rw [W.positivity p hc, Submodule.mem_bot] at ha; exact ha, W.smul_zero_left])
    have hexp := vSqZ_neg_two_eq W a p.toNat b
    have hpcast : ((p.toNat : ℕ) : ℤ) = p := by omega
    have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by rwa [hpcast]
    have hstep : W.smul a (-2) b = vSqZ W a p.toNat (-2) b - sqDefect W a p.toNat b := by
      rw [hexp]
      show W.smul a (-2) b = mode (W.Y a) (-2) b + sqDefect W a p.toNat b
        - sqDefect W a p.toNat b
      rw [add_sub_cancel_right]
      rfl
    rw [hstep]
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.mem_sup_right (sq_gen_mem_O₂sq W ha' b)
    · exact sqDefect_mem_of_lower W ha hb hpq hp0 T hT

/-- **Square-bracket `C₂`-cofiniteness.**  A `C₂`-cofinite VOA has a finite family of
homogeneous generators of positive weight spanning `𝒱` modulo `ℂ𝟙 + C₂[𝒱]` — Zhu's finiteness
input for the genus-one block space. -/
theorem exists_homog_gen_sq_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂sq W := by
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨g, gen, wt, hwt, hgen, le_antisymm ?_ le_top⟩
  have hShom : ∀ s ∈ (Set.range gen ∪ {W.vacuum} : Set 𝒱), IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨n, hx⟩
  exact grading_le_span_sup_O₂sq W _ hShom hdec n hx

end Induction

end VOA
