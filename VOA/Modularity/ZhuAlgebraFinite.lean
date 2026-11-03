/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanning
import VOA.Modules.ZhuVermaAnArchFiltrationFinal

/-!
# `C₂`-cofinite ⟹ `dim A(𝒱) < ∞`

`FiniteDimensional ℂ (A 𝒱)` is carried as a named hypothesis by *every* declaration in the
count — `Modularity.CuspFunctionalCount`, `Modularity.CuspPoint`, `Modularity.WedderburnAMod`,
`Modularity.SimpleAModFinite`, `Modularity.ZhuCount`.  This file **discharges it from
`C₂`-cofiniteness**, which the count already assumes anyway.

## The argument (Zhu Thm 2.1.1 + `C₂`-cofiniteness; cf. Abe–Buhl–Dong)

It is the *same* degree induction as `Modularity.BlockRelSpanning.grading_le_span_sup_blockRelSpan`,
with the deformed relation module `blockRelSpan W z` replaced by `O(𝒱)` itself — and it is strictly
easier, because no square-bracket expansion is involved.  The one VOA input is the banked
`circ_n_mem_O` at `n = 0`: for homogeneous `a ∈ 𝒱_M`,

  `a ∘ b = ∑_{i=0}^{M} C(M,i) · a₍ᵢ₋₂₎ b ∈ O(𝒱)`   (`circ_homogeneous`, `circ_n_mem_O`),

whose `i = 0` term is `a₍₋₂₎b` and whose `i ≥ 1` terms all have **strictly lower** conformal weight
(`wt a₍ᵢ₋₂₎b = M + wt b + 1 - i`).  So modulo `O(𝒱)` the whole of `C₂(𝒱) = O₂(𝒱)` is absorbed into
lower degrees, and the `C₂`-generators alone span `𝒱` modulo `O(𝒱)`.

Note there is **no `VacuumGradeZero` hypothesis**: the `M = 0` case needs no separate treatment,
since the correction sum is then empty and `a₍₋₂₎b = a ∘ b ∈ O(𝒱)` on the nose.

## Main results

* `smul_negTwo_mem_of_lower_O` — the one-step absorption;
* `grading_le_span_sup_O`, `span_sup_O_eq_top`, `exists_finset_span_sup_O`;
* `finiteDimensional_A_of_C2Cofinite` — `C2Cofinite 𝒱 → FiniteDimensional ℂ (A 𝒱)`, with the
  explicit bound `finrank ℂ (A 𝒱) ≤ g + 1` on the number of `C₂`-generators.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- **The one-step absorption.**  For homogeneous `a ∈ 𝒱_p` (`p ≥ 0`) and `b ∈ 𝒱_q`, the vector
`a₍₋₂₎b` lies in any subspace `T` that contains `O(𝒱)` and every grade strictly below
`p + q + 1`.  This is `circ W 0 a b ∈ O(𝒱)` with its `i = 0` term isolated. -/
theorem smul_negTwo_mem_of_lower_O {p q : ℤ} {a b : 𝒱} (ha : a ∈ W.grading p)
    (hb : b ∈ W.grading q) (hp : 0 ≤ p) (T : Submodule ℂ 𝒱) (hO : O W ≤ T)
    (hT : ∀ m : ℤ, m < p + q + 1 → W.grading m ≤ T) :
    W.smul a (-2) b ∈ T := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, p = (M : ℤ) := ⟨p.toNat, by omega⟩
  -- `circ W 0 a b = ∑_{i<M+1} C(M,i) • a₍ᵢ₋₂₎b`, and `circ W 0 a b ∈ O(𝒱)`.
  have hexp0 := circ_homogeneous W 0 ha b
  have hidx : (((M : ℤ) + ((0 : ℕ) : ℤ)).toNat + 1) = M + 1 := by simp
  rw [hidx] at hexp0
  have hsimp : ∀ i : ℕ,
      cbz ((M : ℤ) + ((0 : ℕ) : ℤ)) (i : ℤ) • W.smul a ((i : ℤ) - 2 * ((0 : ℕ) : ℤ) - 2) b
        = cbz ((M : ℤ)) (i : ℤ) • W.smul a ((i : ℤ) - 2) b := by
    intro i
    norm_num
  rw [Finset.sum_congr rfl (fun i _ => hsimp i), Finset.sum_range_succ'] at hexp0
  set R : 𝒱 := ∑ k ∈ Finset.range M,
      cbz ((M : ℤ)) (((k + 1 : ℕ) : ℤ)) • W.smul a (((k + 1 : ℕ) : ℤ) - 2) b with hR
  have hbot : cbz ((M : ℤ)) (((0 : ℕ) : ℤ)) • W.smul a (((0 : ℕ) : ℤ) - 2) b
      = W.smul a (-2) b := by norm_num
  rw [hbot] at hexp0
  have hsolve : W.smul a (-2) b = circ W 0 a b - R := by rw [hexp0]; abel
  rw [hsolve]
  refine Submodule.sub_mem _ (hO (circ_n_mem_O W 0 a b)) ?_
  rw [hR]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hw := W.smul_mem_grading ha hb (((i + 1 : ℕ) : ℤ) - 2)
  have heq : (M : ℤ) + q - ((((i + 1 : ℕ)) : ℤ) - 2) - 1 = (M : ℤ) + q - (i : ℤ) := by
    push_cast; ring
  rw [heq] at hw
  exact hT _ (by omega) hw

/-- **The degree induction with `O(𝒱)` as the relation module.**  The exact analogue of
`grading_le_span_sup_blockRelSpan`, and strictly simpler. -/
theorem grading_le_span_sup_O (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) (n : ℤ) :
    W.grading n ≤ Submodule.span ℂ S ⊔ O W := by
  classical
  set T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ O W with hTdef
  have hO : O W ≤ T := le_sup_right
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
    exact smul_negTwo_mem_of_lower_O W ha hb hp0 T hO (fun m hm => hT m (by omega))

/-- **The `C₂`-generators span `𝒱` modulo `O(𝒱)`.** -/
theorem span_sup_O_eq_top (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) :
    (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O W := by
  refine le_antisymm ?_ le_top
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_span_sup_O W S hShom htop m hx

/-- `Finset` form. -/
theorem exists_finset_span_sup_O (hC2 : C2Cofinite W) :
    ∃ T : Finset 𝒱, (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ O W := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨(Finset.univ.image gen) ∪ {W.vacuum}, ?_⟩
  have hset : (((Finset.univ.image gen) ∪ {W.vacuum} : Finset 𝒱) : Set 𝒱)
      = Set.range gen ∪ {W.vacuum} := by
    ext x; simp [Set.mem_range]
  rw [hset]
  refine span_sup_O_eq_top W _ ?_ hdec
  rintro s (⟨i, rfl⟩ | hs)
  · exact ⟨(wt i : ℤ), hgen i⟩
  · rw [Set.mem_singleton_iff] at hs
    exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩

/-- **`C₂`-cofinite ⟹ Zhu's algebra is finite-dimensional.**  This discharges the
`FiniteDimensional ℂ (A 𝒱)` hypothesis carried throughout the count. -/
theorem finiteDimensional_A_of_C2Cofinite (hC2 : C2Cofinite W) :
    FiniteDimensional ℂ (A W) := by
  obtain ⟨T, hT⟩ := exists_finset_span_sup_O W hC2
  exact (finiteDimensional_and_finrank_quot_le_of_span_sup T hT).1

/-- The explicit bound: `dim A(𝒱)` is at most the number of `C₂`-generators plus one. -/
theorem finrank_A_le_of_C2Cofinite (hC2 : C2Cofinite W) :
    ∃ T : Finset 𝒱, Module.finrank ℂ (A W) ≤ T.card := by
  obtain ⟨T, hT⟩ := exists_finset_span_sup_O W hC2
  exact ⟨T, (finiteDimensional_and_finrank_quot_le_of_span_sup T hT).2⟩

end VOA
