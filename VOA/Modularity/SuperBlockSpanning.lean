/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperAnalyticBlock
import VOA.Modularity.SuperZhuAlgebraFinite

/-!
# C2 spanning for integral-weight analytic super blocks

This file proves the rationality-free finiteness half of the super genus-one block program.  The
argument is the square-bracket triangular descent: `a[minus two]b` differs from the ordinary
`a_(minus two)b` by strictly lower-weight terms, while the block relation expresses the former by
an Eisenstein tail of strictly lower weight.

The resulting theorem is uniform in the evaluation point and uses only super `C2`-cofiniteness
and integral conformal weights.  It does not identify the sharp cusp quotient: that requires the
still-missing signed super Zhu commutator congruence and the `E46` Nakayama transport.

## Main results

* `superVSqZ_neg_two_eq` and `superSqDefect_mem_of_lower`;
* `span_sup_superBlockRelSpan_eq_top`;
* `exists_finset_span_sup_superBlockRelSpan`;
* `finiteDimensional_superAnalyticBlocks_of_superC2Cofinite`.
-/

namespace VOA

open scoped BigOperators
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-- The correction term between the super square-bracket `minus two` product and the ordinary
`minus two` mode.  No parity sign occurs because no states are exchanged. -/
noncomputable def superSqDefect (a : 𝒱) (p : ℕ) (b : 𝒱) : 𝒱 :=
  ∑ᶠ i : ℤ, (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • V.smul a i b

theorem superSqDefect_support_finite (a : 𝒱) (p : ℕ) (b : 𝒱) :
    (Function.support fun i : ℤ =>
      (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • V.smul a i b).Finite := by
  refine Set.Finite.subset (V.superSqModeZ_support_finite a p (-2) b) (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi ⊢
  intro hc
  apply hi
  by_cases h2 : i = -2
  · rw [if_pos h2, zero_smul]
  · rw [if_neg h2, hc]

/-- Square-bracket triangularity at index `minus two`. -/
theorem superVSqZ_neg_two_eq (a : 𝒱) (p : ℕ) (b : 𝒱) :
    V.superVSqZ a p (-2) b = V.smul a (-2) b + V.superSqDefect a p b := by
  rw [V.superVSqZ_apply, superSqDefect]
  have hsplit : ∀ i : ℤ, sqBracketCoeffZ p (-2) i • V.smul a i b
      = (if i = -2 then sqBracketCoeffZ p (-2) i • V.smul a i b else 0)
        + (if i = -2 then (0 : ℂ) else sqBracketCoeffZ p (-2) i) • V.smul a i b := by
    intro i
    by_cases h2 : i = -2
    · rw [if_pos h2, if_pos h2, zero_smul, add_zero]
    · rw [if_neg h2, if_neg h2, zero_add]
  rw [finsum_congr hsplit]
  have hfin : (Function.support fun i : ℤ =>
      if i = -2 then sqBracketCoeffZ p (-2) i • V.smul a i b else 0).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (-2 : ℤ)) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hne
    exact hi (if_neg hne)
  rw [finsum_add_distrib hfin (V.superSqDefect_support_finite a p b)]
  congr 1
  rw [finsum_eq_single _ (-2 : ℤ) (fun i hi => if_neg hi), if_pos rfl,
    sqBracketCoeffZ_diag' p (-2), one_smul]

/-- A super square-bracket mode belongs to any submodule containing the relevant lower graded
pieces. -/
theorem superVSqZ_mem_of_lower {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q) (p' : ℕ) (m : ℤ)
    (T : Submodule ℂ 𝒱)
    (hT : ∀ d : ℤ, d ≤ p + q - m - 1 → V.gradingZ d ≤ T) :
    V.superVSqZ a p' m b ∈ T := by
  rw [V.superVSqZ_apply]
  refine finsum_mem_submodule_pd _ _ (fun i => ?_)
  rcases lt_or_ge i m with hlt | hge
  · rw [sqBracketCoeffZ_of_lt _ hlt, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ ?_
    have hmem : V.smul a i b ∈ V.gradingZ (p + q - i - 1) := V.smul_mem_gradingZ ha hb i
    exact hT _ (by omega) hmem

/-- The square-bracket defect is supported in strictly lower weight. -/
theorem superSqDefect_mem_of_lower {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q)
    (hpq : p + q + 1 = n) (T : Submodule ℂ 𝒱)
    (hT : ∀ m : ℤ, m < n → V.gradingZ m ≤ T) :
    V.superSqDefect a p.toNat b ∈ T := by
  rw [superSqDefect]
  refine finsum_mem_submodule_pd _ _ (fun i => ?_)
  by_cases h2 : i = -2
  · rw [if_pos h2, zero_smul]
    exact Submodule.zero_mem _
  rw [if_neg h2]
  rcases lt_or_ge i (-2 : ℤ) with hlt | hge
  · rw [sqBracketCoeffZ_of_lt _ hlt, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ ?_
    have hmem : V.smul a i b ∈ V.gradingZ (p + q - i - 1) := V.smul_mem_gradingZ ha hb i
    exact hT _ (by omega) hmem

/-- Square-bracket modes of the vacuum are scalar operators. -/
theorem superVSqZ_vacuum_scalar (k : ℤ) (x : 𝒱) :
    V.superVSqZ V.vacuum 0 k x = sqBracketCoeffZ 0 k (-1) • x := by
  rw [V.superVSqZ_apply]
  have heq : (fun i : ℤ => sqBracketCoeffZ 0 k i • V.smul V.vacuum i x)
      = fun i : ℤ => if i = -1 then sqBracketCoeffZ 0 k (-1) • x else 0 := by
    funext i
    rw [SuperVertexAlgebra.smul_vacuum_left]
    rcases eq_or_ne i (-1) with rfl | hi
    · simp
    · simp [hi]
  rw [heq, finsum_eq_single _ (-1) (fun i hi => if_neg hi), if_pos rfl]

/-! ## Degree descent for the deformed relation space -/

/-- The `a[minus two]b` generator descends modulo the analytic relation space. -/
theorem superVSqZ_negTwo_mem_of_superBlockRelSpan (z : ℂ)
    {p q n : ℤ} {a b : 𝒱} (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q)
    (hp1 : 1 ≤ p) (hpq : p + q + 1 = n) (T : Submodule ℂ 𝒱)
    (hT : ∀ m : ℤ, m < n → V.gradingZ m ≤ T)
    (hrel : V.superBlockRelSpan z ≤ T) :
    V.superVSqZ a p.toNat (-2) b ∈ T := by
  classical
  have hk : 1 ≤ p.toNat := by omega
  have ha' : a ∈ V.gradingZ ((p.toNat : ℕ) : ℤ) := by
    rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
  obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a p.toNat b
  set tail : 𝒱 := ∑ m ∈ Finset.range K,
    (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z)
      • V.superVSqZ a p.toNat (2 * (m + 2) - 2 : ℤ) b
  have hmem : V.superVSqZ a p.toNat (-2) b + tail ∈ T :=
    hrel (Submodule.subset_span (Or.inr ⟨p.toNat, K, a, b, hk, ha', hK, rfl⟩))
  have htail : tail ∈ T := by
    rw [show tail = ∑ m ∈ Finset.range K,
      (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z)
        • V.superVSqZ a p.toNat (2 * (m + 2) - 2 : ℤ) b from rfl]
    refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_)
    refine V.superVSqZ_mem_of_lower ha hb p.toNat (2 * ((m : ℤ) + 2) - 2) T
      (fun d hd => ?_)
    exact hT d (by omega)
  have hsplit : V.superVSqZ a p.toNat (-2) b
      = (V.superVSqZ a p.toNat (-2) b + tail) - tail := by abel
  rw [hsplit]
  exact Submodule.sub_mem _ hmem htail

/-- Every integral weight space is generated by a `C2` family modulo the deformed block
relations. -/
theorem gradingZ_le_span_sup_superBlockRelSpan
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W)
    (z : ℂ) (n : ℤ) :
    W.toSuperNearVOA.gradingZ n ≤
      Submodule.span ℂ S ⊔ W.toSuperNearVOA.superBlockRelSpan z := by
  classical
  let V := W.toSuperNearVOA
  let T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ V.superBlockRelSpan z
  have hrel : V.superBlockRelSpan z ≤ T := le_sup_right
  rcases lt_or_ge n 0 with hneg | hnn
  · have hz : V.gradingZ n = ⊥ := by
      change W.grading (n : ℂ) = ⊥
      exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hneg)
    rw [hz]
    exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hlower : ∀ m : ℤ, m < (N : ℤ) → V.gradingZ m ≤ T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · have hz : V.gradingZ m = ⊥ := by
          change W.grading (m : ℂ) = ⊥
          exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hm0)
        rw [hz]
        exact bot_le
      · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
        exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans (gradingZ_le_span_sup_superO₂_inf W hW S hShom htop (N : ℤ)) ?_
    refine sup_le le_sup_left ?_
    refine le_trans (superO₂_inf_gradingZ_le_span_deg W hW (N : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    by_cases hg0 : V.smul a (-2) b = 0
    · rw [hg0]
      exact Submodule.zero_mem _
    have hp0 : 0 ≤ p := by
      by_contra hc
      have hpneg : p < 0 := by omega
      exact hg0 (by
        have ha0 : a = 0 := by
          have hz : V.gradingZ p = ⊥ := by
            change W.grading (p : ℂ) = ⊥
            exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hpneg)
          rw [hz, Submodule.mem_bot] at ha
          exact ha
        rw [ha0, SuperVertexAlgebra.smul_zero_left])
    have hexp := V.superVSqZ_neg_two_eq a p.toNat b
    have hstep : V.smul a (-2) b
        = V.superVSqZ a p.toNat (-2) b - V.superSqDefect a p.toNat b := by
      rw [hexp, add_sub_cancel_right]
    rw [hstep]
    refine Submodule.sub_mem _ ?_ (V.superSqDefect_mem_of_lower ha hb hpq T hlower)
    rcases eq_or_lt_of_le hp0 with hp | hp1
    · have ha0 : a ∈ V.gradingZ 0 := by
        rw [hp]
        exact ha
      have hvgrade : V.gradingZ 0 = ℂ ∙ W.vacuum := by
        simpa only [V, SuperNearVOA.gradingZ_apply, Int.cast_zero] using W.vacuum_grade
      rw [hvgrade, Submodule.mem_span_singleton] at ha0
      obtain ⟨c, rfl⟩ := ha0
      have hp0' : p.toNat = 0 := by omega
      rw [hp0']
      have hlin : V.superVSqZ (c • W.vacuum) 0 (-2) b
          = c • V.superVSqZ W.vacuum 0 (-2) b := by
        rw [V.superVSqZ_apply, V.superVSqZ_apply,
          smul_finsum' c (V.superSqModeZ_support_finite W.vacuum 0 (-2) b)]
        refine finsum_congr (fun i => ?_)
        rw [SuperVertexAlgebra.smul_smul_left, smul_comm]
      have hvac : V.superVSqZ W.vacuum 0 (-2) b
          = sqBracketCoeffZ 0 (-2) (-1) • b := by
        change V.superVSqZ V.vacuum 0 (-2) b = _
        exact V.superVSqZ_vacuum_scalar (-2) b
      rw [hlin, hvac, smul_smul]
      exact Submodule.smul_mem _ _ (hlower q (by omega) hb)
    · exact V.superVSqZ_negTwo_mem_of_superBlockRelSpan z ha hb hp1 hpq T hlower hrel

/-- The span form of the super square-bracket descent, uniformly in the point. -/
theorem span_sup_superBlockRelSpan_eq_top
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W) (z : ℂ) :
    (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ S ⊔ W.toSuperNearVOA.superBlockRelSpan z := by
  let V := W.toSuperNearVOA
  refine le_antisymm ?_ le_top
  rw [← (V.gradingZ_isInternal hW).submodule_iSup_eq_top]
  exact iSup_le (gradingZ_le_span_sup_superBlockRelSpan W hW S hShom htop z)

/-- Super `C2`-cofiniteness supplies a finite determining family at every interior point. -/
theorem exists_finset_span_sup_superBlockRelSpan
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) (z : ℂ) :
    ∃ T : Finset 𝒱, (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (T : Set 𝒱) ⊔ W.toSuperNearVOA.superBlockRelSpan z := by
  obtain ⟨T, hThom, hT⟩ := exists_finset_homog_span_sup_superO₂ W hW hC2
  exact ⟨T, span_sup_superBlockRelSpan_eq_top W hW (T : Set 𝒱) hThom hT z⟩

/-- Integral-weight super `C2`-cofiniteness makes the untwisted analytic super block space
finite-dimensional, without rationality or semisimplicity. -/
theorem finiteDimensional_superAnalyticBlocks_of_superC2Cofinite
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ
      (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks) := by
  have hI : (Complex.I : ℂ) ∈ imGT 0 := by
    change (0 : ℝ) < Complex.I.im
    simp
  obtain ⟨T, hT⟩ := exists_finset_span_sup_superBlockRelSpan W hW hC2 Complex.I
  exact (finrank_superAnalyticBlocks_le_card_of_superBlockRel hI T hT).1

end SuperNearVOA

end VOA
