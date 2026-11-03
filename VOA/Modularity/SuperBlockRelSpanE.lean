/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperBlockSpanning
import VOA.Modularity.BlockRelSpanE

/-!
# The super genus-one relation module over E46

This is the parity-independent algebraic family used to transport the super block quotient from
the cusp to the upper half-plane.  The coefficient ring and specialization maps are exactly the
bosonic `E46` ones.  Only the state-space modes and integral grading are replaced by their super
counterparts.

No signed Zhu commutator theorem is used here.  In particular, this file proves finite generation
of the deformed relation quotient directly from super `C2`-cofiniteness, before the cusp quotient
is identified with a supercommutator quotient.

## Main results

* `superBlockRelSpanE`;
* `superVSqZ_negTwo_mem_of_superBlockRelSpanE`;
* `superGradingZ_le_pullback`;
* `moduleFinite_quot_superBlockRelSpanE`.
-/

namespace VOA

open scoped BigOperators TensorProduct
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-- The `E46`-linear super block relation module.  Neither parity nor a modular group occurs in
its generators; parity enters only when its cusp quotient is interpreted algebraically. -/
noncomputable def superBlockRelSpanE : Submodule (↥E46) (𝒱E 𝒱) :=
  Submodule.span (↥E46)
    ({x : 𝒱E 𝒱 | ∃ (k : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        x = ιE (V.superVSqZ a k 0 v)} ∪
     {x : 𝒱E 𝒱 | ∃ (k K : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        (∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = ιE (V.superVSqZ a k (-2) v) + ∑ m ∈ Finset.range K,
          coefE m • ιE (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v)})

/-- The square-bracket `minus two` generator descends over `E46`. -/
theorem superVSqZ_negTwo_mem_of_superBlockRelSpanE
    {p q n : ℤ} {a b : 𝒱} (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q)
    (hp1 : 1 ≤ p) (hpq : p + q + 1 = n)
    (T : Submodule (↥E46) (𝒱E 𝒱))
    (hT : ∀ m : ℤ, m < n → V.gradingZ m ≤ pullback T)
    (hrel : V.superBlockRelSpanE ≤ T) :
    V.superVSqZ a p.toNat (-2) b ∈ pullback T := by
  classical
  have hk : 1 ≤ p.toNat := by omega
  have ha' : a ∈ V.gradingZ ((p.toNat : ℕ) : ℤ) := by
    rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
  obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a p.toNat b
  set tail : 𝒱E 𝒱 := ∑ m ∈ Finset.range K,
    coefE m • ιE (V.superVSqZ a p.toNat (2 * (m + 2) - 2 : ℤ) b)
  have hmem : (ιE (V.superVSqZ a p.toNat (-2) b) : 𝒱E 𝒱) + tail ∈ T :=
    hrel (Submodule.subset_span (Or.inr ⟨p.toNat, K, a, b, hk, ha', hK, rfl⟩))
  have htail : tail ∈ T := by
    rw [show tail = ∑ m ∈ Finset.range K,
      coefE m • ιE (V.superVSqZ a p.toNat (2 * (m + 2) - 2 : ℤ) b) from rfl]
    refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_)
    refine V.superVSqZ_mem_of_lower ha hb p.toNat (2 * ((m : ℤ) + 2) - 2)
      (pullback T) (fun d hd => ?_)
    exact hT d (by omega)
  have hsplit : (ιE (V.superVSqZ a p.toNat (-2) b) : 𝒱E 𝒱)
      = ((ιE (V.superVSqZ a p.toNat (-2) b) : 𝒱E 𝒱) + tail) - tail := by abel
  rw [mem_pullback, hsplit]
  exact Submodule.sub_mem _ hmem htail

/-- The super degree induction pulled back from an `E46`-submodule. -/
theorem superGradingZ_le_pullback
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W)
    (T : Submodule (↥E46) (𝒱E 𝒱))
    (hS : ∀ s ∈ S, (ιE s : 𝒱E 𝒱) ∈ T)
    (hrel : W.toSuperNearVOA.superBlockRelSpanE ≤ T) (n : ℤ) :
    W.toSuperNearVOA.gradingZ n ≤ pullback T := by
  classical
  let V := W.toSuperNearVOA
  have hSle : Submodule.span ℂ S ≤ pullback T := by
    rw [Submodule.span_le]
    intro s hs
    exact hS s hs
  rcases lt_or_ge n 0 with hneg | hnn
  · have hz : V.gradingZ n = ⊥ := by
      change W.grading (n : ℂ) = ⊥
      exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hneg)
    rw [hz]
    exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hlower : ∀ m : ℤ, m < (N : ℤ) → V.gradingZ m ≤ pullback T := by
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
    refine sup_le hSle ?_
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
    refine Submodule.sub_mem _ ?_ (V.superSqDefect_mem_of_lower ha hb hpq (pullback T) hlower)
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
    · exact V.superVSqZ_negTwo_mem_of_superBlockRelSpanE ha hb hp1 hpq T hlower hrel

/-- The `E46` span form of the super Zhu/DLM finite-generation argument. -/
theorem superSpan_sup_superBlockRelSpanE_eq_top
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W) :
    (⊤ : Submodule (↥E46) (𝒱E 𝒱)) =
      Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S)
        ⊔ W.toSuperNearVOA.superBlockRelSpanE := by
  let V := W.toSuperNearVOA
  set T : Submodule (↥E46) (𝒱E 𝒱) :=
    Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S) ⊔ V.superBlockRelSpanE
  have hS : ∀ s ∈ S, (ιE s : 𝒱E 𝒱) ∈ T := fun s hs =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
  have hrel : V.superBlockRelSpanE ≤ T := le_sup_right
  refine le_antisymm ?_ le_top
  rw [← span_range_ιE_eq_top (𝒱 := 𝒱), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have htopPb : (⊤ : Submodule ℂ 𝒱) ≤ pullback T := by
    rw [← (V.gradingZ_isInternal hW).submodule_iSup_eq_top]
    exact iSup_le (superGradingZ_le_pullback W hW S hShom htop T hS hrel)
  exact htopPb Submodule.mem_top

/-- Super Zhu/DLM finite generation: the `E46` relation quotient is a finite module. -/
theorem moduleFinite_quot_superBlockRelSpanE
    (W : SuperVertexOperatorAlgebra 𝒱) (hW : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    Module.Finite (↥E46) ((𝒱E 𝒱) ⧸ W.toSuperNearVOA.superBlockRelSpanE) := by
  classical
  let V := W.toSuperNearVOA
  obtain ⟨S, hShom, hdec⟩ := exists_finset_homog_span_sup_superO₂ W hW hC2
  have htop := superSpan_sup_superBlockRelSpanE_eq_top W hW (S : Set 𝒱) hShom hdec
  have hfin : (((V.superBlockRelSpanE).mkQ) ''
      ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' (S : Set 𝒱))).Finite :=
    (S.finite_toSet.image _).image _
  have hgen : Submodule.span (↥E46)
      (((V.superBlockRelSpanE).mkQ) '' ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' (S : Set 𝒱))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := V.superBlockRelSpanE.mkQ_surjective y
    have hx : x ∈ Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' (S : Set 𝒱))
        ⊔ V.superBlockRelSpanE := by
      rw [← htop]
      trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    have hw0 : V.superBlockRelSpanE.mkQ w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hw
    rw [map_add, hw0, add_zero, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hu
  have hfg : (Submodule.span (↥E46)
      (((V.superBlockRelSpanE).mkQ) ''
        ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' (S : Set 𝒱)))).FG := Submodule.fg_span hfin
  rw [hgen] at hfg
  exact ⟨hfg⟩

end SuperNearVOA

end VOA
