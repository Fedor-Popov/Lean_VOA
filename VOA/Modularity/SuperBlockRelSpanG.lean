/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanG
import VOA.Modularity.FormalBlockFinite
import VOA.Modularity.SuperBlockSpanning
import VOA.Modularity.SuperQuasiLisseGraded

/-!
# Super Arakawa--Kawasetsu finite generation over `GSeries`

This is the formal-coefficient-ring version of the integral-weight, untwisted-supertrace relation
module.  It ports the algebraic content of `Modules.QuasiLisseFinite` while keeping conformal
weight and parity independent.

The zero-mode triangularity is sign-free: `a[0]b` is expanded without exchanging `a` and `b`.
The Koszul sign belongs only to the separate super-antisymmetry interpretation, audited in
`SuperPoissonTrace.superZeroMode_koszul_antisymm_mod_superO₂`.
-/

namespace VOA

open scoped BigOperators TensorProduct
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-! ## The `GSeries` relation module -/

/-- The super genus-one relation module over `GSeries = ℂ[G₂,G₄,G₆]`.  Its formulas are the
untwisted-supertrace formulas; neither generator exchanges homogeneous states. -/
noncomputable def superBlockRelSpanG : Submodule (↥GSeries) (𝒱G 𝒱) :=
  Submodule.span (↥GSeries)
    ({x : 𝒱G 𝒱 | ∃ (k : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        x = ιG (V.superVSqZ a k 0 v)} ∪
     {x : 𝒱G 𝒱 | ∃ (k K : ℕ) (a v : 𝒱), 1 ≤ k ∧ a ∈ V.gradingZ (k : ℤ) ∧
        (∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = ιG (V.superVSqZ a k (-2) v) + ∑ m ∈ Finset.range K,
          coefG m • ιG (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v)})

/-- The generic `GSeries` pullback, named for the super application. -/
noncomputable abbrev superPullbackG
    (T : Submodule (↥GSeries) (𝒱G 𝒱)) : Submodule ℂ 𝒱 := pullbackG T

@[simp] theorem mem_superPullbackG {T : Submodule (↥GSeries) (𝒱G 𝒱)} {v : 𝒱} :
    v ∈ superPullbackG T ↔ (ιG v : 𝒱G 𝒱) ∈ T := Iff.rfl

/-- The super square-bracket minus-two generator descends over `GSeries`. -/
theorem superVSqZ_negTwo_mem_of_superBlockRelSpanG
    {p q n : ℤ} {a b : 𝒱} (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q)
    (hp1 : 1 ≤ p) (hpq : p + q + 1 = n)
    (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hT : ∀ m : ℤ, m < n → V.gradingZ m ≤ superPullbackG T)
    (hrel : V.superBlockRelSpanG ≤ T) :
    V.superVSqZ a p.toNat (-2) b ∈ superPullbackG T := by
  classical
  have hk : 1 ≤ p.toNat := by omega
  have ha' : a ∈ V.gradingZ ((p.toNat : ℕ) : ℤ) := by
    rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
  obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a p.toNat b
  set tail : 𝒱G 𝒱 := ∑ m ∈ Finset.range K,
    coefG m • ιG (V.superVSqZ a p.toNat (2 * (m + 2) - 2 : ℤ) b)
  have hmem : (ιG (V.superVSqZ a p.toNat (-2) b) : 𝒱G 𝒱) + tail ∈ T :=
    hrel (Submodule.subset_span (Or.inr ⟨p.toNat, K, a, b, hk, ha', hK, rfl⟩))
  have htail : tail ∈ T := by
    rw [show tail = ∑ m ∈ Finset.range K,
      coefG m • ιG (V.superVSqZ a p.toNat (2 * (m + 2) - 2 : ℤ) b) from rfl]
    refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_)
    refine V.superVSqZ_mem_of_lower ha hb p.toNat (2 * ((m : ℤ) + 2) - 2)
      (superPullbackG T) (fun d hd => ?_)
    exact hT d (by omega)
  rw [mem_superPullbackG]
  have hneg : (-1 : ↥GSeries) • tail ∈ T := T.smul_mem (-1) htail
  have hadd := T.add_mem hmem hneg
  have hsmul : (-1 : ↥GSeries) • tail = -tail := neg_one_smul (↥GSeries) tail
  rw [hsmul] at hadd
  have hcancel : ((ιG (V.superVSqZ a p.toNat (-2) b) : 𝒱G 𝒱) + tail) + -tail
      = ιG (V.superVSqZ a p.toNat (-2) b) := by
    abel
  rw [hcancel] at hadd
  exact hadd

/-- A square-bracket zero-mode generator is one of the defining `GSeries` relations. -/
theorem superVSqZ_zero_mem_superBlockRelSpanG {k : ℕ} (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ V.gradingZ (k : ℤ)) (b : 𝒱) :
    V.superVSqZ a k 0 b ∈ superPullbackG V.superBlockRelSpanG :=
  Submodule.subset_span (Or.inl ⟨k, a, b, hk, ha, rfl⟩)

/-! ## Zero-mode triangularity -/

/-- The non-leading terms in the square-bracket zero mode. -/
noncomputable def superSqDefect0 (a : 𝒱) (k : ℕ) (b : 𝒱) : 𝒱 :=
  ∑ᶠ i : ℤ, (if i = 0 then (0 : ℂ) else sqBracketCoeffZ k 0 i) • V.smul a i b

theorem superSqDefect0_support_finite (a : 𝒱) (k : ℕ) (b : 𝒱) :
    (Function.support fun i : ℤ =>
      (if i = 0 then (0 : ℂ) else sqBracketCoeffZ k 0 i) • V.smul a i b).Finite := by
  refine Set.Finite.subset (V.superSqModeZ_support_finite a k 0 b) (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi ⊢
  intro hc
  apply hi
  by_cases h0 : i = 0
  · rw [if_pos h0, zero_smul]
  · rw [if_neg h0, hc]

/-- Square-bracket zero-mode triangularity.  No Koszul scalar occurs because the inputs are not
interchanged. -/
theorem superVSqZ_zero_eq (a : 𝒱) (k : ℕ) (b : 𝒱) :
    V.superVSqZ a k 0 b = V.smul a 0 b + V.superSqDefect0 a k b := by
  rw [V.superVSqZ_apply, superSqDefect0]
  have hsplit : ∀ i : ℤ, sqBracketCoeffZ k 0 i • V.smul a i b
      = (if i = 0 then sqBracketCoeffZ k 0 i • V.smul a i b else 0)
        + (if i = 0 then (0 : ℂ) else sqBracketCoeffZ k 0 i) • V.smul a i b := by
    intro i
    by_cases h0 : i = 0
    · rw [if_pos h0, if_pos h0, zero_smul, add_zero]
    · rw [if_neg h0, if_neg h0, zero_add]
  rw [finsum_congr hsplit]
  have hfin : (Function.support fun i : ℤ =>
      if i = 0 then sqBracketCoeffZ k 0 i • V.smul a i b else 0).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hne
    exact hi (if_neg hne)
  rw [finsum_add_distrib hfin (V.superSqDefect0_support_finite a k b)]
  congr 1
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => if_neg hi), if_pos rfl,
    sqBracketCoeffZ_diag' k 0, one_smul]

/-- The zero-mode defect lies in strictly lower conformal weights. -/
theorem superSqDefect0_mem_of_lower {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q)
    (hpq : p + q - 1 = n) (T : Submodule ℂ 𝒱)
    (hT : ∀ m : ℤ, m < n → V.gradingZ m ≤ T) :
    V.superSqDefect0 a p.toNat b ∈ T := by
  rw [superSqDefect0]
  refine finsum_mem_submodule_pd _ _ (fun i => ?_)
  by_cases h0 : i = 0
  · rw [if_pos h0, zero_smul]
    exact Submodule.zero_mem _
  rw [if_neg h0]
  rcases lt_or_ge i (0 : ℤ) with hi | hi
  · rw [sqBracketCoeffZ_of_lt _ hi, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ ?_
    have hmem : V.smul a i b ∈ V.gradingZ (p + q - i - 1) :=
      V.smul_mem_gradingZ ha hb i
    exact hT _ (by omega) hmem

/-! ## The two ordinary-mode generator descents -/

theorem superNegTwo_mem_pullbackG
    (W : SuperVertexOperatorAlgebra 𝒱) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.toSuperNearVOA.gradingZ p) (hb : b ∈ W.toSuperNearVOA.gradingZ q)
    (hpq : p + q + 1 = n) (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hT : ∀ m : ℤ, m < n → W.toSuperNearVOA.gradingZ m ≤ superPullbackG T)
    (hrel : W.toSuperNearVOA.superBlockRelSpanG ≤ T) :
    W.toSuperNearVOA.smul a (-2) b ∈ superPullbackG T := by
  let V := W.toSuperNearVOA
  rcases lt_or_ge p 0 with hp | hp0
  · have ha0 : a = 0 := by
      have hz : V.gradingZ p = ⊥ := by
        change W.grading (p : ℂ) = ⊥
        exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hp)
      rw [hz, Submodule.mem_bot] at ha
      exact ha
    rw [ha0, SuperVertexAlgebra.smul_zero_left]
    exact Submodule.zero_mem _
  have hexp := V.superVSqZ_neg_two_eq a p.toNat b
  have hstep : V.smul a (-2) b
      = V.superVSqZ a p.toNat (-2) b - V.superSqDefect a p.toNat b := by
    rw [hexp, add_sub_cancel_right]
  rw [hstep]
  refine Submodule.sub_mem _ ?_
    (V.superSqDefect_mem_of_lower ha hb hpq (superPullbackG T) hT)
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
    exact Submodule.smul_mem _ _ (hT q (by omega) hb)
  · exact V.superVSqZ_negTwo_mem_of_superBlockRelSpanG ha hb hp1 hpq T hT hrel

/-- The ordinary zero-mode bracket descends through the square-bracket zero relation.  The proof
is triangular and contains no Koszul sign: no inputs are exchanged. -/
theorem superZeroMode_mem_pullbackG
    (W : SuperVertexOperatorAlgebra 𝒱) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.toSuperNearVOA.gradingZ p) (hb : b ∈ W.toSuperNearVOA.gradingZ q)
    (hpq : p + q - 1 = n) (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hT : ∀ m : ℤ, m < n → W.toSuperNearVOA.gradingZ m ≤ superPullbackG T)
    (hrel : W.toSuperNearVOA.superBlockRelSpanG ≤ T) :
    W.toSuperNearVOA.smul a 0 b ∈ superPullbackG T := by
  let V := W.toSuperNearVOA
  rcases lt_or_ge p 0 with hp | hp0
  · have ha0 : a = 0 := by
      have hz : V.gradingZ p = ⊥ := by
        change W.grading (p : ℂ) = ⊥
        exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hp)
      rw [hz, Submodule.mem_bot] at ha
      exact ha
    rw [ha0, SuperVertexAlgebra.smul_zero_left]
    exact Submodule.zero_mem _
  rcases eq_or_lt_of_le hp0 with hp | hp1
  · have ha0 : a ∈ V.gradingZ 0 := by
      rw [hp]
      exact ha
    have hvgrade : V.gradingZ 0 = ℂ ∙ W.vacuum := by
      simpa only [V, SuperNearVOA.gradingZ_apply, Int.cast_zero] using W.vacuum_grade
    rw [hvgrade, Submodule.mem_span_singleton] at ha0
    obtain ⟨c, rfl⟩ := ha0
    rw [SuperVertexAlgebra.smul_smul_left]
    have hvac : V.smul W.vacuum 0 b = 0 := by
      change V.smul V.vacuum 0 b = 0
      rw [SuperVertexAlgebra.smul_vacuum_left, if_neg (by norm_num)]
    rw [hvac, smul_zero]
    exact Submodule.zero_mem _
  · have hk : 1 ≤ p.toNat := by omega
    have ha' : a ∈ V.gradingZ ((p.toNat : ℕ) : ℤ) := by
      rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
    have hrelmem : V.superVSqZ a p.toNat 0 b ∈ superPullbackG T :=
      hrel (Submodule.subset_span (Or.inl ⟨p.toNat, a, b, hk, ha', rfl⟩))
    have hdef : V.superSqDefect0 a p.toNat b ∈ superPullbackG T :=
      V.superSqDefect0_mem_of_lower ha hb hpq (superPullbackG T) hT
    have hstep : V.smul a 0 b
        = V.superVSqZ a p.toNat 0 b - V.superSqDefect0 a p.toNat b := by
      rw [V.superVSqZ_zero_eq, add_sub_cancel_right]
    rw [hstep]
    exact Submodule.sub_mem _ hrelmem hdef

/-! ## Degree induction and finite generation -/

/-- The super Arakawa--Kawasetsu degree induction over `GSeries`. -/
theorem superGradingZ_le_pullbackG_of_poisson
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superPoissonRelSpan W)
    (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T)
    (hrel : W.toSuperNearVOA.superBlockRelSpanG ≤ T) (n : ℤ) :
    W.toSuperNearVOA.gradingZ n ≤ superPullbackG T := by
  classical
  let V := W.toSuperNearVOA
  have hSle : Submodule.span ℂ S ≤ superPullbackG T := by
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
    have hlower : ∀ m : ℤ, m < (N : ℤ) → V.gradingZ m ≤ superPullbackG T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · have hz : V.gradingZ m = ⊥ := by
          change W.grading (m : ℂ) = ⊥
          exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hm0)
        rw [hz]
        exact bot_le
      · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
        exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans
      (gradingZ_le_span_sup_superPoissonRelSpan_inf W hV S hShom htop (N : ℤ)) ?_
    refine sup_le hSle ?_
    refine le_trans (superPoissonRelSpan_inf_gradingZ_le_span_deg W hV (N : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g (⟨p, q, r, s, a, b, ha, hap, hb, hbq, hpq, rfl⟩ |
      ⟨p, q, r, s, a, b, ha, hap, hb, hbq, hpq, rfl⟩)
    · exact superNegTwo_mem_pullbackG W ha hb hpq T hlower hrel
    · exact superZeroMode_mem_pullbackG W ha hb hpq T hlower hrel

/-- Span form of super Arakawa--Kawasetsu Proposition 5.2. -/
theorem superSpan_sup_superBlockRelSpanG_eq_top_of_poisson
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superPoissonRelSpan W) :
    (⊤ : Submodule (↥GSeries) (𝒱G 𝒱)) =
      Submodule.span (↥GSeries) ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S)
        ⊔ W.toSuperNearVOA.superBlockRelSpanG := by
  let V := W.toSuperNearVOA
  set T : Submodule (↥GSeries) (𝒱G 𝒱) :=
    Submodule.span (↥GSeries) ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S) ⊔ V.superBlockRelSpanG
  have hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T := fun s hs =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
  have hrel : V.superBlockRelSpanG ≤ T := le_sup_right
  refine le_antisymm ?_ le_top
  rw [← span_range_ιG_eq_top (𝒱 := 𝒱), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have htopPb : (⊤ : Submodule ℂ 𝒱) ≤ superPullbackG T := by
    rw [← (V.gradingZ_isInternal hV).submodule_iSup_eq_top]
    exact iSup_le (superGradingZ_le_pullbackG_of_poisson W hV S hShom htop T hS hrel)
  exact htopPb Submodule.mem_top

/-- Finite generating-family form of super Arakawa--Kawasetsu Proposition 5.2.

This is the quotient-independent formulation of `Module.Finite`: the images of `T` generate
`𝒱G 𝒱 / superBlockRelSpanG`.  As already documented for the bosonic Etingof port in
`Modules.QuasiLisseFinite`, the literal quotient type cannot be re-elaborated after importing
`BlockRelSpanG`: competing reducibly unequal tensor-product additive and scalar instances make
`HasQuotient` fail.  No mathematical hypothesis is lost in this presentation. -/
theorem exists_finite_gen_sup_superBlockRelSpanG_of_superEtingofFinite
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hE : SuperEtingofFinite W) :
    ∃ T : Set (𝒱G 𝒱), T.Finite ∧
      (⊤ : Submodule (↥GSeries) (𝒱G 𝒱)) =
        Submodule.span (↥GSeries) T ⊔ W.toSuperNearVOA.superBlockRelSpanG := by
  obtain ⟨S, hShom, hdec⟩ :=
    exists_finset_homog_span_sup_superPoissonRelSpan W hV hE
  exact ⟨(ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' (S : Set 𝒱), S.finite_toSet.image _,
    superSpan_sup_superBlockRelSpanG_eq_top_of_poisson W hV (S : Set 𝒱) hShom hdec⟩

/-! ## Push-forward to formal relation functionals -/

/-- The two formal genus-one relations needed for finite generation.  The Virasoro/derivative
condition is intentionally absent: the repository has no super square-bracket Virasoro operator
or graded ordinary supermodule trace construction yet. -/
structure IsSuperFormalBlockRelations (S : 𝒱 →ₗ[ℂ] FormalQSeries) : Prop where
  vanish : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ V.gradingZ (k : ℤ), ∀ b : 𝒱,
    S (V.superVSqZ a k 0 b) = 0
  negTwo : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ V.gradingZ (k : ℤ), ∀ b : 𝒱,
    S (V.superVSqZ a k (-2) b)
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1))
            (S (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b)) = 0

/-- The formal minus-two tail in the range shape used by `superBlockRelSpanG`. -/
theorem superNegTwo_tail_eq_range {S : 𝒱 →ₗ[ℂ] FormalQSeries}
    (hS : V.IsSuperFormalBlockRelations S) {k K : ℕ} (hk : 1 ≤ k)
    {a : 𝒱} (ha : a ∈ V.gradingZ (k : ℤ)) (b : 𝒱)
    (hK : ∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b = 0) :
    (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1))
          (S (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b)))
      = ∑ m ∈ Finset.range K, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 2))
            (S (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b)) := by
  classical
  set F : ℕ → FormalQSeries := fun m => ((2 * (m + 1) - 1 : ℕ) : ℂ)
    • qConv (zhuG (m + 1))
      (S (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b)) with hFdef
  have hF0 : F 0 = 0 := by
    have hz : (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 := by norm_num
    rw [hFdef]
    simp only [hz]
    rw [hS.vanish k hk a ha b, qConv_zero_right, smul_zero]
  have hFK : ∀ m : ℕ, K ≤ m → F m = 0 := by
    intro m hm
    rw [hFdef]
    simp only [hK m hm, map_zero, qConv_zero_right, smul_zero]
  have hsupp : Function.support F ⊆ (Finset.range (K + 1) : Finset ℕ) := by
    intro m hm
    by_contra hc
    rw [Finset.mem_coe, Finset.mem_range] at hc
    exact hm (hFK m (by omega))
  rw [finsum_eq_sum_of_support_subset F hsupp, Finset.sum_range_succ', hF0, add_zero]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [hFdef]
  congr 2

/-- A formal super relation functional kills the `GSeries` relation module. -/
theorem superBlockRelSpanG_le_ker {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : V.IsSuperFormalBlockRelations S) :
    V.superBlockRelSpanG ≤ LinearMap.ker (blockLift hsupp) := by
  classical
  rw [superBlockRelSpanG, Submodule.span_le]
  rintro x (⟨k, a, b, hk, ha, rfl⟩ | ⟨k, K, a, b, hk, ha, hK, rfl⟩)
  · refine LinearMap.mem_ker.mpr ?_
    rw [blockLift_ιG]
    exact Subtype.ext (by rw [blockRestrict_coe, hS.vanish k hk a ha b]; rfl)
  · refine LinearMap.mem_ker.mpr ?_
    rw [map_add, blockLift_ιG, map_sum]
    refine Subtype.ext ?_
    rw [Submodule.coe_add, blockRestrict_coe, AddSubmonoid.coe_finsetSum]
    have hterm : ∀ m ∈ Finset.range K,
        (((blockLift hsupp)
          (coefG m • ιG (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b))
            : ↥(QSeriesAt hbase)) : FormalQSeries)
          = ((2 * (m + 2) - 1 : ℕ) : ℂ)
              • qConv (zhuG (m + 2))
                (S (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b)) := by
      intro m _
      rw [map_smul, blockLift_ιG]
      change psSMul ((coefG m : ↥GSeries) : PowerSeries ℂ)
        ((blockRestrict hsupp
          (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b) : ↥(QSeriesAt hbase)) :
          FormalQSeries) = _
      rw [blockRestrict_coe, coefG_coe, psSMul_smul_left _ _ (hsupp _), psSMul_mk]
    rw [Finset.sum_congr rfl hterm, ← V.superNegTwo_tail_eq_range hS hk ha b hK]
    exact hS.negTwo k hk a ha b

/-- The `GSeries` span of a formal super relation functional is finitely generated under
`SuperEtingofFinite`. -/
theorem fg_blockSpan_of_superEtingofFinite
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (hS : W.toSuperNearVOA.IsSuperFormalBlockRelations S)
    (hE : SuperEtingofFinite W) :
    (Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))).FG := by
  classical
  let V := W.toSuperNearVOA
  obtain ⟨T, hShom, hdec⟩ :=
    exists_finset_homog_span_sup_superPoissonRelSpan W hV hE
  have htop := superSpan_sup_superBlockRelSpanG_eq_top_of_poisson
    W hV (T : Set 𝒱) hShom hdec
  have hker := V.superBlockRelSpanG_le_ker hsupp hS
  have hmapbot : Submodule.map (blockLift hsupp) V.superBlockRelSpanG = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact LinearMap.mem_ker.mp (hker hx)
  have himg : (blockLift hsupp) ''
      ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' (T : Set 𝒱)) =
      (blockRestrict hsupp) '' (T : Set 𝒱) := by
    rw [Set.image_image]
    exact Set.image_congr (fun v _ => blockLift_ιG hsupp v)
  have h1 : Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase))) =
      LinearMap.range (blockLift hsupp) := by
    rw [blockLift, LinearMap.range_liftBaseChange, LinearMap.coe_range]
  have h2 : LinearMap.range (blockLift hsupp) =
      Submodule.span (↥GSeries) ((blockRestrict hsupp) '' (T : Set 𝒱)) := by
    rw [LinearMap.range_eq_map, htop, Submodule.map_sup, hmapbot, sup_bot_eq,
      Submodule.map_span, himg]
  rw [h1, h2]
  exact Submodule.fg_span (T.finite_toSet.image _)

end SuperNearVOA

end VOA
