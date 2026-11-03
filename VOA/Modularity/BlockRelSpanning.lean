/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.CuspLimit
import VOA.Modularity.SquareBracketC2

/-!
# The span form of Zhu's descent: `𝒱` is spanned by the `C₂`-family modulo `blockRelSpan z`

Everywhere it appears, `⊤ = span ℂ T ⊔ blockRelSpan W z₀` has been a **hypothesis**
(`finrank_analyticBlocks_le_card_of_blockRel`); the repo proved Zhu's Theorem 5.3.2 through the
*dual* (functional) descent instead.  This file proves the span form directly, for **every**
`z : ℂ` and with the *same* finite family that `C₂`-cofiniteness supplies:

  `⊤ = span ℂ (gen ∪ {𝟙}) ⊔ blockRelSpan W z`.

The engine is the one already used for `O₂sq`: block condition (ii) rewrites `a[−2]b` as minus its
Eisenstein tail, and every tail term `a[2m+2]b` has **strictly lower** degree, so a strong induction
on the degree closes.  The grade-`0` slot is handled by `VacuumGradeZero` and `𝟙[k] = scalar`.

## Main results

* `vSqZ_negTwo_mem_of_blockRelSpan` — `a[−2]b` lies in any degree-closed `T ⊇ blockRelSpan W z`;
* `grading_le_span_sup_blockRelSpan`;
* `span_sup_blockRelSpan_eq_top` — the span form, and
  `exists_finset_span_sup_blockRelSpan` in `Finset` shape.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Sole carried hypothesis: `VacuumGradeZero`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section

variable (W : VertexOperatorAlgebra 𝒱)

/-- **The `[−2]`-generator descends.**  Block condition (ii) writes `a[−2]b` as minus a finite
Eisenstein tail of strictly lower degree, modulo `blockRelSpan W z`. -/
theorem vSqZ_negTwo_mem_of_blockRelSpan (z : ℂ) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hp1 : 1 ≤ p) (hpq : p + q + 1 = n)
    (T : Submodule ℂ 𝒱) (hT : ∀ m : ℤ, m < n → W.grading m ≤ T)
    (hrel : blockRelSpan W z ≤ T) :
    vSqZ W a p.toNat (-2) b ∈ T := by
  classical
  have hka : 1 ≤ p.toNat := by omega
  have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by
    rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
  obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W a p.toNat b
  set tail : 𝒱 := ∑ m ∈ Finset.range K,
    (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z) • vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b
    with htail
  have hmem : vSqZ W a p.toNat (-2) b + tail ∈ T :=
    hrel (Submodule.subset_span (Or.inr ⟨p.toNat, K, a, b, hka, ha', hK, rfl⟩))
  have htailT : tail ∈ T := by
    rw [htail]
    refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_)
    refine vSqZ_mem_of_lower W ha hb p.toNat (2 * ((m : ℤ) + 2) - 2) T (fun d hd => ?_)
    exact hT d (by omega)
  have hsplit : vSqZ W a p.toNat (-2) b = (vSqZ W a p.toNat (-2) b + tail) - tail := by abel
  rw [hsplit]
  exact Submodule.sub_mem _ hmem htailT

/-- **The degree induction, with the deformed relations.** -/
theorem grading_le_span_sup_blockRelSpan (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) (z : ℂ) (n : ℤ) :
    W.grading n ≤ Submodule.span ℂ S ⊔ blockRelSpan W z := by
  classical
  set T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ blockRelSpan W z with hTdef
  have hrel : blockRelSpan W z ≤ T := le_sup_right
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
    have hexp := vSqZ_neg_two_eq W a p.toNat b
    have hstep : W.smul a (-2) b = vSqZ W a p.toNat (-2) b - sqDefect W a p.toNat b := by
      rw [hexp]
      show W.smul a (-2) b = mode (W.Y a) (-2) b + sqDefect W a p.toNat b
        - sqDefect W a p.toNat b
      rw [add_sub_cancel_right]
      rfl
    rw [hstep]
    refine Submodule.sub_mem _ ?_ (sqDefect_mem_of_lower W ha hb hpq hp0 T hT)
    rcases eq_or_lt_of_le hp0 with hp | hp1
    · -- grade `0`: `a ∈ ℂ𝟙`, so `a[−2]b` is a scalar multiple of `b ∈ 𝒱_{n−1}`
      have ha0 : a ∈ W.grading 0 := by rw [hp]; exact ha
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hzero ha0)
      have hp0' : p.toNat = 0 := by omega
      rw [hp0']
      have hlin : vSqZ W (c • W.vacuum) 0 (-2) b = c • vSqZ W W.vacuum 0 (-2) b := by
        rw [vSqZ_apply, vSqZ_apply,
          smul_finsum' c (sqModeZ_support_finite W W.vacuum 0 (-2) b)]
        refine finsum_congr (fun i => ?_)
        show sqBracketCoeffZ 0 (-2) i • W.smul (c • W.vacuum) i b
          = c • (sqBracketCoeffZ 0 (-2) i • W.smul W.vacuum i b)
        rw [PreVertexAlgebra.smul_smul_left, smul_comm]
      rw [hlin, vSqZ_vacuum_scalar, smul_smul]
      refine Submodule.smul_mem _ _ (hT q (by omega) hb)
    · exact vSqZ_negTwo_mem_of_blockRelSpan W z ha hb hp1 hpq T hT hrel

/-- **The span form of Zhu's descent**, for every `z`. -/
theorem span_sup_blockRelSpan_eq_top (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) (z : ℂ) :
    (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ blockRelSpan W z := by
  refine le_antisymm ?_ le_top
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_span_sup_blockRelSpan W hzero S hShom htop z m hx

/-- `Finset` form: `C₂`-cofiniteness gives `g + 1` vectors spanning `𝒱` modulo the deformed
relations, at **every** `z`. -/
theorem exists_finset_span_sup_blockRelSpan (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (z : ℂ) :
    ∃ T : Finset 𝒱, (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ blockRelSpan W z := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨(Finset.univ.image gen) ∪ {W.vacuum}, ?_⟩
  have hset : (((Finset.univ.image gen) ∪ {W.vacuum} : Finset 𝒱) : Set 𝒱)
      = Set.range gen ∪ {W.vacuum} := by
    ext x
    simp [Set.mem_range]
  rw [hset]
  refine span_sup_blockRelSpan_eq_top W hzero _ ?_ hdec z
  rintro s (⟨i, rfl⟩ | hs)
  · exact ⟨(wt i : ℤ), hgen i⟩
  · rw [Set.mem_singleton_iff] at hs
    exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩

/-! ## The fibre dimension, uniformly bounded -/

/-- The converse of `exists_finset_card_le_span_sup_eq_top`: a spanning family bounds the quotient.
-/
theorem finiteDimensional_and_finrank_quot_le_of_span_sup {K : Submodule ℂ 𝒱} (T : Finset 𝒱)
    (hT : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ K) :
    FiniteDimensional ℂ (𝒱 ⧸ K) ∧ Module.finrank ℂ (𝒱 ⧸ K) ≤ T.card := by
  classical
  have hspan : Submodule.span ℂ (K.mkQ '' (T : Set 𝒱)) = ⊤ := by
    rw [← Submodule.map_span, eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    have hx : x ∈ Submodule.span ℂ (T : Set 𝒱) ⊔ K := by rw [← hT]; trivial
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    have hw0 : K.mkQ w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hw
    rw [map_add, hw0, add_zero]
    exact Submodule.mem_map_of_mem hy
  have hfin : (K.mkQ '' (T : Set 𝒱)).Finite := T.finite_toSet.image _
  haveI : FiniteDimensional ℂ (𝒱 ⧸ K) :=
    Module.finite_def.mpr (hspan ▸ Submodule.fg_span (R := ℂ) hfin)
  refine ⟨inferInstance, ?_⟩
  have hle : Module.finrank ℂ (𝒱 ⧸ K)
      ≤ (T.image K.mkQ).card := by
    have himg : Submodule.span ℂ ((T.image K.mkQ : Finset (𝒱 ⧸ K)) : Set (𝒱 ⧸ K)) = ⊤ := by
      rw [Finset.coe_image]; exact hspan
    calc Module.finrank ℂ (𝒱 ⧸ K)
        = Module.finrank ℂ (Submodule.span ℂ ((T.image K.mkQ : Finset (𝒱 ⧸ K)) : Set (𝒱 ⧸ K))) := by
          rw [himg, finrank_top]
      _ ≤ (T.image K.mkQ).card := finrank_span_finset_le_card _
  exact hle.trans Finset.card_image_le

/-- **The fibre dimension is uniformly bounded**: at *every* `z`, `𝒱 ⧸ blockRelSpan W z` has
dimension at most the `C₂`-generator count `g + 1`.  (At the cusp it is exactly
`dim A(𝒱)/[A(𝒱),A(𝒱)]`, `finrank_quot_blockRelSpanAtCusp_eq` — the two together are what an
upper-semicontinuity argument would compare.) -/
theorem exists_finrank_quot_blockRelSpan_le (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    ∃ g : ℕ, ∀ z : ℂ, FiniteDimensional ℂ (𝒱 ⧸ blockRelSpan W z) ∧
      Module.finrank ℂ (𝒱 ⧸ blockRelSpan W z) ≤ g := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨((Finset.univ.image gen) ∪ {W.vacuum} : Finset 𝒱).card, fun z => ?_⟩
  obtain ⟨T, hT⟩ := exists_finset_span_sup_blockRelSpan W hzero hC2 z
  have hset : ∃ T' : Finset 𝒱, T' = (Finset.univ.image gen) ∪ {W.vacuum} := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ := hset
  have hspan : (⊤ : Submodule ℂ 𝒱)
      = Submodule.span ℂ (((Finset.univ.image gen) ∪ {W.vacuum} : Finset 𝒱) : Set 𝒱)
        ⊔ blockRelSpan W z := by
    have hcoe : ((((Finset.univ.image gen) ∪ {W.vacuum}) : Finset 𝒱) : Set 𝒱)
        = Set.range gen ∪ {W.vacuum} := by
      ext x; simp [Set.mem_range]
    rw [hcoe]
    refine span_sup_blockRelSpan_eq_top W hzero _ ?_ hdec z
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  exact finiteDimensional_and_finrank_quot_le_of_span_sup _ hspan

end

end VOA
