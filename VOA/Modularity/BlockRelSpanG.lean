/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanE
import VOA.Modularity.SubexpSeriesRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Zhu Lemma 4.4.1 over the **formal** ring `ℂ[G₂, G₄, G₆] ⊆ ℂ⟦q⟧`

`Modularity.BlockRelSpanE` proves Zhu Lemma 4.4.1 / DLM Lemma 5.2 over the *analytic* ring
`E46 ⊆ (ℍ → ℂ)`, which is what residual **(a)** (the cusp → interior transport) consumes.  Residual
**(c)** — the ODE route to the growth datum — needs the same statement over the **formal**
coefficient ring `GSeries = ℂ[G₂, G₄, G₆] ⊆ PowerSeries ℂ` of `Modularity.QExpansionBridge`, since
that is the ring which acts on `FormalQSeries` by `qConv` (`Modularity.QConvModule`).

**Shape-gate, verified declaration by declaration: nothing in `BlockRelSpanE` uses analyticity.**
Every step is either pure tensor algebra, or the `ℂ`-linear degree induction of
`Modularity.BlockRelSpanning`, or the single `[−2]`-generator step — and that step needs only that
the coefficient ring *contains the Eisenstein elements*.  `mk_zhuG_mem_GSeries` supplies them, so
the file transfers verbatim with `E46 ↦ GSeries`, `zhuGE ↦ zhuGG`.

## Main results

* `𝒱G`, `ιG`, `zhuGG`, `coefG`, `blockRelSpanG`, `pullbackG`;
* `vSqZ_negTwo_mem_of_blockRelSpanG` — the one step carrying a `GSeries` scalar;
* `grading_le_pullbackG` — the ported degree induction;
* `span_sup_blockRelSpanG_eq_top`, `moduleFinite_quot_blockRelSpanG` — **Zhu Lemma 4.4.1,
  formal form**.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Sole carried hypotheses: `VacuumGradeZero` and
`C2Cofinite` — exactly as in the analytic twin.
-/

namespace VOA

open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The base-changed space `GSeries ⊗_ℂ 𝒱`. -/
abbrev 𝒱G (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] : Type u := ↥GSeries ⊗[ℂ] 𝒱

/-- The canonical `ℂ`-linear inclusion `v ↦ 1 ⊗ v`. -/
noncomputable def ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱 := TensorProduct.mk ℂ (↥GSeries) 𝒱 1

@[simp] theorem ιG_apply (v : 𝒱) : (ιG v : 𝒱G 𝒱) = (1 : ↥GSeries) ⊗ₜ[ℂ] v := rfl

/-- `𝒱G` is generated over `GSeries` by the image of `𝒱`. -/
theorem span_range_ιG_eq_top :
    Submodule.span (↥GSeries) (Set.range (ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
      have hx : a ⊗ₜ[ℂ] v = a • ((1 : ↥GSeries) ⊗ₜ[ℂ] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Pull a `GSeries`-submodule of `𝒱G` back to a `ℂ`-subspace of `𝒱`. -/
noncomputable def pullbackG (T : Submodule (↥GSeries) (𝒱G 𝒱)) : Submodule ℂ 𝒱 :=
  (T.restrictScalars ℂ).comap (ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱)

@[simp] theorem mem_pullbackG {T : Submodule (↥GSeries) (𝒱G 𝒱)} {v : 𝒱} :
    v ∈ pullbackG T ↔ (ιG v : 𝒱G 𝒱) ∈ T := Iff.rfl

/-- The Eisenstein coefficient `G_{2j}` as an element of the ring `GSeries`. -/
noncomputable def zhuGG (j : ℕ) (hj : 1 ≤ j) : ↥GSeries :=
  ⟨PowerSeries.mk (zhuG j), mk_zhuG_mem_GSeries hj⟩

@[simp] theorem zhuGG_coe (j : ℕ) (hj : 1 ≤ j) :
    (zhuGG j hj : PowerSeries ℂ) = PowerSeries.mk (zhuG j) := rfl

/-- The full coefficient `(2(m+2)−1)·G_{2(m+2)}` of the `[−2]`-relation, in `GSeries`. -/
noncomputable def coefG (m : ℕ) : ↥GSeries :=
  (((2 * (m + 2) - 1 : ℕ) : ℂ)) • zhuGG (m + 2) (by omega)

@[simp] theorem coefG_coe (m : ℕ) :
    (coefG m : PowerSeries ℂ)
      = ((2 * (m + 2) - 1 : ℕ) : ℂ) • PowerSeries.mk (zhuG (m + 2)) := rfl

theorem coefG_mem (m : ℕ) : (coefG m : PowerSeries ℂ) ∈ GSeries := (coefG m).2

section

variable (W : VertexOperatorAlgebra 𝒱)

/-- **The `GSeries`-relation module** — `blockRelSpan` with the Eisenstein coefficients promoted
from numbers to ring elements.  This is DLM's `O(g,h) ⊆ V(T,T₁)` in the untwisted case. -/
noncomputable def blockRelSpanG : Submodule (↥GSeries) (𝒱G 𝒱) :=
  Submodule.span (↥GSeries)
    ({x : 𝒱G 𝒱 | ∃ (ka : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧
        x = ιG (vSqZ W a ka 0 v)} ∪
     {x : 𝒱G 𝒱 | ∃ (ka K : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧
        (∀ m : ℕ, K ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = ιG (vSqZ W a ka (-2) v) + ∑ m ∈ Finset.range K,
              coefG m • ιG (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v)})

/-- **The `[−2]`-generator descends, over `GSeries`.**  The port of
`vSqZ_negTwo_mem_of_blockRelSpan`; the Eisenstein tail is absorbed by a `GSeries` scalar rather
than a complex number. -/
theorem vSqZ_negTwo_mem_of_blockRelSpanG {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hp1 : 1 ≤ p) (hpq : p + q + 1 = n)
    (T : Submodule (↥GSeries) (𝒱G 𝒱)) (hT : ∀ m : ℤ, m < n → W.grading m ≤ pullbackG T)
    (hrel : blockRelSpanG W ≤ T) :
    vSqZ W a p.toNat (-2) b ∈ pullbackG T := by
  classical
  have hka : 1 ≤ p.toNat := by omega
  have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by
    rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
  obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W a p.toNat b
  set tail : 𝒱G 𝒱 := ∑ m ∈ Finset.range K,
    coefG m • ιG (vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b) with htail
  have hmem : (ιG (vSqZ W a p.toNat (-2) b) : 𝒱G 𝒱) + tail ∈ T :=
    hrel (Submodule.subset_span (Or.inr ⟨p.toNat, K, a, b, hka, ha', hK, rfl⟩))
  have htailT : tail ∈ T := by
    rw [htail]
    refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_)
    have hlow : vSqZ W a p.toNat (2 * ((m : ℤ) + 2) - 2) b ∈ pullbackG T :=
      vSqZ_mem_of_lower W ha hb p.toNat (2 * ((m : ℤ) + 2) - 2) (pullbackG T)
        (fun d hd => hT d (by omega))
    exact hlow
  have hsplit : (ιG (vSqZ W a p.toNat (-2) b) : 𝒱G 𝒱)
      = ((ιG (vSqZ W a p.toNat (-2) b) : 𝒱G 𝒱) + tail) - tail := by abel
  rw [mem_pullbackG, hsplit]
  exact Submodule.sub_mem _ hmem htailT

/-- **The ported degree induction.**  Identical to
`grading_le_span_sup_blockRelSpan` except that the target is the pullbackG of an `E46`-submodule. -/
theorem grading_le_pullbackG (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T)
    (hrel : blockRelSpanG W ≤ T) (n : ℤ) :
    W.grading n ≤ pullbackG T := by
  classical
  have hSle : Submodule.span ℂ S ≤ pullbackG T := by
    rw [Submodule.span_le]
    intro s hs
    exact hS s hs
  rcases lt_or_ge n 0 with hneg | hnn
  · rw [W.positivity n hneg]; exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hT : ∀ m : ℤ, m < (N : ℤ) → W.grading m ≤ pullbackG T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · rw [W.positivity m hm0]; exact bot_le
      · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
        exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans (grading_le_span_sup_O₂_inf W S hShom htop (N : ℤ)) ?_
    refine sup_le hSle ?_
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
    refine Submodule.sub_mem _ ?_ (sqDefect_mem_of_lower W ha hb hpq hp0 (pullbackG T) hT)
    rcases eq_or_lt_of_le hp0 with hp | hp1
    · have ha0 : a ∈ W.grading 0 := by rw [hp]; exact ha
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
    · exact vSqZ_negTwo_mem_of_blockRelSpanG W ha hb hp1 hpq T hT hrel

/-- The span form over `GSeries`. -/
theorem pullbackG_eq_top (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T) (hrel : blockRelSpanG W ≤ T) :
    pullbackG T = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_pullbackG W hzero S hShom htop T hS hrel m hx

/-- **Zhu Lemma 4.4.1 / DLM Lemma 5.2, span form**: a finite family generates `𝒱G` over
`GSeries` modulo the relation module. -/
theorem span_sup_blockRelSpanG_eq_top (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) :
    (⊤ : Submodule (↥GSeries) (𝒱G 𝒱))
      = Submodule.span (↥GSeries) ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S) ⊔ blockRelSpanG W := by
  set T : Submodule (↥GSeries) (𝒱G 𝒱) :=
    Submodule.span (↥GSeries) ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S) ⊔ blockRelSpanG W with hTdef
  have hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T := fun s hs =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
  have hrel : blockRelSpanG W ≤ T := le_sup_right
  have hpb := pullbackG_eq_top W hzero S hShom htop T hS hrel
  refine le_antisymm ?_ le_top
  rw [← span_range_ιG_eq_top (𝒱 := 𝒱), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have : v ∈ pullbackG T := by rw [hpb]; trivial
  exact this

/-- **Zhu Lemma 4.4.1 / DLM Lemma 5.2, formal form.**  For a `C₂`-cofinite VOA the deformed
relation quotient is a **finitely generated `ℂ[G₂,G₄,G₆]`-module**. -/
theorem moduleFinite_quot_blockRelSpanG (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    Module.Finite (↥GSeries) ((𝒱G 𝒱) ⧸ blockRelSpanG W) := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  set S : Set 𝒱 := Set.range gen ∪ {W.vacuum} with hSdef
  have hShom : ∀ s ∈ S, IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have htop := span_sup_blockRelSpanG_eq_top W hzero S hShom hdec
  have hSfin : S.Finite := (Set.finite_range gen).union (Set.finite_singleton _)
  have hfin : (((blockRelSpanG W).mkQ) '' ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S)).Finite :=
    (hSfin.image _).image _
  have hgen' : Submodule.span (↥GSeries)
      (((blockRelSpanG W).mkQ) '' ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := (blockRelSpanG W).mkQ_surjective y
    have hx : x ∈ Submodule.span (↥GSeries) ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S) ⊔ blockRelSpanG W := by
      rw [← htop]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    have hw0 : (blockRelSpanG W).mkQ w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hw
    rw [map_add, hw0, add_zero, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hu
  have hfg : (Submodule.span (↥GSeries)
      (((blockRelSpanG W).mkQ) '' ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S))).FG := Submodule.fg_span hfin
  rw [hgen'] at hfg
  exact ⟨hfg⟩

end

end VOA
