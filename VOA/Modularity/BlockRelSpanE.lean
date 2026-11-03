/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanning
import VOA.Modularity.BlockFiniteDim
import VOA.Modularity.E46Point
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Zhu Lemma 4.4.1 / DLM Lemma 5.2 — the relation module is finite over `ℂ[E₄,E₆]`

Zhu, J. AMS 9 (1996), **Lemma 4.4.1** (p. 281): *if `V` satisfies the finiteness condition then
`V[G̃₄, G̃₆]/O_q(V)` is a finitely generated `ℂ[G̃₄, G̃₆]`-module.*  Dong–Li–Mason,
`q-alg/9703016` **Lemma 5.2** (p. 27): *if `V` satisfies `C₂` then `V(T,T₁)/O(g,h)` is a finitely
generated `M(T,T₁)`-module.*  Untwisted, `M(1,1) = ℂ[E₄,E₆] = ` the repo's `E46`.

This is the key input for residual **(a)** — transporting Zhu Thm 5.3.3 from the cusp to a point of
`ℍ`.  It is **purely algebraic**: `C₂`-cofiniteness alone, no analysis, no differential equation.

## The structural point: do NOT base-change the graded machinery

Set `𝒱E := E46 ⊗[ℂ] 𝒱` and `ιE v := 1 ⊗ₜ v`.  For an `E46`-submodule `T_E ≤ 𝒱E`, the **pullback**
`pullback T_E := {v : 𝒱 | ιE v ∈ T_E}` is a plain `ℂ`-subspace of `𝒱`, and the whole degree
induction of `Modularity.BlockRelSpanning.grading_le_span_sup_blockRelSpan` runs verbatim on it.
Thirteen of its fourteen steps never leave `ℂ` — they use only that the target is a `ℂ`-subspace
closed under lower grades — so they are reused unchanged, via the banked
`grading_le_span_sup_O₂_inf`, `O₂_inf_grading_le_span_deg`, `vSqZ_neg_two_eq`,
`sqDefect_mem_of_lower`, `vSqZ_vacuum_scalar`, `vSqZ_mem_of_lower`.

Only the single `[−2]`-generator step needs the `E46` scalar, and that is
`vSqZ_negTwo_mem_of_blockRelSpanE` below.

⚠ This avoids `Submodule.baseChange_sup` and `Submodule.baseChange_inf`, which are **absent from
Mathlib** (and the latter is false without flatness).

## Main results

* `𝒱E`, `ιE`, `zhuGE`, `coefE`, `blockRelSpanE`, `pullback`;
* `span_range_ιE_eq_top` — `𝒱E` is generated over `E46` by `ιE '' 𝒱`;
* `vSqZ_negTwo_mem_of_blockRelSpanE` — the one step carrying an `E46` scalar;
* `grading_le_pullback` — the ported degree induction;
* `span_sup_blockRelSpanE_eq_top` and `moduleFinite_quot_blockRelSpanE` — **Zhu Lemma 4.4.1**.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Sole carried hypotheses: `VacuumGradeZero` and
`C2Cofinite` — the same two the cusp count already carries.
-/

namespace VOA

open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The base-changed space `E46 ⊗_ℂ 𝒱`. -/
abbrev 𝒱E (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] : Type u := ↥E46 ⊗[ℂ] 𝒱

/-- The canonical `ℂ`-linear inclusion `v ↦ 1 ⊗ v`. -/
noncomputable def ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱 := TensorProduct.mk ℂ (↥E46) 𝒱 1

@[simp] theorem ιE_apply (v : 𝒱) : (ιE v : 𝒱E 𝒱) = (1 : ↥E46) ⊗ₜ[ℂ] v := rfl

/-- `𝒱E` is generated over `E46` by the image of `𝒱`. -/
theorem span_range_ιE_eq_top :
    Submodule.span (↥E46) (Set.range (ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
      have hx : a ⊗ₜ[ℂ] v = a • ((1 : ↥E46) ⊗ₜ[ℂ] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Pull an `E46`-submodule of `𝒱E` back to a `ℂ`-subspace of `𝒱`. -/
noncomputable def pullback (T : Submodule (↥E46) (𝒱E 𝒱)) : Submodule ℂ 𝒱 :=
  (T.restrictScalars ℂ).comap (ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱)

@[simp] theorem mem_pullback {T : Submodule (↥E46) (𝒱E 𝒱)} {v : 𝒱} :
    v ∈ pullback T ↔ (ιE v : 𝒱E 𝒱) ∈ T := Iff.rfl

/-- The Eisenstein coefficient `G_{2j}` as an element of the ring `E46`. -/
noncomputable def zhuGE (j : ℕ) (hj : 2 ≤ j) : ↥E46 :=
  ⟨fun z : UpperHalfPlane => zhuGC j (z : ℂ), zhuGC_mem_E46 hj⟩

@[simp] theorem zhuGE_apply (j : ℕ) (hj : 2 ≤ j) (z : UpperHalfPlane) :
    (zhuGE j hj : UpperHalfPlane → ℂ) z = zhuGC j (z : ℂ) := rfl

/-- The full coefficient `(2(m+2)−1)·G_{2(m+2)}` of the `[−2]`-relation, in `E46`. -/
noncomputable def coefE (m : ℕ) : ↥E46 :=
  (((2 * (m + 2) - 1 : ℕ) : ℂ)) • zhuGE (m + 2) (by omega)

section

variable (W : VertexOperatorAlgebra 𝒱)

/-- **The `E46`-relation module** — `blockRelSpan` with the Eisenstein coefficients promoted
from numbers to ring elements.  This is DLM's `O(g,h) ⊆ V(T,T₁)` in the untwisted case. -/
noncomputable def blockRelSpanE : Submodule (↥E46) (𝒱E 𝒱) :=
  Submodule.span (↥E46)
    ({x : 𝒱E 𝒱 | ∃ (ka : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧
        x = ιE (vSqZ W a ka 0 v)} ∪
     {x : 𝒱E 𝒱 | ∃ (ka K : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧
        (∀ m : ℕ, K ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = ιE (vSqZ W a ka (-2) v) + ∑ m ∈ Finset.range K,
              coefE m • ιE (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v)})

/-- **The `[−2]`-generator descends, over `E46`.**  The port of
`vSqZ_negTwo_mem_of_blockRelSpan`; the Eisenstein tail is absorbed by an `E46` scalar rather than a
complex number, so the statement is uniform in `z`. -/
theorem vSqZ_negTwo_mem_of_blockRelSpanE {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hp1 : 1 ≤ p) (hpq : p + q + 1 = n)
    (T : Submodule (↥E46) (𝒱E 𝒱)) (hT : ∀ m : ℤ, m < n → W.grading m ≤ pullback T)
    (hrel : blockRelSpanE W ≤ T) :
    vSqZ W a p.toNat (-2) b ∈ pullback T := by
  classical
  have hka : 1 ≤ p.toNat := by omega
  have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by
    rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
  obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W a p.toNat b
  set tail : 𝒱E 𝒱 := ∑ m ∈ Finset.range K,
    coefE m • ιE (vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b) with htail
  have hmem : (ιE (vSqZ W a p.toNat (-2) b) : 𝒱E 𝒱) + tail ∈ T :=
    hrel (Submodule.subset_span (Or.inr ⟨p.toNat, K, a, b, hka, ha', hK, rfl⟩))
  have htailT : tail ∈ T := by
    rw [htail]
    refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_)
    have hlow : vSqZ W a p.toNat (2 * ((m : ℤ) + 2) - 2) b ∈ pullback T :=
      vSqZ_mem_of_lower W ha hb p.toNat (2 * ((m : ℤ) + 2) - 2) (pullback T)
        (fun d hd => hT d (by omega))
    exact hlow
  have hsplit : (ιE (vSqZ W a p.toNat (-2) b) : 𝒱E 𝒱)
      = ((ιE (vSqZ W a p.toNat (-2) b) : 𝒱E 𝒱) + tail) - tail := by abel
  rw [mem_pullback, hsplit]
  exact Submodule.sub_mem _ hmem htailT

/-- **The ported degree induction.**  Identical to
`grading_le_span_sup_blockRelSpan` except that the target is the pullback of an `E46`-submodule. -/
theorem grading_le_pullback (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (T : Submodule (↥E46) (𝒱E 𝒱))
    (hS : ∀ s ∈ S, (ιE s : 𝒱E 𝒱) ∈ T)
    (hrel : blockRelSpanE W ≤ T) (n : ℤ) :
    W.grading n ≤ pullback T := by
  classical
  have hSle : Submodule.span ℂ S ≤ pullback T := by
    rw [Submodule.span_le]
    intro s hs
    exact hS s hs
  rcases lt_or_ge n 0 with hneg | hnn
  · rw [W.positivity n hneg]; exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hT : ∀ m : ℤ, m < (N : ℤ) → W.grading m ≤ pullback T := by
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
    refine Submodule.sub_mem _ ?_ (sqDefect_mem_of_lower W ha hb hpq hp0 (pullback T) hT)
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
    · exact vSqZ_negTwo_mem_of_blockRelSpanE W ha hb hp1 hpq T hT hrel

/-- The span form over `E46`. -/
theorem pullback_eq_top (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (T : Submodule (↥E46) (𝒱E 𝒱))
    (hS : ∀ s ∈ S, (ιE s : 𝒱E 𝒱) ∈ T) (hrel : blockRelSpanE W ≤ T) :
    pullback T = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_pullback W hzero S hShom htop T hS hrel m hx

/-- **Zhu Lemma 4.4.1 / DLM Lemma 5.2, span form**: a finite family generates `𝒱E` over
`E46` modulo the relation module. -/
theorem span_sup_blockRelSpanE_eq_top (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) :
    (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      = Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S) ⊔ blockRelSpanE W := by
  set T : Submodule (↥E46) (𝒱E 𝒱) :=
    Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S) ⊔ blockRelSpanE W with hTdef
  have hS : ∀ s ∈ S, (ιE s : 𝒱E 𝒱) ∈ T := fun s hs =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
  have hrel : blockRelSpanE W ≤ T := le_sup_right
  have hpb := pullback_eq_top W hzero S hShom htop T hS hrel
  refine le_antisymm ?_ le_top
  rw [← span_range_ιE_eq_top (𝒱 := 𝒱), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have : v ∈ pullback T := by rw [hpb]; trivial
  exact this

/-- **Zhu Lemma 4.4.1 / DLM Lemma 5.2.**  For a `C₂`-cofinite VOA the deformed relation
quotient is a **finitely generated `ℂ[E₄,E₆]`-module**. -/
theorem moduleFinite_quot_blockRelSpanE (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    Module.Finite (↥E46) ((𝒱E 𝒱) ⧸ blockRelSpanE W) := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  set S : Set 𝒱 := Set.range gen ∪ {W.vacuum} with hSdef
  have hShom : ∀ s ∈ S, IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have htop := span_sup_blockRelSpanE_eq_top W hzero S hShom hdec
  have hSfin : S.Finite := (Set.finite_range gen).union (Set.finite_singleton _)
  have hfin : (((blockRelSpanE W).mkQ) '' ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S)).Finite :=
    (hSfin.image _).image _
  have hgen' : Submodule.span (↥E46)
      (((blockRelSpanE W).mkQ) '' ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := (blockRelSpanE W).mkQ_surjective y
    have hx : x ∈ Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S) ⊔ blockRelSpanE W := by
      rw [← htop]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    have hw0 : (blockRelSpanE W).mkQ w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hw
    rw [map_add, hw0, add_zero, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hu
  have hfg : (Submodule.span (↥E46)
      (((blockRelSpanE W).mkQ) '' ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S))).FG := Submodule.fg_span hfin
  rw [hgen'] at hfg
  exact ⟨hfg⟩

end

end VOA
