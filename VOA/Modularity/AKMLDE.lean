/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AKUniformODE
import VOA.Modularity.AKGrading
import VOA.Modularity.BlockRelSpanTransport

/-!
# The analytic Arakawa–Kawasetsu MLDE bridge

This file keeps three logically different rungs separate.

* The Etingof–Schedler finite spanning argument is ported from the formal ring
  `GSeries = ℂ[G₂,G₄,G₆]` to the analytic modular ring `E46 = ℂ[E₄,E₆]`.  It yields a common
  monic `L[-2]` relation with genuine analytic modular coefficients.
* `serreIterC` and `MonicMLDEOn` define an actual modular differential equation using iterated
  Serre derivatives and coefficients of their forced weights.
* `UniformSerreExpansionUpTo` freezes the exact unitriangular datum needed for the algebraic
  conversion.  Its coefficients are fixed after the primary insertion and before the analytic
  block, so a completed conversion is common to every eligible ordinary-module trace block.

Two substantive inputs remain: (a) the `E46SerreClosed` predicate isolated in
`EisensteinRamanujan` (from which `UniformSerreExpansionUpTo` is constructed below), and (b) the
direct-sum and relation-homogeneity data packaged by `AKWeightGrading`.  Given (b), total-weight
projection extracts the exact `E46Weight (2 * ((s - i : ℕ) : ℤ))` coefficient weights from the
common Noetherian relation; the final fixed-insertion MLDE is then assembled below.  No Euler
equation over `SubexpPS` is called an MLDE.

Input (a) is proved downstream: `VOA.e46SerreClosed` (`Modularity/EisensteinSerreClosure.lean`),
where the primed theorems `IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite'` and
`…_of_fin_gen'` discharge it.  Input (b), `AKWeightGrading`, remains an explicit hypothesis.
-/

namespace VOA

open scoped BigOperators TensorProduct
open ModularForm UpperHalfPlane

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section AnalyticPoisson

variable (W : VertexOperatorAlgebra 𝒱)

theorem vSqZ_zero_mem_blockRelSpanE {ka : ℕ} (hka : 1 ≤ ka) {a : 𝒱}
    (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) :
    (ιE (vSqZ W a ka 0 v) : 𝒱E 𝒱) ∈ blockRelSpanE W :=
  Submodule.subset_span (Or.inl ⟨ka, a, v, hka, ha, rfl⟩)

/-- The `₍₋₂₎`-generator step of the degree induction, extracted from `grading_le_pullback`
(where it appears inline). -/
theorem negTwo_mem_pullbackE (hzero : VacuumGradeZero W) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p + q + 1 = n)
    (T : Submodule (↥E46) (𝒱E 𝒱)) (hT : ∀ m : ℤ, m < n → W.grading m ≤ pullback T)
    (hrel : blockRelSpanE W ≤ T) :
    W.smul a (-2) b ∈ pullback T := by
  classical
  rcases lt_or_ge p 0 with hp | hp0
  · have ha0 : a = 0 := by
      rw [W.positivity p hp, Submodule.mem_bot] at ha; exact ha
    rw [ha0, W.smul_zero_left]
    exact Submodule.zero_mem _
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
      change sqBracketCoeffZ 0 (-2) i • W.smul (c • W.vacuum) i b
        = c • (sqBracketCoeffZ 0 (-2) i • W.smul W.vacuum i b)
      rw [PreVertexAlgebra.smul_smul_left, smul_comm]
    rw [hlin, vSqZ_vacuum_scalar, smul_smul]
    refine Submodule.smul_mem _ _ (hT q (by omega) hb)
  · exact vSqZ_negTwo_mem_of_blockRelSpanE W ha hb hp1 hpq T hT hrel

/-- **The bracket generator descends** — the new step.  For homogeneous `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`
with `p + q − 1 = n`, the Poisson representative `a₍₀₎b` lies in `pullback T` as soon as every
strictly lower degree does.

Compare `negTwo_mem_pullbackE`: this step is *easier*, because the `a[0]`-relation is exact — there
is no Eisenstein tail to absorb, hence no `vSqZ_mem_of_lower` bookkeeping and no `E46` scalar.
That is precisely Arakawa–Kawasetsu's "the generators `a[0]b` were free in Zhu's argument". -/
theorem brk_mem_pullbackE (hzero : VacuumGradeZero W) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p + q - 1 = n)
    (T : Submodule (↥E46) (𝒱E 𝒱)) (hT : ∀ m : ℤ, m < n → W.grading m ≤ pullback T)
    (hrel : blockRelSpanE W ≤ T) :
    W.smul a 0 b ∈ pullback T := by
  rcases lt_or_ge p 0 with hp | hp0
  · have ha0 : a = 0 := by
      rw [W.positivity p hp, Submodule.mem_bot] at ha; exact ha
    rw [ha0, W.smul_zero_left]
    exact Submodule.zero_mem _
  rcases eq_or_lt_of_le hp0 with hp | hp1
  · -- `p = 0`: `a = c·𝟙` and `𝟙₍₀₎b = 0`.
    have ha0 : a ∈ W.grading 0 := by rw [hp]; exact ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hzero ha0)
    rw [PreVertexAlgebra.smul_smul_left, W.smul_vacuum_left, if_neg (by norm_num), smul_zero]
    exact Submodule.zero_mem _
  · -- `p ≥ 1`: the exact `a[0]`-relation, minus a strictly lower-degree defect.
    have hka : 1 ≤ p.toNat := by omega
    have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by
      rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
    have hrelmem : vSqZ W a p.toNat 0 b ∈ pullback T :=
      hrel (vSqZ_zero_mem_blockRelSpanE W hka ha' b)
    have hdef : sqDefect0 W a p.toNat b ∈ pullback T :=
      sqDefect0_mem_of_lower W ha hb hpq (pullback T) hT
    have hstep : W.smul a 0 b = vSqZ W a p.toNat 0 b - sqDefect0 W a p.toNat b := by
      rw [vSqZ_zero_eq W a p.toNat b]
      show W.smul a 0 b = mode (W.Y a) 0 b + sqDefect0 W a p.toNat b - sqDefect0 W a p.toNat b
      rw [add_sub_cancel_right]
      rfl
    rw [hstep]
    exact Submodule.sub_mem _ hrelmem hdef

/-- **The degree induction, with the augmented relation space.**  Verbatim
`grading_le_pullback` except that the spanning hypothesis is modulo `O₂P W = O₂ W + {𝒱,𝒱}` rather
than modulo `O₂ W`, and the induction therefore has a second generator branch, `brk_mem_pullbackE`.
-/
theorem grading_le_pullbackE_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W)
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
    refine le_trans (grading_le_span_sup_O₂P_inf W S hShom htop (N : ℤ)) ?_
    refine sup_le hSle ?_
    refine le_trans (O₂P_inf_grading_le_span_deg W (N : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g (⟨p, q, a, b, ha, hb, hpq, rfl⟩ | ⟨p, q, a, b, ha, hb, hpq, rfl⟩)
    · exact negTwo_mem_pullbackE W hzero ha hb hpq T hT hrel
    · exact brk_mem_pullbackE W hzero ha hb hpq T hT hrel

/-- The pullback form. -/
theorem pullbackE_eq_top_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W)
    (T : Submodule (↥E46) (𝒱E 𝒱))
    (hS : ∀ s ∈ S, (ιE s : 𝒱E 𝒱) ∈ T) (hrel : blockRelSpanE W ≤ T) :
    pullback T = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_pullbackE_of_poisson W hzero S hShom htop T hS hrel m hx

/-- **Arakawa–Kawasetsu Proposition 5.2, span form.**  A finite family spanning `𝒱` modulo
`O₂(𝒱) + {𝒱,𝒱}` already generates `𝒱E = ℂ[E₄,E₆] ⊗ 𝒱` over `ℂ[E₄,E₆]` modulo the relation
module `blockRelSpanE` (= AK's `[V_A, V_A] + O_q(V)`).

This is the identical conclusion of `span_sup_blockRelSpanE_eq_top` (Zhu Lemma 4.4.1 / DLM Lemma
5.2) under a **strictly weaker** spanning hypothesis, which is exactly the content of AK §5. -/
theorem span_sup_blockRelSpanE_eq_top_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W) :
    (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      = Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S) ⊔ blockRelSpanE W := by
  set T : Submodule (↥E46) (𝒱E 𝒱) :=
    Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S) ⊔ blockRelSpanE W with hTdef
  have hS : ∀ s ∈ S, (ιE s : 𝒱E 𝒱) ∈ T := fun s hs =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
  have hrel : blockRelSpanE W ≤ T := le_sup_right
  have hpb := pullbackE_eq_top_of_poisson W hzero S hShom htop T hS hrel
  refine le_antisymm ?_ le_top
  rw [← span_range_ιE_eq_top (𝒱 := 𝒱), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have : v ∈ pullback T := by rw [hpb]; trivial
  exact this



end AnalyticPoisson

section AnalyticUniformRelation

variable (W : VertexOperatorAlgebra 𝒱)

/-- Arakawa–Kawasetsu Proposition 5.2 over the analytic modular coefficient ring `E46`.
Unlike the existing `GSeries` statement, this family has no quasimodular `G₂` generator. -/
theorem exists_finite_gen_sup_blockRelSpanE_of_etingofFinite (hzero : VacuumGradeZero W)
    (hE : EtingofFinite W) :
    ∃ T : Set (𝒱E 𝒱), T.Finite ∧
      (⊤ : Submodule (↥E46) (𝒱E 𝒱))
        = Submodule.span (↥E46) T ⊔ blockRelSpanE W := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_etingofFinite W hE
  set S : Set 𝒱 := Set.range gen ∪ {W.vacuum} with hSdef
  have hShom : ∀ s ∈ S, IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have hSfin : S.Finite := (Set.finite_range gen).union (Set.finite_singleton _)
  exact ⟨(ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' S, hSfin.image _,
    span_sup_blockRelSpanE_eq_top_of_poisson W hzero S hShom hdec⟩

set_option synthInstance.maxHeartbeats 100000 in
-- The Noetherian instance search in this finite-generation argument exceeds the default budget.
/-- A common monic `L[-2]` relation with analytic `E46` coefficients, produced before any block
or module is chosen. -/
theorem exists_uniform_monic_Lsq_relationE_of_fin_gen
    (T : Set (𝒱E 𝒱)) (hTfin : T.Finite)
    (htop : (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      = Submodule.span (↥E46) T ⊔ blockRelSpanE W) (a : 𝒱) :
    ∃ (s : ℕ) (c : ℕ → ↥E46), 1 ≤ s ∧
      (ιE ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanE W := by
  letI : IsNoetherianRing (↥E46) := isNoetherianRing_E46
  exact exists_monic_relation_mem_of_fin_gen (blockRelSpanE W) T hTfin htop
    (fun i => ιE ((⇑(Lsq W (-2)))^[i] a))

/-- Analytic-coefficient AK Lemma 5.3 from the Etingof–Schedler finiteness hypothesis. -/
theorem exists_uniform_monic_Lsq_relationE_mem_of_etingofFinite
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) (a : 𝒱) :
    ∃ (s : ℕ) (c : ℕ → ↥E46), 1 ≤ s ∧
      (ιE ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanE W := by
  obtain ⟨T, hTfin, htop⟩ := exists_finite_gen_sup_blockRelSpanE_of_etingofFinite W hzero hE
  exact exists_uniform_monic_Lsq_relationE_of_fin_gen W T hTfin htop a

end AnalyticUniformRelation

section AnalyticEvaluation

variable {W : VertexOperatorAlgebra 𝒱}

/-- Every analytic block evaluates an upstairs `E46` relation to the same scalar relation.  The
coefficient family is chosen before `F`; this is the point at which uniformity across ordinary
modules is preserved. -/
theorem IsAnalyticBlock.Lsq_relation_of_mem {F : 𝒱 → ℂ → ℂ} (hF : IsAnalyticBlock W F)
    {s : ℕ} {c : ℕ → ↥E46} {a : 𝒱}
    (hmem : (ιE ((⇑(Lsq W (-2)))^[s] a)
      - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanE W)
    {z : ℂ} (hz : z ∈ imGT 0) :
    F ((⇑(Lsq W (-2)))^[s] a) z =
      ∑ i ∈ Finset.range s, e46C (c i) z * F ((⇑(Lsq W (-2)))^[i] a) z := by
  classical
  letI : AddCommGroup (𝒱E 𝒱) := TensorProduct.addCommGroup
  let z₀ : UpperHalfPlane := ⟨z, hz⟩
  have hrel := evalAt_mem_blockRelSpan W z₀ hmem
  have hzero := (mem_blockKerAt hF z _).mp (hF.blockRelSpan_le_kerAt hz hrel)
  rw [map_sub, map_sum, evalAt_ιE] at hzero
  simp only [evalAt_smul, evalAt_ιE] at hzero
  have hsub : ∀ x y : 𝒱, F (x - y) z = F x z - F y z := by
    intro x y
    rw [sub_eq_add_neg, hF.addv]
    have hneg := hF.smulv (-1) y z
    rw [neg_one_smul] at hneg
    rw [hneg]
    ring
  rw [hsub, hF.map_finsetSum] at hzero
  simp only [hF.smulv] at hzero
  have hev : ∀ i : ℕ, evAt z₀ (c i) = e46C (c i) z := by
    intro i
    rw [evAt_apply, e46C_of_mem (c i) hz]
  simp_rw [hev] at hzero
  exact eq_of_sub_eq_zero hzero

end AnalyticEvaluation

/-! ## Genuine Serre-derivative MLDEs -/

/-- The iterated Serre derivative, with the operator weight raised by two at each step. -/
noncomputable def serreIterC (wt : ℤ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, f => f
  | i + 1, f => serreDerivC (wt + 2 * (i : ℤ)) (serreIterC wt i f)

@[simp] theorem serreIterC_zero (wt : ℤ) (f : ℂ → ℂ) : serreIterC wt 0 f = f := rfl

@[simp] theorem serreIterC_succ (wt : ℤ) (i : ℕ) (f : ℂ → ℂ) :
    serreIterC wt (i + 1) f =
      serreDerivC (wt + 2 * (i : ℤ)) (serreIterC wt i f) := rfl

/-- Iterated Serre derivatives preserve analyticity at upper-half-plane points. -/
theorem analyticAt_serreIterC (wt : ℤ) (i : ℕ) {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ∈ imGT 0) :
    AnalyticAt ℂ (serreIterC wt i f) z := by
  induction i with
  | zero => simpa using hf
  | succ i ih =>
      rw [serreIterC_succ]
      exact analyticAt_serreDerivC _ ih hz

/-- A monic MLDE on the upper half-plane.  The coefficient of the `i`-th Serre iterate has the
forced modular weight `2(s-i)`; hence every coefficient is a genuine level-one modular form, not
merely a formal or subexponential power series. -/
def MonicMLDEOn (wt : ℤ) (f : ℂ → ℂ) (s : ℕ) (p : ℕ → E46) : Prop :=
  1 ≤ s ∧
    (∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (p i)) ∧
    ∀ z ∈ imGT 0, serreIterC wt s f z
      + ∑ i ∈ Finset.range s, e46C (p i) z * serreIterC wt i f z = 0

/-- A block-independent unitriangular conversion of the fixed insertion's `L[-2]` tower into its
Serre tower, through order `s`.  The coefficient array is chosen before `F`; coefficients on and
above the diagonal vanish, and lower entries carry their exact weight.

Below it is constructed from `IsSqPrimary` and the explicitly named `E46SerreClosed` property.
It is stronger than the block-dependent `SubexpPS` expansion in `AKModularODE`. -/
def UniformSerreExpansionUpTo (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (wt : ℤ) (s : ℕ)
    (h : ℕ → ℕ → E46) : Prop :=
  (∀ i ≤ s, ∀ j, i ≤ j → h i j = 0) ∧
  (∀ i ≤ s, ∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (h i j)) ∧
  ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F → ∀ i ≤ s, ∀ z ∈ imGT 0,
    F ((⇑(Lsq W (-2)))^[i] a) z = serreIterC wt i (F a) z
      + ∑ j ∈ Finset.range s, e46C (h i j) z * serreIterC wt j (F a) z

/-- The rowwise form of the block-independent Serre expansion.  Its finite sum has the natural
cutoff `i`; `UniformSerreExpansionUpTo` is obtained by padding these rows with zeros. -/
def UniformSerreExpansionRow (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (wt : ℤ) (i : ℕ)
    (r : ℕ → E46) : Prop :=
  (∀ j, i ≤ j → r j = 0) ∧
  (∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (r j)) ∧
  ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F → ∀ z ∈ imGT 0,
    F ((⇑(Lsq W (-2)))^[i] a) z = serreIterC wt i (F a) z
      + ∑ j ∈ Finset.range i, e46C (r j) z * serreIterC wt j (F a) z

/-- Adjoin the unit diagonal entry to a strict-lower-triangular expansion row. -/
noncomputable def fullSerreRowCoeff (i : ℕ) (r : ℕ → E46) (j : ℕ) : E46 :=
  if j = i then 1 else r j

@[simp] theorem fullSerreRowCoeff_diag (i : ℕ) (r : ℕ → E46) :
    fullSerreRowCoeff i r i = 1 := by
  simp [fullSerreRowCoeff]

theorem fullSerreRowCoeff_of_lt {i j : ℕ} (r : ℕ → E46) (hj : j < i) :
    fullSerreRowCoeff i r j = r j := by
  simp [fullSerreRowCoeff, Nat.ne_of_lt hj]

theorem UniformSerreExpansionRow.fullCoeff_weight
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {i : ℕ} {r : ℕ → E46}
    (hr : UniformSerreExpansionRow W a wt i r) {j : ℕ} (hj : j ≤ i) :
    E46Weight (2 * ((i - j : ℕ) : ℤ)) (fullSerreRowCoeff i r j) := by
  rcases eq_or_lt_of_le hj with rfl | hji
  · simpa using E46Weight.one
  · rw [fullSerreRowCoeff_of_lt r hji]
    exact hr.2.1 j hji

theorem UniformSerreExpansionRow.fullCoeff_eq_zero_of_lt
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {i : ℕ} {r : ℕ → E46}
    (hr : UniformSerreExpansionRow W a wt i r) {j : ℕ} (hij : i < j) :
    fullSerreRowCoeff i r j = 0 := by
  rw [fullSerreRowCoeff, if_neg (Nat.ne_of_lt hij).symm]
  exact hr.1 j (Nat.le_of_lt hij)

/-- The full row evaluates as the diagonal Serre iterate plus the strict lower row. -/
theorem fullSerreRowCoeff_sum (i : ℕ) (r : ℕ → E46) (D : ℕ → ℂ) (z : ℂ) :
    ∑ j ∈ Finset.range (i + 1), e46C (fullSerreRowCoeff i r j) z * D j =
      D i + ∑ j ∈ Finset.range i, e46C (r j) z * D j := by
  rw [Finset.sum_range_succ]
  have hbelow : ∑ j ∈ Finset.range i, e46C (fullSerreRowCoeff i r j) z * D j =
      ∑ j ∈ Finset.range i, e46C (r j) z * D j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [fullSerreRowCoeff_of_lt r (Finset.mem_range.mp hj)]
  rw [hbelow, fullSerreRowCoeff_diag, e46C_one]
  simp
  ring

theorem UniformSerreExpansionRow.fullCoeff_sum_of_le
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {i : ℕ} {r : ℕ → E46}
    (hr : UniformSerreExpansionRow W a wt i r) {k : ℕ} (hik : i ≤ k)
    (D : ℕ → ℂ) (z : ℂ) :
    ∑ j ∈ Finset.range (k + 1), e46C (fullSerreRowCoeff i r j) z * D j =
      D i + ∑ j ∈ Finset.range i, e46C (r j) z * D j := by
  rw [← fullSerreRowCoeff_sum i r D z]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hjbig hjsmall
  simp only [Finset.mem_range, not_lt] at hjbig hjsmall
  rw [hr.fullCoeff_eq_zero_of_lt (by omega), e46C_zero]
  simp

/-- Coefficientwise Serre derivative of the strict lower part of an expansion row. -/
noncomputable def serreRowDerivCoeff (hclose : E46SerreClosed) (i : ℕ) (r : ℕ → E46)
    (hr : ∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (r j)) (j : ℕ) : E46 :=
  if hj : j < i then
    hclose.derivCoeff (2 * ((i - j : ℕ) : ℤ)) (r j) (hr j hj)
  else 0

/-- Shifting the Serre iterate in a product sends row coefficient `j` to slot `j+1`. -/
noncomputable def serreRowShiftCoeff (r : ℕ → E46) : ℕ → E46
  | 0 => 0
  | j + 1 => r j

theorem serreRowShiftCoeff_sum (i : ℕ) (r : ℕ → E46) (D : ℕ → ℂ) (z : ℂ) :
    ∑ j ∈ Finset.range (i + 1), e46C (serreRowShiftCoeff r j) z * D j =
      ∑ j ∈ Finset.range i, e46C (r j) z * D (j + 1) := by
  rw [Finset.sum_range_succ']
  simp [serreRowShiftCoeff]

/-- The coefficient contribution of the positive-mode tail in the `omega` recursion. -/
noncomputable def omegaTailRowCoeff (W : VertexOperatorAlgebra 𝒱) (wt : ℤ) (k : ℕ)
    (R : ℕ → ℕ → E46) (j : ℕ) : E46 :=
  ∑ m ∈ Finset.range k,
    towerScalar (wt : ℂ) W.centralCharge (m + 1) k •
      (zhuGE (m + 2) (by omega) * fullSerreRowCoeff (k - m - 1) (R (k - m - 1)) j)

/-- The explicit successor row dictated by the graded Leibniz rule and the Virasoro tail. -/
noncomputable def serreRowSuccCoeff (W : VertexOperatorAlgebra 𝒱) (hclose : E46SerreClosed)
    (wt : ℤ) (k : ℕ) (R : ℕ → ℕ → E46)
    (hRk : ∀ j < k, E46Weight (2 * ((k - j : ℕ) : ℤ)) (R k j)) (j : ℕ) : E46 :=
  serreRowDerivCoeff hclose k (R k) hRk j + serreRowShiftCoeff (R k) j
    + omegaTailRowCoeff W wt k R j

theorem serreRowDerivCoeff_weight (hclose : E46SerreClosed) (i : ℕ) (r : ℕ → E46)
    (hr : ∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (r j))
    (j : ℕ) :
    E46Weight (2 * (((i + 1) - j : ℕ) : ℤ)) (serreRowDerivCoeff hclose i r hr j) := by
  by_cases hji : j < i
  · rw [serreRowDerivCoeff, dif_pos hji]
    have hwt := hclose.derivCoeff_weight (2 * ((i - j : ℕ) : ℤ)) (r j) (hr j hji)
    convert hwt using 1
    omega
  · rw [serreRowDerivCoeff, dif_neg hji]
    exact E46Weight.zero _

theorem serreRowDerivCoeff_apply (hclose : E46SerreClosed) (i : ℕ) (r : ℕ → E46)
    (hr : ∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (r j))
    {j : ℕ} (hj : j < i) {z : ℂ} (hz : z ∈ imGT 0) :
    e46C (serreRowDerivCoeff hclose i r hr j) z =
      serreDerivC (2 * ((i - j : ℕ) : ℤ)) (e46C (r j)) z := by
  rw [serreRowDerivCoeff, dif_pos hj]
  exact hclose.derivCoeff_apply _ _ _ hz

theorem serreRowDerivCoeff_sum (hclose : E46SerreClosed) (i : ℕ) (r : ℕ → E46)
    (hr : ∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (r j))
    (D : ℕ → ℂ) (z : ℂ) :
    ∑ j ∈ Finset.range (i + 1), e46C (serreRowDerivCoeff hclose i r hr j) z * D j =
      ∑ j ∈ Finset.range i, e46C (serreRowDerivCoeff hclose i r hr j) z * D j := by
  rw [Finset.sum_range_succ, serreRowDerivCoeff, dif_neg (lt_irrefl i), e46C_zero]
  simp

/-- Differentiate a weighted strict-lower row coefficientwise. -/
theorem serreDerivC_serreRow_sum
    {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ} (hF : IsAnalyticBlock W F)
    {a : 𝒱} {wt : ℤ} (hclose : E46SerreClosed) (i : ℕ) (r : ℕ → E46)
    (hr : ∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (r j))
    {z : ℂ} (hz : z ∈ imGT 0) :
    serreDerivC (wt + 2 * (i : ℤ))
        (∑ j ∈ Finset.range i, e46C (r j) * serreIterC wt j (F a)) z =
      ∑ j ∈ Finset.range i,
        (e46C (serreRowDerivCoeff hclose i r hr j) z * serreIterC wt j (F a) z
          + e46C (r j) z * serreIterC wt (j + 1) (F a) z) := by
  have hbase : AnalyticAt ℂ (F a) z :=
    ((hF.holo a).analyticOnNhd (isOpen_imGT 0)) z hz
  rw [serreDerivC_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j < i := Finset.mem_range.mp hj
    have hD := analyticAt_serreIterC wt j hbase hz
    have hprod := hclose.serreDerivC_e46C_mul (hr j hji)
      (wt + 2 * (j : ℤ)) (serreIterC wt j (F a)) hz hD.differentiableAt
    rw [hclose.derivCoeff_apply _ _ _ hz] at hprod
    rw [← serreIterC_succ] at hprod
    rw [serreRowDerivCoeff_apply hclose i r hr hji hz]
    convert hprod using 1
    rw [Nat.cast_sub (Nat.le_of_lt hji)]
    ring_nf
  · intro j hj
    have hji : j < i := Finset.mem_range.mp hj
    exact (hr j hji).differentiableAt_e46C hz |>.mul
      (analyticAt_serreIterC wt j hbase hz).differentiableAt

theorem serreRowShiftCoeff_weight {i : ℕ} {r : ℕ → E46}
    (hr : ∀ j < i, E46Weight (2 * ((i - j : ℕ) : ℤ)) (r j))
    {j : ℕ} (hj : j ≤ i) :
    E46Weight (2 * (((i + 1) - j : ℕ) : ℤ)) (serreRowShiftCoeff r j) := by
  cases j with
  | zero =>
      rw [serreRowShiftCoeff]
      exact E46Weight.zero _
  | succ j =>
      rw [serreRowShiftCoeff]
      convert hr j (by omega) using 1
      omega

theorem omegaTailRowCoeff_weight
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {k : ℕ}
    {R : ℕ → ℕ → E46}
    (hR : ∀ t ≤ k, UniformSerreExpansionRow W a wt t (R t))
    {j : ℕ} (hj : j ≤ k) :
    E46Weight (2 * (((k + 1) - j : ℕ) : ℤ)) (omegaTailRowCoeff W wt k R j) := by
  apply E46Weight.sum
  intro m hm
  have hmk : m < k := Finset.mem_range.mp hm
  let t : ℕ := k - m - 1
  have htk : t ≤ k := by simp only [t]; omega
  by_cases hjt : j ≤ t
  · have hprod := (zhuGE_weight (m + 2) (by omega)).mul
        ((hR t htk).fullCoeff_weight hjt)
    have hsmul := hprod.smul (towerScalar (wt : ℂ) W.centralCharge (m + 1) k)
    convert hsmul using 1
    simp only [t]
    omega
  · have htj : t < j := by omega
    have hzero : E46Weight
        (2 * (((k + 1) - j : ℕ) : ℤ) - 2 * ((m + 2 : ℕ) : ℤ))
        (fullSerreRowCoeff t (R t) j) := by
      rw [(hR t htk).fullCoeff_eq_zero_of_lt htj]
      exact E46Weight.zero _
    have hprod := (zhuGE_weight (m + 2) (by omega)).mul hzero
    have hsmul := hprod.smul (towerScalar (wt : ℂ) W.centralCharge (m + 1) k)
    convert hsmul using 1
    ring

/-- Evaluation of the collected positive-mode tail coefficients. -/
theorem omegaTailRowCoeff_sum
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {k : ℕ}
    {R : ℕ → ℕ → E46}
    (hR : ∀ t ≤ k, UniformSerreExpansionRow W a wt t (R t))
    (D : ℕ → ℂ) {z : ℂ} (hz : z ∈ imGT 0) :
    ∑ j ∈ Finset.range (k + 1), e46C (omegaTailRowCoeff W wt k R j) z * D j =
      ∑ m ∈ Finset.range k,
        towerScalar (wt : ℂ) W.centralCharge (m + 1) k * zhuGC (m + 2) z *
          (D (k - m - 1) + ∑ j ∈ Finset.range (k - m - 1),
            e46C (R (k - m - 1) j) z * D j) := by
  let A : ℕ → ℂ := fun m =>
    towerScalar (wt : ℂ) W.centralCharge (m + 1) k * zhuGC (m + 2) z
  let B : ℕ → ℕ → ℂ := fun m j =>
    e46C (fullSerreRowCoeff (k - m - 1) (R (k - m - 1)) j) z
  have heval (j : ℕ) : e46C (omegaTailRowCoeff W wt k R j) z =
      ∑ m ∈ Finset.range k, A m * B m j := by
    rw [omegaTailRowCoeff, e46C_finset_sum, Finset.sum_apply]
    change (∑ m ∈ Finset.range k,
      e46C (towerScalar (wt : ℂ) W.centralCharge (m + 1) k •
        (zhuGE (m + 2) (by omega) *
          fullSerreRowCoeff (k - m - 1) (R (k - m - 1)) j)) z) = _
    apply Finset.sum_congr rfl
    intro m hm
    change towerScalar (wt : ℂ) W.centralCharge (m + 1) k *
        (e46C (zhuGE (m + 2) (by omega)) z *
          e46C (fullSerreRowCoeff (k - m - 1) (R (k - m - 1)) j) z) = A m * B m j
    rw [e46C_of_mem (zhuGE (m + 2) (by omega)) hz, zhuGE_apply]
    simp only [A, B]
    ring
  simp_rw [heval]
  have hcomm :
      ∑ j ∈ Finset.range (k + 1),
          (∑ m ∈ Finset.range k, A m * B m j) * D j =
        ∑ m ∈ Finset.range k, A m *
          (∑ j ∈ Finset.range (k + 1), B m j * D j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcomm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m < k := Finset.mem_range.mp hm
  rw [(hR (k - m - 1) (by omega)).fullCoeff_sum_of_le (by omega) D z]

theorem serreRowSuccCoeff_weight
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {k : ℕ}
    (hclose : E46SerreClosed) {R : ℕ → ℕ → E46}
    (hR : ∀ t ≤ k, UniformSerreExpansionRow W a wt t (R t))
    {j : ℕ} (hj : j < k + 1) :
    E46Weight (2 * (((k + 1) - j : ℕ) : ℤ))
      (serreRowSuccCoeff W hclose wt k R (hR k (le_refl k)).2.1 j) := by
  exact ((serreRowDerivCoeff_weight hclose k (R k) (hR k (le_refl k)).2.1 j).add
    (serreRowShiftCoeff_weight (hR k (le_refl k)).2.1 (by omega))).add
      (omegaTailRowCoeff_weight hR (by omega))

theorem serreRowSuccCoeff_eq_zero
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {k : ℕ}
    (hclose : E46SerreClosed) {R : ℕ → ℕ → E46}
    (hR : ∀ t ≤ k, UniformSerreExpansionRow W a wt t (R t))
    {j : ℕ} (hj : k + 1 ≤ j) :
    serreRowSuccCoeff W hclose wt k R (hR k (le_refl k)).2.1 j = 0 := by
  have hderiv : serreRowDerivCoeff hclose k (R k) (hR k (le_refl k)).2.1 j = 0 := by
    rw [serreRowDerivCoeff, dif_neg (by omega)]
  have hshift : serreRowShiftCoeff (R k) j = 0 := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [serreRowShiftCoeff]
    exact (hR k (le_refl k)).1 j' (by omega)
  have htail : omegaTailRowCoeff W wt k R j = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hmk : m < k := Finset.mem_range.mp hm
    have htj : k - m - 1 < j := by omega
    rw [(hR (k - m - 1) (by omega)).fullCoeff_eq_zero_of_lt htj, mul_zero]
    apply Subtype.ext
    funext z
    change towerScalar (wt : ℂ) W.centralCharge (m + 1) k * 0 = 0
    ring
  simp [serreRowSuccCoeff, hderiv, hshift, htail]

/-- The `L[-2]` tower over an integral-weight square-primary vector remains in the corresponding
integral square-weight spaces. -/
theorem IsSqPrimary.negTwo_iterate_mem_sqWeightSpace
    (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (i : ℕ) :
    ((⇑(Lsq W (-2)))^[i] a) ∈ sqWeightSpace W (((wt + 2 * (i : ℤ) : ℤ)) : ℂ) := by
  rw [mem_sqWeightSpace_iff]
  have ht := Lsq_tower W ha i 0
  simp only [Nat.cast_zero, mul_zero, Nat.sub_zero, towerScalar_zero_left] at ht
  rw [ht]
  congr 1
  push_cast
  ring

/-- The embedded `L[-2]` tower has total AK weight `wt + 2i`. -/
theorem IsSqPrimary.ιE_negTwo_iterate_mem_akTotalWeightSpace
    (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (i : ℕ) :
    (ιE ((⇑(Lsq W (-2)))^[i] a) : 𝒱E 𝒱) ∈ akTotalWeightSpace W (wt + 2 * (i : ℤ)) :=
  ιE_mem_akTotalWeightSpace W (ha.negTwo_iterate_mem_sqWeightSpace W i)

set_option synthInstance.maxHeartbeats 100000 in
-- Tensor-product additive and scalar instances are expensive in the component calculation.
/-- Project a common monic relation to the total weight of its leading term.  The projection
canonically replaces every coefficient by its component of weight `2(s-i)`. -/
theorem AKWeightGrading.weighted_Lsq_relation_of_mem
    {W : VertexOperatorAlgebra 𝒱} (hgrade : AKWeightGrading W)
    {a : 𝒱} {wt : ℤ} (ha : IsSqPrimary W a (wt : ℂ))
    {s : ℕ} {c : ℕ → E46}
    (hmem : (ιE ((⇑(Lsq W (-2)))^[s] a)
      - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanE W) :
    ∃ c' : ℕ → E46,
      (∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (c' i)) ∧
      (ιE ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c' i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈
          blockRelSpanE W := by
  classical
  letI := hgrade.coeffDecomposition
  letI := hgrade.totalDecomposition
  let c' : ℕ → E46 := fun i =>
    DirectSum.decompose e46WeightSpace (c i) (2 * ((s - i : ℕ) : ℤ))
  refine ⟨c', ?_, ?_⟩
  · intro i hi
    exact (DirectSum.decompose e46WeightSpace (c i) (2 * ((s - i : ℕ) : ℤ))).2
  · let n : ℤ := wt + 2 * (s : ℤ)
    let rel : 𝒱E 𝒱 := ιE ((⇑(Lsq W (-2)))^[s] a)
      - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)
    let proj : 𝒱E 𝒱 →+ 𝒱E 𝒱 :=
      (akTotalWeightSpace W n).subtype.toAddMonoidHom.comp
        ((DFinsupp.evalAddMonoidHom n).comp
          (DirectSum.decomposeAddEquiv (akTotalWeightSpace W)).toAddMonoidHom)
    have hlead : proj (ιE ((⇑(Lsq W (-2)))^[s] a)) =
        ιE ((⇑(Lsq W (-2)))^[s] a) := by
      change ((DirectSum.decompose (akTotalWeightSpace W)
        (ιE ((⇑(Lsq W (-2)))^[s] a)) n : akTotalWeightSpace W n) : 𝒱E 𝒱) = _
      exact DirectSum.decompose_of_mem_same (akTotalWeightSpace W)
        (ha.ιE_negTwo_iterate_mem_akTotalWeightSpace W s)
    have hterm (i : ℕ) (hi : i ∈ Finset.range s) :
        proj (c i • ιE ((⇑(Lsq W (-2)))^[i] a)) =
          c' i • ιE ((⇑(Lsq W (-2)))^[i] a) := by
      have his : i < s := Finset.mem_range.mp hi
      have hdegree :
          2 * ((s - i : ℕ) : ℤ) + (wt + 2 * (i : ℤ)) = n := by
        rw [Nat.cast_sub (Nat.le_of_lt his)]
        simp only [n]
        ring
      change ((DirectSum.decompose (akTotalWeightSpace W)
        (c i • ιE ((⇑(Lsq W (-2)))^[i] a)) n : akTotalWeightSpace W n) : 𝒱E 𝒱) = _
      rw [← hdegree]
      exact hgrade.decompose_smul_of_mem
        (p := 2 * ((s - i : ℕ) : ℤ)) (q := wt + 2 * (i : ℤ)) (c i)
        (ha.ιE_negTwo_iterate_mem_akTotalWeightSpace W i)
    have hprojEq : proj rel = ιE ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c' i • ιE ((⇑(Lsq W (-2)))^[i] a) := by
      simp only [rel, map_sub, map_sum, hlead]
      congr 1
      exact Finset.sum_congr rfl hterm
    have hrelRestrict : rel ∈ (blockRelSpanE W).restrictScalars ℂ := by
      rw [Submodule.restrictScalars_mem]
      exact hmem
    have hprojRestrict := hgrade.relationHomogeneous n hrelRestrict
    have hproj : proj rel ∈ blockRelSpanE W := by
      rw [← Submodule.restrictScalars_mem ℂ]
      exact hprojRestrict
    rw [hprojEq] at hproj
    exact hproj

/-- A homogeneous AK grading upgrades the Noetherian relation to one with the exact coefficient
weights required by the Serre elimination. -/
theorem AKWeightGrading.exists_uniform_weighted_monic_Lsq_relationE_of_fin_gen
    {W : VertexOperatorAlgebra 𝒱} (hgrade : AKWeightGrading W)
    {a : 𝒱} {wt : ℤ} (ha : IsSqPrimary W a (wt : ℂ))
    (T : Set (𝒱E 𝒱)) (hTfin : T.Finite)
    (htop : (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      = Submodule.span (↥E46) T ⊔ blockRelSpanE W) :
    ∃ (s : ℕ) (c : ℕ → E46), 1 ≤ s ∧
      (∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (c i)) ∧
      (ιE ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈
          blockRelSpanE W := by
  obtain ⟨s, c, hs, hmem⟩ :=
    exists_uniform_monic_Lsq_relationE_of_fin_gen W T hTfin htop a
  obtain ⟨c', hc', hmem'⟩ := hgrade.weighted_Lsq_relation_of_mem ha hmem
  exact ⟨s, c', hs, hc', hmem'⟩

/-- Etingof--Schedler finiteness supplies the finite generating set in the preceding theorem. -/
theorem AKWeightGrading.exists_uniform_weighted_monic_Lsq_relationE_of_etingofFinite
    {W : VertexOperatorAlgebra 𝒱} (hgrade : AKWeightGrading W)
    {a : 𝒱} {wt : ℤ} (ha : IsSqPrimary W a (wt : ℂ))
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    ∃ (s : ℕ) (c : ℕ → E46), 1 ≤ s ∧
      (∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (c i)) ∧
      (ιE ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈
          blockRelSpanE W := by
  obtain ⟨T, hTfin, htop⟩ := exists_finite_gen_sup_blockRelSpanE_of_etingofFinite W hzero hE
  exact hgrade.exists_uniform_weighted_monic_Lsq_relationE_of_fin_gen ha T hTfin htop

/-- The zeroth tower vector has the tautological empty Serre-expansion row. -/
theorem uniformSerreExpansionRow_zero (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (wt : ℤ) :
    UniformSerreExpansionRow W a wt 0 0 := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro j hj
    omega
  · intro F hF z hz
    simp [serreIterC]

/-- The first nontrivial row for an integral-weight square-primary vector: the positive-mode tail
vanishes, so the analytic `omega` identity is exactly the first Serre derivative. -/
theorem IsSqPrimary.uniformSerreExpansionRow_one
    (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) : UniformSerreExpansionRow W a wt 1 0 := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro j hj
    exact E46Weight.zero _
  · intro F hF z hz
    have homega := hF.omega_serre (ha.negTwo_iterate_mem_sqWeightSpace W 0) hz
    simp only [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, add_zero] at homega
    have htail :
        (∑ᶠ m : ℕ, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) a) z) = 0 :=
      finsum_eq_zero_of_forall_eq_zero (fun m => by
        rw [ha.2 (2 * (m + 2) - 2 : ℤ) (by omega), hF.zerov z]
        ring)
    rw [htail, add_zero] at homega
    simpa [Function.iterate_succ_apply', serreIterC] using homega

/-- The Ramanujan/Serre successor step for the unitriangular tower expansion. -/
theorem IsSqPrimary.uniformSerreExpansionRow_succ
    (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hclose : E46SerreClosed) {k : ℕ}
    {R : ℕ → ℕ → E46}
    (hR : ∀ t ≤ k, UniformSerreExpansionRow W a wt t (R t)) :
    UniformSerreExpansionRow W a wt (k + 1)
      (serreRowSuccCoeff W hclose wt k R (hR k (le_refl k)).2.1) := by
  classical
  refine ⟨fun j hj => serreRowSuccCoeff_eq_zero hclose hR hj,
    fun j hj => serreRowSuccCoeff_weight hclose hR hj, ?_⟩
  intro F hF z hz
  let V : ℕ → 𝒱 := fun t => ((⇑(Lsq W (-2)))^[t] a)
  let D : ℕ → ℂ → ℂ := fun t => serreIterC wt t (F a)
  have hbase : AnalyticAt ℂ (F a) z :=
    ((hF.holo a).analyticOnNhd (isOpen_imGT 0)) z hz
  have hevent : F (V k) =ᶠ[nhds z]
      D k + ∑ j ∈ Finset.range k, e46C (R k j) * D j := by
    filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
    simpa only [V, D, Pi.add_apply, Finset.sum_apply, Pi.mul_apply] using
      (hR k (le_refl k)).2.2 F hF w hw
  have hsumDiff : DifferentiableAt ℂ
      (∑ j ∈ Finset.range k, e46C (R k j) * D j) z := by
    apply DifferentiableAt.sum
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    exact ((hR k (le_refl k)).2.1 j hjk).differentiableAt_e46C hz |>.mul
      (analyticAt_serreIterC wt j hbase hz).differentiableAt
  have hderiv : serreDerivC (wt + 2 * (k : ℤ)) (F (V k)) z =
      D (k + 1) z + ∑ j ∈ Finset.range k,
        (e46C (serreRowDerivCoeff hclose k (R k) (hR k (le_refl k)).2.1 j) z * D j z
          + e46C (R k j) z * D (j + 1) z) := by
    calc
      serreDerivC (wt + 2 * (k : ℤ)) (F (V k)) z =
          serreDerivC (wt + 2 * (k : ℤ))
            (D k + ∑ j ∈ Finset.range k, e46C (R k j) * D j) z :=
        serreDerivC_congr_of_eventuallyEq _ hevent
      _ = serreDerivC (wt + 2 * (k : ℤ)) (D k) z +
          serreDerivC (wt + 2 * (k : ℤ))
            (∑ j ∈ Finset.range k, e46C (R k j) * D j) z :=
        serreDerivC_add _ _ _
          (analyticAt_serreIterC wt k hbase hz).differentiableAt hsumDiff
      _ = D (k + 1) z + ∑ j ∈ Finset.range k,
          (e46C (serreRowDerivCoeff hclose k (R k) (hR k (le_refl k)).2.1 j) z * D j z
            + e46C (R k j) z * D (j + 1) z) := by
        have hsum := serreDerivC_serreRow_sum (a := a) (wt := wt) hF hclose k (R k)
          (hR k (le_refl k)).2.1 hz
        simp only [D, serreIterC_succ] at hsum ⊢
        rw [hsum]
  have homega : F (V (k + 1)) z = serreDerivC (wt + 2 * (k : ℤ)) (F (V k)) z
      + ∑ᶠ m : ℕ, zhuGC (m + 2) z *
        F (Lsq W (2 * (m + 2) - 2 : ℤ) (V k)) z := by
    have h := hF.omega_serre (ha.negTwo_iterate_mem_sqWeightSpace W k) hz
    simpa only [V, Function.iterate_succ_apply'] using h
  have htower (m : ℕ) : Lsq W (2 * (m + 2) - 2 : ℤ) (V k) =
      towerScalar (wt : ℂ) W.centralCharge (m + 1) k • V (k - m - 1) := by
    rw [show (2 * ((m : ℤ) + 2) - 2 : ℤ) = 2 * ((m + 1 : ℕ) : ℤ) by
      push_cast; ring]
    simp only [V]
    convert Lsq_tower W ha k (m + 1) using 1
  have hzeroterm (m : ℕ) (hm : k ≤ m) :
      zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) (V k)) z = 0 := by
    rw [htower m, towerScalar_eq_zero_of_lt (wt : ℂ) W.centralCharge (by omega),
      zero_smul, hF.zerov]
    ring
  have hfinsum : (∑ᶠ m : ℕ, zhuGC (m + 2) z *
      F (Lsq W (2 * (m + 2) - 2 : ℤ) (V k)) z) =
      ∑ m ∈ Finset.range k, zhuGC (m + 2) z *
        F (Lsq W (2 * (m + 2) - 2 : ℤ) (V k)) z := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hmk
    exact hm (hzeroterm m (by omega))
  have htail : (∑ᶠ m : ℕ, zhuGC (m + 2) z *
      F (Lsq W (2 * (m + 2) - 2 : ℤ) (V k)) z) =
      ∑ m ∈ Finset.range k,
        towerScalar (wt : ℂ) W.centralCharge (m + 1) k * zhuGC (m + 2) z *
          (D (k - m - 1) z + ∑ j ∈ Finset.range (k - m - 1),
            e46C (R (k - m - 1) j) z * D j z) := by
    rw [hfinsum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmk : m < k := Finset.mem_range.mp hm
    rw [htower m, hF.smulv]
    have hrow := (hR (k - m - 1) (by omega)).2.2 F hF z hz
    simp only [V, D] at hrow ⊢
    rw [hrow]
    ring
  have hcoeff :
      ∑ j ∈ Finset.range (k + 1),
          e46C (serreRowSuccCoeff W hclose wt k R (hR k (le_refl k)).2.1 j) z * D j z =
        (∑ j ∈ Finset.range k,
          (e46C (serreRowDerivCoeff hclose k (R k) (hR k (le_refl k)).2.1 j) z * D j z
            + e46C (R k j) z * D (j + 1) z)) +
        ∑ m ∈ Finset.range k,
          towerScalar (wt : ℂ) W.centralCharge (m + 1) k * zhuGC (m + 2) z *
            (D (k - m - 1) z + ∑ j ∈ Finset.range (k - m - 1),
              e46C (R (k - m - 1) j) z * D j z) := by
    simp only [serreRowSuccCoeff, e46C_add, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
    rw [serreRowDerivCoeff_sum hclose k (R k) (hR k (le_refl k)).2.1
      (fun j => D j z) z]
    rw [serreRowShiftCoeff_sum k (R k) (fun j => D j z) z]
    rw [omegaTailRowCoeff_sum hR (fun j => D j z) hz]
  change F (V (k + 1)) z = D (k + 1) z +
    ∑ j ∈ Finset.range (k + 1),
      e46C (serreRowSuccCoeff W hclose wt k R (hR k (le_refl k)).2.1 j) z * D j z
  calc
    F (V (k + 1)) z = serreDerivC (wt + 2 * (k : ℤ)) (F (V k)) z +
        ∑ᶠ m : ℕ, zhuGC (m + 2) z *
          F (Lsq W (2 * (m + 2) - 2 : ℤ) (V k)) z := homega
    _ = (D (k + 1) z + ∑ j ∈ Finset.range k,
          (e46C (serreRowDerivCoeff hclose k (R k) (hR k (le_refl k)).2.1 j) z * D j z
            + e46C (R k j) z * D (j + 1) z)) +
        ∑ m ∈ Finset.range k,
          towerScalar (wt : ℂ) W.centralCharge (m + 1) k * zhuGC (m + 2) z *
            (D (k - m - 1) z + ∑ j ∈ Finset.range (k - m - 1),
              e46C (R (k - m - 1) j) z * D j z) := by rw [hderiv, htail]
    _ = D (k + 1) z +
        ∑ j ∈ Finset.range (k + 1),
          e46C (serreRowSuccCoeff W hclose wt k R (hR k (le_refl k)).2.1 j) z * D j z := by
      rw [hcoeff]
      ring

/-- Every row of the primary `L[-2]` tower has a block-independent weighted Serre expansion,
assuming the exact Ramanujan closure property of `E46`. -/
theorem IsSqPrimary.exists_uniformSerreExpansionRow
    (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hclose : E46SerreClosed) (i : ℕ) :
    ∃ r : ℕ → E46, UniformSerreExpansionRow W a wt i r := by
  classical
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      rcases i with _ | k
      · exact ⟨0, uniformSerreExpansionRow_zero W a wt⟩
      · have hrows : ∀ t ≤ k, ∃ r : ℕ → E46,
            UniformSerreExpansionRow W a wt t r := by
          intro t ht
          exact ih t (by omega)
        let R : ℕ → ℕ → E46 := fun t =>
          if ht : t ≤ k then Classical.choose (hrows t ht) else 0
        have hR : ∀ t ≤ k, UniformSerreExpansionRow W a wt t (R t) := by
          intro t ht
          simp only [R, dif_pos ht]
          exact Classical.choose_spec (hrows t ht)
        exact ⟨serreRowSuccCoeff W hclose wt k R (hR k (le_refl k)).2.1,
          ha.uniformSerreExpansionRow_succ W hclose hR⟩

/-- Compatible rowwise expansions assemble into the fixed-cutoff array consumed by the MLDE
elimination theorem. -/
theorem uniformSerreExpansionUpTo_of_rows
    (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (wt : ℤ) (s : ℕ)
    (h : ℕ → ℕ → E46)
    (hrow : ∀ i ≤ s, UniformSerreExpansionRow W a wt i (h i)) :
    UniformSerreExpansionUpTo W a wt s h := by
  classical
  refine ⟨fun i his j hij => (hrow i his).1 j hij,
    fun i his j hji => (hrow i his).2.1 j hji, ?_⟩
  intro F hF i his z hz
  have hi := (hrow i his).2.2 F hF z hz
  have hsum :
      (∑ j ∈ Finset.range s, e46C (h i j) z * serreIterC wt j (F a) z) =
        ∑ j ∈ Finset.range i, e46C (h i j) z * serreIterC wt j (F a) z := by
    symm
    apply Finset.sum_subset (Finset.range_mono his)
    intro j hjs hji
    simp only [Finset.mem_range, not_lt] at hjs hji
    rw [(hrow i his).1 j hji, e46C_zero]
    simp
  rw [hsum]
  exact hi

/-- Existential rowwise constructions can be chosen once and padded into a single uniform array. -/
theorem exists_uniformSerreExpansionUpTo_of_exists_rows
    (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (wt : ℤ) (s : ℕ)
    (hrows : ∀ i ≤ s, ∃ r : ℕ → E46, UniformSerreExpansionRow W a wt i r) :
    ∃ h : ℕ → ℕ → E46, UniformSerreExpansionUpTo W a wt s h := by
  classical
  let h : ℕ → ℕ → E46 := fun i =>
    if hi : i ≤ s then Classical.choose (hrows i hi) else 0
  refine ⟨h, uniformSerreExpansionUpTo_of_rows W a wt s h ?_⟩
  intro i hi
  simp only [h, dif_pos hi]
  exact Classical.choose_spec (hrows i hi)

/-- The complete block-independent Serre conversion through any fixed order.  The only
Ramanujan input is the explicitly named closure property `E46SerreClosed`. -/
theorem IsSqPrimary.exists_uniformSerreExpansionUpTo
    (W : VertexOperatorAlgebra 𝒱) {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hclose : E46SerreClosed) (s : ℕ) :
    ∃ h : ℕ → ℕ → E46, UniformSerreExpansionUpTo W a wt s h := by
  apply exists_uniformSerreExpansionUpTo_of_exists_rows W a wt s
  intro i hi
  exact ha.exists_uniformSerreExpansionRow W hclose i

/-- The coefficient obtained by eliminating a unitriangular `L[-2]` tower in favour of the Serre
tower. -/
noncomputable def mldeCoeff (s : ℕ) (c : ℕ → E46) (h : ℕ → ℕ → E46) (j : ℕ) : E46 :=
  h s j - c j - ∑ i ∈ Finset.range s, c i * h i j

/-- The elimination coefficient has the forced modular weight.  This is the exact coefficient
algebra calculation: products add weights, while the upper-triangular terms vanish. -/
theorem mldeCoeff_weight {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ}
    {s : ℕ} {c : ℕ → E46} {h : ℕ → ℕ → E46}
    (hc : ∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (c i))
    (hexp : UniformSerreExpansionUpTo W a wt s h) {j : ℕ} (hj : j < s) :
    E46Weight (2 * ((s - j : ℕ) : ℤ)) (mldeCoeff s c h j) := by
  have hsj := hexp.2.1 s (le_refl s) j hj
  have hcj := hc j hj
  have hsum : E46Weight (2 * ((s - j : ℕ) : ℤ))
      (∑ i ∈ Finset.range s, c i * h i j) := by
    apply E46Weight.sum
    intro i hi
    have his : i < s := Finset.mem_range.mp hi
    by_cases hji : j < i
    · have hprod := (hc i his).mul (hexp.2.1 i (Nat.le_of_lt his) j hji)
      (convert hprod using 1; omega)
    · have hz := hexp.1 i (Nat.le_of_lt his) j (by omega)
      rw [hz, mul_zero]
      exact E46Weight.zero _
  exact (hsj.sub hcj).sub hsum

/-- A common monic square-bracket relation, together with a block-independent unitriangular
Serre expansion and the forced weights on the relation coefficients, gives the same genuine
MLDE for every analytic block. -/
theorem IsAnalyticBlock.monicMLDEOn_of_Lsq_relation
    {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ} (hF : IsAnalyticBlock W F)
    {a : 𝒱} {wt : ℤ} {s : ℕ} {c : ℕ → E46} {h : ℕ → ℕ → E46}
    (hs : 1 ≤ s)
    (hc : ∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (c i))
    (hmem : (ιE ((⇑(Lsq W (-2)))^[s] a)
      - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanE W)
    (hexp : UniformSerreExpansionUpTo W a wt s h) :
    MonicMLDEOn wt (F a) s (mldeCoeff s c h) := by
  classical
  refine ⟨hs, fun i hi => mldeCoeff_weight hc hexp hi, ?_⟩
  intro z hz
  let D : ℕ → ℂ := fun i => serreIterC wt i (F a) z
  let C : ℕ → ℂ := fun i => e46C (c i) z
  let H : ℕ → ℕ → ℂ := fun i j => e46C (h i j) z
  have hsExp : F ((⇑(Lsq W (-2)))^[s] a) z =
      D s + ∑ j ∈ Finset.range s, H s j * D j := by
    simpa [D, H] using hexp.2.2 F hF s (le_refl s) z hz
  have hiExp : ∀ i ∈ Finset.range s,
      F ((⇑(Lsq W (-2)))^[i] a) z =
        D i + ∑ j ∈ Finset.range s, H i j * D j := by
    intro i hi
    simpa [D, H] using hexp.2.2 F hF i (Nat.le_of_lt (Finset.mem_range.mp hi)) z hz
  have hdouble :
      (∑ i ∈ Finset.range s, C i * ∑ j ∈ Finset.range s, H i j * D j) =
        ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, C i * H i j) * D j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hrel' :
      D s + ∑ j ∈ Finset.range s, H s j * D j =
        (∑ i ∈ Finset.range s, C i * D i) +
          ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, C i * H i j) * D j := by
    calc
      D s + ∑ j ∈ Finset.range s, H s j * D j =
          F ((⇑(Lsq W (-2)))^[s] a) z := hsExp.symm
      _ = ∑ i ∈ Finset.range s,
          e46C (c i) z * F ((⇑(Lsq W (-2)))^[i] a) z :=
        hF.Lsq_relation_of_mem hmem hz
      _ = ∑ i ∈ Finset.range s,
          C i * (D i + ∑ j ∈ Finset.range s, H i j * D j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hiExp i hi]
      _ = (∑ i ∈ Finset.range s, C i * D i) +
          ∑ i ∈ Finset.range s, C i * ∑ j ∈ Finset.range s, H i j * D j := by
        simp_rw [mul_add]
        exact Finset.sum_add_distrib
      _ = (∑ i ∈ Finset.range s, C i * D i) +
          ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, C i * H i j) * D j := by
        rw [hdouble]
  have hevalSum (j : ℕ) :
      e46C (∑ i ∈ Finset.range s, c i * h i j) z =
        ∑ i ∈ Finset.range s, C i * H i j := by
    induction Finset.range s using Finset.induction with
    | empty => simp [C, H]
    | @insert i t hi ih =>
        simp only [Finset.sum_insert hi, e46C_add, Pi.add_apply, ih]
        rw [e46C_mul]
        rfl
  change D s + ∑ j ∈ Finset.range s,
      e46C (mldeCoeff s c h j) z * D j = 0
  simp only [mldeCoeff, e46C_sub, Pi.sub_apply, hevalSum]
  calc
    D s + ∑ j ∈ Finset.range s,
        ((H s j - C j - ∑ i ∈ Finset.range s, C i * H i j) * D j) =
        (D s + ∑ j ∈ Finset.range s, H s j * D j) -
          ((∑ i ∈ Finset.range s, C i * D i) +
            ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, C i * H i j) * D j) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    _ = 0 := sub_eq_zero.mpr hrel'

/-- Quantifier-frozen form of `monicMLDEOn_of_Lsq_relation`: the relation, coefficient weights,
and Serre conversion are chosen once, before the analytic block. -/
theorem monicMLDEOn_all_analyticBlocks_of_Lsq_relation
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ} {s : ℕ}
    {c : ℕ → E46} {h : ℕ → ℕ → E46}
    (hs : 1 ≤ s)
    (hc : ∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (c i))
    (hmem : (ιE ((⇑(Lsq W (-2)))^[s] a)
      - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanE W)
    (hexp : UniformSerreExpansionUpTo W a wt s h) :
    ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F →
      MonicMLDEOn wt (F a) s (mldeCoeff s c h) := by
  intro F hF
  exact hF.monicMLDEOn_of_Lsq_relation hs hc hmem hexp

/-- Primary-insertion form with the Serre conversion discharged: after fixing a weighted monic
`L[-2]` relation, `E46SerreClosed` produces one genuine MLDE shared by every analytic block. -/
theorem IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_Lsq_relation
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hclose : E46SerreClosed)
    {s : ℕ} {c : ℕ → E46} (hs : 1 ≤ s)
    (hc : ∀ i < s, E46Weight (2 * ((s - i : ℕ) : ℤ)) (c i))
    (hmem : (ιE ((⇑(Lsq W (-2)))^[s] a)
      - ∑ i ∈ Finset.range s, c i • ιE ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanE W) :
    ∃ p : ℕ → E46, ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F →
      MonicMLDEOn wt (F a) s p := by
  obtain ⟨h, hexp⟩ := ha.exists_uniformSerreExpansionUpTo W hclose s
  exact ⟨mldeCoeff s c h,
    monicMLDEOn_all_analyticBlocks_of_Lsq_relation hs hc hmem hexp⟩

/-- With an AK weight grading, finite generation modulo the homogeneous relation module produces
one genuine MLDE shared by all analytic blocks of the fixed primary insertion. -/
theorem IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_fin_gen
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hgrade : AKWeightGrading W)
    (hclose : E46SerreClosed) (T : Set (𝒱E 𝒱)) (hTfin : T.Finite)
    (htop : (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      = Submodule.span (↥E46) T ⊔ blockRelSpanE W) :
    ∃ (s : ℕ) (p : ℕ → E46), 1 ≤ s ∧
      ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F → MonicMLDEOn wt (F a) s p := by
  obtain ⟨s, c, hs, hc, hmem⟩ :=
    hgrade.exists_uniform_weighted_monic_Lsq_relationE_of_fin_gen ha T hTfin htop
  obtain ⟨p, hp⟩ := ha.exists_monicMLDEOn_all_analyticBlocks_of_Lsq_relation
    hclose hs hc hmem
  exact ⟨s, p, hs, hp⟩

/-- Arakawa--Kawasetsu's fixed-insertion MLDE conclusion from Etingof finiteness, vacuum grade
zero, the exact graded interface `AKWeightGrading`, and the isolated Ramanujan closure of `E46`. -/
theorem IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hgrade : AKWeightGrading W)
    (hclose : E46SerreClosed) (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    ∃ (s : ℕ) (p : ℕ → E46), 1 ≤ s ∧
      ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F → MonicMLDEOn wt (F a) s p := by
  obtain ⟨s, c, hs, hc, hmem⟩ :=
    hgrade.exists_uniform_weighted_monic_Lsq_relationE_of_etingofFinite ha hzero hE
  obtain ⟨p, hp⟩ := ha.exists_monicMLDEOn_all_analyticBlocks_of_Lsq_relation
    hclose hs hc hmem
  exact ⟨s, p, hs, hp⟩

end VOA
