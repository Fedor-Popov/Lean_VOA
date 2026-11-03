/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRank
import VOA.Modularity.BlockDeterminacy
import VOA.Modularity.OnePointDescent

/-!
# Zhu's Theorem 5.3.2: the block space is FINITE-DIMENSIONAL

The `ω`-law expresses `d/dz F(v)` as a **finite combination of values of `F` itself**,

  `F(v)′ = 2πi·( F(L[−2]v) − Σ_{k ≥ 1} G_{2k}·F(L[2k−2]v) )`,

so if a block vanishes at a single point `z₀ ∈ ℍ` on *every* vector, then so do **all** its
derivatives there — hence, being holomorphic, it vanishes identically.  Combined with the
pointwise form of Zhu's determinacy descent (block condition (ii) at the single point `z₀`), this
gives: a block is determined by the `g + 1` **numbers** `F(genᵢ)(z₀)`, `F(𝟙)(z₀)`.

That is an injective linear map into a `(g+1)`-dimensional space, so

  `finiteDimensional_analyticBlocks` and `finrank_analyticBlocks_le` : `dim_ℂ 𝔅 ≤ g + 1`.

No modular linear differential equation, no Frobenius–Fuchs, no structure theorem for modular
forms — only the block conditions, the identity theorem, and the finite `C₂`-generating family.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Iterated derivatives of functions analytic at a point -/

section AnCalc

/-- `iteratedDeriv` is additive at a point of analyticity. -/
theorem iteratedDeriv_add_of_analyticAt {f g : ℂ → ℂ} {z₀ : ℂ} (k : ℕ) :
    AnalyticAt ℂ f z₀ → AnalyticAt ℂ g z₀ →
      iteratedDeriv k (fun z => f z + g z) z₀ = iteratedDeriv k f z₀ + iteratedDeriv k g z₀ := by
  induction k generalizing f g with
  | zero => intro _ _; simp [iteratedDeriv_zero]
  | succ k ih =>
      intro hf hg
      have hstep : _root_.deriv (fun z => f z + g z)
          =ᶠ[nhds z₀] fun z => _root_.deriv f z + _root_.deriv g z := by
        filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with w hfw hgw
        exact deriv_add hfw.differentiableAt hgw.differentiableAt
      rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
        Filter.EventuallyEq.iteratedDeriv_eq k hstep, ih hf.deriv hg.deriv]

/-- `iteratedDeriv` of a finite sum of functions analytic at `z₀`. -/
theorem iteratedDeriv_sum_of_analyticAt {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {z₀ : ℂ}
    (k : ℕ) (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) z₀) :
    iteratedDeriv k (fun z => ∑ i ∈ s, f i z) z₀ = ∑ i ∈ s, iteratedDeriv k (f i) z₀ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hfa : AnalyticAt ℂ (f a) z₀ := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, AnalyticAt ℂ (f i) z₀ := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      have hsum : AnalyticAt ℂ (fun z => ∑ i ∈ s, f i z) z₀ :=
        Finset.analyticAt_fun_sum s (fun i hi => hfs i hi)
      have hrw : (fun z => ∑ i ∈ insert a s, f i z)
          = fun z => f a z + ∑ i ∈ s, f i z := by
        funext z; rw [Finset.sum_insert ha]
      rw [hrw, iteratedDeriv_add_of_analyticAt k hfa hsum, ih hfs, Finset.sum_insert ha]

/-- A function analytic at `z₀` all of whose derivatives vanish there is locally zero. -/
theorem eventuallyEq_zero_of_iteratedDeriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (h : ∀ k : ℕ, iteratedDeriv k f z₀ = 0) :
    ∀ᶠ z in nhds z₀, f z = 0 := by
  have hps := hf.hasFPowerSeriesAt
  have hzero : (FormalMultilinearSeries.ofScalars ℂ
      fun n => iteratedDeriv n f z₀ / (n.factorial : ℂ)) = 0 := by
    ext n
    simp [FormalMultilinearSeries.ofScalars, h n]
  rw [hzero] at hps
  exact hps.eventually_eq_zero

end AnCalc

/-! ## The pointwise descent -/

section Pointwise

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

/-- The vectors on which a block vanishes at the single point `z₀` — a submodule. -/
def blockKerAt (hF : IsAnalyticBlock W F) (z₀ : ℂ) : Submodule ℂ 𝒱 where
  carrier := {x : 𝒱 | F x z₀ = 0}
  add_mem' := fun hx hy => by
    show F _ z₀ = 0
    rw [hF.addv, hx, hy, add_zero]
  zero_mem' := hF.zerov z₀
  smul_mem' := fun c _ hx => by
    show F _ z₀ = 0
    rw [hF.smulv, hx, mul_zero]

@[simp] theorem mem_blockKerAt (hF : IsAnalyticBlock W F) (z₀ : ℂ) (x : 𝒱) :
    x ∈ blockKerAt hF z₀ ↔ F x z₀ = 0 := Iff.rfl

/-- **The determinacy descent, at a single point.**  Zhu's block condition (ii) is an
identity of *numbers* at each `z`, so the descent of `Modularity.BlockFiniteness` runs verbatim
inside `{x | F x z₀ = 0}`. -/
theorem IsAnalyticBlock.eq_zero_at_of_vanish (hF : IsAnalyticBlock W F) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (hvan : ∀ x ∈ S, F x z₀ = 0) : ∀ x : 𝒱, F x z₀ = 0 := by
  classical
  set K : Submodule ℂ 𝒱 := blockKerAt hF z₀ with hK
  have hSK : Submodule.span ℂ S ≤ K := by
    rw [Submodule.span_le]
    intro x hx
    exact hvan x hx
  have hgrad : ∀ n : ℤ, W.grading n ≤ K := by
    intro n
    rcases lt_or_ge n 0 with hneg | hnn
    · rw [W.positivity n hneg]; exact bot_le
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
    induction N using Nat.strong_induction_on with
    | _ N ihN =>
      have hlow : ∀ m : ℤ, m < (N : ℤ) → W.grading m ≤ K := by
        intro m hm
        rcases lt_or_ge m 0 with hm0 | hm0
        · rw [W.positivity m hm0]; exact bot_le
        · obtain ⟨Mn, rfl⟩ : ∃ Mn : ℕ, m = (Mn : ℤ) := ⟨m.toNat, by omega⟩
          exact ihN Mn (by exact_mod_cast hm) (by exact_mod_cast hm0)
      refine le_trans (grading_le_span_sup_O₂_inf W S hShom htop (N : ℤ)) ?_
      refine sup_le hSK ?_
      refine le_trans (O₂_inf_grading_le_span_deg W (N : ℤ)) ?_
      rw [Submodule.span_le]
      rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
      by_cases hg0 : W.smul a (-2) b = 0
      · rw [hg0]; exact Submodule.zero_mem _
      have hp0 : 0 ≤ p := by
        by_contra hc; push_neg at hc
        exact hg0 (by rw [show a = 0 by
          rw [W.positivity p hc, Submodule.mem_bot] at ha; exact ha, W.smul_zero_left])
      have hq0 : 0 ≤ q := by
        by_contra hc; push_neg at hc
        exact hg0 (by rw [show b = 0 by
          rw [W.positivity q hc, Submodule.mem_bot] at hb; exact hb, W.smul_zero_right])
      rcases eq_or_lt_of_le hp0 with hp | hp1
      · exfalso
        apply hg0
        have hmem : a ∈ W.grading (0 : ℤ) := by rw [hp]; exact ha
        rw [W.vacuum_grade, Submodule.mem_span_singleton] at hmem
        obtain ⟨c, rfl⟩ := hmem
        rw [PreVertexAlgebra.smul_smul_left]
        have hvac : W.smul W.vacuum (-2) b = 0 := by
          show mode (W.Y W.vacuum) (-2) b = 0
          rw [W.vacuum_Y, mode_one, if_neg (by norm_num)]
          rfl
        rw [hvac, smul_zero]
      have hpcast : ((p.toNat : ℕ) : ℤ) = p := by omega
      have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by rwa [hpcast]
      have hka : 1 ≤ p.toNat := by omega
      have hpos : ∀ m : ℕ, vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b ∈ K := by
        intro m
        refine vSqZ_mem_of_lower W ha hb p.toNat _ K (fun d hd => hlow d ?_)
        have h2 : (0 : ℤ) ≤ 2 * ((m : ℤ) + 1) - 2 := by omega
        omega
      have hneg2 : vSqZ W a p.toNat (-2) b ∈ K := by
        have hlaw := hF.negTwo p.toNat hka a ha' b z₀ hz₀
        have hzero : ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z₀ * F (vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b) z₀) = 0 := by
          refine finsum_eq_zero_of_forall_eq_zero (fun m => ?_)
          rw [(mem_blockKerAt hF z₀ _).mp (hpos m), mul_zero, mul_zero]
        rw [hzero, add_zero] at hlaw
        exact hlaw
      have hdef : sqDefect W a p.toNat b ∈ K :=
        sqDefect_mem_of_lower W ha hb hpq hp0 K hlow
      have hstep : W.smul a (-2) b = vSqZ W a p.toNat (-2) b - sqDefect W a p.toNat b := by
        rw [vSqZ_neg_two_eq W a p.toNat b]
        show W.smul a (-2) b = mode (W.Y a) (-2) b + sqDefect W a p.toNat b
          - sqDefect W a p.toNat b
        rw [add_sub_cancel_right]
        rfl
      rw [hstep]
      exact Submodule.sub_mem _ hneg2 hdef
  intro x
  have hx : x ∈ Submodule.span ℂ {y : 𝒱 | IsHomog W y} := by
    rw [span_homog_eq_top]; trivial
  have hxK : x ∈ K := by
    refine (Submodule.span_le.mpr ?_) hx
    rintro y ⟨n, hy⟩
    exact hgrad n hy
  exact hxK

end Pointwise

/-! ## `zhuGC` is holomorphic -/

section ZhuGCHolo

open Classical in
/-- A formal `q`-series carrying a given `ℕ`-indexed coefficient sequence. -/
noncomputable def natSeries (a : ℕ → ℂ) : FormalQSeries :=
  fun e => if h : ∃ n : ℕ, (n : ℂ) = e then a h.choose else 0

theorem natSeries_natCast (a : ℕ → ℂ) (m : ℕ) : natSeries a (m : ℂ) = a m := by
  classical
  have h : ∃ n : ℕ, (n : ℂ) = (m : ℂ) := ⟨m, rfl⟩
  rw [natSeries, dif_pos h]
  congr 1
  have := h.choose_spec
  exact_mod_cast this

theorem qEvalC_natSeries (a : ℕ → ℂ) (z : ℂ) :
    qEvalC (natSeries a) 0 z
      = ∑' n : ℕ, a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) := by
  rw [qEvalC, qSeriesC, mul_zero, Complex.exp_zero, one_mul]
  refine tsum_congr (fun n => ?_)
  rw [qTerm, zero_add, natSeries_natCast]

/-- **The Zhu Eisenstein functions are holomorphic on the upper half-plane.** -/
theorem differentiableOn_zhuGC (j : ℕ) : DifferentiableOn ℂ (zhuGC j) (imGT 0) := by
  have hsub : Subexponential (fun n : ℕ => ‖natSeries (zhuG j) (0 + (n : ℂ))‖) := by
    refine Subexponential.of_le (fun n => ?_) (subexponential_zhuG j)
    rw [zero_add, natSeries_natCast]
  have h := differentiableOn_qEvalC (natSeries (zhuG j)) 0 hsub
  have hfun : qEvalC (natSeries (zhuG j)) 0 = zhuGC j := by
    funext z; rw [qEvalC_natSeries]; rfl
  rwa [hfun] at h

theorem analyticAt_zhuGC (j : ℕ) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0) : AnalyticAt ℂ (zhuGC j) z₀ :=
  ((differentiableOn_zhuGC j).analyticOnNhd (isOpen_imGT 0)) z₀ hz₀

end ZhuGCHolo

/-! ## The derivative of a block is a combination of its values -/

section DerivStep

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

theorem IsAnalyticBlock.analyticAt (hF : IsAnalyticBlock W F) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (x : 𝒱) : AnalyticAt ℂ (F x) z₀ :=
  ((hF.holo x).analyticOnNhd (isOpen_imGT 0)) z₀ hz₀

/-- **The `ω`-law solved for the derivative**: `F(v)′` is a finite combination of *values* of
`F`, with holomorphic Eisenstein coefficients. -/
theorem IsAnalyticBlock.deriv_eq_on (hF : IsAnalyticBlock W F) (v : 𝒱) {K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → Lsq W (2 * (m + 1) - 2 : ℤ) v = 0) {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (F v) z
      = 2 * (Real.pi : ℂ) * Complex.I * (F (Lsq W (-2) v) z
          - ∑ m ∈ Finset.range K, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z) := by
  have hlaw := hF.omega v z hz
  rw [omega_finsum_eq_sum hF.zerov hK z] at hlaw
  have hkey : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
      = F (Lsq W (-2) v) z
        - ∑ m ∈ Finset.range K, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z := by
    rw [hlaw]; ring
  calc _root_.deriv (F v) z
      = 2 * (Real.pi : ℂ) * Complex.I
          * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z) := by
        rw [← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
    _ = _ := by rw [hkey]

/-- **All derivatives vanish.**  If a block vanishes at `z₀` on *every* vector, then every
`iteratedDeriv` of every `g·F(v)` (with `g` analytic at `z₀`) vanishes at `z₀` — because
differentiating only ever produces new combinations of the same shape. -/
theorem iteratedDeriv_coeff_eq_zero (hF : IsAnalyticBlock W F) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hall : ∀ x : 𝒱, F x z₀ = 0) (k : ℕ) :
    ∀ (g : ℂ → ℂ), AnalyticAt ℂ g z₀ → ∀ v : 𝒱,
      iteratedDeriv k (fun z => g z * F v z) z₀ = 0 := by
  induction k with
  | zero =>
      intro g _ v
      rw [iteratedDeriv_zero]
      show g z₀ * F v z₀ = 0
      rw [hall v, mul_zero]
  | succ k ih =>
      intro g hg v
      obtain ⟨K, hK⟩ := Lsq_tail_eventually_zero W v
      set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
      set a₁ : ℂ → ℂ := fun z => _root_.deriv g z * F v z with ha₁
      set a₂ : ℂ → ℂ := fun z => (c * g z) * F (Lsq W (-2) v) z with ha₂
      set b : ℕ → ℂ → ℂ := fun m z =>
        (-c * g z * zhuGC (m + 1) z) * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z with hb
      set A : ℂ → ℂ := fun z => a₁ z + a₂ z with hA
      set B : ℂ → ℂ := fun z => ∑ m ∈ Finset.range K, b m z with hB
      have hEq : _root_.deriv (fun z => g z * F v z) =ᶠ[nhds z₀] fun z => A z + B z := by
        filter_upwards [hg.eventually_analyticAt, (isOpen_imGT 0).mem_nhds hz₀] with w hgw hw
        rw [deriv_fun_mul hgw.differentiableAt (hF.analyticAt hw v).differentiableAt,
          hF.deriv_eq_on v hK hw, hA, hB, ha₁, ha₂, hb]
        simp only
        rw [show g w * (c * (F (Lsq W (-2) v) w
              - ∑ m ∈ Finset.range K, zhuGC (m + 1) w * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) w))
            = (c * g w) * F (Lsq W (-2) v) w
              + (-c * g w) * ∑ m ∈ Finset.range K,
                  zhuGC (m + 1) w * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) w from by ring,
          Finset.mul_sum, ← add_assoc]
        congr 1
        exact Finset.sum_congr rfl (fun m _ => by ring)
      have ha₁an : AnalyticAt ℂ a₁ z₀ := hg.deriv.mul (hF.analyticAt hz₀ v)
      have ha₂an : AnalyticAt ℂ a₂ z₀ := (analyticAt_const.mul hg).mul (hF.analyticAt hz₀ _)
      have hban : ∀ m ∈ Finset.range K, AnalyticAt ℂ (b m) z₀ := fun m _ =>
        ((analyticAt_const.mul hg).mul (analyticAt_zhuGC (m + 1) hz₀)).mul (hF.analyticAt hz₀ _)
      have hAan : AnalyticAt ℂ A z₀ := ha₁an.add ha₂an
      have hBan : AnalyticAt ℂ B z₀ := Finset.analyticAt_fun_sum _ hban
      rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq k hEq,
        iteratedDeriv_add_of_analyticAt k hAan hBan,
        iteratedDeriv_add_of_analyticAt k ha₁an ha₂an,
        iteratedDeriv_sum_of_analyticAt (Finset.range K) b k hban,
        ih (_root_.deriv g) hg.deriv v,
        ih (fun z => c * g z) (analyticAt_const.mul hg) (Lsq W (-2) v)]
      have hz : ∀ m ∈ Finset.range K, iteratedDeriv k (b m) z₀ = 0 := fun m _ =>
        ih (fun z => -c * g z * zhuGC (m + 1) z)
          ((analyticAt_const.mul hg).mul (analyticAt_zhuGC (m + 1) hz₀)) _
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      ring

/-- **A block vanishing at one point of `ℍ` on every vector vanishes identically.** -/
theorem IsAnalyticBlock.eq_zero_of_eq_zero_at (hF : IsAnalyticBlock W F) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) (hall : ∀ x : 𝒱, F x z₀ = 0) :
    ∀ (v : 𝒱), ∀ z ∈ imGT 0, F v z = 0 := by
  intro v
  have hloc : ∀ᶠ z in nhds z₀, F v z = 0 := by
    refine eventuallyEq_zero_of_iteratedDeriv_eq_zero (hF.analyticAt hz₀ v) (fun k => ?_)
    have h := iteratedDeriv_coeff_eq_zero hF hz₀ hall k (fun _ => 1) analyticAt_const v
    simpa using h
  intro z hz
  have := eqOn_imGT_of_eventuallyEq (hF.holo v) (differentiableOn_const 0) hz₀
    (by filter_upwards [hloc] with w hw using hw) hz
  exact this

/-- **A block is determined by `g + 1` NUMBERS.**  Vanishing at a single `z₀ ∈ ℍ` on a
homogeneous family spanning `𝒱` modulo `C₂(𝒱)` forces the block to vanish identically. -/
theorem IsAnalyticBlock.eq_zero_of_vanish_at (hF : IsAnalyticBlock W F) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (hvan : ∀ x ∈ S, F x z₀ = 0) : ∀ (v : 𝒱), ∀ z ∈ imGT 0, F v z = 0 :=
  hF.eq_zero_of_eq_zero_at hz₀ (hF.eq_zero_at_of_vanish hz₀ S hShom htop hvan)

end DerivStep



/-! ## The evaluation map and finite-dimensionality -/

section FinDim

/-- **Evaluation of a family at finitely many vectors and one point** — manifestly linear. -/
noncomputable def ptEval {ι : Type*} (t : ι → 𝒱) (z₀ : ℂ) :
    (𝒱 → ℂ → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun F := fun j => F (t j) z₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ptEval_apply {ι : Type*} (t : ι → 𝒱) (z₀ : ℂ) (F : 𝒱 → ℂ → ℂ) (j : ι) :
    ptEval t z₀ F j = F (t j) z₀ := rfl

variable {W : VertexOperatorAlgebra 𝒱}

/-- **ZHU'S THEOREM 5.3.2 — the genus-one block space is FINITE-DIMENSIONAL**, of dimension at
most `g + 1`, where `g` is the number of homogeneous generators of `𝒱` modulo `C₂(𝒱)`.

The injection is the honest evaluation map `F ↦ (F(gen₁)(z₀), …, F(gen_g)(z₀), F(𝟙)(z₀))` into a
`(g+1)`-dimensional space: injective because block condition (ii) propagates vanishing at `z₀`
across all of `𝒱` (`eq_zero_at_of_vanish`), and the `ω`-law then propagates it to every derivative
(`eq_zero_of_eq_zero_at`), whence the identity theorem. -/
theorem exists_finrank_analyticBlocks_le (hC2 : C2Cofinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0) :
    ∃ g : ℕ, FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) ∧
      Module.finrank ℂ (Submodule.map restrictImGT (analyticBlocks W)) ≤ g + 1 := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨g, ?_, ?_⟩ <;>
  · set t : Fin g ⊕ Unit → 𝒱 := Sum.elim gen (fun _ => W.vacuum) with ht
    set 𝔅 : Submodule ℂ (𝒱 → ℂ → ℂ) := Submodule.map restrictImGT (analyticBlocks W) with h𝔅
    have hShom : ∀ s ∈ (Set.range gen ∪ {W.vacuum} : Set 𝒱), IsHomog W s := by
      rintro s (⟨i, rfl⟩ | hs)
      · exact ⟨(wt i : ℤ), hgen i⟩
      · rw [Set.mem_singleton_iff] at hs
        exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
    have hinj : Function.Injective ((ptEval t z₀).domRestrict 𝔅) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨f, hf⟩ hker
      have hker' : (ptEval t z₀).domRestrict 𝔅 ⟨f, hf⟩ = 0 := hker
      obtain ⟨F, hFmem, hFeq⟩ := hf
      have hzero : ∀ j : Fin g ⊕ Unit, F (t j) z₀ = 0 := by
        intro j
        have := congrFun hker' j
        simp only [LinearMap.domRestrict_apply, ptEval_apply, Pi.zero_apply] at this
        rw [← hFeq, restrictImGT_apply _ hz₀] at this
        exact this
      have hvan : ∀ x ∈ (Set.range gen ∪ {W.vacuum} : Set 𝒱), F x z₀ = 0 := by
        rintro s (⟨i, rfl⟩ | hs)
        · exact hzero (Sum.inl i)
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          exact hzero (Sum.inr ())
      have hall := (hFmem : IsAnalyticBlock W F).eq_zero_of_vanish_at hz₀ _ hShom hdec hvan
      refine Subtype.ext ?_
      show f = 0
      rw [← hFeq]
      funext v z
      by_cases hz : z ∈ imGT 0
      · rw [restrictImGT_apply _ hz, hall v z hz]; rfl
      · show Set.indicator (imGT 0) (F v) z = _
        rw [Set.indicator_of_notMem hz]; rfl
    first
      | exact FiniteDimensional.of_injective ((ptEval t z₀).domRestrict 𝔅) hinj
      | · haveI : FiniteDimensional ℂ 𝔅 :=
            FiniteDimensional.of_injective ((ptEval t z₀).domRestrict 𝔅) hinj
          have hle := LinearMap.finrank_le_finrank_of_injective (f := (ptEval t z₀).domRestrict 𝔅)
            hinj
          have hcard : Module.finrank ℂ (Fin g ⊕ Unit → ℂ) = g + 1 := by
            rw [Module.finrank_pi]
            simp
          rw [hcard] at hle
          exact hle

end FinDim

/-! ## Sharpening: the determining space is a *deformed Zhu algebra* quotient

The bound `g + 1` counts the `C₂`-generators.  It can be sharpened: at the point `z₀` the block
conditions say that the linear functional `φ(x) = F(x)(z₀)` kills

* every `a[0]v`   (condition (i)), and
* every `a[−2]v + Σ_{k ≥ 2}(2k−1)G_{2k}(z₀)·a[2k−2]v`   (condition (ii) in `G₂`-free form),

so `φ` factors through `𝒱 ⧸ blockRelSpan`.  Modulo the `q → 0` degeneration that replaces
`G_{2k}(z₀)` by its constant term, this quotient is Zhu's `A(𝒱)/[A(𝒱),A(𝒱)]`, whose dimension is
`#Irr A(𝒱) = #Φ(𝒱)` for a *rational* `𝒱`.  That is exactly where Zhu Thm 5.3.3 lives. -/

section Deformed

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

theorem IsAnalyticBlock.map_finsetSum (hF : IsAnalyticBlock W F) {κ : Type*} (s : Finset κ)
    (f : κ → 𝒱) (z : ℂ) : F (∑ i ∈ s, f i) z = ∑ i ∈ s, F (f i) z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hF.zerov z
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, hF.addv, ih, Finset.sum_insert ha]

variable (W)

/-- The relations satisfied at `z₀` by every genus-one block. -/
def blockRelSpan (z₀ : ℂ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ
    ({x : 𝒱 | ∃ (ka : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧ x = vSqZ W a ka 0 v} ∪
     {x : 𝒱 | ∃ (ka K : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧
        (∀ m : ℕ, K ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = vSqZ W a ka (-2) v + ∑ m ∈ Finset.range K,
              (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z₀)
                • vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v})

variable {W}

/-- **Every block kills the relation space at `z₀`.** -/
theorem IsAnalyticBlock.blockRelSpan_le_kerAt (hF : IsAnalyticBlock W F) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) : blockRelSpan W z₀ ≤ blockKerAt hF z₀ := by
  rw [blockRelSpan, Submodule.span_le]
  rintro x (⟨ka, a, v, hka, ha, rfl⟩ | ⟨ka, K, a, v, hka, ha, hK, rfl⟩)
  · exact hF.vanish_apply ka hka ha v z₀
  · show F _ z₀ = 0
    rw [hF.addv, hF.map_finsetSum]
    have hterm : ∀ m ∈ Finset.range K,
        F ((((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z₀)
            • vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z₀
          = ((2 * (m + 2) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 2) z₀ * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z₀) := by
      intro m _
      rw [hF.smulv]
      ring
    rw [Finset.sum_congr rfl hterm]
    have hlaw := hF.negTwo_tail ka hka ha v hz₀
    rwa [negTwoTail_finsum_eq_sum (fun z _ => hF.zerov z) hK hz₀] at hlaw

/-- **The sharpened bound**: `dim 𝔅 ≤ #T` for *any* finite `T` spanning `𝒱` modulo the
relation space — in particular `dim 𝔅 ≤ dim(𝒱 ⧸ blockRelSpan)`, the deformed Zhu-algebra
quotient.  The same evaluation map `ptEval` as before. -/
theorem finrank_analyticBlocks_le_card_of_blockRel {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0) (T : Finset 𝒱)
    (hT : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ blockRelSpan W z₀) :
    FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) ∧
      Module.finrank ℂ (Submodule.map restrictImGT (analyticBlocks W)) ≤ T.card := by
  classical
  set 𝔅 : Submodule ℂ (𝒱 → ℂ → ℂ) := Submodule.map restrictImGT (analyticBlocks W) with h𝔅
  have hinj : Function.Injective ((ptEval (fun x : {y : 𝒱 // y ∈ T} => (x : 𝒱)) z₀).domRestrict 𝔅) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨f, hf⟩ hker
    have hker' : (ptEval (fun x : {y : 𝒱 // y ∈ T} => (x : 𝒱)) z₀).domRestrict 𝔅 ⟨f, hf⟩ = 0 := hker
    obtain ⟨F, hFmem, hFeq⟩ := hf
    have hFb : IsAnalyticBlock W F := hFmem
    have hTker : ∀ x ∈ T, F x z₀ = 0 := by
      intro x hx
      have := congrFun hker' ⟨x, hx⟩
      simp only [LinearMap.domRestrict_apply, ptEval_apply, Pi.zero_apply] at this
      rw [← hFeq, restrictImGT_apply _ hz₀] at this
      exact this
    have hall : ∀ x : 𝒱, F x z₀ = 0 := by
      intro x
      have hsub : (⊤ : Submodule ℂ 𝒱) ≤ blockKerAt hFb z₀ := by
        rw [hT]
        refine sup_le ?_ (hFb.blockRelSpan_le_kerAt hz₀)
        rw [Submodule.span_le]
        intro y hy
        exact hTker y hy
      exact hsub (Submodule.mem_top) 
    have hzz := hFb.eq_zero_of_eq_zero_at hz₀ hall
    refine Subtype.ext ?_
    show f = 0
    rw [← hFeq]
    funext v z
    by_cases hz : z ∈ imGT 0
    · rw [restrictImGT_apply _ hz, hzz v z hz]; rfl
    · show Set.indicator (imGT 0) (F v) z = _
      rw [Set.indicator_of_notMem hz]; rfl
  haveI : FiniteDimensional ℂ 𝔅 :=
    FiniteDimensional.of_injective ((ptEval (fun x : {y : 𝒱 // y ∈ T} => (x : 𝒱)) z₀).domRestrict 𝔅)
      hinj
  refine ⟨inferInstance, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (ptEval (fun x : {y : 𝒱 // y ∈ T} => (x : 𝒱)) z₀).domRestrict 𝔅) hinj
  have hcard : Module.finrank ℂ ({y : 𝒱 // y ∈ T} → ℂ) = T.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  rw [hcard] at hle
  exact hle

end Deformed

/-! ## Feeding Zhu's theorem: discharging `hfd` -/

section Assemble

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}
variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- The ambient space of `Modularity.BlockRank.slashSpannedAtS_of_rank_le'`, built from the
**analytic** blocks — the space Zhu's Theorem 5.3.2 (`exists_finrank_analyticBlocks_le`) bounds. -/
noncomputable def analyticSlashAmbient : Submodule ℂ (𝒱 → ℂ → ℂ) :=
  Submodule.map restrictImGT (analyticBlocks W)
    ⊔ Submodule.span ℂ
        (Set.range fun i : ι => restrictImGT (blockSlash W ModularGroup.S (traceBlock Mfam h i)))

theorem traceBlock_mem_analyticSlashAmbient
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) (i : ι) :
    traceBlock Mfam h i ∈ analyticSlashAmbient Mfam h :=
  Submodule.mem_sup_left ⟨traceBlock Mfam h i,
    torusOnePoint_isAnalyticBlock (Mfam i).isMod _
      (onePointSupported_of_hasConformalWeight (Mfam i).isMod (hcw i)) (hgr i),
    restrictImGT_traceBlock Mfam h i⟩

theorem slash_mem_analyticSlashAmbient (i : ι) :
    restrictImGT (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ analyticSlashAmbient Mfam h :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

/-- **The ambient space is FINITE-DIMENSIONAL** — unconditionally, from Zhu's Theorem 5.3.2
proved above.  So `hfd` is not a hypothesis of Zhu's modularity theorem. -/
theorem finiteDimensional_analyticSlashAmbient (hC2 : C2Cofinite W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) : FiniteDimensional ℂ (analyticSlashAmbient Mfam h) := by
  obtain ⟨g, hfd, _⟩ := exists_finrank_analyticBlocks_le (W := W) hC2 hz₀
  haveI := hfd
  haveI : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun i : ι => restrictImGT (blockSlash W ModularGroup.S (traceBlock Mfam h i)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_sup _ _

/-- ⚠⚠ **VACUOUS — DO NOT USE.**  `Modularity.SlashAmbientObstruction.not_finrank_analyticSlash`
`Ambient_le` proves that this theorem's hypothesis `hle` is **contradictory**: every element of
`restrictImGT '' 𝔅` is additive in the vector slot (`IsAnalyticBlock.addv` is unrestricted), while
`blockSlash W γ F` weights each vector by *its own* `L[0]`-weight and `sqWtOf` returns `0` on an
inhomogeneous vector, so the `S`-slashes of the trace blocks can never lie in the span of the
`#ι` independent trace blocks.

The repaired statements — same shape, satisfiable hypothesis, on the `L[0]`-homogeneous
restriction `SqPt W` — are `zhu_modularity_of_sqAnalyticRank_le` (with Zhu Thm 5.3.2 still
supplying finite-dimensionality, `finiteDimensional_sqAnalyticSlashAmbient`) and
`zhu_modularity_of_sqGradedRank_le`.

The declaration is kept because it is *true* (its hypothesis is simply unsatisfiable) and because
`SlashAmbientObstruction` refers to it. -/
theorem zhu_modularity_of_analytic_finrank_le (hC2 : C2Cofinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W h))
    (hle : Module.finrank ℂ (analyticSlashAmbient Mfam h) ≤ Fintype.card ι) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_rank_le' Mfam h (analyticSlashAmbient Mfam h)
            (traceIndependent_of_tEigen_injective Mfam h hcw hinj
              (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr))
            (traceBlock_mem_analyticSlashAmbient Mfam h hcw hgr)
            (slash_mem_analyticSlashAmbient Mfam h)
            (by
              haveI := finiteDimensional_analyticSlashAmbient Mfam h hC2 hz₀
              rw [← Module.finrank_eq_rank]
              exact_mod_cast hle)))
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj
          (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr)) hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

/-- **The `≥` side of Zhu's dimension count**: the block space has dimension at least
`#Φ(𝒱)`, because the trace functions are independent. -/
theorem card_le_finrank_analyticSlashAmbient (hC2 : C2Cofinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h) :
    Fintype.card ι ≤ Module.finrank ℂ (analyticSlashAmbient Mfam h) := by
  haveI := finiteDimensional_analyticSlashAmbient Mfam h hC2 hz₀
  have hsub : Submodule.span ℂ (Set.range (traceBlock Mfam h)) ≤ analyticSlashAmbient Mfam h := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact traceBlock_mem_analyticSlashAmbient Mfam h hcw hgr i
  have hrk : Module.finrank ℂ (Submodule.span ℂ (Set.range (traceBlock Mfam h)))
      = Fintype.card ι := finrank_span_eq_card (linearIndependent_traceBlock Mfam h hind)
  rw [← hrk]
  exact Submodule.finrank_mono hsub

end Assemble

end VOA
