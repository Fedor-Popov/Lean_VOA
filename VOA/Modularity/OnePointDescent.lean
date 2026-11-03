/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OnePointGrowth
import VOA.Modularity.BlockFiniteness

/-!
# The growth datum descends the `C₂`-filtration

`Modularity.AnalyticBlock` consumes `OnePointSubexp N h` — subexponential growth of the coefficients
of `𝒵_M(v;q)` for **every** `v` — while the repo's `C₂`-cofiniteness ⟹ growth theorem
(`subexponentialCoeffs_adjoint_of_C2Cofinite`) covers only `v = 𝟙`.

This file closes almost all of that gap, and does so **formally** — no analysis, no differential
equation.  The observation is that Zhu's `[−2]`-identity expresses `𝒵_M(a[−2]v)` as a finite sum of
**convolutions** `G_{2k} ⋆ 𝒵_M(a[2k−2]v)` against vectors of strictly lower degree, and

  `subexponential_qConv` — **convolution against a subexponential sequence preserves
  subexponential growth.**

(If `‖f m‖ ≤ D sᵐ` and `‖χ(h+n)‖ ≤ C rⁿ` with `1 < s < r`, then
`‖(f ⋆ χ)(h+n)‖ ≤ CD rⁿ Σ_{m} (s/r)ᵐ ≤ CD(1−s/r)⁻¹ rⁿ`.)

So the *same* strong induction on the degree that runs in `Modularity.BlockFiniteness` runs here,
inside the submodule `{x | 𝒵_M(x) has subexponential coefficients}`, giving

  `onePointSubexp_of_generators` — the growth datum for **all** `v` from the growth datum on a
  homogeneous family spanning `𝒱` modulo `C₂(𝒱)`,
  `onePointSubexp_of_C2Cofinite` — for a `C₂`-cofinite VOA: from `g + 1` sequences.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Polynomials are subexponential -/

/-- `nᵖ` is subexponential: a convergent series bounds each of its (nonnegative) terms. -/
theorem subexponential_pow (p : ℕ) : Subexponential (fun n : ℕ => (n : ℝ) ^ p) := by
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hinv : ‖(r⁻¹ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    rw [inv_lt_one_iff₀]
    exact Or.inr hr
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ p * (r⁻¹) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one p hinv
  refine ⟨∑' n : ℕ, (n : ℝ) ^ p * (r⁻¹) ^ n, fun n => ?_⟩
  have hterm : (n : ℝ) ^ p * (r⁻¹) ^ n ≤ ∑' k : ℕ, (k : ℝ) ^ p * (r⁻¹) ^ k :=
    hsum.le_tsum n (fun k _ => by positivity)
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr0 n
  have hcan : ((r⁻¹ : ℝ)) ^ n * r ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hr0), one_pow]
  calc (n : ℝ) ^ p = ((n : ℝ) ^ p * (r⁻¹) ^ n) * r ^ n := by
        rw [mul_assoc, hcan, mul_one]
    _ ≤ (∑' k : ℕ, (k : ℝ) ^ p * (r⁻¹) ^ k) * r ^ n :=
        mul_le_mul_of_nonneg_right hterm hrn.le

/-- The Zhu Eisenstein coefficients grow subexponentially (they are `O(n^{2j})`). -/
theorem subexponential_zhuG (j : ℕ) : Subexponential (fun m : ℕ => ‖zhuG j m‖) := by
  refine Subexponential.of_le (fun m => norm_zhuG_le j m) ?_
  exact (subexponential_const _).add
    ((subexponential_pow (2 * j - 1 + 1)).const_mul (norm_nonneg _))

/-! ## Convolution preserves subexponential growth -/

/-- **Convolution preserves subexponential growth.**  With `1 < s < r` chosen between the two
ratios, `Σ_{m ≤ n} D sᵐ · C r^{n−m} = CD rⁿ Σ_m (s/r)ᵐ ≤ CD(1 − s/r)⁻¹ rⁿ`. -/
theorem subexponential_qConv {f : ℕ → ℂ} {χ : FormalQSeries} {h : ℂ}
    (hf : Subexponential (fun m : ℕ => ‖f m‖))
    (hsupp : ∀ i : ℤ, i < 0 → χ (h + (i : ℂ)) = 0)
    (hχ : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) :
    Subexponential (fun n : ℕ => ‖qConv f χ (h + (n : ℂ))‖) := by
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  obtain ⟨s, hs1, hsr⟩ : ∃ s : ℝ, 1 < s ∧ s < r := ⟨(1 + r) / 2, by linarith, by linarith⟩
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  obtain ⟨D, hD⟩ := hf s hs1
  obtain ⟨C, hC⟩ := hχ r hr
  have hD0 : 0 ≤ D := by
    have h0 := hD 0
    simp only [pow_zero, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    simp only [pow_zero, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  set x : ℝ := s / r with hx
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hr0]; exact hsr
  refine ⟨C * D * (1 - x)⁻¹, fun n => ?_⟩
  have hgeo : ∑ m ∈ Finset.range (n + 1), x ^ m ≤ (1 - x)⁻¹ := by
    have hsum : Summable (fun m : ℕ => x ^ m) := summable_geometric_of_lt_one hx0 hx1
    have hle := Summable.sum_le_tsum (Finset.range (n + 1)) (fun m _ => pow_nonneg hx0 m) hsum
    rwa [tsum_geometric_of_lt_one hx0 hx1] at hle
  show ‖qConv f χ (h + (n : ℂ))‖ ≤ C * D * (1 - x)⁻¹ * r ^ n
  rw [qConv_apply_of_support f χ h hsupp n]
  calc ‖∑ m ∈ Finset.range (n + 1), f m * χ (h + ((n - m : ℕ) : ℂ))‖
      ≤ ∑ m ∈ Finset.range (n + 1), ‖f m * χ (h + ((n - m : ℕ) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (n + 1), (D * s ^ m) * (C * r ^ (n - m)) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (hD m) (hC (n - m)) (norm_nonneg _) (by positivity)
    _ = C * D * r ^ n * ∑ m ∈ Finset.range (n + 1), x ^ m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [Finset.mem_range] at hm
        have hle : m ≤ n := by omega
        rw [pow_sub₀ r (ne_of_gt hr0) hle, hx, div_pow, div_eq_mul_inv]
        ring
    _ ≤ C * D * r ^ n * (1 - x)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hgeo ?_
        positivity
    _ = C * D * (1 - x)⁻¹ * r ^ n := by ring

/-! ## The submodule of subexponential `q`-series -/

/-- The formal `q`-series with subexponential coefficients along `h + ℕ` — a `ℂ`-subspace. -/
def SubexpSeries (h : ℂ) : Submodule ℂ FormalQSeries where
  carrier := {χ : FormalQSeries | Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)}
  add_mem' := fun {χ ψ} hχ hψ => by
    refine Subexponential.of_le (fun n => ?_) (hχ.add hψ)
    exact norm_add_le _ _
  zero_mem' := by
    refine Subexponential.of_le (fun n => ?_) subexponential_zero
    simp
  smul_mem' := fun c {χ} hχ => by
    refine Subexponential.of_le (fun n => ?_) (hχ.const_mul (norm_nonneg c))
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact le_refl _

@[simp] theorem mem_subexpSeries (h : ℂ) (χ : FormalQSeries) :
    χ ∈ SubexpSeries h ↔ Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖) := Iff.rfl

/-! ## The descent -/

section Descent

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The growth datum descends the `C₂`-filtration.**  If `𝒵_M(s;q)` has subexponential
coefficients for every `s` in a homogeneous family spanning `𝒱` modulo `C₂(𝒱)`, then it does for
**every** `v`.

The engine is Zhu's `[−2]`-identity together with `subexponential_qConv`: the identity writes
`𝒵_M(a[−2]v)` as a finite sum of convolutions of the (subexponential) Eisenstein coefficients
against `𝒵_M` on vectors of strictly lower degree. -/
theorem onePointSubexp_of_generators (N : OrdVModule W M) (h : ℂ) (hsupp : OnePointSupported N h)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (hgen : ∀ s ∈ S, Subexponential (fun n : ℕ => ‖torusOnePoint N s (h + (n : ℂ))‖)) :
    OnePointSubexp N h := by
  classical
  set K : Submodule ℂ 𝒱 := Submodule.comap (torusOnePointHom N) (SubexpSeries h) with hK
  have hmemK : ∀ x : 𝒱, x ∈ K ↔ Subexponential (fun n : ℕ => ‖torusOnePoint N x (h + (n : ℂ))‖) :=
    fun x => Iff.rfl
  have hSK : Submodule.span ℂ S ≤ K := by
    rw [Submodule.span_le]
    intro x hx
    exact (hmemK x).mpr (hgen x hx)
  have hgrad : ∀ n : ℤ, W.grading n ≤ K := by
    intro n
    rcases lt_or_ge n 0 with hneg | hnn
    · rw [W.positivity n hneg]; exact bot_le
    obtain ⟨Nn, rfl⟩ : ∃ Nn : ℕ, n = (Nn : ℤ) := ⟨n.toNat, by omega⟩
    induction Nn using Nat.strong_induction_on with
    | _ Nn ihN =>
      have hlow : ∀ m : ℤ, m < (Nn : ℤ) → W.grading m ≤ K := by
        intro m hm
        rcases lt_or_ge m 0 with hm0 | hm0
        · rw [W.positivity m hm0]; exact bot_le
        · obtain ⟨Mn, rfl⟩ : ∃ Mn : ℕ, m = (Mn : ℤ) := ⟨m.toNat, by omega⟩
          exact ihN Mn (by exact_mod_cast hm) (by exact_mod_cast hm0)
      refine le_trans (grading_le_span_sup_O₂_inf W S hShom htop (Nn : ℤ)) ?_
      refine sup_le hSK ?_
      refine le_trans (O₂_inf_grading_le_span_deg W (Nn : ℤ)) ?_
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
      -- (α) the tail vectors have strictly lower degree
      have hpos : ∀ m : ℕ, vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b ∈ K := by
        intro m
        refine vSqZ_mem_of_lower W ha hb p.toNat _ K (fun d hd => hlow d ?_)
        have h2 : (0 : ℤ) ≤ 2 * ((m : ℤ) + 1) - 2 := by omega
        omega
      -- (β) hence the head, by Zhu's `[−2]`-identity plus `subexponential_qConv`
      have hneg2 : vSqZ W a p.toNat (-2) b ∈ K := by
        obtain ⟨K₀, hK₀⟩ := vSqZ_eventually_zero W a p.toNat b
        have hlaw := zhuRecursion_neg_two N hka ha' b
        set T : ℕ → FormalQSeries := fun m => ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1)) (torusOnePoint N (vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b))
          with hT
        have hTfin : (Function.support T).Finite := by
          refine Set.Finite.subset (Set.finite_Iio K₀.toNat) (fun m hm => ?_)
          simp only [Function.mem_support, ne_eq] at hm
          simp only [Set.mem_Iio]
          by_contra hc
          push_neg at hc
          exact hm (by
            rw [hT]
            simp only
            rw [hK₀ (2 * ((m : ℤ) + 1) - 2) (by omega), torusOnePoint_zero, qConv_zero_right,
              smul_zero])
        have hTmem : ∀ m : ℕ, T m ∈ SubexpSeries h := by
          intro m
          refine Submodule.smul_mem _ _ ?_
          refine subexponential_qConv (subexponential_zhuG (m + 1)) ?_ ((hmemK _).mp (hpos m))
          exact fun i hi => hsupp _ i hi
        have hsub : Function.support T ⊆ (hTfin.toFinset : Set ℕ) := by
          intro m hm; simpa using hm
        have hval : torusOnePoint N (vSqZ W a p.toNat (-2) b) = -∑ m ∈ hTfin.toFinset, T m := by
          rw [← finsum_eq_finsetSum_of_support_subset _ hsub]
          rw [hT] at hlaw ⊢
          linear_combination (norm := module) hlaw
        rw [hmemK, ← mem_subexpSeries, show torusOnePoint N (vSqZ W a p.toNat (-2) b)
          = torusOnePointHom N (vSqZ W a p.toNat (-2) b) from rfl]
        show torusOnePointHom N (vSqZ W a p.toNat (-2) b) ∈ SubexpSeries h
        rw [show torusOnePointHom N (vSqZ W a p.toNat (-2) b)
          = torusOnePoint N (vSqZ W a p.toNat (-2) b) from rfl, hval]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun m _ => hTmem m))
      -- (γ) the defect is lower-degree
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
  intro v
  have hv : v ∈ Submodule.span ℂ {y : 𝒱 | IsHomog W y} := by
    rw [span_homog_eq_top]; trivial
  have hvK : v ∈ K := by
    refine (Submodule.span_le.mpr ?_) hv
    rintro y ⟨n, hy⟩
    exact hgrad n hy
  exact (hmemK v).mp hvK

/-- **For a `C₂`-cofinite VOA the growth datum is `g + 1` sequences.** -/
theorem onePointSubexp_of_C2Cofinite (hC2 : C2Cofinite W) (N : OrdVModule W M) (h : ℂ)
    (hsupp : OnePointSupported N h) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      ((∀ i, Subexponential (fun n : ℕ => ‖torusOnePoint N (gen i) (h + (n : ℂ))‖)) →
        Subexponential (fun n : ℕ => ‖torusOnePoint N W.vacuum (h + (n : ℂ))‖) →
        OnePointSubexp N h) := by
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨g, gen, wt, hwt, hgen, fun hg hvac => ?_⟩
  refine onePointSubexp_of_generators N h hsupp (Set.range gen ∪ {W.vacuum}) ?_ hdec ?_
  · rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  · rintro s (⟨i, rfl⟩ | hs)
    · exact hg i
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hvac

/-- **For the adjoint module the `𝟙`-sequence is unconditional.**  `𝒵_𝒱(𝟙;q)` is the character
of `𝒱`, whose subexponential growth is already proved from `C₂`-cofiniteness
(`subexponentialCoeffs_adjoint_of_C2Cofinite`, via Buhl's ordered spanning set).  So for `𝒱` itself
the residual growth datum is exactly the `g` **generator** sequences. -/
theorem onePointSubexp_adjoint_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱) (hne : W.vacuum ≠ 0)
    (hC2 : C2Cofinite W)
    (hsupp : OnePointSupported (adjointModule W) (0 - W.centralCharge / 24)) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      ((∀ i, Subexponential (fun n : ℕ =>
          ‖torusOnePoint (adjointModule W) (gen i) (0 - W.centralCharge / 24 + (n : ℂ))‖)) →
        OnePointSubexp (adjointModule W) (0 - W.centralCharge / 24)) := by
  obtain ⟨g, gen, wt, hwt, hgen, hall⟩ :=
    onePointSubexp_of_C2Cofinite hC2 (adjointModule W) (0 - W.centralCharge / 24) hsupp
  refine ⟨g, gen, wt, hwt, hgen, fun hg => hall hg ?_⟩
  have hvac := subexponentialCoeffs_adjoint_of_C2Cofinite W hne hC2
  rw [SubexponentialCoeffs] at hvac
  have hrw : torusOnePoint (adjointModule W) W.vacuum = gradedDim (adjointModule W) := by
    rw [torusOnePoint_vacuum, torusPartition]
  rw [hrw]
  exact hvac

end Descent

end VOA
