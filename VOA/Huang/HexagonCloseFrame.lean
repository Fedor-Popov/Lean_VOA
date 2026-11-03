import VOA.Huang.HexagonCloseMain
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Hexagon closure: four-point functions in logarithmic coordinates

The iterate `iterL I d ℓ = Σ_w c_w e^{(w-α-β)ℓ}` (a function of a logarithm `ℓ` of the inner
coordinate) and the product `prodL J d λ = Σ_w c_w e^{(δ-α-w)λ}` (a function of a logarithm `λ`
of the outer coordinate `1 + r`) are holomorphic on the half planes `Re ℓ < 0`
(`analyticOnNhd_iterL`) and `Re λ > 0` (`analyticOnNhd_prodL`) — on the **universal covers** of
their discs of convergence, so no branch cut is involved.  The real-segment identity
`It I = Pr J` continues to the strip `S = {Re ℓ < 0, |Im ℓ| < π/2}` (`iterL_eq_prodL`):

`iterL I d ℓ = prodL J d (log(1 + e^ℓ))`     (`ℓ ∈ S`).

Strong rationality enters only through the proved real summability and the bounded imaginary
parts of weights (`exists_im_bound`).
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
open Complex Filter Topology
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

/-! ## Elementary analysis -/

theorem exp_mul_le_add {t x a b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    Real.exp (t * x) ≤ Real.exp (t * a) + Real.exp (t * b) := by
  rcases le_or_gt 0 t with ht | ht
  · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxb ht)
    linarith [Real.exp_pos (t * a)]
  · have := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hax ht.le)
    linarith [Real.exp_pos (t * b)]

/-- A sequence of real points accumulating at the midpoint of an interval. -/
theorem frequently_of_real {P : ℂ → Prop} {a b : ℝ} (hab : a < b)
    (h : ∀ t : ℝ, a < t → t < b → P t) :
    ∃ᶠ z in 𝓝[≠] (((a + b) / 2 : ℝ) : ℂ), P z := by
  set m : ℝ := (a + b) / 2 with hm
  set e : ℝ := (b - a) / 4 with he
  have he0 : 0 < e := by rw [he]; linarith
  set t : ℕ → ℝ := fun n => m + e / ((n : ℝ) + 1) with ht
  have htpos : ∀ n : ℕ, 0 < e / ((n : ℝ) + 1) := fun n => by positivity
  have htle : ∀ n : ℕ, e / ((n : ℝ) + 1) ≤ e := fun n => by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact div_le_self he0.le hn
  have hlim : Tendsto (fun n => ((t n : ℝ) : ℂ)) atTop (𝓝[≠] ((m : ℝ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h0 : Tendsto t atTop (𝓝 (m + e * 0)) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul e).const_add m
        refine this.congr fun n => ?_
        simp only [ht]; ring
      rw [mul_zero, add_zero] at h0
      exact (Complex.continuous_ofReal.tendsto _).comp h0
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ht]
      intro heq
      have := Complex.ofReal_injective heq
      linarith [htpos n]
  refine hlim.frequently (Frequently.of_forall fun n => ?_)
  exact h (t n) (by simp only [ht, hm]; linarith [htpos n, htle n])
    (by simp only [ht, hm]; linarith [htpos n, htle n])

/-- The identity theorem on a convex open set, from an open nonempty piece. -/
theorem eqOn_of_convex {f g : ℂ → ℂ} {U O : Set ℂ} (hUc : Convex ℝ U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hO : IsOpen O) (hOU : O ⊆ U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) (hfg : Set.EqOn f g O) : Set.EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hUc.isPreconnected (hOU hz₀)
    (Filter.eventuallyEq_of_mem (hO.mem_nhds hz₀) hfg)

/-! ## Products as functions of the logarithm of the outer coordinate -/

variable (F : FusionChoice W) {X Y Z T : Ordinary W}

/-- The product as a function of a chosen logarithm `λ` of the outer coordinate `1 + r`. -/
def prodL (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (lam : ℂ) : ℂ :=
  ∑' w : ℂ, prodCoef F J d w * Complex.exp ((d.δ - d.α - w) * lam)

theorem prodL_log (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    prodL F J d (Real.log (1 + d.coordinate)) = productEvaluation F J d := by
  have h1 : (0 : ℝ) < 1 + d.coordinate := by linarith [d.positive]
  refine tsum_congr fun w => ?_
  rw [productWeightTerm_eq, Complex.cpow_def_of_ne_zero (by
      rw [show (1 + (d.coordinate : ℂ)) = ((1 + d.coordinate : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast h1.ne'),
    show (1 + (d.coordinate : ℂ)) = ((1 + d.coordinate : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log h1.le, mul_comm (Complex.ofReal _)]

theorem iterL_withCoord (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) (ℓ : ℂ) : iterL F I (d.withCoord r h0 h1) ℓ = iterL F I d ℓ := rfl

theorem prodL_withCoord (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) (lam : ℂ) :
    prodL F J (d.withCoord r h0 h1) lam = prodL F J d lam := rfl

variable (hV : StronglyRational W)
include hV

/-- Real summability of the product at **every** outer radius `R > 1`. -/
theorem summable_norm_prodCoef_ge (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T)
    {R : ℝ} (hR : 1 < R) :
    Summable fun w => ‖prodCoef F J d w‖ * R ^ (d.δ - d.α - w).re := by
  obtain ⟨Bl, hBl⟩ := (F Y Z).isMod.boundedBelow
  set R₀ : ℝ := min R (3 / 2) with hR₀
  have hR₀1 : 1 < R₀ := lt_min hR (by norm_num)
  have hR₀R : R₀ ≤ R := min_le_left _ _
  have hR₀2 : R₀ - 1 < 1 := by have := min_le_right R (3 / 2); rw [← hR₀] at this; linarith
  set T₀ : ℝ := max 0 ((d.δ - d.α).re - Bl) with hT₀
  have hs := (summable_norm_prodCoef F hV J d (r := R₀ - 1) (by linarith) hR₀2).mul_left
    ((R / R₀) ^ T₀)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun w => ?_) hs
  by_cases hc : prodCoef F J d w = 0
  · rw [hc, norm_zero, zero_mul]; positivity
  have hwb : (F Y Z).isMod.weight w ≠ ⊥ := fun hb => hc (prodCoef_eq_zero_of_bot F J d hb)
  have hw := hBl w hwb
  have hRR : 1 ≤ R / R₀ := by rw [le_div_iff₀ (by linarith)]; linarith
  have hsplit : R ^ (d.δ - d.α - w).re = R₀ ^ (d.δ - d.α - w).re *
      (R / R₀) ^ (d.δ - d.α - w).re := by
    rw [Real.div_rpow (by linarith) (by linarith)]
    field_simp
  have hexp : (R / R₀) ^ (d.δ - d.α - w).re ≤ (R / R₀) ^ T₀ := by
    refine Real.rpow_le_rpow_of_exponent_le hRR ?_
    have : (d.δ - d.α - w).re = (d.δ - d.α).re - w.re := by simp
    rw [this, hT₀]
    exact le_max_of_le_right (by linarith)
  rw [hsplit, show 1 + (R₀ - 1) = R₀ by ring]
  have h0 : 0 ≤ R₀ ^ (d.δ - d.α - w).re := Real.rpow_nonneg (by linarith) _
  calc ‖prodCoef F J d w‖ * (R₀ ^ (d.δ - d.α - w).re * (R / R₀) ^ (d.δ - d.α - w).re)
      ≤ ‖prodCoef F J d w‖ * (R₀ ^ (d.δ - d.α - w).re * (R / R₀) ^ T₀) := by gcongr
    _ = (R / R₀) ^ T₀ * (‖prodCoef F J d w‖ * R₀ ^ (d.δ - d.α - w).re) := by ring

/-- The iterate is holomorphic in the logarithm `ℓ` on the half plane `Re ℓ < 0`. -/
theorem analyticOnNhd_iterL (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    AnalyticOnNhd ℂ (iterL F I d) {ℓ | ℓ.re < 0} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_re continuous_const)
  obtain ⟨B, hB⟩ := exists_im_bound hV (tensorObj F X Y)
  intro ℓ₀ hℓ₀
  have hℓ₀ : ℓ₀.re < 0 := hℓ₀
  set a : ℝ := ℓ₀.re - 1 with ha
  set b : ℝ := ℓ₀.re / 2 with hb
  set c : ℝ := |ℓ₀.im| + 1 with hc
  set C : ℝ := Real.exp ((|B| + |(d.α + d.β).im|) * c) with hC
  set U : Set ℂ := {ℓ | a < ℓ.re ∧ ℓ.re < b ∧ |ℓ.im| < c} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_re continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_im) continuous_const))
  have hℓ₀U : ℓ₀ ∈ U := ⟨by rw [ha]; linarith, by rw [hb]; linarith, by rw [hc]; linarith⟩
  have hsum : Summable fun w => ‖iterCoef F I d w‖ *
      (Real.exp ((w - d.α - d.β).re * a) + Real.exp ((w - d.α - d.β).re * b)) * C := by
    refine Summable.mul_right C ?_
    simp_rw [mul_add]
    have h1 := summable_norm_iterCoef F hV I d (r := Real.exp a) (Real.exp_pos a)
      (by rw [Real.exp_lt_one_iff]; rw [ha]; linarith)
    have h2 := summable_norm_iterCoef F hV I d (r := Real.exp b) (Real.exp_pos b)
      (by rw [Real.exp_lt_one_iff]; rw [hb]; linarith)
    refine (h1.congr fun w => ?_).add (h2.congr fun w => ?_)
    · rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp, mul_comm a]
    · rw [Real.rpow_def_of_pos (Real.exp_pos b), Real.log_exp, mul_comm b]
  have hdiff : DifferentiableOn ℂ (iterL F I d) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun w => ?_) hUo (fun w ℓ hℓ => ?_)
    · exact ((differentiable_const _).mul
        ((differentiable_const _).mul differentiable_id).cexp).differentiableOn
    · rw [norm_mul]
      by_cases hcw : iterCoef F I d w = 0
      · rw [hcw, norm_zero, zero_mul, zero_mul, zero_mul]
      have hwb : (F X Y).isMod.weight w ≠ ⊥ := fun hb' =>
        hcw (iterCoef_eq_zero_of_bot F I d hb')
      have him : |(w - d.α - d.β).im| ≤ |B| + |(d.α + d.β).im| := by
        have : (w - d.α - d.β).im = w.im - (d.α + d.β).im := by simp; ring
        rw [this]
        refine (abs_sub _ _).trans ?_
        have : |w.im| ≤ |B| := (hB w hwb).trans (le_abs_self B)
        linarith
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ((norm_exp_mul_le _ _).trans ?_) (norm_nonneg _)
      refine mul_le_mul (exp_mul_le_add hℓ.1.le hℓ.2.1.le) ?_ (Real.exp_pos _).le
        (by positivity)
      rw [hC]
      exact Real.exp_le_exp.2 (mul_le_mul him hℓ.2.2.le (abs_nonneg _) (by positivity))
  exact (hdiff.differentiableAt (hUo.mem_nhds hℓ₀U)).differentiableWithinAt

/-- The product is holomorphic in the logarithm `λ` on the half plane `Re λ > 0`. -/
theorem analyticOnNhd_prodL (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    AnalyticOnNhd ℂ (prodL F J d) {lam | 0 < lam.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const continuous_re)
  obtain ⟨B, hB⟩ := exists_im_bound hV (tensorObj F Y Z)
  intro l₀ hl₀
  have hl₀ : 0 < l₀.re := hl₀
  set a : ℝ := l₀.re / 2 with ha
  set b : ℝ := l₀.re + 1 with hb
  set c : ℝ := |l₀.im| + 1 with hc
  set C : ℝ := Real.exp ((|B| + |(d.δ - d.α).im|) * c) with hC
  set U : Set ℂ := {l | a < l.re ∧ l.re < b ∧ |l.im| < c} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_re continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_im) continuous_const))
  have hl₀U : l₀ ∈ U := ⟨by rw [ha]; linarith, by rw [hb]; linarith, by rw [hc]; linarith⟩
  have hsum : Summable fun w => ‖prodCoef F J d w‖ *
      (Real.exp ((d.δ - d.α - w).re * a) + Real.exp ((d.δ - d.α - w).re * b)) * C := by
    refine Summable.mul_right C ?_
    simp_rw [mul_add]
    have h1 := summable_norm_prodCoef_ge F hV J d (R := Real.exp a)
      (by rw [Real.one_lt_exp_iff]; rw [ha]; linarith)
    have h2 := summable_norm_prodCoef_ge F hV J d (R := Real.exp b)
      (by rw [Real.one_lt_exp_iff]; rw [hb]; linarith)
    refine (h1.congr fun w => ?_).add (h2.congr fun w => ?_)
    · rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp, mul_comm a]
    · rw [Real.rpow_def_of_pos (Real.exp_pos b), Real.log_exp, mul_comm b]
  have hdiff : DifferentiableOn ℂ (prodL F J d) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun w => ?_) hUo (fun w l hl => ?_)
    · exact ((differentiable_const _).mul
        ((differentiable_const _).mul differentiable_id).cexp).differentiableOn
    · rw [norm_mul]
      by_cases hcw : prodCoef F J d w = 0
      · rw [hcw, norm_zero, zero_mul, zero_mul, zero_mul]
      have hwb : (F Y Z).isMod.weight w ≠ ⊥ := fun hb' =>
        hcw (prodCoef_eq_zero_of_bot F J d hb')
      have him : |(d.δ - d.α - w).im| ≤ |B| + |(d.δ - d.α).im| := by
        have : (d.δ - d.α - w).im = (d.δ - d.α).im - w.im := by simp
        rw [this]
        refine (abs_sub _ _).trans ?_
        have : |w.im| ≤ |B| := (hB w hwb).trans (le_abs_self B)
        linarith
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ((norm_exp_mul_le _ _).trans ?_) (norm_nonneg _)
      refine mul_le_mul (exp_mul_le_add hl.1.le hl.2.1.le) ?_ (Real.exp_pos _).le
        (by positivity)
      rw [hC]
      exact Real.exp_le_exp.2 (mul_le_mul him hl.2.2.le (abs_nonneg _) (by positivity))
  exact (hdiff.differentiableAt (hUo.mem_nhds hl₀U)).differentiableWithinAt

/-! ## The real-segment identity continues to the strip -/

/-- The strip `{Re ℓ < 0, |Im ℓ| < π/2}`. -/
def strip : Set ℂ := {ℓ | ℓ.re < 0 ∧ |ℓ.im| < Real.pi / 2}

omit hV in
theorem isOpen_strip : IsOpen strip :=
  (isOpen_lt continuous_re continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)

omit hV in
theorem convex_strip : Convex ℝ strip := by
  have h : strip = {ℓ : ℂ | ℓ.re < 0} ∩ ({ℓ : ℂ | ℓ.im < Real.pi / 2} ∩
      {ℓ : ℂ | -(Real.pi / 2) < ℓ.im}) := by
    ext ℓ; simp only [strip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]; tauto
  rw [h]
  refine (convex_halfSpace_lt ?_ 0).inter ((convex_halfSpace_lt ?_ _).inter
    (convex_halfSpace_gt ?_ _))
  · exact Complex.reLm.isLinear
  · exact Complex.imLm.isLinear
  · exact Complex.imLm.isLinear

omit hV in
theorem one_add_exp_re_pos {ℓ : ℂ} (hℓ : |ℓ.im| < Real.pi / 2) :
    1 < (1 + Complex.exp ℓ).re := by
  rw [Complex.add_re, Complex.one_re, Complex.exp_re]
  have hcos : 0 < Real.cos ℓ.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le ℓ.im],
    by linarith [le_abs_self ℓ.im]⟩
  have := mul_pos (Real.exp_pos ℓ.re) hcos
  linarith

/-- **The frame lemma**: a real-segment identity `It I = Pr J` holds on the whole strip, in
logarithmic coordinates: `iterL I d ℓ = prodL J d (log(1 + e^ℓ))`. -/
theorem iterL_eq_prodL (I : IterateSpace F X Y Z T) (J : ProductSpace F X Y Z T)
    (h : iterateEvaluation F I = productEvaluation F J) (d : FourPointTest X Y Z T) {ℓ : ℂ}
    (hℓ : ℓ ∈ strip) :
    iterL F I d ℓ = prodL F J d (Complex.log (1 + Complex.exp ℓ)) := by
  have hf : AnalyticOnNhd ℂ (iterL F I d) strip := fun z hz =>
    analyticOnNhd_iterL F hV I d z hz.1
  have hg : AnalyticOnNhd ℂ (fun ℓ => prodL F J d (Complex.log (1 + Complex.exp ℓ))) strip := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_strip
    have hre := one_add_exp_re_pos hz.2
    have hslit : 1 + Complex.exp z ∈ Complex.slitPlane := Or.inl (by linarith)
    have hlog : 0 < (Complex.log (1 + Complex.exp z)).re := by
      rw [Complex.log_re]
      exact Real.log_pos (lt_of_lt_of_le hre (Complex.re_le_norm _))
    have h1 : DifferentiableAt ℂ (fun ℓ => Complex.log (1 + Complex.exp ℓ)) z :=
      ((differentiableAt_const _).add (differentiableAt_id.cexp)).clog hslit
    have h2 : DifferentiableAt ℂ (prodL F J d) (Complex.log (1 + Complex.exp z)) :=
      (analyticOnNhd_prodL F hV J d _ hlog).differentiableAt
    exact (h2.comp z h1).differentiableWithinAt
  have hfreq : ∃ᶠ z in 𝓝[≠] (((-1 + -(1 / 2)) / 2 : ℝ) : ℂ),
      iterL F I d z = prodL F J d (Complex.log (1 + Complex.exp z)) := by
    refine frequently_of_real (by norm_num) fun t ht1 ht2 => ?_
    have hρ0 : 0 < Real.exp t := Real.exp_pos t
    have hρ1 : Real.exp t < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have e1 : ((t : ℝ) : ℂ) = (Real.log (Real.exp t) : ℂ) := by rw [Real.log_exp]
    have e2 : Complex.log (1 + Complex.exp (t : ℂ)) = (Real.log (1 + Real.exp t) : ℂ) := by
      rw [← Complex.ofReal_exp, show (1 + ((Real.exp t : ℝ) : ℂ)) = ((1 + Real.exp t : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_log (by positivity)]
    rw [e2, e1]
    have := congrFun h (d.withCoord (Real.exp t) hρ0 hρ1)
    rw [← iterL_log, ← prodL_log] at this
    exact this
  have hpt : (((-1 + -(1 / 2)) / 2 : ℝ) : ℂ) ∈ strip := by
    refine ⟨by simp only [Complex.ofReal_re]; norm_num, ?_⟩
    simp only [Complex.ofReal_im, abs_zero]
    positivity
  exact hf.eqOn_of_preconnected_of_frequently_eq hg convex_strip.isPreconnected hpt hfreq hℓ

end HexagonClose
end VOA.Huang.TensorCat
