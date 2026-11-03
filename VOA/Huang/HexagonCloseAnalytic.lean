import VOA.Huang.BraidRibbonHexagon
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Hexagon closure, analytic preliminaries: complex continuation in the coordinate

The ordinary four-point evaluations (`iterateEvaluation`, `productEvaluation`) are sums over the
intermediate weight `w : ℂ` with powers `r^{w-α-β}` resp. `(1+r)^{δ-α-w}` of the real coordinate
`0 < r < 1`.  For a strongly rational `W` we show here:

* `exists_im_bound`: the weights of every ordinary module have bounded imaginary part (finite
  presentation by irreducible lowest-weight modules, whose weights are `h + ℕ`);
* `iterC`, `prodC`: the same series with a **complex** coordinate (principal powers) are
  holomorphic on `V = {‖z‖ < 1, 0 < Re z}` (`differentiableOn_iterC`, `differentiableOn_prodC`),
  by locally uniform domination with the proved real summability
  (`ordinaryFourPointSummability_pbw`);
* `iterate_eq_product_of_small`: an identity `iterate = product` between the two kinds of real
  evaluations that holds for all small coordinates `0 < r < ε` holds for every `0 < r < 1`
  (identity theorem on the convex set `V`).

The last statement is what lets the hexagon be checked only for small `r`, where the iterate-side
negative-binomial rearrangement is absolutely convergent.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
open Complex Filter Topology
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

/-! ## Weights of ordinary modules -/

/-- The weights of an ordinary module of a strongly rational VOA have bounded imaginary
part. -/
theorem exists_im_bound (hV : StronglyRational W) (X : Ordinary W) :
    ∃ B : ℝ, ∀ α : ℂ, X.isMod.weight α ≠ ⊥ → |α.im| ≤ B := by
  have hΦ := PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV
  obtain ⟨A⟩ := simplePresentation_nonempty hV hΦ X
  refine ⟨∑ j, |(A.part j).h.im|, fun α hα => ?_⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have hex : ∃ j, (A.proj j).val v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    rw [← A.total v]
    simp [h]
  obtain ⟨j, hj⟩ := hex
  have hmem : (A.proj j).val v ∈ (A.part j).isMod.weight α :=
    hom_mem_weight (A.proj j).property hv
  have hne : (A.part j).isMod.weight α ≠ ⊥ := by
    intro hb
    rw [hb] at hmem
    exact hj ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨n, hn⟩ := (A.part j).isLow α hne
  have him : α.im = (A.part j).h.im := by rw [hn]; simp
  rw [him]
  exact Finset.single_le_sum (f := fun j => |(A.part j).h.im|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)

theorem mem_of_weight_eq_bot {M : Type*} [AddCommGroup M] [Module ℂ M] {A : OrdVModule W M}
    {α : ℂ} {v : M} (hv : v ∈ A.weight α) (hb : A.weight α = ⊥) : v = 0 := by
  rw [hb] at hv
  exact (Submodule.mem_bot ℂ).1 hv

/-! ## Elementary bounds -/

/-- `x^a ≤ ε^a + R^a` for `0 < ε ≤ x ≤ R`. -/
theorem rpow_le_add {ε R x a : ℝ} (hε : 0 < ε) (hεx : ε ≤ x) (hxR : x ≤ R) :
    x ^ a ≤ ε ^ a + R ^ a := by
  have hx : 0 < x := hε.trans_le hεx
  rcases le_or_gt 0 a with ha | ha
  · have := Real.rpow_le_rpow hx.le hxR ha
    have h0 : 0 ≤ ε ^ a := Real.rpow_nonneg hε.le a
    linarith
  · have := Real.rpow_le_rpow_of_nonpos hε hεx ha.le
    have h0 : 0 ≤ R ^ a := Real.rpow_nonneg (hε.le.trans (hεx.trans hxR)) a
    linarith

/-- `‖z^s‖ ≤ ‖z‖^{Re s} e^{(π/2)|Im s|}` on the right half plane. -/
theorem norm_cpow_le_of_re_pos {z : ℂ} (hz : 0 < z.re) (s : ℂ) :
    ‖z ^ s‖ ≤ ‖z‖ ^ s.re * Real.exp (Real.pi / 2 * |s.im|) := by
  refine (norm_cpow_le z s).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  have harg : |arg z| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  have h1 : -(arg z * s.im) ≤ |arg z| * |s.im| := by
    rw [← abs_mul]; exact neg_le_abs _
  have h2 : |arg z| * |s.im| ≤ Real.pi / 2 * |s.im| :=
    mul_le_mul_of_nonneg_right harg.le (abs_nonneg _)
  linarith

/-! ## Coefficients and complex continuations -/

variable (F : FusionChoice W)
variable {X Y Z T : Ordinary W}

/-- The intermediate-weight coefficient of the iterate. -/
def iterCoef (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) (w : ℂ) : ℂ :=
  d.functional (I.val (w + d.γ - d.δ - 1)
    ((F X Y).intertwiner.val (d.α + d.β - w - 1) d.x d.y) d.z)

/-- The intermediate-weight coefficient of the product. -/
def prodCoef (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (w : ℂ) : ℂ :=
  d.functional (J.val (d.α + w - d.δ - 1) d.x
    ((F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z))

theorem iterateWeightTerm_eq (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) (w : ℂ) :
    iterateWeightTerm F I d w = iterCoef F I d w * (d.coordinate : ℂ) ^ (w - d.α - d.β) := rfl

theorem productWeightTerm_eq (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (w : ℂ) :
    productWeightTerm F J d w =
      prodCoef F J d w * (1 + (d.coordinate : ℂ)) ^ (d.δ - d.α - w) := rfl

/-- The iterate with a complex coordinate (principal powers). -/
def iterC (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) (z : ℂ) : ℂ :=
  ∑' w : ℂ, iterCoef F I d w * z ^ (w - d.α - d.β)

/-- The product with a complex coordinate (principal powers). -/
def prodC (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (z : ℂ) : ℂ :=
  ∑' w : ℂ, prodCoef F J d w * (1 + z) ^ (d.δ - d.α - w)

/-- The same test at another real coordinate. -/
def _root_.VOA.Huang.TensorCat.FourPointTest.withCoord (d : FourPointTest X Y Z T) (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) : FourPointTest X Y Z T :=
  { d with coordinate := r, positive := h0, less_one := h1 }

theorem iterC_coordinate (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    iterC F I d d.coordinate = iterateEvaluation F I d := rfl

theorem prodC_coordinate (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    prodC F J d d.coordinate = productEvaluation F J d := rfl

theorem iterCoef_withCoord (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) : iterCoef F I (d.withCoord r h0 h1) = iterCoef F I d := rfl

theorem prodCoef_withCoord (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) : prodCoef F J (d.withCoord r h0 h1) = prodCoef F J d := rfl

theorem iterC_withCoord (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) :
    iterateEvaluation F I (d.withCoord r h0 h1) = iterC F I d r := rfl

theorem prodC_withCoord (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) :
    productEvaluation F J (d.withCoord r h0 h1) = prodC F J d r := rfl

/-- A nonzero iterate coefficient sits at a weight of `X ⊠ Y`. -/
theorem iterCoef_eq_zero_of_bot (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T)
    {w : ℂ} (hw : (F X Y).isMod.weight w = ⊥) : iterCoef F I d w = 0 := by
  have hm := VOA.Huang.FusionTop.mem_weight (F X Y).intertwiner.property d.hx d.hy
    (d.α + d.β - w - 1)
  rw [show d.α + d.β - (d.α + d.β - w - 1) - 1 = w by ring] at hm
  rw [iterCoef, mem_of_weight_eq_bot hm hw]
  simp

/-- A nonzero product coefficient sits at a weight of `Y ⊠ Z`. -/
theorem prodCoef_eq_zero_of_bot (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T)
    {w : ℂ} (hw : (F Y Z).isMod.weight w = ⊥) : prodCoef F J d w = 0 := by
  have hm := VOA.Huang.FusionTop.mem_weight (F Y Z).intertwiner.property d.hy d.hz
    (d.β + d.γ - w - 1)
  rw [show d.β + d.γ - (d.β + d.γ - w - 1) - 1 = w by ring] at hm
  rw [prodCoef, mem_of_weight_eq_bot hm hw]
  simp

/-- The right half of the unit disc. -/
def halfDisc : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.re}

theorem isOpen_halfDisc : IsOpen halfDisc :=
  (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_re)

theorem convex_halfDisc : Convex ℝ halfDisc := by
  have h : halfDisc = Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < z.re} := by
    ext z; simp [halfDisc, Metric.mem_ball, dist_zero_right]
  rw [h]
  exact (convex_ball _ _).inter (convex_halfSpace_re_gt 0)

/-! ## Real summability, in norm -/

variable (hV : StronglyRational W)
include hV

theorem summable_norm_iterCoef (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T)
    {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Summable fun w => ‖iterCoef F I d w‖ * r ^ (w - d.α - d.β).re := by
  have hs := ((ordinaryFourPointSummability_pbw F hV X Y Z T (d.withCoord r h0 h1)).1 I)
  have hn := (summable_norm_iff (E := ℂ)).2 hs
  refine hn.congr fun w => ?_
  change ‖iterCoef F I d w * ((r : ℝ) : ℂ) ^ (w - d.α - d.β)‖ = _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0]

theorem summable_norm_prodCoef (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T)
    {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Summable fun w => ‖prodCoef F J d w‖ * (1 + r) ^ (d.δ - d.α - w).re := by
  have hs := ((ordinaryFourPointSummability_pbw F hV X Y Z T (d.withCoord r h0 h1)).2 J)
  have hn := (summable_norm_iff (E := ℂ)).2 hs
  refine hn.congr fun w => ?_
  change ‖prodCoef F J d w * (1 + ((r : ℝ) : ℂ)) ^ (d.δ - d.α - w)‖ = _
  rw [norm_mul, show (1 + ((r : ℝ) : ℂ)) = ((1 + r : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]

/-! ## Holomorphy -/

theorem differentiableOn_iterC (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    DifferentiableOn ℂ (iterC F I d) halfDisc := by
  obtain ⟨B, hB⟩ := exists_im_bound hV (tensorObj F X Y)
  set C : ℝ := Real.exp (Real.pi / 2 * (|B| + |(d.α + d.β).im|)) with hC
  intro z₀ hz₀
  have hz₀0 : 0 < ‖z₀‖ := by
    have := Complex.re_le_norm z₀; linarith [hz₀.2]
  set ε : ℝ := ‖z₀‖ / 2 with hε
  set R : ℝ := (‖z₀‖ + 1) / 2 with hR
  have hε0 : 0 < ε := by positivity
  have hεR : ε < R := by rw [hε, hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith [hz₀.1]
  set U : Set ℂ := {z | ε < ‖z‖ ∧ ‖z‖ < R ∧ 0 < z.re} with hU
  have hUo : IsOpen U :=
    ((isOpen_lt continuous_const continuous_norm).inter
      ((isOpen_lt continuous_norm continuous_const).inter
        (isOpen_lt continuous_const continuous_re)))
  have hz₀U : z₀ ∈ U := ⟨by rw [hε]; linarith, by rw [hR]; linarith [hz₀.1], hz₀.2⟩
  have hsum : Summable fun w => ‖iterCoef F I d w‖ *
      (ε ^ (w - d.α - d.β).re + R ^ (w - d.α - d.β).re) * C := by
    refine Summable.mul_right C ?_
    simp_rw [mul_add]
    exact (summable_norm_iterCoef F hV I d hε0 (by linarith)).add
      (summable_norm_iterCoef F hV I d (by linarith) hR1)
  have hdiff : DifferentiableOn ℂ (iterC F I d) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun w => ?_) hUo (fun w z hz => ?_)
    · intro z hz
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      exact DifferentiableAt.cpow differentiableAt_id (differentiableAt_const _) (Or.inl hz.2.2)
    · rw [norm_mul]
      by_cases hc : iterCoef F I d w = 0
      · rw [hc, norm_zero, zero_mul, zero_mul, zero_mul]
      have hwb : (F X Y).isMod.weight w ≠ ⊥ := fun hb => hc (iterCoef_eq_zero_of_bot F I d hb)
      have hwim := hB w hwb
      have him : |(w - d.α - d.β).im| ≤ |B| + |(d.α + d.β).im| := by
        have : (w - d.α - d.β).im = w.im - (d.α + d.β).im := by simp; ring
        rw [this]
        refine (abs_sub _ _).trans ?_
        have : |w.im| ≤ |B| := hwim.trans (le_abs_self B)
        linarith
      have h1 := norm_cpow_le_of_re_pos hz.2.2 (w - d.α - d.β)
      have h2 : ‖z‖ ^ (w - d.α - d.β).re ≤ ε ^ (w - d.α - d.β).re + R ^ (w - d.α - d.β).re :=
        rpow_le_add hε0 hz.1.le hz.2.1.le
      have h3 : Real.exp (Real.pi / 2 * |(w - d.α - d.β).im|) ≤ C := by
        rw [hC]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left him (by positivity))
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (h1.trans ?_) (norm_nonneg _)
      exact mul_le_mul h2 h3 (Real.exp_pos _).le
        (add_nonneg (Real.rpow_nonneg hε0.le _) (Real.rpow_nonneg (by linarith) _))
  exact (hdiff.differentiableAt (hUo.mem_nhds hz₀U)).differentiableWithinAt

theorem differentiableOn_prodC (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    DifferentiableOn ℂ (prodC F J d) halfDisc := by
  obtain ⟨B, hB⟩ := exists_im_bound hV (tensorObj F Y Z)
  set C : ℝ := Real.exp (Real.pi / 2 * (|B| + |(d.δ - d.α).im|)) with hC
  intro z₀ hz₀
  have hlo : 1 < ‖1 + z₀‖ := by
    have := Complex.re_le_norm (1 + z₀)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith [hz₀.2]
  have hhi : ‖1 + z₀‖ < 2 := by
    have := norm_add_le (1 : ℂ) z₀
    rw [norm_one] at this
    linarith [hz₀.1]
  set a : ℝ := (‖1 + z₀‖ - 1) / 2 with ha
  set b : ℝ := ‖1 + z₀‖ / 2 with hb
  have ha0 : 0 < a := by rw [ha]; linarith
  have hab : a < b := by rw [ha, hb]; linarith
  have hb1 : b < 1 := by rw [hb]; linarith
  set U : Set ℂ := {z | 1 + a < ‖1 + z‖ ∧ ‖1 + z‖ < 1 + b ∧ 0 < z.re} with hU
  have hc1 : Continuous fun z : ℂ => ‖1 + z‖ := (continuous_const.add continuous_id).norm
  have hUo : IsOpen U :=
    ((isOpen_lt continuous_const hc1).inter
      ((isOpen_lt hc1 continuous_const).inter (isOpen_lt continuous_const continuous_re)))
  have hz₀U : z₀ ∈ U := ⟨by rw [ha]; linarith, by rw [hb]; linarith, hz₀.2⟩
  have hsum : Summable fun w => ‖prodCoef F J d w‖ *
      ((1 + a) ^ (d.δ - d.α - w).re + (1 + b) ^ (d.δ - d.α - w).re) * C := by
    refine Summable.mul_right C ?_
    simp_rw [mul_add]
    exact (summable_norm_prodCoef F hV J d ha0 (by linarith)).add
      (summable_norm_prodCoef F hV J d (by linarith) hb1)
  have hdiff : DifferentiableOn ℂ (prodC F J d) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun w => ?_) hUo (fun w z hz => ?_)
    · intro z hz
      have hre : 0 < (1 + z).re := by
        simp only [Complex.add_re, Complex.one_re]; linarith [hz.2.2]
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      exact DifferentiableAt.cpow ((differentiableAt_const _).add differentiableAt_id)
        (differentiableAt_const _) (Or.inl hre)
    · rw [norm_mul]
      by_cases hc : prodCoef F J d w = 0
      · rw [hc, norm_zero, zero_mul, zero_mul, zero_mul]
      have hwb : (F Y Z).isMod.weight w ≠ ⊥ := fun hb => hc (prodCoef_eq_zero_of_bot F J d hb)
      have hwim := hB w hwb
      have him : |(d.δ - d.α - w).im| ≤ |B| + |(d.δ - d.α).im| := by
        have : (d.δ - d.α - w).im = (d.δ - d.α).im - w.im := by simp
        rw [this]
        refine (abs_sub _ _).trans ?_
        have : |w.im| ≤ |B| := hwim.trans (le_abs_self B)
        linarith
      have hre : 0 < (1 + z).re := by
        simp only [Complex.add_re, Complex.one_re]; linarith [hz.2.2]
      have h1 := norm_cpow_le_of_re_pos hre (d.δ - d.α - w)
      have h2 : ‖1 + z‖ ^ (d.δ - d.α - w).re ≤
          (1 + a) ^ (d.δ - d.α - w).re + (1 + b) ^ (d.δ - d.α - w).re :=
        rpow_le_add (by linarith) hz.1.le hz.2.1.le
      have h3 : Real.exp (Real.pi / 2 * |(d.δ - d.α - w).im|) ≤ C := by
        rw [hC]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left him (by positivity))
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (h1.trans ?_) (norm_nonneg _)
      exact mul_le_mul h2 h3 (Real.exp_pos _).le
        (add_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
  exact (hdiff.differentiableAt (hUo.mem_nhds hz₀U)).differentiableWithinAt

/-! ## The identity theorem in the coordinate -/

/-- **Small coordinates suffice.**  If an iterate evaluation equals a product evaluation for
all small real coordinates `0 < r < ε`, then it does so at every coordinate `0 < r < 1`. -/
theorem iterate_eq_product_of_small (I : IterateSpace F X Y Z T) (J : ProductSpace F X Y Z T)
    (d : FourPointTest X Y Z T) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ (r : ℝ) (h0 : 0 < r) (h1 : r < 1), r < ε →
      iterateEvaluation F I (d.withCoord r h0 h1) = productEvaluation F J (d.withCoord r h0 h1)) :
    iterateEvaluation F I d = productEvaluation F J d := by
  have hfa : AnalyticOnNhd ℂ (iterC F I d) halfDisc :=
    (differentiableOn_iterC F hV I d).analyticOnNhd isOpen_halfDisc
  have hga : AnalyticOnNhd ℂ (prodC F J d) halfDisc :=
    (differentiableOn_prodC F hV J d).analyticOnNhd isOpen_halfDisc
  set ε' : ℝ := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hseg : ∀ t : ℝ, 0 < t → t < ε' → iterC F I d t = prodC F J d t := by
    intro t ht0 ht1
    have := h t ht0 (by linarith) (by linarith)
    rwa [iterC_withCoord, prodC_withCoord] at this
  set t₀ : ℝ := ε' / 2 with ht₀
  have hfreq : ∃ᶠ z in 𝓝[≠] ((t₀ : ℝ) : ℂ), iterC F I d z = prodC F J d z := by
    set t : ℕ → ℝ := fun n => t₀ + ε' / 4 / ((n : ℝ) + 1) with ht
    have htpos : ∀ n : ℕ, 0 < ε' / 4 / ((n : ℝ) + 1) := fun n => by positivity
    have htle : ∀ n : ℕ, ε' / 4 / ((n : ℝ) + 1) ≤ ε' / 4 := fun n => by
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact div_le_self (by positivity) hn
    have hlim : Tendsto (fun n => ((t n : ℝ) : ℂ)) atTop (𝓝[≠] ((t₀ : ℝ) : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto t atTop (𝓝 (t₀ + ε' / 4 * 0)) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ε' / 4)).const_add t₀
          refine this.congr fun n => ?_
          simp only [ht]; ring
        rw [mul_zero, add_zero] at h0
        exact (Complex.continuous_ofReal.tendsto _).comp h0
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ht]
        intro heq
        have := Complex.ofReal_injective heq
        linarith [htpos n]
    refine hlim.frequently (Frequently.of_forall fun n => ?_)
    exact hseg (t n) (by simp only [ht, ht₀]; linarith [htpos n])
      (by simp only [ht, ht₀]; linarith [htle n])
  have ht₀V : ((t₀ : ℝ) : ℂ) ∈ halfDisc := by
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by rw [ht₀]; linarith)]
      rw [ht₀]; linarith
    · simp only [Complex.ofReal_re, ht₀]; linarith
  have hEq := hfa.eqOn_of_preconnected_of_frequently_eq hga convex_halfDisc.isPreconnected ht₀V
    hfreq
  have hdV : ((d.coordinate : ℝ) : ℂ) ∈ halfDisc := by
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.positive]; exact d.less_one
    · simp only [Complex.ofReal_re]; exact d.positive
  rw [← iterC_coordinate, ← prodC_coordinate]
  exact hEq hdV

end HexagonClose
end VOA.Huang.TensorCat
