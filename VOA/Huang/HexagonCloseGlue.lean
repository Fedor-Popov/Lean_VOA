import VOA.Huang.HexagonCloseFrame
import VOA.Huang.HexagonCloseGeom

/-! # Hexagon closure: gluing the four expansions in the hexagon coordinate

Work in the coordinate `r` of the hexagon test (`x` at `1 + r`, `y` at `1`, `z` at `0`) and fix a
sign `s = ±1` (phase `κ = sπi`; `s = -1` is FHL's `Ω₀`).  The four expansions of the one
four-point function become four explicit functions of `r` (`fA … fD`):

* `fA` — the `K`-iterates at `ℓ_K(r) = κ - log(1+r)` (the product side of the hexagon,
  `productEvaluation_skewP`), holomorphic on `|1+r| > 1`;
* `fB` — the `G`-products at `log(1 + e^{ℓ_K}) = log(r/(1+r))`, on `Re r < -1/2`;
* `fC` — the `G ∘ (1 × c_{XZ})`-products at `log(1/(1+r))`, on `|1+r| < 1`;
* `fD` — the `M`-iterates at `ℓ_M(r) = log r - log(1+r) - κ` (the iterate side of the hexagon,
  `iterateEvaluation_braid`), on `Re r > -1/2`.

The regions are bounded by the circle `|1+r| = 1` and the line `Re r = -1/2`, which meet at the
equilateral configurations `r = e^{±2πi/3}`; there **no** expansion converges.  Proved here:
`fA = fB` (from `It K = Pr G`, frame lemma), `fC = fD` (from `It M = Pr Gc`), and `fB = fC`
(from the translation identity `InnerBraidTranslation` for the inner braiding of a product).
Closing the cycle around `e^{-2πi s/3}` needs one analytic input about a single product:

`ProductHalfPlaneContinuation F`: every product four-point function `ζ ↦ Σ c_w ζ^{δ-α-w}`
(`|ζ| > 1`) continues analytically to the open half planes `Im ζ > 0` and `Im ζ < 0`
(TRUE: no singular point lies in an open half plane; Huang's convergence-and-extension theorem).

With it, `fA = fD` on `Re r > 0` (`hexagonContinuation_of_glue`).
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff VOA.Huang.BraidingSkew
open Complex Filter Topology
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

open BraidRibbon

variable (F : FusionChoice W)

/-! ## The two named analytic inputs -/

/-- **Half-plane continuation of products** (TRUE for strongly rational `W`: Huang 2005,
convergence and extension; the product function has singular points only at `ζ ∈ {0, 1, ∞}`).
Every product four-point function, as a function `ζ ↦ prodL J d (log ζ)` of the outer point on
`|ζ| > 1`, continues analytically to each open half plane `s · Im ζ > 0`. -/
def ProductHalfPlaneContinuation : Prop :=
  ∀ (A B C T : Ordinary W) (J : ProductSpace F A B C T) (d : FourPointTest A B C T) (s : ℝ),
    (s = 1 ∨ s = -1) →
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ {ζ | 0 < s * ζ.im} ∧
      ∀ ζ : ℂ, 0 < s * ζ.im → 1 < ‖ζ‖ → Φ ζ = prodL F J d (Complex.log ζ)

/-- **The inner-braiding translation identity** for products with phase `p` (`κ = sπi`), on the
real ray `ζ > 2`: `Pr(G ∘ (1 × c_{XZ}))(y,x,z; f)(log ζ)
= e^{(α+β+γ-δ)κ} Σ_a ((-1)^a/a!) Pr_G(y,z,x; f∘L₋₁^a)(log(ζ-1) + κ)`. -/
def InnerBraidTranslation (p : Phase) (s : ℝ) : Prop :=
  ∀ (X Y Z T : Ordinary W) (G : ProductSpace F Y Z X T) (d : FourPointTest X Y Z T) (ζ : ℝ),
    2 < ζ →
    prodL F (restrictInputs (𝟙 Y) (braidingP p F X Z).hom G) d.swapM (Real.log ζ) =
      Complex.exp ((d.α + d.β + d.γ - d.δ) * kap s) *
        ∑' a : ℕ, sc a * prodL F G (d.lowerK a) (Real.log (ζ - 1) + kap s)

/-! ## The four functions -/

variable {X Y Z T : Ordinary W}

def EA (s : ℝ) (d : FourPointTest X Y Z T) (r : ℂ) : ℂ :=
  Complex.exp ((d.δ - d.α - d.β - d.γ) * (Complex.log (1 + r) - kap s))

def ED (d : FourPointTest X Y Z T) (r : ℂ) : ℂ :=
  Complex.exp ((d.δ - d.α - d.β - d.γ) * Complex.log (1 + r))

theorem EA_eq (s : ℝ) (d : FourPointTest X Y Z T) (r : ℂ) :
    EA s d r = ED d r * Complex.exp ((d.α + d.β + d.γ - d.δ) * kap s) := by
  rw [EA, ED, ← Complex.exp_add]; congr 1; ring

def fA (s : ℝ) (K : IterateSpace F Y Z X T) (d : FourPointTest X Y Z T) (N : ℕ) (r : ℂ) : ℂ :=
  EA s d r * ∑ j ∈ Finset.range N, sc j * iterL F K (d.lowerK j) (ellK s r)

def fB (s : ℝ) (G : ProductSpace F Y Z X T) (d : FourPointTest X Y Z T) (N : ℕ) (r : ℂ) : ℂ :=
  EA s d r * ∑ j ∈ Finset.range N, sc j *
    prodL F G (d.lowerK j) (Complex.log (1 + Complex.exp (ellK s r)))

def fC (s : ℝ) (Gc : ProductSpace F Y X Z T) (d : FourPointTest X Y Z T) (r : ℂ) : ℂ :=
  ED d r * prodL F Gc d.swapM (Complex.log (1 + Complex.exp (ellM s r)))

def fD (s : ℝ) (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T) (r : ℂ) : ℂ :=
  ED d r * iterL F M d.swapM (ellM s r)

/-! ## Regions -/

def Lh (s : ℝ) : Set ℂ := {r | 0 < s * r.im}

theorem isOpen_Lh (s : ℝ) : IsOpen (Lh s) :=
  isOpen_lt continuous_const (continuous_const.mul continuous_im)

theorem convex_Lh (s : ℝ) : Convex ℝ (Lh s) :=
  convex_halfSpace_gt (f := fun r : ℂ => s * r.im)
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩ 0

theorem convex_re_gt (a : ℝ) : Convex ℝ {r : ℂ | a < r.re} := convex_halfSpace_re_gt a

theorem convex_re_lt (a : ℝ) : Convex ℝ {r : ℂ | r.re < a} :=
  convex_halfSpace_lt (f := fun r : ℂ => r.re) ⟨fun x y => by simp, fun c x => by simp⟩ a

theorem convex_sim_gt (s a : ℝ) : Convex ℝ {r : ℂ | a < s * r.im} :=
  convex_halfSpace_gt (f := fun r : ℂ => s * r.im)
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩ a

theorem isOpen_re_gt (a : ℝ) : IsOpen {r : ℂ | a < r.re} :=
  isOpen_lt continuous_const continuous_re

theorem isOpen_re_lt (a : ℝ) : IsOpen {r : ℂ | r.re < a} :=
  isOpen_lt continuous_re continuous_const

theorem isOpen_sim_gt (s a : ℝ) : IsOpen {r : ℂ | a < s * r.im} :=
  isOpen_lt continuous_const (continuous_const.mul continuous_im)

/-! ## Elementary facts on the regions -/

theorem mem_slitPlane_of_sim {s : ℝ} (_hs : s = 1 ∨ s = -1) {z : ℂ} (h : 0 < s * z.im) :
    z ∈ Complex.slitPlane := by
  refine Or.inr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

theorem one_add_ne_zero_of_sim {s : ℝ} (_hs : s = 1 ∨ s = -1) {r : ℂ} (h : 0 < s * r.im) :
    1 + r ≠ 0 := by
  intro h0
  have : (1 + r).im = 0 := by rw [h0]; simp
  rw [Complex.add_im, Complex.one_im, zero_add] at this
  rw [this, mul_zero] at h
  exact lt_irrefl _ h

theorem ne_zero_of_sim {s : ℝ} (_hs : s = 1 ∨ s = -1) {r : ℂ} (h : 0 < s * r.im) : r ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

theorem normSq_one_add_sub (r : ℂ) :
    Complex.normSq (1 + r) - Complex.normSq r = 1 + 2 * r.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
    Complex.one_im]
  ring

theorem norm_lt_norm_one_add {r : ℂ} (h : -1 / 2 < r.re) : ‖r‖ < ‖1 + r‖ := by
  have h1 := normSq_one_add_sub r
  have h2 : Complex.normSq r < Complex.normSq (1 + r) := by linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

theorem norm_one_add_lt_norm {r : ℂ} (h : r.re < -1 / 2) : ‖1 + r‖ < ‖r‖ := by
  have h1 := normSq_one_add_sub r
  have h2 : Complex.normSq (1 + r) < Complex.normSq r := by linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

/-! ## Vanishing of the translated products -/

theorem prodL_lowerK_eq_zero (G : ProductSpace F Y Z X T) (d : FourPointTest X Y Z T) {a : ℕ}
    (ha : T.isMod.weight (d.δ - a) = ⊥) (lam : ℂ) : prodL F G (d.lowerK a) lam = 0 := by
  refine (tsum_congr fun w => ?_).trans tsum_zero
  have hm := VOA.Huang.FusionTop.mem_weight G.property d.hy
    (VOA.Huang.FusionTop.mem_weight (F Z X).intertwiner.property d.hz d.hx (d.γ + d.α - w - 1))
    (d.β + w - (d.δ - a) - 1)
  rw [show d.β + (d.γ + d.α - (d.γ + d.α - w - 1) - 1) - (d.β + w - (d.δ - a) - 1) - 1
    = d.δ - a by ring] at hm
  change d.functional ((T.isMod.Lm1 ^ a) (G.val (d.β + w - (d.δ - a) - 1) d.y
    ((F Z X).intertwiner.val (d.γ + d.α - w - 1) d.z d.x))) * _ = 0
  rw [mem_of_weight_eq_bot hm ha]
  simp

/-! ## Differentiability of the four functions -/

theorem differentiableAt_log_one_add {r : ℂ} (h : 1 + r ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun r : ℂ => Complex.log (1 + r)) r :=
  ((differentiableAt_const 1).add differentiableAt_id).clog h

theorem differentiableAt_EA (s : ℝ) (d : FourPointTest X Y Z T) {r : ℂ}
    (h : 1 + r ∈ Complex.slitPlane) : DifferentiableAt ℂ (EA s d) r :=
  ((differentiableAt_log_one_add h).sub_const _ |>.const_mul _).cexp

theorem differentiableAt_ED (d : FourPointTest X Y Z T) {r : ℂ}
    (h : 1 + r ∈ Complex.slitPlane) : DifferentiableAt ℂ (ED d) r :=
  ((differentiableAt_log_one_add h).const_mul _).cexp

theorem differentiableAt_ellK (s : ℝ) {r : ℂ} (h : 1 + r ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (ellK s) r :=
  (differentiableAt_const _).sub (differentiableAt_log_one_add h)

theorem differentiableAt_ellM (s : ℝ) {r : ℂ} (h0 : r ∈ Complex.slitPlane)
    (h : 1 + r ∈ Complex.slitPlane) : DifferentiableAt ℂ (ellM s) r :=
  ((differentiableAt_id.clog h0).sub (differentiableAt_log_one_add h)).sub_const _

variable (hV : StronglyRational W)
include hV

theorem differentiableAt_fA (s : ℝ) (K : IterateSpace F Y Z X T) (d : FourPointTest X Y Z T)
    (N : ℕ) {r : ℂ} (h1 : 1 < ‖1 + r‖) (hsl : 1 + r ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fA F s K d N) r := by
  have hre : (ellK s r).re < 0 := by
    rw [ellK_re]; linarith [Real.log_pos h1]
  refine (differentiableAt_EA s d hsl).mul ?_
  refine DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul ?_
  exact ((analyticOnNhd_iterL F hV K (d.lowerK j) _ hre).differentiableAt).comp r
    (differentiableAt_ellK s hsl)

theorem differentiableAt_fD (s : ℝ) (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T)
    {r : ℂ} (h0 : r ∈ Complex.slitPlane) (h1 : 1 + r ∈ Complex.slitPlane) (hlt : ‖r‖ < ‖1 + r‖) :
    DifferentiableAt ℂ (fD F s M d) r := by
  have hr0 : r ≠ 0 := Complex.slitPlane_ne_zero h0
  have hre : (ellM s r).re < 0 := by
    rw [ellM_re]; linarith [Real.log_lt_log (norm_pos_iff.2 hr0) hlt]
  refine (differentiableAt_ED d h1).mul ?_
  exact ((analyticOnNhd_iterL F hV M d.swapM _ hre).differentiableAt).comp r
    (differentiableAt_ellM s h0 h1)

theorem differentiableAt_fC {s : ℝ} (hs : s = 1 ∨ s = -1) (Gc : ProductSpace F Y X Z T)
    (d : FourPointTest X Y Z T) {r : ℂ} (him : 0 < s * r.im) (hlt : ‖1 + r‖ < 1) :
    DifferentiableAt ℂ (fC F s Gc d) r := by
  have hr0 := ne_zero_of_sim hs him
  have h10 := one_add_ne_zero_of_sim hs him
  have h0 : r ∈ Complex.slitPlane := mem_slitPlane_of_sim hs him
  have h1 : 1 + r ∈ Complex.slitPlane := mem_slitPlane_of_sim hs (by simpa using him)
  have hζ : 1 + Complex.exp (ellM s r) = 1 / (1 + r) := one_add_exp_ellM hs hr0 h10
  have hsl : 1 + Complex.exp (ellM s r) ∈ Complex.slitPlane := by
    rw [hζ]
    refine Or.inr ?_
    rw [im_one_div]
    have : (1 + r).im ≠ 0 := by
      simp only [Complex.add_im, Complex.one_im, zero_add]
      intro h; rw [h, mul_zero] at him; exact lt_irrefl _ him
    have hn : 0 < Complex.normSq (1 + r) := Complex.normSq_pos.2 h10
    exact div_ne_zero (neg_ne_zero.2 this) hn.ne'
  have hlog : 0 < (Complex.log (1 + Complex.exp (ellM s r))).re := by
    rw [Complex.log_re, hζ, norm_div, norm_one]
    refine Real.log_pos ?_
    rw [one_lt_div (norm_pos_iff.2 h10)]
    exact hlt
  refine (differentiableAt_ED d h1).mul ?_
  have hc : DifferentiableAt ℂ (fun r => Complex.log (1 + Complex.exp (ellM s r))) r :=
    ((differentiableAt_const 1).add (differentiableAt_ellM s h0 h1).cexp).clog hsl
  exact ((analyticOnNhd_prodL F hV Gc d.swapM _ hlog).differentiableAt).comp r hc

/-! ## The inner-braiding identity off the real ray -/

/-- The inner-braiding translation identity continues from the real ray `ζ > 2` to the half
plane `Re ζ > 2`. -/
theorem innerBraid_ext (p : Phase) (s : ℝ) (hT : InnerBraidTranslation F p s)
    (G : ProductSpace F Y Z X T) (d : FourPointTest X Y Z T) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → T.isMod.weight (d.δ - j) = ⊥) {ζ : ℂ} (hζ : 2 < ζ.re) :
    prodL F (restrictInputs (𝟙 Y) (braidingP p F X Z).hom G) d.swapM (Complex.log ζ) =
      Complex.exp ((d.α + d.β + d.γ - d.δ) * kap s) *
        ∑ a ∈ Finset.range N, sc a * prodL F G (d.lowerK a) (Complex.log (ζ - 1) + kap s) := by
  set Gc := restrictInputs (𝟙 Y) (braidingP p F X Z).hom G
  set U : Set ℂ := {z | 2 < z.re} with hU
  have hfin : ∀ lam : ℂ, ∑' a : ℕ, sc a * prodL F G (d.lowerK a) lam =
      ∑ a ∈ Finset.range N, sc a * prodL F G (d.lowerK a) lam := fun lam =>
    tsum_eq_sum fun a ha => by
      rw [Finset.mem_range, not_lt] at ha
      rw [prodL_lowerK_eq_zero F G d (hN a ha), mul_zero]
  have hf : AnalyticOnNhd ℂ (fun z => prodL F Gc d.swapM (Complex.log z)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) (isOpen_re_gt 2)
    have hz : 2 < z.re := hz
    have hsl : z ∈ Complex.slitPlane := Or.inl (by linarith)
    have hlog : 0 < (Complex.log z).re := by
      rw [Complex.log_re]
      exact Real.log_pos (by linarith [Complex.re_le_norm z])
    exact (((analyticOnNhd_prodL F hV Gc d.swapM _ hlog).differentiableAt).comp z
      (differentiableAt_id.clog hsl)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z => Complex.exp ((d.α + d.β + d.γ - d.δ) * kap s) *
      ∑ a ∈ Finset.range N, sc a * prodL F G (d.lowerK a) (Complex.log (z - 1) + kap s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) (isOpen_re_gt 2)
    have hz : 2 < z.re := hz
    have hsl : z - 1 ∈ Complex.slitPlane := Or.inl (by simp; linarith)
    have hlog : 0 < (Complex.log (z - 1) + kap s).re := by
      rw [Complex.add_re, kap_re, add_zero, Complex.log_re]
      refine Real.log_pos (lt_of_lt_of_le ?_ (Complex.re_le_norm _))
      simp; linarith
    refine ((differentiableAt_const _).mul (DifferentiableAt.fun_sum fun a _ =>
      (differentiableAt_const _).mul ?_)).differentiableWithinAt
    exact ((analyticOnNhd_prodL F hV G (d.lowerK a) _ hlog).differentiableAt).comp z
      (((differentiableAt_id.sub_const 1).clog hsl).add_const _)
  have hfreq : ∃ᶠ z in 𝓝[≠] (((3 + 4) / 2 : ℝ) : ℂ),
      prodL F Gc d.swapM (Complex.log z) = Complex.exp ((d.α + d.β + d.γ - d.δ) * kap s) *
        ∑ a ∈ Finset.range N, sc a * prodL F G (d.lowerK a) (Complex.log (z - 1) + kap s) := by
    refine frequently_of_real (by norm_num) fun t ht1 ht2 => ?_
    have h := hT X Y Z T G d t (by linarith)
    rw [hfin] at h
    rw [← Complex.ofReal_log (by linarith), show ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_log (by linarith)]
    exact h
  have hpt : (((3 + 4) / 2 : ℝ) : ℂ) ∈ U := by
    change 2 < (((3 + 4) / 2 : ℝ) : ℂ).re
    simp only [Complex.ofReal_re]; norm_num
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_re_gt 2).isPreconnected hpt hfreq hζ

/-! ## The gluing -/

omit hV in
theorem abs_lt_of_sign_mul {s x b : ℝ} (hs : s = 1 ∨ s = -1) (h1 : -b < s * x) (h2 : s * x < b) :
    |x| < b := by
  rcases hs with rfl | rfl <;> rw [abs_lt] <;> constructor <;> linarith

omit hV in
theorem sim_one_add (r : ℂ) (s : ℝ) : s * (1 + r).im = s * r.im := by simp

/-- The continuation of `fB` supplied by `ProductHalfPlaneContinuation`. -/
def PhiT (s : ℝ) (d : FourPointTest X Y Z T) (N : ℕ) (Φ : ℕ → ℂ → ℂ) (r : ℂ) : ℂ :=
  EA s d r * ∑ j ∈ Finset.range N, sc j * Φ j (1 + Complex.exp (ellK s r))

omit hV in
theorem sim_one_add_exp_ellK {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℂ} (hr : 0 < s * r.im) :
    0 < s * (1 + Complex.exp (ellK s r)).im := by
  rw [one_add_exp_ellK hs (one_add_ne_zero_of_sim hs hr), im_div_one_add, mul_div_assoc']
  exact div_pos hr (Complex.normSq_pos.2 (one_add_ne_zero_of_sim hs hr))

omit hV in
theorem differentiableAt_PhiT {s : ℝ} (hs : s = 1 ∨ s = -1) (d : FourPointTest X Y Z T) (N : ℕ)
    {Φ : ℕ → ℂ → ℂ} (hΦa : ∀ j, AnalyticOnNhd ℂ (Φ j) {ζ | 0 < s * ζ.im}) {r : ℂ}
    (hr : 0 < s * r.im) : DifferentiableAt ℂ (PhiT s d N Φ) r := by
  have h1 : 1 + r ∈ Complex.slitPlane := mem_slitPlane_of_sim hs (by rwa [sim_one_add])
  refine (differentiableAt_EA s d h1).mul (DifferentiableAt.fun_sum fun j _ =>
    (differentiableAt_const _).mul ?_)
  exact ((hΦa j _ (sim_one_add_exp_ellK hs hr)).differentiableAt).comp r
    ((differentiableAt_const 1).add (differentiableAt_ellK s h1).cexp)

/-- Step 1: `fA = fB` on `{Re r < -2, s Im r > 0}` (from `It K = Pr G`). -/
theorem glue_AB {s : ℝ} (hs : s = 1 ∨ s = -1) (K : IterateSpace F Y Z X T)
    (G : ProductSpace F Y Z X T) (hK : iterateEvaluation F K = productEvaluation F G)
    (d : FourPointTest X Y Z T) (N : ℕ) {r : ℂ} (hre : r.re < -2) (him : 0 < s * r.im) :
    fA F s K d N r = fB F s G d N r := by
  have him1 : 0 < s * (1 + r).im := by rwa [sim_one_add]
  have hre1 : (1 + r).re < 0 := by simp; linarith
  have hn : 1 < ‖1 + r‖ := by
    have := Complex.abs_re_le_norm (1 + r)
    have h2 : (1 + r).re < -1 := by simp; linarith
    rw [abs_of_neg hre1] at this
    linarith
  have hstrip : ellK s r ∈ strip := by
    refine ⟨by rw [ellK_re]; linarith [Real.log_pos hn], ?_⟩
    rw [ellK_im]
    have ha := sign_arg_mem_of_re_neg hs him1 hre1
    have hb := (sign_arg_mem hs him1).2
    have e : s * (s * Real.pi - Complex.arg (1 + r)) = Real.pi - s * Complex.arg (1 + r) := by
      rw [mul_sub, ← mul_assoc, sign_cases hs, one_mul]
    refine abs_lt_of_sign_mul hs ?_ ?_ <;> rw [e] <;> linarith only [ha, hb]
  simp only [fA, fB]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterL_eq_prodL F hV K G hK (d.lowerK j) hstrip]

omit hV in
/-- Step 2: `fB = PhiT` on `{Re r < -1/2, s Im r > 0}` (the half-plane continuation). -/
theorem glue_BPhi {s : ℝ} (hs : s = 1 ∨ s = -1) (G : ProductSpace F Y Z X T)
    (d : FourPointTest X Y Z T) (N : ℕ) {Φ : ℕ → ℂ → ℂ}
    (hΦ : ∀ j ζ, 0 < s * ζ.im → 1 < ‖ζ‖ → Φ j ζ = prodL F G (d.lowerK j) (Complex.log ζ))
    {r : ℂ} (hre : r.re < -1 / 2) (him : 0 < s * r.im) :
    fB F s G d N r = PhiT s d N Φ r := by
  have h10 := one_add_ne_zero_of_sim hs him
  simp only [fB, PhiT]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hΦ j _ (sim_one_add_exp_ellK hs him)]
  rw [one_add_exp_ellK hs h10, norm_div, one_lt_div (norm_pos_iff.2 h10)]
  exact norm_one_add_lt_norm hre

/-- Step 3: `fB = fC` on `{|r + 3/4| < 1/4, s Im r > 0}` (inner-braiding translation). -/
theorem glue_BC (p : Phase) {s : ℝ} (hs : s = 1 ∨ s = -1) (hT : InnerBraidTranslation F p s)
    (G : ProductSpace F Y Z X T) (d : FourPointTest X Y Z T) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → T.isMod.weight (d.δ - j) = ⊥) {r : ℂ}
    (hball : r ∈ Metric.ball (-3 / 4 : ℂ) (1 / 4)) (him : 0 < s * r.im) :
    fB F s G d N r = fC F s (restrictInputs (𝟙 Y) (braidingP p F X Z).hom G) d r := by
  have hr0 := ne_zero_of_sim hs him
  have h10 := one_add_ne_zero_of_sim hs him
  have hζ : 1 + Complex.exp (ellM s r) = 1 / (1 + r) := one_add_exp_ellM hs hr0 h10
  have hζre : 2 < (1 + Complex.exp (ellM s r)).re := by
    rw [hζ, re_one_div]
    have hn : 0 < Complex.normSq (1 + r) := Complex.normSq_pos.2 h10
    rw [lt_div_iff₀ hn]
    rw [Metric.mem_ball, dist_eq_norm] at hball
    have hb2 : Complex.normSq (r - -3 / 4) < 1 / 16 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg (r - -3 / 4)
      nlinarith
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im] at hb2 ⊢
    norm_num at hb2 ⊢
    nlinarith
  have hext := innerBraid_ext F hV p s hT G d hN hζre
  rw [add_sub_cancel_left] at hext
  have hw : s * (Complex.exp (ellM s r)).im < 0 := by
    rw [exp_ellM hs hr0 h10, Complex.neg_im, im_div_one_add]
    have hn : 0 < Complex.normSq (1 + r) := Complex.normSq_pos.2 h10
    rw [mul_neg, neg_lt_zero, mul_div_assoc']
    exact div_pos him hn
  have hlog : Complex.log (Complex.exp (ellM s r)) + kap s =
      Complex.log (1 + Complex.exp (ellK s r)) := by
    rw [← log_neg_eq hs hw, exp_ellM hs hr0 h10, neg_neg, one_add_exp_ellK hs h10]
  simp only [fB, fC]
  rw [hext, EA_eq]
  simp_rw [hlog]
  ring

/-- Step 4: `fC = fD` on `{|r + 1/2| < 1/2, Re r > -1/2, s Im r > 0}` (from `It M = Pr Gc`). -/
theorem glue_CD {s : ℝ} (hs : s = 1 ∨ s = -1) (M : IterateSpace F Y X Z T)
    (Gc : ProductSpace F Y X Z T) (hM : iterateEvaluation F M = productEvaluation F Gc)
    (d : FourPointTest X Y Z T) {r : ℂ} (hball : r ∈ Metric.ball (-1 / 2 : ℂ) (1 / 2))
    (hre : -1 / 2 < r.re) (him : 0 < s * r.im) :
    fC F s Gc d r = fD F s M d r := by
  have hr0 := ne_zero_of_sim hs him
  have h10 := one_add_ne_zero_of_sim hs him
  rw [Metric.mem_ball, dist_eq_norm] at hball
  have hb2 : Complex.normSq (r - -1 / 2) < 1 / 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_nonneg (r - -1 / 2)
    nlinarith
  have hb3 : r.re + Complex.normSq r < 0 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hb2 ⊢
    norm_num at hb2
    nlinarith
  have hreneg : r.re < 0 := by
    have := Complex.normSq_nonneg r
    linarith
  have him1 : 0 < s * (1 + r).im := by rwa [sim_one_add]
  have hre1 : 0 < (1 + r).re := by simp; linarith
  have hstrip : ellM s r ∈ strip := by
    refine ⟨?_, ?_⟩
    · rw [ellM_re]
      linarith [Real.log_lt_log (norm_pos_iff.2 hr0) (norm_lt_norm_one_add hre)]
    · have hexpre : 0 < (Complex.exp (ellM s r)).re := by
        rw [exp_ellM hs hr0 h10, Complex.neg_re, re_div_one_add, neg_pos]
        exact div_neg_of_neg_of_pos hb3 (Complex.normSq_pos.2 h10)
      have ha := sign_arg_mem_of_re_neg hs him hreneg
      have hb := (sign_arg_mem hs him).2
      have hc := (sign_arg_mem hs him1).1
      have hd := sign_arg_lt_of_re_pos hs hre1
      have habs : |(ellM s r).im| < Real.pi := by
        rw [ellM_im]
        have e : s * (Complex.arg r - Complex.arg (1 + r) - s * Real.pi) =
            s * Complex.arg r - s * Complex.arg (1 + r) - Real.pi := by
          rw [mul_sub, mul_sub, ← mul_assoc, sign_cases hs, one_mul]
        refine abs_lt_of_sign_mul hs ?_ ?_ <;> rw [e] <;> linarith only [ha, hb, hc, hd]
      rw [abs_lt] at habs
      exact abs_im_lt_of_exp_re_pos habs.1 habs.2 hexpre
  simp only [fC, fD]
  rw [iterL_eq_prodL F hV M Gc hM d.swapM hstrip]

omit hV in
theorem one_lt_norm_one_add_of_sim {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℂ}
    (hr : 1 < s * r.im) : 1 < ‖1 + r‖ := by
  have h1 := Complex.abs_im_le_norm (1 + r)
  have h2 : s * r.im ≤ |(1 + r).im| := by
    simp only [Complex.add_im, Complex.one_im, zero_add]
    rcases hs with rfl | rfl
    · simpa using le_abs_self r.im
    · have := neg_abs_le r.im
      simp only [neg_mul, one_mul]
      linarith
  linarith

omit hV in
theorem point_mem (s : ℝ) (hs : s = 1 ∨ s = -1) (a b : ℝ) :
    ((a : ℂ) + ((b * s : ℝ) : ℂ) * Complex.I).re = a ∧
      s * ((a : ℂ) + ((b * s : ℝ) : ℂ) * Complex.I).im = b := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  constructor
  · ring
  · have := sign_cases hs
    linear_combination b * this

/-- **The gluing theorem**: the half-plane continuation of products and the inner-braiding
translation identity give the hexagon continuation identity for the phase `κ = sπi`. -/
theorem hexagonContinuation_of_glue (p : Phase) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hP : ProductHalfPlaneContinuation F) (hT : InnerBraidTranslation F p s) :
    HexagonContinuation F p (kap s) := by
  intro X Y Z T K M G hK hM d hr
  obtain ⟨N, hN⟩ := exists_weight_bot T.isMod d.δ
  choose Φ hΦa hΦ using fun j : ℕ => hP Y Z X T G (d.lowerK j) s hs
  set Gc := restrictInputs (𝟙 Y) (braidingP p F X Z).hom G with hGc
  -- analyticity on the half plane
  have hPhi : ∀ U : Set ℂ, IsOpen U → U ⊆ Lh s → AnalyticOnNhd ℂ (PhiT s d N Φ) U :=
    fun U hU hUL => DifferentiableOn.analyticOnNhd (fun r hr' =>
      (differentiableAt_PhiT hs d N hΦa (hUL hr')).differentiableWithinAt) hU
  -- S3: `fA = PhiT` on `{s Im r > 1}`
  have S3 : Set.EqOn (fA F s K d N) (PhiT s d N Φ) {r | 1 < s * r.im} := by
    obtain ⟨hz1, hz2⟩ := point_mem s hs (-3) 2
    refine eqOn_of_convex (convex_sim_gt s 1) ?_ ?_
      ((isOpen_re_lt (-2)).inter (isOpen_sim_gt s 1)) Set.inter_subset_right
      (z₀ := (-3 : ℝ) + ((2 * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_) (isOpen_sim_gt s 1)
      have hr' : 1 < s * r.im := hr'
      exact (differentiableAt_fA F hV s K d N (one_lt_norm_one_add_of_sim hs hr')
        (mem_slitPlane_of_sim hs (by rw [sim_one_add]; linarith))).differentiableWithinAt
    · exact hPhi _ (isOpen_sim_gt s 1) fun r hr' => by
        change 0 < s * r.im; have : 1 < s * r.im := hr'; linarith
    · simp only [Set.mem_setOf_eq]; rw [hz1]; norm_num
    · simp only [Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨hre, him⟩
      have hre : r.re < -2 := hre
      have him : 1 < s * r.im := him
      rw [glue_AB F hV hs K G hK d N hre (by linarith),
        glue_BPhi F hs G d N (hΦ ·) (by linarith) (by linarith)]
  -- S6: `fC = PhiT` on `{|1+r| < 1, s Im r > 0}`
  have S6 : Set.EqOn (fC F s Gc d) (PhiT s d N Φ) (Metric.ball (-1 : ℂ) 1 ∩ Lh s) := by
    obtain ⟨hz1, hz2⟩ := point_mem s hs (-3 / 4) (1 / 8)
    refine eqOn_of_convex ((convex_ball _ _).inter (convex_Lh s)) ?_ ?_
      (O := Metric.ball (-3 / 4 : ℂ) (1 / 4) ∩ Lh s)
      (Metric.isOpen_ball.inter (isOpen_Lh s)) ?_
      (z₀ := ((-3 / 4 : ℝ) : ℂ) + (((1 / 8) * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_)
        (Metric.isOpen_ball.inter (isOpen_Lh s))
      have hb := hr'.1
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm] at hb
      exact (differentiableAt_fC F hV hs Gc d hr'.2 hb).differentiableWithinAt
    · exact hPhi _ (Metric.isOpen_ball.inter (isOpen_Lh s)) Set.inter_subset_right
    · intro r ⟨hb, hl⟩
      refine ⟨?_, hl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hb ⊢
      calc ‖r - -1‖ = ‖(r - -3 / 4) + 1 / 4‖ := by congr 1; ring
        _ ≤ ‖r - -3 / 4‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
        _ < 1 := by rw [show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]; linarith
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((-3 / 4 : ℝ) : ℂ) + (((1 / 8) * s : ℝ) : ℂ) * Complex.I - -3 / 4 =
          (((1 / 8) * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rcases hs with rfl | rfl <;> norm_num
    · simp only [Lh, Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨hb, hl⟩
      have hre : r.re < -1 / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hb
        have := Complex.abs_re_le_norm (r - -3 / 4)
        have h2 : (r - -3 / 4).re = r.re + 3 / 4 := by simp; norm_num
        rw [h2] at this
        linarith [le_abs_self (r.re + 3 / 4)]
      rw [← glue_BC F hV p hs hT G d hN hb hl, glue_BPhi F hs G d N (hΦ ·) hre hl]
  -- S7: `fD = PhiT` on `{Re r > -1/2, s Im r > 0}`
  have S7 : Set.EqOn (fD F s M d) (PhiT s d N Φ) ({r | -1 / 2 < r.re} ∩ Lh s) := by
    obtain ⟨hz1, hz2⟩ := point_mem s hs (-1 / 4) (1 / 4)
    refine eqOn_of_convex ((convex_re_gt _).inter (convex_Lh s)) ?_ ?_
      (O := (Metric.ball (-1 / 2 : ℂ) (1 / 2) ∩ {r : ℂ | -1 / 2 < r.re}) ∩ Lh s)
      ((Metric.isOpen_ball.inter (isOpen_re_gt _)).inter (isOpen_Lh s))
      (fun r hr' => ⟨hr'.1.2, hr'.2⟩)
      (z₀ := ((-1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I)
      ⟨⟨?_, ?_⟩, ?_⟩ ?_
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_)
        ((isOpen_re_gt _).inter (isOpen_Lh s))
      have hre : -1 / 2 < r.re := hr'.1
      have him : 0 < s * r.im := hr'.2
      exact (differentiableAt_fD F hV s M d (mem_slitPlane_of_sim hs him)
        (mem_slitPlane_of_sim hs (by rwa [sim_one_add])) (norm_lt_norm_one_add hre)
        ).differentiableWithinAt
    · exact hPhi _ ((isOpen_re_gt _).inter (isOpen_Lh s)) Set.inter_subset_right
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((-1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I - -1 / 2 =
          ((1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this]
      have hn : ‖((1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I‖ ^ 2 = 1 / 8 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
        have := sign_cases hs
        linear_combination (1 / 16) * this
      have h0 := norm_nonneg (((1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I)
      nlinarith
    · simp only [Set.mem_setOf_eq]; rw [hz1]; norm_num
    · simp only [Lh, Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨⟨hb, hre⟩, hl⟩
      have hre : -1 / 2 < r.re := hre
      have hC : r ∈ Metric.ball (-1 : ℂ) 1 ∩ Lh s := by
        refine ⟨?_, hl⟩
        rw [Metric.mem_ball, dist_eq_norm] at hb ⊢
        calc ‖r - -1‖ = ‖(r - -1 / 2) + 1 / 2‖ := by congr 1; ring
          _ ≤ ‖r - -1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
          _ < 1 := by rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; linarith
      rw [← glue_CD F hV hs M Gc hM d hb hre hl]
      exact S6 hC
  -- S8: `fA = fD` on `{Re r > 0}`
  have S8 : Set.EqOn (fA F s K d N) (fD F s M d) {r | 0 < r.re} := by
    obtain ⟨hz1, hz2⟩ := point_mem s hs 1 2
    refine eqOn_of_convex (convex_re_gt 0) ?_ ?_
      ((isOpen_sim_gt s 1).inter (isOpen_re_gt 0)) Set.inter_subset_right
      (z₀ := ((1 : ℝ) : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_) (isOpen_re_gt 0)
      have hre : 0 < r.re := hr'
      have h1 : 1 < ‖1 + r‖ := lt_of_lt_of_le (by simp; linarith) (Complex.re_le_norm _)
      exact (differentiableAt_fA F hV s K d N h1 (Or.inl (by simp; linarith))
        ).differentiableWithinAt
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_) (isOpen_re_gt 0)
      have hre : 0 < r.re := hr'
      exact (differentiableAt_fD F hV s M d (Or.inl hre) (Or.inl (by simp; linarith))
        (norm_lt_norm_one_add (by linarith))).differentiableWithinAt
    · simp only [Set.mem_setOf_eq]; rw [hz2]; norm_num
    · simp only [Set.mem_setOf_eq]; rw [hz1]; norm_num
    · intro r ⟨him, hre⟩
      have him : 1 < s * r.im := him
      have hre : 0 < r.re := hre
      rw [S3 him, S7 ⟨(by linarith : -1 / 2 < r.re), (by linarith : 0 < s * r.im)⟩]
  -- S9: evaluate at the real coordinate
  set r := d.coordinate with hrdef
  have hr0 := d.positive
  have hmem : ((r : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    change 0 < ((r : ℝ) : ℂ).re; rw [Complex.ofReal_re]; exact hr0
  have hEq := S8 hmem
  simp only [fA, fD] at hEq
  rw [EA_eq, mul_assoc] at hEq
  have hED : ED d (r : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hEq' := mul_left_cancel₀ hED hEq
  have hlog1 : Complex.log (1 + (r : ℂ)) = (Real.log (1 + r) : ℂ) := by
    rw [show (1 + (r : ℂ)) = ((1 + r : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_log (by linarith)]
  have hlog0 : Complex.log (r : ℂ) = (Real.log r : ℂ) := (Complex.ofReal_log hr0.le).symm
  have hfin : ∑' j : ℕ, sc j * iterL F K (d.lowerK j) (kap s - Real.log (1 + r)) =
      ∑ j ∈ Finset.range N, sc j * iterL F K (d.lowerK j) (kap s - Real.log (1 + r)) :=
    tsum_eq_sum fun j hj => by
      rw [Finset.mem_range, not_lt] at hj
      rw [iterL_lowerK_eq_zero F K d (hN j hj), mul_zero]
  rw [hfin]
  simp only [ellK, ellM, hlog1, hlog0] at hEq'
  exact hEq'

end HexagonClose
end VOA.Huang.TensorCat
