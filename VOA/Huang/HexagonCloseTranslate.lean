import VOA.Huang.HexagonCloseGlue

/-! # Hexagon closure: the inner-braiding translation identity

`InnerBraidTranslation F p s` (the product `G ∘ (1 × c_{X,Z})` re-expanded around the other inner
point) is proved here for strongly rational `W` and the exponential phases `p.c n = e^{κ(n+1)}`,
`κ = sπi` (`innerBraidTranslation_of_phase`).  No new series manipulation is needed: write
`G = Ω_p(K')` with `K' = Ω_{p⁻¹}(G)` (`skewP_skewP_inv`), so that
`G ∘ (1 × c) = Ω_p(K' ∘ (c × 1))` (`skewP_restrictInputs`).  Then

* the product side of a skewed iterate (`productEvaluation_skewP`), continued in the logarithm
  `λ` of the outer coordinate to `Re λ > 0` (`prodL_skewP`), and
* the iterate side of a braided iterate (`iterateEvaluation_braid`), continued in the logarithm
  `ℓ` of the inner coordinate to `Re ℓ < -log 2` (`iterL_braid`),

express both sides through the iterates of `K'` at the real point `-log(ζ-1)`; the two finite
`L₋₁`-sums agree by the binomial theorem (`sum_sc_mul_sc`).
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

variable (F : FusionChoice W) {X Y Z T : Ordinary W}

/-! ## The binomial identity for the `L₋₁`-coefficients -/

/-- `Σ_{a ≤ k} ((-1)^a/a!) ((-1)^{k-a}/(k-a)!) x^a = ((-1)^k/k!) (1 + x)^k`. -/
theorem sum_sc_mul_sc (x : ℂ) (k : ℕ) :
    ∑ a ∈ Finset.range (k + 1), sc a * x ^ a * sc (k - a) = sc k * (1 + x) ^ k := by
  rw [add_comm (1 : ℂ) x, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  have hak : a ≤ k := by omega
  rw [one_pow, mul_one, sc, sc, sc]
  have hfa : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hfb : ((k - a).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - a)
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hch : (k.choose a : ℂ) = (k.factorial : ℂ) / (a.factorial * (k - a).factorial) := by
    rw [Nat.choose_eq_factorial_div_factorial hak,
      Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hak)
        (by push_cast; exact mul_ne_zero hfa hfb)]
    push_cast; ring
  rw [hch]
  have hpow : ((-1 : ℂ) ^ a) * (-1) ^ (k - a) = (-1) ^ k := by
    rw [← pow_add, Nat.add_sub_cancel' hak]
  rw [← hpow]
  field_simp


/-- The Cauchy product of the two `e^{-L₋₁}`-sums against a finitely supported family. -/
theorem tsum_sc_cauchy (x : ℂ) (I : ℕ → ℂ) {N : ℕ} (hI : ∀ k, N ≤ k → I k = 0) :
    ∑' a : ℕ, sc a * x ^ a * ∑' j : ℕ, sc j * I (a + j) =
      ∑' k : ℕ, sc k * (1 + x) ^ k * I k := by
  set g : ℕ × ℕ → ℂ := fun q => sc q.1 * x ^ q.1 * (sc q.2 * I (q.1 + q.2)) with hg
  have hsupp : ∀ q ∉ Finset.range N ×ˢ Finset.range N, g q = 0 := by
    intro q hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hq
    have : N ≤ q.1 + q.2 := by omega
    simp only [hg, hI _ this, mul_zero]
  have hS : Summable g := summable_of_ne_finset_zero hsupp
  have h1 : ∑' q, g q = ∑' a : ℕ, sc a * x ^ a * ∑' j : ℕ, sc j * I (a + j) := by
    rw [hS.tsum_prod]
    refine tsum_congr fun a => ?_
    rw [← tsum_mul_left]
  have h2 : HasSum (fun k => ∑ q ∈ Finset.antidiagonal k, g q) (∑' q, g q) := by
    have h := (Finset.sigmaAntidiagonalEquivProd.hasSum_iff (f := g)).mpr hS.hasSum
    refine h.sigma fun k => ?_
    have := hasSum_fintype (fun c : Finset.antidiagonal k => g c.1)
    rwa [Finset.sum_coe_sort] at this
  rw [← h1, ← h2.tsum_eq]
  refine tsum_congr fun k => ?_
  have h3 : ∑ q ∈ Finset.antidiagonal k, g q =
      I k * ∑ q ∈ Finset.antidiagonal k, (fun a j => sc a * x ^ a * sc j) q.1 q.2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_antidiagonal] at hq
    simp only [hg, hq]
    ring
  rw [h3, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a j => sc a * x ^ a * sc j) k,
    sum_sc_mul_sc]
  ring

/-! ## Test bookkeeping -/

/-- Two ways of writing the test `(z, x, y; f ∘ L₋₁^{a+j})`. -/
theorem iterL_lowerK_lowerK (K : IterateSpace F Z X Y T) (d : FourPointTest X Y Z T) (a j : ℕ)
    (ℓ : ℂ) :
    iterL F K ((d.lowerK a).lowerK j) ℓ = iterL F K ((d.swapM.lowerK (a + j)).swapM) ℓ := by
  refine tsum_congr fun w => ?_
  congr 1
  change d.functional ((T.isMod.Lm1 ^ a) ((T.isMod.Lm1 ^ j) (K.val (w + d.β - (d.δ - a - j) - 1)
      ((F Z X).intertwiner.val (d.γ + d.α - w - 1) d.z d.x) d.y))) =
    d.functional ((T.isMod.Lm1 ^ (a + j)) (K.val (w + d.β - (d.δ - ((a + j : ℕ) : ℂ)) - 1)
      ((F Z X).intertwiner.val (d.γ + d.α - w - 1) d.z d.x) d.y))
  rw [pow_add, Module.End.mul_apply]
  congr 4
  push_cast; ring_nf

variable (hV : StronglyRational W)
include hV

/-! ## Continuation of the product-side formula -/

/-- `productEvaluation_skewP` continued to every logarithm `λ` with `Re λ > 0`. -/
theorem prodL_skewP (p : Phase) {s : ℝ} (_hs : s = 1 ∨ s = -1)
    (hκ : ∀ n, p.c n = Complex.exp (kap s * (n + 1))) (K : IterateSpace F Y Z X T)
    (d : FourPointTest X Y Z T) {lam : ℂ} (hlam : 0 < lam.re) :
    prodL F (skewP p (tensorObj F Y Z) X T K) d lam =
      Complex.exp ((d.δ - d.α - d.β - d.γ) * (lam - kap s)) *
        ∑' j : ℕ, sc j * iterL F K (d.lowerK j) (kap s - lam) := by
  obtain ⟨N, hN⟩ := exists_weight_bot T.isMod d.δ
  have hfin : ∀ l : ℂ, ∑' j : ℕ, sc j * iterL F K (d.lowerK j) l =
      ∑ j ∈ Finset.range N, sc j * iterL F K (d.lowerK j) l := fun l =>
    tsum_eq_sum fun j hj => by
      rw [Finset.mem_range, not_lt] at hj
      rw [iterL_lowerK_eq_zero F K d (hN j hj), mul_zero]
  rw [hfin]
  have hf := analyticOnNhd_prodL F hV (skewP p (tensorObj F Y Z) X T K) d
  have hg : AnalyticOnNhd ℂ (fun l => Complex.exp ((d.δ - d.α - d.β - d.γ) * (l - kap s)) *
      ∑ j ∈ Finset.range N, sc j * iterL F K (d.lowerK j) (kap s - l)) {l | 0 < l.re} := by
    refine DifferentiableOn.analyticOnNhd (fun l hl => ?_) (isOpen_re_gt 0)
    have hl : 0 < l.re := hl
    have hre : (kap s - l).re < 0 := by rw [Complex.sub_re, kap_re]; linarith
    refine ((((differentiableAt_id.sub_const _).const_mul _).cexp).mul
      (DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul ?_)
      ).differentiableWithinAt
    exact ((analyticOnNhd_iterL F hV K (d.lowerK j) _ hre).differentiableAt).comp l
      ((differentiableAt_const _).sub differentiableAt_id)
  have hfreq : ∃ᶠ l in 𝓝[≠] (((1 / 10 + 1 / 2) / 2 : ℝ) : ℂ),
      prodL F (skewP p (tensorObj F Y Z) X T K) d l =
        Complex.exp ((d.δ - d.α - d.β - d.γ) * (l - kap s)) *
          ∑ j ∈ Finset.range N, sc j * iterL F K (d.lowerK j) (kap s - l) := by
    refine frequently_of_real (by norm_num) fun μ hμ1 hμ2 => ?_
    set t : ℝ := Real.exp μ - 1 with ht
    have ht0 : 0 < t := by rw [ht]; linarith [Real.add_one_lt_exp (by linarith : μ ≠ 0)]
    have ht1 : t < 1 := by
      rw [ht]
      have : Real.exp μ < 2 := by
        calc Real.exp μ < Real.exp (1 / 2) := Real.exp_lt_exp.2 hμ2
          _ < 2 := by
            have := Real.exp_one_lt_d9
            have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
              rw [← Real.exp_nat_mul]; norm_num
            nlinarith [Real.exp_pos (1 / 2)]
      linarith
    have hlog : Real.log (1 + t) = μ := by rw [ht]; simp
    have h := productEvaluation_skewP F hV p (κ := kap s) hκ K (d.withCoord t ht0 ht1)
    rw [← prodL_log] at h
    change prodL F (skewP p (tensorObj F Y Z) X T K) d (Real.log (1 + t)) =
      Complex.exp ((d.δ - d.α - d.β - d.γ) * ((Real.log (1 + t) : ℂ) - kap s)) *
        ∑' j : ℕ, sc j * iterL F K (d.lowerK j) (kap s - Real.log (1 + t)) at h
    rw [hlog, hfin] at h
    exact h
  have hpt : (((1 / 10 + 1 / 2) / 2 : ℝ) : ℂ) ∈ {l : ℂ | 0 < l.re} := by
    change 0 < ((((1 / 10 + 1 / 2) / 2 : ℝ)) : ℂ).re
    simp only [Complex.ofReal_re]; norm_num
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_re_gt 0).isPreconnected hpt hfreq hlam

/-! ## Continuation of the iterate-side formula -/

/-- `iterateEvaluation_braid` continued to every logarithm `ℓ` with `Re ℓ < -log 2`. -/
theorem iterL_braid (p : Phase) {s : ℝ} (_hs : s = 1 ∨ s = -1)
    (hκ : ∀ n, p.c n = Complex.exp (kap s * (n + 1))) (M : IterateSpace F Y X Z T)
    (e : FourPointTest X Y Z T) {ℓ : ℂ} (hℓ : ℓ.re < -Real.log 2) :
    iterL F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) e ℓ =
      Complex.exp ((e.δ - e.α - e.β - e.γ) * Complex.log (1 + Complex.exp ℓ)) *
        iterL F M e.swapM (ℓ - Complex.log (1 + Complex.exp ℓ) - kap s) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hf : AnalyticOnNhd ℂ (iterL F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) e)
      {l : ℂ | l.re < -Real.log 2} := fun l hl =>
    analyticOnNhd_iterL F hV _ e l (by
      have : l.re < -Real.log 2 := hl
      change l.re < 0
      linarith)
  -- facts on the region
  have hreg : ∀ l : ℂ, l.re < -Real.log 2 →
      0 < (1 + Complex.exp l).re ∧ (l - Complex.log (1 + Complex.exp l) - kap s).re < 0 := by
    intro l hl
    have he : ‖Complex.exp l‖ < 1 / 2 := by
      rw [Complex.norm_exp]
      calc Real.exp l.re < Real.exp (-Real.log 2) := Real.exp_lt_exp.2 hl
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have hre : 1 / 2 < (1 + Complex.exp l).re := by
      have := Complex.abs_re_le_norm (Complex.exp l)
      rw [Complex.add_re, Complex.one_re]
      linarith [neg_abs_le (Complex.exp l).re]
    refine ⟨by linarith, ?_⟩
    rw [Complex.sub_re, Complex.sub_re, kap_re, sub_zero, Complex.log_re]
    have hn : 1 / 2 < ‖1 + Complex.exp l‖ := lt_of_lt_of_le hre (Complex.re_le_norm _)
    have := Real.log_lt_log (by norm_num) hn
    rw [one_div, Real.log_inv] at this
    linarith
  have hg : AnalyticOnNhd ℂ (fun l => Complex.exp ((e.δ - e.α - e.β - e.γ) *
      Complex.log (1 + Complex.exp l)) *
        iterL F M e.swapM (l - Complex.log (1 + Complex.exp l) - kap s))
      {l : ℂ | l.re < -Real.log 2} := by
    refine DifferentiableOn.analyticOnNhd (fun l hl => ?_) (isOpen_re_lt _)
    obtain ⟨h1, h2⟩ := hreg l hl
    have hlog : DifferentiableAt ℂ (fun l => Complex.log (1 + Complex.exp l)) l :=
      ((differentiableAt_const 1).add differentiableAt_id.cexp).clog (Or.inl h1)
    refine ((hlog.const_mul _).cexp.mul ?_).differentiableWithinAt
    exact ((analyticOnNhd_iterL F hV M e.swapM _ h2).differentiableAt).comp l
      ((differentiableAt_id.sub hlog).sub_const _)
  have hfreq : ∃ᶠ l in 𝓝[≠] (((-2 + -1) / 2 : ℝ) : ℂ),
      iterL F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) e l =
        Complex.exp ((e.δ - e.α - e.β - e.γ) * Complex.log (1 + Complex.exp l)) *
          iterL F M e.swapM (l - Complex.log (1 + Complex.exp l) - kap s) := by
    refine frequently_of_real (by norm_num) fun μ hμ1 hμ2 => ?_
    set r : ℝ := Real.exp μ with hrdef
    have hr0 : 0 < r := Real.exp_pos μ
    have hr2 : r < 1 / 2 := by
      calc r < Real.exp (-1) := Real.exp_lt_exp.2 hμ2
        _ < 1 / 2 := by
          rw [Real.exp_neg]
          have := Real.exp_one_gt_d9
          rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
          linarith
    have h := iterateEvaluation_braid F hV p (κ := kap s) hκ M (e.withCoord r hr0 (by linarith))
      hr2
    rw [← iterL_log] at h
    have hl1 : Complex.log (1 + Complex.exp (μ : ℂ)) = (Real.log (1 + r) : ℂ) := by
      rw [← Complex.ofReal_exp, show (1 + ((Real.exp μ : ℝ) : ℂ)) = ((1 + r : ℝ) : ℂ) by
        rw [hrdef]; push_cast; ring, Complex.ofReal_log (by positivity)]
    rw [hl1]
    have hμr : (μ : ℂ) = (Real.log r : ℂ) := by rw [hrdef, Real.log_exp]
    rw [hμr]
    exact h
  have hpt : (((-2 + -1) / 2 : ℝ) : ℂ) ∈ {l : ℂ | l.re < -Real.log 2} := by
    change ((((-2 + -1) / 2 : ℝ)) : ℂ).re < -Real.log 2
    simp only [Complex.ofReal_re]
    have := Real.log_two_lt_d9
    linarith
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_re_lt _).isPreconnected hpt hfreq hℓ

/-! ## The inner-braiding translation identity -/

/-- **The inner-braiding translation identity holds** for every strongly rational `W` and
every exponential phase `p.c n = e^{κ(n+1)}`, `κ = sπi`. -/
theorem innerBraidTranslation_of_phase (p : Phase) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hκ : ∀ n, p.c n = Complex.exp (kap s * (n + 1))) : InnerBraidTranslation F p s := by
  intro X Y Z T G d ζ hζ
  obtain ⟨K', rfl⟩ : ∃ K' : IterateSpace F Z X Y T, G = skewP p (tensorObj F Z X) Y T K' :=
    ⟨skewP p.inv Y (tensorObj F Z X) T G, (skewP_skewP_inv p Y (tensorObj F Z X) T G).symm⟩
  rw [← skewP_restrictInputs p K' (braidingP p F X Z).hom (𝟙 Y)]
  have hζ0 : 0 < ζ := by linarith
  have hu0 : 0 < ζ - 1 := by linarith
  set Lu : ℂ := (Real.log (ζ - 1) : ℂ) with hLu
  set Lz : ℂ := (Real.log ζ : ℂ) with hLz
  set c : ℂ := d.δ - d.α - d.β - d.γ with hc
  obtain ⟨N, hN⟩ := exists_weight_bot T.isMod d.δ
  set I : ℕ → ℂ := fun k => iterL F K' ((d.swapM.lowerK k).swapM) (-Lu) with hI
  have hIN : ∀ k : ℕ, N ≤ k → I k = 0 := by
    intro k hk
    have h := iterL_lowerK_lowerK F K' d 0 k (-Lu)
    rw [zero_add] at h
    simp only [hI]
    rw [← h]
    refine iterL_lowerK_eq_zero F K' (d.lowerK 0) ?_ _
    change T.isMod.weight (d.δ - ((0 : ℕ) : ℂ) - k) = ⊥
    rw [Nat.cast_zero, sub_zero]
    exact hN k hk
  set x : ℂ := Complex.exp (-Lu) with hx
  have hy : Complex.exp (Lz - Lu) = 1 + x := by
    rw [hx, Complex.exp_sub, Complex.exp_neg, hLz, hLu, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
      Real.exp_log hζ0, Real.exp_log hu0]
    have : ((ζ - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    field_simp
    push_cast; ring
  -- the left side
  have hLzre : 0 < Lz.re := by
    rw [hLz, Complex.ofReal_re]; exact Real.log_pos (by linarith)
  rw [prodL_skewP F hV p hs hκ _ d.swapM hLzre]
  have hC4 : ∀ k : ℕ, iterL F (restrictInputs (braidingP p F X Z).hom (𝟙 Y) K')
      (d.swapM.lowerK k) (kap s - Lz) =
        Complex.exp ((d.δ - k - d.α - d.γ - d.β) * (Lu - Lz)) * I k := by
    intro k
    have hre : (kap s - Lz).re < -Real.log 2 := by
      rw [Complex.sub_re, kap_re, zero_sub, hLz, Complex.ofReal_re, neg_lt_neg_iff]
      exact Real.log_lt_log (by norm_num) hζ
    have h := iterL_braid F hV p hs hκ K' (d.swapM.lowerK k) hre
    have h1 : 1 + Complex.exp (kap s - Lz) = (((ζ - 1) / ζ : ℝ) : ℂ) := by
      rw [Complex.exp_sub, exp_kap hs, hLz, ← Complex.ofReal_exp, Real.exp_log hζ0]
      have : ((ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hζ0.ne'
      push_cast
      field_simp
      ring
    have h2 : Complex.log (1 + Complex.exp (kap s - Lz)) = Lu - Lz := by
      rw [h1, ← Complex.ofReal_log (div_pos hu0 hζ0).le, Real.log_div hu0.ne' hζ0.ne']
      push_cast; rfl
    rw [h, h2, show kap s - Lz - (Lu - Lz) - kap s = -Lu by ring]
    rfl
  simp_rw [hC4]
  -- the right side
  have hLure : 0 < (Lu + kap s).re := by
    rw [Complex.add_re, kap_re, add_zero, hLu, Complex.ofReal_re]
    exact Real.log_pos (by linarith)
  have hC3 : ∀ a : ℕ, prodL F (skewP p (tensorObj F Z X) Y T K') (d.lowerK a) (Lu + kap s) =
      Complex.exp ((d.δ - a - d.β - d.γ - d.α) * Lu) * ∑' j : ℕ, sc j * I (a + j) := by
    intro a
    rw [prodL_skewP F hV p hs hκ K' (d.lowerK a) hLure,
      show Lu + kap s - kap s = Lu by ring, show kap s - (Lu + kap s) = -Lu by ring]
    congr 1
    refine tsum_congr fun j => ?_
    rw [iterL_lowerK_lowerK]
  change _ = Complex.exp ((d.α + d.β + d.γ - d.δ) * kap s) *
    ∑' a : ℕ, sc a * prodL F (skewP p (tensorObj F Z X) Y T K') (d.lowerK a) (Lu + kap s)
  simp_rw [hC3]
  -- reduce to the Cauchy product
  have hk : ∀ k : ℕ, Complex.exp ((d.δ - k - d.α - d.γ - d.β) * (Lu - Lz)) =
      Complex.exp (c * (Lu - Lz)) * (1 + x) ^ k := by
    intro k
    rw [← hy, ← Complex.exp_nat_mul, ← Complex.exp_add, hc]
    congr 1; ring
  have ha : ∀ a : ℕ, Complex.exp ((d.δ - a - d.β - d.γ - d.α) * Lu) =
      Complex.exp (c * Lu) * x ^ a := by
    intro a
    rw [hx, ← Complex.exp_nat_mul, ← Complex.exp_add, hc]
    congr 1; ring
  simp_rw [hk, ha]
  have hcauchy := tsum_sc_cauchy x I hIN
  have e1 : ∑' k : ℕ, sc k * (Complex.exp (c * (Lu - Lz)) * (1 + x) ^ k * I k) =
      Complex.exp (c * (Lu - Lz)) * ∑' k : ℕ, sc k * (1 + x) ^ k * I k := by
    rw [← tsum_mul_left]; refine tsum_congr fun k => ?_; ring
  have e2 : ∑' a : ℕ, sc a * (Complex.exp (c * Lu) * x ^ a * ∑' j : ℕ, sc j * I (a + j)) =
      Complex.exp (c * Lu) * ∑' a : ℕ, sc a * x ^ a * ∑' j : ℕ, sc j * I (a + j) := by
    rw [← tsum_mul_left]; refine tsum_congr fun a => ?_; ring
  rw [e1, e2, hcauchy]
  have e3 : Complex.exp ((d.swapM.δ - d.swapM.α - d.swapM.β - d.swapM.γ) * (Lz - kap s)) *
      Complex.exp (c * (Lu - Lz)) =
      Complex.exp ((d.α + d.β + d.γ - d.δ) * kap s) * Complex.exp (c * Lu) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hc]
    congr 1
    change (d.δ - d.β - d.α - d.γ) * (Lz - kap s) + (d.δ - d.α - d.β - d.γ) * (Lu - Lz) = _
    ring
  rw [← mul_assoc, e3, mul_assoc]

end HexagonClose
end VOA.Huang.TensorCat
