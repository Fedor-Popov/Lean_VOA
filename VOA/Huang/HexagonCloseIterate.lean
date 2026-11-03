import VOA.Huang.HexagonCloseProduct
import VOA.Huang.BraidingTranslate

/-! # Hexagon closure: the iterate side `It(M ∘ (c_{X,Y} × 1))` as a continued iterate of `M`

For `M ∈ I((Y ⊠ X) Z; T)` and the braiding `c_{X,Y} = braidingP p F X Y` with an admissible phase
of exponential form `p.c n = e^{κ(n+1)}`, the iterate of `M ∘ (c_{X,Y} × 1)` at a real test
`(x, y, z; f; r)` is a double series: skew-symmetry gives `c(𝒴_{XY}(x, r)y) =
e^{rL₋₁}𝒴_{YX}(y, e^{…}r)x`, and the `L₋₁`-derivative property of `M` turns `e^{rL₋₁}` into a
translation of the outer variable, i.e. negative binomial series
`Σ_k C(m+k, k)(-r)^k = (1+r)^{-m-1}`.  For `0 < r < 1/2` the double series is absolutely
summable, and the rearrangement gives (`iterateEvaluation_braid`)

`It(M ∘ (c_{X,Y} × 1))(x, y, z; f; r) = (1+r)^{δ-α-β-γ} · It_M(y, x, z; f)(log r - log(1+r) - κ)`,

the iterate of `M` at the **continued** coordinate `ρ = e^{-κ} r/(1+r)` (`e^{πi} r/(1+r)` for FHL's
`Ω₀`).  The bound `r < 1/2` is exactly where the majorant `Σ ‖b_w‖ (r/(1-r))^{w}` converges; the
extension to all `r` is done by `HexagonClose.iterate_eq_product_of_small` (identity theorem).
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff VOA.Huang.BraidingSkew VOA.SkewIntertwiner
open Complex
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

open BraidRibbon

variable (F : FusionChoice W) {X Y Z T : Ordinary W}

/-- The `(w', k)` term of the double series: `b_{w'} c(n') r^{w'-α-β} · C(m'+k, k) (-r)^k`, with
`b` the iterate coefficient of `M` on the swapped test, `n' = α+β-w'-1`, `m' = w'+γ-δ-1`. -/
def braidTerm (p : Phase) (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T)
    (q : ℂ × ℕ) : ℂ :=
  iterCoef F M d.swapM q.1 * p.c (d.α + d.β - q.1 - 1) *
    (d.coordinate : ℂ) ^ (q.1 - d.α - d.β) *
    (bc (q.1 + d.γ - d.δ - 1 + q.2) q.2 * (-(d.coordinate : ℂ)) ^ q.2)

/-- The shear `(w, k) ↦ (w - k, k)`. -/
def shear : ℂ × ℕ ≃ ℂ × ℕ where
  toFun q := (q.1 - q.2, q.2)
  invFun q := (q.1 + q.2, q.2)
  left_inv q := by simp
  right_inv q := by simp

theorem iterCoef_swapM (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T) (w : ℂ) :
    iterCoef F M d.swapM w = d.functional (M.val (w + d.γ - d.δ - 1)
      ((F Y X).intertwiner.val (d.β + d.α - w - 1) d.y d.x) d.z) := rfl

/-- Step A: each iterate term of `M ∘ (c × 1)` is the (finite) `k`-sum along a shear fibre. -/
theorem iterateWeightTerm_braid (p : Phase) (M : IterateSpace F Y X Z T)
    (d : FourPointTest X Y Z T) (w : ℂ) :
    HasSum (fun k : ℕ => braidTerm F p M d (shear (w, k)))
      (iterateWeightTerm F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) d w) := by
  set n := d.α + d.β - w - 1 with hn
  set m := w + d.γ - d.δ - 1 with hm
  set r := d.coordinate with hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast d.positive.ne'
  have htr := trunc_of_isIntertwining (F Y X).intertwiner.property
  obtain ⟨K₀, hK₀⟩ := htr.bound d.y d.x n
  -- the coefficient of the braided iterate
  have hcoef : iterCoef F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) d w =
      ∑ k ∈ Finset.range K₀, p.c n * (bc m k * iterCoef F M d.swapM (w - k)) := by
    change d.functional (M.val m ((braidingP p F X Y).hom.val
      ((F X Y).intertwiner.val n d.x d.y)) d.z) = _
    erw [braidingP_intertwiner, skewP_val, skewModes_apply htr, sSum_eq_sum K₀ hK₀]
    rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, map_sum, LinearMap.sum_apply,
      map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [sTerm, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
    have hY := Y_Lm1_pow M.property k m ((F Y X).intertwiner.val (n + k) d.y d.x)
    change sc k * d.functional ((M.val m ((Lm1 (F Y X).isMod.toWeakModule ^ k)
      ((F Y X).intertwiner.val (n + k) d.y d.x))) d.z) = _
    rw [hY, LinearMap.smul_apply, map_smul, smul_eq_mul, ← mul_assoc, sc_mul_prod,
      iterCoef_swapM, show m - k = w - k + d.γ - d.δ - 1 by rw [hm]; ring,
      show n + k = d.β + d.α - (w - k) - 1 by rw [hn]; ring]
  rw [iterateWeightTerm_eq, hcoef, Finset.sum_mul]
  have hfin : ∀ k ∉ Finset.range K₀, braidTerm F p M d (shear (w, k)) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    simp only [braidTerm, shear, Equiv.coe_fn_mk]
    rw [iterCoef_swapM, show d.β + d.α - (w - k) - 1 = n + k by rw [hn]; ring, hK₀ k hk]
    simp
  have hs : HasSum (fun k : ℕ => braidTerm F p M d (shear (w, k)))
      (∑ k ∈ Finset.range K₀, braidTerm F p M d (shear (w, k))) :=
    hasSum_sum_of_ne_finset_zero hfin
  convert hs using 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [braidTerm, shear, Equiv.coe_fn_mk]
  have hph : p.c (d.α + d.β - (w - k) - 1) = (-1) ^ k * p.c n := by
    rw [show d.α + d.β - (w - k) - 1 = n + k by rw [hn]; ring, phase_nat p.succ]
  have hpow : (r : ℂ) ^ (w - k - d.α - d.β) * (-(r : ℂ)) ^ k =
      (-1) ^ k * (r : ℂ) ^ (w - d.α - d.β) := by
    rw [neg_pow, show w - (k : ℂ) - d.α - d.β = (w - d.α - d.β) + (-(k : ℂ)) by ring,
      Complex.cpow_add _ _ hr0, Complex.cpow_neg, Complex.cpow_natCast]
    field_simp
  rw [hph, show w - (k : ℂ) + d.γ - d.δ - 1 + k = m by rw [hm]; ring]
  have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-(iterCoef F M d.swapM (w - k) * (-1) ^ k * p.c n * bc m k)) * hpow
    - (p.c n * bc m k * iterCoef F M d.swapM (w - k) * (r : ℂ) ^ (w - d.α - d.β)) * h1

/-! ## Step C: the fibre sums are negative binomial series -/

theorem hasSum_braidTerm_fiber (p : Phase) (M : IterateSpace F Y X Z T)
    (d : FourPointTest X Y Z T) (w : ℂ) :
    HasSum (fun k : ℕ => braidTerm F p M d (w, k))
      (iterCoef F M d.swapM w * p.c (d.α + d.β - w - 1) *
        (d.coordinate : ℂ) ^ (w - d.α - d.β) *
        (1 + (d.coordinate : ℂ)) ^ (-(w + d.γ - d.δ - 1) - 1)) := by
  set r := d.coordinate with hr
  have ht : ‖-(r : ℂ)‖ < 1 := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.positive]; exact d.less_one
  have h := (hasSum_bc (w + d.γ - d.δ - 1 + 1) ht).mul_left
    (iterCoef F M d.swapM w * p.c (d.α + d.β - w - 1) * (r : ℂ) ^ (w - d.α - d.β))
  have e1 : (1 : ℂ) / (1 - -(r : ℂ)) ^ (w + d.γ - d.δ - 1 + 1) =
      (1 + (r : ℂ)) ^ (-(w + d.γ - d.δ - 1) - 1) := by
    rw [sub_neg_eq_add, one_div, show -(w + d.γ - d.δ - 1) - 1 = -(w + d.γ - d.δ - 1 + 1) by
      ring, Complex.cpow_neg]
  rw [e1] at h
  refine h.congr_fun fun k => ?_
  simp only [braidTerm]
  rw [show w + d.γ - d.δ - 1 + 1 + (k : ℂ) - 1 = w + d.γ - d.δ - 1 + k by ring]

/-! ## Step B: absolute summability for `r < 1/2` -/

/-- The real majorant of `braidTerm`. -/
def braidMaj (p : Phase) (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T)
    (q : ℂ × ℕ) : ℝ :=
  ‖iterCoef F M d.swapM q.1‖ * ‖p.c (d.α + d.β - q.1 - 1)‖ *
    d.coordinate ^ (q.1 - d.α - d.β).re *
    (Ring.choose (‖q.1 + d.γ - d.δ - 1‖ + q.2) q.2 * d.coordinate ^ q.2)

theorem norm_braidTerm_le (p : Phase) (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T)
    (q : ℂ × ℕ) : ‖braidTerm F p M d q‖ ≤ braidMaj F p M d q := by
  obtain ⟨w, k⟩ := q
  simp only [braidTerm, braidMaj]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos d.positive,
    norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.positive]
  have hb := norm_bc_le (w + d.γ - d.δ - 1) 0 k
  simp only [Nat.cast_zero, add_zero] at hb
  have h0 : 0 ≤ ‖iterCoef F M d.swapM w‖ * ‖p.c (d.α + d.β - w - 1)‖ *
      d.coordinate ^ (w - d.α - d.β).re := by
    have := Real.rpow_nonneg d.positive.le (w - d.α - d.β).re
    positivity
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hb (pow_nonneg d.positive.le k)) h0

theorem braidMaj_nonneg (p : Phase) (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T)
    (q : ℂ × ℕ) : 0 ≤ braidMaj F p M d q :=
  (norm_nonneg _).trans (norm_braidTerm_le F p M d q)

theorem hasSum_braidMaj_fiber (p : Phase) (M : IterateSpace F Y X Z T)
    (d : FourPointTest X Y Z T) (w : ℂ) :
    HasSum (fun k : ℕ => braidMaj F p M d (w, k))
      (‖iterCoef F M d.swapM w‖ * ‖p.c (d.α + d.β - w - 1)‖ *
        d.coordinate ^ (w - d.α - d.β).re *
        (1 / (1 - d.coordinate) ^ (‖w + d.γ - d.δ - 1‖ + 1))) := by
  have h := (hasSum_choose_real (‖w + d.γ - d.δ - 1‖ + 1) d.positive.le d.less_one).mul_left
    (‖iterCoef F M d.swapM w‖ * ‖p.c (d.α + d.β - w - 1)‖ *
      d.coordinate ^ (w - d.α - d.β).re)
  refine h.congr_fun fun k => ?_
  simp only [braidMaj]
  rw [show ‖w + d.γ - d.δ - 1‖ + 1 + (k : ℝ) - 1 = ‖w + d.γ - d.δ - 1‖ + k by ring]

variable (hV : StronglyRational W)
include hV

theorem summable_braidMaj (p : Phase) {κ : ℂ} (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1)))
    (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T) (hr : d.coordinate < 1 / 2) :
    Summable (braidMaj F p M d) := by
  set r := d.coordinate with hr'
  have hr0 := d.positive
  have h1r : 0 < 1 - r := by linarith
  have h1r1 : 1 - r ≤ 1 := by linarith
  have hκre := re_eq_zero_of_phase p hκ
  obtain ⟨B, hB⟩ := exists_im_bound hV (tensorObj F Y X)
  obtain ⟨Bl, hBl⟩ := (F Y X).isMod.boundedBelow
  set ρ : ℝ := r / (1 - r) with hρ
  have hρ0 : 0 < ρ := div_pos hr0 h1r
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one h1r]; linarith
  set C1 : ℝ := Real.exp (|κ.im| * (|(d.α + d.β).im| + |B|)) with hC1
  set A : ℝ := (d.α + d.β).re + (|(d.γ - d.δ).re - 1| + 2 * |Bl| + |B| + |(d.γ - d.δ).im| + 1)
    with hA
  rw [summable_prod_of_nonneg (fun q => braidMaj_nonneg F p M d q)]
  refine ⟨fun w => (hasSum_braidMaj_fiber F p M d w).summable, ?_⟩
  have hbase := (summable_norm_iterCoef F hV M d.swapM hρ0 hρ1).mul_left (C1 * (1 - r) ^ (-A))
  refine Summable.of_nonneg_of_le (fun w => ?_) (fun w => ?_) hbase
  · rw [(hasSum_braidMaj_fiber F p M d w).tsum_eq]
    have := Real.rpow_nonneg hr0.le (w - d.α - d.β).re
    have := Real.rpow_nonneg h1r.le (‖w + d.γ - d.δ - 1‖ + 1)
    positivity
  rw [(hasSum_braidMaj_fiber F p M d w).tsum_eq]
  by_cases hc : iterCoef F M d.swapM w = 0
  · simp only [hc, norm_zero, zero_mul, mul_zero, le_refl]
  have hwb : (F Y X).isMod.weight w ≠ ⊥ := fun hb => hc (iterCoef_eq_zero_of_bot F M d.swapM hb)
  have hwim : |w.im| ≤ |B| := (hB w hwb).trans (le_abs_self B)
  have hwre : Bl ≤ w.re := hBl w hwb
  -- the phase
  have hph : ‖p.c (d.α + d.β - w - 1)‖ ≤ C1 := by
    rw [hκ, Complex.norm_exp, hC1]
    refine Real.exp_le_exp.2 ?_
    have : (κ * (d.α + d.β - w - 1 + 1)).re = -(κ.im * ((d.α + d.β).im - w.im)) := by
      simp [Complex.mul_re, hκre]
    rw [this]
    have h1 : -(κ.im * ((d.α + d.β).im - w.im)) ≤ |κ.im| * |(d.α + d.β).im - w.im| := by
      rw [← abs_mul]; exact neg_le_abs _
    have h2 : |(d.α + d.β).im - w.im| ≤ |(d.α + d.β).im| + |B| :=
      (abs_sub _ _).trans (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  -- the binomial factor
  have hnorm : ‖w + d.γ - d.δ - 1‖ + 1 ≤ (w - d.α - d.β).re + A := by
    have hn := Complex.norm_le_abs_re_add_abs_im (w + d.γ - d.δ - 1)
    have hre : (w + d.γ - d.δ - 1).re = w.re + ((d.γ - d.δ).re - 1) := by simp; ring
    have him : (w + d.γ - d.δ - 1).im = w.im + (d.γ - d.δ).im := by simp; ring
    rw [hre, him] at hn
    have e1 : |w.re + ((d.γ - d.δ).re - 1)| ≤ w.re + |(d.γ - d.δ).re - 1| + 2 * |Bl| := by
      rcases le_or_gt 0 (w.re + ((d.γ - d.δ).re - 1)) with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self ((d.γ - d.δ).re - 1), abs_nonneg Bl]
      · rw [abs_of_neg h]
        linarith [neg_abs_le ((d.γ - d.δ).re - 1), neg_abs_le Bl, abs_nonneg Bl,
          abs_nonneg ((d.γ - d.δ).re - 1)]
    have e2 : |w.im + (d.γ - d.δ).im| ≤ |B| + |(d.γ - d.δ).im| :=
      (abs_add_le _ _).trans (by linarith)
    have e3 : (w - d.α - d.β).re = w.re - (d.α + d.β).re := by simp; ring
    rw [e3, hA]
    linarith
  have hpow : 1 / (1 - r) ^ (‖w + d.γ - d.δ - 1‖ + 1) ≤ (1 - r) ^ (-((w - d.α - d.β).re + A)) := by
    rw [one_div, ← Real.rpow_neg h1r.le]
    exact Real.rpow_le_rpow_of_exponent_ge h1r h1r1 (by linarith)
  have hsplit : r ^ (w - d.α - d.β).re * (1 - r) ^ (-((w - d.α - d.β).re + A)) =
      (1 - r) ^ (-A) * ρ ^ (w - d.swapM.α - d.swapM.β).re := by
    have e : (w - d.swapM.α - d.swapM.β).re = (w - d.α - d.β).re := by
      change (w - d.β - d.α).re = _; congr 1; ring
    rw [e, hρ, Real.div_rpow hr0.le h1r.le, neg_add, Real.rpow_add h1r, Real.rpow_neg h1r.le]
    field_simp
    rfl
  calc ‖iterCoef F M d.swapM w‖ * ‖p.c (d.α + d.β - w - 1)‖ * r ^ (w - d.α - d.β).re *
        (1 / (1 - r) ^ (‖w + d.γ - d.δ - 1‖ + 1))
      ≤ ‖iterCoef F M d.swapM w‖ * C1 * r ^ (w - d.α - d.β).re *
        (1 - r) ^ (-((w - d.α - d.β).re + A)) := by
        have := Real.rpow_nonneg hr0.le (w - d.α - d.β).re
        have := Real.rpow_nonneg h1r.le (‖w + d.γ - d.δ - 1‖ + 1)
        gcongr
    _ = C1 * (1 - r) ^ (-A) * (‖iterCoef F M d.swapM w‖ *
          ρ ^ (w - d.swapM.α - d.swapM.β).re) := by
        rw [mul_assoc _ (r ^ _), hsplit]; ring

theorem summable_braidTerm (p : Phase) {κ : ℂ} (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1)))
    (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T) (hr : d.coordinate < 1 / 2) :
    Summable (braidTerm F p M d) :=
  Summable.of_norm_bounded (summable_braidMaj F hV p hκ M d hr) (norm_braidTerm_le F p M d)

/-! ## Step D: assembly -/

/-- **The iterate side of the hexagon** (`0 < r < 1/2`): for a phase `p.c n = e^{κ(n+1)}`,
`It(M ∘ (c_{X,Y} × 1))(d) = e^{(δ-α-β-γ) log(1+r)} · It_M(d.swapM)(log r - log(1+r) - κ)`. -/
theorem iterateEvaluation_braid (p : Phase) {κ : ℂ}
    (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1)))
    (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T) (hr : d.coordinate < 1 / 2) :
    iterateEvaluation F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) d =
      Complex.exp ((d.δ - d.α - d.β - d.γ) * Real.log (1 + d.coordinate)) *
        iterL F M d.swapM
          ((Real.log d.coordinate : ℂ) - Real.log (1 + d.coordinate) - κ) := by
  set r := d.coordinate with hr'
  have hr0 := d.positive
  have hS := summable_braidTerm F hV p hκ M d hr
  have hS' : Summable (fun q => braidTerm F p M d (shear q)) := (shear.summable_iff).2 hS
  change ∑' w, iterateWeightTerm F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) d w = _
  rw [tsum_congr fun w => (iterateWeightTerm_braid F p M d w).tsum_eq.symm, ← hS'.tsum_prod,
    shear.tsum_eq (braidTerm F p M d), hS.tsum_prod,
    tsum_congr fun w => (hasSum_braidTerm_fiber F p M d w).tsum_eq, iterL, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have hr1 : (0 : ℝ) < 1 + r := by linarith
  have e1 : (r : ℂ) ^ (w - d.α - d.β) = Complex.exp ((Real.log r : ℂ) * (w - d.α - d.β)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr0.ne'), ← Complex.ofReal_log hr0.le]
  have e2 : (1 + (r : ℂ)) ^ (-(w + d.γ - d.δ - 1) - 1) =
      Complex.exp ((Real.log (1 + r) : ℂ) * (-(w + d.γ - d.δ - 1) - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr1.ne'), show (1 + (r : ℂ)) =
      ((1 + r : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log hr1.le]
  rw [e1, e2, hκ]
  change _ = _ * (iterCoef F M d.swapM w * Complex.exp ((w - d.β - d.α) * _))
  have hexp : Complex.exp (κ * (d.α + d.β - w - 1 + 1)) *
      Complex.exp ((Real.log r : ℂ) * (w - d.α - d.β)) *
      Complex.exp ((Real.log (1 + r) : ℂ) * (-(w + d.γ - d.δ - 1) - 1)) =
      Complex.exp ((d.δ - d.α - d.β - d.γ) * Real.log (1 + r)) *
        Complex.exp ((w - d.β - d.α) * ((Real.log r : ℂ) - Real.log (1 + r) - κ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  linear_combination (iterCoef F M d.swapM w) * hexp

end HexagonClose
end VOA.Huang.TensorCat
