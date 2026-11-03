import VOA.Huang.HexagonCloseAnalytic

/-! # Hexagon closure: the product side `Pr(Ω_p K)` as continued iterates of `K`

For `K ∈ I((Y ⊠ Z) X; T)` and an admissible phase `p` of exponential form
`p.c n = e^{κ(n+1)}` (FHL's `Ω₀` is `κ = -πi`, `Ω₋₁` is `κ = πi`), skew-symmetry
`Ω_p(K)(x, z) u = p.c · e^{z L₋₁} K(u, e^{…} z) x` moves the output translation `e^{L₋₁}` onto the
dual vector.  On a real four-point test `(x, y, z; f; r)` this gives the exact finite formula
(`productEvaluation_skewP`)

`Pr(Ω_p K)(x, y, z; f; r)
  = e^{(δ-α-β-γ)(log(1+r) - κ)} · Σ_j ((-1)^j / j!) · It_K(y, z, x; f ∘ L₋₁^j)(ℓ)`

with the iterate of `K` evaluated at the **continued** coordinate `ℓ = κ - log(1+r)`, i.e. at
`ρ = e^{κ}/(1+r)` (`e^{-πi}/(1+r)` for `Ω₀`), which lies outside the real segment.  The `j`-sum
is finite (`f ∘ L₋₁^j` vanishes below the lowest weight of `T`), and every series converges
absolutely (`summable_iterL`).

`iterL I d ℓ = Σ_w c_w e^{(w-α-β)ℓ}` is the iterate as a function of a chosen logarithm `ℓ` of the
coordinate (`iterL_log`: `ℓ = log r` recovers `iterateEvaluation`).
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff VOA.Huang.BraidingSkew
open Complex
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

open BraidRibbon

/-! ## `L₋₁` on weights and on supported functionals -/

theorem Lm1_pow_mem_weight {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    {α : ℂ} {v : M} (hv : v ∈ A.weight α) (j : ℕ) : (A.Lm1 ^ j) v ∈ A.weight (α + j) := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := mode_mem_weight A W.conformalVector_mem_grading_two ih 0
    convert h using 2
    push_cast; ring

/-- `f ∘ L₋₁^j` is supported at `δ - j` when `f` is supported at `δ`. -/
theorem supportedAt_comp_Lm1_pow {M : Type u} [AddCommGroup M] [Module ℂ M] {A : OrdVModule W M}
    {f : M →ₗ[ℂ] ℂ} {δ : ℂ} (hf : SupportedAt A f δ) (j : ℕ) :
    SupportedAt A (f ∘ₗ (A.Lm1 ^ j)) (δ - j) := by
  intro α hα v hv
  rw [LinearMap.comp_apply]
  exact hf (α + j) (fun h => hα (by rw [← h]; ring)) _ (Lm1_pow_mem_weight A hv j)

/-- Low weight spaces vanish: there is `N` with `T_{δ-j} = 0` for `j ≥ N`. -/
theorem exists_weight_bot {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    (δ : ℂ) : ∃ N : ℕ, ∀ j : ℕ, N ≤ j → A.weight (δ - j) = ⊥ := by
  obtain ⟨B, hB⟩ := A.boundedBelow
  refine ⟨⌈δ.re - B⌉₊ + 1, fun j hj => ?_⟩
  by_contra hne
  have h1 := hB _ hne
  have h2 : δ.re - B ≤ (⌈δ.re - B⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : ((⌈δ.re - B⌉₊ + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  push_cast at h3
  simp only [Complex.sub_re, Complex.natCast_re] at h1
  linarith

/-- An admissible phase of exponential form has purely imaginary `κ` (`e^κ = -1`). -/
theorem re_eq_zero_of_phase (p : Phase) {κ : ℂ} (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1))) :
    κ.re = 0 := by
  have h1 := p.succ 0
  rw [hκ, hκ] at h1
  have h2 : Complex.exp κ * (Complex.exp κ + 1) = 0 := by
    have e : Complex.exp (κ * (0 + 1 + 1)) = Complex.exp κ * Complex.exp κ := by
      rw [← Complex.exp_add]; ring_nf
    rw [e, show κ * ((0 : ℂ) + 1) = κ by ring] at h1
    linear_combination h1
  have h3 : Complex.exp κ = -1 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (Complex.exp_ne_zero κ)
    · linear_combination h
  have h4 := congrArg norm h3
  rw [Complex.norm_exp, norm_neg, norm_one] at h4
  exact Real.exp_eq_one_iff _ |>.1 h4

/-! ## Tests for the continued iterates -/

variable {X Y Z T : Ordinary W}

/-- The test `(y, z, x; f ∘ L₋₁^j)` for an iterate of type `(Y ⊠ Z) X → T`. -/
def _root_.VOA.Huang.TensorCat.FourPointTest.lowerK (d : FourPointTest X Y Z T) (j : ℕ) :
    FourPointTest Y Z X T where
  α := d.β
  β := d.γ
  γ := d.α
  δ := d.δ - j
  x := d.y
  y := d.z
  z := d.x
  functional := d.functional ∘ₗ (T.isMod.Lm1 ^ j)
  hx := d.hy
  hy := d.hz
  hz := d.hx
  supported := supportedAt_comp_Lm1_pow d.supported j
  coordinate := d.coordinate
  positive := d.positive
  less_one := d.less_one

/-- The test `(y, x, z; f)` for an iterate of type `(Y ⊠ X) Z → T`. -/
def _root_.VOA.Huang.TensorCat.FourPointTest.swapM (d : FourPointTest X Y Z T) :
    FourPointTest Y X Z T where
  α := d.β
  β := d.α
  γ := d.γ
  δ := d.δ
  x := d.y
  y := d.x
  z := d.z
  functional := d.functional
  hx := d.hy
  hy := d.hx
  hz := d.hz
  supported := d.supported
  coordinate := d.coordinate
  positive := d.positive
  less_one := d.less_one

/-! ## Iterates at a chosen logarithm of the coordinate -/

variable (F : FusionChoice W)

/-- The iterate as a function of a chosen logarithm `ℓ` of the coordinate:
`Σ_w c_w e^{(w - α - β) ℓ}`. -/
def iterL (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) (ℓ : ℂ) : ℂ :=
  ∑' w : ℂ, iterCoef F I d w * Complex.exp ((w - d.α - d.β) * ℓ)

theorem iterL_log (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    iterL F I d (Real.log d.coordinate) = iterateEvaluation F I d := by
  refine tsum_congr fun w => ?_
  rw [iterateWeightTerm_eq, Complex.cpow_def_of_ne_zero (by exact_mod_cast d.positive.ne'),
    ← Complex.ofReal_log d.positive.le, mul_comm (Complex.ofReal _)]

theorem norm_exp_mul_le (s ℓ : ℂ) :
    ‖Complex.exp (s * ℓ)‖ ≤ Real.exp (s.re * ℓ.re) * Real.exp (|s.im| * |ℓ.im|) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : (s * ℓ).re = s.re * ℓ.re - s.im * ℓ.im := by simp [Complex.mul_re]
  rw [this]
  have : -(s.im * ℓ.im) ≤ |s.im| * |ℓ.im| := by rw [← abs_mul]; exact neg_le_abs _
  linarith

variable (hV : StronglyRational W)
include hV

/-- The iterate converges absolutely at every logarithm `ℓ` with `e^{Re ℓ} < 1`. -/
theorem summable_norm_iterL (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ℓ : ℂ} (hℓ : ℓ.re = Real.log ρ) :
    Summable fun w => ‖iterCoef F I d w * Complex.exp ((w - d.α - d.β) * ℓ)‖ := by
  obtain ⟨B, hB⟩ := exists_im_bound hV (tensorObj F X Y)
  set C : ℝ := Real.exp ((|B| + |(d.α + d.β).im|) * |ℓ.im|) with hC
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => ?_)
    ((summable_norm_iterCoef F hV I d hρ0 hρ1).mul_right C)
  rw [norm_mul]
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
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((norm_exp_mul_le _ _).trans ?_) (norm_nonneg _)
  rw [hℓ, Real.rpow_def_of_pos hρ0, mul_comm (w - d.α - d.β).re]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right him (abs_nonneg _)

theorem summable_iterL (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ℓ : ℂ} (hℓ : ℓ.re = Real.log ρ) :
    Summable fun w => iterCoef F I d w * Complex.exp ((w - d.α - d.β) * ℓ) :=
  (summable_norm_iterL F hV I d hρ0 hρ1 hℓ).of_norm

omit hV in
/-- The continued `K`-iterates vanish once `f ∘ L₋₁^j` is supported below the lowest weight. -/
theorem iterL_lowerK_eq_zero (K : IterateSpace F Y Z X T) (d : FourPointTest X Y Z T) {j : ℕ}
    (hj : T.isMod.weight (d.δ - j) = ⊥) (ℓ : ℂ) : iterL F K (d.lowerK j) ℓ = 0 := by
  refine (tsum_congr fun w => ?_).trans tsum_zero
  have hm := VOA.Huang.FusionTop.mem_weight K.property
    (VOA.Huang.FusionTop.mem_weight (F Y Z).intertwiner.property d.hy d.hz (d.β + d.γ - w - 1))
    d.hx (w + d.α - (d.δ - j) - 1)
  rw [show d.β + d.γ - (d.β + d.γ - w - 1) - 1 + d.α - (w + d.α - (d.δ - j) - 1) - 1
    = d.δ - j by ring] at hm
  change d.functional ((T.isMod.Lm1 ^ j) (K.val (w + d.α - (d.δ - j) - 1)
    ((F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z) d.x)) * _ = 0
  rw [mem_of_weight_eq_bot hm hj]
  simp

omit hV in
/-- The coefficient of the skewed product, expanded on the continued iterate coefficients. -/
theorem prodCoef_skewP (p : Phase) (K : IterateSpace F Y Z X T) (d : FourPointTest X Y Z T)
    {N : ℕ} (hN : ∀ j : ℕ, N ≤ j → T.isMod.weight (d.δ - j) = ⊥) (w : ℂ) :
    prodCoef F (skewP p (tensorObj F Y Z) X T K) d w =
      p.c (d.α + w - d.δ - 1) *
        ∑ j ∈ Finset.range N, sc j * iterCoef F K (d.lowerK j) w := by
  set n := d.α + w - d.δ - 1 with hn
  set u := (F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z with hu
  have htr := trunc_of_isIntertwining K.property
  obtain ⟨K₀, hK₀⟩ := htr.bound u d.x n
  change d.functional (skewModes T.isMod.Lm1 p.c K.val n d.x u) = _
  rw [skewModes_apply htr, map_smul, smul_eq_mul]
  congr 1
  have hmax := sSum_eq_sum (L := T.isMod.Lm1) (max K₀ N)
    (fun j hj => hK₀ j (le_trans (le_max_left _ _) hj))
  rw [hmax, map_sum]
  have hcoef : ∀ j, d.functional (sTerm T.isMod.Lm1 K.val n u d.x j) =
      sc j * iterCoef F K (d.lowerK j) w := by
    intro j
    rw [sTerm, map_smul, smul_eq_mul]
    congr 1
    change _ = d.functional ((T.isMod.Lm1 ^ j) (K.val (w + d.α - (d.δ - j) - 1)
      ((F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z) d.x))
    rw [show w + d.α - (d.δ - j) - 1 = n + j by rw [hn]; ring]
  simp_rw [hcoef]
  refine (Finset.sum_subset (Finset.range_subset_range.2 (le_max_right K₀ N))
    (fun j hj hjN => ?_)).symm
  rw [Finset.mem_range] at hj hjN
  have hm := VOA.Huang.FusionTop.mem_weight K.property
    (VOA.Huang.FusionTop.mem_weight (F Y Z).intertwiner.property d.hy d.hz (d.β + d.γ - w - 1))
    d.hx (w + d.α - (d.δ - j) - 1)
  rw [show d.β + d.γ - (d.β + d.γ - w - 1) - 1 + d.α - (w + d.α - (d.δ - j) - 1) - 1
    = d.δ - j by ring] at hm
  change sc j * d.functional ((T.isMod.Lm1 ^ j) (K.val (w + d.α - (d.δ - j) - 1)
    ((F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z) d.x)) = 0
  rw [mem_of_weight_eq_bot hm (hN j (by omega))]
  simp

/-- **The product side of the hexagon.**  For a phase `p.c n = e^{κ(n+1)}`:
`Pr(Ω_p K)(d) = e^{(δ-α-β-γ)(log(1+r) - κ)} Σ_j ((-1)^j/j!) It_K(d.lowerK j)(κ - log(1+r))`. -/
theorem productEvaluation_skewP (p : Phase) {κ : ℂ} (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1)))
    (K : IterateSpace F Y Z X T) (d : FourPointTest X Y Z T) :
    productEvaluation F (skewP p (tensorObj F Y Z) X T K) d =
      Complex.exp ((d.δ - d.α - d.β - d.γ) * ((Real.log (1 + d.coordinate) : ℂ) - κ)) *
        ∑' j : ℕ, sc j * iterL F K (d.lowerK j) (κ - Real.log (1 + d.coordinate)) := by
  obtain ⟨N, hN⟩ := exists_weight_bot T.isMod d.δ
  set r := d.coordinate with hr
  have hr0 : 0 < 1 + r := by linarith [d.positive]
  set L : ℂ := (Real.log (1 + r) : ℂ) - κ with hL
  set E : ℂ := Complex.exp ((d.δ - d.α - d.β - d.γ) * L) with hE
  -- the `j`-tsum is the finite sum over `range N`
  have hfin : ∑' j : ℕ, sc j * iterL F K (d.lowerK j) (κ - Real.log (1 + r)) =
      ∑ j ∈ Finset.range N, sc j * iterL F K (d.lowerK j) (κ - Real.log (1 + r)) := by
    refine tsum_eq_sum fun j hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [iterL_lowerK_eq_zero F K d (hN j hj), mul_zero]
  rw [hfin, Finset.mul_sum]
  -- each continued iterate converges
  have hρ0 : 0 < 1 / (1 + r) := by positivity
  have hρ1 : 1 / (1 + r) < 1 := by rw [div_lt_one hr0]; linarith [d.positive]
  have hκre := re_eq_zero_of_phase p hκ
  have hℓ : (κ - (Real.log (1 + r) : ℂ)).re = Real.log (1 / (1 + r)) := by
    rw [Real.log_div (by norm_num) hr0.ne', Real.log_one]
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [hκre]
  have hsum : ∀ j ∈ Finset.range N, Summable fun w =>
      E * (sc j * (iterCoef F K (d.lowerK j) w *
        Complex.exp ((w - (d.lowerK j).α - (d.lowerK j).β) * (κ - Real.log (1 + r))))) :=
    fun j _ => ((summable_iterL F hV K (d.lowerK j) hρ0 hρ1 hℓ).mul_left (sc j)).mul_left E
  have hterm : ∀ w, productWeightTerm F (skewP p (tensorObj F Y Z) X T K) d w =
      ∑ j ∈ Finset.range N, E * (sc j * (iterCoef F K (d.lowerK j) w *
        Complex.exp ((w - (d.lowerK j).α - (d.lowerK j).β) * (κ - Real.log (1 + r))))) := by
    intro w
    rw [productWeightTerm_eq, prodCoef_skewP F p K d hN w, hκ]
    have hc : (1 + (r : ℂ)) ^ (d.δ - d.α - w) =
        Complex.exp ((Real.log (1 + r) : ℂ) * (d.δ - d.α - w)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr0.ne'), show (1 + (r : ℂ)) =
        ((1 + r : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log hr0.le]
    rw [hc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hexp : Complex.exp (κ * (d.α + w - d.δ - 1 + 1)) *
        Complex.exp ((Real.log (1 + r) : ℂ) * (d.δ - d.α - w)) =
        E * Complex.exp ((w - (d.lowerK j).α - (d.lowerK j).β) * (κ - Real.log (1 + r))) := by
      rw [hE, hL, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      change _ = _ + (w - d.β - d.γ) * _
      ring
    linear_combination (sc j * iterCoef F K (d.lowerK j) w) * hexp
  change ∑' w, productWeightTerm F (skewP p (tensorObj F Y Z) X T K) d w = _
  rw [tsum_congr hterm, Summable.tsum_finsetSum hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left, tsum_mul_left]
  rfl

end HexagonClose
end VOA.Huang.TensorCat
