import VOA.Huang.FivePointSepOrdinary
import VOA.Huang.BraidingSkewJacobi

/-!
# Coefficient growth of the inner five-point expansion, via skew-symmetry at the root

The inner pentagon vertex `(X ⊠ (Y ⊠ Z)) ⊠ T` is the iterate
`𝒴_out(𝒴_{X,YZ}(x, s+r) 𝒴_{Y,Z}(y, s) z, 1) t`. Skew-symmetry of the ROOT intertwiner
(FHL Prop. 5.4.7, `skewModes`, `Ω₋₁ ∘ Ω₀ = id`) rewrites each coefficient as a FINITE
combination (the `L₋₁`-powers fall on the output functional, which sees a single weight) of
coefficients of the product

  `Ω(𝒴_out)(t, -1) 𝒴_{X,YZ}(x, s+r) 𝒴_{Y,Z}(y, s) z`,

with the SAME two intermediate weights, in the product region `1 > s+r > s`. The product
theory (`ordinaryProduct_geometric`) applies; its rows are the proved four-point product
summability at a chart radius `c₄` with `(1+c₄)(s+r) < 1`.

* `skew_expand` — the root expansion with an explicit finite range;
* `fivePointCoefficientGrowth_inner`.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop VOA.Huang.HuangODEThree VOA.Huang.HuangODEProduct
open VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.BraidingSkew VOA.SkewIntertwiner VOA.Huang.MatrixCoeff
open Filter
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

section Skew
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
  {A₃ : OrdVModule W M₃}

/-- The skew operator used at the root. -/
abbrev rootSkew (A₃ : OrdVModule W M₃) (Y : IntertwiningModes M₁ M₂ M₃) :
    IntertwiningModes M₂ M₁ M₃ :=
  skewModes (Lm1 A₃.toWeakModule) omegaPhase Y

theorem isIntertwiningOperator_rootSkew {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    IsIntertwiningOperator A₂ A₁ A₃ (rootSkew A₃ Y) :=
  isIntertwiningOperator_skewModes hY omegaPhase_succ omegaPhase_ne_zero

/-- **Root skew expansion**: `𝒴₍ₚ₎ w₁ w₂ = c(p)⁻¹ Σ_{j<J} ((-1)ʲ/j!) L₋₁ʲ Ω(𝒴)₍ₚ₊ⱼ₎ w₂ w₁`,
for any `J` beyond which the skew modes vanish. -/
theorem skew_expand {Y : IntertwiningModes M₁ M₂ M₃} (hY : IsIntertwiningOperator A₁ A₂ A₃ Y)
    (p : ℂ) (w₁ : M₁) (w₂ : M₂) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → rootSkew A₃ Y (p + j) w₂ w₁ = 0) :
    Y p w₁ w₂ = (omegaPhase p)⁻¹ • ∑ j ∈ Finset.range J,
      sc j • (Lm1 A₃.toWeakModule ^ j) (rootSkew A₃ Y (p + j) w₂ w₁) := by
  have hT : Trunc Y := trunc_of_isIntertwining hY
  have hinv := skewModes_skewModes (L := Lm1 A₃.toWeakModule) (c := omegaPhase)
    (c' := fun n => (omegaPhase n)⁻¹) omegaPhase_succ
    (fun n => inv_mul_cancel₀ (omegaPhase_ne_zero n)) hT
  have e := congrArg (fun Z : IntertwiningModes M₁ M₂ M₃ => Z p w₁ w₂) hinv
  simp only at e
  rw [← e, skewModes_apply (trunc_skewModes _ _), sSum_eq_sum J hJ]
  rfl

/-- The root skew expansion under a scalar functional. -/
theorem skew_expand_apply {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (f : M₃ →ₗ[ℂ] ℂ)
    (p : ℂ) (w₁ : M₁) (w₂ : M₂) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → rootSkew A₃ Y (p + j) w₂ w₁ = 0) :
    f (Y p w₁ w₂) = ∑ j ∈ Finset.range J, (omegaPhase p)⁻¹ * sc j *
      (f ∘ₗ (Lm1 A₃.toWeakModule ^ j)) (rootSkew A₃ Y (p + j) w₂ w₁) := by
  rw [skew_expand hY p w₁ w₂ J hJ, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, LinearMap.comp_apply]
  ring

end Skew

/-! ## The inner chart factor -/

variable {X Y Z T U : Ordinary W}

theorem fivePointFactor_inner_shift (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    fivePointFactor .inner d (w + m, v + n) =
      fivePointFactor .inner d (w, v) *
        (((d.s : ℂ) ^ m / ((d.s + d.r : ℝ) : ℂ) ^ m) * ((d.s + d.r : ℝ) : ℂ) ^ n) := by
  have hs : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hsr : (0 : ℝ) < d.s + d.r := by linarith [d.positive]
  have hP : ((d.s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hQ : ((d.s + d.r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsr.ne'
  change (d.s : ℂ) ^ ((w + m) - d.β - d.γ) * ((d.s + d.r : ℝ) : ℂ) ^ ((v + n) - d.α - (w + m)) =
    (d.s : ℂ) ^ (w - d.β - d.γ) * ((d.s + d.r : ℝ) : ℂ) ^ (v - d.α - w) * _
  rw [show (w + m) - d.β - d.γ = (w - d.β - d.γ) + (m : ℂ) by ring,
    show (v + n) - d.α - (w + m) = (v - d.α - w) + ((n : ℂ) - m) by ring,
    Complex.cpow_add (w - d.β - d.γ) (m : ℂ) hP, Complex.cpow_add (v - d.α - w) _ hQ,
    Complex.cpow_sub (n : ℂ) (m : ℂ) hQ,
    Complex.cpow_natCast, Complex.cpow_natCast, Complex.cpow_natCast]
  have hQm : ((d.s + d.r : ℝ) : ℂ) ^ m ≠ 0 := pow_ne_zero _ hQ
  field_simp

theorem norm_fivePointFactor_inner (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    ‖fivePointFactor .inner d (w + m, v + n)‖ =
      ‖fivePointFactor .inner d (w, v)‖ * (d.s / (d.s + d.r)) ^ m * (d.s + d.r) ^ n := by
  have hs : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hsr : (0 : ℝ) < d.s + d.r := by linarith [d.positive]
  rw [fivePointFactor_inner_shift, norm_mul, norm_mul, norm_div, norm_pow, norm_pow, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs.le,
    Real.norm_of_nonneg hsr.le, div_pow]
  ring

/-! ## The inner tree -/

variable (F : FusionChoice W)

/-- `L₋₁ʲ` raises weights by `j`. -/
theorem Lm1_pow_mem_weight {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    {β : ℂ} {x : M} (hx : x ∈ A.weight β) (j : ℕ) :
    (Lm1 A.toWeakModule ^ j) x ∈ A.weight (β + j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := mode_mem_weight A W.conformalVector_mem_grading_two ih (0 : ℤ)
    have e : β + (j : ℂ) + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = β + ((j + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [e] at h
    exact h

/-- The functional `f ∘ L₋₁ʲ ∘ π` is supported one weight `j` lower. -/
theorem supportedAt_comp_Lm1 {O U : Ordinary W} (k : O ⟶ U) (f : U.carrier →ₗ[ℂ] ℂ) {ε : ℂ}
    (hf : SupportedAt U.isMod f ε) (j : ℕ) (π : O ⟶ O) :
    SupportedAt O.isMod ((f ∘ₗ k.val ∘ₗ (Lm1 O.isMod.toWeakModule ^ j)) ∘ₗ π.val) (ε - j) := by
  intro α hα x hx
  have h1 := hom_mem_weight π.property hx
  have h2 := Lm1_pow_mem_weight O.isMod h1 j
  have h3 := hom_mem_weight k.property h2
  exact hf (α + j) (fun he => hα (by rw [← he]; ring)) _ h3

/-- The root-skewed intertwiner of the inner tree. -/
abbrev innerΩ (X Y Z T : Ordinary W) :=
  rootSkew (fiveObj F X Y Z T .inner).isMod
    (F (tensorObj F X (tensorObj F Y Z)) T).intertwiner.val

theorem isInnerΩ (X Y Z T : Ordinary W) :
    IsIntertwiningOperator T.isMod (tensorObj F X (tensorObj F Y Z)).isMod
      (fiveObj F X Y Z T .inner).isMod (innerΩ F X Y Z T) :=
  isIntertwiningOperator_rootSkew (F (tensorObj F X (tensorObj F Y Z)) T).intertwiner.property

/-- The inner array as a finite sum of product arrays. -/
theorem fivePointTerm_inner_eq (k : fiveObj F X Y Z T .inner ⟶ U)
    (d : FivePointTest X Y Z T U) (J : ℕ)
    (hJ : ∀ (w v : ℂ) (j : ℕ), J ≤ j → innerΩ F X Y Z T (v + d.δ - d.ε - 1 + j) d.t
      (fiveSecondVector F .inner d w v) = 0) (w v : ℂ) :
    fivePointTerm F .inner k d (w, v) =
      ∑ j ∈ Finset.range J, (omegaPhase (v + d.δ - d.ε - 1))⁻¹ * sc j *
        productCoeff (innerΩ F X Y Z T) (F X (tensorObj F Y Z)).intertwiner.val
          (F Y Z).intertwiner.val
          (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .inner).isMod.toWeakModule ^ j))
          d.t d.x d.y d.z (v + d.δ - d.ε - 1 + j) (d.α + w - v - 1) (d.β + d.γ - w - 1) *
        fivePointFactor .inner d (w, v) := by
  rw [← Finset.sum_mul]
  change d.functional (k.val (fivePointVector F .inner d (w, v))) *
    fivePointFactor .inner d (w, v) = _
  congr 1
  exact skew_expand_apply (F (tensorObj F X (tensorObj F Y Z)) T).intertwiner.property
    (d.functional ∘ₗ k.val) (v + d.δ - d.ε - 1) (fiveSecondVector F .inner d w v) d.t J
    (fun j hj => hJ w v j hj)

/-- A uniform finite range for the root skew expansion: the skew vector lies in weight `ε - j`. -/
theorem exists_inner_range (d : FivePointTest X Y Z T U) :
    ∃ J : ℕ, ∀ (w v : ℂ) (j : ℕ), J ≤ j → innerΩ F X Y Z T (v + d.δ - d.ε - 1 + j) d.t
      (fiveSecondVector F .inner d w v) = 0 := by
  obtain ⟨B, hB⟩ := (fiveObj F X Y Z T .inner).isMod.boundedBelow
  refine ⟨Nat.ceil (d.ε.re - B) + 1, fun w v j hj => ?_⟩
  have hmem := mem_weight (isInnerΩ F X Y Z T) d.ht (fiveSecondVector_mem F .inner d w v)
    (v + d.δ - d.ε - 1 + j)
  have e : d.δ + v - (v + d.δ - d.ε - 1 + j) - 1 = d.ε - j := by ring
  rw [e] at hmem
  by_contra hne
  have hbot : (fiveObj F X Y Z T .inner).isMod.weight (d.ε - j) ≠ ⊥ := fun hb => hne (by
    rw [hb] at hmem; exact (Submodule.mem_bot ℂ).mp hmem)
  have h1 := hB _ hbot
  have h2 : (Nat.ceil (d.ε.re - B) : ℝ) + 1 ≤ j := by exact_mod_cast hj
  have h3 : d.ε.re - B ≤ Nat.ceil (d.ε.re - B) := Nat.le_ceil _
  simp only [Complex.sub_re, Complex.natCast_re] at h1
  linarith

/-- Rows of the root-skewed inner arrays: the proved four-point product summability. -/
theorem inner_rowBound (hs : OrdinaryFourPointSummability F)
    (k : fiveObj F X Y Z T .inner ⟶ U) (d : FivePointTest X Y Z T U) (j : ℕ) (h h' : ℂ)
    (c₄ : ℝ) (hc₀ : 0 < c₄) (hc₁ : c₄ < 1) :
    OrdinaryRowBound ⟨innerΩ F X Y Z T, isInnerΩ F X Y Z T⟩
      (F X (tensorObj F Y Z)).intertwiner (F Y Z).intertwiner
      (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .inner).isMod.toWeakModule ^ j))
      d.t d.x d.y d.z (h' + d.δ - d.ε - 1 + j) (d.α + h - h' - 1) (d.β + d.γ - h - 1)
      (1 + c₄) := by
  intro πo πa πb πc πd k₀ j₀
  let O := fiveObj F X Y Z T .inner
  let g := d.functional ∘ₗ k.val ∘ₗ (Lm1 O.isMod.toWeakModule ^ j)
  have hz : (F Y Z).intertwiner.val (d.β + d.γ - h - 1 - j₀) (πc.val d.y) (πd.val d.z) ∈
      (tensorObj F Y Z).isMod.weight (h + j₀) := by
    have := mem_weight (F Y Z).intertwiner.property (hom_mem_weight πc.property d.hy)
      (hom_mem_weight πd.property d.hz) (d.β + d.γ - h - 1 - j₀)
    convert this using 2; ring
  let d₄ : FourPointTest T X (tensorObj F Y Z) O :=
    { α := d.δ, β := d.α, γ := h + j₀, δ := d.ε - j
      x := πa.val d.t, y := πb.val d.x
      z := (F Y Z).intertwiner.val (d.β + d.γ - h - 1 - j₀) (πc.val d.y) (πd.val d.z)
      functional := g ∘ₗ πo.val
      hx := hom_mem_weight πa.property d.ht
      hy := hom_mem_weight πb.property d.hx
      hz := hz
      supported := supportedAt_comp_Lm1 k d.functional d.supported j πo
      coordinate := c₄, positive := hc₀, less_one := hc₁ }
  have hsum := (hs T X (tensorObj F Y Z) O d₄).2 ⟨innerΩ F X Y Z T, isInnerΩ F X Y Z T⟩
  have hinj : Function.Injective (fun m : ℕ => (h' - k₀) + (m : ℂ)) := by
    intro a b hab
    have : (a : ℂ) = b := by simpa using hab
    exact_mod_cast this
  obtain ⟨K, hK⟩ := ((hsum.comp_injective hinj).tendsto_atTop_zero.norm).bddAbove_range
  have hc : (0 : ℝ) < 1 + c₄ := by linarith
  set z₀ : ℂ := d.ε - j - d.δ - (h' - k₀) with hz₀
  have hBpos : 0 < ‖((1 + c₄ : ℝ) : ℂ) ^ z₀‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hc]; positivity
  refine ⟨K / ‖((1 + c₄ : ℝ) : ℂ) ^ z₀‖, fun mm => ?_⟩
  have hm := hK ⟨mm, rfl⟩
  simp only [Function.comp_apply, productWeightTerm] at hm
  have hpow : (1 + (c₄ : ℂ)) ^ (d.ε - j - d.δ - (h' - k₀ + mm)) =
      ((1 + c₄ : ℝ) : ℂ) ^ z₀ / ((1 + c₄ : ℝ) : ℂ) ^ mm := by
    have hne : ((1 + c₄ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [show (1 + (c₄ : ℂ)) = ((1 + c₄ : ℝ) : ℂ) by push_cast; ring,
      show d.ε - j - d.δ - (h' - k₀ + mm) = z₀ - (mm : ℂ) by rw [hz₀]; ring,
      Complex.cpow_sub _ _ hne, Complex.cpow_natCast]
  have hcoef : (g ∘ₗ πo.val) (innerΩ F X Y Z T (d.δ + (h' - k₀ + mm) - (d.ε - j) - 1)
      (πa.val d.t) ((F X (tensorObj F Y Z)).intertwiner.val (d.α + (h + j₀) - (h' - k₀ + mm) - 1)
        (πb.val d.x) ((F Y Z).intertwiner.val (d.β + d.γ - h - 1 - j₀) (πc.val d.y)
          (πd.val d.z)))) =
      productCoeff (innerΩ F X Y Z T) (F X (tensorObj F Y Z)).intertwiner.val
        (F Y Z).intertwiner.val (g ∘ₗ πo.val) (πa.val d.t) (πb.val d.x) (πc.val d.y)
        (πd.val d.z) (h' + d.δ - d.ε - 1 + j - k₀ + mm) (d.α + h - h' - 1 + k₀ - mm + j₀)
        (d.β + d.γ - h - 1 - j₀) := by
    unfold productCoeff
    exact prod3_congr _ _ _ _ _ (by ring) (by ring) rfl
  change ‖(g ∘ₗ πo.val) (innerΩ F X Y Z T (d.δ + (h' - k₀ + mm) - (d.ε - j) - 1)
      (πa.val d.t) ((F X (tensorObj F Y Z)).intertwiner.val (d.α + (h + j₀) - (h' - k₀ + mm) - 1)
        (πb.val d.x) ((F Y Z).intertwiner.val (d.β + d.γ - h - 1 - j₀) (πc.val d.y)
          (πd.val d.z)))) * (1 + (c₄ : ℂ)) ^ (d.ε - j - d.δ - (h' - k₀ + mm))‖ ≤ K at hm
  rw [hcoef, hpow, norm_mul, norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hc.le] at hm
  rw [show K / ‖((1 + c₄ : ℝ) : ℂ) ^ z₀‖ * (1 + c₄) ^ mm =
      K / (‖((1 + c₄ : ℝ) : ℂ) ^ z₀‖ / (1 + c₄) ^ mm) by field_simp,
    le_div_iff₀ (by positivity)]
  exact hm

theorem norm_inv_omegaPhase_add_nat (p : ℂ) (n : ℕ) :
    ‖(omegaPhase (p + n))⁻¹‖ = ‖(omegaPhase p)⁻¹‖ := by
  rw [phase_nat omegaPhase_succ p n, mul_inv, norm_mul, norm_inv, norm_pow, norm_neg,
    norm_one, one_pow, inv_one, one_mul]

/-- **Coefficient growth of the inner five-point expansion**, for a strongly rational
VOA (given finiteness of the irreducibles and the proved four-point summability). -/
theorem fivePointCoefficientGrowth_inner (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) (k : fiveObj F X Y Z T .inner ⟶ U)
    (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    LocalJointGrowth (fun m n => fivePointTerm F .inner k d (h + m, h' + n)) := by
  obtain ⟨J, hJ⟩ := exists_inner_range F d
  have hs0 : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hsr : (0 : ℝ) < d.s + d.r := by linarith [d.positive]
  have hsr1 : d.s + d.r < 1 := d.sum_lt
  -- the row radius
  set c₄ : ℝ := min (1 / 2) ((1 / (d.s + d.r) - 1) / 2) with hc₄
  have hinv : 1 < 1 / (d.s + d.r) := by rw [lt_div_iff₀ hsr]; linarith
  have hc₀ : 0 < c₄ := lt_min (by norm_num) (by linarith)
  have hc₁ : c₄ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hc₂ : (1 + c₄) * (d.s + d.r) < 1 := by
    have : c₄ ≤ (1 / (d.s + d.r) - 1) / 2 := min_le_right _ _
    have e : (1 / (d.s + d.r)) * (d.s + d.r) = 1 := by field_simp
    nlinarith
  set ρ₂ : ℝ := (1 + (d.s + d.r) / d.s) / 2 with hρ₂
  have hq : 1 < (d.s + d.r) / d.s := by rw [lt_div_iff₀ hs0]; linarith [d.positive]
  have hρ₂1 : 1 < ρ₂ := by rw [hρ₂]; linarith
  have hρ₂s : ρ₂ * (d.s / (d.s + d.r)) < 1 := by
    have hlt : ρ₂ < (d.s + d.r) / d.s := by rw [hρ₂]; linarith
    calc ρ₂ * (d.s / (d.s + d.r)) < (d.s + d.r) / d.s * (d.s / (d.s + d.r)) :=
          mul_lt_mul_of_pos_right hlt (by positivity)
      _ = 1 := by field_simp
  refine LocalJointGrowth.congr (LocalJointGrowth.sum (Finset.range J) (fun j _ => ?_))
    (fun m n => fivePointTerm_inner_eq F k d J hJ (h + m) (h' + n))
  -- one root-skew summand
  obtain ⟨K, hK⟩ := ordinaryProduct_geometric hV hΦ ⟨innerΩ F X Y Z T, isInnerΩ F X Y Z T⟩
    (F X (tensorObj F Y Z)).intertwiner (F Y Z).intertwiner
    (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .inner).isMod.toWeakModule ^ j))
    d.ht d.hx d.hy d.hz (h' + d.δ - d.ε - 1 + j) (d.α + h - h' - 1) (d.β + d.γ - h - 1)
    (by linarith : (1 : ℝ) < 1 + c₄) hρ₂1 (inner_rowBound F hs k d j h h' c₄ hc₀ hc₁)
  set P := ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ * ‖sc j‖
  set B := ‖fivePointFactor .inner d (h, h')‖
  refine localJointGrowth_of_geometric (K := P * K * B) (a := ρ₂ * (d.s / (d.s + d.r)))
    (b := (1 + c₄) * (d.s + d.r)) (by positivity) hρ₂s (by positivity) hc₂ fun m n => ?_
  have e1 : h' + n + d.δ - d.ε - 1 = (h' + d.δ - d.ε - 1) + n := by ring
  have e2 : productCoeff (innerΩ F X Y Z T) (F X (tensorObj F Y Z)).intertwiner.val
      (F Y Z).intertwiner.val
      (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .inner).isMod.toWeakModule ^ j))
      d.t d.x d.y d.z (h' + d.δ - d.ε - 1 + n + j) (d.α + (h + m) - (h' + n) - 1)
      (d.β + d.γ - (h + m) - 1) =
    productCoeff (innerΩ F X Y Z T) (F X (tensorObj F Y Z)).intertwiner.val
      (F Y Z).intertwiner.val
      (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .inner).isMod.toWeakModule ^ j))
      d.t d.x d.y d.z (h' + d.δ - d.ε - 1 + j + n) (d.α + h - h' - 1 - n + m)
      (d.β + d.γ - h - 1 - m) := by
    unfold productCoeff
    exact prod3_congr _ _ _ _ _ (by ring) (by ring) (by ring)
  rw [e1, e2, norm_mul, norm_mul, norm_mul, norm_inv_omegaPhase_add_nat,
    norm_fivePointFactor_inner]
  have h1 := hK n m
  have hP0 : 0 ≤ ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ := norm_nonneg _
  have hsc : 0 ≤ ‖sc j‖ := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hx : 0 ≤ (d.s / (d.s + d.r)) ^ m := by positivity
  have hy : 0 ≤ (d.s + d.r) ^ n := by positivity
  calc ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ * ‖sc j‖ * ‖_‖ *
        (B * (d.s / (d.s + d.r)) ^ m * (d.s + d.r) ^ n)
      ≤ ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ * ‖sc j‖ * (K * (1 + c₄) ^ n * ρ₂ ^ m) *
        (B * (d.s / (d.s + d.r)) ^ m * (d.s + d.r) ^ n) := by gcongr
    _ = P * K * B * (ρ₂ * (d.s / (d.s + d.r))) ^ m * ((1 + c₄) * (d.s + d.r)) ^ n := by
        rw [mul_pow, mul_pow]; ring

end VOA.Huang.FivePointSep
