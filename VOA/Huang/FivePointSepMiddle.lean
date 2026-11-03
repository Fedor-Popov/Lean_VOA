import VOA.Huang.FivePointSepMid
import VOA.Huang.FivePointSepInner

/-!
# Coefficient growth of the middle and left five-point expansions

* the middle vertex `X ⊠ ((Y ⊠ Z) ⊠ T)` is directly of the middle shape
  `f(𝒴_X(x) 𝒴_{YZ,T}(𝒴_{Y,Z}(y)z) t)`; chart `x = 1/(1+s+r)`, `y = s`;
  rows: the proved five-point slices at the radius `r/2`;
* the left vertex `((X ⊠ Y) ⊠ Z) ⊠ T`, after skew-symmetry at the root, is a finite
  combination of middle-shape arrays `Ω(t, -1) 𝒴_{XY,Z}(𝒴_{X,Y}(x, r) y, s) z`;
  chart `x = -s`, `y = r/s`; rows: four-point product summability.

`fivePointCoefficientGrowth_middle`, `fivePointCoefficientGrowth_left`.
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
variable {X Y Z T U : Ordinary W}

/-! ## The middle chart factor -/

theorem fivePointFactor_middle_shift (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    fivePointFactor .middle d (w + m, v + n) =
      fivePointFactor .middle d (w, v) *
        ((d.s : ℂ) ^ m * (1 / ((1 + d.s + d.r : ℝ) : ℂ) ^ n)) := by
  have hs : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith [d.positive]
  have hP : ((d.s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hQ : ((1 + d.s + d.r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsr.ne'
  change (d.s : ℂ) ^ ((w + m) - d.β - d.γ) * ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - (v + n)) =
    (d.s : ℂ) ^ (w - d.β - d.γ) * ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - v) * _
  rw [show (w + m) - d.β - d.γ = (w - d.β - d.γ) + (m : ℂ) by ring,
    show d.ε - d.α - (v + n) = (d.ε - d.α - v) - (n : ℂ) by ring,
    Complex.cpow_add (w - d.β - d.γ) (m : ℂ) hP, Complex.cpow_sub (d.ε - d.α - v) (n : ℂ) hQ,
    Complex.cpow_natCast, Complex.cpow_natCast]
  have hQn : ((1 + d.s + d.r : ℝ) : ℂ) ^ n ≠ 0 := pow_ne_zero _ hQ
  field_simp

theorem norm_fivePointFactor_middle (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    ‖fivePointFactor .middle d (w + m, v + n)‖ =
      ‖fivePointFactor .middle d (w, v)‖ * d.s ^ m * (1 / (1 + d.s + d.r)) ^ n := by
  have hs : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith [d.positive]
  rw [fivePointFactor_middle_shift]
  simp only [norm_mul, norm_div, norm_pow, norm_one, Complex.norm_real,
    Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hsr.le, one_div_pow]
  ring

theorem norm_fivePointFactor_middle_row (d : FivePointTest X Y Z T U) (w v : ℂ) (n : ℕ) :
    ‖fivePointFactor .middle d (w, v + n)‖ =
      ‖fivePointFactor .middle d (w, v)‖ * (1 / (1 + d.s + d.r)) ^ n := by
  have h := norm_fivePointFactor_middle d w v 0 n
  simp only [Nat.cast_zero, add_zero, pow_zero, mul_one] at h
  exact h

theorem norm_fivePointFactor_middle_pos (d : FivePointTest X Y Z T U) (w v : ℂ) :
    0 < ‖fivePointFactor .middle d (w, v)‖ := by
  have hs : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith [d.positive]
  change 0 < ‖(d.s : ℂ) ^ (w - d.β - d.γ) * ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - v)‖
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hs,
    Complex.norm_cpow_eq_rpow_re_of_pos hsr]
  positivity

variable (F : FusionChoice W)

/-- The middle-tree term in middle-shape form (definitional). -/
theorem fivePointTerm_middle_def (k : fiveObj F X Y Z T .middle ⟶ U)
    (d : FivePointTest X Y Z T U) (w v : ℂ) :
    fivePointTerm F .middle k d (w, v) =
      productCoeff (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner.val
        (swap2 (F (tensorObj F Y Z) T).intertwiner.val) (F Y Z).intertwiner.val
        (d.functional ∘ₗ k.val) d.x d.t d.y d.z (d.α + v - d.ε - 1) (w + d.δ - v - 1)
        (d.β + d.γ - w - 1) * fivePointFactor .middle d (w, v) := rfl

/-- Rows of the middle arrays from the proved five-point slices at radius `r/2`. -/
theorem middle_rowBound (hs : OrdinaryFourPointSummability F)
    (k : fiveObj F X Y Z T .middle ⟶ U) (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    OrdinaryMidRowBound (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner
      (F (tensorObj F Y Z) T).intertwiner (F Y Z).intertwiner (d.functional ∘ₗ k.val)
      d.x d.t d.y d.z (d.α + h' - d.ε - 1) (h + d.δ - h' - 1) (d.β + d.γ - h - 1)
      (1 + d.s + d.r / 2) := by
  intro πo πa πb πc πd k₀ j₀
  have hr0 : 0 < d.r / 2 := by linarith [d.positive]
  have hr1 : d.r / 2 ≤ d.r := by linarith [d.positive]
  set d' := testWithR (testWithVectors d (πa.val d.x) (πc.val d.y) (πd.val d.z) (πb.val d.t)
    (hom_mem_weight πa.property d.hx) (hom_mem_weight πc.property d.hy)
    (hom_mem_weight πd.property d.hz) (hom_mem_weight πb.property d.ht)) (d.r / 2) hr0 hr1
    with hd'
  have hsl := fivePoint_slice_summable F hs .middle (πo ≫ k) d' (h + j₀)
  have hinj : Function.Injective (fun m : ℕ => (h' - k₀) + (m : ℂ)) := by
    intro a b hab
    have : (a : ℂ) = b := by simpa using hab
    exact_mod_cast this
  obtain ⟨K, hK⟩ := ((hsl.comp_injective hinj).tendsto_atTop_zero.norm).bddAbove_range
  have hsr : (0 : ℝ) < 1 + d.s + d.r / 2 := by linarith [d.positive, d.smaller]
  set B := ‖fivePointFactor .middle d' (h + j₀, h' - k₀)‖ with hB
  have hBpos : 0 < B := norm_fivePointFactor_middle_pos _ _ _
  refine ⟨K / B, fun mm => ?_⟩
  have hm : ‖fivePointTerm F .middle (πo ≫ k) d' (h + j₀, (h' - k₀) + mm)‖ ≤ K := hK ⟨mm, rfl⟩
  rw [fivePointTerm_middle_def, norm_mul] at hm
  rw [norm_fivePointFactor_middle_row] at hm
  change ‖_‖ * (B * (1 / (1 + d'.s + d'.r)) ^ mm) ≤ K at hm
  have e : productCoeff (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner.val
      (swap2 (F (tensorObj F Y Z) T).intertwiner.val) (F Y Z).intertwiner.val
      (d'.functional ∘ₗ (πo ≫ k).val) d'.x d'.t d'.y d'.z (d'.α + (h' - k₀ + mm) - d'.ε - 1)
      (h + j₀ + d'.δ - (h' - k₀ + mm) - 1) (d'.β + d'.γ - (h + j₀) - 1) =
    productCoeff (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner.val
      (swap2 (F (tensorObj F Y Z) T).intertwiner.val) (F Y Z).intertwiner.val
      ((d.functional ∘ₗ k.val) ∘ₗ πo.val) (πa.val d.x) (πb.val d.t) (πc.val d.y) (πd.val d.z)
      (d.α + h' - d.ε - 1 - k₀ + mm) (h + d.δ - h' - 1 + k₀ - mm + j₀)
      (d.β + d.γ - h - 1 - j₀) := by
    have hα : d'.α = d.α := rfl
    have hβ : d'.β = d.β := rfl
    have hγ : d'.γ = d.γ := rfl
    have hδ : d'.δ = d.δ := rfl
    have hε : d'.ε = d.ε := rfl
    unfold productCoeff
    rw [hα, hβ, hγ, hδ, hε]
    exact mid3_congr _ _ _ _ _ (by ring) (by ring) (by ring)
  rw [e] at hm
  have hd's : d'.s = d.s := rfl
  have hd'r : d'.r = d.r / 2 := rfl
  rw [hd's, hd'r] at hm
  rw [show K / B * (1 + d.s + d.r / 2) ^ mm = K / (B * (1 / (1 + d.s + d.r / 2)) ^ mm) by
    rw [one_div_pow, mul_one_div, div_div_eq_mul_div]; ring, le_div_iff₀ (by positivity)]
  exact hm

/-- **Coefficient growth of the middle five-point expansion.** -/
theorem fivePointCoefficientGrowth_middle (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) (k : fiveObj F X Y Z T .middle ⟶ U)
    (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    LocalJointGrowth (fun m n => fivePointTerm F .middle k d (h + m, h' + n)) := by
  have hs0 : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hr0 : (0 : ℝ) < d.r := d.positive
  have hsr1 : d.s + d.r < 1 := d.sum_lt
  set ρ₁ : ℝ := 1 + d.s + d.r / 2 with hρ₁
  set ρ₂ : ℝ := 1 / (d.s + d.r / 4) with hρ₂
  have hq0 : 0 < d.s + d.r / 4 := by positivity
  have hρ₂1 : 1 < ρ₂ := by rw [hρ₂, lt_div_iff₀ hq0]; linarith
  have hρ : 1 + 1 / ρ₂ < ρ₁ := by rw [hρ₂, one_div_one_div, hρ₁]; linarith
  obtain ⟨K, hK⟩ := ordinaryMid_geometric hV hΦ (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner
    (F (tensorObj F Y Z) T).intertwiner (F Y Z).intertwiner (d.functional ∘ₗ k.val)
    d.hx d.ht d.hy d.hz (d.α + h' - d.ε - 1) (h + d.δ - h' - 1) (d.β + d.γ - h - 1)
    hρ₂1 hρ (middle_rowBound F hs k d h h')
  set B := ‖fivePointFactor .middle d (h, h')‖
  have hsr : (0 : ℝ) < 1 + d.s + d.r := by linarith
  refine localJointGrowth_of_geometric (K := K * B) (a := ρ₂ * d.s)
    (b := ρ₁ * (1 / (1 + d.s + d.r))) (by positivity) ?_ (by positivity) ?_ fun m n => ?_
  · rw [hρ₂, one_div_mul_eq_div, div_lt_one hq0]; linarith
  · rw [hρ₁, mul_one_div, div_lt_one hsr]; linarith
  · rw [fivePointTerm_middle_def, norm_mul, norm_fivePointFactor_middle]
    have e : productCoeff (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner.val
        (swap2 (F (tensorObj F Y Z) T).intertwiner.val) (F Y Z).intertwiner.val
        (d.functional ∘ₗ k.val) d.x d.t d.y d.z (d.α + (h' + n) - d.ε - 1)
        (h + m + d.δ - (h' + n) - 1) (d.β + d.γ - (h + m) - 1) =
      productCoeff (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner.val
        (swap2 (F (tensorObj F Y Z) T).intertwiner.val) (F Y Z).intertwiner.val
        (d.functional ∘ₗ k.val) d.x d.t d.y d.z (d.α + h' - d.ε - 1 + n)
        (h + d.δ - h' - 1 - n + m) (d.β + d.γ - h - 1 - m) := by
      unfold productCoeff
      exact mid3_congr _ _ _ _ _ (by ring) (by ring) (by ring)
    rw [e]
    have h1 := hK n m
    have hB0 : 0 ≤ B := norm_nonneg _
    have hx : 0 ≤ (1 / (1 + d.s + d.r)) ^ n := by positivity
    have hy : 0 ≤ d.s ^ m := by positivity
    calc _ ≤ (K * ρ₁ ^ n * ρ₂ ^ m) * (B * d.s ^ m * (1 / (1 + d.s + d.r)) ^ n) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K * B * (ρ₂ * d.s) ^ m * (ρ₁ * (1 / (1 + d.s + d.r))) ^ n := by
          rw [mul_pow, mul_pow]; ring

/-! ## The left vertex, via skew-symmetry at the root -/

theorem fivePointFactor_left_shift (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    fivePointFactor .left d (w + m, v + n) =
      fivePointFactor .left d (w, v) *
        (((d.r : ℂ) ^ m / (d.s : ℂ) ^ m) * (d.s : ℂ) ^ n) := by
  have hs : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hr : (0 : ℝ) < d.r := d.positive
  have hP : ((d.r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hQ : ((d.s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  change (d.r : ℂ) ^ ((w + m) - d.α - d.β) * (d.s : ℂ) ^ ((v + n) - (w + m) - d.γ) =
    (d.r : ℂ) ^ (w - d.α - d.β) * (d.s : ℂ) ^ (v - w - d.γ) * _
  rw [show (w + m) - d.α - d.β = (w - d.α - d.β) + (m : ℂ) by ring,
    show (v + n) - (w + m) - d.γ = (v - w - d.γ) + ((n : ℂ) - m) by ring,
    Complex.cpow_add (w - d.α - d.β) (m : ℂ) hP, Complex.cpow_add (v - w - d.γ) _ hQ,
    Complex.cpow_sub (n : ℂ) (m : ℂ) hQ,
    Complex.cpow_natCast, Complex.cpow_natCast, Complex.cpow_natCast]
  have hQm : ((d.s : ℝ) : ℂ) ^ m ≠ 0 := pow_ne_zero _ hQ
  field_simp

theorem norm_fivePointFactor_left (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    ‖fivePointFactor .left d (w + m, v + n)‖ =
      ‖fivePointFactor .left d (w, v)‖ * (d.r / d.s) ^ m * d.s ^ n := by
  have hs : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hr : (0 : ℝ) < d.r := d.positive
  rw [fivePointFactor_left_shift]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le,
    Real.norm_of_nonneg hr.le, div_pow]
  ring

/-- The root-skewed intertwiner of the left tree. -/
abbrev leftΩ (X Y Z T : Ordinary W) :=
  rootSkew (fiveObj F X Y Z T .left).isMod
    (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner.val

theorem isLeftΩ (X Y Z T : Ordinary W) :
    IsIntertwiningOperator T.isMod (tensorObj F (tensorObj F X Y) Z).isMod
      (fiveObj F X Y Z T .left).isMod (leftΩ F X Y Z T) :=
  isIntertwiningOperator_rootSkew (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner.property

/-- The left array as a finite sum of middle-shape arrays. -/
theorem fivePointTerm_left_eq (k : fiveObj F X Y Z T .left ⟶ U)
    (d : FivePointTest X Y Z T U) (J : ℕ)
    (hJ : ∀ (w v : ℂ) (j : ℕ), J ≤ j → leftΩ F X Y Z T (v + d.δ - d.ε - 1 + j) d.t
      (fiveSecondVector F .left d w v) = 0) (w v : ℂ) :
    fivePointTerm F .left k d (w, v) =
      ∑ j ∈ Finset.range J, (omegaPhase (v + d.δ - d.ε - 1))⁻¹ * sc j *
        productCoeff (leftΩ F X Y Z T) (swap2 (F (tensorObj F X Y) Z).intertwiner.val)
          (F X Y).intertwiner.val
          (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .left).isMod.toWeakModule ^ j))
          d.t d.z d.x d.y (v + d.δ - d.ε - 1 + j) (w + d.γ - v - 1) (d.α + d.β - w - 1) *
        fivePointFactor .left d (w, v) := by
  rw [← Finset.sum_mul]
  change d.functional (k.val (fivePointVector F .left d (w, v))) *
    fivePointFactor .left d (w, v) = _
  congr 1
  exact skew_expand_apply (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner.property
    (d.functional ∘ₗ k.val) (v + d.δ - d.ε - 1) (fiveSecondVector F .left d w v) d.t J
    (fun j hj => hJ w v j hj)

theorem exists_left_range (d : FivePointTest X Y Z T U) :
    ∃ J : ℕ, ∀ (w v : ℂ) (j : ℕ), J ≤ j → leftΩ F X Y Z T (v + d.δ - d.ε - 1 + j) d.t
      (fiveSecondVector F .left d w v) = 0 := by
  obtain ⟨B, hB⟩ := (fiveObj F X Y Z T .left).isMod.boundedBelow
  refine ⟨Nat.ceil (d.ε.re - B) + 1, fun w v j hj => ?_⟩
  have hmem := mem_weight (isLeftΩ F X Y Z T) d.ht (fiveSecondVector_mem F .left d w v)
    (v + d.δ - d.ε - 1 + j)
  have e : d.δ + v - (v + d.δ - d.ε - 1 + j) - 1 = d.ε - j := by ring
  rw [e] at hmem
  by_contra hne
  have hbot : (fiveObj F X Y Z T .left).isMod.weight (d.ε - j) ≠ ⊥ := fun hb => hne (by
    rw [hb] at hmem; exact (Submodule.mem_bot ℂ).mp hmem)
  have h1 := hB _ hbot
  have h2 : (Nat.ceil (d.ε.re - B) : ℝ) + 1 ≤ j := by exact_mod_cast hj
  have h3 : d.ε.re - B ≤ Nat.ceil (d.ε.re - B) := Nat.le_ceil _
  simp only [Complex.sub_re, Complex.natCast_re] at h1
  linarith

/-- Rows of the root-skewed left arrays: four-point product summability. -/
theorem left_rowBound (hs : OrdinaryFourPointSummability F)
    (k : fiveObj F X Y Z T .left ⟶ U) (d : FivePointTest X Y Z T U) (j : ℕ) (h h' : ℂ)
    (c₄ : ℝ) (hc₀ : 0 < c₄) (hc₁ : c₄ < 1) :
    OrdinaryMidRowBound ⟨leftΩ F X Y Z T, isLeftΩ F X Y Z T⟩
      (F (tensorObj F X Y) Z).intertwiner (F X Y).intertwiner
      (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .left).isMod.toWeakModule ^ j))
      d.t d.z d.x d.y (h' + d.δ - d.ε - 1 + j) (h + d.γ - h' - 1) (d.α + d.β - h - 1)
      (1 + c₄) := by
  intro πo πa πb πc πd k₀ j₀
  let O := fiveObj F X Y Z T .left
  let g := d.functional ∘ₗ k.val ∘ₗ (Lm1 O.isMod.toWeakModule ^ j)
  have hU : (F X Y).intertwiner.val (d.α + d.β - h - 1 - j₀) (πc.val d.x) (πd.val d.y) ∈
      (tensorObj F X Y).isMod.weight (h + j₀) := by
    have := mem_weight (F X Y).intertwiner.property (hom_mem_weight πc.property d.hx)
      (hom_mem_weight πd.property d.hy) (d.α + d.β - h - 1 - j₀)
    convert this using 2; ring
  let d₄ : FourPointTest T (tensorObj F X Y) Z O :=
    { α := d.δ, β := h + j₀, γ := d.γ, δ := d.ε - j
      x := πa.val d.t
      y := (F X Y).intertwiner.val (d.α + d.β - h - 1 - j₀) (πc.val d.x) (πd.val d.y)
      z := πb.val d.z
      functional := g ∘ₗ πo.val
      hx := hom_mem_weight πa.property d.ht
      hy := hU
      hz := hom_mem_weight πb.property d.hz
      supported := supportedAt_comp_Lm1 k d.functional d.supported j πo
      coordinate := c₄, positive := hc₀, less_one := hc₁ }
  have hsum := (hs T (tensorObj F X Y) Z O d₄).2 ⟨leftΩ F X Y Z T, isLeftΩ F X Y Z T⟩
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
  have hcoef : (g ∘ₗ πo.val) (leftΩ F X Y Z T (d.δ + (h' - k₀ + mm) - (d.ε - j) - 1)
      (πa.val d.t) ((F (tensorObj F X Y) Z).intertwiner.val (h + j₀ + d.γ - (h' - k₀ + mm) - 1)
        ((F X Y).intertwiner.val (d.α + d.β - h - 1 - j₀) (πc.val d.x) (πd.val d.y))
          (πb.val d.z))) =
      productCoeff (leftΩ F X Y Z T) (swap2 (F (tensorObj F X Y) Z).intertwiner.val)
        (F X Y).intertwiner.val (g ∘ₗ πo.val) (πa.val d.t) (πb.val d.z) (πc.val d.x)
        (πd.val d.y) (h' + d.δ - d.ε - 1 + j - k₀ + mm) (h + d.γ - h' - 1 + k₀ - mm + j₀)
        (d.α + d.β - h - 1 - j₀) := by
    unfold productCoeff
    exact mid3_congr _ _ _ _ _ (by ring) (by ring) rfl
  change ‖(g ∘ₗ πo.val) (leftΩ F X Y Z T (d.δ + (h' - k₀ + mm) - (d.ε - j) - 1)
      (πa.val d.t) ((F (tensorObj F X Y) Z).intertwiner.val (h + j₀ + d.γ - (h' - k₀ + mm) - 1)
        ((F X Y).intertwiner.val (d.α + d.β - h - 1 - j₀) (πc.val d.x) (πd.val d.y))
          (πb.val d.z))) * (1 + (c₄ : ℂ)) ^ (d.ε - j - d.δ - (h' - k₀ + mm))‖ ≤ K at hm
  rw [hcoef, hpow, norm_mul, norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hc.le] at hm
  rw [show K / ‖((1 + c₄ : ℝ) : ℂ) ^ z₀‖ * (1 + c₄) ^ mm =
      K / (‖((1 + c₄ : ℝ) : ℂ) ^ z₀‖ / (1 + c₄) ^ mm) by field_simp,
    le_div_iff₀ (by positivity)]
  exact hm

/-- **Coefficient growth of the left five-point expansion.** -/
theorem fivePointCoefficientGrowth_left (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) (k : fiveObj F X Y Z T .left ⟶ U)
    (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    LocalJointGrowth (fun m n => fivePointTerm F .left k d (h + m, h' + n)) := by
  obtain ⟨J, hJ⟩ := exists_left_range F d
  have hs0 : (0 : ℝ) < d.s := lt_trans d.positive d.smaller
  have hr0 : (0 : ℝ) < d.r := d.positive
  have hrs : d.r < d.s := d.smaller
  have hsr1 : d.s + d.r < 1 := d.sum_lt
  -- the rates
  set t : ℝ := d.r / d.s with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hs0]; exact hrs
  have hts : t < 1 / d.s - 1 := by
    rw [ht, lt_sub_iff_add_lt, div_add_one hs0.ne', div_lt_div_iff_of_pos_right hs0]; linarith
  set c₄ : ℝ := (t + min 1 (1 / d.s - 1)) / 2 with hc₄
  have hmin : t < min 1 (1 / d.s - 1) := lt_min ht1 hts
  have hc₀ : 0 < c₄ := by rw [hc₄]; linarith
  have hct : t < c₄ := by rw [hc₄]; linarith
  have hcm : c₄ < min 1 (1 / d.s - 1) := by rw [hc₄]; linarith
  have hc₁ : c₄ < 1 := lt_of_lt_of_le hcm (min_le_left _ _)
  have hc₂ : (1 + c₄) * d.s < 1 := by
    have h1 : c₄ < 1 / d.s - 1 := lt_of_lt_of_le hcm (min_le_right _ _)
    have h2 : (1 / d.s) * d.s = 1 := by field_simp
    nlinarith
  set ρ₂ : ℝ := (1 / c₄ + 1 / t) / 2 with hρ₂
  have hinv : 1 / c₄ < 1 / t := one_div_lt_one_div_of_lt ht0 hct
  have hρ₂a : 1 / c₄ < ρ₂ := by rw [hρ₂]; linarith
  have hρ₂b : ρ₂ < 1 / t := by rw [hρ₂]; linarith
  have hc1 : 1 < 1 / c₄ := by rw [lt_div_iff₀ hc₀]; linarith
  have hρ₂1 : 1 < ρ₂ := by linarith
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hρ : 1 + 1 / ρ₂ < 1 + c₄ := by
    have : 1 / ρ₂ < c₄ := by
      rw [div_lt_iff₀ hρ₂0]
      rw [div_lt_iff₀ hc₀] at hρ₂a
      linarith
    linarith
  have hρ₂t : ρ₂ * t < 1 := by
    have := (lt_div_iff₀ ht0).mp hρ₂b
    linarith
  refine LocalJointGrowth.congr (LocalJointGrowth.sum (Finset.range J) (fun j _ => ?_))
    (fun m n => fivePointTerm_left_eq F k d J hJ (h + m) (h' + n))
  obtain ⟨K, hK⟩ := ordinaryMid_geometric hV hΦ ⟨leftΩ F X Y Z T, isLeftΩ F X Y Z T⟩
    (F (tensorObj F X Y) Z).intertwiner (F X Y).intertwiner
    (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .left).isMod.toWeakModule ^ j))
    d.ht d.hz d.hx d.hy (h' + d.δ - d.ε - 1 + j) (h + d.γ - h' - 1) (d.α + d.β - h - 1)
    hρ₂1 hρ (left_rowBound F hs k d j h h' c₄ hc₀ hc₁)
  set P := ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ * ‖sc j‖
  set B := ‖fivePointFactor .left d (h, h')‖
  refine localJointGrowth_of_geometric (K := P * K * B) (a := ρ₂ * t)
    (b := (1 + c₄) * d.s) (by positivity) hρ₂t (by positivity) hc₂ fun m n => ?_
  have e1 : h' + n + d.δ - d.ε - 1 = (h' + d.δ - d.ε - 1) + n := by ring
  have e2 : productCoeff (leftΩ F X Y Z T) (swap2 (F (tensorObj F X Y) Z).intertwiner.val)
      (F X Y).intertwiner.val
      (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .left).isMod.toWeakModule ^ j))
      d.t d.z d.x d.y (h' + d.δ - d.ε - 1 + n + j) (h + m + d.γ - (h' + n) - 1)
      (d.α + d.β - (h + m) - 1) =
    productCoeff (leftΩ F X Y Z T) (swap2 (F (tensorObj F X Y) Z).intertwiner.val)
      (F X Y).intertwiner.val
      (d.functional ∘ₗ k.val ∘ₗ (Lm1 (fiveObj F X Y Z T .left).isMod.toWeakModule ^ j))
      d.t d.z d.x d.y (h' + d.δ - d.ε - 1 + j + n) (h + d.γ - h' - 1 - n + m)
      (d.α + d.β - h - 1 - m) := by
    unfold productCoeff
    exact mid3_congr _ _ _ _ _ (by ring) (by ring) (by ring)
  rw [e1, e2, norm_mul, norm_mul, norm_mul, norm_inv_omegaPhase_add_nat,
    norm_fivePointFactor_left]
  have h1 := hK n m
  have hP0 : 0 ≤ ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ := norm_nonneg _
  have hsc : 0 ≤ ‖sc j‖ := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hx : 0 ≤ (d.r / d.s) ^ m := by positivity
  have hy : 0 ≤ d.s ^ n := by positivity
  calc ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ * ‖sc j‖ * ‖_‖ *
        (B * (d.r / d.s) ^ m * d.s ^ n)
      ≤ ‖(omegaPhase (h' + d.δ - d.ε - 1))⁻¹‖ * ‖sc j‖ * (K * (1 + c₄) ^ n * ρ₂ ^ m) *
        (B * (d.r / d.s) ^ m * d.s ^ n) := by gcongr
    _ = P * K * B * (ρ₂ * t) ^ m * ((1 + c₄) * d.s) ^ n := by
        rw [mul_pow, mul_pow, ht]; ring

end VOA.Huang.FivePointSep
