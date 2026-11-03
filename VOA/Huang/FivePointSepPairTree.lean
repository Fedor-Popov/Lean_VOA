import VOA.Huang.FivePointSepPair
import VOA.Huang.FivePointSepMiddle

/-!
# Coefficient growth of the pair five-point expansion

The pair vertex `(X ⊠ Y) ⊠ (Z ⊠ T)` is directly of the pair shape
`f(𝒴_P(p) (𝒴_{XY}(r) x y) (𝒴_{ZT}(q) z t))`. Its array is indexed by the two internal weights
`(w, v)` (of `X ⊠ Y` and of `Z ⊠ T`); in the blow-up chart the first normalized index is
`w + v` and the second is `w`. Rows (`w` fixed) come from the proved five-point slices at a
smaller chart radius `s' ∈ (0, s)`; the inner equation is `innerRegular_pairSeries`.

`fivePointCoefficientGrowth_pair`.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop VOA.Huang.HuangODEThree VOA.Huang.HuangODEProduct
open VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
open Filter
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {X Y Z T U : Ordinary W}

/-- Replace both chart radii of a five-point test. -/
def testWithSR (d : FivePointTest X Y Z T U) (s' r' : ℝ) (h0 : 0 < r') (h1 : r' < s')
    (h2 : s' + r' < 1) : FivePointTest X Y Z T U where
  α := d.α
  β := d.β
  γ := d.γ
  δ := d.δ
  ε := d.ε
  x := d.x
  y := d.y
  z := d.z
  t := d.t
  functional := d.functional
  hx := d.hx
  hy := d.hy
  hz := d.hz
  ht := d.ht
  supported := d.supported
  s := s'
  r := r'
  positive := h0
  smaller := h1
  sum_lt := h2

/-! ## The pair chart factor -/

theorem fivePointFactor_pair_shift (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    fivePointFactor .pair d (w + m, v + n) =
      fivePointFactor .pair d (w, v) *
        ((d.r : ℂ) ^ m * (1 / ((1 + d.s : ℝ) : ℂ) ^ (m + n))) := by
  have hr : (0 : ℝ) < d.r := d.positive
  have hs : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  have hP : ((d.r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hQ : ((1 + d.s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  change (d.r : ℂ) ^ ((w + m) - d.α - d.β) * ((1 + d.s : ℝ) : ℂ) ^ (d.ε - (w + m) - (v + n)) =
    (d.r : ℂ) ^ (w - d.α - d.β) * ((1 + d.s : ℝ) : ℂ) ^ (d.ε - w - v) * _
  rw [show (w + m) - d.α - d.β = (w - d.α - d.β) + (m : ℂ) by ring,
    show d.ε - (w + m) - (v + n) = (d.ε - w - v) - ((m + n : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_add (w - d.α - d.β) (m : ℂ) hP, Complex.cpow_sub (d.ε - w - v) _ hQ,
    Complex.cpow_natCast, Complex.cpow_natCast]
  have hQn : ((1 + d.s : ℝ) : ℂ) ^ (m + n) ≠ 0 := pow_ne_zero _ hQ
  field_simp

theorem norm_fivePointFactor_pair (d : FivePointTest X Y Z T U) (w v : ℂ) (m n : ℕ) :
    ‖fivePointFactor .pair d (w + m, v + n)‖ =
      ‖fivePointFactor .pair d (w, v)‖ * d.r ^ m * (1 / (1 + d.s)) ^ (m + n) := by
  have hr : (0 : ℝ) < d.r := d.positive
  have hs : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  rw [fivePointFactor_pair_shift]
  simp only [norm_mul, norm_div, norm_pow, norm_one, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hs.le, one_div_pow]
  ring

theorem norm_fivePointFactor_pair_row (d : FivePointTest X Y Z T U) (w v : ℂ) (n : ℕ) :
    ‖fivePointFactor .pair d (w, v + n)‖ =
      ‖fivePointFactor .pair d (w, v)‖ * (1 / (1 + d.s)) ^ n := by
  have h := norm_fivePointFactor_pair d w v 0 n
  simp only [Nat.cast_zero, add_zero, pow_zero, mul_one, zero_add] at h
  exact h

theorem norm_fivePointFactor_pair_pos (d : FivePointTest X Y Z T U) (w v : ℂ) :
    0 < ‖fivePointFactor .pair d (w, v)‖ := by
  have hr : (0 : ℝ) < d.r := d.positive
  have hs : (0 : ℝ) < 1 + d.s := by linarith [d.positive, d.smaller]
  change 0 < ‖(d.r : ℂ) ^ (w - d.α - d.β) * ((1 + d.s : ℝ) : ℂ) ^ (d.ε - w - v)‖
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
    Complex.norm_cpow_eq_rpow_re_of_pos hs]
  positivity

variable (F : FusionChoice W)

/-- The pair-tree term in pair-shape form (definitional). -/
theorem fivePointTerm_pair_def (k : fiveObj F X Y Z T .pair ⟶ U)
    (d : FivePointTest X Y Z T U) (w v : ℂ) :
    fivePointTerm F .pair k d (w, v) =
      productCoeff (pairY₁ (M₀ := (tensorObj F (tensorObj F X Y) (tensorObj F Z T)).carrier))
        (pairY₂ (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner.val
          (F Z T).intertwiner.val) (F X Y).intertwiner.val
        (d.functional ∘ₗ k.val) d.t d.z d.x d.y (w + v - d.ε - 1) (d.γ + d.δ - v - 1)
        (d.α + d.β - w - 1) * fivePointFactor .pair d (w, v) := rfl

/-- Rows of the pair arrays (first internal weight fixed) from the proved five-point slices,
at a smaller chart radius `s'`. -/
theorem pair_rowBound (hs : OrdinaryFourPointSummability F)
    (k : fiveObj F X Y Z T .pair ⟶ U) (d : FivePointTest X Y Z T U) (h h' : ℂ) {s' : ℝ}
    (hs0 : 0 < s') (hs1 : s' < d.s) :
    OrdinaryPairRowBound (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner
      (F Z T).intertwiner (F X Y).intertwiner (d.functional ∘ₗ k.val)
      d.t d.z d.x d.y (h + h' - d.ε - 1) (d.γ + d.δ - h' - 1) (d.α + d.β - h - 1)
      (1 + s') := by
  intro πo πt πz πx πy k₀ j₀
  have hr' : 0 < min (s' / 2) d.r := lt_min (by linarith) d.positive
  have hsum : s' + min (s' / 2) d.r < 1 := by
    have := min_le_right (s' / 2) d.r
    linarith [d.sum_lt]
  have hlt : min (s' / 2) d.r < s' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set d' := testWithSR (testWithVectors d (πx.val d.x) (πy.val d.y) (πz.val d.z) (πt.val d.t)
    (hom_mem_weight πx.property d.hx) (hom_mem_weight πy.property d.hy)
    (hom_mem_weight πz.property d.hz) (hom_mem_weight πt.property d.ht)) s'
    (min (s' / 2) d.r) hr' hlt hsum with hd'
  have hsl := fivePoint_slice_summable F hs .pair (πo ≫ k) d' (h + j₀)
  have hinj : Function.Injective (fun m : ℕ => (h' - k₀ - j₀) + (m : ℂ)) := by
    intro a b hab
    have : (a : ℂ) = b := by simpa using hab
    exact_mod_cast this
  obtain ⟨K, hK⟩ := ((hsl.comp_injective hinj).tendsto_atTop_zero.norm).bddAbove_range
  have hsr : (0 : ℝ) < 1 + s' := by linarith
  set B := ‖fivePointFactor .pair d' (h + j₀, h' - k₀ - j₀)‖ with hB
  have hBpos : 0 < B := norm_fivePointFactor_pair_pos _ _ _
  refine ⟨K / B, fun mm => ?_⟩
  have hm : ‖fivePointTerm F .pair (πo ≫ k) d' (h + j₀, (h' - k₀ - j₀) + mm)‖ ≤ K :=
    hK ⟨mm, rfl⟩
  rw [fivePointTerm_pair_def, norm_mul] at hm
  rw [norm_fivePointFactor_pair_row] at hm
  change ‖_‖ * (B * (1 / (1 + d'.s)) ^ mm) ≤ K at hm
  have e : productCoeff
      (pairY₁ (M₀ := (tensorObj F (tensorObj F X Y) (tensorObj F Z T)).carrier))
      (pairY₂ (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner.val (F Z T).intertwiner.val)
      (F X Y).intertwiner.val (d'.functional ∘ₗ (πo ≫ k).val) d'.t d'.z d'.x d'.y
      (h + j₀ + (h' - k₀ - j₀ + mm) - d'.ε - 1) (d'.γ + d'.δ - (h' - k₀ - j₀ + mm) - 1)
      (d'.α + d'.β - (h + j₀) - 1) =
    productCoeff
      (pairY₁ (M₀ := (tensorObj F (tensorObj F X Y) (tensorObj F Z T)).carrier))
      (pairY₂ (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner.val (F Z T).intertwiner.val)
      (F X Y).intertwiner.val ((d.functional ∘ₗ k.val) ∘ₗ πo.val)
      (πt.val d.t) (πz.val d.z) (πx.val d.x) (πy.val d.y)
      (h + h' - d.ε - 1 - k₀ + mm) (d.γ + d.δ - h' - 1 + k₀ - mm + j₀)
      (d.α + d.β - h - 1 - j₀) := by
    have hα : d'.α = d.α := rfl
    have hβ : d'.β = d.β := rfl
    have hγ : d'.γ = d.γ := rfl
    have hδ : d'.δ = d.δ := rfl
    have hε : d'.ε = d.ε := rfl
    unfold productCoeff
    rw [hα, hβ, hγ, hδ, hε]
    exact pair3_congr _ _ _ _ _ (by ring) (by ring) (by ring)
  rw [e] at hm
  have hd's : d'.s = s' := rfl
  rw [hd's] at hm
  rw [show K / B * (1 + s') ^ mm = K / (B * (1 / (1 + s')) ^ mm) by
    rw [one_div_pow, mul_one_div, div_div_eq_mul_div]; ring, le_div_iff₀ (by positivity)]
  exact hm

/-- **Coefficient growth of the pair five-point expansion.** -/
theorem fivePointCoefficientGrowth_pair (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) (k : fiveObj F X Y Z T .pair ⟶ U)
    (d : FivePointTest X Y Z T U) (h h' : ℂ) :
    LocalJointGrowth (fun m n => fivePointTerm F .pair k d (h + m, h' + n)) := by
  have hr0 : (0 : ℝ) < d.r := d.positive
  have hrs : d.r < d.s := d.smaller
  have hs0 : (0 : ℝ) < d.s := lt_trans hr0 hrs
  have hsr1 : d.s + d.r < 1 := d.sum_lt
  set s' : ℝ := (d.r + 3 * d.s) / 4 with hs'
  set ρ₁ : ℝ := 1 + s' with hρ₁
  set ρ₂ : ℝ := 2 / (d.r + d.s) with hρ₂
  have hq0 : 0 < d.r + d.s := by positivity
  have hρ₂1 : 1 < ρ₂ := by rw [hρ₂, lt_div_iff₀ hq0]; linarith
  have hinv : 1 / ρ₂ = (d.r + d.s) / 2 := by rw [hρ₂]; field_simp
  have hρ : 1 + 1 / ρ₂ < ρ₁ := by rw [hinv, hρ₁, hs']; linarith
  have hs'0 : 0 < s' := by rw [hs']; positivity
  have hs's : s' < d.s := by rw [hs']; linarith
  obtain ⟨K, hK⟩ := ordinaryPair_geometric hV hΦ
    (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner (F Z T).intertwiner
    (F X Y).intertwiner (d.functional ∘ₗ k.val) d.ht d.hz d.hx d.hy
    (h + h' - d.ε - 1) (d.γ + d.δ - h' - 1) (d.α + d.β - h - 1) hρ₂1 hρ
    (pair_rowBound F hs k d h h' hs'0 hs's)
  set B := ‖fivePointFactor .pair d (h, h')‖
  have hsp : (0 : ℝ) < 1 + d.s := by linarith
  have hρ₂r : ρ₂ * d.r < 1 := by
    rw [hρ₂, div_mul_eq_mul_div, div_lt_one hq0]; linarith
  have hρ₁s : ρ₁ < 1 + d.s := by rw [hρ₁, hs']; linarith
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁]; linarith
  have hρ₂0 : 0 < ρ₂ := by linarith
  refine localJointGrowth_of_geometric (K := K * B) (a := ρ₁ * ρ₂ * d.r * (1 / (1 + d.s)))
    (b := ρ₁ * (1 / (1 + d.s))) (by positivity) ?_ (by positivity) ?_ fun m n => ?_
  · rw [mul_one_div, div_lt_one hsp]
    have h1 : ρ₁ * (ρ₂ * d.r) < ρ₁ * 1 := mul_lt_mul_of_pos_left hρ₂r hρ₁0
    nlinarith
  · rw [mul_one_div, div_lt_one hsp]; exact hρ₁s
  · rw [fivePointTerm_pair_def, norm_mul, norm_fivePointFactor_pair]
    have e : productCoeff
        (pairY₁ (M₀ := (tensorObj F (tensorObj F X Y) (tensorObj F Z T)).carrier))
        (pairY₂ (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner.val
          (F Z T).intertwiner.val) (F X Y).intertwiner.val
        (d.functional ∘ₗ k.val) d.t d.z d.x d.y (h + m + (h' + n) - d.ε - 1)
        (d.γ + d.δ - (h' + n) - 1) (d.α + d.β - (h + m) - 1) =
      productCoeff
        (pairY₁ (M₀ := (tensorObj F (tensorObj F X Y) (tensorObj F Z T)).carrier))
        (pairY₂ (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner.val
          (F Z T).intertwiner.val) (F X Y).intertwiner.val
        (d.functional ∘ₗ k.val) d.t d.z d.x d.y (h + h' - d.ε - 1 + ((m + n : ℕ) : ℂ))
        (d.γ + d.δ - h' - 1 - ((m + n : ℕ) : ℂ) + m) (d.α + d.β - h - 1 - m) := by
      unfold productCoeff
      exact pair3_congr _ _ _ _ _ (by push_cast; ring) (by push_cast; ring) (by ring)
    rw [e]
    have h1 := hK (m + n) m
    have hB0 : 0 ≤ B := norm_nonneg _
    calc _ ≤ (K * ρ₁ ^ (m + n) * ρ₂ ^ m) * (B * d.r ^ m * (1 / (1 + d.s)) ^ (m + n)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K * B * (ρ₁ * ρ₂ * d.r * (1 / (1 + d.s))) ^ m * (ρ₁ * (1 / (1 + d.s))) ^ n := by
          simp only [mul_pow, pow_add]; ring

end VOA.Huang.FivePointSep
