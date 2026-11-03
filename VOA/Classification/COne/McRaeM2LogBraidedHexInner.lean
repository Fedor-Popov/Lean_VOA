import VOA.Classification.COne.McRaeM2LogBraidedHexData

/-! # The inner braiding of a product near `u = -3/4`

The two product expansions of the hexagon into `Y ⊠ (Z ⊠ X)` agree on the disc
`|u + 3/4| < 1/4` of the half plane `s·Im u > 0` (`hexFB_eq_hexFC`). Writing the
outer canonical operator as `Ω_r(K')` with `K' = Ω_{-r-1}(𝒴_{Y,Z⊠X})`, both sides become
`L(−1)`-sums of completed iterates of `K'` at the same pair of branches:
`hexFB` by the product side of skew-symmetry, and `hexFC` by the product side
followed by the inner translation theorem. The two `L(−1)`-sums agree by the
binomial theorem `e^{(1+u)L} e^{-uL} = e^{L}`, and the branches agree because both
are logarithms of `u` with imaginary parts in a common window of width `< 2π`. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000
noncomputable section
namespace VOA.Huang.LogBraided
open scoped BigOperators
universe w

/-- `Ω_r ∘ Ω_{-r-1} = id` on actual logarithmic intertwining operators. -/
theorem omegaEquiv_omegaEquiv_neg {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃]
    (A₁ : VOA.WeakModule W M₁) (A₂ : VOA.WeakModule W M₂) (A₃ : VOA.WeakModule W M₃) (r : ℤ)
    (Y : VOA.LogTensor.LogIntertwiningOperator A₁ A₂ A₃) :
    VOA.LogTensor.omegaEquiv A₂ A₁ A₃ r (VOA.LogTensor.omegaEquiv A₁ A₂ A₃ (-r-1) Y) = Y := by
  apply Subtype.ext
  have h := Y.2.omega_omega (-r-1)
  rw [show -(-r-1)-1 = r by ring] at h
  exact h

/-- Composing translation powers on the functional of a completed iterate. -/
theorem completedLogIterate_pow_add {V : Type w} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} {M₁ M₂ M₃ M₄ M₅ : Type w}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
    [AddCommGroup M₅] [Module ℂ M₅]
    (N₁ : VOA.LogVModule W M₁) (N₂ : VOA.LogVModule W M₂) (N₃ : VOA.LogVModule W M₃)
    (N₄ : VOA.LogVModule W M₄) (N₅ : VOA.LogVModule W M₅)
    (Y₃ : VOA.LogTensor.LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : VOA.LogTensor.LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (ℓ₀ ℓ₂ c β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (i m : ℕ) (x : M₁) (y : M₂) (z : N₃.weight c) :
    VOA.Huang.LogAssocExpansion.completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ ℓ₀ ℓ₂ c (β-i-m)
        ((f ∘ₗ (VOA.LogTensor.Lm1 N₄.toWeakModule ^ i)) ∘ₗ (VOA.LogTensor.Lm1 N₄.toWeakModule ^ m))
        x y z =
      VOA.Huang.LogAssocExpansion.completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ ℓ₀ ℓ₂ c
        (β-((i+m : ℕ) : ℂ)) (f ∘ₗ (VOA.LogTensor.Lm1 N₄.toWeakModule ^ (i+m))) x y z := by
  have hβ : β-((i+m : ℕ) : ℂ) = β-i-m := by push_cast; ring
  rw [hβ, pow_add, Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- Regrouping a truncated double sum along antidiagonals. -/
theorem double_sum_trunc (J : ℕ) (c d F : ℕ → ℂ) (hF : ∀ j, J ≤ j → F j = 0) :
    ∑ i∈Finset.range J, ∑ m∈Finset.range J, c i * d m * F (i+m) =
      ∑ j∈Finset.range J, (∑ i∈Finset.range (j+1), c i * d (j-i)) * F j := by
  have h1 : ∀ i ∈ Finset.range J, ∑ m∈Finset.range J, c i * d m * F (i+m) =
      ∑ j∈Finset.Ico i J, c i * d (j-i) * F j := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le J i))
      (fun m _ hm => ?_)).symm
    rw [Finset.mem_range, not_lt] at hm
    rw [hF _ (by omega), mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm' (t' := Finset.range J)
    (s' := fun j => Finset.range (j+1)) (by
      intro i j
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

/-- The binomial theorem in exponential form. -/
theorem sum_transCoeff_binom (p q : ℂ) (j : ℕ) :
    ∑ i∈Finset.range (j+1), (p^i * ((i.factorial : ℂ))⁻¹) * (q^(j-i) * (((j-i).factorial : ℂ))⁻¹) =
      (p+q)^j * ((j.factorial : ℂ))⁻¹ := by
  rw [add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hc := Nat.choose_mul_factorial_mul_factorial (show i ≤ j by omega)
  have hc' : ((j.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((j-i).factorial : ℂ) =
      (j.factorial : ℂ) := by exact_mod_cast hc
  have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj0 : ((j-i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-i)
  have hc0 : ((j.choose i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show i ≤ j by omega)).ne'
  rw [← hc']
  field_simp

/-- Two logarithms of the same number with close imaginary parts coincide. -/
theorem eq_of_exp_eq_of_abs_im_sub {A B : ℂ} (h : Complex.exp A = Complex.exp B)
    (him : |A.im - B.im| < 2*Real.pi) : A = B := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hnim : A.im - B.im = n * (2*Real.pi) := by
    rw [hn]; simp
  rw [hnim, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)] at him
  have hn1 : |(n : ℝ)| < 1 := by
    have := Real.pi_pos
    by_contra hc
    push Not at hc
    nlinarith
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hn1
    exact Int.abs_lt_one_iff.mp this
  rw [hn, hn0]; simp

end VOA.Huang.LogBraided

namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion VOA.Huang.LogBraided
open VOA.Huang.AssocExpansion
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-! ## Geometry of the disc `|u + 3/4| < 1/4` -/

section Geometry
open VOA.Huang.TensorCat.HexagonClose (sign_arg_mem sign_arg_mem_of_re_neg sign_arg_lt_of_re_pos
  re_div_one_add im_div_one_add)

theorem disc_re_bounds {u : ℂ} (hu : u∈Metric.ball (-3/4 : ℂ) (1/4)) :
    -1 < u.re ∧ u.re < -1/2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hu
  have := Complex.abs_re_le_norm (u - -3/4)
  have h2 : (u - -3/4).re = u.re + 3/4 := by simp; norm_num
  rw [h2] at this
  constructor <;> linarith [abs_lt.mp (lt_of_le_of_lt this hu)]

theorem disc_norm_one_add {u : ℂ} (hu : u∈Metric.ball (-3/4 : ℂ) (1/4)) : ‖1+u‖ < 1/2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hu
  calc ‖1+u‖ = ‖(u - -3/4) + 1/4‖ := by congr 1; ring
    _ ≤ ‖u - -3/4‖ + ‖(1/4 : ℂ)‖ := norm_add_le _ _
    _ < 1/2 := by rw [show ‖(1/4 : ℂ)‖ = 1/4 by norm_num]; linarith

theorem disc_re_add_normSq {u : ℂ} (hu : u∈Metric.ball (-3/4 : ℂ) (1/4)) :
    u.re + Complex.normSq u < 0 := by
  rw [Metric.mem_ball, dist_eq_norm] at hu
  have h0 := norm_nonneg (u - -3/4)
  have hsq : Complex.normSq (u - -3/4) < 1/16 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hsq ⊢
  norm_num at hsq
  nlinarith

end Geometry

/-- `e^{λ₁(u)} = -u`. -/
theorem exp_hexL1 (r : ℤ) {u : ℂ} (h0 : u ≠ 0) (h1 : 1+u ≠ 0) :
    Complex.exp (hexL1 r u) = -u := by
  have hL2 : Complex.exp (hexL2 r u) = -(1+u) := by
    rw [hexL2, Complex.exp_add, Complex.exp_log h1, exp_kap]; ring
  have he : 1 + Complex.exp (-hexL2 r u) = u/(1+u) := by
    rw [Complex.exp_neg, hL2]; field_simp; ring
  have hne : u/(1+u) ≠ 0 := div_ne_zero h0 h1
  rw [hexL1, Complex.exp_add, he, Complex.exp_log hne, hL2]
  field_simp

section Branch
open VOA.Huang.TensorCat.HexagonClose (sign_arg_mem sign_arg_mem_of_re_neg sign_arg_lt_of_re_pos
  re_div_one_add im_div_one_add)

/-- `1 + e^{-λ₂(u)} = u/(1+u)`. -/
theorem one_add_exp_neg_hexL2 (r : ℤ) {u : ℂ} (h1 : 1+u ≠ 0) :
    1 + Complex.exp (-hexL2 r u) = u/(1+u) := by
  have hL2 : Complex.exp (hexL2 r u) = -(1+u) := by
    rw [hexL2, Complex.exp_add, Complex.exp_log h1, exp_kap]; ring
  rw [Complex.exp_neg, hL2]; field_simp; ring

/-- The two rotated outer branches agree on the disc. -/
theorem hexL1_branch (r : ℤ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hrs : kap r = -VOA.Huang.TensorCat.HexagonClose.kap s) {u : ℂ}
    (hball : u∈Metric.ball (-3/4 : ℂ) (1/4)) (him : 0 < s * u.im) :
    (0+kap r) + Complex.log (1+Complex.exp (Complex.log (1+u) - (0+kap r))) =
      hexL1 r u + kap r := by
  obtain ⟨hre1, hre2⟩ := disc_re_bounds hball
  have hu0 : u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre2; linarith
  have h1re : 0 < (1+u).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have h10 : 1+u ≠ 0 := by intro h; rw [h, Complex.zero_re] at h1re; linarith
  have he1 : 1 + Complex.exp (Complex.log (1+u) - (0+kap r)) = -u := by
    rw [zero_add, Complex.exp_sub, Complex.exp_log h10, exp_kap]; field_simp; ring
  have hkapim : (kap r).im = -(s*Real.pi) := by
    rw [hrs, Complex.neg_im, VOA.Huang.TensorCat.HexagonClose.kap_im]
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine eq_of_exp_eq_of_abs_im_sub ?_ ?_
  · rw [Complex.exp_add, he1, Complex.exp_log (neg_ne_zero.mpr hu0),
      Complex.exp_add (hexL1 r u), exp_hexL1 r hu0 h10, zero_add]
    ring
  · rw [he1, hexL1, one_add_exp_neg_hexL2 r h10, hexL2]
    simp only [Complex.add_im, zero_add, Complex.log_im]
    rw [hkapim]
    -- the three arguments
    have hs' : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
    have hneg : 0 < -s * (-u).im := by simp only [Complex.neg_im]; linarith
    have a1 := sign_arg_mem hs' hneg
    have hdivim : 0 < s * (u/(1+u)).im := by
      rw [im_div_one_add, mul_div_assoc']
      exact div_pos him (Complex.normSq_pos.mpr h10)
    have hdivre : (u/(1+u)).re < 0 := by
      rw [re_div_one_add]
      exact div_neg_of_neg_of_pos (disc_re_add_normSq hball) (Complex.normSq_pos.mpr h10)
    have a2 := sign_arg_mem hs hdivim
    have a2' := sign_arg_mem_of_re_neg hs hdivim hdivre
    have h1im : 0 < s * (1+u).im := by
      simp only [Complex.add_im, Complex.one_im, zero_add]; exact him
    have a3 := sign_arg_mem hs h1im
    have a3' := sign_arg_lt_of_re_pos hs h1re
    have key : s * (-(s*Real.pi) + Complex.arg (-u) -
        (Complex.arg (u/(1+u)) + Complex.arg (1+u) + -(s*Real.pi) + -(s*Real.pi))) =
        s * Complex.arg (-u) - s * Complex.arg (u/(1+u)) - s * Complex.arg (1+u) + Real.pi := by
      linear_combination (Real.pi) * hss
    have hb : |s * (-(s*Real.pi) + Complex.arg (-u) -
        (Complex.arg (u/(1+u)) + Complex.arg (1+u) + -(s*Real.pi) + -(s*Real.pi)))| <
        2*Real.pi := by
      rw [key, abs_lt]
      have : -s * Complex.arg (-u) = -(s * Complex.arg (-u)) := by ring
      rw [this] at a1
      constructor <;> linarith [Real.pi_pos]
    rw [abs_mul] at hb
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [habs, one_mul] at hb
    convert hb using 2
    ring

end Branch

/-- **The inner braiding identity**: `hexFB = hexFC` on `|u + 3/4| < 1/4`,
`s·Im u > 0`. -/
theorem hexFB_eq_hexFC (r : ℤ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hrs : kap r = -VOA.Huang.TensorCat.HexagonClose.kap s)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) (J : ℕ)
    (hJT : ∀ β' : ℂ, β'.re ≤ β.re → ∀ j : ℕ, J ≤ j →
      (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).weight (β'-j) = ⊥)
    {u : ℂ} (hball : u∈Metric.ball (-3/4 : ℂ) (1/4)) (him : 0 < s * u.im) :
    hexFB hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy J u =
      hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy u := by
  have hfgZX := tensorModule_finGen hC2 N₃ N₁ h₃ h₁
  have hfgT := tensorModule_finGen hC2 N₂ (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ hfgZX
  obtain ⟨K', hK'⟩ : ∃ K' : LogIntertwiningOperator (tensorModule hC2 N₃ N₁ h₃ h₁).toWeakModule
      N₂.toWeakModule (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule,
      omegaEquiv (tensorModule hC2 N₃ N₁ h₃ h₁).toWeakModule N₂.toWeakModule
        (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule r K' =
      tensorIntertwiner hC2 N₂ (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ hfgZX := by
    exact ⟨_, omegaEquiv_omegaEquiv_neg _ _ _ r _⟩
  obtain ⟨hre1, hre2⟩ := disc_re_bounds hball
  have hn1 := disc_norm_one_add hball
  have hu0 : u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre2; linarith
  have h1re : 0 < (1+u).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have h10 : 1+u ≠ 0 := by intro h; rw [h, Complex.zero_re] at h1re; linarith
  have hn1pos : 0 < ‖1+u‖ := norm_pos_iff.mpr h10
  have hkre : (kap r).re = 0 := by rw [kap]; simp
  -- the common iterates
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℂ, ∀ j, F j = completedLogIterate N₃ N₁ N₂
      (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁) K' (tensorIntertwiner hC2 N₃ N₁ h₃ h₁)
      (Complex.log (1+u) + kap r) (hexL1 r u + kap r) b (β-j)
      (f ∘ₗ (Lm1 (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule ^ j)) z x ⟨y,hy⟩ :=
    ⟨_, fun j => rfl⟩
  have hF0 : ∀ j, J ≤ j → F j = 0 := fun j hj => by
    rw [hFdef]
    exact completedLogIterate_eq_zero_of_bot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hJT β le_rfl j hj)
  -- the right product
  have hC' : hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy u =
      ∑ j∈Finset.range J, transCoeff 0 j * F j := by
    have hlt : (Complex.log (1+u)).re < (0:ℂ).re := by
      rw [Complex.log_re, Complex.zero_re]
      exact Real.log_neg hn1pos (by linarith)
    have hP := completedLogProduct_omega hC2 N₂ N₁ N₃ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ h₁ h₃ hfgT hfgZX K'
      (omegaEquiv N₃.toWeakModule N₁.toWeakModule (tensorModule hC2 N₃ N₁ h₃ h₁).toWeakModule r
        (tensorIntertwiner hC2 N₃ N₁ h₃ h₁)) r hy hx hz f β hlt J (hJT β le_rfl)
    rw [hK'] at hP
    unfold hexFC
    rw [hP]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hp2 : ‖Complex.exp (Complex.log (1+u) - (0+kap r))‖ < 1/2 := by
      rw [Complex.exp_sub, Complex.exp_log h10, norm_div, Complex.norm_exp, zero_add, hkre,
        Real.exp_zero, div_one]
      exact hn1
    rw [completedLogIterate_omega_inner hC2 N₁ N₃ N₂ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁) h₁ h₃ h₂ hfgT hfgZX K' _ r hx hz hy _ _ hp2,
      hexL1_branch r hs hrs hball him, hFdef]
  -- the left products
  have hB' : hexFB hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy J u =
      ∑ i∈Finset.range J, ∑ m∈Finset.range J,
        transCoeff (Complex.log (1+u)) i * transCoeff (hexL1 r u) m * F (i+m) := by
    have hlt : (hexL2 r u).re < (hexL1 r u).re := by
      rw [hexL1, Complex.add_re, Complex.log_re, one_add_exp_neg_hexL2 r h10, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hu0) (norm_ne_zero_iff.mpr h10)]
      rw [hexL2, Complex.add_re, Complex.log_re, hkre, add_zero]
      have := VOA.Huang.LogBraided.norm_one_add_lt_norm' (r := u) (by linarith)
      have := Real.log_lt_log hn1pos this
      linarith
    unfold hexFB
    refine Finset.sum_congr rfl fun i _ => ?_
    have hP := completedLogProduct_omega hC2 N₂ N₃ N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ h₃ h₁ hfgT hfgZX K' (tensorIntertwiner hC2 N₃ N₁ h₃ h₁) r
      hy hz hx (f ∘ₗ (Lm1 (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule ^ i)) (β-i)
      hlt J (hJT (β-i) (by simp))
    rw [hK'] at hP
    rw [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hIt := completedLogIterate_pow_add N₃ N₁ N₂ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁) K' (tensorIntertwiner hC2 N₃ N₁ h₃ h₁)
      (hexL2 r u) (hexL1 r u + kap r) b β f i m z x ⟨y,hy⟩
    have key := hIt.trans (hFdef (i+m)).symm
    rw [key]
    ring
  rw [hB', hC', double_sum_trunc J _ _ F hF0]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hc : ∀ i : ℕ, transCoeff (Complex.log (1+u)) i =
      (1+u)^i * ((i.factorial : ℂ))⁻¹ := by
    intro i
    rw [transCoeff, mul_comm (Complex.log (1+u)), Complex.exp_nat_mul, Complex.exp_log h10]
  have hd : ∀ m : ℕ, transCoeff (hexL1 r u) m = (-u)^m * ((m.factorial : ℂ))⁻¹ := by
    intro m
    rw [transCoeff, mul_comm (hexL1 r u), Complex.exp_nat_mul, exp_hexL1 r hu0 h10]
  simp only [hc, hd]
  rw [sum_transCoeff_binom, transCoeff]
  simp

end VOA.C2Rigid.LocalInjective
