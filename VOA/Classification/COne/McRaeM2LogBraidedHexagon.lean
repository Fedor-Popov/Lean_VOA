import VOA.Classification.COne.McRaeM2LogBraidedHexInner

/-! # The logarithmic hexagons

For finite logarithmic modules of a `C₂`-cofinite VOA and the swap branches
`r = 0` (the braiding `Ω₀`) and `r = -1` (the reverse braiding `Ω₋₁`), the two
hexagon paths agree (`hexagon_weak`). The proof tests both paths on completed
canonical iterates (`leftTriple_linearMap_ext_of_completed_iterate`). For small
real coordinates the left path is the expansion `hexFA` and the right path is
`hexFD`; these are glued (`glue_four`) through the two product expansions
`hexFB`, `hexFC` and the half-plane continuation of products
(`exists_prodValue_halfPlane`), and the identity theorem in the iterate coordinate
extends the agreement to the whole overlap chart. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion VOA.Huang.LogBraided
open VOA.Huang.AssocExpansion
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-! ## Geometry of the two associativity regions -/

section Geometry
open VOA.Huang.TensorCat.HexagonClose (sign_arg_mem sign_arg_mem_of_re_neg sign_arg_lt_of_re_pos
  abs_im_lt_of_exp_re_pos ellK ellM ellK_re ellK_im ellM_re ellM_im exp_ellM re_div_one_add
  sign_cases)

theorem abs_lt_of_sign_mul' {s x b : ℝ} (hs : s = 1 ∨ s = -1) (h1 : -b < s * x)
    (h2 : s * x < b) : |x| < b := by
  rcases hs with rfl | rfl <;> rw [abs_lt] <;> constructor <;> linarith

/-- The left associativity chart: `-λ₂(u) = ℓ_K(u)` lies in the overlap domain. -/
theorem hexAB_mem {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℤ}
    (hrs : kap r = -VOA.Huang.TensorCat.HexagonClose.kap s) {u : ℂ}
    (hre : u.re < -2) (him : 0 < s * u.im) : -hexL2 r u∈overlapDomain := by
  have he : -hexL2 r u = ellK s u := by rw [hexL2, hrs, ellK]; ring
  rw [he]
  have him1 : 0 < s * (1 + u).im := by simpa using him
  have hre1 : (1 + u).re < 0 := by simp; linarith
  have hn : 1 < ‖1 + u‖ := by
    have := Complex.abs_re_le_norm (1 + u)
    have h2 : (1 + u).re < -1 := by simp; linarith
    rw [abs_of_neg hre1] at this
    linarith
  refine ⟨by rw [ellK_re]; linarith [Real.log_pos hn], ?_⟩
  rw [ellK_im]
  have ha := sign_arg_mem_of_re_neg hs him1 hre1
  have hb := (sign_arg_mem hs him1).2
  have e : s * (s * Real.pi - Complex.arg (1 + u)) = Real.pi - s * Complex.arg (1 + u) := by
    rw [mul_sub, ← mul_assoc, sign_cases hs, one_mul]
  refine abs_lt_of_sign_mul' hs ?_ ?_ <;> rw [e] <;> linarith only [ha, hb]

/-- The right associativity chart: `log u + κ - log(1+u) = ℓ_M(u)` lies in the overlap domain. -/
theorem hexCD_mem {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℤ}
    (hrs : kap r = -VOA.Huang.TensorCat.HexagonClose.kap s) {u : ℂ}
    (hball : u ∈ Metric.ball (-1 / 2 : ℂ) (1 / 2)) (hre : -1 / 2 < u.re) (him : 0 < s * u.im) :
    Complex.log u + kap r - Complex.log (1+u)∈overlapDomain := by
  have he : Complex.log u + kap r - Complex.log (1+u) = ellM s u := by rw [hrs, ellM]; ring
  rw [he]
  have hr0 : u ≠ 0 := by intro h; rw [h] at him; simp at him
  have h10 : 1 + u ≠ 0 := by
    intro h
    have : (1+u).im = 0 := by rw [h]; simp
    simp at this; rw [this, mul_zero] at him; exact lt_irrefl _ him
  rw [Metric.mem_ball, dist_eq_norm] at hball
  have hb2 : Complex.normSq (u - -1 / 2) < 1 / 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_nonneg (u - -1 / 2)
    nlinarith
  have hb3 : u.re + Complex.normSq u < 0 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hb2 ⊢
    norm_num at hb2
    nlinarith
  have hreneg : u.re < 0 := by
    have := Complex.normSq_nonneg u
    linarith
  have him1 : 0 < s * (1 + u).im := by simpa using him
  have hre1 : 0 < (1 + u).re := by simp; linarith
  refine ⟨?_, ?_⟩
  · rw [ellM_re]
    linarith [Real.log_lt_log (norm_pos_iff.2 hr0) (norm_lt_norm_one_add' hre)]
  · have hexpre : 0 < (Complex.exp (ellM s u)).re := by
      rw [exp_ellM hs hr0 h10, Complex.neg_re, re_div_one_add, neg_pos]
      exact div_neg_of_neg_of_pos hb3 (Complex.normSq_pos.2 h10)
    have ha := sign_arg_mem_of_re_neg hs him hreneg
    have hb := (sign_arg_mem hs him).2
    have hc := (sign_arg_mem hs him1).1
    have hd := sign_arg_lt_of_re_pos hs hre1
    have habs : |(ellM s u).im| < Real.pi := by
      rw [ellM_im]
      have e : s * (Complex.arg u - Complex.arg (1 + u) - s * Real.pi) =
          s * Complex.arg u - s * Complex.arg (1 + u) - Real.pi := by
        rw [mul_sub, mul_sub, ← mul_assoc, sign_cases hs, one_mul]
      refine abs_lt_of_sign_mul' hs ?_ ?_ <;> rw [e] <;> linarith only [ha, hb, hc, hd]
    rw [abs_lt] at habs
    exact abs_im_lt_of_exp_re_pos habs.1 habs.2 hexpre

/-- The first product branch on the right is `0`. -/
theorem hexCD_branch (r : ℤ) {u : ℂ} (hu0 : u ≠ 0) (him : (1+u).im ≠ 0) :
    Complex.log (1+Complex.exp (Complex.log u + kap r - Complex.log (1+u))) +
      Complex.log (1+u) = 0 := by
  have h10 : 1+u ≠ 0 := by intro h; rw [h] at him; simp at him
  have he : 1+Complex.exp (Complex.log u + kap r - Complex.log (1+u)) = (1+u)⁻¹ := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hu0, Complex.exp_log h10, exp_kap]
    field_simp; ring
  have harg : Complex.arg (1+u) ≠ Real.pi := by
    intro h
    exact him (Complex.arg_eq_pi_iff.mp h).2
  rw [he, Complex.log_inv _ harg, neg_add_cancel]

theorem isOpen_overlapDomain : IsOpen overlapDomain :=
  (isOpen_lt Complex.continuous_re continuous_const).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem convex_overlapDomain : Convex ℝ overlapDomain := by
  have he : overlapDomain = {t : ℂ | t.re < 0} ∩ ({t : ℂ | t.im < Real.pi/2} ∩
      {t : ℂ | -(Real.pi/2) < t.im}) := by
    ext t
    simp only [overlapDomain, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
    tauto
  rw [he]
  exact (convex_halfSpace_re_lt 0).inter ((convex_halfSpace_im_lt _).inter
    (convex_halfSpace_im_gt _))

end Geometry

variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-! ## Holomorphy of the expansions -/

theorem differentiableAt_log_one_add {u : ℂ} (hsl : 1+u∈Complex.slitPlane) :
    DifferentiableAt ℂ (fun u : ℂ => Complex.log (1+u)) u :=
  ((differentiableAt_const 1).add differentiableAt_id).clog hsl

theorem differentiableAt_transCoeff_log {u : ℂ} (hsl : 1+u∈Complex.slitPlane) (j : ℕ) :
    DifferentiableAt ℂ (fun u : ℂ => transCoeff (Complex.log (1+u)) j) u := by
  simp only [transCoeff]
  exact (((differentiableAt_log_one_add hsl).mul_const _).cexp).mul_const _

theorem differentiableAt_hexFA (r : ℤ)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) (J : ℕ) {u : ℂ}
    (h1 : 1 < ‖1+u‖) (hsl : 1+u∈Complex.slitPlane) :
    DifferentiableAt ℂ (hexFA hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β y z hx J) u := by
  have hL2 : DifferentiableAt ℂ (hexL2 r) u :=
    (differentiableAt_log_one_add hsl).add_const (kap r)
  have hlt : ((fun _ : ℂ => (0:ℂ)) u).re < (hexL2 r u).re := by
    rw [hexL2, Complex.add_re, Complex.log_re, kap]
    simp only [Complex.zero_re]
    simp
    exact Real.log_pos h1
  show DifferentiableAt ℂ (fun u => hexFA hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β y z hx J u) u
  unfold hexFA
  refine DifferentiableAt.fun_sum fun j _ => DifferentiableAt.mul
    (differentiableAt_transCoeff_log hsl j) ?_
  exact differentiableAt_completedLogIterate_comp hC2 N₂ N₃ N₁
    (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁) (tensorModule hC2 N₂ N₃ h₂ h₃) h₂ h₃ h₁
    (tensorModule_finGen hC2 _ N₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) h₁)
    (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) _ _ hy hz hx _ _ (ℓ₀ := fun _ => 0) (ℓ₂ := hexL2 r)
    (differentiableAt_const _) hL2 hlt

theorem differentiableAt_hexFC (r : ℤ)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) {u : ℂ}
    (h1 : ‖1+u‖ < 1) (hsl : 1+u∈Complex.slitPlane) :
    DifferentiableAt ℂ (hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy) u := by
  have h10 : 1+u ≠ 0 := Complex.slitPlane_ne_zero hsl
  have hlt : ((fun u : ℂ => Complex.log (1+u)) u).re < ((fun _ : ℂ => (0:ℂ)) u).re := by
    simp only [Complex.log_re, Complex.zero_re]
    exact Real.log_neg (norm_pos_iff.mpr h10) h1
  show DifferentiableAt ℂ (fun u => hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy u) u
  unfold hexFC
  exact differentiableAt_completedLogProduct_comp hC2 N₂ N₁ N₃
    (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁) (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ h₁ h₃
    (tensorModule_finGen hC2 N₂ _ h₂ (tensorModule_finGen hC2 N₃ N₁ h₃ h₁))
    (tensorModule_finGen hC2 N₃ N₁ h₃ h₁) _ _ hy hx hz _ _ (m₁ := fun _ => 0)
    (m₂ := fun u => Complex.log (1+u)) (differentiableAt_const _)
    (differentiableAt_log_one_add hsl) hlt

theorem differentiableAt_hexFD (r : ℤ)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) {u : ℂ}
    (hlt' : ‖u‖ < ‖1+u‖) (hsl0 : u∈Complex.slitPlane) (hsl : 1+u∈Complex.slitPlane) :
    DifferentiableAt ℂ (hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x y hz) u := by
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hsl0
  have hlt : ((fun u : ℂ => Complex.log u + kap r) u).re <
      ((fun u : ℂ => Complex.log (1+u)) u).re := by
    simp only [Complex.add_re, Complex.log_re, kap]
    simp
    exact Real.log_lt_log (norm_pos_iff.mpr hu0) hlt'
  show DifferentiableAt ℂ (fun u => hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x y hz u) u
  unfold hexFD
  exact differentiableAt_completedLogIterate_comp hC2 N₂ N₁ N₃
    (leftTripleModule hC2 N₂ N₁ h₂ h₁ N₃ h₃) (tensorModule hC2 N₂ N₁ h₂ h₁) h₂ h₁ h₃
    (tensorModule_finGen hC2 _ N₃ (tensorModule_finGen hC2 N₂ N₁ h₂ h₁) h₃)
    (tensorModule_finGen hC2 N₂ N₁ h₂ h₁) _ _ hy hx hz _ _
    (ℓ₀ := fun u => Complex.log u + kap r) (ℓ₂ := fun u => Complex.log (1+u))
    ((differentiableAt_id.clog hsl0).add_const _) (differentiableAt_log_one_add hsl) hlt

/-! ## The hexagon on the weak level -/

/-- **The logarithmic hexagon** for the swap branches `r = 0` and `r = -1`:
`α_{Y,Z,X} ∘ c_{X,Y⊠Z} ∘ α_{X,Y,Z} = (Y ◁ c_{X,Z}) ∘ α_{Y,X,Z} ∘ (c_{X,Y} ▷ Z)`. -/
theorem hexagon_weak (r : ℤ) (hr : r = 0 ∨ r = -1) :
    (hexLeft hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap =
      (hexRight hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap := by
  obtain ⟨s, hs, hrs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      kap r = -VOA.Huang.TensorCat.HexagonClose.kap s := by
    rcases hr with rfl | rfl
    · exact ⟨-1, Or.inr rfl, by simp [kap, VOA.Huang.TensorCat.HexagonClose.kap]⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      simp only [kap, VOA.Huang.TensorCat.HexagonClose.kap]
      push_cast; ring
  have hs' : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  have hss' : (-s) * (-s) = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hfgYZ := tensorModule_finGen hC2 N₂ N₃ h₂ h₃
  have hfgZX := tensorModule_finGen hC2 N₃ N₁ h₃ h₁
  have hfgT := tensorModule_finGen hC2 N₂ (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ hfgZX
  apply leftTriple_linearMap_ext_of_completed_iterate hC2 N₁ N₂ N₃ h₁ h₂ h₃
  intro f a b c β x y z hx hy hz t ht
  -- a common weight cutoff
  obtain ⟨B1, hB1⟩ := (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).boundedBelow
  obtain ⟨B2, hB2⟩ := (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).boundedBelow
  set J := ⌈β.re - min B1 B2⌉₊ + 1 with hJdef
  have hJbound : ∀ (β' : ℂ), β'.re ≤ β.re → ∀ j : ℕ, J ≤ j → (β' - j).re < min B1 B2 := by
    intro β' hβ' j hj
    have h1 := Nat.le_ceil (β.re - min B1 B2)
    have h3 : ((⌈β.re - min B1 B2⌉₊ : ℕ) : ℝ) + 1 ≤ j := by exact_mod_cast hj
    rw [Complex.sub_re, Complex.natCast_re]
    linarith
  have hJL : ∀ j : ℕ, J ≤ j → (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).weight (β-j) = ⊥ := by
    intro j hj
    by_contra hne
    have := hB1 _ hne
    have := hJbound β le_rfl j hj
    have := min_le_left B1 B2
    linarith
  have hJT : ∀ β' : ℂ, β'.re ≤ β.re → ∀ j : ℕ, J ≤ j →
      (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).weight (β'-j) = ⊥ := by
    intro β' hβ' j hj
    by_contra hne
    have := hB2 _ hne
    have := hJbound β' hβ' j hj
    have := min_le_right B1 B2
    linarith
  -- the half-plane continuation of the left products
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₂ (tensorModule hC2 N₃ N₁ h₃ h₁)
    (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁) h₂ hfgZX hfgT
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₃ N₁ (tensorModule hC2 N₃ N₁ h₃ h₁) h₃ h₁ hfgZX
  have hΦex : ∀ j : ℕ, ∃ Φ : ℂ × ℂ → ℂ,
      DifferentiableOn ℂ Φ {p : ℂ × ℂ | 0 < (-s) * (Complex.exp (p.2-p.1)).im} ∧
      ∀ p : ℂ × ℂ, p.2.re < p.1.re → 0 < (-s) * (Complex.exp (p.2-p.1)).im →
        prodValue hC2 (tensorModule hC2 N₃ N₁ h₃ h₁) hfgZX
          (tensorIntertwiner hC2 N₂ (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ hfgZX).1
          (tensorIntertwiner hC2 N₃ N₁ h₃ h₁).1 K L
          (f ∘ₗ (Lm1 (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule ^ j)) y z x b c a
          (β-j) p.1 p.2 = Φ p := fun j =>
    exists_prodValue_halfPlane hC2 N₂ N₃ N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ h₃ h₁ hfgT hfgZX _ _ K L hy hz hx _ (β-j) hss'
  choose Φ hΦd hΦe using hΦex
  let PhiT : ℂ → ℂ := fun u => ∑ j∈Finset.range J,
    transCoeff (Complex.log (1+u)) j * Φ j (hexL1 r u, hexL2 r u)
  -- elementary facts on the half plane
  have hsl_of : ∀ {w : ℂ}, 0 < s * w.im → w∈Complex.slitPlane := fun h =>
    mem_slitPlane_of_sim' h
  have h1im : ∀ {u : ℂ}, 0 < s * u.im → 0 < s * (1+u).im := fun h => by simpa using h
  have hdiv : ∀ {u : ℂ}, 0 < s * u.im → 1 + Complex.exp (-hexL2 r u) = u/(1+u) := by
    intro u hu
    exact one_add_exp_neg_hexL2 r (Complex.slitPlane_ne_zero (hsl_of (h1im hu)))
  have hdivim : ∀ {u : ℂ}, 0 < s * u.im → 0 < s * (u/(1+u)).im := by
    intro u hu
    rw [VOA.Huang.TensorCat.HexagonClose.im_div_one_add, mul_div_assoc']
    exact div_pos hu (Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero (hsl_of (h1im hu))))
  have hexpdiff : ∀ {u : ℂ}, 0 < s * u.im →
      0 < (-s) * (Complex.exp (hexL2 r u - hexL1 r u)).im := by
    intro u hu
    have hw := hdivim hu
    have hw0 : u/(1+u) ≠ 0 := by
      intro h0; rw [h0, Complex.zero_im, mul_zero] at hw; exact lt_irrefl _ hw
    have he : hexL2 r u - hexL1 r u = -Complex.log (u/(1+u)) := by
      rw [hexL1, hdiv hu]; ring
    rw [he, Complex.exp_neg, Complex.exp_log hw0, Complex.inv_im]
    have hN := Complex.normSq_pos.mpr hw0
    rw [show -s * (-(u/(1+u)).im / Complex.normSq (u/(1+u))) =
      s * (u/(1+u)).im / Complex.normSq (u/(1+u)) by ring]
    exact div_pos hw hN
  have hBΦ : ∀ u : ℂ, u.re < -1/2 → 0 < s * u.im →
      hexFB hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy J u = PhiT u := by
    intro u hre hu
    have h10 : 1+u ≠ 0 := Complex.slitPlane_ne_zero (hsl_of (h1im hu))
    have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero (hsl_of hu)
    have hlt : (hexL2 r u).re < (hexL1 r u).re := by
      rw [hexL1, Complex.add_re, Complex.log_re, hdiv hu, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hu0) (norm_ne_zero_iff.mpr h10)]
      rw [hexL2, Complex.add_re, Complex.log_re]
      have hk : (kap r).re = 0 := by rw [kap]; simp
      rw [hk, add_zero]
      have := norm_one_add_lt_norm' (r := u) hre
      have := Real.log_lt_log (norm_pos_iff.mpr h10) this
      linarith
    unfold hexFB
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [(completedLogProduct_eq_prodValue hC2 N₂ N₃ N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ h₃ h₁ hfgT hfgZX _ _ (fun n k hk => hK _ n k hk)
      (fun n l hl => hL _ n l hl) hy hz hx _ (β-j) hlt).2]
    exact hΦe j (hexL1 r u, hexL2 r u) hlt (hexpdiff hu)
  -- the glue hypotheses
  have hA : ∀ u, 1 < ‖1+u‖ → 1+u∈Complex.slitPlane →
      DifferentiableAt ℂ (hexFA hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β y z hx J) u :=
    fun u h1 hsl => differentiableAt_hexFA hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β hx hy hz J h1 hsl
  have hC : ∀ u, ‖1+u‖ < 1 → 0 < s*u.im →
      DifferentiableAt ℂ (hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy) u :=
    fun u h1 hu => differentiableAt_hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β hx hy hz h1
      (hsl_of (h1im hu))
  have hD : ∀ u, ‖u‖ < ‖1+u‖ → u∈Complex.slitPlane → 1+u∈Complex.slitPlane →
      DifferentiableAt ℂ (hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x y hz) u :=
    fun u h h0 h1 => differentiableAt_hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β hx hy hz h h0 h1
  have hΦ : ∀ u, 0 < s*u.im → DifferentiableAt ℂ PhiT u := by
    intro u hu
    have hsl1 := hsl_of (h1im hu)
    have hL2d : DifferentiableAt ℂ (hexL2 r) u :=
      (differentiableAt_log_one_add hsl1).add_const (kap r)
    have hL1d : DifferentiableAt ℂ (hexL1 r) u := by
      have hsl2 : 1 + Complex.exp (-hexL2 r u)∈Complex.slitPlane := by
        rw [hdiv hu]; exact hsl_of (hdivim hu)
      exact (((differentiableAt_const 1).add hL2d.neg.cexp).clog hsl2).add hL2d
    have hopen : IsOpen {p : ℂ × ℂ | 0 < (-s) * (Complex.exp (p.2-p.1)).im} :=
      isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_im.comp
        (Complex.continuous_exp.comp (continuous_snd.sub continuous_fst))))
    refine DifferentiableAt.fun_sum fun j _ => DifferentiableAt.mul
      (differentiableAt_transCoeff_log hsl1 j) ?_
    have hp : (hexL1 r u, hexL2 r u)∈{p : ℂ × ℂ | 0 < (-s) * (Complex.exp (p.2-p.1)).im} :=
      hexpdiff hu
    exact ((hΦd j).differentiableAt (hopen.mem_nhds hp)).comp u (hL1d.prodMk hL2d)
  have hAΦ : ∀ u, u.re < -2 → 1 < s*u.im →
      hexFA hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β y z hx J u = PhiT u := fun u hre hu =>
    (hexFA_eq_hexFB hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β hx hy hz J (hexAB_mem hs hrs hre (by linarith))).trans
      (hBΦ u (by linarith) (by linarith))
  have hCΦ : ∀ u ∈ Metric.ball (-3/4 : ℂ) (1/4), 0 < s*u.im →
      hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy u = PhiT u := fun u hb hu =>
    (hexFB_eq_hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r hs hrs f β hx hy hz J hJT hb hu).symm.trans
      (hBΦ u (disc_re_bounds hb).2 hu)
  have hCD : ∀ u ∈ Metric.ball (-1/2 : ℂ) (1/2), -1/2 < u.re → 0 < s*u.im →
      hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy u =
        hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x y hz u := fun u hb hre hu =>
    hexFC_eq_hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β hx hy hz (hexCD_mem hs hrs hb hre hu)
      (hexCD_branch r (Complex.slitPlane_ne_zero (hsl_of hu))
        (by intro h0; have := h1im hu; rw [h0, mul_zero] at this; exact lt_irrefl _ this))
  have hglue := glue_four hs _ _ _ PhiT hA hC hD hΦ hAΦ hCΦ hCD
  -- the identity theorem in the iterate coordinate
  have hdiff : ∀ (G : RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ]
      RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW), ∀ t ∈ overlapDomain,
      DifferentiableAt ℂ (fun t => completedLogIterate N₁ N₂ N₃
        (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) (tensorModule hC2 N₁ N₂ h₁ h₂)
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
        (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) t 0 c β (f ∘ₗ G) x y ⟨z,hz⟩) t := by
    intro G t ht
    exact differentiableAt_completedLogIterate_comp hC2 N₁ N₂ N₃
      (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) (tensorModule hC2 N₁ N₂ h₁ h₂) h₁ h₂ h₃
      (tensorModule_finGen hC2 _ N₃ (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
      (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) _ _ hx hy hz _ _ (ℓ₀ := fun t => t)
      (ℓ₂ := fun _ => 0) differentiableAt_id (differentiableAt_const _)
      (by simpa using ht.1)
  have hO : IsOpen (overlapDomain ∩ {t : ℂ | t.re < -1}) :=
    isOpen_overlapDomain.inter (isOpen_lt Complex.continuous_re continuous_const)
  refine eqOn_of_convex_open convex_overlapDomain isOpen_overlapDomain
    (hdiff _) (hdiff _) hO Set.inter_subset_left (z₀ := -2) ?_ (fun t ht' => ?_) ht
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · norm_num
    · have : (-2 : ℂ).im = 0 := by simp
      rw [this, abs_zero]; positivity
    · show (-2 : ℂ).re < -1; norm_num
  obtain ⟨ht1, ht2⟩ := ht'
  have ht2' : t.re < -1 := ht2
  have hsmall : ‖Complex.exp t‖ < 1/2 := by
    rw [Complex.norm_exp]
    have : Real.exp t.re < Real.exp (-1) := Real.exp_lt_exp.mpr ht2'
    have he : Real.exp (-1) < 1/2 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg]
      rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  rw [hexLeft_iterate hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β hx hy hz J hJL ht1,
    hexRight_iterate hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β hx hy hz ht1 hsmall]
  exact hglue _ (re_exp_pos_of_overlap ht1)

end VOA.C2Rigid.LocalInjective
