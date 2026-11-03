import VOA.Huang.HuangODEThreeSepRing

/-!
# The coefficient ring of the iterate-in-product (middle) chart

For `⟨f, 𝒴_A(a, z₁) 𝒴_B(𝒴_C(b, z₀) c, z₂) e⟩` in the chart `x = z₂/z₁`, `y = z₀/z₂`, the
collision divisors are `x = 1` (`a`–`c`), `y = -1` (`b`–`e`) and `x(1+y) = 1` (`a`–`b`).

* `ιm` — the ring map `t ↦ x(1+y)`; `c2 (ιm f) i j = coeff i f · C(i,j)`;
* `midRing = ℂ[x, y, (1-x)⁻¹, (1+y)⁻¹, (1-x-xy)⁻¹]`, Noetherian;
* `MidBound r` — coefficient bounds `G R₁^i R₂^j` on the region `R₂ > 1`, `R₁ > 1 + 1/R₂`
  (the polydiscs of radii `1/R₁, 1/R₂` avoiding `x(1+y) = 1`); `midBound_of_mem_midRing`;
* `innerRegularMid_of_fg` — the inner equation from finite generation over `midRing`.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open PowerSeries VOA.Huang.UniformConv VOA.Huang.FuchsianODE
open scoped BigOperators

/-- `t ↦ x(1+y)`. -/
def ιm : PowerSeries ℂ →+* PS2 := (PowerSeries.rescale (1 + X : PowerSeries ℂ)).comp ιx

theorem coeff_one_add_X_pow' (i j : ℕ) :
    coeff j ((1 + X : PowerSeries ℂ) ^ i) = (i.choose j : ℂ) := by
  have h : ((1 + X : PowerSeries ℂ)) ^ i = (((1 + Polynomial.X) ^ i : Polynomial ℂ) :
      PowerSeries ℂ) := by
    simp [Polynomial.coe_X]
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem c2_ιm (f : PowerSeries ℂ) (i j : ℕ) :
    c2 (ιm f) i j = coeff i f * (i.choose j : ℂ) := by
  unfold c2 ιm
  rw [RingHom.comp_apply, coeff_rescale]
  simp only [ιx, coeff_map]
  rw [coeff_mul_C, coeff_one_add_X_pow', mul_comm]

theorem c2_ιm_mul (f : PowerSeries ℂ) (Q : PS2) (m n : ℕ) :
    c2 (ιm f * Q) m n = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      coeff i f * (i.choose j : ℂ) * c2 Q (m - i) (n - j) := by
  rw [c2_mul]
  simp only [c2_ιm]

theorem ιm_X : ιm X = (X : PS2) * PowerSeries.C (1 + X : PowerSeries ℂ) := by
  simp only [ιm, RingHom.comp_apply, ιx_X]
  rw [rescale_X, mul_comm]

/-- `ℂ[x, y, (1-x)⁻¹, (1+y)⁻¹, (1-x-xy)⁻¹]` inside `ℂ⟦x,y⟧`. -/
def midRing : Subalgebra ℂ PS2 :=
  Algebra.adjoin ℂ ({ιx X, ιy X, ιx (HuangODEAlgebra.geom 1), ιy (HuangODEAlgebra.geom (-1)),
    ιm (HuangODEAlgebra.geom 1)} : Set PS2)

instance : IsNoetherianRing midRing := by
  classical
  have hfg : midRing.FG := by
    have := Subalgebra.fg_adjoin_finset (R := ℂ) ({ιx X, ιy X, ιx (HuangODEAlgebra.geom 1),
      ιy (HuangODEAlgebra.geom (-1)), ιm (HuangODEAlgebra.geom 1)} : Finset PS2)
    simpa [midRing] using this
  haveI : Algebra.FiniteType ℂ midRing := (Subalgebra.fg_iff_finiteType _).mp hfg
  exact Algebra.FiniteType.isNoetherianRing ℂ midRing

theorem mid_ιx_X_mem : ιx X ∈ midRing := Algebra.subset_adjoin (by simp)
theorem mid_ιy_X_mem : ιy X ∈ midRing := Algebra.subset_adjoin (by simp)
theorem mid_ιx_geom_mem : ιx (HuangODEAlgebra.geom 1) ∈ midRing :=
  Algebra.subset_adjoin (by simp)
theorem mid_ιy_geom_mem : ιy (HuangODEAlgebra.geom (-1)) ∈ midRing :=
  Algebra.subset_adjoin (by simp)
theorem mid_ιm_geom_mem : ιm (HuangODEAlgebra.geom 1) ∈ midRing :=
  Algebra.subset_adjoin (by simp)

theorem mid_monomial_mem (a b : ℕ) :
    (X : PS2) ^ a * PowerSeries.C ((X : PowerSeries ℂ) ^ b) ∈ midRing := by
  rw [map_pow, ← ιx_X, ← ιy_X]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ mid_ιx_X_mem _)
    (Subalgebra.pow_mem _ mid_ιy_X_mem _)

theorem mid_ιx_binom_mem (k : ℕ) : ιx (X * HuangODEAlgebra.binomSeries 1 k) ∈ midRing := by
  rw [HuangODEAlgebra.binomSeries_eq, map_mul, map_mul, map_pow, map_pow]
  exact Subalgebra.mul_mem _ mid_ιx_X_mem (Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ mid_ιx_X_mem _) (Subalgebra.pow_mem _ mid_ιx_geom_mem _))

theorem mid_ιy_binom_mem (k : ℕ) :
    ιy (X * HuangODEAlgebra.binomSeries (-1) k) ∈ midRing := by
  rw [HuangODEAlgebra.binomSeries_eq, map_mul, map_mul, map_pow, map_pow]
  exact Subalgebra.mul_mem _ mid_ιy_X_mem (Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ mid_ιy_X_mem _) (Subalgebra.pow_mem _ mid_ιy_geom_mem _))

theorem mid_ιm_geom_pow_mem (k : ℕ) : ιm (HuangODEAlgebra.geom 1 ^ k) ∈ midRing := by
  rw [map_pow]; exact Subalgebra.pow_mem _ mid_ιm_geom_mem _

theorem mul_mem_of_midRing (NN : Submodule midRing PS2) {r q : PS2} (hr : r ∈ midRing)
    (hq : q ∈ NN) : r * q ∈ NN := by
  have h := NN.smul_mem ⟨r, hr⟩ hq
  rwa [Subalgebra.smul_def] at h

theorem smul_mem_of_midRing (NN : Submodule midRing PS2) (a : ℂ) {q : PS2} (hq : q ∈ NN) :
    a • q ∈ NN := by
  have h := NN.smul_mem (algebraMap ℂ midRing a) hq
  rwa [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul] at h

/-! ## Coefficient bounds on the admissible region -/

/-- The admissible rates: `R₂ > 1`, `R₁ > 1 + 1/R₂`. -/
def MidAdm (R₁ R₂ : ℝ) : Prop := 1 < R₂ ∧ 1 + 1 / R₂ < R₁

theorem MidAdm.one_lt₁ {R₁ R₂ : ℝ} (h : MidAdm R₁ R₂) : 1 < R₁ := by
  have : 0 < 1 / R₂ := by have := h.1; positivity
  linarith [h.2]

/-- Coefficients bounded by `G R₁^i R₂^j` on the admissible region. -/
def MidBound (r : PS2) : Prop :=
  ∀ R₁ R₂ : ℝ, MidAdm R₁ R₂ → ∃ G : ℝ, ∀ i j, ‖c2 r i j‖ ≤ G * R₁ ^ i * R₂ ^ j

/-- Shrinking inside the admissible region. -/
theorem MidAdm.exists_shrink {R₁ R₂ : ℝ} (h : MidAdm R₁ R₂) :
    ∃ R₁' R₂' : ℝ, MidAdm R₁' R₂' ∧ R₁' < R₁ ∧ R₂' < R₂ := by
  obtain ⟨h₂, h₁⟩ := h
  have hR₂0 : 0 < R₂ := by linarith
  set ε : ℝ := R₁ - (1 + 1 / R₂) with hε
  have hε0 : 0 < ε := by linarith
  set R₁' : ℝ := R₁ - ε / 2
  set δ : ℝ := min (ε / 4) ((1 - 1 / R₂) / 2) with hδ
  have hinv1 : 1 / R₂ < 1 := by rw [div_lt_one hR₂0]; exact h₂
  have hinv0 : 0 < 1 / R₂ := by positivity
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  set R₂' : ℝ := 1 / (1 / R₂ + δ)
  have hden : 0 < 1 / R₂ + δ := by linarith
  have hden1 : 1 / R₂ + δ < 1 := by
    have : δ ≤ (1 - 1 / R₂) / 2 := min_le_right _ _
    linarith
  refine ⟨R₁', R₂', ⟨?_, ?_⟩, by simp only [R₁']; linarith, ?_⟩
  · simp only [R₂']; rw [lt_div_iff₀ hden]; linarith
  · simp only [R₂', R₁']
    rw [one_div_one_div]
    have : δ ≤ ε / 4 := min_le_left _ _
    linarith
  · simp only [R₂']
    rw [div_lt_iff₀ hden]
    have : 1 / R₂ * R₂ = 1 := by field_simp
    nlinarith

theorem midBound_of_le_one {r : PS2} (h : ∀ i j, ‖c2 r i j‖ ≤ 1) : MidBound r := by
  intro R₁ R₂ hR
  have h1 : 1 < R₁ := hR.one_lt₁
  refine ⟨1, fun i j => le_trans (h i j) ?_⟩
  have h1' : 1 ≤ R₁ ^ i := one_le_pow₀ h1.le
  have h2 : 1 ≤ R₂ ^ j := one_le_pow₀ hR.1.le
  nlinarith

theorem MidBound.add {r r' : PS2} (h : MidBound r) (h' : MidBound r') : MidBound (r + r') := by
  intro R₁ R₂ hR
  obtain ⟨G, hG⟩ := h R₁ R₂ hR
  obtain ⟨G', hG'⟩ := h' R₁ R₂ hR
  refine ⟨G + G', fun i j => ?_⟩
  rw [c2_add]
  refine le_trans (norm_add_le _ _) ?_
  have := hG i j; have := hG' i j
  linarith

theorem MidBound.const (a : ℂ) : MidBound (a • (1 : PS2)) := by
  intro R₁ R₂ hR
  have h1 : 1 < R₁ := hR.one_lt₁
  obtain ⟨G, hG⟩ := BidiscBound.const a (min R₁ R₂) (lt_min h1 hR.1)
  have hG0 : 0 ≤ G := by
    have := hG 0 0; simp only [pow_zero, mul_one] at this; exact le_trans (norm_nonneg _) this
  refine ⟨G, fun i j => le_trans (hG i j) ?_⟩
  have e1 : min R₁ R₂ ^ i ≤ R₁ ^ i :=
    pow_le_pow_left₀ (le_trans zero_le_one (le_min h1.le hR.1.le)) (min_le_left _ _) i
  have e2 : min R₁ R₂ ^ j ≤ R₂ ^ j :=
    pow_le_pow_left₀ (le_trans zero_le_one (le_min h1.le hR.1.le)) (min_le_right _ _) j
  have : 0 ≤ min R₁ R₂ ^ i := pow_nonneg (le_trans zero_le_one (le_min h1.le hR.1.le)) i
  have : 0 ≤ min R₁ R₂ ^ j := pow_nonneg (le_trans zero_le_one (le_min h1.le hR.1.le)) j
  calc G * min R₁ R₂ ^ i * min R₁ R₂ ^ j ≤ G * R₁ ^ i * min R₁ R₂ ^ j := by gcongr
    _ ≤ G * R₁ ^ i * R₂ ^ j := by gcongr

theorem MidBound.mul {r r' : PS2} (h : MidBound r) (h' : MidBound r') : MidBound (r * r') := by
  intro R₁ R₂ hR
  obtain ⟨R₁', R₂', hR', h1, h2⟩ := hR.exists_shrink
  have hR₁'0 : 0 < R₁' := lt_trans zero_lt_one hR'.one_lt₁
  have hR₂'0 : 0 < R₂' := lt_trans zero_lt_one hR'.1
  obtain ⟨G, hG⟩ := h R₁' R₂' hR'
  obtain ⟨G', hG'⟩ := h' R₁' R₂' hR'
  have hG0 : 0 ≤ G := by
    have := hG 0 0; simp only [pow_zero, mul_one] at this; exact le_trans (norm_nonneg _) this
  have hG0' : 0 ≤ G' := by
    have := hG' 0 0; simp only [pow_zero, mul_one] at this; exact le_trans (norm_nonneg _) this
  have hR₁0 : 0 < R₁ := by linarith
  have hR₂0 : 0 < R₂ := by linarith
  obtain ⟨C₁, hC₁⟩ := exists_bound_succ_mul_pow (t := R₁' / R₁) (by positivity)
    ((div_lt_one hR₁0).mpr h1)
  obtain ⟨C₂, hC₂⟩ := exists_bound_succ_mul_pow (t := R₂' / R₂) (by positivity)
    ((div_lt_one hR₂0).mpr h2)
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) (hC₁ 0)
  have hC₂0 : 0 ≤ C₂ := le_trans (by positivity) (hC₂ 0)
  refine ⟨G * G' * C₁ * C₂, fun m n => ?_⟩
  rw [c2_mul]
  have hterm : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (n + 1),
      ‖c2 r i j * c2 r' (m - i) (n - j)‖ ≤ G * G' * R₁' ^ m * R₂' ^ n := by
    intro i hi j hj
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [norm_mul]
    calc ‖c2 r i j‖ * ‖c2 r' (m - i) (n - j)‖
        ≤ (G * R₁' ^ i * R₂' ^ j) * (G' * R₁' ^ (m - i) * R₂' ^ (n - j)) :=
          mul_le_mul (hG i j) (hG' _ _) (norm_nonneg _) (by positivity)
      _ = G * G' * (R₁' ^ i * R₁' ^ (m - i)) * (R₂' ^ j * R₂' ^ (n - j)) := by ring
      _ = G * G' * R₁' ^ m * R₂' ^ n := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hi', Nat.add_sub_cancel' hj']
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum fun i hi =>
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => hterm i hi j hj)) ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have hm := hC₁ m
  have hn := hC₂ n
  have hRm : R₁' ^ m = (R₁' / R₁) ^ m * R₁ ^ m := by
    rw [div_pow, div_mul_cancel₀]; positivity
  have hRn : R₂' ^ n = (R₂' / R₂) ^ n * R₂ ^ n := by
    rw [div_pow, div_mul_cancel₀]; positivity
  rw [hRm, hRn]
  have : 0 ≤ R₁ ^ m := by positivity
  have : 0 ≤ R₂ ^ n := by positivity
  calc ((m : ℝ) + 1) * (((n : ℝ) + 1) *
        (G * G' * ((R₁' / R₁) ^ m * R₁ ^ m) * ((R₂' / R₂) ^ n * R₂ ^ n)))
      = G * G' * (((m : ℝ) + 1) * (R₁' / R₁) ^ m) * (((n : ℝ) + 1) * (R₂' / R₂) ^ n) *
          R₁ ^ m * R₂ ^ n := by ring
    _ ≤ G * G' * C₁ * C₂ * R₁ ^ m * R₂ ^ n := by gcongr

/-- `(1 - x(1+y))⁻¹` on the admissible region: `C(i,j) ≤ (1 + 1/R₂)^i R₂^j`. -/
theorem midBound_ιm_geom : MidBound (ιm (HuangODEAlgebra.geom 1)) := by
  intro R₁ R₂ hR
  have hR₂0 : 0 < R₂ := lt_trans zero_lt_one hR.1
  refine ⟨1, fun i j => ?_⟩
  rw [c2_ιm]
  simp only [HuangODEAlgebra.geom, coeff_mk, one_pow, one_mul, Complex.norm_natCast]
  -- `C(i,j) R₂^(-j) ≤ (1 + 1/R₂)^i ≤ R₁^i`
  set t : ℝ := 1 / R₂ with ht
  have ht0 : 0 ≤ t := by positivity
  have e : (1 + t) ^ i = ∑ k ∈ Finset.range (i + 1), t ^ k * (i.choose k : ℝ) := by
    rw [add_comm, add_pow]; simp
  have hsum : (i.choose j : ℝ) * t ^ j ≤ (1 + t) ^ i := by
    rw [e]
    by_cases hj : j ≤ i
    · have := Finset.single_le_sum (f := fun k => t ^ k * (i.choose k : ℝ))
        (fun k _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      simp only at this
      linarith [mul_comm ((i.choose j : ℝ)) (t ^ j)]
    · rw [Nat.choose_eq_zero_of_lt (not_le.mp hj), Nat.cast_zero, zero_mul]
      exact Finset.sum_nonneg fun k _ => by positivity
  have hle : (1 + t) ^ i ≤ R₁ ^ i := pow_le_pow_left₀ (by positivity) hR.2.le i
  have hRj : (0 : ℝ) < R₂ ^ j := by positivity
  have htj : t ^ j * R₂ ^ j = 1 := by rw [ht, ← mul_pow]; field_simp; simp
  have key : (i.choose j : ℝ) ≤ (1 + t) ^ i * R₂ ^ j := by
    calc (i.choose j : ℝ) = (i.choose j : ℝ) * t ^ j * R₂ ^ j := by
          rw [mul_assoc, htj, mul_one]
      _ ≤ (1 + t) ^ i * R₂ ^ j := mul_le_mul_of_nonneg_right hsum hRj.le
  calc (i.choose j : ℝ) ≤ (1 + t) ^ i * R₂ ^ j := key
    _ ≤ R₁ ^ i * R₂ ^ j := mul_le_mul_of_nonneg_right hle hRj.le

theorem midBound_generators :
    MidBound (ιx X) ∧ MidBound (ιy X) ∧ MidBound (ιx (HuangODEAlgebra.geom 1)) ∧
      MidBound (ιy (HuangODEAlgebra.geom (-1))) ∧ MidBound (ιm (HuangODEAlgebra.geom 1)) := by
  refine ⟨midBound_of_le_one fun i j => ?_, midBound_of_le_one fun i j => ?_,
    midBound_of_le_one fun i j => ?_, midBound_of_le_one fun i j => ?_, midBound_ιm_geom⟩
  · rw [c2_ιx, coeff_X]; split_ifs <;> simp
  · rw [c2_ιy, coeff_X]; split_ifs <;> simp
  · rw [c2_ιx]; split_ifs <;> simp [HuangODEAlgebra.geom]
  · rw [c2_ιy]; split_ifs <;> simp [HuangODEAlgebra.geom]

/-- **Every element of the middle-chart ring is holomorphic on the admissible polydiscs.** -/
theorem midBound_of_mem_midRing {r : PS2} (hr : r ∈ midRing) : MidBound r := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := midBound_generators
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one]; exact MidBound.const a
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/-- The inner equation over `midRing`, with admissible-region coefficient bounds. -/
def InnerRegularMid (lam : ℂ) (c : ℕ → ℕ → ℂ) : Prop :=
  ∃ (s : ℕ) (g : ℕ → ℕ → ℕ → ℂ), 1 ≤ s ∧
    (∀ R₁ R₂ : ℝ, MidAdm R₁ R₂ → ∃ G : ℝ, ∀ k < s, ∀ i j, ‖g k i j‖ ≤ G * R₁ ^ i * R₂ ^ j) ∧
    DiagonalFuchsian (fun _ n => lam + n) s g c

theorem thetaY_iter_mem_mid (NN : Submodule midRing PS2) (Q : ℕ → PS2) (lam : ℕ → ℂ)
    (hQ : ∀ j, Q (j + 1) = thetaY (lam j) (Q j)) (hmem : ∀ j, Q j ∈ NN) (μ : ℂ) :
    ∀ i j, (thetaY μ)^[i] (Q j) ∈ NN := by
  intro i
  induction i with
  | zero => intro j; simpa using hmem j
  | succ i ih =>
    intro j
    rw [Function.iterate_succ_apply]
    have e : thetaY μ (Q j) = Q (j + 1) + (μ - lam j) • Q j := by
      rw [hQ, ← thetaY_add_const, add_sub_cancel]
    rw [e, thetaY_iterate_add, thetaY_iterate_smul]
    exact NN.add_mem (ih (j + 1)) (smul_mem_of_midRing NN _ (ih j))

theorem exists_uniform_midBound_fin {s : ℕ} {r : ℕ → PS2} (hr : ∀ k < s, MidBound (r k))
    (R₁ R₂ : ℝ) (hR : MidAdm R₁ R₂) :
    ∃ G : ℝ, ∀ k < s, ∀ i j, ‖c2 (r k) i j‖ ≤ G * R₁ ^ i * R₂ ^ j := by
  have hR₁ : 0 < R₁ := lt_trans zero_lt_one hR.one_lt₁
  have hR₂ : 0 < R₂ := lt_trans zero_lt_one hR.1
  induction s with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ s ih =>
    obtain ⟨G, hG⟩ := ih (fun k hk => hr k (by omega))
    obtain ⟨G', hG'⟩ := hr s (by omega) R₁ R₂ hR
    refine ⟨max G G', fun k hk i j => ?_⟩
    have hRi : 0 ≤ R₁ ^ i * R₂ ^ j := by positivity
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · refine le_trans (hG k h i j) ?_
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRi
    · refine le_trans (hG' i j) ?_
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hRi

/-- **The inner equation from finite generation over the middle-chart ring.** -/
theorem innerRegularMid_of_fg (NN : Submodule midRing PS2) (hN : NN.FG) {Q : PS2} {μ : ℂ}
    (h : ∀ j, (thetaY μ)^[j] Q ∈ NN) (lam : ℂ) : InnerRegularMid lam (c2 Q) := by
  classical
  have hmem : ∀ j, (thetaY lam)^[j] Q ∈ NN := by
    have key := thetaY_iter_mem_mid NN (fun j => (thetaY μ)^[j] Q) (fun _ => μ)
      (fun j => Function.iterate_succ_apply' _ _ _) h lam
    intro j; simpa using key j 0
  haveI : Module.Finite midRing NN := Module.Finite.iff_fg.mpr hN
  obtain ⟨m, r, hr⟩ := VOA.Huang.MatrixCoeffODE.exists_monic_relation (R := midRing)
    (fun j => (⟨(thetaY lam)^[j] Q, hmem j⟩ : NN))
  have hr' : (thetaY lam)^[m] Q =
      ∑ k ∈ Finset.range m, (r k : PS2) * (thetaY lam)^[k] Q := by
    have := congrArg Subtype.val hr
    simpa [Submodule.coe_sum, Subalgebra.smul_def] using this
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hQ : Q = 0 := by simpa using hr'
    refine ⟨1, fun _ _ _ => 0, le_rfl, fun R₁ R₂ _ => ⟨0, fun k _ i j => by simp⟩, ?_⟩
    intro a b
    simp [hQ, c2_zero]
  · refine ⟨m, fun k => c2 (r k), hm, fun R₁ R₂ hR => ?_, ?_⟩
    · exact exists_uniform_midBound_fin (fun k _ => midBound_of_mem_midRing (r k).2) R₁ R₂ hR
    · apply diagonalFuchsian_of_conv
      intro a b
      have hc := congrArg (fun P => c2 P a b) hr'
      simp only at hc
      unfold diagPow
      rw [← c2_thetaY_iterate, hc, c2_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [c2_mul_eq_conv]
      congr 1
      funext i j
      rw [c2_thetaY_iterate]

end VOA.Huang.FivePointSep
