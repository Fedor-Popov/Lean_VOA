import VOA.Huang.FivePointSepAnalytic
import VOA.Huang.HuangODEAlgebra
import VOA.Huang.UniformConvSeries

/-!
# The bivariate regular coefficient ring and the inner Euler operator

Double power series are `PowerSeries (PowerSeries ℂ)`: the outer variable `x` (first
index) and the inner variable `y = C X` (second index), as in
`HuangODEThree.normalizedSeries`. For products of three intertwiners in the chart
`x = z₂/z₁`, `y = z₃/z₂` the collision divisors are `x = 1`, `y = 1`, `xy = 1`.

* `ιx`, `ιy`, `ιxy` — the ring maps `ℂ⟦t⟧ → ℂ⟦x⟧⟦y⟧`, `t ↦ x`, `t ↦ y`, `t ↦ xy`;
* `sepRing = ℂ[x, y, (1-x)⁻¹, (1-y)⁻¹, (1-xy)⁻¹] ⊆ ℂ⟦x,y⟧`, Noetherian;
* `BidiscBound r` (every rate `R > 1` bounds the coefficients) holds on `sepRing`
  (`bidiscBound_of_mem_sepRing`): its elements are holomorphic on the open unit bidisc;
* `thetaY μ` — the Euler operator `y∂_y + μ`;
* `diagonalFuchsian_of_fg` — if every `thetaY`-iterate of `Q` lies in one finitely
  generated `sepRing`-submodule, the coefficient array of `Q` satisfies a monic
  `DiagonalFuchsian` equation in the second index with `sepRing` coefficients.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open PowerSeries VOA.Huang.UniformConv VOA.Huang.FuchsianODE
open scoped BigOperators

/-- Double power series: outer variable `x`, inner variable `y`. -/
abbrev PS2 : Type := PowerSeries (PowerSeries ℂ)

/-- The `(m,n)` coefficient (power `x^m y^n`). -/
def c2 (Q : PS2) (m n : ℕ) : ℂ := coeff n (coeff m Q)

theorem c2_add (Q Q' : PS2) (m n : ℕ) : c2 (Q + Q') m n = c2 Q m n + c2 Q' m n := by
  simp [c2]

theorem c2_sub (Q Q' : PS2) (m n : ℕ) : c2 (Q - Q') m n = c2 Q m n - c2 Q' m n := by
  simp [c2]

theorem c2_smul (a : ℂ) (Q : PS2) (m n : ℕ) : c2 (a • Q) m n = a * c2 Q m n := by
  simp [c2]

theorem c2_zero (m n : ℕ) : c2 0 m n = 0 := by simp [c2]

theorem c2_sum {ι : Type*} (S : Finset ι) (Q : ι → PS2) (m n : ℕ) :
    c2 (∑ i ∈ S, Q i) m n = ∑ i ∈ S, c2 (Q i) m n := by
  simp [c2, map_sum]

theorem PS2.ext {Q Q' : PS2} (h : ∀ m n, c2 Q m n = c2 Q' m n) : Q = Q' := by
  ext m n; exact h m n

/-- Cauchy product of double series in coefficient form. -/
theorem c2_mul (A Q : PS2) (m n : ℕ) :
    c2 (A * Q) m n = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      c2 A i j * c2 Q (m - i) (n - j) := by
  unfold c2
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- `conv` of `UniformConvSeries` is the coefficient array of a product. -/
theorem c2_mul_eq_conv (A Q : PS2) (m n : ℕ) :
    c2 (A * Q) m n = conv (c2 A) (c2 Q) m n := by
  rw [mul_comm, c2_mul]
  unfold conv
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## The three embeddings -/

/-- `t ↦ x`. -/
def ιx : PowerSeries ℂ →+* PS2 := PowerSeries.map PowerSeries.C

/-- `t ↦ y`. -/
def ιy : PowerSeries ℂ →+* PS2 := PowerSeries.C

/-- `t ↦ xy`. -/
def ιxy : PowerSeries ℂ →+* PS2 := (PowerSeries.rescale (X : PowerSeries ℂ)).comp ιx

theorem c2_ιx (f : PowerSeries ℂ) (i j : ℕ) :
    c2 (ιx f) i j = if j = 0 then coeff i f else 0 := by
  simp [c2, ιx, coeff_map, coeff_C]

theorem c2_ιy (f : PowerSeries ℂ) (i j : ℕ) :
    c2 (ιy f) i j = if i = 0 then coeff j f else 0 := by
  unfold c2 ιy
  rw [coeff_C]
  split_ifs <;> simp

theorem c2_ιxy (f : PowerSeries ℂ) (i j : ℕ) :
    c2 (ιxy f) i j = if j = i then coeff i f else 0 := by
  unfold c2 ιxy
  rw [RingHom.comp_apply, coeff_rescale]
  simp only [ιx, coeff_map]
  rw [coeff_mul_C, coeff_X_pow]
  split_ifs <;> simp

theorem c2_ιx_mul (f : PowerSeries ℂ) (Q : PS2) (m n : ℕ) :
    c2 (ιx f * Q) m n = ∑ i ∈ Finset.range (m + 1), coeff i f * c2 Q (m - i) n := by
  rw [c2_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0]
  · simp [c2_ιx]
  · intro j _ hj; simp [c2_ιx, hj]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h

theorem c2_ιy_mul (f : PowerSeries ℂ) (Q : PS2) (m n : ℕ) :
    c2 (ιy f * Q) m n = ∑ j ∈ Finset.range (n + 1), coeff j f * c2 Q m (n - j) := by
  rw [c2_mul, Finset.sum_eq_single 0]
  · simp [c2_ιy]
  · intro i _ hi; simp [c2_ιy, hi]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h

theorem c2_ιxy_mul (f : PowerSeries ℂ) (Q : PS2) (m n : ℕ) :
    c2 (ιxy f * Q) m n = ∑ i ∈ Finset.range (m + 1),
      if i ≤ n then coeff i f * c2 Q (m - i) (n - i) else 0 := by
  rw [c2_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hin
  · rw [Finset.sum_eq_single i]
    · simp [c2_ιxy]
    · intro j _ hj; simp [c2_ιxy, hj]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · refine Finset.sum_eq_zero fun j hj => ?_
    have : j ≠ i := by have := Finset.mem_range.mp hj; omega
    simp [c2_ιxy, this]

theorem ιx_X : ιx X = (X : PS2) := by simp [ιx]

theorem ιy_X : ιy X = PowerSeries.C (X : PowerSeries ℂ) := rfl

theorem ιxy_X : ιxy X = (X : PS2) * PowerSeries.C (X : PowerSeries ℂ) := by
  simp only [ιxy, RingHom.comp_apply, ιx_X]
  rw [rescale_X, mul_comm]

/-! ## The ring -/

/-- `ℂ[x, y, (1-x)⁻¹, (1-y)⁻¹, (1-xy)⁻¹]` inside `ℂ⟦x,y⟧`. -/
def sepRing : Subalgebra ℂ PS2 :=
  Algebra.adjoin ℂ ({ιx X, ιy X, ιx (HuangODEAlgebra.geom 1), ιy (HuangODEAlgebra.geom 1),
    ιxy (HuangODEAlgebra.geom 1)} : Set PS2)

instance : IsNoetherianRing sepRing := by
  classical
  have hfg : sepRing.FG := by
    have := Subalgebra.fg_adjoin_finset (R := ℂ) ({ιx X, ιy X, ιx (HuangODEAlgebra.geom 1),
      ιy (HuangODEAlgebra.geom 1), ιxy (HuangODEAlgebra.geom 1)} : Finset PS2)
    simpa [sepRing] using this
  haveI : Algebra.FiniteType ℂ sepRing := (Subalgebra.fg_iff_finiteType _).mp hfg
  exact Algebra.FiniteType.isNoetherianRing ℂ sepRing

theorem ιx_X_mem : ιx X ∈ sepRing := Algebra.subset_adjoin (by simp)
theorem ιy_X_mem : ιy X ∈ sepRing := Algebra.subset_adjoin (by simp)
theorem ιx_geom_mem : ιx (HuangODEAlgebra.geom 1) ∈ sepRing := Algebra.subset_adjoin (by simp)
theorem ιy_geom_mem : ιy (HuangODEAlgebra.geom 1) ∈ sepRing := Algebra.subset_adjoin (by simp)
theorem ιxy_geom_mem : ιxy (HuangODEAlgebra.geom 1) ∈ sepRing :=
  Algebra.subset_adjoin (by simp)

theorem ιxy_X_mem : ιxy X ∈ sepRing := by
  rw [ιxy_X, ← ιx_X, ← ιy_X]
  exact Subalgebra.mul_mem _ ιx_X_mem ιy_X_mem

theorem monomial_mem (a b : ℕ) :
    (X : PS2) ^ a * PowerSeries.C ((X : PowerSeries ℂ) ^ b) ∈ sepRing := by
  rw [map_pow, ← ιx_X, ← ιy_X]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ιx_X_mem _) (Subalgebra.pow_mem _ ιy_X_mem _)

/-- `x · Σ C(i,k) xⁱ` and its `y`, `xy` analogues lie in the ring. -/
theorem ιx_binom_mem (k : ℕ) : ιx (X * HuangODEAlgebra.binomSeries 1 k) ∈ sepRing := by
  rw [HuangODEAlgebra.binomSeries_eq, map_mul, map_mul, map_pow, map_pow]
  exact Subalgebra.mul_mem _ ιx_X_mem (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ιx_X_mem _)
    (Subalgebra.pow_mem _ ιx_geom_mem _))

theorem ιy_binom_mem (k : ℕ) : ιy (X * HuangODEAlgebra.binomSeries 1 k) ∈ sepRing := by
  rw [HuangODEAlgebra.binomSeries_eq, map_mul, map_mul, map_pow, map_pow]
  exact Subalgebra.mul_mem _ ιy_X_mem (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ιy_X_mem _)
    (Subalgebra.pow_mem _ ιy_geom_mem _))

theorem ιxy_binom_mem (k : ℕ) : ιxy (X * HuangODEAlgebra.binomSeries 1 k) ∈ sepRing := by
  rw [HuangODEAlgebra.binomSeries_eq, map_mul, map_mul, map_pow, map_pow]
  exact Subalgebra.mul_mem _ ιxy_X_mem (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ιxy_X_mem _)
    (Subalgebra.pow_mem _ ιxy_geom_mem _))

theorem mul_mem_of_sepRing (NN : Submodule sepRing PS2) {r q : PS2} (hr : r ∈ sepRing)
    (hq : q ∈ NN) : r * q ∈ NN := by
  have h := NN.smul_mem ⟨r, hr⟩ hq
  rwa [Subalgebra.smul_def] at h

theorem smul_mem_of_sepRing (NN : Submodule sepRing PS2) (a : ℂ) {q : PS2} (hq : q ∈ NN) :
    a • q ∈ NN := by
  have h := NN.smul_mem (algebraMap ℂ sepRing a) hq
  rwa [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul] at h

/-! ## Coefficient bounds on the ring -/

/-- Coefficients bounded by `G R^(i+j)` at every rate `R > 1`. -/
def BidiscBound (r : PS2) : Prop :=
  ∀ R : ℝ, 1 < R → ∃ G : ℝ, ∀ i j, ‖c2 r i j‖ ≤ G * R ^ i * R ^ j

theorem bidiscBound_of_le_one {r : PS2} (h : ∀ i j, ‖c2 r i j‖ ≤ 1) : BidiscBound r := by
  intro R hR
  refine ⟨1, fun i j => le_trans (h i j) ?_⟩
  have h1 : 1 ≤ R ^ i := one_le_pow₀ hR.le
  have h2 : 1 ≤ R ^ j := one_le_pow₀ hR.le
  nlinarith

theorem BidiscBound.add {r r' : PS2} (h : BidiscBound r) (h' : BidiscBound r') :
    BidiscBound (r + r') := by
  intro R hR
  obtain ⟨G, hG⟩ := h R hR
  obtain ⟨G', hG'⟩ := h' R hR
  refine ⟨G + G', fun i j => ?_⟩
  rw [c2_add]
  refine le_trans (norm_add_le _ _) ?_
  have := hG i j; have := hG' i j
  linarith

theorem BidiscBound.const (a : ℂ) : BidiscBound (a • (1 : PS2)) := by
  intro R hR
  refine ⟨‖a‖, fun i j => ?_⟩
  have h1 : 1 ≤ R ^ i := one_le_pow₀ hR.le
  have h2 : 1 ≤ R ^ j := one_le_pow₀ hR.le
  have ha := norm_nonneg a
  rw [c2_smul, norm_mul]
  unfold c2
  rw [coeff_one]
  split_ifs with hi
  · rw [coeff_one]
    split_ifs with hj
    · simp only [norm_one, mul_one]
      have : 1 ≤ R ^ i * R ^ j := one_le_mul_of_one_le_of_one_le h1 h2
      calc ‖a‖ = ‖a‖ * 1 := (mul_one _).symm
        _ ≤ ‖a‖ * (R ^ i * R ^ j) := mul_le_mul_of_nonneg_left this ha
        _ = _ := by ring
    · simp only [norm_zero, mul_zero]; positivity
  · simp only [map_zero, norm_zero, mul_zero]; positivity

/-- `(m+1) t^m` is bounded for `0 ≤ t < 1`. -/
theorem exists_bound_succ_mul_pow {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ∃ C : ℝ, ∀ m : ℕ, ((m : ℝ) + 1) * t ^ m ≤ C := by
  have hs : Summable (fun m : ℕ => ((m : ℝ) + 1) * t ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * t ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg ht₀])
    have h2 : Summable (fun m : ℕ => t ^ m) := summable_geometric_of_lt_one ht₀ ht₁
    convert h1.add h2 using 1
    ext m; ring
  refine ⟨∑' j : ℕ, ((j : ℝ) + 1) * t ^ j, fun m => ?_⟩
  exact hs.le_tsum m (fun j _ => by positivity)

theorem BidiscBound.mul {r r' : PS2} (h : BidiscBound r) (h' : BidiscBound r') :
    BidiscBound (r * r') := by
  intro R hR
  obtain ⟨R', hR'1, hR'R⟩ : ∃ R' : ℝ, 1 < R' ∧ R' < R := ⟨(1 + R) / 2, by linarith, by linarith⟩
  have hR'0 : 0 < R' := by linarith
  obtain ⟨G, hG⟩ := h R' hR'1
  obtain ⟨G', hG'⟩ := h' R' hR'1
  have hG0 : 0 ≤ G := by
    have := hG 0 0; simp only [pow_zero, mul_one] at this; exact le_trans (norm_nonneg _) this
  have hG0' : 0 ≤ G' := by
    have := hG' 0 0; simp only [pow_zero, mul_one] at this; exact le_trans (norm_nonneg _) this
  obtain ⟨C, hC⟩ := exists_bound_succ_mul_pow (t := R' / R) (by positivity)
    ((div_lt_one (by linarith)).mpr hR'R)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  refine ⟨G * G' * C * C, fun m n => ?_⟩
  rw [c2_mul]
  have hterm : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (n + 1),
      ‖c2 r i j * c2 r' (m - i) (n - j)‖ ≤ G * G' * R' ^ m * R' ^ n := by
    intro i hi j hj
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [norm_mul]
    calc ‖c2 r i j‖ * ‖c2 r' (m - i) (n - j)‖
        ≤ (G * R' ^ i * R' ^ j) * (G' * R' ^ (m - i) * R' ^ (n - j)) :=
          mul_le_mul (hG i j) (hG' _ _) (norm_nonneg _) (by positivity)
      _ = G * G' * (R' ^ i * R' ^ (m - i)) * (R' ^ j * R' ^ (n - j)) := by ring
      _ = G * G' * R' ^ m * R' ^ n := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hi', Nat.add_sub_cancel' hj']
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum fun i hi =>
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => hterm i hi j hj)) ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have hm := hC m
  have hn := hC n
  have hRm : R' ^ m = (R' / R) ^ m * R ^ m := by
    rw [div_pow, div_mul_cancel₀]; positivity
  have hRn : R' ^ n = (R' / R) ^ n * R ^ n := by
    rw [div_pow, div_mul_cancel₀]; positivity
  rw [hRm, hRn]
  have hRm0 : 0 ≤ R ^ m := by positivity
  have hRn0 : 0 ≤ R ^ n := by positivity
  calc ((m : ℝ) + 1) * (((n : ℝ) + 1) * (G * G' * ((R' / R) ^ m * R ^ m) * ((R' / R) ^ n * R ^ n)))
      = G * G' * (((m : ℝ) + 1) * (R' / R) ^ m) * (((n : ℝ) + 1) * (R' / R) ^ n) *
          R ^ m * R ^ n := by ring
    _ ≤ G * G' * C * C * R ^ m * R ^ n := by gcongr

theorem bidiscBound_generators :
    BidiscBound (ιx X) ∧ BidiscBound (ιy X) ∧ BidiscBound (ιx (HuangODEAlgebra.geom 1)) ∧
      BidiscBound (ιy (HuangODEAlgebra.geom 1)) ∧ BidiscBound (ιxy (HuangODEAlgebra.geom 1)) := by
  refine ⟨bidiscBound_of_le_one fun i j => ?_, bidiscBound_of_le_one fun i j => ?_,
    bidiscBound_of_le_one fun i j => ?_, bidiscBound_of_le_one fun i j => ?_,
    bidiscBound_of_le_one fun i j => ?_⟩
  · rw [c2_ιx, coeff_X]; split_ifs <;> simp
  · rw [c2_ιy, coeff_X]; split_ifs <;> simp
  · rw [c2_ιx]; split_ifs <;> simp [HuangODEAlgebra.geom]
  · rw [c2_ιy]; split_ifs <;> simp [HuangODEAlgebra.geom]
  · rw [c2_ιxy]; split_ifs <;> simp [HuangODEAlgebra.geom]

/-- **Every element of the coefficient ring is holomorphic on the open unit bidisc.** -/
theorem bidiscBound_of_mem_sepRing {r : PS2} (hr : r ∈ sepRing) : BidiscBound r := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := bidiscBound_generators
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one]; exact BidiscBound.const a
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/-! ## The inner Euler operator and the equation from finite generation -/

/-- `y ∂_y + μ` on double series. -/
def thetaY (μ : ℂ) : PS2 →ₗ[ℂ] PS2 where
  toFun Q := PowerSeries.mk fun m => thetaShift μ (coeff m Q)
  map_add' Q Q' := by ext m n; simp
  map_smul' a Q := by ext m n; simp

theorem c2_thetaY (μ : ℂ) (Q : PS2) (m n : ℕ) :
    c2 (thetaY μ Q) m n = (μ + n) * c2 Q m n := by
  simp [c2, thetaY, coeff_thetaShift]

theorem c2_thetaY_iterate (μ : ℂ) (i : ℕ) (Q : PS2) (m n : ℕ) :
    c2 ((thetaY μ)^[i] Q) m n = (μ + n) ^ i * c2 Q m n := by
  induction i generalizing Q with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, c2_thetaY, pow_succ]; ring

theorem thetaY_add_const (μ d : ℂ) (Q : PS2) : thetaY (μ + d) Q = thetaY μ Q + d • Q := by
  refine PS2.ext fun m n => ?_
  rw [c2_add, c2_smul, c2_thetaY, c2_thetaY]; ring

theorem thetaY_iterate_add (μ : ℂ) (i : ℕ) (x y : PS2) :
    (thetaY μ)^[i] (x + y) = (thetaY μ)^[i] x + (thetaY μ)^[i] y := by
  simp only [← Module.End.pow_apply, map_add]

theorem thetaY_iterate_smul (μ : ℂ) (i : ℕ) (c : ℂ) (x : PS2) :
    (thetaY μ)^[i] (c • x) = c • (thetaY μ)^[i] x := by
  simp only [← Module.End.pow_apply, map_smul]

/-- A chain of series, each a twisted `thetaY` of the previous one, all in one submodule:
then all `thetaY`-iterates (any twist) of the first lie in it. -/
theorem thetaY_iter_mem (NN : Submodule sepRing PS2) (Q : ℕ → PS2) (lam : ℕ → ℂ)
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
    exact NN.add_mem (ih (j + 1)) (smul_mem_of_sepRing NN _ (ih j))

/-- The inner regular equation with coefficients in `sepRing`: the coefficient form used by
`geometric_of_rowFuchsian`. -/
def InnerRegular (lam : ℂ) (c : ℕ → ℕ → ℂ) : Prop :=
  ∃ (s : ℕ) (g : ℕ → ℕ → ℕ → ℂ), 1 ≤ s ∧
    (∀ R : ℝ, 1 < R → ∃ G : ℝ, ∀ k < s, ∀ i j, ‖g k i j‖ ≤ G * R ^ i * R ^ j) ∧
    DiagonalFuchsian (fun _ n => lam + n) s g c

theorem exists_uniform_bound_fin {s : ℕ} {r : ℕ → PS2} (hr : ∀ k < s, BidiscBound (r k))
    (R : ℝ) (hR : 1 < R) : ∃ G : ℝ, ∀ k < s, ∀ i j, ‖c2 (r k) i j‖ ≤ G * R ^ i * R ^ j := by
  induction s with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ s ih =>
    obtain ⟨G, hG⟩ := ih (fun k hk => hr k (by omega))
    obtain ⟨G', hG'⟩ := hr s (by omega) R hR
    refine ⟨max G G', fun k hk i j => ?_⟩
    have hRi : 0 ≤ R ^ i * R ^ j := by positivity
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · refine le_trans (hG k h i j) ?_
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRi
    · refine le_trans (hG' i j) ?_
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hRi

/-- **The inner equation from finite generation.** If every `thetaY μ`-iterate of `Q`
lies in a finitely generated `sepRing`-submodule, then for every `λ` the coefficient array
of `Q` satisfies `InnerRegular λ`. -/
theorem innerRegular_of_fg (NN : Submodule sepRing PS2) (hN : NN.FG) {Q : PS2} {μ : ℂ}
    (h : ∀ j, (thetaY μ)^[j] Q ∈ NN) (lam : ℂ) : InnerRegular lam (c2 Q) := by
  classical
  -- change the twist
  have hmem : ∀ j, (thetaY lam)^[j] Q ∈ NN := by
    have key := thetaY_iter_mem NN (fun j => (thetaY μ)^[j] Q) (fun _ => μ)
      (fun j => Function.iterate_succ_apply' _ _ _) h lam
    intro j; simpa using key j 0
  haveI : Module.Finite sepRing NN := Module.Finite.iff_fg.mpr hN
  obtain ⟨m, r, hr⟩ := VOA.Huang.MatrixCoeffODE.exists_monic_relation (R := sepRing)
    (fun j => (⟨(thetaY lam)^[j] Q, hmem j⟩ : NN))
  have hr' : (thetaY lam)^[m] Q =
      ∑ k ∈ Finset.range m, (r k : PS2) * (thetaY lam)^[k] Q := by
    have := congrArg Subtype.val hr
    simpa [Submodule.coe_sum, Subalgebra.smul_def] using this
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `Q = 0`
    subst hm
    have hQ : Q = 0 := by simpa using hr'
    refine ⟨1, fun _ _ _ => 0, le_rfl, fun R _ => ⟨0, fun k _ i j => by simp⟩, ?_⟩
    intro a b
    simp [hQ, c2_zero]
  · refine ⟨m, fun k => c2 (r k), hm, fun R hR => ?_, ?_⟩
    · exact exists_uniform_bound_fin (fun k _ => bidiscBound_of_mem_sepRing (r k).2) R hR
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
