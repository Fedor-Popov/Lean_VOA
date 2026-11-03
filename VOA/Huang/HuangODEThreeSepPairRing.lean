import VOA.Huang.HuangODEThreeSepMidRing
import VOA.Huang.HuangODEThreeSepMidMoves

/-!
# The coefficient ring of the pair (blow-up) chart, and coefficient bookkeeping

In the blow-up chart `x = z₃/z₂`, `y = z₀/z₃` of the pair vertex the collision divisors are
`x = 1` (`y`–`z`), `xy = -1` (`x`–`t`) and `x(1-y) = 1` (`x`–`z`).

* `ιm'` — the ring map `t ↦ x(1-y)`; `c2 (ιm' f) i j = coeff i f · C(i,j) (-1)^j`;
* `pairRing = ℂ[x, y, (1-x)⁻¹, (1+xy)⁻¹, (1-x(1-y))⁻¹]`, Noetherian, all elements `MidBound`;
* `innerRegularAdm_of_fg` — the inner equation from finite generation over any Noetherian
  subalgebra all of whose elements satisfy `MidBound`;
* coefficient formulas for ring elements times an array that vanishes at negative indices
  (abstract vanishing hypothesis; used for the pair shape, whose strips depend on all levels).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open PowerSeries VOA.Huang.UniformConv VOA.Huang.FuchsianODE
open scoped BigOperators

/-- `t ↦ x(1-y)`. -/
def ιm' : PowerSeries ℂ →+* PS2 := (PowerSeries.rescale (1 - X : PowerSeries ℂ)).comp ιx

theorem coeff_one_sub_X_pow (i j : ℕ) :
    coeff j ((1 - X : PowerSeries ℂ) ^ i) = (i.choose j : ℂ) * (-1) ^ j := by
  have h : ((1 - X : PowerSeries ℂ)) ^ i = PowerSeries.rescale (-1 : ℂ) ((1 + X) ^ i) := by
    rw [map_pow, map_add, map_one, rescale_X]
    congr 1
    simp [sub_eq_add_neg]
  rw [h, coeff_rescale, coeff_one_add_X_pow', mul_comm]

theorem c2_ιm' (f : PowerSeries ℂ) (i j : ℕ) :
    c2 (ιm' f) i j = coeff i f * ((i.choose j : ℂ) * (-1) ^ j) := by
  unfold c2 ιm'
  rw [RingHom.comp_apply, coeff_rescale]
  simp only [ιx, coeff_map]
  rw [coeff_mul_C, coeff_one_sub_X_pow, mul_comm]

theorem c2_ιm'_mul (f : PowerSeries ℂ) (Q : PS2) (m n : ℕ) :
    c2 (ιm' f * Q) m n = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      coeff i f * ((i.choose j : ℂ) * (-1) ^ j) * c2 Q (m - i) (n - j) := by
  rw [c2_mul]
  simp only [c2_ιm']

/-- `ℂ[x, y, (1-x)⁻¹, (1+xy)⁻¹, (1-x(1-y))⁻¹]` inside `ℂ⟦x,y⟧`. -/
def pairRing : Subalgebra ℂ PS2 :=
  Algebra.adjoin ℂ ({ιx X, ιy X, ιx (HuangODEAlgebra.geom 1), ιxy (HuangODEAlgebra.geom (-1)),
    ιm' (HuangODEAlgebra.geom 1)} : Set PS2)

instance : IsNoetherianRing pairRing := by
  classical
  have hfg : pairRing.FG := by
    have := Subalgebra.fg_adjoin_finset (R := ℂ) ({ιx X, ιy X, ιx (HuangODEAlgebra.geom 1),
      ιxy (HuangODEAlgebra.geom (-1)), ιm' (HuangODEAlgebra.geom 1)} : Finset PS2)
    simpa [pairRing] using this
  haveI : Algebra.FiniteType ℂ pairRing := (Subalgebra.fg_iff_finiteType _).mp hfg
  exact Algebra.FiniteType.isNoetherianRing ℂ pairRing

theorem pair_ιx_X_mem : ιx X ∈ pairRing := Algebra.subset_adjoin (by simp)
theorem pair_ιy_X_mem : ιy X ∈ pairRing := Algebra.subset_adjoin (by simp)
theorem pair_ιx_geom_mem : ιx (HuangODEAlgebra.geom 1) ∈ pairRing :=
  Algebra.subset_adjoin (by simp)
theorem pair_ιxy_geom_mem : ιxy (HuangODEAlgebra.geom (-1)) ∈ pairRing :=
  Algebra.subset_adjoin (by simp)
theorem pair_ιm'_geom_mem : ιm' (HuangODEAlgebra.geom 1) ∈ pairRing :=
  Algebra.subset_adjoin (by simp)

theorem pair_ιxy_X_mem : ιxy X ∈ pairRing := by
  rw [ιxy_X, ← ιx_X, ← ιy_X]
  exact Subalgebra.mul_mem _ pair_ιx_X_mem pair_ιy_X_mem

theorem pair_monomial_mem (a b : ℕ) :
    (X : PS2) ^ a * PowerSeries.C ((X : PowerSeries ℂ) ^ b) ∈ pairRing := by
  rw [map_pow, ← ιx_X, ← ιy_X]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ pair_ιx_X_mem _)
    (Subalgebra.pow_mem _ pair_ιy_X_mem _)

theorem pair_ιx_binom_mem (k : ℕ) : ιx (X * HuangODEAlgebra.binomSeries 1 k) ∈ pairRing := by
  rw [HuangODEAlgebra.binomSeries_eq, map_mul, map_mul, map_pow, map_pow]
  exact Subalgebra.mul_mem _ pair_ιx_X_mem (Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ pair_ιx_X_mem _) (Subalgebra.pow_mem _ pair_ιx_geom_mem _))

theorem pair_ιxy_binom_mem (k : ℕ) :
    ιxy (X * HuangODEAlgebra.binomSeries (-1) k) ∈ pairRing := by
  rw [HuangODEAlgebra.binomSeries_eq, map_mul, map_mul, map_pow, map_pow]
  exact Subalgebra.mul_mem _ pair_ιxy_X_mem (Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ pair_ιxy_X_mem _) (Subalgebra.pow_mem _ pair_ιxy_geom_mem _))

theorem pair_ιm'_geom_pow_mem (k : ℕ) : ιm' (HuangODEAlgebra.geom 1 ^ k) ∈ pairRing := by
  rw [map_pow]; exact Subalgebra.pow_mem _ pair_ιm'_geom_mem _

/-- `(1 - x(1-y))⁻¹` on the admissible region. -/
theorem midBound_ιm'_geom : MidBound (ιm' (HuangODEAlgebra.geom 1)) := by
  intro R₁ R₂ hR
  obtain ⟨G, hG⟩ := midBound_ιm_geom R₁ R₂ hR
  refine ⟨G, fun i j => ?_⟩
  have h := hG i j
  rw [c2_ιm] at h
  rw [c2_ιm', ← mul_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  exact h

theorem midBound_of_mem_pairRing {r : PS2} (hr : r ∈ pairRing) : MidBound r := by
  have g1 : MidBound (ιx X) := midBound_of_le_one fun i j => by
    rw [c2_ιx, coeff_X]; split_ifs <;> simp
  have g2 : MidBound (ιy X) := midBound_of_le_one fun i j => by
    rw [c2_ιy, coeff_X]; split_ifs <;> simp
  have g3 : MidBound (ιx (HuangODEAlgebra.geom 1)) := midBound_of_le_one fun i j => by
    rw [c2_ιx]; split_ifs <;> simp [HuangODEAlgebra.geom]
  have g4 : MidBound (ιxy (HuangODEAlgebra.geom (-1))) := midBound_of_le_one fun i j => by
    rw [c2_ιxy]; split_ifs <;> simp [HuangODEAlgebra.geom]
  have g5 := midBound_ιm'_geom
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one]; exact MidBound.const a
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/-! ## The inner equation over an admissible Noetherian subalgebra -/

section General
variable {R : Subalgebra ℂ PS2}

theorem mul_mem_of_sub (NN : Submodule R PS2) {r q : PS2} (hr : r ∈ R) (hq : q ∈ NN) :
    r * q ∈ NN := by
  have h := NN.smul_mem ⟨r, hr⟩ hq
  rwa [Subalgebra.smul_def] at h

theorem smul_mem_of_sub (NN : Submodule R PS2) (a : ℂ) {q : PS2} (hq : q ∈ NN) : a • q ∈ NN := by
  have h := NN.smul_mem (algebraMap ℂ R a) hq
  rwa [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul] at h

theorem thetaY_iter_mem_sub (NN : Submodule R PS2) (Q : ℕ → PS2) (lam : ℕ → ℂ)
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
    exact NN.add_mem (ih (j + 1)) (smul_mem_of_sub NN _ (ih j))

/-- **The inner equation from finite generation over an admissible Noetherian ring.** -/
theorem innerRegularAdm_of_fg [IsNoetherianRing R] (hR : ∀ r ∈ R, MidBound r)
    (NN : Submodule R PS2) (hN : NN.FG) {Q : PS2} {μ : ℂ}
    (h : ∀ j, (thetaY μ)^[j] Q ∈ NN) (lam : ℂ) : InnerRegularMid lam (c2 Q) := by
  classical
  have hmem : ∀ j, (thetaY lam)^[j] Q ∈ NN := by
    have key := thetaY_iter_mem_sub NN (fun j => (thetaY μ)^[j] Q) (fun _ => μ)
      (fun j => Function.iterate_succ_apply' _ _ _) h lam
    intro j; simpa using key j 0
  haveI : Module.Finite R NN := Module.Finite.iff_fg.mpr hN
  obtain ⟨m, r, hr⟩ := VOA.Huang.MatrixCoeffODE.exists_monic_relation (R := R)
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
  · refine ⟨m, fun k => c2 (r k), hm, fun R₁ R₂ hRR => ?_, ?_⟩
    · exact exists_uniform_midBound_fin (fun k _ => hR _ (r k).2) R₁ R₂ hRR
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

end General

/-! ## Coefficients against an array vanishing at negative indices -/

section Vanish
variable {Q : PS2} {F : ℂ → ℂ → ℂ} (hQ : ∀ m n : ℕ, c2 Q m n = F m n)
  (hvan : ∀ a b : ℤ, a < 0 ∨ b < 0 → F a b = 0)
include hQ hvan

omit hQ in
theorem vanish_cast (a b : ℤ) (h : a < 0 ∨ b < 0) {x y : ℂ} (hx : x = (a : ℂ))
    (hy : y = (b : ℂ)) : F x y = 0 := by
  subst hx hy; exact hvan a b h

theorem c2_monomial_van (a b m n : ℕ) :
    c2 (X ^ a * PowerSeries.C (X ^ b) * Q) m n = F ((m : ℂ) - a) ((n : ℂ) - b) := by
  rw [c2_monomial_mul]
  split_ifs with h
  · rw [hQ, Nat.cast_sub h.1, Nat.cast_sub h.2]
  · symm
    refine vanish_cast hvan ((m : ℤ) - a) ((n : ℤ) - b) (by omega)
      (by push_cast; ring) (by push_cast; ring)

theorem c2_ιx_binom_van (k b m n I : ℕ) (hI : m ≤ I) :
    c2 (ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ b) * Q)) m n =
    ∑ i ∈ Finset.range I, (i.choose k : ℂ) * F ((m : ℂ) - 1 - i) ((n : ℂ) - b) := by
  rw [c2_ιx_mul, Finset.sum_range_succ']
  simp only [coeff_zero_X_mul_binom, zero_mul, add_zero]
  rw [← Finset.sum_range_add_sum_Ico _ hI]
  rw [Finset.sum_eq_zero (s := Finset.Ico m I) (fun i hi => by
    have hi' := (Finset.mem_Ico.mp hi).1
    rw [vanish_cast hvan ((m : ℤ) - 1 - i) ((n : ℤ) - b) (Or.inl (by omega))
      (by push_cast; ring) (by push_cast; ring), mul_zero]), add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  rw [coeff_X_mul_binom, c2_monomial_van hQ hvan]
  congr 2
  rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem c2_ιxy_binomNeg_van (k m n I : ℕ) (hI : m ≤ I) :
    c2 (ιxy (X * HuangODEAlgebra.binomSeries (-1) k) * Q) m n =
    ∑ i ∈ Finset.range I, (i.choose k : ℂ) * (-1) ^ (i - k) *
      F ((m : ℂ) - 1 - i) ((n : ℂ) - 1 - i) := by
  rw [c2_ιxy_mul, Finset.sum_range_succ']
  simp only [Nat.zero_le, ite_true, coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X,
    zero_mul, add_zero]
  rw [← Finset.sum_range_add_sum_Ico _ hI]
  rw [Finset.sum_eq_zero (s := Finset.Ico m I) (fun i hi => by
    have hi' := (Finset.mem_Ico.mp hi).1
    rw [vanish_cast hvan ((m : ℤ) - 1 - i) ((n : ℤ) - 1 - i) (Or.inl (by omega))
      (by push_cast; ring) (by push_cast; ring), mul_zero]), add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  split_ifs with hin
  · rw [coeff_X_mul_binom', hQ]
    congr 2
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
    · rw [Nat.cast_sub hin]; push_cast; ring
  · rw [vanish_cast hvan ((m : ℤ) - 1 - i) ((n : ℤ) - 1 - i) (Or.inr (by omega))
      (by push_cast; ring) (by push_cast; ring), mul_zero]

omit hvan in
theorem c2_ιm'_geom_van (k m n : ℕ) :
    c2 (ιm' (HuangODEAlgebra.geom 1 ^ (k + 1)) * Q) m n =
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      ((i + k).choose k : ℂ) * ((i.choose j : ℂ) * (-1) ^ j) *
        F ((m : ℂ) - i) ((n : ℂ) - j) := by
  rw [c2_ιm'_mul]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rw [hQ]
  have hgeom : coeff i (HuangODEAlgebra.geom 1 ^ (k + 1)) = ((i + k).choose k : ℂ) := by
    have h := congrArg (coeff (i + k)) (HuangODEAlgebra.binomSeries_eq 1 k)
    rw [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h
    rw [← h]
    simp [HuangODEAlgebra.binomSeries]
  rw [hgeom, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]

end Vanish

end VOA.Huang.FivePointSep
