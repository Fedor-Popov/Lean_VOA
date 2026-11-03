import VOA.Classification.COne.OrbIcoSmall
import VOA.Classification.COne.OrbIcoChan2

/-! # OrbIco: explicit coefficients for the channel eliminations

* `psi_J6`: `psi J₆ = f`, the icosahedral form of degree `12` in the frame where the `z`-axis
  is a two-fold axis: `f = f₀(x¹² + y¹²) + f₂(x¹⁰y² + x²y¹⁰) + f₄(x⁸y⁴ + x⁴y⁸) + f₆ x⁶y⁶`.
* coefficient functionals `cf d k` (the coefficient of `x^{d-k} y^k`) and the bilinear formulas
  `cf_B2_zero`, `cf_B2_two` (second channel) and `cf_tv1_one` (first channel);
* `cf_H_zero_ne`, `cf_tv1_ne`: the two channel values used in the eliminations are nonzero;
* `Tb_injective`: `Tb` is injective on binary forms of a fixed even degree.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv OrbPrim OrbOcta
  Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## The form `f = psi J₆` -/

def f0 : ℂ := -3 - 4 * gp
def f2 : ℂ := -22 - 44 * gp
def f4 : ℂ := 99 + 132 * gp
def f6 : ℂ := 44 + 88 * gp

def fpoly : P2 :=
  MvPolynomial.C f0 * (X 0 ^ 12 + X 1 ^ 12) + MvPolynomial.C f2 * (X 0 ^ 10 * X 1 ^ 2 + X 0 ^ 2 * X 1 ^ 10) +
    MvPolynomial.C f4 * (X 0 ^ 8 * X 1 ^ 4 + X 0 ^ 4 * X 1 ^ 8) + MvPolynomial.C f6 * (X 0 ^ 6 * X 1 ^ 6)

theorem gp_pow_five : gp ^ 5 = 5 * gp + 3 := by
  rw [pow_succ, gp_pow_four]; linear_combination 3 * gp_sq'
theorem gp_pow_six : gp ^ 6 = 8 * gp + 5 := by
  rw [pow_succ, gp_pow_five]; linear_combination 5 * gp_sq'

theorem psi_J6 : psi J6 = fpoly := by
  apply MvPolynomial.funext
  intro x
  rw [eval_psi, J6, map_prod]
  simp only [eval_lin]
  simp [Fin.prod_univ_succ, a5, pt, dotProduct, Fin.sum_univ_three, fpoly, f0, f2, f4, f6]
  rcases eps1_cases with h | h <;> rw [h] <;> ring_nf <;>
    simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, gp_sq', gp_pow_three,
      gp_pow_four, gp_pow_five, gp_pow_six] <;> ring_nf


/-! ## Coefficient functionals -/

/-- The coefficient of `x^{d-k} y^k`. -/
def cf (d k : ℕ) : P2 →ₗ[ℂ] ℂ := lcoeff ℂ (Finsupp.single 0 (d - k) + Finsupp.single 1 k)

theorem fin2_exp_eq_iff (a b a' b' : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b = Finsupp.single 0 a' + Finsupp.single 1 b')
      ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have h0 := congrArg (fun e => e 0) h
    have h1 := congrArg (fun e => e 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem cf_xy (d k a b : ℕ) :
    cf d k (X 0 ^ a * X 1 ^ b) = if a = d - k ∧ b = k then 1 else 0 := by
  rw [cf, lcoeff_apply, binMono_eq, coeff_monomial]
  by_cases h : a = d - k ∧ b = k
  · rw [if_pos ((fin2_exp_eq_iff _ _ _ _).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((fin2_exp_eq_iff _ _ _ _).mp h')), if_neg h]

theorem monomial_eq_xy (e : Fin 2 →₀ ℕ) : (monomial e (1 : ℂ) : P2) = X 0 ^ e 0 * X 1 ^ e 1 := by
  have h : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
    ext i; fin_cases i <;> simp
  rw [binMono_eq, h]

theorem binDeg_bilin {d₁ d₂ : ℕ} (Φ : P2 → P2 → ℂ)
    (hadd1 : ∀ P P' Q, Φ (P + P') Q = Φ P Q + Φ P' Q) (hsmul1 : ∀ (c : ℂ) P Q, Φ (c • P) Q = c * Φ P Q)
    (hadd2 : ∀ P Q Q', Φ P (Q + Q') = Φ P Q + Φ P Q') (hsmul2 : ∀ (c : ℂ) P Q, Φ P (c • Q) = c * Φ P Q)
    (hmono : ∀ e f : Fin 2 →₀ ℕ, e 0 + e 1 = d₁ → f 0 + f 1 = d₂ →
      Φ (X 0 ^ e 0 * X 1 ^ e 1) (X 0 ^ f 0 * X 1 ^ f 1) = 0) :
    ∀ P ∈ binDeg d₁, ∀ Q ∈ binDeg d₂, Φ P Q = 0 := by
  have h0l : ∀ Q, Φ 0 Q = 0 := fun Q => by simpa using hsmul1 0 0 Q
  have h0r : ∀ P, Φ P 0 = 0 := fun P => by simpa using hsmul2 0 P 0
  intro P hP Q hQ
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      beta_reduce
      rw [monomial_eq_xy, monomial_eq_xy]
      exact hmono e f he hf
    | zero => exact h0r _
    | add y z _ _ hy hz => rw [hadd2, hy, hz, add_zero]
    | smul c y _ hy => rw [hsmul2, hy, mul_zero]
  | zero => exact h0l _
  | add x y _ _ hx hy => rw [hadd1, hx, hy, add_zero]
  | smul c x _ hx => rw [hsmul1, hx, mul_zero]

/-! ## The second channel, coefficientwise -/

theorem B2_xy (a b c d : ℕ) (hab : a + b = 12) (hcd : c + d = 12) :
    B2 (X 0 ^ a * X 1 ^ b) (X 0 ^ c * X 1 ^ d) =
      tau2 b d • (X 0 ^ (22 - (b + d)) * X 1 ^ (b + d - 2)) := by
  have h1 : (X 0 ^ a * X 1 ^ b : P2) = monomial (Finsupp.single 0 a + Finsupp.single 1 b) 1 :=
    binMono_eq a b
  have h2 : (X 0 ^ c * X 1 ^ d : P2) = monomial (Finsupp.single 0 c + Finsupp.single 1 d) 1 :=
    binMono_eq c d
  rw [h1, h2, B2_monomial]
  simp

theorem cf_B2_zero {P Q : P2} (hP : P ∈ binDeg 12) (hQ : Q ∈ binDeg 12) :
    cf 20 0 (B2 P Q) = 264 * (cf 12 0 P * cf 12 2 Q + cf 12 2 P * cf 12 0 Q) -
      242 * (cf 12 1 P * cf 12 1 Q) := by
  have := binDeg_bilin (d₁ := 12) (d₂ := 12) (fun P Q => cf 20 0 (B2 P Q) -
      (264 * (cf 12 0 P * cf 12 2 Q + cf 12 2 P * cf 12 0 Q) - 242 * (cf 12 1 P * cf 12 1 Q)))
    (fun P P' Q => by simp only [map_add, LinearMap.add_apply]; ring)
    (fun c P Q => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun P Q Q' => by simp only [map_add]; ring)
    (fun c P Q => by simp only [map_smul, smul_eq_mul]; ring)
    (fun e f he hf => by
      beta_reduce
      rw [B2_xy _ _ _ _ he hf, map_smul, cf_xy, cf_xy, cf_xy, cf_xy, cf_xy, cf_xy, cf_xy,
        smul_eq_mul]
      by_cases h2 : e 1 + f 1 = 2
      · rcases (show (e 1 = 0 ∧ f 1 = 2) ∨ (e 1 = 1 ∧ f 1 = 1) ∨ (e 1 = 2 ∧ f 1 = 0) by omega)
          with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
          simp [h3, h4, show e 0 = 12 - e 1 by omega, show f 0 = 12 - f 1 by omega, tau2] <;>
          norm_num
      · have hz : ¬ (22 - (e 1 + f 1) = 20 - 0 ∧ e 1 + f 1 - 2 = 0) := by omega
        rw [if_neg hz]
        by_cases h0 : e 1 = 0 <;> by_cases h1 : e 1 = 1 <;> by_cases h2' : e 1 = 2 <;>
          simp [h0, h1, h2', show e 0 = 12 - e 1 by omega, show f 0 = 12 - f 1 by omega] <;>
          omega)
  exact sub_eq_zero.mp (this P hP Q hQ)


set_option maxHeartbeats 4000000 in
-- 169 explicit monomial pairs.
theorem cf_B2_two {P Q : P2} (hP : P ∈ binDeg 12) (hQ : Q ∈ binDeg 12) :
    cf 20 2 (B2 P Q) = 1584 * (cf 12 0 P * cf 12 4 Q + cf 12 4 P * cf 12 0 Q) +
      66 * (cf 12 1 P * cf 12 3 Q + cf 12 3 P * cf 12 1 Q) - 440 * (cf 12 2 P * cf 12 2 Q) := by
  have := binDeg_bilin (d₁ := 12) (d₂ := 12) (fun P Q => cf 20 2 (B2 P Q) -
      (1584 * (cf 12 0 P * cf 12 4 Q + cf 12 4 P * cf 12 0 Q) +
        66 * (cf 12 1 P * cf 12 3 Q + cf 12 3 P * cf 12 1 Q) - 440 * (cf 12 2 P * cf 12 2 Q)))
    (fun P P' Q => by simp only [map_add, LinearMap.add_apply]; ring)
    (fun c P Q => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun P Q Q' => by simp only [map_add]; ring)
    (fun c P Q => by simp only [map_smul, smul_eq_mul]; ring)
    (fun e f he hf => by
      beta_reduce
      rw [B2_xy _ _ _ _ he hf, map_smul, show e 0 = 12 - e 1 by omega,
        show f 0 = 12 - f 1 by omega]
      simp only [cf_xy, smul_eq_mul]
      have hi : e 1 ≤ 12 := by omega
      have hj : f 1 ≤ 12 := by omega
      generalize e 1 = i at hi ⊢
      generalize f 1 = j at hj ⊢
      interval_cases i <;> interval_cases j <;> norm_num [tau2])
  exact sub_eq_zero.mp (this P hP Q hQ)

/-! ## The first channel, coefficientwise -/

theorem pd0_xy (a b : ℕ) :
    pderiv 0 (X 0 ^ a * X 1 ^ b : P2) = (a : P2) * X 0 ^ (a - 1) * X 1 ^ b := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, pderiv_X_self,
    pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  simp only [smul_zero, zero_add, smul_eq_mul, nsmul_eq_mul, mul_one]
  ring

theorem pd1_xy (a b : ℕ) :
    pderiv 1 (X 0 ^ a * X 1 ^ b : P2) = (b : P2) * X 0 ^ a * X 1 ^ (b - 1) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, pderiv_X_self,
    pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  simp only [smul_zero, add_zero, smul_eq_mul, nsmul_eq_mul, mul_one]
  ring

theorem cf_natCast_mul (d k n : ℕ) (M : P2) : cf d k ((n : P2) * M) = (n : ℂ) * cf d k M := by
  rw [show ((n : P2)) = MvPolynomial.C (n : ℂ) by simp, cf, lcoeff_apply, lcoeff_apply,
    coeff_C_mul]

theorem tv1_xy (a b c d : ℕ) :
    tv1 (X 0 ^ a * X 1 ^ b) (X 0 ^ c * X 1 ^ d) =
      ((a * d : ℕ) : P2) * (X 0 ^ (a - 1 + c) * X 1 ^ (b + (d - 1))) -
        ((b * c : ℕ) : P2) * (X 0 ^ (a + (c - 1)) * X 1 ^ (b - 1 + d)) := by
  rw [tv1, pd0_xy, pd1_xy, pd0_xy, pd1_xy]
  push_cast
  ring

set_option maxHeartbeats 4000000 in
-- 273 explicit monomial pairs.
theorem cf_tv1_one {P Q : P2} (hP : P ∈ binDeg 12) (hQ : Q ∈ binDeg 20) :
    cf 30 1 (tv1 P Q) = 24 * (cf 12 0 P * cf 20 2 Q) - 40 * (cf 12 2 P * cf 20 0 Q) -
      8 * (cf 12 1 P * cf 20 1 Q) := by
  have := binDeg_bilin (d₁ := 12) (d₂ := 20) (fun P Q => cf 30 1 (tv1 P Q) -
      (24 * (cf 12 0 P * cf 20 2 Q) - 40 * (cf 12 2 P * cf 20 0 Q) -
        8 * (cf 12 1 P * cf 20 1 Q)))
    (fun P P' Q => by simp only [tv1_add_left, map_add]; ring)
    (fun c P Q => by simp only [tv1_smul_left, map_smul, smul_eq_mul]; ring)
    (fun P Q Q' => by simp only [tv1_add_right, map_add]; ring)
    (fun c P Q => by simp only [tv1_smul_right, map_smul, smul_eq_mul]; ring)
    (fun e f he hf => by
      beta_reduce
      rw [show e 0 = 12 - e 1 by omega, show f 0 = 20 - f 1 by omega, tv1_xy, map_sub,
        cf_natCast_mul, cf_natCast_mul]
      simp only [cf_xy]
      have hi : e 1 ≤ 12 := by omega
      have hj : f 1 ≤ 20 := by omega
      generalize e 1 = i at hi ⊢
      generalize f 1 = j at hj ⊢
      interval_cases i <;> interval_cases j <;> norm_num)
  exact sub_eq_zero.mp (this P hP Q hQ)

/-! ## Values on `f` -/

theorem fpoly_eq : fpoly = MvPolynomial.C f0 * (X 0 ^ 12 * X 1 ^ 0 + X 0 ^ 0 * X 1 ^ 12) +
    MvPolynomial.C f2 * (X 0 ^ 10 * X 1 ^ 2 + X 0 ^ 2 * X 1 ^ 10) +
    MvPolynomial.C f4 * (X 0 ^ 8 * X 1 ^ 4 + X 0 ^ 4 * X 1 ^ 8) +
    MvPolynomial.C f6 * (X 0 ^ 6 * X 1 ^ 6) := by
  rw [fpoly]; simp

theorem cf_C_mul (d k : ℕ) (c : ℂ) (M : P2) : cf d k (MvPolynomial.C c * M) = c * cf d k M := by
  rw [cf, lcoeff_apply, lcoeff_apply, coeff_C_mul]

theorem cf_f (k : ℕ) (hk : k ≤ 4) :
    cf 12 k fpoly = ![f0, 0, f2, 0, f4] ⟨k, by omega⟩ := by
  rw [fpoly_eq]
  simp only [map_add, cf_C_mul, cf_xy]
  interval_cases k <;> simp

theorem fpoly_mem : fpoly ∈ binDeg 12 := by
  rw [← psi_J6]; exact mem_binDeg_of_hom (psi_hom J6_hom)


/-! ## The two channel values -/

/-- `H' = B2 f f`, the binary form of the weight-100 channel. -/
def Hpoly : P2 := B2 fpoly fpoly

theorem cf_H_zero : cf 20 0 Hpoly = 528 * (f0 * f2) := by
  rw [Hpoly, cf_B2_zero fpoly_mem fpoly_mem, cf_f 0 (by norm_num), cf_f 1 (by norm_num),
    cf_f 2 (by norm_num)]
  simp; ring

theorem cf_H_two : cf 20 2 Hpoly = 3168 * (f0 * f4) - 440 * f2 ^ 2 := by
  rw [Hpoly, cf_B2_two fpoly_mem fpoly_mem, cf_f 0 (by norm_num), cf_f 1 (by norm_num),
    cf_f 2 (by norm_num), cf_f 3 (by norm_num), cf_f 4 (by norm_num)]
  simp; ring

theorem gp_re_pos : 0 < gp.re := by
  rw [gp_re]; positivity

theorem ne_zero_of_lin_gp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : (a : ℂ) + b * gp ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [gp_im] at this
  nlinarith [gp_re_pos]

theorem cf_H_zero_ne : cf 20 0 Hpoly ≠ 0 := by
  rw [cf_H_zero, show (528 : ℂ) * (f0 * f2) = ((127776 : ℝ) : ℂ) + ((209088 : ℝ) : ℂ) * gp by
    unfold f0 f2; push_cast; linear_combination 92928 * gp_sq']
  exact ne_zero_of_lin_gp (by norm_num) (by norm_num)

theorem binDeg_hom {B : P2} {d : ℕ} (hB : B ∈ binDeg d) : B.IsHomogeneous d := by
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    apply isHomogeneous_monomial
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    exact he
  | zero => exact isHomogeneous_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => rw [smul_eq_C_mul]; simpa using hx.C_mul c

theorem xy_mem_binDeg (a b : ℕ) : (X 0 ^ a * X 1 ^ b : P2) ∈ binDeg (a + b) := by
  rw [binMono_eq]
  exact Submodule.subset_span ⟨_, by simp, rfl⟩

theorem B2_mem {P Q : P2} (hP : P ∈ binDeg 12) (hQ : Q ∈ binDeg 12) : B2 P Q ∈ binDeg 20 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [Set.mem_setOf_eq] at he hf
      rw [B2_monomial]
      by_cases h : 2 ≤ e 1 + f 1 ∧ e 1 + f 1 ≤ 22
      · refine Submodule.smul_mem _ _ ?_
        have := xy_mem_binDeg (22 - (e 1 + f 1)) (e 1 + f 1 - 2)
        rwa [show 22 - (e 1 + f 1) + (e 1 + f 1 - 2) = 20 by omega] at this
      · rcases (show e 1 + f 1 ≤ 1 ∨ 23 ≤ e 1 + f 1 by omega) with h1 | h1
        · rw [tau2_zero_of_le _ _ h1, zero_smul]; exact Submodule.zero_mem _
        · rw [tau2_zero_of_ge _ _ (by omega) (by omega) h1, zero_smul]
          exact Submodule.zero_mem _
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hx

theorem Hpoly_mem : Hpoly ∈ binDeg 20 := B2_mem fpoly_mem fpoly_mem

theorem tv1_mem {P Q : P2} (hP : P ∈ binDeg 12) (hQ : Q ∈ binDeg 20) : tv1 P Q ∈ binDeg 30 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [Set.mem_setOf_eq] at he hf
      beta_reduce
      rw [monomial_eq_xy, monomial_eq_xy, tv1_xy]
      have hnat : ∀ (n : ℕ) (M : P2), M ∈ binDeg 30 → ((n : P2)) * M ∈ binDeg 30 := by
        intro n M hM
        rw [show ((n : P2)) = MvPolynomial.C (n : ℂ) by simp, ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hM
      refine Submodule.sub_mem _ ?_ ?_
      · by_cases h : e 0 * f 1 = 0
        · rw [h, Nat.cast_zero, zero_mul]; exact Submodule.zero_mem _
        · apply hnat
          have := xy_mem_binDeg (e 0 - 1 + f 0) (e 1 + (f 1 - 1))
          rcases Nat.mul_ne_zero_iff.mp h with ⟨h1, h2⟩
          rwa [show e 0 - 1 + f 0 + (e 1 + (f 1 - 1)) = 30 by omega] at this
      · by_cases h : e 1 * f 0 = 0
        · rw [h, Nat.cast_zero, zero_mul]; exact Submodule.zero_mem _
        · apply hnat
          have := xy_mem_binDeg (e 0 + (f 0 - 1)) (e 1 - 1 + f 1)
          rcases Nat.mul_ne_zero_iff.mp h with ⟨h1, h2⟩
          rwa [show e 0 + (f 0 - 1) + (e 1 - 1 + f 1) = 30 by omega] at this
    | zero => simp [tv1]
    | add y z _ _ hy hz => rw [tv1_add_right]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [tv1_smul_right]; exact Submodule.smul_mem _ _ hy
  | zero => simp [tv1]
  | add x y _ _ hx hy => rw [tv1_add_left]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [tv1_smul_left]; exact Submodule.smul_mem _ _ hx


theorem cf_tv1_value : cf 30 1 (tv1 fpoly Hpoly) =
    24 * (f0 * (3168 * (f0 * f4) - 440 * f2 ^ 2)) - 40 * (f2 * (528 * (f0 * f2))) := by
  rw [cf_tv1_one fpoly_mem Hpoly_mem, cf_f 0 (by norm_num), cf_f 1 (by norm_num),
    cf_f 2 (by norm_num), cf_H_zero, cf_H_two]
  simp

/-- The weight-225 channel value is nonzero. -/
theorem cf_tv1_ne : cf 30 1 (tv1 fpoly Hpoly) ≠ 0 := by
  rw [cf_tv1_value]
  rw [show 24 * (f0 * (3168 * (f0 * f4) - 440 * f2 ^ 2)) - 40 * (f2 * (528 * (f0 * f2))) =
      ((1310284800 : ℝ) : ℂ) + ((2118758400 : ℝ) : ℂ) * gp by
    unfold f0 f2 f4
    push_cast
    linear_combination (405909504 * gp + 1196540928) * gp_sq']
  exact ne_zero_of_lin_gp (by norm_num) (by norm_num)

/-! ## `Tb` is injective in each degree -/

theorem Tb_eq_sum {B : P2} {n : ℕ} (hB : B ∈ binDeg (2 * n)) :
    Tb B = ∑ k : Fin (2 * n + 1), cf (2 * n) k B • wv n k := by
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    simp only [Set.mem_setOf_eq] at he
    beta_reduce
    rw [Tb_monomial, one_smul, tbm_of_deg he, monomial_eq_xy]
    simp only [cf_xy]
    rw [Finset.sum_eq_single ⟨e 1, by omega⟩]
    · rw [if_pos ⟨by simp; omega, rfl⟩, one_smul]
    · intro k _ hk
      rw [if_neg (fun h => hk (Fin.ext h.2.symm)), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, ← Finset.sum_add_distrib]; simp [add_smul]
  | smul c x _ hx =>
    rw [map_smul, hx, Finset.smul_sum]; simp [smul_smul]

theorem Tb_inj {B : P2} {n : ℕ} (hB : B ∈ binDeg (2 * n)) (h : Tb B = 0) : B = 0 := by
  rw [Tb_eq_sum hB] at h
  have hli := Fintype.linearIndependent_iff.mp (vn_linearIndependent n)
    (fun k => cf (2 * n) k B * cnk n k)
    (by rw [← h]; refine Finset.sum_congr rfl fun k _ => ?_; rw [wv, smul_smul])
  have hc : ∀ k : Fin (2 * n + 1), cf (2 * n) k B = 0 := fun k =>
    (mul_eq_zero.mp (hli k)).resolve_right (cnk_ne_zero n k)
  have hh := binDeg_hom hB
  ext e
  rw [coeff_zero]
  by_cases he : e 0 + e 1 = 2 * n
  · have := hc ⟨e 1, by omega⟩
    rw [cf, lcoeff_apply] at this
    have heq : Finsupp.single 0 (2 * n - e 1) + Finsupp.single 1 (e 1) = e := by
      ext i; fin_cases i <;> simp <;> omega
    rw [← heq]; exact this
  · apply hh.coeff_eq_zero
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]; exact he

theorem eval_one_zero {B : P2} {d : ℕ} (hB : B ∈ binDeg d) : eval ![1, 0] B = cf d 0 B := by
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    simp only [Set.mem_setOf_eq] at he
    beta_reduce
    rw [monomial_eq_xy, cf_xy]
    by_cases h : e 1 = 0
    · rw [if_pos ⟨by omega, h⟩, h]; simp
    · rw [if_neg (fun h' => h h'.2)]; simp [h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [MvPolynomial.smul_eval, map_smul, hx, smul_eq_mul]

end VOA.Classification.COne.OrbIco
