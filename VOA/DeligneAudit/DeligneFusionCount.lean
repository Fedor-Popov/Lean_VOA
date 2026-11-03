/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionInverse

/-!
# U5: the `q = 1` counts

* `demazureHilb n` (the Gelfand–Tsetlin polynomial `P_{(2n,n,0)}(1,1,1;q,0)`) is the coefficient
  sequence of an explicit polynomial `demazureQPoly n` (`coeff_demazureQPoly`), whose value at
  `q = 1` is `9ⁿ` (`demazureQPoly_eval_one`); hence `∑_N demazureHilb n N = 9ⁿ`
  (`sum_demazureHilb`).
* The `fusionF m` is the power series of a polynomial `fusionPoly m` (`fusionPoly_coe`), and
  `fusionPoly m (1) = 8^m` (`fusionPoly_eval_one`), by binomial inversion of
  `9ⁿ = ∑_d C(n,d) 8^{n-d}`; hence `∑_N [q^N] fusionF m = 8^m` (`sum_coeff_fusionF`).

The `q = 1` value of the Gelfand–Tsetlin sum is
`∑_{a,b ≤ n} C(n,a) C(n,b) 2^{n-a+b} = 2ⁿ (3/2)ⁿ 3ⁿ = 9ⁿ`.
-/

namespace VOA.DeligneAudit.A2

open Polynomial VOA.DeligneGaussian

open scoped BigOperators

noncomputable section

/-! ## Gaussian binomials as polynomials -/

theorem map_qbinom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (q : R) :
    ∀ n k : ℕ, φ (qbinom q n k) = qbinom (φ q) n k
  | _, 0 => by simp
  | 0, _ + 1 => by simp [qbinom]
  | n + 1, k + 1 => by
      rw [qbinom_succ_succ, qbinom_succ_succ, map_add, map_mul, map_pow, map_qbinom φ q n k,
        map_qbinom φ q n (k + 1)]

theorem qbinom_one : ∀ n k : ℕ, qbinom (1 : ℚ) n k = (n.choose k : ℚ)
  | _, 0 => by simp
  | 0, _ + 1 => by simp [qbinom]
  | n + 1, k + 1 => by
      rw [qbinom_succ_succ, one_pow, one_mul, qbinom_one n k, qbinom_one n (k + 1),
        Nat.choose_succ_succ]
      push_cast; ring

theorem coeff_qbinom_X : ∀ n k N : ℕ,
    (qbinom (X : ℚ[X]) n k).coeff N = (qbinomCoeff n k N : ℚ)
  | _, 0, N => by
      rw [qbinom_zero_right, coeff_one]
      cases N <;> simp [qbinomCoeff]
  | 0, k + 1, N => by simp [qbinom, qbinomCoeff]
  | n + 1, k + 1, N => by
      rw [qbinom_succ_succ, coeff_add, coeff_X_pow_mul', coeff_qbinom_X n k,
        coeff_qbinom_X n (k + 1), qbinomCoeff]
      split_ifs <;> simp

/-- `conv` is the coefficient of a product of polynomials. -/
theorem coeff_mul_eq_convQ {p r : ℚ[X]} {f g : ℕ → ℕ} (hp : ∀ N, p.coeff N = f N)
    (hr : ∀ N, r.coeff N = g N) (N : ℕ) : (p * r).coeff N = (conv f g N : ℚ) := by
  rw [coeff_mul, conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  simp [hp, hr]

/-! ## The Gelfand–Tsetlin polynomial -/

/-- `P_{(m₁,m₂)}(1,1;q,0)`. -/
def gl2Poly (m₁ m₂ : ℕ) : ℚ[X] :=
  ∑ ν ∈ Finset.Icc m₂ m₁, qbinom (X : ℚ[X]) (m₁ - m₂) (m₁ - ν)

/-- `P_{(l₁,l₂,l₃)}(1,1,1;q,0)`. -/
def gl3Poly (l₁ l₂ l₃ : ℕ) : ℚ[X] :=
  ∑ m₁ ∈ Finset.Icc l₂ l₁, ∑ m₂ ∈ Finset.Icc l₃ l₂,
    qbinom (X : ℚ[X]) (l₁ - l₂) (l₁ - m₁) * qbinom (X : ℚ[X]) (l₂ - l₃) (l₂ - m₂) *
      gl2Poly m₁ m₂

/-- The Demazure polynomial `Hilb_q D(1,nθ)` (as the `demazureHilb n`). -/
def demazureQPoly (n : ℕ) : ℚ[X] := gl3Poly (2 * n) n 0

theorem coeff_gl2Poly (m₁ m₂ N : ℕ) : (gl2Poly m₁ m₂).coeff N = (gl2Hilb m₁ m₂ N : ℚ) := by
  rw [gl2Poly, finsetSum_coeff, gl2Hilb]
  push_cast
  exact Finset.sum_congr rfl fun ν _ => coeff_qbinom_X _ _ _

theorem coeff_gl3Poly (l₁ l₂ l₃ N : ℕ) :
    (gl3Poly l₁ l₂ l₃).coeff N = (gl3Hilb l₁ l₂ l₃ N : ℚ) := by
  rw [gl3Poly, finsetSum_coeff, gl3Hilb]
  push_cast
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  exact coeff_mul_eq_convQ (fun M => coeff_mul_eq_convQ (coeff_qbinom_X _ _) (coeff_qbinom_X _ _) M)
    (coeff_gl2Poly m₁ m₂) N

theorem coeff_demazureQPoly (n N : ℕ) : (demazureQPoly n).coeff N = (demazureHilb n N : ℚ) :=
  coeff_gl3Poly _ _ _ _

theorem demazureQPoly_coe (n : ℕ) : (demazureQPoly n : PowerSeries ℚ) = demazureHilbSeries n := by
  ext N
  rw [Polynomial.coeff_coe, coeff_demazureQPoly, demazureHilbSeries, PowerSeries.coeff_mk]

/-! ## The value at `q = 1` -/

theorem eval_one_qbinom (n k : ℕ) : (qbinom (X : ℚ[X]) n k).eval 1 = (n.choose k : ℚ) := by
  rw [← coe_evalRingHom, map_qbinom, coe_evalRingHom, eval_X, qbinom_one]

theorem gl2Poly_eval_one (m₁ m₂ : ℕ) (h : m₂ ≤ m₁) : (gl2Poly m₁ m₂).eval 1 = 2 ^ (m₁ - m₂) := by
  rw [gl2Poly, eval_finsetSum]
  simp only [eval_one_qbinom]
  have : ∑ ν ∈ Finset.Icc m₂ m₁, ((m₁ - m₂).choose (m₁ - ν) : ℚ) =
      ∑ i ∈ Finset.range (m₁ - m₂ + 1), ((m₁ - m₂).choose i : ℚ) := by
    apply Finset.sum_nbij' (fun ν => m₁ - ν) (fun i => m₁ - i)
    · intro ν hν; simp only [Finset.mem_Icc] at hν; simp only [Finset.mem_range]; omega
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro ν hν; simp only [Finset.mem_Icc] at hν; omega
    · intro i hi; simp only [Finset.mem_range] at hi; omega
    · intro ν _; rfl
  rw [this]
  exact_mod_cast Nat.sum_range_choose (m₁ - m₂)

/-- **`Hilb_q D(1,nθ)` at `q = 1` is `9ⁿ`** (Gelfand–Tsetlin count). -/
theorem demazureQPoly_eval_one (n : ℕ) : (demazureQPoly n).eval 1 = 9 ^ n := by
  rw [demazureQPoly, gl3Poly, eval_finsetSum]
  simp only [eval_finsetSum, eval_mul, eval_one_qbinom]
  -- reindex `a = 2n - m₁`, `b = n - m₂`
  have h1 : ∀ m₁ ∈ Finset.Icc n (2 * n), ∀ m₂ ∈ Finset.Icc 0 n,
      ((2 * n - n).choose (2 * n - m₁) : ℚ) * ((n - 0).choose (n - m₂) : ℚ) *
        (gl2Poly m₁ m₂).eval 1 =
      (n.choose (2 * n - m₁) : ℚ) * (n.choose (n - m₂) : ℚ) * 2 ^ (m₁ - m₂) := by
    intro m₁ hm₁ m₂ hm₂
    simp only [Finset.mem_Icc] at hm₁ hm₂
    rw [gl2Poly_eval_one _ _ (by omega), show 2 * n - n = n by omega, Nat.sub_zero]
  rw [Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => h1 m₁ hm₁ m₂ hm₂]
  have h2 : ∑ m₁ ∈ Finset.Icc n (2 * n), ∑ m₂ ∈ Finset.Icc 0 n,
      (n.choose (2 * n - m₁) : ℚ) * (n.choose (n - m₂) : ℚ) * 2 ^ (m₁ - m₂) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
        (n.choose a : ℚ) * (n.choose b : ℚ) * 2 ^ (n - a + b) := by
    apply Finset.sum_nbij' (fun m₁ => 2 * n - m₁) (fun a => 2 * n - a)
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; omega
    · intro a ha; simp only [Finset.mem_range] at ha; omega
    · intro m₁ hm₁
      simp only [Finset.mem_Icc] at hm₁
      apply Finset.sum_nbij' (fun m₂ => n - m₂) (fun b => n - b)
      · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
      · intro b hb; simp only [Finset.mem_range] at hb; simp only [Finset.mem_Icc]; omega
      · intro m hm; simp only [Finset.mem_Icc] at hm; omega
      · intro b hb; simp only [Finset.mem_range] at hb; omega
      · intro m₂ hm₂
        simp only [Finset.mem_Icc] at hm₂
        rw [show m₁ - m₂ = n - (2 * n - m₁) + (n - m₂) by omega]
  rw [h2]
  have h3 : ∀ a ∈ Finset.range (n + 1), ∀ b ∈ Finset.range (n + 1),
      (n.choose a : ℚ) * (n.choose b : ℚ) * 2 ^ (n - a + b) =
      2 ^ n * ((n.choose a : ℚ) * (1 / 2) ^ a) * ((n.choose b : ℚ) * 2 ^ b) := by
    intro a ha b _
    simp only [Finset.mem_range] at ha
    rw [pow_add, show (2 : ℚ) ^ (n - a) = 2 ^ n * (1 / 2) ^ a by
      rw [one_div, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ two_ne_zero), ← pow_add,
        Nat.sub_add_cancel (by omega)]]
    ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => h3 a ha b hb]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have e1 : ∑ a ∈ Finset.range (n + 1), (n.choose a : ℚ) * (1 / 2) ^ a = (3 / 2) ^ n := by
    rw [show (3 / 2 : ℚ) = 1 / 2 + 1 by norm_num, add_pow]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∑ b ∈ Finset.range (n + 1), (n.choose b : ℚ) * 2 ^ b = 3 ^ n := by
    rw [show (3 : ℚ) = 2 + 1 by norm_num, add_pow]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e1, e2, ← mul_pow, ← mul_pow]
  norm_num

/-- **`∑_N demazureHilb n N = 9ⁿ`**, for any cutoff beyond the degree. -/
theorem sum_demazureHilb (n B : ℕ) (hB : (demazureQPoly n).natDegree < B) :
    ∑ N ∈ Finset.range B, demazureHilb n N = 9 ^ n := by
  have h := demazureQPoly_eval_one n
  rw [eval_eq_sum_range' hB] at h
  simp only [one_pow, mul_one, coeff_demazureQPoly] at h
  exact_mod_cast h

/-! ## `fusionF` is a polynomial with value `8^m` at `q = 1` -/

/-- `fusionF` as a polynomial (same recursion). -/
def fusionPoly : ℕ → ℚ[X]
  | n => demazureQPoly n -
      ∑ d : Fin n, X ^ ((d.1 + 1) * n) * qbinom (X : ℚ[X]) n (d.1 + 1) * fusionPoly (n - (d.1 + 1))
decreasing_by omega

theorem fusionPoly_eq (n : ℕ) : fusionPoly n = demazureQPoly n -
    ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) * qbinom (X : ℚ[X]) n (d + 1) *
      fusionPoly (n - (d + 1)) := by
  rw [fusionPoly, Fin.sum_univ_eq_sum_range (fun d => X ^ ((d + 1) * n) *
    qbinom (X : ℚ[X]) n (d + 1) * fusionPoly (n - (d + 1))) n]

/-- `fusionF m` is the power series of `fusionPoly m`. -/
theorem fusionPoly_coe (n : ℕ) : (fusionPoly n : PowerSeries ℚ) = fusionF n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [fusionPoly_eq, fusionF_eq, Polynomial.coe_sub, demazureQPoly_coe]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_range] at hd
    rw [map_mul, map_mul, map_pow, map_qbinom, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, ih _ (by omega)]

/-- **`fusionF m` at `q = 1` is `8^m`** (binomial inversion of `9ⁿ = ∑_d C(n,d) 8^{n-d}`). -/
theorem fusionPoly_eval_one (n : ℕ) : (fusionPoly n).eval 1 = 8 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [fusionPoly_eq, eval_sub, demazureQPoly_eval_one, eval_finsetSum]
    have h : ∀ d ∈ Finset.range n, (X ^ ((d + 1) * n) * qbinom (X : ℚ[X]) n (d + 1) *
        fusionPoly (n - (d + 1))).eval 1 = (n.choose (d + 1) : ℚ) * 8 ^ (n - (d + 1)) := by
      intro d hd
      simp only [Finset.mem_range] at hd
      rw [eval_mul, eval_mul, eval_pow, eval_X, one_pow, one_mul, eval_one_qbinom,
        ih _ (by omega)]
    rw [Finset.sum_congr rfl h]
    have hb : (9 : ℚ) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * 8 ^ (n - k) := by
      have := add_pow (1 : ℚ) 8 n
      rw [show (1 : ℚ) + 8 = 9 by norm_num] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hb, Finset.sum_range_succ']
    simp

/-- **`∑_N [q^N] fusionF m = 8^m`**, for any cutoff beyond the degree. -/
theorem sum_coeff_fusionF (m B : ℕ) (hB : (fusionPoly m).natDegree < B) :
    ∑ N ∈ Finset.range B, PowerSeries.coeff N (fusionF m) = 8 ^ m := by
  have h := fusionPoly_eval_one m
  rw [eval_eq_sum_range' hB] at h
  simp only [one_pow, mul_one] at h
  rw [← h, ← fusionPoly_coe]
  exact Finset.sum_congr rfl fun N _ => Polynomial.coeff_coe _ _

/-- `fusionF m` has finitely many nonzero coefficients. -/
theorem coeff_fusionF_eq_zero (m N : ℕ) (hN : (fusionPoly m).natDegree < N) :
    PowerSeries.coeff N (fusionF m) = 0 := by
  rw [← fusionPoly_coe, Polynomial.coeff_coe]
  exact coeff_eq_zero_of_natDegree_lt hN

/-! ## The forms used by the fusion recursion -/

theorem demazureHilb_sum (n : ℕ) : ∃ B, (∀ N, B ≤ N → demazureHilb n N = 0) ∧
    ∑ N ∈ Finset.range B, demazureHilb n N = 9 ^ n := by
  refine ⟨(demazureQPoly n).natDegree + 1, fun N hN => ?_, sum_demazureHilb n _ (by omega)⟩
  have h := coeff_eq_zero_of_natDegree_lt (p := demazureQPoly n) (n := N) (by omega)
  rw [coeff_demazureQPoly] at h
  exact_mod_cast h

theorem fusionF_sum (m : ℕ) : ∃ B, (∀ b, B ≤ b → PowerSeries.coeff b (fusionF m) = 0) ∧
    ∑ b ∈ Finset.range B, PowerSeries.coeff b (fusionF m) = 8 ^ m :=
  ⟨(fusionPoly m).natDegree + 1, fun b hb => coeff_fusionF_eq_zero m b (by omega),
    sum_coeff_fusionF m _ (by omega)⟩

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.demazureQPoly_coe
#print axioms VOA.DeligneAudit.A2.demazureQPoly_eval_one
#print axioms VOA.DeligneAudit.A2.sum_demazureHilb
#print axioms VOA.DeligneAudit.A2.fusionPoly_coe
#print axioms VOA.DeligneAudit.A2.fusionPoly_eval_one
#print axioms VOA.DeligneAudit.A2.sum_coeff_fusionF
#print axioms VOA.DeligneAudit.A2.coeff_fusionF_eq_zero
#print axioms VOA.DeligneAudit.A2.demazureHilb_sum
#print axioms VOA.DeligneAudit.A2.fusionF_sum
end AxiomAudit
