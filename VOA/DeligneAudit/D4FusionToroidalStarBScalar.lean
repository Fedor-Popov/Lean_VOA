import VOA.DeligneAudit.D4FusionToroidalFusionPolynomial

/-!
# Scalar reduction of the two-variable complete homogeneous polynomials (★b, scalar part)

Let `z : Fin m → ℂ` be the evaluation points, `P = ∏ (X − z_q)` their point polynomial,
`h_N(x, y) = ∑_{a+b=N} x^a y^b`.  On the off-diagonal pairs `(z_q, z_p)`, `q ≠ p`, the
function `h_N` lies in the span of the monomials `x^a y^b` with `a + b < N` as soon as
`N ≥ m − 1` (`hvec_mem`).  Two inputs:

* the divided difference `(P(x) − P(y))/(x − y) = ∑_s c_s h_{s−1}(x, y)` vanishes at two
  distinct roots (`divided_difference`), which reduces `h_{m−1}`;
* `h_{N+1} = x h_N + y^{N+1}`, and `y^{N+1}` reduces by `P(y) = 0` for `N + 1 ≥ m`.

This is the scalar content of the probe's identity for `P^{(1)}_N v_F`, in the form that
transfers directly to the tensor model (see `D4FusionToroidalStarB`).
-/

namespace VOA.DeligneAudit.Toroidal.StarB

open Finset

noncomputable section

/-- The complete homogeneous polynomial `h_N(x, y) = ∑_{a+b=N} x^a y^b`. -/
def hN (N : ℕ) (x y : ℂ) : ℂ := ∑ p ∈ antidiagonal N, x ^ p.1 * y ^ p.2

theorem hN_succ (N : ℕ) (x y : ℂ) : hN (N + 1) x y = x * hN N x y + y ^ (N + 1) := by
  simp only [hN, Nat.sum_antidiagonal_succ, pow_zero, one_mul, mul_sum]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  ring

theorem sub_mul_hN (N : ℕ) (x y : ℂ) : (x - y) * hN N x y = x ^ (N + 1) - y ^ (N + 1) := by
  rw [hN, Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_comm, ← geom_sum₂_mul x y (N + 1)]
  congr 1

section Points

variable {m : ℕ} (z : Fin m → ℂ)

theorem coeff_top : (pointPolynomial z).coeff m = 1 := by
  have h := (pointPolynomial_monic z).coeff_natDegree
  rwa [pointPolynomial_degree] at h

/-- At a root, `x^m = −∑_{s<m} c_s x^s`. -/
theorem root_pow (x : ℂ) (hx : (pointPolynomial z).eval x = 0) :
    x ^ m = -∑ s ∈ range m, (pointPolynomial z).coeff s * x ^ s := by
  have h := hx
  rw [Polynomial.eval_eq_sum_range, pointPolynomial_degree, sum_range_succ, coeff_top,
    one_mul] at h
  exact eq_neg_of_add_eq_zero_right h

theorem root_pow_high (x : ℂ) (hx : (pointPolynomial z).eval x = 0) (k : ℕ) (hk : m ≤ k) :
    x ^ k = -∑ s ∈ range m, (pointPolynomial z).coeff s * x ^ (k - m + s) := by
  have hsplit : x ^ k = x ^ (k - m) * x ^ m := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, root_pow z x hx, mul_neg, mul_sum]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [pow_add]
  ring

/-- The divided difference of the point polynomial vanishes at two distinct roots. -/
theorem divided_difference (x y : ℂ) (hxy : x ≠ y)
    (hx : (pointPolynomial z).eval x = 0) (hy : (pointPolynomial z).eval y = 0) :
    ∑ s ∈ range m, (pointPolynomial z).coeff (s + 1) * hN s x y = 0 := by
  have h1 : (x - y) * ∑ s ∈ range m, (pointPolynomial z).coeff (s + 1) * hN s x y =
      (pointPolynomial z).eval x - (pointPolynomial z).eval y := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, pointPolynomial_degree,
      sum_range_succ', sum_range_succ', mul_sum]
    simp only [pow_zero, mul_one]
    rw [add_sub_add_right_eq_sub, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← mul_sub, ← sub_mul_hN]
    ring
  rw [hx, hy, sub_zero] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h) hxy
  · exact h

/-- Off-diagonal site pairs. -/
abbrev Pairs (m : ℕ) := {r : Fin m × Fin m // r.1 ≠ r.2}

/-- The monomial `z_q^a z_p^b` on off-diagonal pairs. -/
def mon (a b : ℕ) : Pairs m → ℂ := fun r => z r.1.1 ^ a * z r.1.2 ^ b

/-- `h_N(z_q, z_p)` on off-diagonal pairs. -/
def hvec (N : ℕ) : Pairs m → ℂ := fun r => hN N (z r.1.1) (z r.1.2)

/-- Functions spanned by the monomials of total degree `< N`. -/
def lowSpan (N : ℕ) : Submodule ℂ (Pairs m → ℂ) :=
  Submodule.span ℂ {φ | ∃ a b, a + b < N ∧ φ = mon z a b}

theorem hvec_eq_sum (N : ℕ) : hvec z N = ∑ p ∈ antidiagonal N, mon z p.1 p.2 := by
  funext r
  simp [hvec, hN, mon, Finset.sum_apply]

theorem mon_mem (a b N : ℕ) (h : a + b < N) : mon z a b ∈ lowSpan z N :=
  Submodule.subset_span ⟨a, b, h, rfl⟩

theorem hvec_mem_of_lt (s N : ℕ) (h : s < N) : hvec z s ∈ lowSpan z N := by
  rw [hvec_eq_sum]
  refine Submodule.sum_mem _ fun p hp => ?_
  rw [mem_antidiagonal] at hp
  exact mon_mem z p.1 p.2 N (by omega)

/-- Multiplication by the first coordinate. -/
def mulFirst : (Pairs m → ℂ) →ₗ[ℂ] (Pairs m → ℂ) :=
  LinearMap.mulLeft ℂ (fun r : Pairs m => z r.1.1)

theorem mulFirst_apply (φ : Pairs m → ℂ) (r : Pairs m) :
    mulFirst z φ r = z r.1.1 * φ r := rfl

theorem mulFirst_lowSpan (N : ℕ) :
    Submodule.map (mulFirst z) (lowSpan z N) ≤ lowSpan z (N + 1) := by
  rw [lowSpan, Submodule.map_span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  have h : mulFirst z (mon z a b) = mon z (a + 1) b := by
    funext r
    simp only [mulFirst_apply, mon, pow_succ]
    ring
  rw [h]
  exact mon_mem z (a + 1) b (N + 1) (by omega)

/-- **The scalar reduction**: for `N ≥ m − 1`, `h_N(z_q, z_p)` on off-diagonal pairs is a
combination of the monomials of total degree `< N`. -/
theorem hvec_mem (hz : Function.Injective z) (N : ℕ) (hN : m ≤ N + 1) :
    hvec z N ∈ lowSpan z N := by
  rcases m with _ | M
  · have h0 : hvec z N = 0 := funext fun r => r.1.1.elim0
    rw [h0]
    exact Submodule.zero_mem _
  obtain ⟨k, rfl⟩ : ∃ k, N = M + k := ⟨N - M, by omega⟩
  induction k with
  | zero =>
    have heq : hvec z (M + 0) =
        -∑ s ∈ range M, (pointPolynomial z).coeff (s + 1) • hvec z s := by
      funext r
      have hd := divided_difference z (z r.1.1) (z r.1.2) (hz.ne r.2)
        (pointPolynomial_root z _) (pointPolynomial_root z _)
      rw [sum_range_succ, coeff_top, one_mul] at hd
      simp only [Nat.add_zero, hvec, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact eq_neg_of_add_eq_zero_right hd
    rw [heq]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ ?_)
    exact hvec_mem_of_lt z s _ (by have := mem_range.mp hs; omega)
  | succ k ih =>
    have ih' := ih (by omega)
    have heq : hvec z (M + (k + 1)) = mulFirst z (hvec z (M + k)) +
        -∑ s ∈ range (M + 1),
          (pointPolynomial z).coeff s • mon z 0 (M + k + 1 - (M + 1) + s) := by
      funext r
      simp only [hvec, Pi.add_apply, mulFirst_apply, Pi.neg_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, mon, pow_zero, one_mul]
      rw [show M + (k + 1) = M + k + 1 by omega, hN_succ,
        root_pow_high z (z r.1.2) (pointPolynomial_root z _) (M + k + 1) (by omega)]
    rw [heq]
    refine Submodule.add_mem _ ?_ ?_
    · exact mulFirst_lowSpan z (M + k) (Submodule.mem_map_of_mem ih')
    · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ ?_)
      have := mem_range.mp hs
      exact mon_mem z 0 _ _ (by omega)

end Points

end

end VOA.DeligneAudit.Toroidal.StarB

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.StarB.divided_difference
#print axioms VOA.DeligneAudit.Toroidal.StarB.hvec_mem
end AxiomAudit
