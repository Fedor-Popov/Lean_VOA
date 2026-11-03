import VOA.DeligneAudit.SL4TThomChain
import Mathlib.Algebra.Polynomial.Inductions

/-! # The four polynomial identities used in the site induction -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-- The polynomial relation ideal for two alphabets. -/
def relationIdeal (p q : R[X]) (M : ℕ) : Ideal R[X] :=
  Ideal.span {p * q} ⊔ Ideal.span {X ^ M}

theorem relationIdeal_product (p q : R[X]) (M : ℕ) : p * q ∈ relationIdeal p q M :=
  (show Ideal.span {p * q} ≤ relationIdeal p q M from le_sup_left)
    (Ideal.subset_span (Set.mem_singleton _))

theorem relationIdeal_power (p q : R[X]) (M : ℕ) : X ^ M ∈ relationIdeal p q M :=
  (show Ideal.span {X ^ M} ≤ relationIdeal p q M from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton _))

theorem polynomial_divX_mul (p q : R[X]) :
    (p * q).divX = p.divX * q + Polynomial.C (p.coeff 0) * q.divX := by
  apply (Polynomial.isRegular_X (R := R)).left
  have hp := X_mul_divX_add p
  have hq := X_mul_divX_add q
  have hpq := X_mul_divX_add (p * q)
  rw [mul_coeff_zero, map_mul] at hpq
  linear_combination hpq - q * hp - Polynomial.C (p.coeff 0) * hq

/-- Identity (nn), before removing its invertible sign. -/
theorem polynomial_nn (p q : R[X]) (m : ℕ) :
    Polynomial.C (p.coeff 0 * q.coeff 0) * X ^ m =
      X ^ m * (p * q) - X ^ (m + 1) * (p * q).divX := by
  have h := X_mul_divX_add (p * q)
  rw [mul_coeff_zero] at h
  rw [pow_succ]
  linear_combination X ^ m * h

theorem polynomial_nn_mem (p q : R[X]) (m : ℕ) :
    Polynomial.C (p.coeff 0 * q.coeff 0) * X ^ m ∈ relationIdeal p q (m + 1) := by
  rw [polynomial_nn]
  exact (relationIdeal p q (m + 1)).sub_mem
    ((relationIdeal p q (m + 1)).mul_mem_left _ (relationIdeal_product p q (m + 1)))
    ((relationIdeal p q (m + 1)).mul_mem_right _ (relationIdeal_power p q (m + 1)))

/-- Identity (ng). -/
theorem polynomial_ng (p q : R[X]) (z : R) :
    Polynomial.C z * X * p * q.divX =
      Polynomial.C z * (p * q) - p * Polynomial.C (z * q.coeff 0) := by
  have h := X_mul_divX_add q
  rw [map_mul]
  linear_combination Polynomial.C z * p * h

theorem polynomial_ng_mem (p q : R[X]) (M : ℕ) (z : R) (I : Ideal R)
    (hz : z * q.coeff 0 ∈ I) :
    Polynomial.C z * X * p * q.divX ∈ relationIdeal p q M ⊔ I.map Polynomial.C := by
  let J := relationIdeal p q M ⊔ I.map Polynomial.C
  have hA : relationIdeal p q M ≤ J := le_sup_left
  have hI : I.map Polynomial.C ≤ J := le_sup_right
  rw [polynomial_ng]
  exact J.sub_mem
    (J.mul_mem_left _ (hA (relationIdeal_product p q M)))
    (J.mul_mem_left _ (hI (Ideal.mem_map_of_mem Polynomial.C hz)))

/-- Dividing the complementary factorization by `X`, without cancellation assumptions on `R`. -/
theorem polynomial_complement_divX (q qb : R[X]) (m : ℕ)
    (h : q * qb = X ^ (m + 1)) :
    X ^ m = qb.divX * q + q.divX * Polynomial.C (qb.coeff 0) := by
  have hd := congrArg Polynomial.divX ((mul_comm qb q).trans h)
  rw [polynomial_divX_mul, divX_X_pow, if_neg (by omega), Nat.add_sub_cancel] at hd
  simpa only [mul_comm] using hd.symm

/-- Identity (both), including the additional term supported on the preceding ideal. -/
theorem polynomial_both (p q qb : R[X]) (m : ℕ)
    (h : q * qb = X ^ (m + 1)) :
    Polynomial.C (qb.coeff 0) * X * p.divX * q.divX =
      p.divX * X ^ (m + 1) + Polynomial.C (p.coeff 0) * X ^ m -
        qb.divX * (p * q) -
          (Polynomial.C (qb.coeff 0) * q.divX) * Polynomial.C (p.coeff 0) := by
  have hd := polynomial_complement_divX q qb m h
  have hp := X_mul_divX_add p
  rw [pow_succ]
  linear_combination -p * hd +
    (Polynomial.C (qb.coeff 0) * q.divX - X ^ m) * hp

theorem polynomial_both_mem (p q qb : R[X]) (m : ℕ) (I : Ideal R)
    (h : q * qb = X ^ (m + 1)) (hp : p.coeff 0 ∈ I) :
    Polynomial.C (qb.coeff 0) * X * p.divX * q.divX ∈
      relationIdeal p q (m + 1) ⊔ I.map Polynomial.C := by
  let J := relationIdeal p q (m + 1) ⊔ I.map Polynomial.C
  have hA : relationIdeal p q (m + 1) ≤ J := le_sup_left
  have hI : I.map Polynomial.C ≤ J := le_sup_right
  have hc : Polynomial.C (p.coeff 0) ∈ J :=
    hI (Ideal.mem_map_of_mem Polynomial.C hp)
  have hprod : p * q ∈ J := hA (relationIdeal_product p q (m + 1))
  have hpow : X ^ (m + 1) ∈ J := hA (relationIdeal_power p q (m + 1))
  rw [polynomial_both p q qb m h]
  exact J.sub_mem (J.sub_mem (J.add_mem (J.mul_mem_left _ hpow)
    (J.mul_mem_right _ hc)) (J.mul_mem_left _ hprod)) (J.mul_mem_left _ hc)

/-- Identity (gn). -/
theorem polynomial_gn (p q : R[X]) :
    X * p.divX * q = p * q - q * Polynomial.C (p.coeff 0) := by
  have h := X_mul_divX_add p
  linear_combination q * h

theorem polynomial_gn_mem (p q : R[X]) (M : ℕ) (I : Ideal R)
    (hp : p.coeff 0 ∈ I) :
    X * p.divX * q ∈ relationIdeal p q M ⊔ I.map Polynomial.C := by
  let J := relationIdeal p q M ⊔ I.map Polynomial.C
  have hA : relationIdeal p q M ≤ J := le_sup_left
  have hI : I.map Polynomial.C ≤ J := le_sup_right
  rw [polynomial_gn]
  exact J.sub_mem (hA (relationIdeal_product p q M))
    (J.mul_mem_left _ (hI (Ideal.mem_map_of_mem Polynomial.C hp)))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.polynomial_divX_mul
#print axioms VOA.DeligneAudit.SL4T.polynomial_nn
#print axioms VOA.DeligneAudit.SL4T.polynomial_nn_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_ng
#print axioms VOA.DeligneAudit.SL4T.polynomial_ng_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_complement_divX
#print axioms VOA.DeligneAudit.SL4T.polynomial_both
#print axioms VOA.DeligneAudit.SL4T.polynomial_both_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_gn
#print axioms VOA.DeligneAudit.SL4T.polynomial_gn_mem
