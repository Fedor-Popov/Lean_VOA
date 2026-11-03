/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTriple
import Mathlib.Combinatorics.Enumerative.Pentagonal

/-!
# Euler's pentagonal number theorem

  `(q;q)_∞ = ∑_{r ∈ ℤ} (-1)^r q^{r(3r-1)/2}`   (`euler_eq_pentagonal`)

as formal power series over any commutative ring.  This is the Jacobi triple product with
`q ↦ q³`, `u = q`; since `u = q` is not a unit of the coefficient ring, we rerun the finite
(Cauchy–MacMahon) argument of `jacobiTriple_finite` with `a = q^{3n}`, `b = -q`:

  `∏_{m<n}(1 - q^{3m+2}) ∏_{i<n}(1 - q^{3i+1}) = ∑_{k ≤ 2n} (-1)^{k-n} q^{p(k-n)} [2n, k]_{q³}`

(`pentagonal_finite`), and let `n → ∞`.
-/

namespace VOA.QSeries.JTP

open PowerSeries VOA.QSeries

open scoped BigOperators

noncomputable section

section Pentagonal

variable {R : Type*} [CommRing R]

theorem natAbs_le_pentagonal (r : ℤ) : r.natAbs ≤ pentagonal r + 1 := by
  have h := two_mul_natCast_pentagonal r
  zify
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr]; nlinarith
  · rw [abs_of_neg hr]; nlinarith

theorem neg_one_pow_eq_negSign (k n : ℕ) :
    ((-1 : R) ^ k) = (-1) ^ n * negSign ((k : ℤ) - n) := by
  rw [negSign_eq]
  rcases Nat.even_or_odd k with hk | hk <;> rcases Nat.even_or_odd n with hn | hn
  · rw [hk.neg_one_pow, hn.neg_one_pow, if_pos (by
      obtain ⟨a, rfl⟩ := hk; obtain ⟨b, rfl⟩ := hn; omega)]; ring
  · rw [hk.neg_one_pow, hn.neg_one_pow, if_neg (by
      obtain ⟨a, rfl⟩ := hk; obtain ⟨b, rfl⟩ := hn; omega)]; ring
  · rw [hk.neg_one_pow, hn.neg_one_pow, if_neg (by
      obtain ⟨a, rfl⟩ := hk; obtain ⟨b, rfl⟩ := hn; omega)]; ring
  · rw [hk.neg_one_pow, hn.neg_one_pow, if_pos (by
      obtain ⟨a, rfl⟩ := hk; obtain ⟨b, rfl⟩ := hn; omega)]; ring

/-- The finite pentagonal identity (division-free). -/
theorem pentagonal_finite (n : ℕ) :
    (∏ m ∈ Finset.range n, (1 - X ^ (3 * m + 2) : PowerSeries R)) *
        (∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 1) : PowerSeries R)) =
      ∑ k ∈ Finset.range (2 * n + 1),
        C (negSign ((k : ℤ) - n)) * X ^ pentagonal ((k : ℤ) - n) *
          gaussian (X ^ 3 : PowerSeries R) (2 * n) k := by
  set S := ∑ j ∈ Finset.range n, j with hS
  set E0 := 3 * n * n + (3 * S + n) with hE0
  have h := finite_qBinomial_homog (X ^ 3 : PowerSeries R) (X ^ (3 * n)) (-X) (2 * n)
  have hprod : (∏ j ∈ Finset.range (2 * n), (X ^ (3 * n) + -X * (X ^ 3) ^ j : PowerSeries R)) =
      (-1) ^ n * X ^ E0 *
        ((∏ m ∈ Finset.range n, (1 - X ^ (3 * m + 2) : PowerSeries R)) *
          (∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 1) : PowerSeries R))) := by
    rw [show 2 * n = n + n by ring, Finset.prod_range_add]
    have hlow : (∏ j ∈ Finset.range n, (X ^ (3 * n) + -X * (X ^ 3) ^ j : PowerSeries R)) =
        (-1) ^ n * X ^ (3 * S + n) *
          ∏ m ∈ Finset.range n, (1 - X ^ (3 * m + 2) : PowerSeries R) := by
      have hj : ∀ j ∈ Finset.range n, (X ^ (3 * n) + -X * (X ^ 3) ^ j : PowerSeries R) =
          (-X ^ (3 * j + 1)) * (1 - X ^ (3 * (n - 1 - j) + 2)) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hX : (X : PowerSeries R) ^ (3 * n) = X ^ (3 * j + 1) * X ^ (3 * (n - 1 - j) + 2) := by
          rw [← pow_add]; congr 1; omega
        rw [hX, ← pow_mul]
        ring
      rw [Finset.prod_congr rfl hj, Finset.prod_mul_distrib,
        Finset.prod_range_reflect (fun m => (1 - X ^ (3 * m + 2) : PowerSeries R)) n]
      congr 1
      have : (∏ j ∈ Finset.range n, (-X ^ (3 * j + 1) : PowerSeries R)) =
          (-1) ^ n * X ^ (∑ j ∈ Finset.range n, (3 * j + 1)) := by
        rw [← Finset.prod_pow_eq_pow_sum,
          show ((-1 : PowerSeries R)) ^ n = ∏ _j ∈ Finset.range n, (-1 : PowerSeries R) by
            rw [Finset.prod_const, Finset.card_range],
          ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl; intro j _; ring
      rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
        smul_eq_mul, mul_one]
    have hhigh : (∏ i ∈ Finset.range n, (X ^ (3 * n) + -X * (X ^ 3) ^ (n + i) : PowerSeries R)) =
        X ^ (3 * n * n) * ∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 1) : PowerSeries R) := by
      have hc : (∏ _i ∈ Finset.range n, (X ^ (3 * n) : PowerSeries R)) = X ^ (3 * n * n) := by
        rw [Finset.prod_const, Finset.card_range, ← pow_mul]
      rw [← hc, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_mul, show 3 * (n + i) = 3 * n + 3 * i by ring, pow_add]
      ring
    rw [hlow, hhigh, hE0, pow_add]
    ring
  rw [hprod] at h
  have hunit : IsUnit ((-1) ^ n : PowerSeries R) := (isUnit_one.neg).pow n
  have hterm : ∀ k ∈ Finset.range (2 * n + 1),
      weightedGaussian (X ^ 3 : PowerSeries R) (2 * n) k * (-X) ^ k * (X ^ (3 * n)) ^ (2 * n - k) =
        (-1) ^ n * (X ^ E0 * (C (negSign ((k : ℤ) - n)) * X ^ pentagonal ((k : ℤ) - n) *
          gaussian (X ^ 3 : PowerSeries R) (2 * n) k)) := by
    intro k hk
    have hk' : k ≤ 2 * n := by have := Finset.mem_range.mp hk; omega
    rw [weightedGaussian_eq, neg_pow, neg_one_pow_eq_negSign k n, ← pow_mul, ← pow_mul]
    have hexp : 3 * k.choose 2 + k + 3 * n * (2 * n - k) = E0 + pentagonal ((k : ℤ) - n) := by
      have h1 := two_mul_choose_two_add k
      have h2 := two_mul_natCast_pentagonal ((k : ℤ) - n)
      have h3 := two_mul_sum_range_id_add n
      rw [← hS] at h3
      rw [hE0]
      zify [hk'] at h1 h3 ⊢
      nlinarith [h1, h2, h3]
    have hC : (C (negSign ((k : ℤ) - n)) : PowerSeries R) = negSign ((k : ℤ) - n) := by
      rw [negSign, negSign, map_pow, map_neg, map_one]
    rw [hC]
    calc X ^ (3 * k.choose 2) * gaussian (X ^ 3 : PowerSeries R) (2 * n) k *
          ((-1) ^ n * negSign ((k : ℤ) - n) * X ^ k) * X ^ (3 * n * (2 * n - k))
        = (-1) ^ n * (X ^ (3 * k.choose 2 + k + 3 * n * (2 * n - k)) *
            (negSign ((k : ℤ) - n) * gaussian (X ^ 3 : PowerSeries R) (2 * n) k)) := by
          rw [pow_add, pow_add]; ring
      _ = _ := by rw [hexp, pow_add]; ring
  apply X_pow_mul_cancel E0
  apply hunit.mul_left_cancel
  calc (-1) ^ n * (X ^ E0 * ((∏ m ∈ Finset.range n, (1 - X ^ (3 * m + 2) : PowerSeries R)) *
          (∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 1) : PowerSeries R))))
      = (-1) ^ n * X ^ E0 * ((∏ m ∈ Finset.range n, (1 - X ^ (3 * m + 2) : PowerSeries R)) *
          (∏ i ∈ Finset.range n, (1 - X ^ (3 * i + 1) : PowerSeries R))) := by ring
    _ = _ := h
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl hterm

theorem prodFactors_three_two : ProdFactors fun m => (1 - X ^ (3 * m + 2) : PowerSeries R) :=
  prodFactors_one_sub_X_pow _ fun k => by omega

theorem prodFactors_three_one : ProdFactors fun m => (1 - X ^ (3 * m + 1) : PowerSeries R) :=
  prodFactors_one_sub_X_pow _ fun k => by omega

/-- The pentagonal series. -/
def pentSeries : PowerSeries R := zSeries (fun r => negSign r) pentagonal

/-- The sum side of the finite identity approximates `pentSeries / (q³;q³)_∞`. -/
theorem agreeTo_pentagonal_sum (n : ℕ) :
    AgreeTo n (∑ k ∈ Finset.range (2 * n + 1),
        C (negSign ((k : ℤ) - n)) * X ^ pentagonal ((k : ℤ) - n) *
          gaussian (X ^ 3 : PowerSeries R) (2 * n) k)
      (pentSeries * expand 3 (by norm_num) reciprocalEuler) := by
  have hterm : ∀ k ∈ Finset.range (2 * n + 1),
      AgreeTo n (C (negSign ((k : ℤ) - n)) * X ^ pentagonal ((k : ℤ) - n) *
          gaussian (X ^ 3 : PowerSeries R) (2 * n) k)
        (C (negSign ((k : ℤ) - n)) * X ^ pentagonal ((k : ℤ) - n) *
          expand 3 (by norm_num) (reciprocalEuler : PowerSeries R)) := by
    intro k hk
    have hk' : k ≤ 2 * n := by have := Finset.mem_range.mp hk; omega
    have h1 := (agreeTo_gaussian_reciprocalEuler (R := R) (2 * n) k hk').expand 3 (by norm_num)
    have hg : expand 3 (by norm_num) (gaussian (X : PowerSeries R) (2 * n) k) =
        gaussian (X ^ 3) (2 * n) k := by
      have := map_gaussian (expand 3 (by norm_num) : PowerSeries R →ₐ[R] PowerSeries R).toRingHom
        (X : PowerSeries R) (2 * n) k
      simpa [expand_X] using this
    rw [hg] at h1
    have h2 := (h1.X_pow_mul (pentagonal ((k : ℤ) - n))).mul_left (C (negSign ((k : ℤ) - n)))
    rw [← mul_assoc, ← mul_assoc] at h2
    apply h2.mono
    have hb := natAbs_le_pentagonal ((k : ℤ) - n)
    have hmin : min k (2 * n - k) + ((k : ℤ) - n).natAbs = n := by omega
    omega
  refine (AgreeTo.finset_sum _ hterm).trans ?_
  rw [← Finset.sum_mul]
  refine AgreeTo.mul_right _ ?_
  have hreindex : (∑ k ∈ Finset.range (2 * n + 1),
        C (negSign ((k : ℤ) - n)) * X ^ pentagonal ((k : ℤ) - n)) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, C (negSign j : R) * (X : PowerSeries R) ^ pentagonal j := by
    symm
    apply Finset.sum_nbij' (fun (j : ℤ) => (j + n).toNat) (fun (k : ℕ) => (k : ℤ) - n)
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      omega
    · intro k _
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have : ((j + n).toNat : ℤ) - n = j := by omega
      rw [this]
  rw [hreindex]
  refine (agreeTo_zSeries (fun r => (negSign r : R)) pentagonal natAbs_le_pentagonal
    (K := n) (Finset.Icc (-(n : ℤ)) n) (fun j hj => ?_)).symm
  have := natAbs_le_pentagonal j
  simp only [Finset.mem_Icc]
  omega

theorem infProd_triples {u : ℕ → PowerSeries R} (hu : ProdFactors u) :
    infProd (fun k => u (3 * k) * u (3 * k + 1) * u (3 * k + 2)) = infProd u := by
  have htri : ProdFactors fun k => u (3 * k) * u (3 * k + 1) * u (3 * k + 2) := fun k => by
    have h1 := (hu (3 * k)).mono (show k + 1 ≤ 3 * k + 1 by omega)
    have h2 := (hu (3 * k + 1)).mono (show k + 1 ≤ 3 * k + 1 + 1 by omega)
    have h3 := (hu (3 * k + 2)).mono (show k + 1 ≤ 3 * k + 2 + 1 by omega)
    simpa using (h1.mul h2).mul h3
  have hpart : ∀ N, (∏ k ∈ Finset.range N, (u (3 * k) * u (3 * k + 1) * u (3 * k + 2))) =
      ∏ k ∈ Finset.range (3 * N), u k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.prod_range_succ, ih, show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring,
          Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
        ring
  symm
  apply eq_infProd_of_agree htri
  intro N
  rw [hpart]
  exact ((agreeTo_infProd hu (3 * N)).mono (by omega))

/-- **Euler's pentagonal number theorem.** -/
theorem euler_eq_pentagonal : (euler : PowerSeries R) = pentSeries := by
  have hfin : (infProd fun m => (1 - X ^ (3 * m + 2) : PowerSeries R)) *
      infProd (fun m => (1 - X ^ (3 * m + 1) : PowerSeries R)) =
      pentSeries * expand 3 (by norm_num) reciprocalEuler := by
    apply eq_of_agreeTo
    intro N
    have hP := ((agreeTo_infProd (prodFactors_three_two (R := R)) (N + 1)).mono
      (Nat.le_succ _)).mul ((agreeTo_infProd (prodFactors_three_one (R := R)) (N + 1)).mono
        (Nat.le_succ _))
    exact (hP.trans (AgreeTo.of_eq (pentagonal_finite (N + 1)))).trans
      (agreeTo_pentagonal_sum (N + 1))
  have he3 : expand 3 (by norm_num) (euler : PowerSeries R) =
      infProd fun m => (1 - X ^ (3 * m + 3) : PowerSeries R) := by
    rw [euler_eq_infProd, expand_infProd 3 (by norm_num) (prodFactors_euler (R := R))]
    apply infProd_congr
    intro m
    rw [map_sub, map_one, map_pow, expand_X, ← pow_mul]
    congr 2
  have hinv : expand 3 (by norm_num) (reciprocalEuler : PowerSeries R) *
      expand 3 (by norm_num) euler = 1 := by
    rw [← map_mul, mul_comm, euler_mul_reciprocal, map_one]
  have key := congrArg (· * expand 3 (by norm_num) (euler : PowerSeries R)) hfin
  simp only at key
  rw [mul_assoc pentSeries, hinv, mul_one, he3,
    infProd_mul prodFactors_three_two prodFactors_three_one,
    infProd_mul (prodFactors_three_two.mul prodFactors_three_one)
      (prodFactors_one_sub_X_pow _ fun k => by omega)] at key
  rw [← key, euler_eq_infProd, ← infProd_triples prodFactors_euler]
  apply infProd_congr
  intro k
  rw [show 3 * k + 1 = 3 * k + 0 + 1 by ring, show 3 * k + 1 + 1 = 3 * k + 2 by ring,
    show 3 * k + 2 + 1 = 3 * k + 3 by ring]
  ring

end Pentagonal

end

end VOA.QSeries.JTP

section AxiomAudit
#print axioms VOA.QSeries.JTP.pentagonal_finite
#print axioms VOA.QSeries.JTP.euler_eq_pentagonal
end AxiomAudit
