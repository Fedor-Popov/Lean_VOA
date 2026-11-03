/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CharacterInterface
import VOA.DeligneAudit.GaussianTransform

/-!
# The A₂ star identity as a power-series identity

`StarIdentity` (`A2CharacterInterface`) says `demazureCoeff N = productCoeff N` for every `N`.
This file moves both sides from the computable coefficient functions into `PowerSeries ℤ`:

* `coeff_qbinom`: `qbinomCoeff n k` is the coefficient sequence of the Gaussian binomial
  `DeligneGaussian.qbinom X n k` of `GaussianTransform.lean`;
* `partSeries_mul_poch`: the series of `partitionsLe n` is the inverse of `(q;q)_n`;
* `coeff_fermionProd`: `fermionCoeff R` is the coefficient sequence of `∏_{r=1}^{R} (1+q^r)^8`;
* `demazurePoly`: `Hilb D(1,nθ) = ∑_{i,j ≤ n} [n,i][n,j] G_{n-i+j}` with `G_M = ∑_r [M,r]`
  (the Rogers–Szegő value at `1`); `coeff_demazurePoly` identifies it with `demazureHilb`.

The residual is then the single named power-series statement `StarSeriesIdentity`, equivalent
to `StarIdentity` (`starIdentity_iff_series`).
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.DeligneGaussian

/-- Shorthand for the formal variable. -/
local notation "q" => (PowerSeries.X : PowerSeries ℤ)

/-! ## Products of coefficient functions -/

theorem coeff_mul_eq_conv (f g : ℕ → ℕ) (φ ψ : PowerSeries ℤ)
    (hφ : ∀ N, coeff N φ = f N) (hψ : ∀ N, coeff N ψ = g N) (N : ℕ) :
    coeff N (φ * ψ) = (conv f g N : ℤ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i φ * coeff j ψ)]
  simp [conv, hφ, hψ]

/-! ## Gaussian binomials -/

theorem coeff_qbinom : ∀ n k N, coeff N (qbinom q n k) = (qbinomCoeff n k N : ℤ)
  | _, 0, N => by
      rw [qbinom_zero_right, coeff_one]
      simp [qbinomCoeff]
  | 0, k + 1, N => by simp [qbinom, qbinomCoeff]
  | n + 1, k + 1, N => by
      rw [qbinom_succ_succ, map_add, coeff_X_pow_mul', coeff_qbinom n k, coeff_qbinom n (k + 1)]
      simp only [qbinomCoeff]
      split_ifs <;> push_cast <;> ring

/-! ## `1/(q;q)_n` -/

theorem partitionsLe_succ (n N : ℕ) :
    partitionsLe (n + 1) N =
      partitionsLe n N + if n + 1 ≤ N then partitionsLe (n + 1) (N - (n + 1)) else 0 := by
  rw [partitionsLe, Finset.sum_range_succ']
  simp only [zero_mul, Nat.sub_zero]
  split_ifs with h
  · rw [partitionsLe, Nat.div_eq_sub_div (Nat.succ_pos n) h, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Nat.sub_sub, add_mul, one_mul, add_comm]
  · rw [Nat.div_eq_of_lt (Nat.lt_of_not_le h)]
    simp

/-- The series `∑_N partitionsLe n N q^N`. -/
noncomputable def partSeries (n : ℕ) : PowerSeries ℤ := PowerSeries.mk fun N => (partitionsLe n N : ℤ)

/-- `(q;q)_n = ∏_{j=1}^{n} (1 - q^j)`. -/
noncomputable def poch (n : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.range n, (1 - q ^ (j + 1))

theorem partSeries_succ_mul (n : ℕ) :
    partSeries (n + 1) * (1 - q ^ (n + 1)) = partSeries n := by
  ext N
  rw [mul_sub, mul_one, map_sub, mul_comm, coeff_X_pow_mul']
  simp only [partSeries, coeff_mk]
  rw [partitionsLe_succ n N]
  split_ifs <;> push_cast <;> ring

theorem partSeries_zero : partSeries 0 = 1 := by
  ext N
  simp [partSeries, partitionsLe, coeff_one]

/-- **`partitionsLe n` is the coefficient sequence of `1/(q;q)_n`.** -/
theorem partSeries_mul_poch (n : ℕ) : partSeries n * poch n = 1 := by
  induction n with
  | zero => simp [partSeries_zero, poch]
  | succ n ih =>
      rw [poch, Finset.prod_range_succ, ← poch, mul_comm (poch n), ← mul_assoc,
        partSeries_succ_mul, ih]

/-! ## `∏ (1+q^r)^8` -/

/-- `∏_{r=1}^{R} (1+q^r)^8`. -/
noncomputable def fermionProd (R : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range R, (1 + q ^ (r + 1)) ^ 8

theorem coeff_fermionProd : ∀ R N, coeff N (fermionProd R) = (fermionCoeff R N : ℤ)
  | 0, N => by simp [fermionProd, fermionCoeff, coeff_one]
  | R + 1, N => by
      rw [fermionProd, Finset.prod_range_succ, ← fermionProd, add_comm (1 : PowerSeries ℤ),
        add_pow, Finset.mul_sum, map_sum]
      simp only [one_pow, mul_one, fermionCoeff]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      have hrw : fermionProd R * ((q ^ (R + 1)) ^ j * ((Nat.choose 8 j : ℕ) : PowerSeries ℤ)) =
          q ^ (j * (R + 1)) * (PowerSeries.C ((Nat.choose 8 j : ℕ) : ℤ) * fermionProd R) := by
        rw [map_natCast]; ring
      rw [hrw, coeff_X_pow_mul']
      split_ifs
      · rw [coeff_C_mul, coeff_fermionProd R]
      · rfl

/-! ## `Hilb D(1,nθ)` as a polynomial -/

theorem sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (a b : ℕ) (h : a ≤ b) (g : ℕ → M) :
    ∑ ν ∈ Finset.Icc a b, g ν = ∑ r ∈ Finset.range (b - a + 1), g (b - r) := by
  refine Finset.sum_bij' (fun ν _ => b - ν) (fun r _ => b - r) ?_ ?_ ?_ ?_ ?_
  · intro ν hν; rw [Finset.mem_Icc] at hν; rw [Finset.mem_range]; dsimp only; omega
  · intro r hr; rw [Finset.mem_range] at hr; rw [Finset.mem_Icc]; dsimp only; omega
  · intro ν hν; rw [Finset.mem_Icc] at hν; dsimp only; omega
  · intro r hr; rw [Finset.mem_range] at hr; dsimp only; omega
  · intro ν hν; rw [Finset.mem_Icc] at hν; dsimp only; congr 1; omega

/-- `G_M = ∑_r [M,r]_q`, the Rogers–Szegő polynomial at `1` (`= Hilb` of the `GL₂` branching). -/
noncomputable def rogersSzego (M : ℕ) : PowerSeries ℤ :=
  ∑ r ∈ Finset.range (M + 1), qbinom q M r

theorem coeff_rogersSzego (m₁ m₂ : ℕ) (h : m₂ ≤ m₁) (N : ℕ) :
    coeff N (rogersSzego (m₁ - m₂)) = (gl2Hilb m₁ m₂ N : ℤ) := by
  rw [gl2Hilb, sum_Icc_eq_sum_range _ _ h, rogersSzego, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [coeff_qbinom]
  congr 2
  simp only [Finset.mem_range] at hr
  omega

/-- **`Hilb_q D(1,nθ) = ∑_{i,j ≤ n} [n,i][n,j] G_{n-i+j}`** (Gelfand–Tsetlin, reindexed). -/
noncomputable def demazurePoly (n : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    qbinom q n i * qbinom q n j * rogersSzego (n - i + j)

theorem coeff_demazurePoly (n N : ℕ) : coeff N (demazurePoly n) = (demazureHilb n N : ℤ) := by
  rw [demazureHilb, gl3Hilb, sum_Icc_eq_sum_range _ _ (by omega), demazurePoly, map_sum]
  push_cast
  refine Finset.sum_congr (by congr 1; omega) fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [sum_Icc_eq_sum_range _ _ (Nat.zero_le n), map_sum]
  refine Finset.sum_congr (by congr 1) fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have h1 : 2 * n - (2 * n - i) = i := by omega
  have h2 : n - (n - j) = j := by omega
  have h3 : n - i + j = (2 * n - i) - (n - j) := by omega
  rw [show 2 * n - n = n by omega, h1, h2, h3]
  refine coeff_mul_eq_conv _ _ _ _ (fun M => coeff_mul_eq_conv _ _ _ _ (coeff_qbinom n i)
    (coeff_qbinom n j) M) (coeff_rogersSzego _ _ (by omega)) N

/-! ## The star identity as a power-series statement -/

/-- The truncated left side `∑_{n ≤ N} q^n Hilb_q D(1,nθ) / (q;q)_n`. -/
noncomputable def starLHS (N : ℕ) : PowerSeries ℤ :=
  ∑ n ∈ Finset.range (N + 1), q ^ n * (demazurePoly n * partSeries n)

theorem coeff_starLHS (N : ℕ) : coeff N (starLHS N) = (demazureCoeff N : ℤ) := by
  rw [starLHS, map_sum, demazureCoeff]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [coeff_X_pow_mul', if_pos (by simp only [Finset.mem_range] at hn; omega)]
  exact coeff_mul_eq_conv _ _ _ _ (coeff_demazurePoly n)
    (fun M => by simp [partSeries]) _

theorem coeff_fermionProd_self (N : ℕ) : coeff N (fermionProd N) = (productCoeff N : ℤ) :=
  coeff_fermionProd N N

/-- **The residual, as a statement about formal power series over `ℤ`**:
`[q^N] ∑_{n ≤ N} q^n D_n(q)/(q;q)_n = [q^N] ∏_{r=1}^{N}(1+q^r)^8`, where
`D_n = ∑_{i,j ≤ n} [n,i][n,j] G_{n-i+j}` (`demazurePoly`) and `1/(q;q)_n = partSeries n`
(`partSeries_mul_poch`). -/
structure StarSeriesIdentity : Prop where
  eq : ∀ N, coeff N (starLHS N) = coeff N (fermionProd N)

theorem starIdentity_iff_series : StarIdentity ↔ StarSeriesIdentity := by
  constructor
  · intro h
    exact ⟨fun N => by rw [coeff_starLHS, coeff_fermionProd_self, h.eq N]⟩
  · intro h
    refine ⟨fun N => ?_⟩
    have := h.eq N
    rw [coeff_starLHS, coeff_fermionProd_self] at this
    exact_mod_cast this

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.coeff_qbinom
#print axioms VOA.DeligneAudit.A2.partSeries_mul_poch
#print axioms VOA.DeligneAudit.A2.coeff_fermionProd
#print axioms VOA.DeligneAudit.A2.coeff_demazurePoly
#print axioms VOA.DeligneAudit.A2.coeff_starLHS
#print axioms VOA.DeligneAudit.A2.starIdentity_iff_series
end AxiomAudit
