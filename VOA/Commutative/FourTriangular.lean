/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTripleGauss
import VOA.Commutative.QJacobiCube
import VOA.Commutative.QSeriesSum

/-!
# Legendre's four-triangular-numbers theorem

  `∑_{v ≥ 0} (2v+1) q^v / (1 - q^{2v+1}) = (q;q)_∞⁴ (-q;q)_∞⁸`   (`lambertS_eq`)

as formal power series over `ℤ`.  Equivalently `ψ(q)⁴ = ∑_n σ(2n+1) q^n` with
`ψ(q) = ∑_{n ≥ 0} q^{n(n+1)/2} = (q;q)_∞ (-q;q)_∞²`.

## Proof

Work in `ℤ⟦x⟧`, `q = x²`, with `φ(x) = ∑_{n ∈ ℤ} x^{n²}` and `θ = x d/dx`.  Put
`Q± = (∓x;x²)_∞`, `E₂ = (x²;x²)_∞`, `S = ∑_v (2v+1) q^v/(1-q^{2v+1})`.

1. Gauss (`JacobiTripleGauss`): `φ(x) = E₂ Q₊²`, `φ(-x) = E₂ Q₋²`.
2. Logarithmic derivative (`eulerOp_oddPlus_wronskian`): `θQ₊·Q₋ - Q₊·θQ₋ = 2x S(x²) Q₊Q₋`,
   because `θ log((1+u)/(1-u)) = 2θu/(1-u²)` for `u = x^{2k+1}`.
3. Hence the theta Wronskian `W = θφ(x)·φ(-x) - φ(x)·θφ(-x) = 4x S(x²) E₂² Q₊² Q₋²`.
4. Reindexing (`wronskian_eq`): `W = x Z²` with `Z = ∑_{a ∈ ℤ} (-1)^a (2a+1) x^{2a(a+1)}`.
   Same-parity pairs `(m,n)` cancel under `(m,n) ↦ (n,m)`; opposite-parity pairs are
   `(m,n) = (a+b+1, a-b)`, and `m² - n² = (2a+1)(2b+1)`, `m² + n² = 2a(a+1) + 2b(b+1) + 1`.
5. `Z = 2 (x⁴;x⁴)_∞³` by Jacobi's cube identity (`VOA.QSeries.jacobi_cube`, ported to `ℤ`).
6. Cancel `4x`, undo `q = x²` (`expand 2` is injective), and use Euler's
   `(q;q²)_∞ (-q;q)_∞ = 1`.
-/

namespace VOA.QSeries.JTP

open PowerSeries VOA.QSeries

open scoped BigOperators

noncomputable section

/-! ## The Lambert series -/

section Lambert

variable {R : Type*} [CommRing R]

/-- `1/(1 - q^m) = ∑_{m ∣ N} q^N`. -/
def geomInvSeries (m : ℕ) : PowerSeries R := mk fun N => if m ∣ N then 1 else 0

theorem one_sub_X_pow_mul_geomInvSeries (m : ℕ) (hm : 0 < m) :
    (1 - X ^ m) * (geomInvSeries m : PowerSeries R) = 1 := by
  have key : ∀ N, m ≤ N → (m ∣ N - m ↔ m ∣ N) := fun N h => by
    constructor
    · intro hd
      have := Nat.dvd_add hd (dvd_refl m)
      rwa [Nat.sub_add_cancel h] at this
    · intro hd
      exact Nat.dvd_sub hd (dvd_refl m)
  ext N
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', geomInvSeries, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [show ¬ m ≤ 0 by omega]
  · by_cases h : m ≤ N
    · rw [if_pos h, coeff_mk, if_neg hN.ne']
      by_cases hd : m ∣ N
      · rw [if_pos hd, if_pos ((key N h).mpr hd), sub_self]
      · rw [if_neg hd, if_neg (fun h' => hd ((key N h).mp h')), sub_self]
    · have : ¬ m ∣ N := fun hd => h (Nat.le_of_dvd hN hd)
      simp [h, this, hN.ne']

/-- The Lambert series `S(q) = ∑_{v ≥ 0} (2v+1) q^v / (1 - q^{2v+1})`. -/
def lambertS : PowerSeries R :=
  powerShiftSum 1 fun v => ((2 * v + 1 : ℕ) : PowerSeries R) * geomInvSeries (2 * v + 1)

/-- The `v`-th summand of `S(x²)`. -/
def lambertTerm (v : ℕ) : PowerSeries R :=
  X ^ (2 * v) *
    (((2 * v + 1 : ℕ) : PowerSeries R) * expand 2 two_ne_zero (geomInvSeries (2 * v + 1)))

theorem one_sub_X_pow_mul_expand_geomInvSeries (v : ℕ) :
    (1 - X ^ (4 * v + 2)) *
      expand 2 two_ne_zero (geomInvSeries (2 * v + 1) : PowerSeries R) = 1 := by
  have h := congrArg (expand 2 two_ne_zero)
    (one_sub_X_pow_mul_geomInvSeries (R := R) (2 * v + 1) (by omega))
  rw [map_mul, map_sub, map_one, map_pow, expand_X, ← pow_mul] at h
  rw [show 4 * v + 2 = 2 * (2 * v + 1) by ring]
  exact h

/-- `S(x²)` agrees with its partial sums. -/
theorem agreeTo_expand_lambertS (N : ℕ) :
    AgreeTo (N + 1) (expand 2 two_ne_zero (lambertS : PowerSeries R))
      (∑ v ∈ Finset.range (N + 1), lambertTerm v) := by
  have h : AgreeTo (N + 1) (lambertS : PowerSeries R)
      (∑ v ∈ Finset.range (N + 1), X ^ (1 * v) *
        (((2 * v + 1 : ℕ) : PowerSeries R) * geomInvSeries (2 * v + 1))) :=
    AgreeTo.of_coeff fun d hd => coeff_powerShiftSum 1 one_pos _ d N (by omega)
  have h2 := (h.expand 2 two_ne_zero).mono (show N + 1 ≤ 2 * (N + 1) by omega)
  refine h2.trans (AgreeTo.of_eq ?_)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [lambertTerm, map_mul, map_mul, map_pow, expand_X, map_natCast, one_mul, ← pow_mul]

/-- Finite logarithmic-derivative identity for `∏ (1 ± x^{2k+1})`. -/
theorem eulerOp_wronskian_finite (N : ℕ) :
    eulerOp (∏ k ∈ Finset.range N, (1 + X ^ (2 * k + 1) : PowerSeries R)) *
        (∏ k ∈ Finset.range N, (1 - X ^ (2 * k + 1))) -
      (∏ k ∈ Finset.range N, (1 + X ^ (2 * k + 1))) *
        eulerOp (∏ k ∈ Finset.range N, (1 - X ^ (2 * k + 1) : PowerSeries R)) =
      2 * X * (∑ v ∈ Finset.range N, lambertTerm v) *
        (∏ k ∈ Finset.range N, (1 + X ^ (2 * k + 1))) *
        (∏ k ∈ Finset.range N, (1 - X ^ (2 * k + 1))) := by
  induction N with
  | zero => simp [eulerOp_one]
  | succ N ih =>
      simp only [Finset.prod_range_succ, Finset.sum_range_succ]
      set A := ∏ k ∈ Finset.range N, (1 + X ^ (2 * k + 1) : PowerSeries R)
      set B := ∏ k ∈ Finset.range N, (1 - X ^ (2 * k + 1) : PowerSeries R)
      set T := ∑ v ∈ Finset.range N, (lambertTerm v : PowerSeries R)
      have ha : eulerOp (1 + X ^ (2 * N + 1) : PowerSeries R) =
          ((2 * N + 1 : ℕ) : PowerSeries R) * X ^ (2 * N + 1) := by
        rw [eulerOp_add, eulerOp_one, eulerOp_X_pow, zero_add]
      have hb : eulerOp (1 - X ^ (2 * N + 1) : PowerSeries R) =
          -(((2 * N + 1 : ℕ) : PowerSeries R) * X ^ (2 * N + 1)) := by
        rw [eulerOp_sub, eulerOp_one, eulerOp_X_pow, zero_sub]
      have hg := one_sub_X_pow_mul_expand_geomInvSeries (R := R) N
      rw [eulerOp_mul, eulerOp_mul, ha, hb, lambertTerm]
      set g := expand 2 two_ne_zero (geomInvSeries (2 * N + 1) : PowerSeries R)
      set c := ((2 * N + 1 : ℕ) : PowerSeries R)
      linear_combination ((1 + X ^ (2 * N + 1)) * (1 - X ^ (2 * N + 1))) * ih -
        (2 * c * X ^ (2 * N + 1) * A * B) * hg

/-- **The logarithmic derivative of `(-x;x²)_∞/(x;x²)_∞`**:
`θQ₊·Q₋ - Q₊·θQ₋ = 2x S(x²) Q₊ Q₋`. -/
theorem eulerOp_oddPlus_wronskian :
    eulerOp (oddPlus : PowerSeries R) * oddMinus - oddPlus * eulerOp oddMinus =
      2 * X * expand 2 two_ne_zero lambertS * oddPlus * oddMinus := by
  apply eq_of_agreeTo
  intro N
  have hP := (agreeTo_infProd (prodFactors_oddPlus (R := R)) (N + 1)).mono
    (show N + 1 ≤ N + 1 + 1 by omega)
  have hM := (agreeTo_infProd (prodFactors_oddMinus (R := R)) (N + 1)).mono
    (show N + 1 ≤ N + 1 + 1 by omega)
  rw [← oddPlus] at hP
  rw [← oddMinus] at hM
  have hS := agreeTo_expand_lambertS (R := R) N
  have h := ((hP.eulerOp.mul hM).sub (hP.mul hM.eulerOp)).trans
    (AgreeTo.of_eq (eulerOp_wronskian_finite (R := R) (N + 1)))
  exact h.trans ((((AgreeTo.refl _ (2 * X)).mul hS).mul hP).mul hM).symm

end Lambert

/-! ## Signs and exponents on `ℤ` -/

section Signs

variable {R : Type*} [CommRing R]

/-- `(-1)^n` for `n ∈ ℤ`. -/
def negSign (n : ℤ) : R := (-1) ^ n.natAbs

theorem negSign_eq (n : ℤ) : (negSign n : R) = if n % 2 = 0 then 1 else -1 := by
  unfold negSign
  rcases Nat.even_or_odd n.natAbs with h | h
  · rw [h.neg_one_pow, if_pos]
    have := Int.natAbs_even.mp h
    exact Int.even_iff.mp this
  · rw [h.neg_one_pow, if_neg]
    have := Int.natAbs_odd.mp h
    have := Int.odd_iff.mp this
    omega

theorem negSign_add (m n : ℤ) : (negSign (m + n) : R) = negSign m * negSign n := by
  simp only [negSign_eq]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem negSign_sub (m n : ℤ) : (negSign (m - n) : R) = negSign m * negSign n := by
  simp only [negSign_eq]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem negSign_neg_sub_one (a : ℤ) : (negSign (-a - 1) : R) = - negSign a := by
  simp only [negSign_eq]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem negSign_of_even_sub {m n : ℤ} (h : (m - n) % 2 = 0) : (negSign m : R) = negSign n := by
  simp only [negSign_eq]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem neg_one_pow_natAbs_sq (n : ℤ) : (-1 : R) ^ (n.natAbs ^ 2) = negSign n := by
  unfold negSign
  rcases Nat.even_or_odd n.natAbs with h | h
  · rw [h.neg_one_pow, (Nat.even_pow.mpr ⟨h, two_ne_zero⟩).neg_one_pow]
  · rw [h.neg_one_pow, (Odd.pow h).neg_one_pow]

/-- The square exponent `n ↦ n²`. -/
def sqExp (n : ℤ) : ℕ := n.natAbs ^ 2

/-- The exponent `a ↦ 2a(a+1)`. -/
def triExp (a : ℤ) : ℕ := 2 * (a * (a + 1)).toNat

theorem cast_sqExp (n : ℤ) : ((sqExp n : ℕ) : ℤ) = n ^ 2 := by
  rw [sqExp]; push_cast; exact sq_abs n

theorem cast_triExp (a : ℤ) : ((triExp a : ℕ) : ℤ) = 2 * (a * (a + 1)) := by
  rw [triExp]
  push_cast
  rw [Int.toNat_of_nonneg]
  rcases le_or_gt 0 a with h | h <;> nlinarith

theorem natAbs_le_sqExp (n : ℤ) : n.natAbs ≤ sqExp n + 1 := by
  have := Nat.le_self_pow two_ne_zero n.natAbs
  rw [sqExp]; omega

theorem natAbs_le_triExp (a : ℤ) : a.natAbs ≤ triExp a + 1 := by
  have h := cast_triExp a
  zify
  rw [h]
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]; nlinarith
  · rw [abs_of_neg ha]; nlinarith

theorem triExp_neg_sub_one (a : ℤ) : triExp (-a - 1) = triExp a := by
  have h1 := cast_triExp (-a - 1)
  have h2 := cast_triExp a
  have : ((triExp (-a - 1) : ℕ) : ℤ) = ((triExp a : ℕ) : ℤ) := by rw [h1, h2]; ring
  exact_mod_cast this

end Signs

/-! ## The theta Wronskian as a square -/

section Reindex

variable {R : Type*} [CommRing R]

/-- `Z = ∑_{a ∈ ℤ} (-1)^a (2a+1) x^{2a(a+1)}`. -/
def zetaSeries : PowerSeries R :=
  zSeries (fun a => negSign a * ((2 * a + 1 : ℤ) : R)) triExp

theorem thetaPhi_eq_zSeries : (thetaPhi : PowerSeries R) = zSeries (fun _ => 1) sqExp := rfl

theorem rescale_thetaPhi : rescale (-1 : R) (thetaPhi : PowerSeries R) =
    zSeries (fun n => negSign n) sqExp := by
  rw [thetaPhi_eq_zSeries, rescale_zSeries]
  congr 1
  funext n
  rw [mul_one, sqExp, neg_one_pow_natAbs_sq]

/-- The combinatorial heart: pairs `(m,n)` with `m² + n² = d`, weighted by
`(-1)^n (m² - n²)`, against pairs `(a,b)` with `2a(a+1) + 2b(b+1) + 1 = d`. -/
theorem wronskian_coeff_sum (K d : ℕ) (hd : d < K) :
    (∑ p ∈ Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K with
        sqExp p.1 + sqExp p.2 = d,
        (negSign p.2 : R) * ((sqExp p.1 : R) - (sqExp p.2 : R))) =
      ∑ p ∈ Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K with
        triExp p.1 + triExp p.2 + 1 = d,
        (negSign p.1 * ((2 * p.1 + 1 : ℤ) : R)) * (negSign p.2 * ((2 * p.2 + 1 : ℤ) : R)) := by
  classical
  set I := Finset.Icc (-(K : ℤ)) K with hI
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ℤ × ℤ => (p.1 + p.2) % 2 = 1)]
  -- same-parity pairs cancel
  have hsame : (∑ p ∈ (I ×ˢ I).filter (fun p => sqExp p.1 + sqExp p.2 = d) with
      ¬ (p.1 + p.2) % 2 = 1,
      (negSign p.2 : R) * ((sqExp p.1 : R) - (sqExp p.2 : R))) = 0 := by
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rw [negSign_of_even_sub (R := R) (show (p.1 - p.2) % 2 = 0 by omega)]
      ring
    · intro p _ hne heq
      apply hne
      have : p.1 = p.2 := ((Prod.ext_iff.mp heq).1).symm
      rw [this, sub_self, mul_zero]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      refine ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by omega⟩, by omega⟩
    · intro p _
      rfl
  rw [hsame, add_zero]
  -- opposite-parity pairs are `(a+b+1, a-b)`
  apply Finset.sum_nbij' (fun p => ((p.1 + p.2 - 1) / 2, (p.1 - p.2 - 1) / 2))
    (fun p => (p.1 + p.2 + 1, p.1 - p.2))
  · intro p hp
    simp only [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨⟨_, _⟩, hpd⟩, hodd⟩ := hp
    set a := (p.1 + p.2 - 1) / 2
    set b := (p.1 - p.2 - 1) / 2
    have hm : p.1 = a + b + 1 := by omega
    have hn : p.2 = a - b := by omega
    have key : ((triExp a + triExp b + 1 : ℕ) : ℤ) = ((sqExp p.1 + sqExp p.2 : ℕ) : ℤ) := by
      push_cast [cast_triExp, cast_sqExp]
      rw [hm, hn]
      ring
    have hkey : triExp a + triExp b + 1 = d := by rw [← hpd]; exact_mod_cast key
    have ha := natAbs_le_triExp a
    have hb := natAbs_le_triExp b
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hkey⟩ <;> omega
  · intro p hp
    simp only [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨_, _⟩, hpd⟩ := hp
    have key : ((sqExp (p.1 + p.2 + 1) + sqExp (p.1 - p.2) : ℕ) : ℤ) =
        ((triExp p.1 + triExp p.2 + 1 : ℕ) : ℤ) := by
      push_cast [cast_triExp, cast_sqExp]
      ring
    have hkey : sqExp (p.1 + p.2 + 1) + sqExp (p.1 - p.2) = d := by
      rw [← hpd]; exact_mod_cast key
    have h1 := natAbs_le_sqExp (p.1 + p.2 + 1)
    have h1' := Nat.le_self_pow two_ne_zero (p.1 + p.2 + 1).natAbs
    have h2' := Nat.le_self_pow two_ne_zero (p.1 - p.2).natAbs
    simp only [sqExp] at hkey
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hkey⟩, ?_⟩ <;> omega
  · intro p hp
    simp only [Finset.mem_filter] at hp
    ext <;> simp <;> omega
  · intro p _
    ext <;> simp <;> omega
  · intro p hp
    simp only [Finset.mem_filter] at hp
    set a := (p.1 + p.2 - 1) / 2
    set b := (p.1 - p.2 - 1) / 2
    have hm : p.1 = a + b + 1 := by omega
    have hn : p.2 = a - b := by omega
    have hcast : ((sqExp p.1 : ℕ) : R) - ((sqExp p.2 : ℕ) : R) =
        (((2 * a + 1) * (2 * b + 1) : ℤ) : R) := by
      rw [← Int.cast_natCast, ← Int.cast_natCast (R := R), ← Int.cast_sub, cast_sqExp,
        cast_sqExp, hm, hn]
      congr 1
      ring
    rw [hcast, hn, negSign_sub]
    push_cast
    ring


/-- **The theta Wronskian is a square**:
`θφ(x)·φ(-x) - φ(x)·θφ(-x) = x Z²`. -/
theorem wronskian_eq :
    eulerOp (thetaPhi : PowerSeries R) * rescale (-1) thetaPhi -
        thetaPhi * eulerOp (rescale (-1) thetaPhi) =
      X * zetaSeries ^ 2 := by
  apply eq_of_agreeTo
  intro N
  set K := N + 1
  set I := Finset.Icc (-(K : ℤ)) K with hI
  have hIsq : ∀ n, sqExp n < K → n ∈ I := fun n hn => by
    have := natAbs_le_sqExp n
    have h' := Nat.le_self_pow two_ne_zero n.natAbs
    simp only [hI, Finset.mem_Icc, sqExp] at hn ⊢
    omega
  have hItri : ∀ a, triExp a < K → a ∈ I := fun a ha => by
    have := natAbs_le_triExp a
    simp only [hI, Finset.mem_Icc]
    omega
  have h1 := agreeTo_zSeries (R := R) (fun n => (sqExp n : R) * 1) sqExp natAbs_le_sqExp I hIsq
  have h2 := agreeTo_zSeries (R := R) (fun n => negSign n) sqExp natAbs_le_sqExp I hIsq
  have h3 := agreeTo_zSeries (R := R) (fun _ => 1) sqExp natAbs_le_sqExp I hIsq
  have h4 := agreeTo_zSeries (R := R) (fun n => (sqExp n : R) * negSign n) sqExp
    natAbs_le_sqExp I hIsq
  have h5 := agreeTo_zSeries (R := R) (fun a => negSign a * ((2 * a + 1 : ℤ) : R)) triExp
    natAbs_le_triExp I hItri
  rw [← eulerOp_zSeries, ← thetaPhi_eq_zSeries] at h1
  rw [← rescale_thetaPhi] at h2
  rw [← thetaPhi_eq_zSeries] at h3
  rw [← eulerOp_zSeries, ← rescale_thetaPhi] at h4
  rw [← zetaSeries] at h5
  have hL := (h1.mul h2).sub (h3.mul h4)
  have hR := (h5.mul h5).mul_left X
  rw [sum_monomial_mul_sum_monomial, sum_monomial_mul_sum_monomial] at hL
  rw [sum_monomial_mul_sum_monomial, Finset.mul_sum] at hR
  rw [pow_two]
  refine hL.trans (AgreeTo.trans (AgreeTo.of_coeff fun d hd => ?_) hR.symm)
  rw [map_sub, coeff_sum_monomial, coeff_sum_monomial, ← Finset.sum_sub_distrib]
  have hX : ∀ p : ℤ × ℤ, (X : PowerSeries R) *
      (C (negSign p.1 * ((2 * p.1 + 1 : ℤ) : R) * (negSign p.2 * ((2 * p.2 + 1 : ℤ) : R))) *
        X ^ (triExp p.1 + triExp p.2)) =
      C (negSign p.1 * ((2 * p.1 + 1 : ℤ) : R) * (negSign p.2 * ((2 * p.2 + 1 : ℤ) : R))) *
        X ^ (triExp p.1 + triExp p.2 + 1) := fun p => by ring
  simp only [hX]
  rw [coeff_sum_monomial]
  rw [← wronskian_coeff_sum (R := R) K d hd]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- `Z = 2 (x⁴;x⁴)`-side: `Z = 2 · expand 4 (∑_r (-1)^r (2r+1) q^{r(r+1)/2})`. -/
theorem zetaSeries_eq :
    (zetaSeries : PowerSeries R) = 2 * expand 4 (by norm_num) alternatingTheta := by
  apply eq_of_agreeTo
  intro N
  set K := N + 1
  set J := Finset.Icc (-(K : ℤ) - 1) K with hJ
  have hJtri : ∀ a, triExp a < K → a ∈ J := fun a ha => by
    have := natAbs_le_triExp a
    simp only [hJ, Finset.mem_Icc]
    omega
  have h5 := agreeTo_zSeries (R := R) (fun a => negSign a * ((2 * a + 1 : ℤ) : R)) triExp
    natAbs_le_triExp J hJtri
  rw [← zetaSeries] at h5
  refine h5.trans ?_
  -- fold the negative half onto the nonnegative half
  have hsplit : (∑ a ∈ J, C (negSign a * ((2 * a + 1 : ℤ) : R)) * X ^ triExp a) =
      2 * ∑ r ∈ Finset.range (K + 1),
        C (negSign (r : ℤ) * ((2 * (r : ℤ) + 1 : ℤ) : R)) * X ^ triExp r := by
    rw [← Finset.sum_filter_add_sum_filter_not J (fun a : ℤ => 0 ≤ a)]
    have hpos : (∑ a ∈ J with 0 ≤ a, C (negSign a * ((2 * a + 1 : ℤ) : R)) * X ^ triExp a) =
        ∑ r ∈ Finset.range (K + 1),
          C (negSign (r : ℤ) * ((2 * (r : ℤ) + 1 : ℤ) : R)) * X ^ triExp r := by
      apply Finset.sum_nbij' (fun (a : ℤ) => a.toNat) (fun (r : ℕ) => (r : ℤ))
      · intro a ha
        simp only [hJ, Finset.mem_filter, Finset.mem_Icc] at ha
        simp only [Finset.mem_range]
        omega
      · intro r hr
        simp only [Finset.mem_range] at hr
        simp only [hJ, Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro a ha
        simp only [hJ, Finset.mem_filter, Finset.mem_Icc] at ha
        omega
      · intro r _
        simp
      · intro a ha
        simp only [hJ, Finset.mem_filter, Finset.mem_Icc] at ha
        rw [Int.toNat_of_nonneg ha.2]
    have hneg : (∑ a ∈ J with ¬ 0 ≤ a, C (negSign a * ((2 * a + 1 : ℤ) : R)) * X ^ triExp a) =
        ∑ a ∈ J with 0 ≤ a, C (negSign a * ((2 * a + 1 : ℤ) : R)) * X ^ triExp a := by
      apply Finset.sum_nbij' (fun (a : ℤ) => -a - 1) (fun (a : ℤ) => -a - 1)
      · intro a ha
        simp only [hJ, Finset.mem_filter, Finset.mem_Icc] at ha ⊢
        omega
      · intro a ha
        simp only [hJ, Finset.mem_filter, Finset.mem_Icc] at ha ⊢
        omega
      · intro a _
        ring
      · intro a _
        ring
      · intro a _
        rw [triExp_neg_sub_one, negSign_neg_sub_one]
        congr 2
        push_cast
        ring
    rw [hneg, hpos]
    ring
  rw [hsplit]
  have hcut : AgreeTo (K + 1) (alternatingTheta : PowerSeries R)
      (∑ r ∈ Finset.range (K + 1), alternatingTerm r) :=
    AgreeTo.of_coeff fun d hd => coeff_alternatingTheta d K (by omega)
  have hexp := ((hcut.expand 4 (by norm_num)).mono (show K ≤ 4 * (K + 1) by omega)).mul_left 2
  refine (AgreeTo.of_eq ?_).trans hexp.symm
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hexp' : triExp (r : ℤ) = 4 * (r + 1).choose 2 := by
    have h1 := cast_triExp (r : ℤ)
    have h2 := two_mul_choose_two_add (r + 1)
    have : ((triExp (r : ℤ) : ℕ) : ℤ) = ((4 * (r + 1).choose 2 : ℕ) : ℤ) := by
      rw [h1]; push_cast
      have h2' : (2 * ((r + 1).choose 2 : ℤ)) + (r + 1) = (r + 1) * (r + 1) := by
        exact_mod_cast h2
      linear_combination (-2 : ℤ) * h2'
    exact_mod_cast this
  have hl : C (negSign (r : ℤ) * ((2 * (r : ℤ) + 1 : ℤ) : R)) * X ^ triExp (r : ℤ) =
      (-1) ^ r * ((2 * r + 1 : ℕ) : PowerSeries R) * X ^ (4 * (r + 1).choose 2) := by
    rw [hexp', negSign, Int.natAbs_natCast, map_mul, map_pow, map_neg, map_one, map_intCast]
    push_cast
    ring
  have hr : expand 4 (by norm_num) (alternatingTerm r : PowerSeries R) =
      (-1) ^ r * ((2 * r + 1 : ℕ) : PowerSeries R) * X ^ (4 * (r + 1).choose 2) := by
    rw [alternatingTerm, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, map_pow,
      expand_X, ← pow_mul]
  rw [hl, hr]

end Reindex

/-! ## Assembly over `ℤ` -/

section Assembly

/-- Jacobi's cube identity over `ℤ`, transported from `ℚ`. -/
theorem jacobi_cube_int : (alternatingTheta : PowerSeries ℤ) = euler ^ 3 := by
  have hinj := PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply hinj
  have hθ : PowerSeries.map (Int.castRingHom ℚ) (alternatingTheta : PowerSeries ℤ) =
      alternatingTheta := by
    ext d
    rw [coeff_map, coeff_alternatingTheta d d le_rfl, coeff_alternatingTheta d d le_rfl,
      ← coeff_map, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [alternatingTerm, alternatingTerm, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
      map_pow, map_X]
  have he : PowerSeries.map (Int.castRingHom ℚ) (euler : PowerSeries ℤ) = euler := by
    ext d
    rw [coeff_map, coeff_euler d d le_rfl, coeff_euler d d le_rfl, ← coeff_map, map_qFactorial,
      map_X]
  rw [hθ, map_pow, he]
  exact jacobi_cube

theorem expand_injective (p : ℕ) (hp : p ≠ 0) {R : Type*} [CommRing R] {f g : PowerSeries R}
    (h : expand p hp f = expand p hp g) : f = g := by
  ext m
  have := congrArg (coeff (p * m)) h
  simpa only [coeff_expand_mul] using this

/-- `(-q;q)_∞ = ∏_{k ≥ 0} (1 + q^{k+1})`. -/
def fermionEuler : PowerSeries ℤ := infProd fun k => 1 + X ^ (k + 1)

theorem prodFactors_fermion : ProdFactors fun k => (1 : PowerSeries ℤ) + X ^ (k + 1) :=
  prodFactors_one_add_X_pow _ fun k => by omega

/-- `(q;q)_∞ = (q;q²)_∞ (q²;q²)_∞`. -/
theorem euler_eq_oddMinus_mul_evenEuler :
    (euler : PowerSeries ℤ) = oddMinus * evenEuler := by
  rw [euler_eq_infProd, oddMinus, evenEuler, infProd_mul prodFactors_oddMinus prodFactors_evenEuler,
    ← infProd_pairs prodFactors_euler]

/-- `(q;q)_∞ (-q;q)_∞ = (q²;q²)_∞`. -/
theorem euler_mul_fermionEuler : (euler : PowerSeries ℤ) * fermionEuler = evenEuler := by
  rw [euler_eq_infProd, fermionEuler, evenEuler, infProd_mul prodFactors_euler prodFactors_fermion]
  apply infProd_congr
  intro k
  ring

/-- Euler: `(q;q²)_∞ (-q;q)_∞ = 1`. -/
theorem oddMinus_mul_fermionEuler : (oddMinus : PowerSeries ℤ) * fermionEuler = 1 := by
  have h := euler_mul_fermionEuler
  rw [euler_eq_oddMinus_mul_evenEuler] at h
  have hu : (evenEuler : PowerSeries ℤ) ≠ 0 := (isUnit_infProd _).ne_zero
  apply mul_left_cancel₀ hu
  linear_combination h

theorem oddPlus_mul_oddMinus :
    (oddPlus : PowerSeries ℤ) * oddMinus = expand 2 two_ne_zero oddMinus := by
  rw [oddPlus, oddMinus, infProd_mul prodFactors_oddPlus prodFactors_oddMinus,
    expand_infProd 2 two_ne_zero prodFactors_oddMinus]
  apply infProd_congr
  intro k
  rw [map_sub, map_one, map_pow, expand_X, ← pow_mul]
  ring

/-- **Legendre's four-triangular-numbers theorem** (with Gauss's product for `ψ`):
`∑_{v ≥ 0} (2v+1) q^v/(1 - q^{2v+1}) = (q;q)_∞⁴ ∏_{k ≥ 1} (1 + q^k)⁸`. -/
theorem lambertS_eq :
    (lambertS : PowerSeries ℤ) = euler ^ 4 * infProd fun k => (1 + X ^ (k + 1)) ^ 8 := by
  set Sx := expand 2 two_ne_zero (lambertS : PowerSeries ℤ)
  -- the Wronskian two ways
  have hW1 : eulerOp (thetaPhi : PowerSeries ℤ) * rescale (-1) thetaPhi -
      thetaPhi * eulerOp (rescale (-1) thetaPhi) =
      4 * X * (Sx * evenEuler ^ 2 * (oddPlus * oddMinus) ^ 2) := by
    rw [rescale_thetaPhi_eq, thetaPhi_eq, eulerOp_mul, eulerOp_mul, eulerOp_sq, eulerOp_sq]
    linear_combination (2 * evenEuler ^ 2 * oddPlus * oddMinus) *
      (eulerOp_oddPlus_wronskian (R := ℤ))
  have hW2 : eulerOp (thetaPhi : PowerSeries ℤ) * rescale (-1) thetaPhi -
      thetaPhi * eulerOp (rescale (-1) thetaPhi) =
      4 * X * (expand 4 (by norm_num) euler) ^ 6 := by
    rw [wronskian_eq, zetaSeries_eq, jacobi_cube_int, map_pow]
    ring
  have h4 : (4 : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have hne : (4 * X : PowerSeries ℤ) ≠ 0 := mul_ne_zero h4 X_ne_zero
  have hx := mul_left_cancel₀ hne (hW1.symm.trans hW2)
  -- undo `q = x²`
  have h44 : expand 4 (by norm_num) (euler : PowerSeries ℤ) =
      expand 2 two_ne_zero (expand 2 two_ne_zero euler) :=
    expand_mul 2 two_ne_zero 2 two_ne_zero euler
  rw [oddPlus_mul_oddMinus, h44, expand_two_euler] at hx
  have hy : (lambertS : PowerSeries ℤ) * euler ^ 2 * oddMinus ^ 2 = evenEuler ^ 6 := by
    apply expand_injective 2 two_ne_zero
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, expand_two_euler]
    rw [← hx]
  rw [euler_eq_oddMinus_mul_evenEuler] at hy
  have hu : (evenEuler : PowerSeries ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (isUnit_infProd _).ne_zero
  have hy' : (lambertS : PowerSeries ℤ) * oddMinus ^ 4 = evenEuler ^ 4 := by
    apply mul_left_cancel₀ hu
    linear_combination hy
  rw [← infProd_pow prodFactors_fermion, ← fermionEuler]
  calc (lambertS : PowerSeries ℤ)
      = lambertS * (oddMinus * fermionEuler) ^ 4 := by rw [oddMinus_mul_fermionEuler]; ring
    _ = (euler * fermionEuler) ^ 4 * fermionEuler ^ 4 := by
        rw [euler_mul_fermionEuler]; linear_combination fermionEuler ^ 4 * hy'
    _ = euler ^ 4 * fermionEuler ^ 8 := by ring

end Assembly

end

end VOA.QSeries.JTP
