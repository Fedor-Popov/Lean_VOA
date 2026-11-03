import VOA.Huang.GenusOneWardSeries

/-!
# The genus-one two-point kernels in `ℂ⟦u⟧⟦t⟧`

`piK m` is the spatial kernel `Σ_{d≥1} (d^m t^d − (−d)^m u^d) / (m! (1 − q^d))`,
`xiK m` the Lambert part `Σ_{d≥1} (d^m − (−d)^m) q^d / (m! (1 − q^d))`, and
`eis j` the Eisenstein series `G_{2j}` of `zhuG`, all as elements of
`ℂ⟦u⟧⟦t⟧` with `q = u t`. The binomial and Zhu coefficient identities convert
the geometric sums produced by trace cyclicity into these kernels.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open PowerSeries
open scoped BigOperators

/-- `Σ_{j<K} C(p,j) F_j`, the commutator combination. -/
def binSum (K : ℕ) (F : ℤ → R2) (p : ℤ) : R2 :=
  ∑ j ∈ Finset.range K, cbz p (j : ℤ) • F j

/-- The spatial kernel; `piK 0 + 1/2` is `P₁(z₁ − z₂)` and `(-1)^m piK (m+1)` is `P_{m+2}(z₂ − z₁)`. -/
def piK (m : ℕ) : R2 :=
  lsum fun i => ((((i + 1 : ℕ) : ℂ) ^ m / (m.factorial : ℂ)) • (tt ^ (i + 1) * geo (i + 1)) -
    ((-((i + 1 : ℕ) : ℂ)) ^ m / (m.factorial : ℂ)) • (uu ^ (i + 1) * geo (i + 1)))

/-- The Lambert kernel. -/
def xiK (m : ℕ) : R2 :=
  lsum fun i => ((((i + 1 : ℕ) : ℂ) ^ m - (-((i + 1 : ℕ) : ℂ)) ^ m) / (m.factorial : ℂ)) •
    (qq ^ (i + 1) * geo (i + 1))

/-- The Eisenstein series `G_{2j}` (Zhu normalization) in the variable `q = u t`. -/
def eis (j : ℕ) : R2 := mk2 fun n k => if n = k then zhuG j n else 0

theorem locFin_tt_geo (a : ℕ → ℂ) : LocFin fun i => a i • (tt ^ (i + 1) * geo (i + 1)) := by
  have h := locFin_tt_pow (fun i => geo (i + 1)) (fun i => i + 1) (fun i => Nat.le_succ i)
  exact h.smul a

theorem locFin_uu_geo (a : ℕ → ℂ) : LocFin fun i => a i • (uu ^ (i + 1) * geo (i + 1)) := by
  have h := locFin_uu_pow (fun i => geo (i + 1)) (fun i => i + 1) (fun i => Nat.le_succ i)
  exact h.smul a

theorem locFin_qq_geo (a : ℕ → ℂ) : LocFin fun i => a i • (qq ^ (i + 1) * geo (i + 1)) := by
  have h := locFin_uu_pow (fun i => tt ^ (i + 1) * geo (i + 1)) (fun i => i + 1)
    (fun i => Nat.le_succ i)
  have h' := h.smul a
  simpa only [qq_pow, mul_assoc] using h'

theorem c2_qq_pow_geo (d n k : ℕ) (hd : 1 ≤ d) :
    c2 (qq ^ d * geo d) n k = if n = k ∧ d ∣ n ∧ d ≤ n then 1 else 0 := by
  rw [c2_qq_pow_mul]
  by_cases h : d ≤ n ∧ d ≤ k
  · rw [if_pos h, c2_geo]
    have h1 : (n - d = k - d) ↔ n = k := by omega
    have h2 : d ∣ n - d ↔ d ∣ n := Nat.dvd_sub_iff_left h.1 (dvd_refl d)
    simp only [h1, h2, h.1, and_true]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.2, by omega⟩)]

/-- The divisor sum over `d ≤ n` written over `d' < n`. -/
theorem sum_range_dvd_eq_divisors (N : ℕ) (f : ℕ → ℂ) :
    ∑ i ∈ Finset.range N, (if i + 1 ∣ N then f (i + 1) else 0) =
      ∑ d ∈ N.divisors, f d := by
  rw [Nat.divisors, Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm 1]

/-- `G_{2(m+1)} = G_{2(m+1)}(0) + xiK(2m+1)`. -/
theorem eis_eq_const_add_xiK (m : ℕ) :
    eis (m + 1) = algebraMap ℂ R2 (zhuG (m + 1) 0) + xiK (2 * m + 1) := by
  apply ext2
  intro n k
  rw [c2_add, c2_algebraMap, eis, c2_mk2, xiK,
    c2_lsum_eq_sum (B := n) (fun i hi => by
      rw [c2_smul, c2_qq_pow_geo _ _ _ (by omega), if_neg (by omega), mul_zero])]
  by_cases hnk : n = k
  · subst hnk
    rw [if_pos rfl]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · rw [if_neg (by omega), zero_add, zhuG_of_ne_zero _ hpos.ne', lambertCoeff,
        Nat.sum_divisorsAntidiagonal (fun d _ => (d : ℂ) ^ (2 * (m + 1) - 1)),
        show 2 * (m + 1) - 1 = 2 * m + 1 by omega, ← sum_range_dvd_eq_divisors, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [c2_smul, c2_qq_pow_geo _ _ _ (by omega)]
      by_cases hd : i + 1 ∣ n
      · rw [if_pos (show n = n ∧ i + 1 ∣ n ∧ i + 1 ≤ n from ⟨rfl, hd, Nat.le_of_dvd hpos hd⟩),
          Odd.neg_pow ⟨m, rfl⟩]
        simp only [hd, if_true]
        ring
      · rw [if_neg (show ¬(n = n ∧ i + 1 ∣ n ∧ i + 1 ≤ n) from fun h => hd h.2.1)]
        simp only [hd, if_false]
        ring
  · rw [if_neg hnk, if_neg (fun h => hnk (h.1.trans h.2.symm)), zero_add]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [c2_smul, c2_qq_pow_geo _ _ _ (by omega), if_neg (fun h => hnk h.1), mul_zero]

theorem xiK_even (m : ℕ) : xiK (2 * m) = 0 := by
  apply ext2
  intro n k
  rw [xiK, c2_lsum_eq_sum (B := 0) (fun i _ => by
    rw [c2_smul, Even.neg_pow ⟨m, by ring⟩, sub_self, zero_div, zero_mul])]
  simp

/-- (I1) at a positive and a negative integer, rewritten with `sqBracketCoeff`. -/
theorem cbz_eq_sum_sq {kc : ℕ} (hk : 1 ≤ kc) (d : ℤ) {j K : ℕ} (hj : j < K) :
    cbz ((kc : ℤ) - 1 + d) (j : ℤ) =
      ∑ m ∈ Finset.range K, ((d : ℂ) ^ m / (m.factorial : ℂ)) * sqBracketCoeff kc m j := by
  rw [← sum_pow_div_factorial_mul_sqBracketCoeff hk d j]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro m _ hm
  rw [Finset.mem_range, not_lt] at hm
  rw [sqBracketCoeff_eq_zero_of_lt kc (by omega), mul_zero]

/-- The spatial kernel identity. -/
theorem lsum_spatial_eq_piK {kc : ℕ} (hk : 1 ≤ kc) {j K : ℕ} (hj : j < K) :
    lsum (fun i => cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (tt ^ (i + 1) * geo (i + 1)) -
      cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (uu ^ (i + 1) * geo (i + 1))) =
      ∑ m ∈ Finset.range K, sqBracketCoeff kc m j • piK m := by
  have hterm : ∀ i : ℕ,
      cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (tt ^ (i + 1) * geo (i + 1)) -
        cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (uu ^ (i + 1) * geo (i + 1)) =
      ∑ m ∈ Finset.range K, sqBracketCoeff kc m j •
        (((((i + 1 : ℕ) : ℂ) ^ m / (m.factorial : ℂ)) • (tt ^ (i + 1) * geo (i + 1)) -
          ((-((i + 1 : ℕ) : ℂ)) ^ m / (m.factorial : ℂ)) • (uu ^ (i + 1) * geo (i + 1)))) := by
    intro i
    rw [cbz_eq_sum_sq hk _ hj, show (kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ) =
      (kc : ℤ) - 1 + (-((i + 1 : ℕ) : ℤ)) by ring, cbz_eq_sum_sq hk _ hj,
      Finset.sum_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    rw [smul_sub, smul_smul, smul_smul]
    congr 2 <;> ring
  rw [lsum_congr hterm, lsum_finset_sum]
  · apply Finset.sum_congr rfl
    intro m _
    rw [lsum_smul_const, piK]
    exact (locFin_tt_geo _).sub (locFin_uu_geo _)
  · intro m _
    exact ((locFin_tt_geo _).sub (locFin_uu_geo _)).smul (fun _ => _)

/-- The Lambert kernel identity. -/
theorem lsum_lambert_eq_xiK {kc : ℕ} (hk : 1 ≤ kc) {j K : ℕ} (hj : j < K) :
    lsum (fun i => (cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) -
        cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ)) • (qq ^ (i + 1) * geo (i + 1))) =
      ∑ m ∈ Finset.range K, sqBracketCoeff kc m j • xiK m := by
  have hterm : ∀ i : ℕ,
      (cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) -
        cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ)) • (qq ^ (i + 1) * geo (i + 1)) =
      ∑ m ∈ Finset.range K, sqBracketCoeff kc m j •
        (((((i + 1 : ℕ) : ℂ) ^ m - (-((i + 1 : ℕ) : ℂ)) ^ m) / (m.factorial : ℂ)) •
          (qq ^ (i + 1) * geo (i + 1))) := by
    intro i
    rw [cbz_eq_sum_sq hk _ hj, show (kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ) =
      (kc : ℤ) - 1 + (-((i + 1 : ℕ) : ℤ)) by ring, cbz_eq_sum_sq hk _ hj,
      ← Finset.sum_sub_distrib, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    rw [smul_smul]
    congr 1
    ring
  rw [lsum_congr hterm, lsum_finset_sum]
  · apply Finset.sum_congr rfl
    intro m _
    rw [lsum_smul_const (locFin_qq_geo _), xiK]
  · intro m _
    exact (locFin_qq_geo _).smul (fun _ => _)

end VOA.Huang.GenusOneWard
