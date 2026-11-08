import VOA.Moonshine.MoonshineLRHecke
import VOA.Moonshine.MoonshineLRCoeffBound
import VOA.Moonshine.MoonshineLRTower

/-!
# The `q`-expansion of the replicate Hecke sum

For a replicable family `F`, a member `k` and `m ≥ 1`,
`H_m(τ) = q^{−m} + Σ_{r ≥ 1} (Σ_{a ∣ gcd(m,r)} (m/a) c_{ka}(mr/a²)) qʳ`
(`hasSum_heckeOrbitSum`), where the coefficient is `faberRemainderCoeff F.c k m r` of
`MoonshineLRTower`.

Proof. For one Hecke block `B(a, d)(τ) = Σ_{b<d} f_{ka}((aτ+b)/d)` the `q`-parameter of the `b`-th
point is `Q ζᵇ`, with `Q = e^{2πi aτ/d}`, `ζ = e^{2πi/d}` and `Q^d = qᵃ`. The pole terms `(Q ζᵇ)⁻¹`
cancel unless `d = 1` (`sum_range_pow_rootOfUnity`). In the tail only the exponents `n+1 = d s`
survive, with weight `d`, and `Q^{ds} = q^{as}` (`hasSum_heckeBlock`). Summing over `a ∣ m`
collects the coefficient of `qʳ` over the divisors of `gcd(m, r)`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real

theorem heckePoint_eq_vadd (a d b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    heckePoint a d b ha hd τ = ((b : ℝ) / d) +ᵥ heckePoint a d 0 ha hd τ := by
  apply UpperHalfPlane.ext
  rw [coe_vadd, coe_heckePoint_apply, coe_heckePoint_apply]
  push_cast
  ring

theorem qPar_heckePoint (a d b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    qPar (heckePoint a d b ha hd τ) =
      qPar (heckePoint a d 0 ha hd τ) * Complex.exp (2 * π * Complex.I / d) ^ b := by
  rw [heckePoint_eq_vadd a d b, qPar_vadd_div]

theorem qPar_heckePoint_zero_pow (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    qPar (heckePoint a d 0 ha hd τ) ^ d = qPar τ ^ a := by
  simp only [qPar, Function.Periodic.qParam, coe_heckePoint_apply]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp
  ring

/-- The pole part of a Hecke block: `Σ_{b<d} (Q ζᵇ)⁻¹` is `Q⁻¹` if `d = 1` and `0` otherwise. -/
theorem sum_inv_mul_rootOfUnity (Q : ℂ) {d : ℕ} (hd : 0 < d) :
    ∑ b ∈ Finset.range d, (Q * Complex.exp (2 * π * Complex.I / d) ^ b)⁻¹ =
      if d = 1 then Q⁻¹ else 0 := by
  set ζ := Complex.exp (2 * π * Complex.I / d) with hζdef
  have hζ := Complex.isPrimitiveRoot_exp d hd.ne'
  have hinv : ∀ b : ℕ, (ζ ^ b)⁻¹ = (ζ ^ (d - 1)) ^ b := by
    intro b
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_mul, ← pow_add, show (d - 1) * b + b = d * b by
      rcases d with _ | d
      · omega
      · simp only [Nat.add_sub_cancel]; ring, pow_mul, hζ.pow_eq_one, one_pow]
  simp_rw [mul_inv, hinv]
  rw [← Finset.mul_sum, sum_range_pow_rootOfUnity hd]
  by_cases h1 : d = 1
  · subst h1
    simp
  · rw [if_neg (fun h => h1 (by
        have := Nat.le_of_dvd (by omega) h
        omega)), if_neg h1, mul_zero]
    -- `d ∣ d − 1` with `0 < d − 1 < d` is impossible; the `if_neg` above uses `d − 1 > 0`

/-- **One Hecke block as a `q`-series.** For `a, d > 0`,
`B(a, d)(τ) − [d = 1] q^{−a} = Σ_r [r ≠ 0 ∧ a ∣ r] · d · c_{ka}(d · r/a) · qʳ`. -/
theorem hasSum_heckeBlock {N : ℕ} (F : ReplicableFamily N) (k a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ : ℍ) :
    HasSum (fun r : ℕ => (if r ≠ 0 ∧ a ∣ r then (d : ℂ) * F.c (k * a) (d * (r / a)) else 0) *
        qPar τ ^ r)
      (heckeBlock F k a d τ - if d = 1 then (qPar τ ^ a)⁻¹ else 0) := by
  set c := F.c (k * a) with hcdef
  set Q := qPar (heckePoint a d 0 ha hd τ) with hQ
  set ζ := Complex.exp (2 * π * Complex.I / d) with hζdef
  have hc : IsJDominated c := F.isJDominated (k * a)
  have htail : ∀ b ∈ Finset.range d,
      HasSum (fun n : ℕ => c (n + 1) * (Q * ζ ^ b) ^ (n + 1)) (qTailSeries c (Q * ζ ^ b)) := by
    intro b _
    refine (summable_qTail_term hc (heckePoint a d b ha hd τ).im_pos ?_).hasSum
    rw [hQ, hζdef, ← qPar_heckePoint, norm_qPar_eq]
  have hsum := hasSum_sum htail
  have hblock : heckeBlock F k a d τ = ∑ b ∈ Finset.range d, (Q * ζ ^ b)⁻¹ +
      ∑ b ∈ Finset.range d, qTailSeries c (Q * ζ ^ b) := by
    rw [heckeBlock_of_pos F k a d ha hd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [qSeriesFun_eq_inv_add_qTailSeries, qPar_heckePoint]
  have hQd : Q ^ d = qPar τ ^ a := qPar_heckePoint_zero_pow a d ha hd τ
  have hpole : ∑ b ∈ Finset.range d, (Q * ζ ^ b)⁻¹ = if d = 1 then (qPar τ ^ a)⁻¹ else 0 := by
    rw [sum_inv_mul_rootOfUnity Q hd]
    by_cases h1 : d = 1
    · rw [if_pos h1, if_pos h1, ← hQd, h1, pow_one]
    · rw [if_neg h1, if_neg h1]
  rw [hblock, hpole, add_sub_cancel_left]
  have hinner : ∀ n : ℕ, ∑ b ∈ Finset.range d, c (n + 1) * (Q * ζ ^ b) ^ (n + 1) =
      if d ∣ n + 1 then (d : ℂ) * c (n + 1) * Q ^ (n + 1) else 0 := by
    intro n
    have e : ∀ b : ℕ, c (n + 1) * (Q * ζ ^ b) ^ (n + 1) =
        c (n + 1) * Q ^ (n + 1) * (ζ ^ (n + 1)) ^ b := by
      intro b
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, hζdef, sum_range_pow_rootOfUnity hd]
    split_ifs <;> ring
  simp_rw [hinner] at hsum
  -- reindex `n + 1 = d (s + 1)`
  have hinj1 : Function.Injective fun s : ℕ => d * (s + 1) - 1 := by
    intro s t h
    have h' : d * (s + 1) = d * (t + 1) := by
      have h1 : 1 ≤ d * (s + 1) := Nat.mul_pos hd (Nat.succ_pos s)
      have h2 : 1 ≤ d * (t + 1) := Nat.mul_pos hd (Nat.succ_pos t)
      simp only at h
      omega
    have := Nat.eq_of_mul_eq_mul_left hd h'
    omega
  have hsupp1 : ∀ n : ℕ, n ∉ Set.range (fun s : ℕ => d * (s + 1) - 1) →
      (if d ∣ n + 1 then (d : ℂ) * c (n + 1) * Q ^ (n + 1) else 0) = 0 := by
    intro n hn
    rw [if_neg]
    rintro ⟨j, hj⟩
    apply hn
    rcases j with _ | j
    · omega
    · exact ⟨j, by simp only; omega⟩
  have e1 := (hinj1.hasSum_iff hsupp1).mpr hsum
  have hinj2 : Function.Injective fun s : ℕ => a * (s + 1) := by
    intro s t h
    have := Nat.eq_of_mul_eq_mul_left ha h
    omega
  have hsupp2 : ∀ r : ℕ, r ∉ Set.range (fun s : ℕ => a * (s + 1)) →
      (if r ≠ 0 ∧ a ∣ r then (d : ℂ) * c (d * (r / a)) else 0) * qPar τ ^ r = 0 := by
    intro r hr
    rw [if_neg, zero_mul]
    rintro ⟨hr0, j, hj⟩
    apply hr
    rcases j with _ | j
    · omega
    · exact ⟨j, by simp only; omega⟩
  refine (hinj2.hasSum_iff hsupp2).mp ?_
  convert e1 using 1
  funext s
  simp only [Function.comp]
  have hds : d * (s + 1) - 1 + 1 = d * (s + 1) := by
    have : 1 ≤ d * (s + 1) := Nat.mul_pos hd (Nat.succ_pos s)
    omega
  rw [hds, if_pos (dvd_mul_right d _), if_pos ⟨by positivity, dvd_mul_right a _⟩,
    Nat.mul_div_cancel_left _ ha, pow_mul, pow_mul, hQd]

/-- **The `q`-expansion of the replicate Hecke sum.** For `m ≥ 1`,
`H_m(τ) − q^{−m} = Σ_{r ≥ 1} faberRemainderCoeff F.c k m r · qʳ`. -/
theorem hasSum_heckeOrbitSum {N : ℕ} (F : ReplicableFamily N) (k : ℕ) {m : ℕ} (hm : 0 < m)
    (τ : ℍ) :
    HasSum (fun r : ℕ => (if r = 0 then 0 else faberRemainderCoeff F.c k m r) * qPar τ ^ r)
      (heckeOrbitSum F k m τ - (qPar τ ^ m)⁻¹) := by
  have hblocks : ∀ a ∈ m.divisors, HasSum
      (fun r : ℕ => (if r ≠ 0 ∧ a ∣ r then ((m / a : ℕ) : ℂ) * F.c (k * a) (m / a * (r / a))
        else 0) * qPar τ ^ r)
      (heckeBlock F k a (m / a) τ - if m / a = 1 then (qPar τ ^ a)⁻¹ else 0) := fun a ha =>
    hasSum_heckeBlock F k a (m / a) (Nat.pos_of_mem_divisors ha)
      (Nat.div_pos (Nat.divisor_le ha) (Nat.pos_of_mem_divisors ha)) τ
  have h := hasSum_sum hblocks
  rw [Finset.sum_sub_distrib, ← heckeOrbitSum_eq_sum_heckeBlock] at h
  have hpole : ∑ a ∈ m.divisors, (if m / a = 1 then (qPar τ ^ a)⁻¹ else 0) = (qPar τ ^ m)⁻¹ := by
    rw [Finset.sum_eq_single m]
    · rw [Nat.div_self hm, if_pos rfl]
    · intro a ha hne
      rw [if_neg]
      intro h1
      apply hne
      have hdvd := Nat.dvd_of_mem_divisors ha
      have := Nat.div_mul_cancel hdvd
      rw [h1, one_mul] at this
      exact this
    · intro hmn
      exact absurd (Nat.mem_divisors_self m hm.ne') hmn
  rw [hpole] at h
  convert h using 1
  funext r
  rw [← Finset.sum_mul]
  congr 1
  by_cases hr : r = 0
  · subst hr
    simp
  · rw [if_neg hr, faberRemainderCoeff]
    have hset : (Nat.gcd m r).divisors = m.divisors.filter (fun a => a ∣ r) := by
      ext a
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩
        exact ⟨⟨h1, hm.ne'⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left r hm).ne'⟩
    rw [hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases har : a ∣ r
    · rw [if_pos har, if_pos ⟨hr, har⟩,
        Nat.div_mul_div_comm (Nat.dvd_of_mem_divisors ha) har]
    · rw [if_neg har, if_neg (fun h => har h.2)]

end VOA.Moonshine.ConwayNorton.M8
