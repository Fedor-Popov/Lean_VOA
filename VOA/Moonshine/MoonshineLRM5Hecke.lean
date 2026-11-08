import VOA.Moonshine.MoonshineLRHeckeExpansion

/-!
# The Hecke sum of a single `q`-series

For a `J`-dominated coefficient sequence `c` (`IsJDominated c`) with `f = qSeriesFun c`, and
`M ≥ 1`, the Hecke sum `R_M(τ) = Σ_{ad = M} Σ_{b<d} f((aτ+b)/d)` (`qHeckeSum c M`) satisfies
`R_M(τ) − q^{−M} = Σ_{r ≥ 1} (Σ_{a ∣ gcd(M,r)} (M/a) c(Mr/a²)) qʳ` (`hasSum_qHeckeSum`).

Blueprint: the Hecke expansion in `Notes/moonshine/MOON_BKM.md`, the single-series version of
`hasSum_heckeOrbitSum` (`MoonshineLRHeckeExpansion`), with the same proof: the root-of-unity sum
over `b` in each block (`hasSum_qHeckeBlock`), then the divisor bookkeeping. It is used for `J`
in the untwisted denominator identity and can be reused for complete replicability.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real

/-- The Hecke block `B(a, d)(τ) = Σ_{b<d} f((aτ+b)/d)` of a single `q`-series
(zero unless `a, d > 0`). -/
noncomputable def qHeckeBlock (c : ℕ → ℂ) (a d : ℕ) (τ : ℍ) : ℂ :=
  if h : 0 < a ∧ 0 < d then
    ∑ b ∈ Finset.range d, qSeriesFun c (heckePoint a d b h.1 h.2 τ)
  else 0

theorem qHeckeBlock_of_pos (c : ℕ → ℂ) (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    qHeckeBlock c a d τ = ∑ b ∈ Finset.range d, qSeriesFun c (heckePoint a d b ha hd τ) := by
  rw [qHeckeBlock, dif_pos ⟨ha, hd⟩]

/-- The Hecke sum `R_M(τ) = Σ_{a ∣ M} Σ_{b < M/a} f((aτ+b)/(M/a))` of a single `q`-series. -/
noncomputable def qHeckeSum (c : ℕ → ℂ) (M : ℕ) (τ : ℍ) : ℂ :=
  ∑ a ∈ M.divisors, qHeckeBlock c a (M / a) τ

/-- The `qʳ`-coefficient of `R_M − q^{−M}`: `Σ_{a ∣ gcd(M,r)} (M/a) · c(Mr/a²)`. -/
noncomputable def qHeckeCoeff (c : ℕ → ℂ) (M r : ℕ) : ℂ :=
  ∑ a ∈ (Nat.gcd M r).divisors, ((M / a : ℕ) : ℂ) * c (M * r / (a * a))

/-- **One Hecke block of a single `q`-series.** For `a, d > 0`,
`B(a, d)(τ) − [d = 1] q^{−a} = Σ_r [r ≠ 0 ∧ a ∣ r] · d · c(d · r/a) · qʳ`. -/
theorem hasSum_qHeckeBlock {c : ℕ → ℂ} (hc : IsJDominated c) (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ : ℍ) :
    HasSum (fun r : ℕ => (if r ≠ 0 ∧ a ∣ r then (d : ℂ) * c (d * (r / a)) else 0) * qPar τ ^ r)
      (qHeckeBlock c a d τ - if d = 1 then (qPar τ ^ a)⁻¹ else 0) := by
  set Q := qPar (heckePoint a d 0 ha hd τ) with hQ
  set ζ := Complex.exp (2 * π * Complex.I / d) with hζdef
  have htail : ∀ b ∈ Finset.range d,
      HasSum (fun n : ℕ => c (n + 1) * (Q * ζ ^ b) ^ (n + 1)) (qTailSeries c (Q * ζ ^ b)) := by
    intro b _
    refine (summable_qTail_term hc (heckePoint a d b ha hd τ).im_pos ?_).hasSum
    rw [hQ, hζdef, ← qPar_heckePoint, norm_qPar_eq]
  have hsum := hasSum_sum htail
  have hblock : qHeckeBlock c a d τ = ∑ b ∈ Finset.range d, (Q * ζ ^ b)⁻¹ +
      ∑ b ∈ Finset.range d, qTailSeries c (Q * ζ ^ b) := by
    rw [qHeckeBlock_of_pos c a d ha hd, ← Finset.sum_add_distrib]
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

/-- **The `q`-expansion of the Hecke sum of a single `q`-series** (blueprint: `MOON_BKM.md`). -/
theorem hasSum_qHeckeSum {c : ℕ → ℂ} (hc : IsJDominated c) {m : ℕ} (hm : 0 < m) (τ : ℍ) :
    HasSum (fun r : ℕ => (if r = 0 then 0 else qHeckeCoeff c m r) * qPar τ ^ r)
      (qHeckeSum c m τ - (qPar τ ^ m)⁻¹) := by
  have hblocks : ∀ a ∈ m.divisors, HasSum
      (fun r : ℕ => (if r ≠ 0 ∧ a ∣ r then ((m / a : ℕ) : ℂ) * c (m / a * (r / a))
        else 0) * qPar τ ^ r)
      (qHeckeBlock c a (m / a) τ - if m / a = 1 then (qPar τ ^ a)⁻¹ else 0) := fun a ha =>
    hasSum_qHeckeBlock hc a (m / a) (Nat.pos_of_mem_divisors ha)
      (Nat.div_pos (Nat.divisor_le ha) (Nat.pos_of_mem_divisors ha)) τ
  have h := hasSum_sum hblocks
  rw [Finset.sum_sub_distrib, ← qHeckeSum] at h
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
  · rw [if_neg hr, qHeckeCoeff]
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
