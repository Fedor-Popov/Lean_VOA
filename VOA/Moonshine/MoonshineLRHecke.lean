import VOA.Moonshine.MoonshineCNGenusZeroInterface

/-!
# The prime Hecke identity

Blueprint: the prime Hecke identity in `MOON_M8_LEAN.md`.

For a replicable family `F` of period `N`, a member `k` and a prime `p ≡ 1 (mod N)`, with
`H_m = heckeOrbitSum F k m`:
`Σ_{j<p} H_m((τ+j)/p) + H_m(pτ) = H_{mp}(τ) + [p ∣ m] · p · H_{m/p}(τ)`
(`PrimeHeckeIdentityAt`, `MoonshineCNGenusZeroInterface`).
Main result:
`ReplicableFamily_primeHeckeIdentity : PrimeHeckeIdentity F k`.

Proof (the prime Hecke argument in `Notes/moonshine/MOON_ROUTE.md`).
Write `H_m = Σ_{a ∣ m} B(a, m/a)` with the Hecke block
`B(a, d)(τ) = Σ_{b<d} f_{ka}((aτ+b)/d)` (`heckeBlock`). Then
* `B(a, d)(pτ) = B(ap, d)(τ)` (`heckeBlock_at_mul`), since `f_{kap} = f_{ka}` for `p ≡ 1 (mod N)`;
* if `p ∤ a`, `Σ_{j<p} B(a, d)((τ+j)/p) = B(a, dp)(τ)` (`sum_heckeBlock_at_div_of_not_dvd`): the map
  `(j, b) ↦ aj + bp` is a bijection onto the residues mod `dp`, and `f` is `1`-periodic;
* if `a = p a₀`, `Σ_{j<p} B(a, d)((τ+j)/p) = p · B(a₀, d)(τ)` (`sum_heckeBlock_at_div_of_eq_mul`);
* the divisors of `mp` divisible by `p` are `a p` with `a ∣ m`, and those prime to `p` are the
  divisors of `m` prime to `p`; the divisors of `m` divisible by `p` are `p a₀` with `a₀ ∣ m/p`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real

/-! ### Periodicity -/

theorem qPar_eq_of_eq_add_int {σ τ : ℍ} {n : ℤ} (h : (σ : ℂ) = τ + n) : qPar σ = qPar τ := by
  have e : 2 * (π : ℂ) * Complex.I * (σ : ℂ) / ((1 : ℝ) : ℂ) =
      2 * (π : ℂ) * Complex.I * (τ : ℂ) / ((1 : ℝ) : ℂ) + n * (2 * (π : ℂ) * Complex.I) := by
    rw [h]
    push_cast
    ring
  simp only [qPar, Function.Periodic.qParam, e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one]

/-- `qSeriesFun c` is `1`-periodic. -/
theorem qSeriesFun_eq_of_eq_add_int (c : ℕ → ℂ) {σ τ : ℍ} {n : ℤ} (h : (σ : ℂ) = τ + n) :
    qSeriesFun c σ = qSeriesFun c τ := by
  simp only [qSeriesFun, qPar_eq_of_eq_add_int h]

theorem coe_heckePoint_apply (a d b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    (heckePoint a d b ha hd τ : ℂ) = (a * (τ : ℂ) + b) / d :=
  rfl

/-! ### Replicates modulo the period -/

theorem ReplicableFamily_c_add_mul {N : ℕ} (F : ReplicableFamily N) (r q : ℕ) :
    F.c (r + N * q) = F.c r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, ← add_assoc]
    funext n
    rw [F.periodic, ih]

theorem ReplicableFamily_c_eq_of_modEq {N : ℕ} (F : ReplicableFamily N) {i j : ℕ}
    (h : i ≡ j [MOD N]) : F.c i = F.c j := by
  have hi : F.c i = F.c (i % N) := by
    conv_lhs => rw [← Nat.mod_add_div i N]
    exact ReplicableFamily_c_add_mul F _ _
  have hj : F.c j = F.c (j % N) := by
    conv_lhs => rw [← Nat.mod_add_div j N]
    exact ReplicableFamily_c_add_mul F _ _
  rw [hi, hj, show i % N = j % N from h]

theorem ReplicableFamily_c_mul_mul_of_modEq_one {N : ℕ} (F : ReplicableFamily N) (k a : ℕ) {p : ℕ}
    (hp : p ≡ 1 [MOD N]) : F.c (k * (a * p)) = F.c (k * a) := by
  apply ReplicableFamily_c_eq_of_modEq
  have := Nat.ModEq.mul_left k (Nat.ModEq.mul_left a hp)
  simpa using this

/-! ### Sums of periodic sequences -/

/-- Summing a `D`-periodic sequence along an index set of size `D` that maps injectively to the
residues mod `D` gives the sum over one period. -/
theorem sum_comp_eq_sum_range_of_periodic {α : Type*} (s : Finset α) (e : α → ℕ) (φ : ℕ → ℂ)
    {D : ℕ} (hD : 0 < D) (hφ : ∀ n, φ (n + D) = φ n) (hinj : Set.InjOn (fun i => e i % D) s)
    (hcard : s.card = D) : ∑ i ∈ s, φ (e i) = ∑ n ∈ Finset.range D, φ n := by
  have key : ∀ q r, φ (r + D * q) = φ r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih => intro r; rw [Nat.mul_succ, ← add_assoc, hφ, ih]
  have hper : ∀ n, φ n = φ (n % D) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n D]
    exact key _ _
  rw [Finset.sum_congr rfl fun i _ => hper (e i), ← Finset.sum_image hinj]
  congr 1
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (Nat.mod_lt _ hD)
  · rw [Finset.card_range, Finset.card_image_of_injOn hinj, hcard]

/-! ### Hecke blocks -/

/-- The Hecke block `B(a, d)(τ) = Σ_{b<d} f_{ka}((aτ+b)/d)` (zero unless `a, d > 0`). -/
noncomputable def heckeBlock {N : ℕ} (F : ReplicableFamily N) (k a d : ℕ) (τ : ℍ) : ℂ :=
  if h : 0 < a ∧ 0 < d then
    ∑ b ∈ Finset.range d, qSeriesFun (F.c (k * a)) (heckePoint a d b h.1 h.2 τ)
  else 0

theorem heckeBlock_of_pos {N : ℕ} (F : ReplicableFamily N) (k a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ : ℍ) :
    heckeBlock F k a d τ =
      ∑ b ∈ Finset.range d, qSeriesFun (F.c (k * a)) (heckePoint a d b ha hd τ) := by
  rw [heckeBlock, dif_pos ⟨ha, hd⟩]

theorem heckeOrbitSum_eq_sum_heckeBlock {N : ℕ} (F : ReplicableFamily N) (k m : ℕ) (τ : ℍ) :
    heckeOrbitSum F k m τ = ∑ a ∈ m.divisors, heckeBlock F k a (m / a) τ := by
  rw [heckeOrbitSum, ← Finset.sum_attach m.divisors (fun a => heckeBlock F k a (m / a) τ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [heckeBlock_of_pos]

/-- `B(a, d)(pτ) = B(ap, d)(τ)` when `f_{kap} = f_{ka}`. -/
theorem heckeBlock_at_mul {N : ℕ} (F : ReplicableFamily N) (k a d p : ℕ) (ha : 0 < a)
    (hd : 0 < d) (hp : 0 < p) (hc : F.c (k * (a * p)) = F.c (k * a)) (τ : ℍ) :
    heckeBlock F k a d (heckePoint p 1 0 hp one_pos τ) = heckeBlock F k (a * p) d τ := by
  rw [heckeBlock_of_pos F k a d ha hd, heckeBlock_of_pos F k (a * p) d (Nat.mul_pos ha hp) hd, hc]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  apply UpperHalfPlane.ext
  simp only [coe_heckePoint_apply]
  push_cast
  ring

/-- If `p ∤ a` (`p` prime): `Σ_{j<p} B(a, d)((τ+j)/p) = B(a, dp)(τ)`. -/
theorem sum_heckeBlock_at_div_of_not_dvd {N : ℕ} (F : ReplicableFamily N) (k a d p : ℕ)
    (ha : 0 < a) (hd : 0 < d) (hp : p.Prime) (hpa : ¬ p ∣ a) (τ : ℍ) :
    ∑ j ∈ Finset.range p, heckeBlock F k a d (heckePoint 1 p j one_pos hp.pos τ) =
      heckeBlock F k a (d * p) τ := by
  have hdp : 0 < d * p := Nat.mul_pos hd hp.pos
  set φ : ℕ → ℂ := fun n => qSeriesFun (F.c (k * a)) (heckePoint a (d * p) n ha hdp τ) with hφdef
  have hpt : ∀ j b : ℕ, heckePoint a d b ha hd (heckePoint 1 p j one_pos hp.pos τ) =
      heckePoint a (d * p) (a * j + b * p) ha hdp τ := by
    intro j b
    apply UpperHalfPlane.ext
    simp only [coe_heckePoint_apply]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    ring
  rw [heckeBlock_of_pos F k a (d * p) ha hdp]
  simp_rw [heckeBlock_of_pos F k a d ha hd, hpt]
  rw [← Finset.sum_product (Finset.range p) (Finset.range d)
    (fun x : ℕ × ℕ => φ (a * x.1 + x.2 * p))]
  refine sum_comp_eq_sum_range_of_periodic _ (fun x : ℕ × ℕ => a * x.1 + x.2 * p) φ hdp ?_ ?_ ?_
  · intro n
    simp only [hφdef]
    apply qSeriesFun_eq_of_eq_add_int (n := 1)
    simp only [coe_heckePoint_apply]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    ring
  · rintro ⟨j, b⟩ hjb ⟨j', b'⟩ hjb' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hjb hjb'
    have hmod : a * j + b * p ≡ a * j' + b' * p [MOD d * p] := heq
    have hmodp : a * j + b * p ≡ a * j' + b' * p [MOD p] := Nat.ModEq.of_mul_left d hmod
    have h0 : b * p ≡ b' * p [MOD p] := by
      simp [Nat.ModEq, Nat.mul_mod_left]
    have hj : a * j ≡ a * j' [MOD p] := Nat.ModEq.add_right_cancel h0 hmodp
    have hcop : Nat.gcd p a = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa
    have hjj : j ≡ j' [MOD p] := Nat.ModEq.cancel_left_of_coprime hcop hj
    have hjeq : j = j' := by
      have := hjj
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt hjb.1, Nat.mod_eq_of_lt hjb'.1] at this
    subst hjeq
    have hb : b * p ≡ b' * p [MOD d * p] := Nat.ModEq.add_left_cancel' (a * j) hmod
    have hbb : b ≡ b' [MOD d] := Nat.ModEq.mul_right_cancel' hp.pos.ne' hb
    have hbeq : b = b' := by
      have := hbb
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt hjb.2, Nat.mod_eq_of_lt hjb'.2] at this
    rw [hbeq]
  · rw [Finset.card_product, Finset.card_range, Finset.card_range, mul_comm]

/-- If `a = p a₀` and `f_{kpa₀} = f_{ka₀}`: `Σ_{j<p} B(a, d)((τ+j)/p) = p · B(a₀, d)(τ)`. -/
theorem sum_heckeBlock_at_div_of_eq_mul {N : ℕ} (F : ReplicableFamily N) (k a₀ d p : ℕ)
    (ha₀ : 0 < a₀) (hd : 0 < d) (hp : 0 < p) (hc : F.c (k * (p * a₀)) = F.c (k * a₀)) (τ : ℍ) :
    ∑ j ∈ Finset.range p, heckeBlock F k (p * a₀) d (heckePoint 1 p j one_pos hp τ) =
      (p : ℂ) * heckeBlock F k a₀ d τ := by
  have hpa : 0 < p * a₀ := Nat.mul_pos hp ha₀
  set φ : ℕ → ℂ := fun n => qSeriesFun (F.c (k * a₀)) (heckePoint a₀ d n ha₀ hd τ) with hφdef
  have hpt : ∀ j b : ℕ, heckePoint (p * a₀) d b hpa hd (heckePoint 1 p j one_pos hp τ) =
      heckePoint a₀ d (a₀ * j + b) ha₀ hd τ := by
    intro j b
    apply UpperHalfPlane.ext
    simp only [coe_heckePoint_apply]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    ring
  have hinner : ∀ j : ℕ, heckeBlock F k (p * a₀) d (heckePoint 1 p j one_pos hp τ) =
      heckeBlock F k a₀ d τ := by
    intro j
    rw [heckeBlock_of_pos F k (p * a₀) d hpa hd, heckeBlock_of_pos F k a₀ d ha₀ hd, hc]
    simp_rw [hpt]
    refine sum_comp_eq_sum_range_of_periodic (Finset.range d) (fun b => a₀ * j + b) φ hd ?_ ?_ ?_
    · intro n
      simp only [hφdef]
      apply qSeriesFun_eq_of_eq_add_int (n := 1)
      simp only [coe_heckePoint_apply]
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      push_cast
      field_simp
      ring
    · intro b hb b' hb' heq
      simp only [Finset.coe_range, Set.mem_Iio] at hb hb'
      have h1 : a₀ * j + b ≡ a₀ * j + b' [MOD d] := heq
      have h2 := Nat.ModEq.add_left_cancel' (a₀ * j) h1
      unfold Nat.ModEq at h2
      rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h2
    · rw [Finset.card_range]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Assembly: divisor bookkeeping -/

/-- **The prime Hecke identity** at every prime `p ≡ 1 (mod N)`, for every member `k` of
a replicable family of period `N`. -/
theorem ReplicableFamily_primeHeckeIdentity {N : ℕ} (F : ReplicableFamily N) (k : ℕ) :
    PrimeHeckeIdentity F k := by
  intro p hp hpN m hm τ
  have hp0 : 0 < p := hp.pos
  have hc : ∀ a, F.c (k * (a * p)) = F.c (k * a) :=
    fun a => ReplicableFamily_c_mul_mul_of_modEq_one F k a hpN
  have hm0 : m ≠ 0 := hm.ne'
  simp_rw [heckeOrbitSum_eq_sum_heckeBlock]
  rw [Finset.sum_comm]
  -- the blocks at `pτ`
  have h2 : ∑ a ∈ m.divisors, heckeBlock F k a (m / a) (heckePoint p 1 0 hp0 one_pos τ) =
      ∑ a ∈ m.divisors, heckeBlock F k (a * p) (m / a) τ :=
    Finset.sum_congr rfl fun a ha => heckeBlock_at_mul F k a (m / a) p
      (Nat.pos_of_mem_divisors ha) (Nat.div_pos (Nat.divisor_le ha) (Nat.pos_of_mem_divisors ha))
      hp0 (hc a) τ
  -- the blocks at `(τ+j)/p`, split by `p ∣ a`
  have hL1 : ∑ a ∈ m.divisors, ∑ j ∈ Finset.range p,
        heckeBlock F k a (m / a) (heckePoint 1 p j one_pos hp0 τ) =
      ∑ a ∈ m.divisors.filter (fun a => p ∣ a), (p : ℂ) * heckeBlock F k (a / p) (m / a) τ +
        ∑ a ∈ m.divisors.filter (fun a => ¬ p ∣ a), heckeBlock F k a (m * p / a) τ := by
    rw [← Finset.sum_filter_add_sum_filter_not m.divisors (fun a => p ∣ a)]
    congr 1
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp ha
      have hapos := Nat.pos_of_mem_divisors ha
      have ha₀ : 0 < a / p := Nat.div_pos (Nat.le_of_dvd hapos hpa) hp0
      have hd : 0 < m / a := Nat.div_pos (Nat.divisor_le ha) hapos
      have hc' : F.c (k * (p * (a / p))) = F.c (k * (a / p)) := by
        rw [mul_comm p]
        exact hc _
      have := sum_heckeBlock_at_div_of_eq_mul F k (a / p) (m / a) p ha₀ hd hp0 hc' τ
      rwa [Nat.mul_div_cancel' hpa] at this
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp ha
      have hapos := Nat.pos_of_mem_divisors ha
      have hd : 0 < m / a := Nat.div_pos (Nat.divisor_le ha) hapos
      rw [sum_heckeBlock_at_div_of_not_dvd F k a (m / a) p hapos hd hp hpa τ,
        Nat.div_mul_right_comm (Nat.dvd_of_mem_divisors ha)]
  -- the divisors of `mp`
  have hR1 : ∑ a ∈ (m * p).divisors, heckeBlock F k a (m * p / a) τ =
      ∑ a ∈ m.divisors, heckeBlock F k (a * p) (m / a) τ +
        ∑ a ∈ m.divisors.filter (fun a => ¬ p ∣ a), heckeBlock F k a (m * p / a) τ := by
    rw [← Finset.sum_filter_add_sum_filter_not (m * p).divisors (fun a => p ∣ a)]
    congr 1
    · symm
      refine Finset.sum_nbij' (fun a => a * p) (fun a => a / p) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        have ha := Finset.mem_coe.mp ha
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, dvd_mul_left p a⟩)
        exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors ha) p,
          Nat.mul_ne_zero hm0 hp0.ne'⟩
      · intro a ha
        obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
        obtain ⟨q, rfl⟩ := hpa
        refine Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨?_, hm0⟩)
        dsimp only
        rw [Nat.mul_div_cancel_left q hp0]
        have h1 : p * q ∣ m * p := Nat.dvd_of_mem_divisors ha
        rw [mul_comm m p] at h1
        exact Nat.dvd_of_mul_dvd_mul_left hp0 h1
      · intro a _
        exact Nat.mul_div_cancel a hp0
      · intro a ha
        obtain ⟨_, hpa⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
        exact Nat.div_mul_cancel hpa
      · intro a _
        rw [Nat.mul_div_mul_right m a hp0]
    · congr 1
      ext a
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hpa⟩
        have hcop : Nat.Coprime a p :=
          Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)
        exact ⟨⟨hcop.dvd_of_dvd_mul_right hdvd, hm0⟩, hpa⟩
      · rintro ⟨⟨hdvd, _⟩, hpa⟩
        exact ⟨⟨dvd_mul_of_dvd_left hdvd p, Nat.mul_ne_zero hm0 hp0.ne'⟩, hpa⟩
  -- the term `[p ∣ m] · p · H_{m/p}`
  have hR2 : (if p ∣ m then (p : ℂ) * ∑ a ∈ (m / p).divisors, heckeBlock F k a (m / p / a) τ
        else 0) =
      ∑ a ∈ m.divisors.filter (fun a => p ∣ a), (p : ℂ) * heckeBlock F k (a / p) (m / a) τ := by
    split_ifs with hpm
    · rw [Finset.mul_sum]
      refine Finset.sum_nbij' (fun a => p * a) (fun a => a / p) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        have ha := Nat.mem_divisors.mp (Finset.mem_coe.mp ha)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hm0⟩,
          dvd_mul_right p a⟩)
        obtain ⟨r, hr⟩ := hpm
        have h1 : a ∣ r := by
          rw [hr, Nat.mul_div_cancel_left r hp0] at ha
          exact ha.1
        rw [hr]
        exact Nat.mul_dvd_mul_left p h1
      · intro a ha
        obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
        refine Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨?_, ?_⟩)
        · obtain ⟨q, rfl⟩ := hpa
          dsimp only
          rw [Nat.mul_div_cancel_left q hp0]
          exact Nat.dvd_div_of_mul_dvd (Nat.dvd_of_mem_divisors ha)
        · exact (Nat.div_pos (Nat.le_of_dvd hm hpm) hp0).ne'
      · intro a _
        exact Nat.mul_div_cancel_left a hp0
      · intro a ha
        obtain ⟨_, hpa⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
        exact Nat.mul_div_cancel' hpa
      · intro a _
        rw [Nat.mul_div_cancel_left a hp0, Nat.div_div_eq_div_mul]
    · symm
      refine Finset.sum_eq_zero fun a ha => ?_
      obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp ha
      exact absurd (hpa.trans (Nat.dvd_of_mem_divisors ha)) hpm
  rw [h2, hL1, hR1, hR2]
  ring

end VOA.Moonshine.ConwayNorton.M8
