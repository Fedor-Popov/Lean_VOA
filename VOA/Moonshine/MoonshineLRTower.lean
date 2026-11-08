import VOA.Moonshine.MoonshineCNStatement
import VOA.Moonshine.MoonshineLRJUnbounded

/-!
# The tower down to `J`

For a replicable family, the `q^r`-coefficient (`r ≥ 1`) of the Faber remainder
`F_{k,m}(f_k) − q^{−m}` is, by the replication formula,
`faberRemainderCoeff c k m r = Σ_{a ∣ gcd(m,r)} (m/a) · c_{ka}(m r / a²)`
(blueprint: the Faber coefficient and non-injectivity arguments in
`Notes/moonshine/MOON_ROUTE.md` and `MOON_M8_LEAN.md`).

* `bounded_replicate_of_bounded_faberRemainderCoeff`: if, for every `m ≥ 1`, these coefficients are
  bounded in `r ≥ 1`, then every replicate sequence `ℓ ↦ c_{km}(ℓ)` (`ℓ ≥ 1`) is bounded.
  Induction on `m` along `r = mℓ`: the `a = m` term is `c_{km}(ℓ)`, and every other term involves a
  smaller replicate `a ∣ m`, `a < m`.
* `not_bounded_faberRemainderCoeff`: for a `ReplicableFamily N` with `0 < N`, the coefficients
  cannot all be bounded, because the replicate `kN` is `J` itself and `J`'s coefficients are
  unbounded (`JShift_coeff_unbounded`).

The analytic argument (injectivity of `f_k` modulo `ℤ` makes these coefficients bounded) is
separate.
-/

namespace VOA.Moonshine.ConwayNorton.M8

/-- The `q^r`-coefficient of the Faber remainder `F_{k,m}(f_k) − q^{−m}` given by the replication
formula: `Σ_{a ∣ gcd(m,r)} (m/a) · c_{ka}(m r / a²)`. -/
noncomputable def faberRemainderCoeff (c : ℕ → ℕ → ℂ) (k m r : ℕ) : ℂ :=
  ∑ a ∈ (Nat.gcd m r).divisors, ((m / a : ℕ) : ℂ) * c (k * a) (m * r / (a * a))

/-- At `r = mℓ` the remainder coefficient is `c_{km}(ℓ)` plus terms of smaller replicates. -/
theorem faberRemainderCoeff_mul_self (c : ℕ → ℕ → ℂ) (k : ℕ) {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) :
    faberRemainderCoeff c k m (m * ℓ) =
      c (k * m) ℓ + ∑ a ∈ m.divisors.erase m,
        ((m / a : ℕ) : ℂ) * c (k * a) (m * (m * ℓ) / (a * a)) := by
  rw [faberRemainderCoeff, Nat.gcd_eq_left (dvd_mul_right m ℓ),
    ← Finset.add_sum_erase _ _ (Nat.mem_divisors_self m (by omega))]
  congr 1
  have hm0 : 0 < m := by omega
  rw [Nat.div_self hm0, Nat.cast_one, one_mul,
    show m * (m * ℓ) = ℓ * (m * m) by ring, Nat.mul_div_cancel _ (Nat.mul_pos hm0 hm0)]

/-- **The tower.** Bounded Faber-remainder coefficients for every `m ≥ 1` force every replicate
sequence `ℓ ↦ c_{km}(ℓ)` (`ℓ ≥ 1`, `m ≥ 1`) to be bounded. -/
theorem bounded_replicate_of_bounded_faberRemainderCoeff (c : ℕ → ℕ → ℂ) (k : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → ∃ M : ℝ, ∀ r : ℕ, 1 ≤ r → ‖faberRemainderCoeff c k m r‖ ≤ M) :
    ∀ m : ℕ, 1 ≤ m → ∃ M : ℝ, ∀ ℓ : ℕ, 1 ≤ ℓ → ‖c (k * m) ℓ‖ ≤ M := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    choose! Mf hMf using ih
    obtain ⟨M0, hM0⟩ := h m hm
    refine ⟨M0 + ∑ a ∈ m.divisors.erase m, ((m / a : ℕ) : ℝ) * Mf a, fun ℓ hℓ => ?_⟩
    have hrel := faberRemainderCoeff_mul_self c k hm ℓ
    have heq : c (k * m) ℓ = faberRemainderCoeff c k m (m * ℓ) -
        ∑ a ∈ m.divisors.erase m, ((m / a : ℕ) : ℂ) * c (k * a) (m * (m * ℓ) / (a * a)) := by
      rw [hrel]
      ring
    rw [heq]
    refine (norm_sub_le _ _).trans (add_le_add (hM0 _ (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)))) ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
    have ha' := Finset.mem_erase.mp ha
    have hadvd : a ∣ m := Nat.dvd_of_mem_divisors ha'.2
    have hapos : 0 < a := Nat.pos_of_mem_divisors ha'.2
    have halt : a < m := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hadvd) ha'.1
    have harg : 1 ≤ m * (m * ℓ) / (a * a) := by
      apply Nat.div_pos _ (Nat.mul_pos hapos hapos)
      have h1 : a * a ≤ m * m := Nat.mul_le_mul halt.le halt.le
      have h2 : m * m ≤ m * (m * ℓ) := Nat.mul_le_mul_left m (Nat.le_mul_of_pos_right m hℓ)
      omega
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hMf a halt hapos _ harg) (Nat.cast_nonneg _)

/-- The replicate `kN` of a family of period `N` is the replicate `0`, i.e. `J`. -/
theorem ReplicableFamily_c_mul_period {N : ℕ} (F : ReplicableFamily N) (k : ℕ) :
    F.c (k * N) = F.c 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    funext n
    rw [Nat.succ_mul, F.periodic, ih]

/-- **Unbounded Faber remainder coefficients.** For a replicable family of positive period, the
Faber remainder coefficients `Σ_{a ∣ gcd(m,r)} (m/a) c_{ka}(mr/a²)` are not bounded in `r` for every
`m ≥ 1`. -/
theorem not_bounded_faberRemainderCoeff {N : ℕ} (hN : 0 < N) (F : ReplicableFamily N) (k : ℕ) :
    ¬ ∀ m : ℕ, 1 ≤ m → ∃ M : ℝ, ∀ r : ℕ, 1 ≤ r → ‖faberRemainderCoeff F.c k m r‖ ≤ M := by
  intro h
  obtain ⟨M, hM⟩ := bounded_replicate_of_bounded_faberRemainderCoeff F.c k h N hN
  rw [ReplicableFamily_c_mul_period] at hM
  apply JShift_coeff_unbounded
  refine ⟨max M (max ‖PowerSeries.coeff 0 JShift‖ ‖PowerSeries.coeff 1 JShift‖), fun n => ?_⟩
  rcases n with _ | _ | n
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · have := hM (n + 1) (by omega)
    rw [F.zero_eq_J] at this
    exact this.trans (le_max_left _ _)

end VOA.Moonshine.ConwayNorton.M8
