import VOA.Moonshine.MoonshineLRM5KNZ
import VOA.Moonshine.MoonshineLRM5Ode

/-!
# The product identity

In `ℂ((q))[[p]]` (`p` outer):
* `coneLog e = −Σ_{k,m,n ≥ 1} m e(m,n) p^{mk} q^{nk}`, the logarithmic derivative `p ∂_p log` of
  `Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{e(m,n)}`;
* `coneProd e = odeSol (coneLog e)`: the product `Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{e(m,n)}`, defined as the
  solution of `p A′ = A · coneLog e` with constant term `1`;
* `coneProd_add`: `coneProd (e₁ + e₂) = coneProd e₁ · coneProd e₂`;
* `coneProd_exponent_unique`: the exponents are determined by the product;
* **`knz_product`**: `Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{c(mn)} = 1 − Σ_{a,b ≥ 1} c(a+b−1) pᵃ q^b` for the
  coefficients `c` of `J` (the KNZ identity in `Notes/moonshine/MOON_BKM.md`). The proof is
  `knz_log_J` plus uniqueness for `p A′ = A L`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

instance charZero_laurentSeries : CharZero (LaurentSeries ℂ) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (LaurentSeries ℂ)).injective

theorem ofPowerSeries_mk_zero :
    HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun _ : ℕ => (0 : ℂ)) = 0 := by
  rw [show (PowerSeries.mk fun _ : ℕ => (0 : ℂ)) = 0 from PowerSeries.ext fun _ => by simp,
    map_zero]

/-- The `p^a`-coefficient of `coneLog e`: `−Σ_{m ∣ a} Σ_{n ≥ 1} m e(m,n) q^{n·(a/m)}`. -/
noncomputable def coneLogCoeff (e : ℕ → ℕ → ℂ) (a : ℕ) : LaurentSeries ℂ :=
  -HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun b =>
    ∑ m ∈ a.divisors, if a / m ∣ b ∧ b ≠ 0 then (m : ℂ) * e m (b / (a / m)) else 0)

/-- `coneLog e = −Σ_{k,m,n ≥ 1} m e(m,n) p^{mk} q^{nk}`. -/
noncomputable def coneLog (e : ℕ → ℕ → ℂ) : PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.mk (coneLogCoeff e)

theorem constantCoeff_coneLog (e : ℕ → ℕ → ℂ) : PowerSeries.constantCoeff (coneLog e) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coneLog, PowerSeries.coeff_mk, coneLogCoeff]
  simp [ofPowerSeries_mk_zero]

/-- **The product** `Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{e(m,n)}`, defined by its logarithmic derivative. -/
noncomputable def coneProd (e : ℕ → ℕ → ℂ) : PowerSeries (LaurentSeries ℂ) :=
  odeSol (coneLog e)

theorem coneProd_spec (e : ℕ → ℕ → ℂ) :
    PowerSeries.X * PowerSeries.derivative (LaurentSeries ℂ) (coneProd e) =
      coneProd e * coneLog e :=
  odeSol_spec _ (constantCoeff_coneLog e)

theorem constantCoeff_coneProd (e : ℕ → ℕ → ℂ) : PowerSeries.constantCoeff (coneProd e) = 1 :=
  constantCoeff_odeSol _

theorem coneLog_add (e₁ e₂ : ℕ → ℕ → ℂ) : coneLog (e₁ + e₂) = coneLog e₁ + coneLog e₂ := by
  ext a n
  simp only [coneLog, coneLogCoeff, PowerSeries.coeff_mk, map_add, HahnSeries.coeff_add,
    HahnSeries.coeff_neg, coeff_ofPowerSeries_mk, Pi.add_apply]
  split_ifs
  · simp
  · rw [← neg_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring

/-- **Multiplicativity in the exponents.** -/
theorem coneProd_add (e₁ e₂ : ℕ → ℕ → ℂ) : coneProd (e₁ + e₂) = coneProd e₁ * coneProd e₂ := by
  rw [coneProd, coneLog_add, odeSol_add _ _ (constantCoeff_coneLog e₁) (constantCoeff_coneLog e₂)]
  rfl

/-- For `J`, `coneLog (c(m n))` is `−E`, the series of `knz_log_J`. -/
theorem coneLog_cJ :
    coneLog (fun m n => cJ (m * n)) = -(PowerSeries.mk fun M => if M = 0 then 0 else
      HahnSeries.ofPowerSeries ℤ ℂ
        (PowerSeries.mk fun r => if r = 0 then 0 else qHeckeCoeff cJ M r)) := by
  refine PowerSeries.ext fun M => ?_
  rw [map_neg, coneLog, PowerSeries.coeff_mk, PowerSeries.coeff_mk, coneLogCoeff]
  by_cases hM : M = 0
  · subst hM
    rw [if_pos rfl]
    simp [ofPowerSeries_mk_zero]
  rw [if_neg hM, neg_inj]
  congr 1
  refine PowerSeries.ext fun r => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hr : r = 0
  · subst hr
    simp
  rw [if_neg hr, qHeckeCoeff]
  have hset : (Nat.gcd M r).divisors = M.divisors.filter (fun a => a ∣ r) := by
    ext a
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨⟨h1, hM⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left r (Nat.pos_of_ne_zero hM)).ne'⟩
  rw [hset, Finset.sum_filter, ← Nat.sum_div_divisors M]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmM : m ∣ M := Nat.dvd_of_mem_divisors hm
  have hmpos : 0 < m := Nat.pos_of_mem_divisors hm
  have hk : M / m ∣ M := Nat.div_dvd_of_dvd hmM
  have hkpos : 0 < M / m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hmM) hmpos
  rw [Nat.div_div_self hmM hM]
  split_ifs with h1 h2 h2
  · congr 2
    exact Nat.div_mul_div_comm hmM h2
  · exact absurd h1.1 h2
  · exact absurd ⟨h2, hr⟩ h1
  · rfl

/-- **The product identity (KNZ).** For the coefficients `c` of `J`, in `ℂ((q))[[p]]`:
`Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{c(mn)} = 1 − Σ_{a,b ≥ 1} c(a+b−1) pᵃ q^b`. -/
theorem knz_product : coneProd (fun m n => cJ (m * n)) = knzSeries cJ := by
  refine eq_of_ode (constantCoeff_coneLog _) (coneProd_spec _) ?_ ?_
  · rw [knz_log_J, coneLog_cJ, mul_neg]
  · rw [constantCoeff_coneProd, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, knzSeries,
      PowerSeries.coeff_mk, knzCoeff, if_pos rfl]

/-! ### Exponents are determined by the product -/

/-- Equal products have equal logarithmic derivatives. -/
theorem coneLog_eq_of_coneProd_eq {e₁ e₂ : ℕ → ℕ → ℂ} (h : coneProd e₁ = coneProd e₂) :
    coneLog e₁ = coneLog e₂ := by
  have h1 := coneProd_spec e₁
  have h2 := coneProd_spec e₂
  rw [h] at h1
  have hne : coneProd e₂ ≠ 0 := by
    intro h0
    have := constantCoeff_coneProd e₂
    rw [h0, map_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (h1.symm.trans h2)

/-- The `pᵐ qⁿ`-coefficient of the logarithmic derivative (`n ≥ 1`). -/
theorem coeff_coneLog (e : ℕ → ℕ → ℂ) (m n : ℕ) :
    (PowerSeries.coeff m (coneLog e)).coeff (n : ℤ) =
      -∑ m' ∈ m.divisors, if m / m' ∣ n ∧ n ≠ 0 then (m' : ℂ) * e m' (n / (m / m')) else 0 := by
  rw [coneLog, PowerSeries.coeff_mk, coneLogCoeff, HahnSeries.coeff_neg, coeff_ofPowerSeries_mk,
    if_neg (by omega), Int.natAbs_natCast]

/-- **Exponent uniqueness** (blueprint: the product argument in `Notes/moonshine/MOON_BKM.md`): if
`Π (1 − pᵐ qⁿ)^{e₁(m,n)} = Π (1 − pᵐ qⁿ)^{e₂(m,n)}`, then `e₁ = e₂` on `m, n ≥ 1`. -/
theorem coneProd_exponent_unique {e₁ e₂ : ℕ → ℕ → ℂ} (h : coneProd e₁ = coneProd e₂) :
    ∀ m n : ℕ, 0 < m → 0 < n → e₁ m n = e₂ m n := by
  have hlog := coneLog_eq_of_coneProd_eq h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hm hn
    have hc := congrArg (fun L => (PowerSeries.coeff m L).coeff (n : ℤ)) hlog
    simp only [coeff_coneLog, neg_inj] at hc
    rw [← Finset.add_sum_erase _ _ (Nat.mem_divisors_self m hm.ne'),
      ← Finset.add_sum_erase _ _ (Nat.mem_divisors_self m hm.ne'), Nat.div_self hm,
      Nat.div_one, if_pos ⟨one_dvd n, hn.ne'⟩, if_pos ⟨one_dvd n, hn.ne'⟩] at hc
    have hrest : ∑ m' ∈ m.divisors.erase m,
        (if m / m' ∣ n ∧ n ≠ 0 then (m' : ℂ) * e₁ m' (n / (m / m')) else 0) =
        ∑ m' ∈ m.divisors.erase m,
        (if m / m' ∣ n ∧ n ≠ 0 then (m' : ℂ) * e₂ m' (n / (m / m')) else 0) := by
      refine Finset.sum_congr rfl fun m' hm' => ?_
      obtain ⟨hne, hdiv⟩ := Finset.mem_erase.mp hm'
      have hm'dvd := Nat.dvd_of_mem_divisors hdiv
      have hm'pos := Nat.pos_of_mem_divisors hdiv
      have hlt : m' < m := lt_of_le_of_ne (Nat.le_of_dvd hm hm'dvd) hne
      split_ifs with hcond
      · have hq : 0 < m / m' := Nat.div_pos (Nat.le_of_dvd hm hm'dvd) hm'pos
        have hpos : 0 < n / (m / m') := Nat.div_pos (Nat.le_of_dvd hn hcond.1) hq
        rw [ih m' hlt _ hm'pos hpos]
      · rfl
    rw [hrest, add_left_inj] at hc
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    exact mul_left_cancel₀ hm0 hc

end VOA.Moonshine.ConwayNorton.M8
