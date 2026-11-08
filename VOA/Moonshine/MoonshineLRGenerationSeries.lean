import VOA.Moonshine.MoonshineLRGenerationCount

/-!
# The PBW count is the product `Π (1 − e^γ)^{−d(γ)}`

With `N(Γ)` the number of exponent vectors of weight `Γ` (`MoonshineLRGenerationCount`) and
`d(γ)` the number of basis vectors of degree `γ`, the generating series
`Σ_{a,b} N(a,b) pᵃ q^b` (`expSeries`) equals `coneProd (fun m n => −d(m,n))`
(`expSeries_eq_coneProd`). Proof: both solve `p A′ = A · coneLog (−d)` with constant term `1`.
The coefficient identity is `count_recursion`, regrouped by degree (`expCount_coeff_identity`).

This step does not use any Lie theory.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open Finset

/-! ### Two summation lemmas -/

/-- An indicator on the antidiagonal picks one term. -/
theorem sum_antidiagonal_ite_snd (a j₀ : ℕ) (g : ℕ → ℂ) :
    ∑ x ∈ Finset.antidiagonal a, (if x.2 = j₀ then g x.1 else 0) =
      if j₀ ≤ a then g (a - j₀) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (a - j₀, j₀)]
    · simp
    · intro x hx hne
      rw [if_neg]
      intro hx2
      apply hne
      rw [Finset.mem_antidiagonal] at hx
      ext <;> simp <;> omega
    · intro hn
      exact absurd (Finset.mem_antidiagonal.mpr (by simp; omega)) hn
  · refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [if_neg (by omega)]

/-- For a degree `(mᵢ, nᵢ)` in the open cone, the divisor sum of `coneLog` sees exactly the
multiples `k • (mᵢ, nᵢ)`. -/
theorem sum_divisors_ite_eq_sum_Icc {mi ni j v A : ℕ} (hmi : 1 ≤ mi) (hni : 1 ≤ ni)
    (hjA : j ≤ A) :
    ∑ m ∈ j.divisors, (if j / m ∣ v ∧ v ≠ 0 ∧ (mi, ni) = (m, v / (j / m)) then (m : ℂ) else 0) =
      ∑ k ∈ Finset.Icc 1 A, (if (j, v) = k • (mi, ni) then (mi : ℂ) else 0) := by
  by_cases hex : ∃ k, 1 ≤ k ∧ j = k * mi ∧ v = k * ni
  · obtain ⟨k, hk1, hj, hv⟩ := hex
    have hkpos : 0 < k := hk1
    have hjm : j / mi = k := by rw [hj, Nat.mul_div_cancel _ (by omega : 0 < mi)]
    have hcondL : j / mi ∣ v ∧ v ≠ 0 ∧ (mi, ni) = (mi, v / (j / mi)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hjm, hv]
        exact dvd_mul_right k ni
      · rw [hv]
        positivity
      · rw [hjm, hv, Nat.mul_div_cancel_left _ hkpos]
    have hcondR : (j, v) = k • (mi, ni) := by
      rw [Prod.smul_mk, hj, hv, smul_eq_mul, smul_eq_mul]
    rw [Finset.sum_eq_single mi, Finset.sum_eq_single k]
    · rw [if_pos hcondL, if_pos hcondR]
    · intro k' _ hne
      rw [if_neg]
      intro h
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h
      apply hne
      have : k' * mi = k * mi := by rw [← h.1, hj]
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    · intro hn
      exact absurd (Finset.mem_Icc.mpr ⟨hk1, by
        have : k ≤ k * mi := Nat.le_mul_of_pos_right _ (by omega)
        omega⟩) hn
    · intro m _ hne
      rw [if_neg]
      rintro ⟨_, _, h⟩
      exact hne (Prod.mk.inj h).1.symm
    · intro hn
      exact absurd (Nat.mem_divisors.mpr ⟨by rw [hj]; exact dvd_mul_left mi k, by
        rw [hj]; positivity⟩) hn
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro k hk
      rw [if_neg]
      intro h
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h
      exact hex ⟨k, (Finset.mem_Icc.mp hk).1, h.1, h.2⟩
    · intro m hm
      rw [if_neg]
      rintro ⟨hdvd, hv0, h⟩
      obtain ⟨rfl, hn⟩ := Prod.mk.inj h
      have hmj := Nat.dvd_of_mem_divisors hm
      apply hex
      refine ⟨j / mi, ?_, (Nat.div_mul_cancel hmj).symm, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_mem_divisors hm |>.trans_le
          (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2) hmj)) hmj)
          (by omega) |>.trans_le le_rfl
      · rw [hn]
        exact (Nat.mul_div_cancel' hdvd).symm

/-- The two-variable antidiagonal indicator. -/
theorem sum_antidiagonal_ite_two (a b j₀ v₀ : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ x ∈ Finset.antidiagonal a, ∑ y ∈ Finset.antidiagonal b,
        (if (x.2, y.2) = (j₀, v₀) then F x.1 y.1 else 0) =
      if j₀ ≤ a ∧ v₀ ≤ b then F (a - j₀) (b - v₀) else 0 := by
  have h : ∀ x : ℕ × ℕ, ∑ y ∈ Finset.antidiagonal b,
      (if (x.2, y.2) = (j₀, v₀) then F x.1 y.1 else 0) =
        if x.2 = j₀ then (if v₀ ≤ b then F x.1 (b - v₀) else 0) else 0 := by
    intro x
    by_cases hx : x.2 = j₀
    · rw [if_pos hx, ← sum_antidiagonal_ite_snd b v₀ (F x.1)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [hx]
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg]
      intro h
      exact hx (Prod.mk.inj h).1
  simp_rw [h]
  rw [sum_antidiagonal_ite_snd a j₀ (fun s => if v₀ ≤ b then F s (b - v₀) else 0)]
  by_cases h1 : j₀ ≤ a <;> by_cases h2 : v₀ ≤ b <;> simp [h1, h2]

variable {ι : Type*} (deg : ι → ℕ × ℕ) (hdeg : ∀ i, 1 ≤ (deg i).1 ∧ 1 ≤ (deg i).2)
variable (low : (ℕ × ℕ) → Finset ι) (hlow : ∀ Γ i, i ∈ low Γ ↔ deg i ≤ Γ)

/-- `d(γ)`: the number of basis vectors of degree `γ`. -/
noncomputable def basisDegCount (γ : ℕ × ℕ) : ℕ := by
  classical
  exact ((low γ).filter fun i => deg i = γ).card

include hlow in
theorem basisDegCount_eq_card_filter {γ Γ : ℕ × ℕ} (hγ : γ ≤ Γ) :
    basisDegCount deg low γ = ((low Γ).filter fun i => deg i = γ).card := by
  classical
  unfold basisDegCount
  congr 1
  ext i
  simp only [Finset.mem_filter, hlow]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨h ▸ hγ, h⟩
  · rintro ⟨_, h⟩
    exact ⟨h ▸ le_rfl, h⟩

/-- `ℓ(j, v)`, the `p^j q^v`-coefficient of `coneLog (−d)`. -/
noncomputable def logCountCoeff (j v : ℕ) : ℂ :=
  ∑ m ∈ j.divisors,
    if j / m ∣ v ∧ v ≠ 0 then (m : ℂ) * basisDegCount deg low (m, v / (j / m)) else 0

include hdeg hlow in
/-- **The coefficient identity:**
`a · N(a,b) = Σ_{s+j=a} Σ_{u+v=b} N(s,u) · ℓ(j,v)`. -/
theorem expCount_coeff_identity (a b : ℕ) :
    (a : ℂ) * expCount deg low (a, b) =
      ∑ x ∈ Finset.antidiagonal a, ∑ y ∈ Finset.antidiagonal b,
        (expCount deg low (x.1, y.1) : ℂ) * logCountCoeff deg low x.2 y.2 := by
  classical
  have hrec := count_recursion deg hdeg low hlow (a, b)
  have hrecC : (a : ℂ) * expCount deg low (a, b) =
      ∑ i ∈ low (a, b), ∑ k ∈ Finset.Icc 1 a,
        if k • deg i ≤ (a, b) then
          ((deg i).1 : ℂ) * expCount deg low ((a, b) - k • deg i) else 0 := by
    have := congrArg (fun n : ℕ => (n : ℂ)) hrec
    simpa [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul] using this
  rw [hrecC]
  -- each recursion term as a double antidiagonal indicator
  have hterm : ∀ i ∈ low (a, b), ∀ k ∈ Finset.Icc 1 a,
      (if k • deg i ≤ (a, b) then
          ((deg i).1 : ℂ) * expCount deg low ((a, b) - k • deg i) else 0) =
        ∑ x ∈ Finset.antidiagonal a, ∑ y ∈ Finset.antidiagonal b,
          (if (x.2, y.2) = k • deg i then
            (expCount deg low (x.1, y.1) : ℂ) * ((deg i).1 : ℂ) else 0) := by
    intro i _ k _
    rw [show k • deg i = ((k • deg i).1, (k • deg i).2) from rfl,
      sum_antidiagonal_ite_two a b _ _
        (fun s u => (expCount deg low (s, u) : ℂ) * ((deg i).1 : ℂ))]
    have hle : k • deg i ≤ (a, b) ↔ (k • deg i).1 ≤ a ∧ (k • deg i).2 ≤ b := Prod.le_def
    by_cases h : k • deg i ≤ (a, b)
    · rw [if_pos h, if_pos (hle.mp h), mul_comm]
      rfl
    · rw [if_neg h, if_neg (fun h' => h (hle.mpr h'))]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => hterm i hi k hk]
  -- swap to put the antidiagonals outside
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.Icc 1 a)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  -- now: Σ_i Σ_k [ (x.2,y.2) = k • deg i ] N(x.1,y.1) mᵢ = N(x.1,y.1) ℓ(x.2,y.2)
  have hxa : x.2 ≤ a := by rw [Finset.mem_antidiagonal] at hx; omega
  have hyb : y.2 ≤ b := by rw [Finset.mem_antidiagonal] at hy; omega
  have hinner : ∀ i ∈ low (a, b),
      ∑ k ∈ Finset.Icc 1 a, (if (x.2, y.2) = k • deg i then
        (expCount deg low (x.1, y.1) : ℂ) * ((deg i).1 : ℂ) else 0) =
        (expCount deg low (x.1, y.1) : ℂ) *
          ∑ m ∈ x.2.divisors, (if x.2 / m ∣ y.2 ∧ y.2 ≠ 0 ∧ deg i = (m, y.2 / (x.2 / m))
            then (m : ℂ) else 0) := by
    intro i _
    have hdi := hdeg i
    have h := sum_divisors_ite_eq_sum_Icc (v := y.2) (A := a) hdi.1 hdi.2 hxa
    rw [show ((deg i).1, (deg i).2) = deg i from rfl] at h
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, logCountCoeff, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  by_cases hc : x.2 / m ∣ y.2 ∧ y.2 ≠ 0
  · rw [if_pos hc]
    have hmle : m ≤ a := (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2)
      (Nat.dvd_of_mem_divisors hm)).trans hxa
    have hvle : y.2 / (x.2 / m) ≤ b := (Nat.div_le_self _ _).trans hyb
    rw [basisDegCount_eq_card_filter deg low hlow (Γ := (a, b)) (Prod.le_def.mpr ⟨hmle, hvle⟩)]
    have hfilt : ((low (a, b)).filter fun i =>
        x.2 / m ∣ y.2 ∧ y.2 ≠ 0 ∧ deg i = (m, y.2 / (x.2 / m))) =
          (low (a, b)).filter fun i => deg i = (m, y.2 / (x.2 / m)) := by
      ext i
      simp only [Finset.mem_filter]
      tauto
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hfilt]
    ring
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2, _⟩
    exact hc ⟨h1, h2⟩

/-! ### The generating series -/

include hdeg hlow in
/-- Only the zero exponent vector has `p`-weight `0`. -/
theorem expCount_zero_fst (b : ℕ) : expCount deg low (0, b) = if b = 0 then 1 else 0 := by
  classical
  have hset : expVectors deg low (0, b) = if b = 0 then {0} else ∅ := by
    ext f
    rw [mem_expVectors deg hdeg low hlow]
    constructor
    · intro hw
      have hf : f = 0 := by
        ext i
        by_contra hi
        have h1 := (smul_deg_le_expWeight deg f i).1
        rw [hw] at h1
        simp only [Prod.smul_fst, smul_eq_mul, nonpos_iff_eq_zero, mul_eq_zero] at h1
        rcases h1 with h1 | h1
        · exact hi h1
        · have := (hdeg i).1
          omega
      subst hf
      have h0 : expWeight deg (0 : ι →₀ ℕ) = 0 := Finsupp.sum_zero_index
      rw [h0] at hw
      have hb : b = 0 := (Prod.mk.inj hw.symm).2
      simp [hb]
    · intro hf
      split_ifs at hf with hb
      · rw [Finset.mem_singleton] at hf
        subst hf hb
        exact Finsupp.sum_zero_index
      · simp at hf
  rw [expCount, hset]
  split_ifs <;> simp

/-- `Σ_{a,b} N(a,b) pᵃ q^b`. -/
noncomputable def expSeries : PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.mk fun a => HahnSeries.ofPowerSeries ℤ ℂ
    (PowerSeries.mk fun b => (expCount deg low (a, b) : ℂ))

theorem coneLogCoeff_neg_basisDegCount (j : ℕ) :
    coneLogCoeff (fun m n => -(basisDegCount deg low (m, n) : ℂ)) j =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun v => logCountCoeff deg low j v) := by
  rw [coneLogCoeff, ← map_neg]
  congr 1
  refine PowerSeries.ext fun v => ?_
  simp only [PowerSeries.coeff_mk, map_neg, logCountCoeff]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

include hdeg hlow in
/-- **The PBW count is the product:**
`Σ_{a,b} N(a,b) pᵃ q^b = Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−d(m,n)}`. -/
theorem expSeries_eq_coneProd :
    expSeries deg low = coneProd (fun m n => -(basisDegCount deg low (m, n) : ℂ)) := by
  refine eq_of_ode (constantCoeff_coneLog _) ?_ (coneProd_spec _) ?_
  · refine PowerSeries.ext fun a => ?_
    rcases a with _ | a
    · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        constantCoeff_coneLog, mul_zero]
    · rw [coeff_succ_X_mul_derivative, PowerSeries.coeff_mul]
      simp only [expSeries, coneLog, PowerSeries.coeff_mk]
      simp_rw [coneLogCoeff_neg_basisDegCount, ← map_mul, ← map_sum]
      rw [show (((a + 1 : ℕ) : LaurentSeries ℂ)) = HahnSeries.ofPowerSeries ℤ ℂ
          (PowerSeries.C ((a + 1 : ℕ) : ℂ)) by rw [HahnSeries.ofPowerSeries_C]; rfl, ← map_mul]
      congr 1
      refine PowerSeries.ext fun b => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_sum]
      rw [expCount_coeff_identity deg hdeg low hlow (a + 1) b]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_mk]
  · rw [constantCoeff_coneProd, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, expSeries,
      PowerSeries.coeff_mk]
    have : (PowerSeries.mk fun b => (expCount deg low (0, b) : ℂ)) = 1 := by
      refine PowerSeries.ext fun b => ?_
      rw [PowerSeries.coeff_mk, expCount_zero_fst deg hdeg low hlow, PowerSeries.coeff_one]
      split_ifs <;> simp
    rw [this, map_one]

end VOA.Moonshine.ConwayNorton.M8
