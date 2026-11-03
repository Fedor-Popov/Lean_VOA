/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDEHeatK
import VOA.DeligneAudit.DeligneMLDEProduct

/-!
# The heat equation at a cube root of unity: level-three Lambert identities

Over `K⟦x⟧` (`K` a field of characteristic zero) the identity (*) of `DeligneMLDEHeatK` holds for
`u = ω eˣ`.  Taking `K = ℂ`, `ω` a primitive cube root of unity, the order `x⁰` coefficient gives,
after cancelling `1 - ω`, the level-three identity (`level3_l0`)

  `3 L₀² + L₀ = P₁(q) - 3 P₁(q³)`,     i.e.   `(1 + 6L₀)² = 1 + 12 P₁(q) - 36 P₁(q³)`,

with `L₀ = ∑_{dk=n} χ₋₃(k) qⁿ` (so `[qⁿ]L₀ = d_{1,3}(n) - d_{2,3}(n)`).  With the Lambert form
`θ_{A₂} = 1 + 6L₀` this is `l2 : 2a² = 3E₂(q³) - E₂(q)` of `G2Level3Core`.
-/

namespace VOA.DeligneAudit.DeligneMLDE.HeatK

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

local notation "A" => (PowerSeries K)
local notation "dx" => PowerSeries.derivative K

/-! ## Extracting `x`-coefficients over `K` -/

/-- `π_j`. -/
def pjK (j : ℕ) (F : PowerSeries A) : PowerSeries K := PowerSeries.mk fun n => coeff j (coeff n F)

@[simp] theorem coeff_pjK (j n : ℕ) (F : PowerSeries A) :
    coeff n (pjK j F) = coeff j (coeff n F) := by simp [pjK]

theorem pjK_add (j : ℕ) (F G : PowerSeries A) : pjK j (F + G) = pjK j F + pjK j G := by
  refine PowerSeries.ext fun n => ?_; simp

theorem pjK_sub (j : ℕ) (F G : PowerSeries A) : pjK j (F - G) = pjK j F - pjK j G := by
  refine PowerSeries.ext fun n => ?_; simp

theorem pjK_mul (j : ℕ) (F G : PowerSeries A) :
    pjK j (F * G) = ∑ p ∈ Finset.antidiagonal j, pjK p.1 F * pjK p.2 G := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_pjK, coeff_mul, map_sum]
  rw [Finset.sum_comm]

theorem pjK_C (j : ℕ) (a : A) : pjK j (PowerSeries.C a) = PowerSeries.C (coeff j a) := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_pjK, coeff_C]; split_ifs <;> simp

theorem pjK_one (j : ℕ) : pjK j (1 : PowerSeries A) = PowerSeries.C (if j = 0 then 1 else 0) := by
  rw [← map_one (PowerSeries.C (R := A)), pjK_C, coeff_one]

theorem pjK_liftD (j : ℕ) (F : PowerSeries A) :
    pjK j (liftD F) = PowerSeries.C ((j : K) + 1) * pjK (j + 1) F := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_pjK, coeff_liftD, coeff_derivative, coeff_C_mul]
  ring

theorem star_pjK (w : (PowerSeries K)ˣ) (hw : dx (w : A) = w) (j : ℕ) :
    ∑ p ∈ Finset.antidiagonal j, (pjK p.1 1 - pjK p.1 (PowerSeries.C (w : A))) *
        (PowerSeries.C ((p.2 : K) + 1) * pjK (p.2 + 1) (Rser w)
          + ∑ q ∈ Finset.antidiagonal p.2, pjK q.1 (Rser w) * pjK q.2 (Rser w)
          - (pjK p.2 (Tser w) + pjK p.2 (Tser w)))
      = ∑ p ∈ Finset.antidiagonal j, (pjK p.1 1 + pjK p.1 (PowerSeries.C (w : A))) * pjK p.2 (Rser w) := by
  have h := congrArg (pjK j) (star_identity w hw)
  rw [two_mul, sq] at h
  simpa only [pjK_mul, pjK_add, pjK_sub, pjK_liftD] using h

/-- Lambert series over `K`. -/
def lamK (F : ℕ → ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ m ∈ Finset.range n, if (m + 1) ∣ n then F (m + 1) (n / (m + 1)) else 0

/-! ## Powers of `u = ω eˣ` -/

variable (ω : K) (hω : ω ≠ 0)

theorem coeff_uW_pow (j k : ℕ) :
    coeff j (((uW ω hω : (PowerSeries K)ˣ) : A) ^ k) = ω ^ k * ((k : K) ^ j / (j.factorial : K)) := by
  change coeff j ((ω • exp K) ^ k) = _
  rw [smul_pow, exp_pow_eq_rescale_exp, coeff_smul, coeff_rescale, coeff_exp, smul_eq_mul]
  simp only [map_div₀, map_one, map_natCast]
  ring

theorem coeff_uW_inv_pow (j k : ℕ) :
    coeff j (((uW ω hω)⁻¹ : (PowerSeries K)ˣ) ^ k : A)
      = ω⁻¹ ^ k * ((-(k : K)) ^ j / (j.factorial : K)) := by
  change coeff j ((ω⁻¹ • evalNegHom (exp K)) ^ k) = _
  rw [smul_pow, evalNegHom, ← map_pow, exp_pow_eq_rescale_exp, coeff_smul, coeff_rescale,
    coeff_rescale, coeff_exp, smul_eq_mul]
  simp only [map_div₀, map_one, map_natCast]
  rw [neg_pow]
  ring

theorem coeff_uW (j : ℕ) : coeff j ((uW ω hω : (PowerSeries K)ˣ) : A) = ω / (j.factorial : K) := by
  have := coeff_uW_pow ω hω j 1
  rw [pow_one, pow_one, Nat.cast_one, one_pow] at this
  rw [this, mul_one_div]

theorem pjK_R (j : ℕ) :
    pjK j (Rser (uW ω hω)) =
      lamK (fun _ k => ω⁻¹ ^ k * ((-(k : K)) ^ j / (j.factorial : K))
        - ω ^ k * ((k : K) ^ j / (j.factorial : K))) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_pjK, Rser, tailSum, coeff_mk, map_sum, map_sum, lamK, coeff_mk]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [rho, map_sub, coeff_gs, coeff_gs]
  split_ifs with h1 h2 h3
  · rw [map_sub, coeff_uW_inv_pow, coeff_uW_pow]
  · exact absurd h1.2 h2
  · exact absurd ⟨by omega, h3⟩ h1
  · simp

theorem pjK_T (j : ℕ) :
    pjK j (Tser (uW ω hω)) =
      lamK (fun d k => -(d : K) * (ω ^ k * ((k : K) ^ j / (j.factorial : K))
        + ω⁻¹ ^ k * ((-(k : K)) ^ j / (j.factorial : K)) + if j = 0 then 1 else 0)) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_pjK, Tser, tailSum, coeff_mk, map_sum, map_sum, lamK, coeff_mk]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [tau, neg_mul, map_neg, coeff_C_mul, map_add, map_add, coeff_gs, coeff_gs, coeff_gs]
  have hd : ∀ y : A, coeff j ((((m + 1 : ℕ) : A)) * y) = ((m + 1 : ℕ) : K) * coeff j y := by
    intro y; rw [← map_natCast (PowerSeries.C (R := K)), PowerSeries.coeff_C_mul]
  by_cases h : m + 1 ∣ n
  · rw [if_pos ⟨by omega, h⟩, if_pos ⟨by omega, h⟩, if_pos ⟨by omega, h⟩, if_pos h, map_neg, hd,
      map_add, map_add, coeff_uW_inv_pow, coeff_uW_pow, one_pow, coeff_one]
    ring
  · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2), if_neg h]
    simp

end

end VOA.DeligneAudit.DeligneMLDE.HeatK

/-! ## `ℚ`-side: level-three Lambert series -/

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- `q ↦ q³`. -/
abbrev ex3 : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := expand 3 (by norm_num)

/-- The character `χ₋₃`. -/
def chi3 (k : ℕ) : ℚ := if k % 3 = 1 then 1 else if k % 3 = 2 then -1 else 0
/-- `ω^k + ω^{-k}`. -/
def cc3 (k : ℕ) : ℚ := if k % 3 = 0 then 2 else -1

/-- `L₀ = ∑_{dk=n} χ₋₃(k) qⁿ`. -/
def L0 : PowerSeries ℚ := lamQ fun _ k => chi3 k
/-- `M₁ = ∑_{dk=n} (ω^k+ω^{-k}) k qⁿ`. -/
def M1 : PowerSeries ℚ := lamQ fun _ k => cc3 k * k
/-- `N₃ = ∑_{dk=n} d (ω^k+ω^{-k}+1) qⁿ`. -/
def N3 : PowerSeries ℚ := lamQ fun d k => (d : ℚ) * (cc3 k + 1)

theorem lamQ_dvd3 (F : ℕ → ℕ → ℚ) :
    lamQ (fun d k => if 3 ∣ k then F d k else 0) = ex3 (lamQ fun d k => F d (3 * k)) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_expand, coeff_lamQ_divisors]
  split_ifs with h2
  · obtain ⟨t, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left _ (by norm_num), coeff_lamQ_divisors, ← Finset.sum_filter]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    have hset : (Nat.divisors (3 * t)).filter (fun d => 3 ∣ (3 * t / d)) = t.divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, -⟩, ⟨s, hs⟩⟩
        refine ⟨?_, by omega⟩
        have : 3 * t = d * (3 * s) := by rw [← hs, Nat.mul_div_cancel' hd]
        exact ⟨s, by linarith⟩
      · rintro ⟨hd, -⟩
        refine ⟨⟨Dvd.dvd.mul_left hd 3, by omega⟩, ?_⟩
        rw [Nat.mul_div_assoc _ hd]; exact dvd_mul_right _ _
    rw [hset]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mul_div_assoc _ (Nat.mem_divisors.mp hd).1]
  · refine Finset.sum_eq_zero fun d hd => ?_
    rw [if_neg]
    rintro ⟨s, hs⟩
    apply h2
    have := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    exact ⟨s * d, by rw [← this, hs]; ring⟩

theorem M1_eq : M1 = -P1 + 9 * ex3 P1 := by
  have h : lamQ (fun _ k => cc3 k * k) =
      lamQ (fun d k => -1 * (k : ℚ) + 3 * (if 3 ∣ k then (k : ℚ) else 0)) := by
    refine lamQ_congr fun d k _ => ?_
    unfold cc3
    by_cases h3 : 3 ∣ k
    · rw [if_pos (Nat.mod_eq_zero_of_dvd h3), if_pos h3]; ring
    · rw [if_neg (fun h' => h3 (Nat.dvd_of_mod_eq_zero h')), if_neg h3]; ring
  rw [M1, h, lamQ_add, lamQ_smul, lamQ_smul, lamQ_dvd3, P1]
  have : lamQ (fun (_ : ℕ) (k : ℕ) => ((3 * k : ℕ) : ℚ)) = PowerSeries.C 3 * lamQ fun _ k => (k : ℚ) := by
    rw [← lamQ_smul]; exact lamQ_congr fun d k _ => by push_cast; ring
  rw [this, map_mul, show ex3 (PowerSeries.C 3) = PowerSeries.C 3 from by
    rw [show (PowerSeries.C (3 : ℚ)) = 3 from map_ofNat _ 3, map_ofNat]]
  simp only [map_neg, map_one, show (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 from map_ofNat _ 3]
  ring

theorem M1_eq' : M1 = -P1 + PowerSeries.C 9 * ex3 P1 := by
  rw [M1_eq, map_ofNat]

theorem N3_eq : N3 = 3 * ex3 P1 := by
  have h : lamQ (fun d k => (d : ℚ) * (cc3 k + 1)) =
      lamQ (fun d k => 3 * (if 3 ∣ k then (d : ℚ) else 0)) := by
    refine lamQ_congr fun d k _ => ?_
    unfold cc3
    by_cases h3 : 3 ∣ k
    · rw [if_pos (Nat.mod_eq_zero_of_dvd h3), if_pos h3]; ring
    · rw [if_neg (fun h' => h3 (Nat.dvd_of_mod_eq_zero h')), if_neg h3]; ring
  rw [N3, h, lamQ_smul, lamQ_dvd3, ← order_one, D1,
    show (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 from map_ofNat _ 3]

theorem N3_eq' : N3 = PowerSeries.C 3 * ex3 P1 := by
  rw [N3_eq, map_ofNat]

end

end VOA.DeligneAudit.DeligneMLDE.Heat

/-! ## `ℂ`-side: the specialization `u = ω eˣ` -/

namespace VOA.DeligneAudit.DeligneMLDE.HeatK

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneMLDE.Heat

open scoped BigOperators

noncomputable section

/-- A primitive cube root of unity. -/
def ω3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem ω3_sq_add : ω3 ^ 2 + ω3 + 1 = 0 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [ω3, pow_two] <;> nlinarith [h3]

theorem ω3_ne_zero : ω3 ≠ 0 := by
  intro h; have := ω3_sq_add; rw [h] at this; norm_num at this

theorem ω3_ne_one : ω3 ≠ 1 := by
  intro h; have := ω3_sq_add; rw [h] at this; norm_num at this

theorem ω3_cube : ω3 ^ 3 = 1 := by
  linear_combination (ω3 - 1) * ω3_sq_add

theorem ω3_inv : ω3⁻¹ = ω3 ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', ω3_cube]

theorem ω3_pow_mod (k : ℕ) : ω3 ^ k = ω3 ^ (k % 3) := by
  conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, ω3_cube, one_pow, one_mul]

theorem ω3_inv_pow_mod (k : ℕ) : ω3⁻¹ ^ k = ω3⁻¹ ^ (k % 3) := by
  conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, inv_pow, ω3_cube, inv_one, one_pow,
    one_mul]

theorem ω3_add_inv (k : ℕ) : ω3 ^ k + ω3⁻¹ ^ k = (cc3 k : ℂ) := by
  rw [ω3_pow_mod, ω3_inv_pow_mod, ω3_inv, cc3]
  have h := ω3_sq_add
  have hc := ω3_cube
  have : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hk : k % 3
  · norm_num
  · simp only [pow_one, one_ne_zero, if_false, zero_ne_one, OfNat.one_ne_ofNat]
    push_cast
    linear_combination h
  · simp only [OfNat.ofNat_ne_zero, if_false]
    push_cast
    linear_combination h + ω3 * hc

theorem ω3_sub_inv (k : ℕ) : ω3⁻¹ ^ k - ω3 ^ k = -(ω3 - ω3⁻¹) * (chi3 k : ℂ) := by
  rw [ω3_pow_mod, ω3_inv_pow_mod, ω3_inv, chi3]
  have hc := ω3_cube
  have : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hk : k % 3
  · norm_num
  · norm_num
  · norm_num
    linear_combination ω3 * hc

/-! ### Lambert series over `ℂ` from `ℚ` -/

theorem lamK_congr {F G : ℕ → ℕ → ℂ} (h : ∀ d k, 1 ≤ d → F d k = G d k) : lamK F = lamK G := by
  refine PowerSeries.ext fun n => ?_
  simp only [lamK, coeff_mk]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h _ _ (by omega)]

theorem lamK_smul (c : ℂ) (F : ℕ → ℕ → ℂ) :
    lamK (fun d k => c * F d k) = PowerSeries.C c * lamK F := by
  refine PowerSeries.ext fun n => ?_
  simp only [lamK, coeff_mk, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

/-- The `ℚ → ℂ` coefficient map. -/
abbrev toC : PowerSeries ℚ →+* PowerSeries ℂ := PowerSeries.map (algebraMap ℚ ℂ)

theorem lamK_map (F : ℕ → ℕ → ℚ) : lamK (fun d k => ((F d k : ℚ) : ℂ)) = toC (lamQ F) := by
  refine PowerSeries.ext fun n => ?_
  simp only [lamK, coeff_mk, coeff_map, coeff_lamQ, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem C_mul_C_mulC (a b : ℂ) (F G : PowerSeries ℂ) :
    PowerSeries.C a * F * (PowerSeries.C b * G) = PowerSeries.C (a * b) * (F * G) := by
  rw [map_mul]; ring

/-! ### Order `x⁰` at `u = ω eˣ` -/

theorem pj0R : pjK 0 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-(ω3 - ω3⁻¹)) * toC L0 := by
  rw [pjK_R, L0, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  exact ω3_sub_inv k

theorem pj1R : pjK 1 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-1) * toC M1 := by
  rw [pjK_R, M1, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_add_inv k
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  push_cast
  linear_combination (-(k : ℂ)) * h

theorem pj0T : pjK 0 (Tser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-1) * toC N3 := by
  rw [pjK_T, N3, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_add_inv k
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, if_true]
  push_cast
  linear_combination (-(d : ℂ)) * h

/-- **The level-three Lambert identity** `3L₀² + L₀ = P₁(q) - 3P₁(q³)`, from order `x⁰` of the
heat identity at `u = ω eˣ`. -/
theorem level3_l0 : 3 * (L0 * L0) + L0 = P1 - 3 * ex3 P1 := by
  have h := star_pjK (uW ω3 ω3_ne_zero) (dx_uW ω3 ω3_ne_zero) 0
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pjK_one, pjK_C, coeff_uW,
    if_true, Nat.factorial_zero, Nat.cast_one, div_one, Nat.cast_zero, zero_add, pj0R, pj1R, pj0T,
    C_mul_C_mulC] at h
  rw [← map_mul toC L0 L0, M1_eq', N3_eq'] at h
  set LL := toC (L0 * L0) with hLL
  simp only [map_add, map_neg, map_mul, PowerSeries.map_C] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, neg_mul, mul_neg, neg_neg, map_add, map_sub,
    map_neg, mul_assoc, coeff_C_mul, coeff_map, hLL] at hn
  rw [ω3_inv] at hn
  have hω := ω3_sq_add
  have h1 : (1 : ℂ) - ω3 ≠ 0 := sub_ne_zero.mpr (Ne.symm ω3_ne_one)
  set x1 := coeff n P1
  set x2 := coeff n (ex3 P1)
  set x3 := coeff n (L0 * L0)
  set x4 := coeff n L0
  have key : (1 - ω3) * (((x1 - 3 * x2 - 3 * x3 - x4 : ℚ) : ℂ)) = 0 := by
    simp only [eq_ratCast, Rat.cast_ofNat] at hn
    push_cast
    linear_combination hn - ((1 - ω3) * (ω3 ^ 2 - 3 * ω3 + 3) * (x3 : ℂ) + (1 - ω3) * (x4 : ℂ)) * hω
  have := (mul_eq_zero.mp key).resolve_left h1
  have hq : x1 - 3 * x2 - 3 * x3 - x4 = 0 := by exact_mod_cast this
  rw [show (3 : PowerSeries ℚ) = PowerSeries.C 3 from (map_ofNat _ 3).symm, map_add, coeff_C_mul,
    map_sub, coeff_C_mul]
  linarith


/-- **`(1 + 6L₀)² = 1 + 12P₁(q) - 36P₁(q³)`** (the Lambert form of `2a² = 3E₂(q³) - E₂(q)`). -/
theorem level3_sq : (1 + 6 * L0) ^ 2 = 1 + 12 * P1 - 36 * ex3 P1 := by
  linear_combination 12 * level3_l0

end

end VOA.DeligneAudit.DeligneMLDE.HeatK

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries

/-- `[qⁿ] L₀ = ∑_{k ∣ n} χ₋₃(k)`. -/
theorem coeff_L0 (n : ℕ) : coeff n L0 = ∑ k ∈ n.divisors, chi3 k := by
  rw [L0, coeff_lamQ_divisors, Nat.sum_div_divisors n chi3]

end VOA.DeligneAudit.DeligneMLDE.Heat

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.HeatK.level3_l0
#print axioms VOA.DeligneAudit.DeligneMLDE.HeatK.level3_sq
end AxiomAudit
