/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO4cInstance

/-! # O5, part (a), algebra: the monodromy of a logarithmic intertwining operator

HLZ's skew-symmetry `Ω_r(𝒴)(w₂,x)w₁ = e^{xL(−1)} 𝒴(w₁, e^{(2r+1)πi}x)w₂` composes to the
**monodromy**: `Ω₀(Ω₀(𝒴))(w₁,x)w₂ = 𝒴(w₁, e^{2πi}x)w₂`. On modes this is

`monoModes 𝒴_{n;k} = e^{−2πi(n+1)} Σ_j C(j,k)(2πi)^{j−k} 𝒴_{n;j}`

(a phase times the log shift `log x ↦ log x + 2πi`).

* `IsLogIntertwining.phaseModes`: scaling the modes by a phase `p(n)` with `p(n+j) = p(n)` for
  `j ∈ ℤ` preserves logarithmic intertwining operators.
* `skewK_phaseModes`: such a phase passes through the per-degree skew.
* `omega_neg_one_monoModes`: `Ω₋₁(monoModes 𝒴) = Ω₀(𝒴)`.
* `omega_zero_omega_zero`: `Ω₀(Ω₀(𝒴)) = monoModes 𝒴`.
* `fixed_monodromy` / `monoModes_fixed`: if a mode coefficient is fixed by the monodromy,
  then it has no logarithm, and it vanishes unless `n ∈ ℤ`.

All of this is formal algebra; no analysis is used.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor
open scoped BigOperators
open VOA.LogSkew

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}

/-! ## The monodromy phase -/

/-- The phase `e^{−2πi(n+1)}` of `x ↦ e^{2πi}x` on `x^{−n−1}`. -/
def monoPhase (n : ℂ) : ℂ := Complex.exp (-(2 * ((Real.pi : ℂ) * Complex.I)) * (n + 1))

theorem monoPhase_add_int (n : ℂ) (j : ℤ) : monoPhase (n + j) = monoPhase n := by
  rw [monoPhase, monoPhase, show -(2 * ((Real.pi : ℂ) * Complex.I)) * (n + j + 1)
      = -(2 * ((Real.pi : ℂ) * Complex.I)) * (n + 1) + ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
      by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `e^{−2πi(n+1)} = 1` exactly for integral `n`. -/
theorem monoPhase_eq_one_iff (n : ℂ) : monoPhase n = 1 ↔ ∃ j : ℤ, n = j := by
  rw [monoPhase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m - 1, ?_⟩
    have h2 : (2 * ((Real.pi : ℂ) * Complex.I)) ≠ 0 := by
      have := Complex.two_pi_I_ne_zero
      rwa [show (2 * ((Real.pi : ℂ) * Complex.I)) = 2 * Real.pi * Complex.I by ring]
    have : (2 * ((Real.pi : ℂ) * Complex.I)) * (n + 1 + m) = 0 := by
      linear_combination -hm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · push_cast; linear_combination h
  · rintro ⟨j, rfl⟩
    exact ⟨-j - 1, by push_cast; ring⟩

/-! ## Phase scaling -/

/-- Scale every mode `𝒴_{n;k}` by `p(n)`. -/
def phaseModes (p : ℂ → ℂ) (Y : LogModes M₁ M₂ M₃) : LogModes M₁ M₂ M₃ :=
  fun n k => p n • Y n k

@[simp] theorem phaseModes_apply (p : ℂ → ℂ) (Y : LogModes M₁ M₂ M₃) (n : ℂ) (k : ℕ)
    (w₁ : M₁) (w₂ : M₂) : phaseModes p Y n k w₁ w₂ = p n • Y n k w₁ w₂ := rfl

/-- **The monodromy** `𝒴(w, e^{2πi}x)`: the phase `e^{−2πi(n+1)}` after the log shift by `2πi`. -/
def monoModes (Y : LogModes M₁ M₂ M₃) : LogModes M₁ M₂ M₃ :=
  phaseModes monoPhase (logShift (2 * ((Real.pi : ℂ) * Complex.I)) Y)

/-- A phase with integral period preserves logarithmic intertwining operators. -/
theorem IsLogIntertwining.isLogIntertwining_phaseModes {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y)
    {p : ℂ → ℂ} (hp : ∀ (n : ℂ) (j : ℤ), p (n + j) = p n) :
    IsLogIntertwining A₁ A₂ A₃ (phaseModes p Y) := by
  refine ⟨fun w₁ w₂ n => ?_, fun w₁ w₂ n => ?_, fun w₁ n k => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hY.logFinite w₁ w₂ n
    exact ⟨K, fun k hk => by rw [phaseModes_apply, hK k hk, smul_zero]⟩
  · obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
    exact ⟨N, fun m hm k => by rw [phaseModes_apply, hN m hm k, smul_zero]⟩
  · have h1 : p (n - 1) = p n := by
      have := hp n (-1)
      rwa [show n + ((-1 : ℤ) : ℂ) = n - 1 by push_cast; ring] at this
    change p n • Y n k (Lm1 A₁ w₁) = (-n) • (p (n - 1) • Y (n - 1) k w₁)
      + ((k : ℂ) + 1) • (p (n - 1) • Y (n - 1) (k + 1) w₁)
    rw [hY.L_neg_one, h1, smul_add, smul_comm (-n), smul_comm ((k : ℂ) + 1)]
  · intro u w₁ w₂ ℓ m n k
    have hL : ∀ i : ℤ, IsLogIntertwining.jacL A₂ A₃ (phaseModes p Y) u w₁ w₂ ℓ m n k i
        = p n • IsLogIntertwining.jacL A₂ A₃ Y u w₁ w₂ ℓ m n k i := by
      intro i
      have e1 : p (n + i) = p n := hp n i
      have e2 : p (ℓ + n - i) = p n := by
        rw [show (ℓ : ℂ) + n - i = n + ((ℓ - i : ℤ) : ℂ) by push_cast; ring, hp]
      simp only [IsLogIntertwining.jacL, phaseModes_apply, e1, e2, map_smul, smul_sub]
      rw [smul_comm (negOnePow i * cbz ℓ i) (p n), smul_comm (negOnePow ℓ) (p n),
        smul_comm (negOnePow i * cbz ℓ i) (p n)]
    have hR : ∀ i : ℤ, IsLogIntertwining.jacR A₁ (phaseModes p Y) u w₁ w₂ ℓ m n k i
        = p n • IsLogIntertwining.jacR A₁ Y u w₁ w₂ ℓ m n k i := by
      intro i
      have e3 : p (m + n - i) = p n := by
        rw [show (m : ℂ) + n - i = n + ((m - i : ℤ) : ℂ) by push_cast; ring, hp]
      simp only [IsLogIntertwining.jacR, phaseModes_apply, e3]
      rw [smul_comm]
    change ∑ᶠ i, IsLogIntertwining.jacL A₂ A₃ (phaseModes p Y) u w₁ w₂ ℓ m n k i
      = ∑ᶠ i, IsLogIntertwining.jacR A₁ (phaseModes p Y) u w₁ w₂ ℓ m n k i
    simp only [hL, hR]
    rw [← smul_finsum' (p n) (IsLogIntertwining.jacL_support_finite hY.truncation ..),
      ← smul_finsum' (p n)
        (IsLogIntertwining.jacR_support_finite (A₁ := A₁) Y u w₁ w₂ ℓ m n k)]
    exact congrArg (p n • ·) (hY.jacobi u w₁ w₂ ℓ m n k)

/-- A phase with integral period passes through the per-degree skew. -/
theorem skewK_phaseModes {Y : LogModes M₁ M₂ M₃} (hT : ∀ k, Trunc (comp Y k))
    {p : ℂ → ℂ} (hp : ∀ (n : ℂ) (j : ℤ), p (n + j) = p n) (c : ℂ → ℂ) :
    skewK A₃ c (phaseModes p Y) = skewK A₃ (fun n => c n * p n) Y := by
  funext n k
  refine LinearMap.ext fun w₂ => LinearMap.ext fun w₁ => ?_
  have hT' : Trunc (comp (phaseModes p Y) k) := by
    intro x y q
    obtain ⟨N, hN⟩ := hT k x y q
    exact ⟨N, fun j hj => by
      change p (q + j) • Y (q + j) k x y = 0
      rw [show Y (q + j) k x y = comp Y k (q + j) x y from rfl, hN j hj, smul_zero]⟩
  change skewModes (Lm1 A₃) c (comp (phaseModes p Y) k) n w₂ w₁
    = skewModes (Lm1 A₃) (fun n => c n * p n) (comp Y k) n w₂ w₁
  rw [skewModes_apply hT', skewModes_apply (hT k)]
  obtain ⟨K, hK⟩ := (hT k).bound w₁ w₂ n
  rw [sSum_eq_sum K (fun j hj => by
      change p (n + j) • Y (n + j) k w₁ w₂ = 0
      rw [show Y (n + j) k w₁ w₂ = comp Y k (n + j) w₁ w₂ from rfl, hK j hj, smul_zero]),
    sSum_eq_sum K hK, mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpj : p (n + j) = p n := by
    have := hp n (j : ℤ)
    rwa [Int.cast_natCast] at this
  change sc j • (Lm1 A₃ ^ j) (p (n + j) • Y (n + j) k w₁ w₂)
    = p n • (sc j • (Lm1 A₃ ^ j) (Y (n + j) k w₁ w₂))
  rw [hpj, map_smul, smul_comm]

/-- `Ω₋₁(monoModes 𝒴) = Ω₀(𝒴)`. -/
theorem omega_neg_one_monoModes {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y) :
    omega A₃ (-1) (monoModes Y) = omega A₃ 0 Y := by
  have hL := hY.isLogIntertwining_logShift (2 * ((Real.pi : ℂ) * Complex.I))
  unfold omega monoModes
  rw [skewK_phaseModes (fun k => hL.trunc_comp k) monoPhase_add_int]
  have hph : (fun n => omegaPhase (-1) n * monoPhase n) = omegaPhase 0 := by
    funext n
    rw [omegaPhase, monoPhase, omegaPhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hph, hY.skewK_logShift (omegaPhase_succ 0) (omegaPhase_ne_zero 0),
    logShift_logShift (hY.isLogIntertwining_skewK (omegaPhase_succ 0)
      (omegaPhase_ne_zero 0)).logFin]
  congr 1
  push_cast
  ring

/-- **`Ω₀ ∘ Ω₀` is the monodromy**: `Ω₀(Ω₀(𝒴))(w₁,x)w₂ = 𝒴(w₁, e^{2πi}x)w₂`. -/
theorem omega_zero_omega_zero {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y) :
    omega A₃ 0 (omega A₃ 0 Y) = monoModes Y := by
  rw [← omega_neg_one_monoModes hY]
  have hM : IsLogIntertwining A₁ A₂ A₃ (monoModes Y) :=
    (hY.isLogIntertwining_logShift _).isLogIntertwining_phaseModes monoPhase_add_int
  have h := hM.omega_omega (-1)
  rwa [show (-(-1 : ℤ) - 1) = 0 by norm_num] at h

/-- The same for the bundled operators. -/
theorem omegaEquiv_zero_omegaEquiv_zero (Y : LogIntertwiningOperator A₁ A₂ A₃) :
    (omegaEquiv A₂ A₁ A₃ 0 (omegaEquiv A₁ A₂ A₃ 0 Y)).1 = monoModes Y.1 :=
  omega_zero_omega_zero Y.2

/-! ## Coefficients fixed by the monodromy -/

/-- `2πi`. -/
abbrev twoPiI : ℂ := 2 * ((Real.pi : ℂ) * Complex.I)

theorem twoPiI_ne_zero : twoPiI ≠ 0 := by
  show 2 * ((Real.pi : ℂ) * Complex.I) ≠ 0
  have := Complex.two_pi_I_ne_zero
  rwa [show (2 * ((Real.pi : ℂ) * Complex.I)) = 2 * Real.pi * Complex.I by ring]

/-- **Pure algebra.** If a finitely supported log-polynomial `Σ_j c_j (log x)^j` is fixed by
`log x ↦ log x + 2πi` up to the phase `q`, then it is constant (`c_j = 0` for `j ≥ 1`), and it
vanishes if `q ≠ 1`. -/
theorem fixed_monodromy {M : Type*} [AddCommGroup M] [Module ℂ M] (c : ℕ → M) (K : ℕ)
    (hK : ∀ k, K ≤ k → c k = 0) (q : ℂ)
    (h : ∀ k, q • ∑ j ∈ Finset.range K, shc twoPiI j k • c j = c k) :
    (∀ k, 1 ≤ k → c k = 0) ∧ (q ≠ 1 → c 0 = 0) := by
  -- the sum at index `i`, when `c` vanishes above `k`
  have hsum : ∀ k i, i ≤ k → (∀ j, k < j → c j = 0) →
      ∑ j ∈ Finset.range K, shc twoPiI j i • c j
        = ∑ j ∈ Finset.range (k + 1), shc twoPiI j i • c j := by
    intro k i _ hbig
    by_cases hKk : K ≤ k + 1
    · refine Finset.sum_subset (Finset.range_subset_range.mpr hKk) fun j hj hjK => ?_
      rw [Finset.mem_range] at hj hjK
      rw [hK j (by omega), smul_zero]
    · refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j hj hjk => ?_).symm
      rw [Finset.mem_range] at hj hjk
      rw [hbig j (by omega), smul_zero]
  have hlow : ∀ k i, i ≤ k →
      ∑ j ∈ Finset.range i, shc twoPiI j i • c j = 0 := by
    intro k i _
    exact Finset.sum_eq_zero fun j hj => by
      rw [Finset.mem_range] at hj
      rw [shc_eq_zero hj, zero_smul]
  have hdiag : ∀ k : ℕ, shc twoPiI k k = 1 := by
    intro k; simp [shc]
  have hsub : ∀ k : ℕ, shc twoPiI (k + 1) k = ((k : ℂ) + 1) * twoPiI := by
    intro k
    simp only [shc, Nat.choose_succ_self_right, show k + 1 - k = 1 by omega, pow_one]
    push_cast; ring
  have key : ∀ t k, K ≤ k + t → 1 ≤ k → c k = 0 := by
    intro t
    induction t with
    | zero => intro k hk _; exact hK k (by omega)
    | succ t ih =>
      intro k hk h1
      have hbig : ∀ j, k < j → c j = 0 := fun j hj => ih j (by omega) (by omega)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      -- index `k' + 1`
      have e1 := h (k' + 1)
      rw [hsum (k' + 1) (k' + 1) le_rfl hbig, Finset.sum_range_succ,
        hlow (k' + 1) (k' + 1) le_rfl, zero_add, hdiag, one_smul] at e1
      -- index `k'`
      have e0 := h k'
      rw [hsum (k' + 1) k' (by omega) hbig, Finset.sum_range_succ, Finset.sum_range_succ,
        hlow (k' + 1) k' (by omega), zero_add, hdiag, one_smul, hsub] at e0
      have hA : (q - 1) • c (k' + 1) = 0 := by rw [sub_smul, e1, one_smul, sub_self]
      by_cases hq : q = 1
      · subst hq
        rw [one_smul, add_eq_left] at e0
        rcases smul_eq_zero.mp e0 with h0 | h0
        · exfalso
          rcases mul_eq_zero.mp h0 with h2 | h2
          · have : ((k' : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k'
            exact this h2
          · exact twoPiI_ne_zero h2
        · exact h0
      · rcases smul_eq_zero.mp hA with h0 | h0
        · exact absurd (sub_eq_zero.mp h0) hq
        · exact h0
  have hpos : ∀ k, 1 ≤ k → c k = 0 := fun k hk => key K k (by omega) hk
  refine ⟨hpos, fun hq => ?_⟩
  have e := h 0
  rw [hsum 0 0 le_rfl (fun j hj => hpos j hj), Finset.sum_range_one, hdiag, one_smul] at e
  have hA : (q - 1) • c 0 = 0 := by rw [sub_smul, e, one_smul, sub_self]
  rcases smul_eq_zero.mp hA with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hq
  · exact h0

/-- **Monodromy-fixed coefficients.** If the monodromy of `Z` agrees with `Y` at `(n, w₁, w₂)`
in every log degree, and `Z` agrees with `Y` there, then `Y_{n;k} w₁ w₂ = 0` for `k ≥ 1`, and
also for `k = 0` unless `n ∈ ℤ`. -/
theorem monoModes_fixed {Y Z : LogModes M₁ M₂ M₃} (hZ : LogFin Z) {w₁ : M₁} {w₂ : M₂} {n : ℂ}
    (hZY : ∀ j, Z n j w₁ w₂ = Y n j w₁ w₂)
    (h : ∀ k, monoModes Z n k w₁ w₂ = Y n k w₁ w₂) :
    (∀ k, 1 ≤ k → Y n k w₁ w₂ = 0) ∧ ((∀ j : ℤ, n ≠ j) → Y n 0 w₁ w₂ = 0) := by
  obtain ⟨K, hK⟩ := hZ w₁ w₂ n
  have hK' : ∀ k, K ≤ k → Y n k w₁ w₂ = 0 := fun k hk => (hZY k).symm.trans (hK k hk)
  have hfix : ∀ k, monoPhase n • ∑ j ∈ Finset.range K, shc twoPiI j k • Y n j w₁ w₂
      = Y n k w₁ w₂ := by
    intro k
    rw [← h k]
    change monoPhase n • _ = monoPhase n • logShift twoPiI Z n k w₁ w₂
    rw [logShift_eq_sum hZ K hK]
    simp only [hZY]
  obtain ⟨h1, h2⟩ := fixed_monodromy (fun k => Y n k w₁ w₂) K hK' (monoPhase n) hfix
  refine ⟨h1, fun hn => h2 fun h1' => ?_⟩
  obtain ⟨j, hj⟩ := (monoPhase_eq_one_iff n).mp h1'
  exact hn j hj

end VOA.LogTensor
