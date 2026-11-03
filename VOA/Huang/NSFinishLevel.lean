/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NgSchauenburgCongruence
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The exact-level lemma (Wohlfahrt; Dong–Lin–Ng, Lemma A.1)

Let `H` be a **normal** subgroup of `SL(2, ℤ)` containing some principal congruence subgroup
`Γ(N)`, and suppose `Tⁿ ∈ H` with `n ∣ N`.  Then `Γ(n) ≤ H`.

Consequently, if a representation of `SL(2, ℤ)` (into any monoid) kills `Γ(N)` for some
`N > 0`, then `ρ(T)` has finite order `n` and `ρ` already kills `Γ(n)`.  This discharges the
named contract `VOA.Huang.NgSchauenburg.ExactLevelTheorem` for **every** representation, and
gives `CongruenceAtOrder`-type conclusions from congruence at an arbitrary level.

## Proof

All steps are elementary matrix manipulations in `SL(2, ℤ)`.

1. `T^x ∈ H` and `L(y) = S T^{-y} S⁻¹ = !![1, 0; y, 1] ∈ H` for `n ∣ x`, `n ∣ y` (normality).
2. For `γ ∈ Γ(n)` the entry `a = γ₀₀` is coprime to `n γ₁₀`; an explicit product of primes
   `k` makes `a + n γ₁₀ k` coprime to `N` (`exists_isCoprime_add_mul`).  Replace `γ` by
   `T^{nk} γ`.
3. If `γ₀₀ = u` is a unit modulo `N` and the off-diagonal entries of `γ` are divisible by `n`, then
   `L(x) γ T^y` with `x, y ∈ nℤ` is congruent to `diag(u, u⁻¹)` modulo `N` (`reduce_mod`).
4. The element `g = T L(u - 1) T⁻¹ = !![u, 1 - u; u - 1, 2 - u]` lies in `H` (normality), has
   `g₀₀ = u`, and off-diagonal entries in `nℤ`.  Reducing both `γ` and `g` as in step 3 gives two
   elements of `SL(2, ℤ)` with the same reduction modulo `N`, so their quotient lies in
   `Γ(N) ≤ H`.  Hence `γ ∈ H`.

No representation theory, no Schur multiplier and no congruence-subgroup theorem is used.
-/

noncomputable section

namespace VOA.Huang.NSFinish

open Matrix CongruenceSubgroup
open scoped MatrixGroups

/-! ## Arithmetic: moving an entry into the units modulo `N` -/

/-- If `a` is coprime to `m`, some `a + m k` is coprime to a given positive `N`.  The witness is
the product of the primes of `N` that do not divide `a`. -/
theorem exists_isCoprime_add_mul {a m : ℤ} (h : IsCoprime a m) {N : ℕ} (hN : N ≠ 0) :
    ∃ k : ℤ, IsCoprime (a + m * k) (N : ℤ) := by
  classical
  let P : ℕ := ∏ p ∈ N.primeFactors.filter (fun p : ℕ => ¬ ((p : ℤ) ∣ a)), p
  refine ⟨(P : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  change Nat.gcd (a + m * (P : ℤ)).natAbs (N : ℤ).natAbs = 1
  rw [Int.natAbs_natCast]
  apply Nat.coprime_of_dvd
  intro k hk hkx hkN
  have hkx' : (k : ℤ) ∣ a + m * (P : ℤ) := Int.natCast_dvd.mpr hkx
  have hkZ : Prime (k : ℤ) := Nat.prime_iff_prime_int.mp hk
  by_cases hka : (k : ℤ) ∣ a
  · -- `k` divides `a`, hence not `m`, and `k` is not among the primes of `P`.
    have hkm : ¬ (k : ℤ) ∣ m := by
      intro hkm
      have hu := h.isUnit_of_dvd' hka hkm
      rw [Int.isUnit_iff] at hu
      rcases hu with hu | hu
      · have : k = 1 := by exact_mod_cast hu
        exact hk.one_lt.ne' this
      · have : (0 : ℤ) ≤ k := Int.natCast_nonneg k
        omega
    have hkP : ¬ (k : ℤ) ∣ (P : ℤ) := by
      intro hkP
      have hkP' : k ∣ P := Int.natCast_dvd_natCast.mp hkP
      have hkp : Prime k := Nat.prime_iff.mp hk
      obtain ⟨p, hp, hkp'⟩ := (Prime.dvd_finsetProd_iff hkp _).mp hkP'
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      have : k = p := (Nat.prime_dvd_prime_iff_eq hk hp.1.1).mp hkp'
      subst this
      exact hp.2 hka
    have hmP : (k : ℤ) ∣ m * (P : ℤ) := by
      have := dvd_sub hkx' hka
      simpa using this
    rcases hkZ.dvd_or_dvd hmP with h1 | h1
    · exact hkm h1
    · exact hkP h1
  · -- `k` does not divide `a`, so `k` is one of the primes of `P`.
    have hmem : k ∈ N.primeFactors.filter (fun p : ℕ => ¬ ((p : ℤ) ∣ a)) := by
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hk, hkN, hN⟩, hka⟩
    have hkP : k ∣ P := Finset.dvd_prod_of_mem _ hmem
    have hkmP : (k : ℤ) ∣ m * (P : ℤ) :=
      Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hkP) m
    apply hka
    have := dvd_sub hkx' hkmP
    simpa using this

/-! ## Unipotent elements -/

theorem T_zpow_apply (x : ℤ) (i j : Fin 2) :
    (ModularGroup.T ^ x) i j = (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  rw [show (ModularGroup.T ^ x) i j = ((ModularGroup.T ^ x).1) i j from rfl,
    ModularGroup.coe_T_zpow]

theorem S_apply (i j : Fin 2) :
    ModularGroup.S i j = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  rw [show ModularGroup.S i j = (ModularGroup.S.1) i j from rfl, ModularGroup.coe_S]

/-- Entries of a product in `SL(2, ℤ)`. -/
theorem mul_apply' (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower unipotent `!![1, 0; y, 1]`, written as a conjugate of a power of `T`. -/
def lower (y : ℤ) : SL(2, ℤ) := ModularGroup.S * ModularGroup.T ^ (-y) * ModularGroup.S⁻¹

theorem lower_apply (y : ℤ) (i j : Fin 2) :
    (lower y) i j = (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [lower, mul_apply', Matrix.SpecialLinearGroup.SL2_inv_expl, S_apply, T_zpow_apply]

theorem det_eq (A : SL(2, ℤ)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rw [Matrix.det_fin_two] at h
  exact h

/-! ## The normal-subgroup lemma -/

section Normal

variable {H : Subgroup SL(2, ℤ)} {n N : ℕ}

theorem T_zpow_mem (hT : ModularGroup.T ^ (n : ℤ) ∈ H) {x : ℤ} (hx : (n : ℤ) ∣ x) :
    ModularGroup.T ^ x ∈ H := by
  obtain ⟨k, rfl⟩ := hx
  rw [zpow_mul]
  exact Subgroup.zpow_mem _ hT k

theorem lower_mem (hH : H.Normal) (hT : ModularGroup.T ^ (n : ℤ) ∈ H) {y : ℤ}
    (hy : (n : ℤ) ∣ y) : lower y ∈ H :=
  hH.conj_mem _ (T_zpow_mem hT (dvd_neg.mpr hy)) ModularGroup.S

/-- Two elements with equal `(0,0)` entries and off-diagonal entries divisible by `N` have the
same reduction modulo `N`. -/
theorem inv_mul_mem_Gamma {δ₁ δ₂ : SL(2, ℤ)} (h00 : δ₁ 0 0 = δ₂ 0 0)
    (h1 : (N : ℤ) ∣ δ₁ 0 1) (h2 : (N : ℤ) ∣ δ₁ 1 0) (h3 : (N : ℤ) ∣ δ₂ 0 1)
    (h4 : (N : ℤ) ∣ δ₂ 1 0) : δ₂⁻¹ * δ₁ ∈ Gamma N := by
  have e1 : ((δ₁ 0 1 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
  have e2 : ((δ₁ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  have e3 : ((δ₂ 0 1 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3
  have e4 : ((δ₂ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h4
  have d1 : ((δ₁ 0 0 * δ₁ 1 1 - δ₁ 0 1 * δ₁ 1 0 : ℤ) : ZMod N) = 1 := by
    rw [det_eq]; simp
  have d2 : ((δ₂ 0 0 * δ₂ 1 1 - δ₂ 0 1 * δ₂ 1 0 : ℤ) : ZMod N) = 1 := by
    rw [det_eq]; simp
  push_cast at d1 d2
  rw [e1, e2] at d1
  rw [e3, e4] at d2
  rw [Gamma_mem]
  simp only [mul_apply', Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  rw [e1, e2, e3, e4, h00]
  rw [h00] at d1
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination d2
  · ring
  · ring
  · linear_combination d1

/-- **Reduction to diagonal form modulo `N`** by unipotents in `H`. -/
theorem reduce_mod (hH : H.Normal) (hT : ModularGroup.T ^ (n : ℤ) ∈ H) {γ : SL(2, ℤ)}
    (hb : (n : ℤ) ∣ γ 0 1) (hc : (n : ℤ) ∣ γ 1 0) (hu : IsCoprime (γ 0 0) (N : ℤ)) :
    ∃ δ : SL(2, ℤ), (δ ∈ H ↔ γ ∈ H) ∧ δ 0 0 = γ 0 0 ∧ (N : ℤ) ∣ δ 0 1 ∧ (N : ℤ) ∣ δ 1 0 := by
  obtain ⟨u, v, huv⟩ := hu
  have hx : (n : ℤ) ∣ -(γ 1 0 * u) := dvd_neg.mpr (Dvd.dvd.mul_right hc u)
  have hy : (n : ℤ) ∣ -(u * γ 0 1) := dvd_neg.mpr (Dvd.dvd.mul_left hb u)
  refine ⟨lower (-(γ 1 0 * u)) * γ * ModularGroup.T ^ (-(u * γ 0 1)), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mul_mem_cancel_right _ (T_zpow_mem hT hy),
      Subgroup.mul_mem_cancel_left _ (lower_mem hH hT hx)]
  · simp only [mul_apply', lower_apply, T_zpow_apply]
    simp
  · refine ⟨γ 0 1 * v, ?_⟩
    simp only [mul_apply', lower_apply, T_zpow_apply]
    simp
    linear_combination (-(γ 0 1)) * huv
  · refine ⟨γ 1 0 * v, ?_⟩
    simp only [mul_apply', lower_apply, T_zpow_apply]
    simp
    linear_combination (-(γ 1 0)) * huv

/-- **Wohlfahrt / Dong–Lin–Ng Lemma A.1.** A normal subgroup of `SL(2, ℤ)` containing
`Γ(N)` (some `N ≠ 0`) and `Tⁿ` contains `Γ(n)`.  (No divisibility `n ∣ N` is needed: the proof
only ever reduces modulo `N` and uses unipotents in `nℤ`.) -/
theorem gamma_le_of_normal (hH : H.Normal) (hN : N ≠ 0)
    (hΓ : Gamma N ≤ H) (hT : ModularGroup.T ^ (n : ℤ) ∈ H) : Gamma n ≤ H := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  obtain ⟨g00, g01, g10, _⟩ := hγ
  have ha : (n : ℤ) ∣ γ 0 0 - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [g00]; ring)
  have hb : (n : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp g01
  have hc : (n : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp g10
  -- Step 2: make the `(0,0)` entry a unit modulo `N`.
  have hcop : IsCoprime (γ 0 0) ((n : ℤ) * γ 1 0) := by
    apply IsCoprime.mul_right
    · obtain ⟨t, ht⟩ := ha
      exact ⟨1, -t, by linear_combination ht⟩
    · exact ⟨γ 1 1, -(γ 0 1), by linear_combination det_eq γ⟩
  obtain ⟨k, hk⟩ := exists_isCoprime_add_mul hcop hN
  set γ₁ := ModularGroup.T ^ ((n : ℤ) * k) * γ with hγ₁
  have hTk : ModularGroup.T ^ ((n : ℤ) * k) ∈ H := T_zpow_mem hT (dvd_mul_right _ _)
  have hγγ₁ : γ₁ ∈ H ↔ γ ∈ H := Subgroup.mul_mem_cancel_left _ hTk
  have e00 : γ₁ 0 0 = γ 0 0 + (n : ℤ) * γ 1 0 * k := by
    simp only [hγ₁, mul_apply', T_zpow_apply]; simp; ring
  have e01 : γ₁ 0 1 = γ 0 1 + (n : ℤ) * k * γ 1 1 := by
    simp only [hγ₁, mul_apply', T_zpow_apply]; simp
  have e10 : γ₁ 1 0 = γ 1 0 := by
    simp only [hγ₁, mul_apply', T_zpow_apply]; simp
  have hu1 : (n : ℤ) ∣ γ₁ 0 0 - 1 := by
    rw [e00]
    have : γ 0 0 + (n : ℤ) * γ 1 0 * k - 1 = (γ 0 0 - 1) + (n : ℤ) * (γ 1 0 * k) := by ring
    rw [this]
    exact dvd_add ha (dvd_mul_right _ _)
  have huN : IsCoprime (γ₁ 0 0) (N : ℤ) := by rw [e00]; exact hk
  -- Step 3 for `γ₁`.
  obtain ⟨δ₁, hδ₁, d00, d01, d10⟩ := reduce_mod (N := N) hH hT (γ := γ₁)
    (by rw [e01]; exact dvd_add hb (dvd_mul_of_dvd_left (dvd_mul_right _ _) _))
    (by rw [e10]; exact hc) huN
  -- Step 4: the comparison element `g = T L(u-1) T⁻¹ ∈ H`.
  set g := ModularGroup.T * lower (γ₁ 0 0 - 1) * ModularGroup.T⁻¹ with hg
  have hgH : g ∈ H := hH.conj_mem _ (lower_mem hH hT hu1) _
  have hT1 : ∀ i j : Fin 2,
      ModularGroup.T i j = (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    have := T_zpow_apply 1 i j
    rwa [zpow_one] at this
  have hTi : ∀ i j : Fin 2,
      (ModularGroup.T⁻¹) i j = (!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    have := T_zpow_apply (-1) i j
    rwa [zpow_neg, zpow_one] at this
  have f00 : g 0 0 = γ₁ 0 0 := by
    simp only [hg, mul_apply', hT1, hTi, lower_apply]; simp
  have f01 : g 0 1 = -(γ₁ 0 0 - 1) := by
    simp only [hg, mul_apply', hT1, hTi, lower_apply]; simp; ring
  have f10 : g 1 0 = γ₁ 0 0 - 1 := by
    simp only [hg, mul_apply', hT1, hTi, lower_apply]; simp
  obtain ⟨δ₂, hδ₂, d00', d01', d10'⟩ := reduce_mod (N := N) hH hT (γ := g)
    (by rw [f01]; exact dvd_neg.mpr hu1) (by rw [f10]; exact hu1) (by rw [f00]; exact huN)
  have hδ₂H : δ₂ ∈ H := hδ₂.mpr hgH
  have hq : δ₂⁻¹ * δ₁ ∈ H :=
    hΓ (inv_mul_mem_Gamma (by rw [d00, d00', f00]) d01 d10 d01' d10')
  have hδ₁H : δ₁ ∈ H := by
    have := H.mul_mem hδ₂H hq
    rwa [mul_inv_cancel_left] at this
  exact hγγ₁.mp (hδ₁.mp hδ₁H)

end Normal

/-! ## Consequences for representations -/

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
  rw [Gamma_mem]
  simp only [T_zpow_apply]
  simp

/-- **Exact level for a representation into any monoid.** If `f` kills `Γ(N)` for some
`N > 0`, then `f T` has finite order `n` and `f` kills `Γ(n)`. -/
theorem kernel_gamma_orderOf {M : Type*} [Monoid M] (f : SL(2, ℤ) →* M) {N : ℕ} (hN : 0 < N)
    (hf : ∀ γ ∈ Gamma N, f γ = 1) :
    IsOfFinOrder (f ModularGroup.T) ∧ ∀ γ ∈ Gamma (orderOf (f ModularGroup.T)), f γ = 1 := by
  have hTN : f ModularGroup.T ^ N = 1 := by
    have h := hf _ (T_pow_mem_Gamma N)
    rwa [zpow_natCast, map_pow] at h
  have hfin : IsOfFinOrder (f ModularGroup.T) := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, hTN⟩
  refine ⟨hfin, ?_⟩
  let H : Subgroup SL(2, ℤ) := f.toHomUnits.ker
  have hHN : H.Normal := f.toHomUnits.normal_ker
  have hmem : ∀ γ, γ ∈ H ↔ f γ = 1 := by
    intro γ
    change f.toHomUnits γ = 1 ↔ f γ = 1
    rw [Units.ext_iff]
    rfl
  have hΓ : Gamma N ≤ H := fun γ hγ => (hmem γ).mpr (hf γ hγ)
  have hT : ModularGroup.T ^ ((orderOf (f ModularGroup.T) : ℕ) : ℤ) ∈ H := by
    rw [hmem, zpow_natCast, map_pow, pow_orderOf_eq_one]
  intro γ hγ
  exact (hmem γ).mp (gamma_le_of_normal hHN hN.ne' hΓ hT hγ)

theorem inPrincipalCongruence_iff (N : ℕ) (γ : SL(2, ℤ)) :
    NgSchauenburg.InPrincipalCongruence N γ ↔ γ ∈ Gamma N := by
  rw [Gamma_mem]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h 0 0
    · simpa using h 0 1
    · simpa using h 1 0
    · simpa using h 1 1
  · rintro ⟨h00, h01, h10, h11⟩ i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

/-- **`ExactLevelTheorem` holds for every representation** (the Ng–Schauenburg-route contract
of `NgSchauenburgCongruence.lean`, DLN Lemma A.1). -/
theorem exactLevelTheorem {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) : NgSchauenburg.ExactLevelTheorem ρ := by
  rintro ⟨N, hN, hk⟩
  have hf : ∀ γ ∈ Gamma N, ρ γ = 1 := fun γ hγ =>
    hk γ ((inPrincipalCongruence_iff N γ).mpr hγ)
  obtain ⟨hfin, hker⟩ := kernel_gamma_orderOf ρ hN hf
  exact ⟨hfin.orderOf_pos, fun γ hγ => hker γ ((inPrincipalCongruence_iff _ γ).mp hγ)⟩

/-- **Projective congruence plus the DLN lifting contract gives congruence at the exact order**,
with the exact-level half proved. -/
theorem congruenceAtOrder_of_projective_lifting {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W))
    (hlift : NgSchauenburg.DLNLiftingTheorem ρ) {N : ℕ} (hN : 0 < N)
    (hprojective : NgSchauenburg.ProjectiveKernelContainsGamma ρ N) :
    0 < orderOf (ρ ModularGroup.T) ∧
      NgSchauenburg.KernelContainsGamma ρ (orderOf (ρ ModularGroup.T)) :=
  NgSchauenburg.congruenceAtOrder_of_projective ρ hlift (exactLevelTheorem ρ) hN hprojective

end VOA.Huang.NSFinish
