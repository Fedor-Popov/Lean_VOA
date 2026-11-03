/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedTranslation

/-!
# A charge-`γ` field on `S[θ] ⊗ T` is determined by its vacuum expectation  (Moonshine step M6, d)

If a family of operators `Ψ_k` on `S[θ] ⊗ T` has the commutation relations of the twisted
exponential of charge `γ`,

  `[h_b(K/2) ⊗ 1, Ψ_k] = γ_b Ψ_{k+K}`  (all odd `K`, all `b`),

then `Ψ` is determined by its vacuum-to-vacuum components `⟨1| Ψ_k |1⟩ ∈ End T`: if these vanish,
`Ψ = 0` (`eq_zero_of_charge`).  Proof: the coefficients of `Ψ_k(1 ⊗ t)` are reached from the
constant term by the annihilators `h_b(K/2) ∝ ∂/∂X` (induction on the degree), and the creators
`h_b(−K/2) = X ·` move `Ψ` across every polynomial.

`fld_eq_zero_of_charge` is the field form used for the base case of the twisted product
formula: a family of fields `Φ c` (class `c`, `Φ (c+2) = z Φ c`) whose twisted products with the
generators are `star ½ (Fgen_b) s (Φ c) = δ_{s0} γ_b Φ(c+1)` and whose vacuum expectations
vanish is zero.

`cfT m : S[θ] ⊗ T → T` is the coefficient of the monomial `m`; `cfT 0` is the vacuum projection.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

variable {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm]

/-! ## Coefficients on `S[θ] ⊗ T` -/

/-- The coefficient of the monomial `m`, `S[θ] ⊗ T → T`. -/
noncomputable def cfT (m : (ℕ × Fin r) →₀ ℕ) : FockT r ⊗[ℂ] Tm →ₗ[ℂ] Tm :=
  (TensorProduct.lid ℂ Tm).toLinearMap ∘ₗ (MvPolynomial.lcoeff ℂ m).rTensor Tm

theorem cfT_tmul (m : (ℕ × Fin r) →₀ ℕ) (p : FockT r) (t : Tm) :
    cfT m (p ⊗ₜ[ℂ] t) = coeff m p • t := by
  rw [cfT, LinearMap.comp_apply, LinearMap.rTensor_tmul]
  rfl

theorem eq_zero_of_cfT {z : FockT r ⊗[ℂ] Tm} (h : ∀ m, cfT m z = 0) : z = 0 := by
  have hf : TensorProduct.finsuppScalarLeft ℂ Tm ((ℕ × Fin r) →₀ ℕ) z = 0 := by
    ext m
    rw [TensorProduct.finsuppScalarLeft_apply, Finsupp.coe_zero, Pi.zero_apply, ← h m]
    rfl
  exact (LinearEquiv.map_eq_zero_iff _).mp hf

theorem coeff_pderiv (m : (ℕ × Fin r) →₀ ℕ) (x : ℕ × Fin r) (p : FockT r) :
    coeff m (pderiv x p) = ((m x : ℂ) + 1) * coeff (m + Finsupp.single x 1) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [pderiv_monomial, coeff_monomial, coeff_monomial]
      by_cases hs : s = m + Finsupp.single x 1
      · subst hs
        rw [if_pos (by ext y; simp), if_pos rfl]
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast; ring
      · rw [if_neg hs, mul_zero]
        split_ifs with h
        · have hsx : s x = 0 := by
            by_contra hne
            apply hs
            ext y
            have := congrArg (fun f => f y) h
            simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.add_apply] at this ⊢
            by_cases hy : y = x
            · subst hy; simp only [Finsupp.single_eq_same] at this ⊢; omega
            · rw [Finsupp.single_eq_of_ne' (Ne.symm hy)] at this ⊢; omega
          rw [hsx, Nat.cast_zero, mul_zero]
        · rfl
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, mul_add]

theorem cfT_pderiv (m : (ℕ × Fin r) →₀ ℕ) (x : ℕ × Fin r) (z : FockT r ⊗[ℂ] Tm) :
    cfT m ((pderiv x).toLinearMap.rTensor Tm z)
      = ((m x : ℂ) + 1) • cfT (m + Finsupp.single x 1) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, smul_zero]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, smul_add]
  | tmul p t =>
      rw [LinearMap.rTensor_tmul, cfT_tmul, cfT_tmul, smul_smul]
      change coeff m (pderiv x p) • t = _
      rw [coeff_pderiv]

/-! ## The uniqueness lemma -/

/-- **A charge-`γ` operator family with vanishing vacuum expectations is zero.** -/
theorem eq_zero_of_charge (γ : Fin r → ℂ) (Ψ : ℤ → End ℂ (FockT r ⊗[ℂ] Tm))
    (hcomm : ∀ (b : Fin r) (K : ℤ), Odd K → ∀ k : ℤ,
      (modeT r b K).rTensor Tm * Ψ k - Ψ k * (modeT r b K).rTensor Tm = γ b • Ψ (k + K))
    (hvac : ∀ (k : ℤ) (t : Tm), cfT 0 (Ψ k (1 ⊗ₜ[ℂ] t)) = 0) : ∀ k, Ψ k = 0 := by
  -- the coefficients of `Ψ_k (1 ⊗ t)`
  have hcoef : ∀ (d : ℕ) (m : (ℕ × Fin r) →₀ ℕ), m.degree = d →
      ∀ (k : ℤ) (t : Tm), cfT m (Ψ k (1 ⊗ₜ[ℂ] t)) = 0 := by
    intro d
    induction d with
    | zero =>
        intro m hm k t
        rw [(Finsupp.degree_eq_zero_iff m).mp hm]
        exact hvac k t
    | succ d ih =>
        intro m hm k t
        obtain ⟨x, hx⟩ : ∃ x, m x ≠ 0 := by
          by_contra h
          push Not at h
          have : m = 0 := by ext y; exact h y
          rw [this, map_zero] at hm
          omega
        set m' := m - Finsupp.single x 1 with hm'
        have hmm : m = m' + Finsupp.single x 1 := by
          ext y
          simp only [hm', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
          by_cases hy : y = x
          · subst hy; simp only [Finsupp.single_eq_same]; omega
          · rw [Finsupp.single_eq_of_ne' (Ne.symm hy)]; omega
        have hdeg : m'.degree = d := by
          have := congrArg Finsupp.degree hmm
          rw [map_add, Finsupp.degree_single, hm] at this
          omega
        -- the annihilator `∂/∂X_x`
        set K : ℤ := 2 * x.1 + 1 with hK
        have hpd : (pderiv x).toLinearMap.rTensor Tm (Ψ k (1 ⊗ₜ[ℂ] t))
            = ((2 : ℂ) / K * γ x.2) • Ψ (k + K) (1 ⊗ₜ[ℂ] t) := by
          have h := congrArg (fun f : End ℂ (FockT r ⊗[ℂ] Tm) => f (1 ⊗ₜ[ℂ] t))
            (hcomm x.2 K ⟨x.1, by rw [hK]⟩ k)
          simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.rTensor_tmul,
            LinearMap.smul_apply] at h
          rw [show modeT r x.2 K 1 = 0 from modeT_vacT r x.2 (by omega),
            TensorProduct.zero_tmul, map_zero, sub_zero] at h
          have hmode : (modeT r x.2 K).rTensor Tm
              = (((2 * x.1 + 1 : ℤ) : ℂ) / 2) • (pderiv x).toLinearMap.rTensor Tm := by
            rw [← LinearMap.rTensor_smul]
            congr 1
            refine LinearMap.ext fun p => ?_
            rw [LinearMap.smul_apply, hK, modeT_annihilation]
            rfl
          rw [hmode, LinearMap.smul_apply] at h
          have hne : (((2 * x.1 + 1 : ℤ) : ℂ) / 2) ≠ 0 := by
            have : ((2 * x.1 + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show (2 * x.1 + 1 : ℤ) ≠ 0 by omega)
            exact div_ne_zero this two_ne_zero
          rw [← smul_right_injective _ hne |>.eq_iff, h, smul_smul]
          congr 1
          rw [hK]
          have : ((2 * x.1 + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show (2 * x.1 + 1 : ℤ) ≠ 0 by omega)
          field_simp
        have h1 := cfT_pderiv m' x (Ψ k (1 ⊗ₜ[ℂ] t))
        rw [hpd, map_smul, ih m' hdeg (k + K) t, smul_zero, ← hmm] at h1
        have hne : ((m' x : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero (m' x)
        exact (smul_eq_zero.mp h1.symm).resolve_left hne
  have hone : ∀ (k : ℤ) (t : Tm), Ψ k (1 ⊗ₜ[ℂ] t) = 0 := fun k t =>
    eq_zero_of_cfT fun m => hcoef m.degree m rfl k t
  -- the creators move `Ψ` across the polynomials
  have hpoly : ∀ (y : FockT r) (k : ℤ) (t : Tm), Ψ k (y ⊗ₜ[ℂ] t) = 0 := by
    intro y
    induction y using MvPolynomial.induction_on with
    | C c =>
        intro k t
        rw [show (MvPolynomial.C c : FockT r) = c • 1 by rw [MvPolynomial.smul_eq_C_mul, mul_one],
          ← TensorProduct.smul_tmul', map_smul, hone, smul_zero]
    | add p q hp hq => intro k t; rw [TensorProduct.add_tmul, map_add, hp, hq, add_zero]
    | mul_X p x hp =>
        intro k t
        set K : ℤ := -(2 * x.1 + 1) with hK
        have h := congrArg (fun f : End ℂ (FockT r ⊗[ℂ] Tm) => f (p ⊗ₜ[ℂ] t))
          (hcomm x.2 K ⟨-(x.1 : ℤ) - 1, by rw [hK]; ring⟩ k)
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.rTensor_tmul,
          LinearMap.smul_apply, hp, map_zero, zero_sub] at h
        rw [hK, modeT_creation, mul_comm] at h
        rw [show (Prod.mk x.1 x.2 : ℕ × Fin r) = x from rfl] at h
        rw [← neg_eq_zero, h, smul_zero]
  intro k
  exact TensorProduct.ext' fun y t => by rw [hpoly, LinearMap.zero_apply]

/-! ## The field form -/

theorem mode_FgT' (b : Fin r) (m : ℤ) :
    mode (FgT (Tm := Tm) b).1 m = (modeT r b (2 * m + 1)).rTensor Tm := by
  rw [mode_apply]
  change ((Moonshine.FgenFld r b).1 (-m - 1)).rTensor Tm = _
  have h := Moonshine.mode_Fgen r b m
  rw [mode_apply] at h
  rw [Moonshine.FgenFld_val, h]

theorem fld_shift_of_two {Φ : ℤ → Fld (FockT r ⊗[ℂ] Tm)}
    (hshift : ∀ c, Φ (c + 2) = fzmul 1 (Φ c)) (c p : ℤ) : Φ (c + 2 * p) = fzmul p (Φ c) := by
  induction p using Int.induction_on with
  | zero => simp
  | succ p ih => rw [show c + 2 * (p + 1) = (c + 2 * p) + 2 by ring, hshift, ih, fzmul_fzmul,
      add_comm]
  | pred p ih =>
      have h := hshift (c + 2 * (-(p : ℤ) - 1))
      rw [show c + 2 * (-(p : ℤ) - 1) + 2 = c + 2 * (-(p : ℤ)) by ring, ih] at h
      have h' := congrArg (fzmul (-1)) h
      rw [fzmul_fzmul, fzmul_fzmul, show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift] at h'
      rw [← h', show (-1 : ℤ) + -(p : ℤ) = -(p : ℤ) - 1 by ring]

/-- **Uniqueness, field form**: a family of fields of charge `γ` (twisted products with the
generators `δ_{s0} γ_b Φ(c+1)`) with vanishing vacuum expectations is zero. -/
theorem fld_eq_zero_of_charge (γ : Fin r → ℂ) (Φ : ℤ → Fld (FockT r ⊗[ℂ] Tm))
    (hshift : ∀ c, Φ (c + 2) = fzmul 1 (Φ c))
    (hloc : ∀ b c, Local (FgT (Tm := Tm) b).1 (Φ c).1)
    (hcharge : ∀ (b : Fin r) (c : ℤ) (s : ℕ),
      star (1 / 2) (FgT b) s (Φ c) = if s = 0 then γ b • Φ (c + 1) else 0)
    (hvac : ∀ (c : ℤ) (t : Tm), cfT 0 (mode (Φ c).1 0 (1 ⊗ₜ[ℂ] t)) = 0) : ∀ c, Φ c = 0 := by
  -- the untwisted products with the generators
  have hprod : ∀ (b : Fin r) (c : ℤ) (s : ℕ),
      Fld.prod s (FgT b) (Φ c) = if s = 0 then γ b • Φ (c + 1) else 0 := by
    intro b c
    obtain ⟨N0, hN0⟩ := Fld.prod_eventually_zero_of_local (hloc b c)
    set N : ℕ := N0.toNat + 1 with hN
    have key : ∀ k : ℕ, ∀ s : ℕ, N ≤ s + k →
        Fld.prod s (FgT b) (Φ c) = if s = 0 then γ b • Φ (c + 1) else 0 := by
      intro k
      induction k with
      | zero =>
          intro s hs
          rw [hN0 _ (by omega), if_neg (by omega)]
      | succ k ih =>
          intro s hs
          have h := hcharge b c s
          rw [star_eq_sum_range _ _ _ _ N (fun i hi => hN0 _ (by omega)),
            Finset.sum_eq_single 0 (fun i _ hi => by
              have := ih (s + i) (by omega)
              push_cast at this
              rw [this, if_neg (by omega), fzmul_zero, smul_zero])
              (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0)] at h
          simpa using h
    exact fun s => key N s (by omega)
  set Ψ : ℤ → End ℂ (FockT r ⊗[ℂ] Tm) := fun k => mode (Φ k).1 0 with hΨ
  have hmode : ∀ c p : ℤ, mode (Φ c).1 p = Ψ (c + 2 * p) := by
    intro c p
    simp only [hΨ]
    rw [fld_shift_of_two hshift c p, fzmul_val, mode_zmul, zero_add]
  have hcomm : ∀ (b : Fin r) (K : ℤ), Odd K → ∀ k : ℤ,
      (modeT r b K).rTensor Tm * Ψ k - Ψ k * (modeT r b K).rTensor Tm = γ b • Ψ (k + K) := by
    intro b K hK k
    obtain ⟨m, rfl⟩ := hK
    obtain ⟨N0, hN0⟩ := Fld.prod_eventually_zero_of_local (hloc b k)
    refine LinearMap.ext fun y => ?_
    have h := mode_comm_eq_sum_range (hloc b k) (N0.toNat + 1)
      (fun s hs => hN0 _ (by omega)) m 0 y
    rw [Finset.sum_eq_single 0 (fun s _ hs => by
        rw [hprod b k s, if_neg hs, Fld.zero_val, mode_zero, LinearMap.zero_apply, smul_zero])
      (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0)] at h
    rw [hprod b k 0, if_pos rfl, mode_FgT', Fld.smul_val, mode_smul, LinearMap.smul_apply,
      gBinom_zero, one_smul, hmode, hmode] at h
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
    rw [show (2 * m + 1) = 2 * m + 1 from rfl] at h
    rw [show k + 2 * 0 = k by ring, show k + 1 + 2 * (m + 0 - ((0 : ℕ) : ℤ)) = k + (2 * m + 1) by
      push_cast; ring] at h
    exact h
  have hzero := eq_zero_of_charge γ Ψ hcomm (fun k t => hvac k t)
  intro c
  apply fld_ext_mode
  intro p x
  rw [hmode, hzero, Fld.zero_val, mode_zero]

end VOA.Moonshine.LatticeTwisted
