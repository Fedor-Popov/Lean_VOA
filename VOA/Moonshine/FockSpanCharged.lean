/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FockSpanBase

/-!
# `ExcitedSpanned`: the charged excited states of `V₀⁺`  (Moonshine step M8g, R-gen)

`excitedSpanned : ExcitedSpanned` — machine-checked, unconditional.

For `γ ∈ Λ₀ \ 0` (so `|γ|² ≥ 4`, `½|γ|² ≥ 2`) and Fock weight `w ≥ 1`, every `P(p ⊗ e^γ)` is a
combination of weight-raising products of lower-weight states of `V₀⁺`.  Only the quadratic
Heisenberg states `h_a(-i-1)h_b(-j-1)𝟙` of `V₀⁺` are used as left factors:

* **Degree `≥ 2`** (`step_quad`): `(h_ah_b)₍₋₁₎P(m' ⊗ e^γ) = P(X X m' ⊗ e^γ) + (degree ≤ deg)`.
* **Degree `1`** (`charged_deg_one`).  With `φ_a = [X(τ+1,a) e^γ]` in the quotient by `Tsub`
  and `ε = (-1)^τ`, `T = τ+1`, the `0`-modes `(h_ah_b)₍₀₎(X(τ,c)e^γ)` and the `(-1)`-modes
  `(h_a(-1)h_c(-τ-1))₍₋₁₎e^γ` give, for all colours `a, b, c`,
  `T(δ_{cb}φ_a + δ_{ca}φ_b) − εγ_c(γ_bφ_a + γ_aφ_b) − 2Tγ_aγ_bφ_c = 0`.
  Contracting with `γ_c` and then with `γ_a` (`∑γ_c² = |γ|² = N`) gives
  `(T − εN − TN)Φ = 0` and `(T − εN)(γ_bφ_a + γ_aφ_b) = 0`; both coefficients are nonzero
  because `N ≥ 4` is even (`coeff_ne_zero_one`, `coeff_ne_zero_two`), so `φ = 0`
  (`charged_algebra`, `vanish_of_sym`).  The bottom case `X(0,a)e^γ` uses
  `(h_ah_b)₍₀₎e^γ = γ_bX(0,a) + γ_aX(0,b)` alone.

No change of basis to a vector `z ⊥ γ` is needed: the contraction does it.

## Main results
* `charged_algebra`, `charged_deg_one_zero`, `charged_deg_one`, `charged_base`.
* `excitedSpanned`.

## Status
`sorry`-free; no project axiom (`#print axioms excitedSpanned` =
`[propext, Classical.choice, Quot.sound]`).  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FockSpan

open VOA VOA.Moonshine VOA.Moonshine.SigmaExist VOA.Moonshine.ZhuGen LatGen IntegralLattice
  HeisenbergN MvPolynomial
open Submodule

/-! ## §1  The linear algebra of the degree-one relations -/

/-- The contraction argument: the relations `R(a,b,c) = 0` (one for every triple of colours)
force `φ = 0`, provided the two contracted coefficients are nonzero. -/
theorem charged_algebra {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : ι → ℂ) (φ : ι → M) (T ε N : ℂ) (hN : ∑ c, g c * g c = N)
    (hR : ∀ a b c, ((if c = b then T • φ a else 0) + (if c = a then T • φ b else 0))
      - (ε * g c) • (g b • φ a + g a • φ b) - (2 * T * g a * g b) • φ c = 0)
    (h1 : T - ε * N - T * N ≠ 0) (h2 : T - ε * N ≠ 0) (hg : ∃ b, g b ≠ 0) : ∀ a, φ a = 0 := by
  set Φ := ∑ c, g c • φ c with hΦ
  have e1 : ∀ y : ℂ, ∑ i, g i * (ε * g i * y) = ε * N * y := by
    intro y
    rw [← hN, Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring
  have hS : ∀ a b, (T - ε * N) • (g b • φ a + g a • φ b) - (2 * T * g a * g b) • Φ = 0 := by
    intro a b
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun c _ => show
      g c • (((if c = b then T • φ a else 0) + (if c = a then T • φ b else 0))
      - (ε * g c) • (g b • φ a + g a • φ b) - (2 * T * g a * g b) • φ c) = 0 by
        rw [hR a b c, smul_zero])
    rw [← h]
    simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_ite,
      smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul, ← Finset.sum_smul, hΦ,
      Finset.smul_sum, e1]
    simp only [mul_comm (g _) (2 * T * g a * g b)]
    module
  have hΦ0 : Φ = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun a _ => show
      (T - ε * N) • (g a • φ a + g a • φ a) - (2 * T * g a * g a) • Φ = 0 from hS a a)
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_add_distrib, ← hΦ,
      ← Finset.sum_smul, show ∑ i, 2 * T * g i * g i = 2 * T * N by
      rw [← hN, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring] at h
    have h' : (2 * (T - ε * N - T * N)) • Φ = 0 := by rw [← h]; module
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (mul_ne_zero two_ne_zero h1)
    · exact h0
  refine vanish_of_sym g φ (fun a b => ?_) hg
  have h := hS a b
  rw [hΦ0, smul_zero, sub_zero] at h
  rcases smul_eq_zero.mp h with h0 | h0
  · exact absurd h0 h2
  · exact h0

/-! ## §2  Lattice inputs -/

theorem two_le_halfNorm {γ : leech.carrier} (hγ0 : γ ≠ 0) : 2 ≤ LatGen.halfNorm leech γ := by
  have h1 := form_ge_four hγ0
  have h2 := two_mul_halfNorm γ
  omega

theorem sum_chargeCoord_sq (γ : leech.carrier) :
    ∑ c, chargeCoord leech γ c * chargeCoord leech γ c = ((leech.form γ γ : ℤ) : ℂ) :=
  sum_chargeCoord leech leech_posDef γ γ

theorem exists_chargeCoord_ne_zero {γ : leech.carrier} (hγ0 : γ ≠ 0) :
    ∃ b, chargeCoord leech γ b ≠ 0 := by
  by_contra h
  push Not at h
  have hs := sum_chargeCoord_sq γ
  simp only [h, mul_zero, Finset.sum_const_zero] at hs
  have h4 := form_ge_four hγ0
  have : (leech.form γ γ : ℤ) = 0 := by exact_mod_cast hs.symm
  omega

/-! ## §3  Degree one -/

theorem charged_deg_one_zero {γ : leech.carrier} (hγ : γ ∈ lambda0) (hγ0 : γ ≠ 0)
    (c : Fin (rank leech)) :
    (X (0, c) : Fk) ∈ Tsub hγ (1 + LatGen.halfNorm leech γ) := by
  have hh := two_le_halfNorm hγ0
  set T := Tsub hγ (1 + LatGen.halfNorm leech γ)
  have hR : ∀ a b, T.mkQ (chargeCoord leech γ b • (X (0, a) : Fk) + chargeCoord leech γ a •
      (X (0, b) : Fk)) = 0 := by
    intro a b
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have := quadF_mem_Tsub 0 0 a b hγ (n := 1 + LatGen.halfNorm leech γ) (m := 0) le_rfl
      one_mem_gradingWN (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    rwa [show -(0 : ℤ) - 1 = -1 by norm_num, quadF_D_one] at this
  have := vanish_of_sym (fun b => chargeCoord leech γ b) (fun a => T.mkQ (X (0, a) : Fk))
    (fun a b => by rw [← map_smul, ← map_smul, ← map_add]; exact hR a b)
    (exists_chargeCoord_ne_zero hγ0) c
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

theorem coeff_ne_zero_one (τ : ℕ) (N : ℤ) (hN4 : 4 ≤ N) :
    ((τ : ℂ) + 1) - (-1 : ℂ) ^ τ * (N : ℂ) - ((τ : ℂ) + 1) * (N : ℂ) ≠ 0 := by
  rcases Nat.even_or_odd τ with he | ho
  · rw [he.neg_one_pow, one_mul]
    have : ((τ : ℤ) + 1) - N - ((τ : ℤ) + 1) * N ≠ 0 := by nlinarith
    exact_mod_cast this
  · rw [ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]
    have : ((τ : ℤ) + 1) + N - ((τ : ℤ) + 1) * N ≠ 0 := by
      intro h
      rcases Nat.eq_zero_or_pos τ with h0 | h0
      · subst h0; simp at h
      · nlinarith
    exact_mod_cast this

theorem coeff_ne_zero_two (τ : ℕ) (N : ℤ) (hN4 : 4 ≤ N) (hNe : Even N) :
    ((τ : ℂ) + 1) - (-1 : ℂ) ^ τ * (N : ℂ) ≠ 0 := by
  rcases Nat.even_or_odd τ with ⟨k, hk⟩ | ho
  · rw [Even.neg_one_pow ⟨k, hk⟩, one_mul]
    obtain ⟨m, hm⟩ := hNe
    have : ((τ : ℤ) + 1) - N ≠ 0 := by omega
    exact_mod_cast this
  · rw [ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]
    have : ((τ : ℤ) + 1) + N ≠ 0 := by omega
    exact_mod_cast this

/-- **Charged degree one**: every `h_c(-t-1) e^γ` (`γ ∈ Λ₀ \ 0`) lies in `Tsub`. -/
theorem charged_deg_one {γ : leech.carrier} (hγ : γ ∈ lambda0) (hγ0 : γ ≠ 0) (t : ℕ)
    (c : Fin (rank leech)) :
    (X (t, c) : Fk) ∈ Tsub hγ ((t : ℤ) + 1 + LatGen.halfNorm leech γ) := by
  rcases t with _ | τ
  · simpa using charged_deg_one_zero hγ hγ0 c
  have hh := two_le_halfNorm hγ0
  set n : ℤ := ((τ + 1 : ℕ) : ℤ) + 1 + LatGen.halfNorm leech γ with hn
  set T := Tsub hγ n
  set g : Fin (rank leech) → ℂ := fun b => chargeCoord leech γ b with hg
  set φ : Fin (rank leech) → Fk ⧸ T := fun a => T.mkQ (X (τ + 1, a) : Fk) with hφ
  -- the `L4` relation: `X(0,a)X(τ,c) ≡ -((-1)^τ g_c φ_a + (τ+1) g_a φ_c)`
  have hL : ∀ a c, T.mkQ (X (0, a) * X (τ, c) : Fk)
      = -(((-1 : ℂ) ^ τ * g c) • φ a + (((τ : ℂ) + 1) * g a) • φ c) := by
    intro a c
    have := quadF_mem_Tsub 0 τ a c hγ (n := n) (m := -1) (by norm_num) one_mem_gradingWN
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    rw [show -(-1 : ℤ) - 1 = 0 by norm_num, quadF_lead_one, add_assoc] at this
    rw [eq_neg_iff_add_eq_zero]
    simp only [hφ, hg, ← map_smul, ← map_add]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  have hR : ∀ a b c, ((if c = b then ((τ : ℂ) + 1) • φ a else 0)
      + (if c = a then ((τ : ℂ) + 1) • φ b else 0))
      - ((-1 : ℂ) ^ τ * g c) • (g b • φ a + g a • φ b)
      - (2 * ((τ : ℂ) + 1) * g a * g b) • φ c = 0 := by
    intro a b c
    have h := quadF_mem_Tsub 0 0 a b hγ (n := n) (m := 0) le_rfl (X_mem_gradingWN (τ, c))
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    rw [show -(0 : ℤ) - 1 = -1 by norm_num, ← mul_one (X (τ, c) : Fk), quadD_X, quadF_D_one]
      at h
    have h0 := (Submodule.Quotient.mk_eq_zero T).mpr h
    rw [← Submodule.mkQ_apply] at h0
    simp only [map_add, mul_add, mul_smul_comm, apply_ite T.mkQ, map_zero, mul_one,
      LinearMap.map_smul_of_tower] at h0
    rw [mul_comm (X (τ, c) : Fk) (X (0, a)), mul_comm (X (τ, c) : Fk) (X (0, b)), hL, hL] at h0
    split_ifs at h0 ⊢ with h1 h2 h2 <;> (try subst h1) <;> (try subst h2) <;>
      (simp only [hφ, hg] at h0 ⊢; linear_combination (norm := module) h0)
  have hT := charged_algebra g φ ((τ : ℂ) + 1) ((-1 : ℂ) ^ τ) ((leech.form γ γ : ℤ) : ℂ)
    (sum_chargeCoord_sq γ) hR (coeff_ne_zero_one τ _ (form_ge_four hγ0))
    (coeff_ne_zero_two τ _ (form_ge_four hγ0) ⟨LatGen.halfNorm leech γ, by
      have := two_mul_halfNorm γ; omega⟩) (exists_chargeCoord_ne_zero hγ0) c
  simpa only [hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hT

/-! ## §4  `ExcitedSpanned` -/

theorem wordWt_pos {l : List (ℕ × Fin (rank leech))} (hl : l ≠ []) : 1 ≤ wordWt l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons ia rest => rw [wordWt_cons]; omega

theorem eq_zero_of_degree_eq_zero {s : (ℕ × Fin (rank leech)) →₀ ℕ} (h : s.degree = 0) : s = 0 :=
  (Finsupp.degree_eq_zero_iff s).mp h

/-- Degrees `≤ 1` in a charged sector. -/
theorem charged_base {γ : leech.carrier} (hγ : γ ∈ lambda0) (hγ0 : γ ≠ 0) (w : ℕ) (hw : 1 ≤ w) :
    Fdw 1 w ≤ Tsub hγ ((w : ℤ) + LatGen.halfNorm leech γ) := by
  refine (Fdw_le_span 1 w).trans (span_le.mpr ?_)
  rintro _ ⟨s, hsd, hsw, rfl⟩
  rcases Nat.eq_zero_or_pos s.degree with h0 | h0
  · rw [eq_zero_of_degree_eq_zero h0, wt, map_zero] at hsw
    omega
  · obtain ⟨v, s', rfl⟩ := exists_single_add (s := s) h0
    rw [degree_single_add] at hsd
    obtain rfl : s' = 0 := eq_zero_of_degree_eq_zero (by omega)
    rw [wt_single_add, wt, map_zero] at hsw
    rw [SetLike.mem_coe, monomial_single_add_one, monomial_zero', C_1, mul_one]
    have := charged_deg_one hγ hγ0 v.1 v.2
    rw [show ((v.1 : ℤ) + 1) = w by push_cast at hsw; omega] at this
    exact this

/-- **`ExcitedSpanned`** (machine-checked): every projected charged word state with at least
one oscillator is a combination of weight-raising products of lower-weight states of `V₀⁺`. -/
theorem excitedSpanned : ExcitedSpanned := by
  intro l γ hγ hγ0 hl
  rw [← excitedV0_word]
  have hw := wordWt_pos hl
  have hh := two_le_halfNorm hγ0
  change wordStateN l ∈ Tsub hγ ((wordWt l : ℤ) + LatGen.halfNorm leech γ)
  refine gradingWN_le_of_Fdw (fun D => ?_) (wordStateN_mem_gradingWN l)
  refine Fdw_le_of_ascent _ (wordWt l) 1 le_rfl (charged_base hγ hγ0 _ hw)
    (fun D' _ IH v1 v2 s' hdeg hwt => step_quad hγ _ D' (wordWt l) rfl IH v1 v2 s' hdeg hwt
      (by omega)) D

end VOA.Moonshine.FockSpan
