/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2Indep
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The Wakimoto free-field realization of `V^k(𝔰𝔩₂)`, and `sl2Singular ≠ 0`

A **Lie-algebra-only** free-field model for the level-`k` affine `𝔰𝔩₂` current algebra, built on
a polynomial ring with a manifest monomial basis.  No vertex-algebra structure is used anywhere:
the Wakimoto (Feigin–Frenkel) construction is a representation of the *Lie algebra* `𝔰𝔩₂^` on a
`βγ ⊗ Heisenberg` Fock space, and that is all that is needed to detect nonvanishing of creation
monomials.

## The model

`WakFock = MvPolynomial (Fin 3 × ℕ) ℂ`, the three families of variables standing for the three
creation towers

* `X (0, i) = bᵢ₊₁` — the `β` mode `β₋₍ᵢ₊₁₎`,
* `X (1, j) = c_j`  — the `γ` mode `γ₋ⱼ`,
* `X (2, i) = Aᵢ₊₁` — the boson mode `a₋₍ᵢ₊₁₎`,

with free fields

```
[β_m, γ_n] = δ_{m+n,0},   [β,β] = [γ,γ] = 0,   [a_m, a_n] = 2(k+2)·m·δ_{m+n,0},   a₀ = 0,
```

`a` being the *rescaled* boson `a = √(2(k+2)) ∂φ`.  Rescaling is essential: it removes every
square root, so all structure constants are **polynomials in `k` with integer coefficients** and
the whole construction lives over `ℂ` with `k` a free parameter (at `k = -4/3` the naive
normalization would require `√(4/3)`).  The currents are

```
e_n = β_n,      h_n = -2·:βγ:_n + a_n,      f_n = -:βγγ:_n + :aγ:_n - k·n·γ_n .
```

## Method

The normal-ordered products `:βγ:`, `:γγ:`, `:aγ:`, `:βγγ:` are infinite but locally finite
operator sums, realized with `finsum` exactly as `Core.Dong.nprodCoeff` does (`opSum`,
`LocFin`).  Every commutator is then computed by pushing the bracket through the sum
(`opSum_lie`, `lie_opSum`) and collapsing it with the canonical commutators.

The three relations `[e,e]`, `[h,e]`, `[e,f]` come out directly from that table.  The remaining
three are closed by a **rigidity** argument instead of any explicit polynomial algebra: an
endomorphism commuting with every free-field mode is multiplication by a polynomial with all
partials zero, hence a scalar (`exists_smul_id_of_lie_modes`, needs `k + 2 ≠ 0`); a nonzero
eigenvalue under the charge grading `Dch` or the weight grading `Dwt` then forces it to vanish
(`eq_zero_of_lie_modes_of_eigen`).  Only one genuine arithmetic input survives — the central term
`[h_m, h_{-m}]|0⟩ = 2 k m |0⟩` (`Hcur_lie_Hcur_vac`).

## Main results

* `WakFock`, `Bet`, `Gam`, `Aos` — the carrier and the three free-field mode families;
  `Bet_Gam_lie`, `Aos_Aos_lie`, … — the complete canonical commutation relations.
* `Ecur`, `Hcur`, `Fcur` and their full commutator table against the free fields.
* `rel_ee`, `rel_he`, `rel_ef`, `rel_hh`, `rel_hf`, `rel_ff` — **all six affine `𝔰𝔩₂`
  relations**, at every non-critical level `k ≠ -2`; `rel_ef` and `rel_hh` carry the level.
* `Jw_comm` — the packaged form `[J^a_m, J^b_n] = ∑_c f^{ab}_c J^c_{m+n} + m k κ(a,b) δ`,
  the exact analogue of `AffineVOA.current_comm` but on a **free** module.
* `wakRho : 𝔰𝔩₂^ →ₗ⁅ℂ⁆ End ℂ WakFock` — the Wakimoto representation (`C ↦ k`, `ℓ₀ ↦ -Dwt`).
* `evAlgW`, `valW`, `valW_vacuumIdeal` — the induced evaluation `U(𝔰𝔩₂^) → WakFock`,
  `w ↦ ρ(w)|0⟩`, killing the whole vacuum ideal.
* `sl2Singular_ne_zero` — **the weight-3 singular vector of `V^{-4/3}(𝔰𝔩₂)` is nonzero**,
  proved `pbw`-free.  The separating functional is `γ₃` followed by the constant term:
  `γ₃ φ(s) = -8 ≠ 0` (`Gam3_valW_wSing`), from `γ₃ φ(M₁) = -1`, `γ₃ φ(M₃) = -2` and
  `γ₃ φ(M₂) = γ₃ φ(M₄) = γ₃ φ(M₅) = 0`.
* `M_indep_sing` — hence `M₁ … M₅` are linearly independent at `k = -4/3`, discharging the
  standing conditional `Sl2Indep.indep_iff_sl2Singular_ne_zero`.
* `vacuumA_ne_zero_free` — a `pbw`-free re-proof that `|0⟩ ≠ 0` in `V^k(𝔰𝔩₂)` for `k ≠ -2`.

## Status

Complete.  `sorry`-free, no `native_decide`, no new axioms.  `#print axioms` on
`sl2Singular_ne_zero`, `wakRho`, `rel_ff`, `rel_hh`, `vacuumA_ne_zero_free` gives
`[propext, Classical.choice, Quot.sound]` — **`pbw`-free**.  (`M_indep_sing` inherits
`VOA.pbw` only through the pre-existing bridge
`Sl2Indep.indep_iff_sl2Singular_ne_zero`, whose *other* direction uses `vacuumA_ne_zero`; the
nonvanishing statement itself is axiom-clean.)

## Caveat

Everything is proved for **non-critical level** `k + 2 ≠ 0`.  The hypothesis enters only through
the rigidity lemma, where the boson annihilators `a_u = 2(k+2)·u·∂_{A_u}` must be nonzero; at
`k = -4/3` it is discharged by `norm_num`.

## References
* Feigin–Frenkel, *A family of representations of affine Lie algebras*; Frenkel–Ben-Zvi,
  *Vertex algebras and algebraic curves*, Ch. 12 (Wakimoto modules);
* Gannon §3.2 (the affine bracket convention matched here);
* the `Examples/LeeYangSingular` §6 pattern (free-field model + evaluation functional).
-/

namespace VOA.Wak

open scoped BigOperators
open MvPolynomial

/-! ## §1  The Fock space and the elementary operators -/

/-- The **Wakimoto Fock space** `MvPolynomial (Fin 3 × ℕ) ℂ`.  Family `0` carries the `β`
creation modes, family `1` the `γ` creation modes, family `2` the boson creation modes. -/
abbrev WakFock : Type := MvPolynomial (Fin 3 × ℕ) ℂ

/-- Multiplication by a fixed polynomial, as an endomorphism. -/
noncomputable def mulL (Q : WakFock) : Module.End ℂ WakFock := LinearMap.mulLeft ℂ Q

@[simp] theorem mulL_apply (Q P : WakFock) : mulL Q P = Q * P := rfl

@[simp] theorem mulL_zero : mulL 0 = 0 := by
  refine LinearMap.ext fun P => ?_
  simp only [mulL_apply, zero_mul, LinearMap.zero_apply]

/-- Partial differentiation with respect to a variable, as an endomorphism. -/
noncomputable def dV (v : Fin 3 × ℕ) : Module.End ℂ WakFock := (pderiv v).toLinearMap

@[simp] theorem dV_apply (v : Fin 3 × ℕ) (P : WakFock) : dV v P = pderiv v P := rfl

/-- Multiplication operators commute (the Fock space is a commutative ring). -/
theorem mulL_lie_mulL (Q R : WakFock) : ⁅mulL Q, mulL R⁆ = 0 := by
  rw [Ring.lie_def]
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, mulL_apply, LinearMap.zero_apply]
  ring

/-- Antisymmetry of the commutator of endomorphisms, in rewrite-friendly form. -/
theorem lie_swap (A B : Module.End ℂ WakFock) : ⁅A, B⁆ = -⁅B, A⁆ := (lie_skew A B).symm

/-- Partial derivatives commute: mixed partials agree (Schwarz for formal polynomials). -/
theorem pderiv_comm' (v w : Fin 3 × ℕ) (P : WakFock) :
    pderiv v (pderiv w P) = pderiv w (pderiv v P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s h =>
    rw [pderiv_mul, pderiv_mul, map_add, map_add, pderiv_mul, pderiv_mul]
    simp only [pderiv_X, Pi.single_apply, h]
    by_cases hsv : s = v <;> by_cases hsw : s = w <;> simp_all <;> ring

/-- Differentiation operators commute. -/
theorem dV_lie_dV (v w : Fin 3 × ℕ) : ⁅dV v, dV w⁆ = 0 := by
  rw [Ring.lie_def]
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dV_apply, LinearMap.zero_apply]
  rw [pderiv_comm' v w P, sub_self]

/-- **The canonical commutator**: `[∂_v, X_w ·] = δ_{v,w}`. -/
theorem dV_lie_mulX (v w : Fin 3 × ℕ) :
    ⁅dV v, mulL (X w)⁆ = if v = w then (1 : Module.End ℂ WakFock) else 0 := by
  rw [Ring.lie_def]
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dV_apply, mulL_apply, pderiv_mul,
    pderiv_X, Pi.single_apply]
  by_cases h : v = w
  · subst h; simp
  · rw [if_neg h, if_neg (fun hc : w = v => h hc.symm)]
    simp

/-! ## §2  The `ℤ`-indexed variables and derivatives

Every mode index is an integer, and the "out of range" convention (a variable with a
non-positive label is `0`, the corresponding derivative is `0`) is built into the definitions.
This removes all `Int.toNat` bookkeeping from the statements downstream. -/

/-- The `β`-creation variable `bᵢ = β₋ᵢ`, extended by `0` for `i ≤ 0`. -/
noncomputable def bV (i : ℤ) : WakFock := if 1 ≤ i then X ((0 : Fin 3), (i - 1).toNat) else 0

/-- The `γ`-creation variable `c_j = γ₋ⱼ`, extended by `0` for `j < 0`. -/
noncomputable def cV (j : ℤ) : WakFock := if 0 ≤ j then X ((1 : Fin 3), j.toNat) else 0

/-- The boson creation variable `Aᵢ = a₋ᵢ`, extended by `0` for `i ≤ 0`. -/
noncomputable def aV (i : ℤ) : WakFock := if 1 ≤ i then X ((2 : Fin 3), (i - 1).toNat) else 0

/-- `∂/∂bᵢ`, extended by `0` for `i ≤ 0`. -/
noncomputable def bD (i : ℤ) : Module.End ℂ WakFock :=
  if 1 ≤ i then dV ((0 : Fin 3), (i - 1).toNat) else 0

/-- `∂/∂c_j`, extended by `0` for `j < 0`. -/
noncomputable def cD (j : ℤ) : Module.End ℂ WakFock :=
  if 0 ≤ j then dV ((1 : Fin 3), j.toNat) else 0

/-- `∂/∂Aᵢ`, extended by `0` for `i ≤ 0`. -/
noncomputable def aD (i : ℤ) : Module.End ℂ WakFock :=
  if 1 ≤ i then dV ((2 : Fin 3), (i - 1).toNat) else 0

theorem bV_of_pos {i : ℤ} (h : 1 ≤ i) : bV i = X ((0 : Fin 3), (i - 1).toNat) := if_pos h
theorem bV_of_nonpos {i : ℤ} (h : i ≤ 0) : bV i = 0 := if_neg (by omega)
theorem cV_of_nonneg {j : ℤ} (h : 0 ≤ j) : cV j = X ((1 : Fin 3), j.toNat) := if_pos h
theorem cV_of_neg {j : ℤ} (h : j < 0) : cV j = 0 := if_neg (by omega)
theorem aV_of_pos {i : ℤ} (h : 1 ≤ i) : aV i = X ((2 : Fin 3), (i - 1).toNat) := if_pos h
theorem aV_of_nonpos {i : ℤ} (h : i ≤ 0) : aV i = 0 := if_neg (by omega)
theorem bD_of_pos {i : ℤ} (h : 1 ≤ i) : bD i = dV ((0 : Fin 3), (i - 1).toNat) := if_pos h
theorem bD_of_nonpos {i : ℤ} (h : i ≤ 0) : bD i = 0 := if_neg (by omega)
theorem cD_of_nonneg {j : ℤ} (h : 0 ≤ j) : cD j = dV ((1 : Fin 3), j.toNat) := if_pos h
theorem cD_of_neg {j : ℤ} (h : j < 0) : cD j = 0 := if_neg (by omega)
theorem aD_of_pos {i : ℤ} (h : 1 ≤ i) : aD i = dV ((2 : Fin 3), (i - 1).toNat) := if_pos h
theorem aD_of_nonpos {i : ℤ} (h : i ≤ 0) : aD i = 0 := if_neg (by omega)

/-- `[∂/∂bᵢ, bⱼ·] = δ_{ij}` (both labels in range; out-of-range labels give `0` on both sides). -/
theorem bD_lie_bV (i j : ℤ) :
    ⁅bD i, mulL (bV j)⁆ = if (1 ≤ i ∧ i = j) then (1 : Module.End ℂ WakFock) else 0 := by
  by_cases hi : 1 ≤ i
  · rw [bD_of_pos hi]
    by_cases hj : 1 ≤ j
    · rw [bV_of_pos hj, dV_lie_mulX]
      by_cases h : i = j
      · subst h; simp [hi]
      · rw [if_neg (by simp only [Prod.mk.injEq, true_and]; omega), if_neg (by tauto)]
    · rw [bV_of_nonpos (by omega), mulL_zero, lie_zero, if_neg (by omega)]
  · rw [bD_of_nonpos (by omega), zero_lie, if_neg (by tauto)]

/-- `[∂/∂c_j, c_l·] = δ_{jl}`. -/
theorem cD_lie_cV (j l : ℤ) :
    ⁅cD j, mulL (cV l)⁆ = if (0 ≤ j ∧ j = l) then (1 : Module.End ℂ WakFock) else 0 := by
  by_cases hj : 0 ≤ j
  · rw [cD_of_nonneg hj]
    by_cases hl : 0 ≤ l
    · rw [cV_of_nonneg hl, dV_lie_mulX]
      by_cases h : j = l
      · subst h; simp [hj]
      · rw [if_neg (by simp only [Prod.mk.injEq, true_and]; omega), if_neg (by tauto)]
    · rw [cV_of_neg (by omega), mulL_zero, lie_zero, if_neg (by omega)]
  · rw [cD_of_neg (by omega), zero_lie, if_neg (by tauto)]

/-- `[∂/∂Aᵢ, Aⱼ·] = δ_{ij}`. -/
theorem aD_lie_aV (i j : ℤ) :
    ⁅aD i, mulL (aV j)⁆ = if (1 ≤ i ∧ i = j) then (1 : Module.End ℂ WakFock) else 0 := by
  by_cases hi : 1 ≤ i
  · rw [aD_of_pos hi]
    by_cases hj : 1 ≤ j
    · rw [aV_of_pos hj, dV_lie_mulX]
      by_cases h : i = j
      · subst h; simp [hi]
      · rw [if_neg (by simp only [Prod.mk.injEq, true_and]; omega), if_neg (by tauto)]
    · rw [aV_of_nonpos (by omega), mulL_zero, lie_zero, if_neg (by omega)]
  · rw [aD_of_nonpos (by omega), zero_lie, if_neg (by tauto)]

/-- Derivatives from different families annihilate each other's variables (`b` vs `c`). -/
theorem bD_lie_cV (i j : ℤ) : ⁅bD i, mulL (cV j)⁆ = 0 := by
  by_cases hi : 1 ≤ i
  · by_cases hj : 0 ≤ j
    · rw [bD_of_pos hi, cV_of_nonneg hj, dV_lie_mulX, if_neg (by simp)]
    · rw [cV_of_neg (by omega), mulL_zero, lie_zero]
  · rw [bD_of_nonpos (by omega), zero_lie]

/-- Derivatives from different families annihilate each other's variables (`b` vs `A`). -/
theorem bD_lie_aV (i j : ℤ) : ⁅bD i, mulL (aV j)⁆ = 0 := by
  by_cases hi : 1 ≤ i
  · by_cases hj : 1 ≤ j
    · rw [bD_of_pos hi, aV_of_pos hj, dV_lie_mulX, if_neg (by simp)]
    · rw [aV_of_nonpos (by omega), mulL_zero, lie_zero]
  · rw [bD_of_nonpos (by omega), zero_lie]

/-- Derivatives from different families annihilate each other's variables (`c` vs `b`). -/
theorem cD_lie_bV (i j : ℤ) : ⁅cD i, mulL (bV j)⁆ = 0 := by
  by_cases hi : 0 ≤ i
  · by_cases hj : 1 ≤ j
    · rw [cD_of_nonneg hi, bV_of_pos hj, dV_lie_mulX, if_neg (by simp)]
    · rw [bV_of_nonpos (by omega), mulL_zero, lie_zero]
  · rw [cD_of_neg (by omega), zero_lie]

/-- Derivatives from different families annihilate each other's variables (`c` vs `A`). -/
theorem cD_lie_aV (i j : ℤ) : ⁅cD i, mulL (aV j)⁆ = 0 := by
  by_cases hi : 0 ≤ i
  · by_cases hj : 1 ≤ j
    · rw [cD_of_nonneg hi, aV_of_pos hj, dV_lie_mulX, if_neg (by simp)]
    · rw [aV_of_nonpos (by omega), mulL_zero, lie_zero]
  · rw [cD_of_neg (by omega), zero_lie]

/-- Derivatives from different families annihilate each other's variables (`A` vs `b`). -/
theorem aD_lie_bV (i j : ℤ) : ⁅aD i, mulL (bV j)⁆ = 0 := by
  by_cases hi : 1 ≤ i
  · by_cases hj : 1 ≤ j
    · rw [aD_of_pos hi, bV_of_pos hj, dV_lie_mulX, if_neg (by simp)]
    · rw [bV_of_nonpos (by omega), mulL_zero, lie_zero]
  · rw [aD_of_nonpos (by omega), zero_lie]

/-- Derivatives from different families annihilate each other's variables (`A` vs `c`). -/
theorem aD_lie_cV (i j : ℤ) : ⁅aD i, mulL (cV j)⁆ = 0 := by
  by_cases hi : 1 ≤ i
  · by_cases hj : 0 ≤ j
    · rw [aD_of_pos hi, cV_of_nonneg hj, dV_lie_mulX, if_neg (by simp)]
    · rw [cV_of_neg (by omega), mulL_zero, lie_zero]
  · rw [aD_of_nonpos (by omega), zero_lie]

/-- Any two of the elementary derivative operators commute. -/
theorem D_lie_D (D₁ D₂ : Module.End ℂ WakFock)
    (h₁ : ∃ v, D₁ = dV v ∨ D₁ = 0) (h₂ : ∃ w, D₂ = dV w ∨ D₂ = 0) : ⁅D₁, D₂⁆ = 0 := by
  obtain ⟨v, hv⟩ := h₁; obtain ⟨w, hw⟩ := h₂
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
    simp [dV_lie_dV]

theorem bD_isD (i : ℤ) : ∃ v, bD i = dV v ∨ bD i = 0 := by
  by_cases h : 1 ≤ i
  · exact ⟨_, Or.inl (bD_of_pos h)⟩
  · exact ⟨((0 : Fin 3), 0), Or.inr (bD_of_nonpos (by omega))⟩

theorem cD_isD (i : ℤ) : ∃ v, cD i = dV v ∨ cD i = 0 := by
  by_cases h : 0 ≤ i
  · exact ⟨_, Or.inl (cD_of_nonneg h)⟩
  · exact ⟨((1 : Fin 3), 0), Or.inr (cD_of_neg (by omega))⟩

theorem aD_isD (i : ℤ) : ∃ v, aD i = dV v ∨ aD i = 0 := by
  by_cases h : 1 ≤ i
  · exact ⟨_, Or.inl (aD_of_pos h)⟩
  · exact ⟨((2 : Fin 3), 0), Or.inr (aD_of_nonpos (by omega))⟩

/-! ## §3  The free-field modes -/

/-- The `β` mode `β_m`: multiplication by `b₋ₘ` for `m ≤ -1`, `∂/∂c_m` for `m ≥ 0`. -/
noncomputable def Bet (m : ℤ) : Module.End ℂ WakFock :=
  if m ≤ -1 then mulL (bV (-m)) else cD m

/-- The `γ` mode `γ_n`: multiplication by `c₋ₙ` for `n ≤ 0`, `-∂/∂b_n` for `n ≥ 1`. -/
noncomputable def Gam (n : ℤ) : Module.End ℂ WakFock :=
  if n ≤ 0 then mulL (cV (-n)) else -(bD n)

/-- The rescaled boson mode `a_m` at level `k`: multiplication by `A₋ₘ` for `m ≤ -1`, and
`2(k+2)·m·∂/∂A_m` for `m ≥ 0` (in particular `a₀ = 0`). -/
noncomputable def Aos (k : ℂ) (m : ℤ) : Module.End ℂ WakFock :=
  if m ≤ -1 then mulL (aV (-m)) else ((2 * (k + 2)) * (m : ℂ)) • aD m

theorem Bet_of_neg {m : ℤ} (h : m ≤ -1) : Bet m = mulL (bV (-m)) := if_pos h
theorem Bet_of_nonneg {m : ℤ} (h : 0 ≤ m) : Bet m = cD m := if_neg (by omega)
theorem Gam_of_nonpos {n : ℤ} (h : n ≤ 0) : Gam n = mulL (cV (-n)) := if_pos h
theorem Gam_of_pos {n : ℤ} (h : 1 ≤ n) : Gam n = -(bD n) := if_neg (by omega)
theorem Aos_of_neg (k : ℂ) {m : ℤ} (h : m ≤ -1) : Aos k m = mulL (aV (-m)) := if_pos h
theorem Aos_of_nonneg (k : ℂ) {m : ℤ} (h : 0 ≤ m) :
    Aos k m = ((2 * (k + 2)) * (m : ℂ)) • aD m := if_neg (by omega)

/-- **`[β_m, γ_n] = δ_{m+n,0}`** — the canonical `βγ` commutation relation, all modes. -/
theorem Bet_Gam_lie (m n : ℤ) :
    ⁅Bet m, Gam n⁆ = if m + n = 0 then (1 : Module.End ℂ WakFock) else 0 := by
  by_cases hm : m ≤ -1
  · rw [Bet_of_neg hm]
    by_cases hn : n ≤ 0
    · rw [Gam_of_nonpos hn, mulL_lie_mulL, if_neg (by omega)]
    · rw [Gam_of_pos (by omega), lie_neg, lie_swap (mulL (bV (-m))) (bD n), neg_neg, bD_lie_bV]
      by_cases h : m + n = 0
      · rw [if_pos h, if_pos ⟨by omega, by omega⟩]
      · rw [if_neg h, if_neg (by omega)]
  · rw [Bet_of_nonneg (by omega)]
    by_cases hn : n ≤ 0
    · rw [Gam_of_nonpos hn, cD_lie_cV]
      by_cases h : m + n = 0
      · rw [if_pos h, if_pos ⟨by omega, by omega⟩]
      · rw [if_neg h, if_neg (by omega)]
    · rw [Gam_of_pos (by omega), lie_neg, D_lie_D _ _ (cD_isD m) (bD_isD n), neg_zero,
        if_neg (by omega)]

/-- **`[β_m, β_n] = 0`**. -/
theorem Bet_Bet_lie (m n : ℤ) : ⁅Bet m, Bet n⁆ = 0 := by
  by_cases hm : m ≤ -1 <;> by_cases hn : n ≤ -1
  · rw [Bet_of_neg hm, Bet_of_neg hn, mulL_lie_mulL]
  · rw [Bet_of_neg hm, Bet_of_nonneg (by omega),
      lie_swap (mulL (bV (-m))) (cD n), cD_lie_bV, neg_zero]
  · rw [Bet_of_nonneg (by omega), Bet_of_neg hn, cD_lie_bV]
  · rw [Bet_of_nonneg (by omega), Bet_of_nonneg (by omega), D_lie_D _ _ (cD_isD m) (cD_isD n)]

/-- **`[γ_m, γ_n] = 0`**. -/
theorem Gam_Gam_lie (m n : ℤ) : ⁅Gam m, Gam n⁆ = 0 := by
  by_cases hm : m ≤ 0 <;> by_cases hn : n ≤ 0
  · rw [Gam_of_nonpos hm, Gam_of_nonpos hn, mulL_lie_mulL]
  · rw [Gam_of_nonpos hm, Gam_of_pos (by omega), lie_neg,
      lie_swap (mulL (cV (-m))) (bD n), bD_lie_cV, neg_zero, neg_zero]
  · rw [Gam_of_pos (by omega), Gam_of_nonpos hn, neg_lie, bD_lie_cV, neg_zero]
  · rw [Gam_of_pos (by omega), Gam_of_pos (by omega), neg_lie, lie_neg,
      D_lie_D _ _ (bD_isD m) (bD_isD n), neg_zero, neg_zero]

/-- **`[a_m, a_n] = 2(k+2)·m·δ_{m+n,0}`** — the rescaled Heisenberg relation. -/
theorem Aos_Aos_lie (k : ℂ) (m n : ℤ) :
    ⁅Aos k m, Aos k n⁆
      = if m + n = 0 then ((2 * (k + 2)) * (m : ℂ)) • (1 : Module.End ℂ WakFock) else 0 := by
  by_cases hm : m ≤ -1 <;> by_cases hn : n ≤ -1
  · rw [Aos_of_neg k hm, Aos_of_neg k hn, mulL_lie_mulL, if_neg (by omega)]
  · rw [Aos_of_neg k hm, Aos_of_nonneg k (by omega), lie_smul,
      lie_swap (mulL (aV (-m))) (aD n), aD_lie_aV]
    by_cases h : m + n = 0
    · rw [if_pos h, if_pos ⟨by omega, by omega⟩]
      have hnm : (n : ℂ) = -(m : ℂ) := by
        have hnm' : n = -m := by omega
        rw [hnm']; push_cast; ring
      rw [hnm]; module
    · rw [if_neg h, if_neg (by omega), neg_zero, smul_zero]
  · rw [Aos_of_nonneg k (by omega), Aos_of_neg k hn, smul_lie, aD_lie_aV]
    by_cases h : m + n = 0
    · rw [if_pos h, if_pos ⟨by omega, by omega⟩]
    · rw [if_neg h, if_neg (by omega), smul_zero]
  · rw [Aos_of_nonneg k (by omega), Aos_of_nonneg k (by omega), smul_lie, lie_smul,
      D_lie_D _ _ (aD_isD m) (aD_isD n), smul_zero, smul_zero]
    by_cases h : m + n = 0
    · have hm0 : m = 0 := by omega
      rw [if_pos h, hm0]
      simp
    · rw [if_neg h]

/-- **`[a_m, β_n] = 0`** — the boson decouples from the `βγ` system. -/
theorem Aos_Bet_lie (k : ℂ) (m n : ℤ) : ⁅Aos k m, Bet n⁆ = 0 := by
  by_cases hm : m ≤ -1 <;> by_cases hn : n ≤ -1
  · rw [Aos_of_neg k hm, Bet_of_neg hn, mulL_lie_mulL]
  · rw [Aos_of_neg k hm, Bet_of_nonneg (by omega),
      lie_swap (mulL (aV (-m))) (cD n), cD_lie_aV, neg_zero]
  · rw [Aos_of_nonneg k (by omega), Bet_of_neg hn, smul_lie, aD_lie_bV, smul_zero]
  · rw [Aos_of_nonneg k (by omega), Bet_of_nonneg (by omega), smul_lie,
      D_lie_D _ _ (aD_isD m) (cD_isD n), smul_zero]

/-- **`[a_m, γ_n] = 0`**. -/
theorem Aos_Gam_lie (k : ℂ) (m n : ℤ) : ⁅Aos k m, Gam n⁆ = 0 := by
  by_cases hm : m ≤ -1 <;> by_cases hn : n ≤ 0
  · rw [Aos_of_neg k hm, Gam_of_nonpos hn, mulL_lie_mulL]
  · rw [Aos_of_neg k hm, Gam_of_pos (by omega), lie_neg,
      lie_swap (mulL (aV (-m))) (bD n), bD_lie_aV, neg_zero, neg_zero]
  · rw [Aos_of_nonneg k (by omega), Gam_of_nonpos hn, smul_lie, aD_lie_cV, smul_zero]
  · rw [Aos_of_nonneg k (by omega), Gam_of_pos (by omega), smul_lie, lie_neg,
      D_lie_D _ _ (aD_isD m) (bD_isD n), neg_zero, smul_zero]

/-! ## §4  The vacuum -/

/-- The non-negative `β` modes annihilate the vacuum `1`. -/
theorem Bet_one {m : ℤ} (h : 0 ≤ m) : Bet m (1 : WakFock) = 0 := by
  rw [Bet_of_nonneg h, cD_of_nonneg h, dV_apply, pderiv_one]

/-- The strictly positive `γ` modes annihilate the vacuum `1`. -/
theorem Gam_one {n : ℤ} (h : 1 ≤ n) : Gam n (1 : WakFock) = 0 := by
  rw [Gam_of_pos h, bD_of_pos h]
  simp

/-- The non-negative boson modes annihilate the vacuum `1`. -/
theorem Aos_one (k : ℂ) {m : ℤ} (h : 0 ≤ m) : Aos k m (1 : WakFock) = 0 := by
  rw [Aos_of_nonneg k h]
  by_cases h1 : 1 ≤ m
  · rw [aD_of_pos h1]; simp
  · rw [aD_of_nonpos (by omega)]; simp

/-- The creation `β` modes applied to the vacuum give the variables. -/
theorem Bet_one_neg {m : ℤ} (h : m ≤ -1) : Bet m (1 : WakFock) = bV (-m) := by
  rw [Bet_of_neg h, mulL_apply, mul_one]

/-- The creation `γ` modes applied to the vacuum give the variables. -/
theorem Gam_one_nonpos {n : ℤ} (h : n ≤ 0) : Gam n (1 : WakFock) = cV (-n) := by
  rw [Gam_of_nonpos h, mulL_apply, mul_one]

/-- The creation boson modes applied to the vacuum give the variables. -/
theorem Aos_one_neg (k : ℂ) {m : ℤ} (h : m ≤ -1) : Aos k m (1 : WakFock) = aV (-m) := by
  rw [Aos_of_neg k h, mulL_apply, mul_one]


/-! ## §5  Truncation bounds

Every annihilation mode with a sufficiently large index kills a given polynomial, because a
polynomial involves only finitely many variables.  This is what makes the normal-ordered mode
sums of §7 locally finite. -/

/-- The **mode cutoff** of a polynomial: every annihilation mode with index `≥ NB P` kills `P`. -/
noncomputable def NB (P : WakFock) : ℤ := ((P.vars.sup fun v => v.2 : ℕ) : ℤ) + 2

theorem two_le_NB (P : WakFock) : 2 ≤ NB P := by
  have h : (0 : ℤ) ≤ ((P.vars.sup fun v => v.2 : ℕ) : ℤ) := Int.natCast_nonneg _
  simp only [NB]; omega

/-- Variables above the cutoff do not occur, so their derivatives vanish. -/
theorem pderiv_eq_zero_of_NB_le {P : WakFock} {a : Fin 3} {i : ℕ} (h : NB P ≤ (i : ℤ) + 1) :
    pderiv (a, i) P = 0 := by
  refine pderiv_eq_zero_of_notMem_vars ?_
  intro hmem
  have hle0 : (fun v : Fin 3 × ℕ => v.2) (a, i) ≤ P.vars.sup (fun v : Fin 3 × ℕ => v.2) :=
    Finset.le_sup hmem
  have hle : i ≤ P.vars.sup (fun v : Fin 3 × ℕ => v.2) := hle0
  simp only [NB] at h
  omega

/-- `β_m` annihilates `P` once `m ≥ NB P`. -/
theorem Bet_apply_eq_zero {P : WakFock} {m : ℤ} (h : NB P ≤ m) : Bet m P = 0 := by
  have h2 := two_le_NB P
  rw [Bet_of_nonneg (by omega), cD_of_nonneg (by omega), dV_apply]
  exact pderiv_eq_zero_of_NB_le (by omega)

/-- `γ_n` annihilates `P` once `n ≥ NB P`. -/
theorem Gam_apply_eq_zero {P : WakFock} {n : ℤ} (h : NB P ≤ n) : Gam n P = 0 := by
  have h2 := two_le_NB P
  rw [Gam_of_pos (by omega), bD_of_pos (by omega)]
  simp only [LinearMap.neg_apply, dV_apply, neg_eq_zero]
  exact pderiv_eq_zero_of_NB_le (by omega)

/-- `a_m` annihilates `P` once `m ≥ NB P`. -/
theorem Aos_apply_eq_zero (k : ℂ) {P : WakFock} {m : ℤ} (h : NB P ≤ m) : Aos k m P = 0 := by
  have h2 := two_le_NB P
  rw [Aos_of_nonneg k (by omega), aD_of_pos (by omega)]
  simp only [LinearMap.smul_apply, dV_apply]
  rw [pderiv_eq_zero_of_NB_le (by omega), smul_zero]

/-! ## §6  Locally finite operator sums

The normal-ordered products of free fields are infinite sums of operators which, applied to any
fixed polynomial, have only finitely many nonzero terms.  We realize them with `finsum`, exactly
as `Core.Dong.nprodCoeff` does for the same-variable normal product. -/

/-- A `ℤ`-indexed family of operators is **locally finite** when, on each vector, only finitely
many members are nonzero. -/
def LocFin (T : ℤ → Module.End ℂ WakFock) : Prop :=
  ∀ P : WakFock, (Function.support fun p : ℤ => T p P).Finite

open Classical in
/-- The operator sum `∑ᶠ p, T p` of a locally finite family (junk value `0` otherwise). -/
noncomputable def opSum (T : ℤ → Module.End ℂ WakFock) : Module.End ℂ WakFock :=
  if h : LocFin T then
    { toFun := fun P => ∑ᶠ p : ℤ, T p P
      map_add' := fun P Q => by
        rw [← finsum_add_distrib (h P) (h Q)]
        exact finsum_congr fun p => map_add _ P Q
      map_smul' := fun c P => by
        rw [RingHom.id_apply, smul_finsum' c (h P)]
        exact finsum_congr fun p => map_smul _ c P }
  else 0

theorem opSum_apply {T : ℤ → Module.End ℂ WakFock} (h : LocFin T) (P : WakFock) :
    opSum T P = ∑ᶠ p : ℤ, T p P := by
  rw [opSum, dif_pos h]; rfl

/-- Local finiteness from an explicit two-sided index bound. -/
theorem locFin_of_bounds {T : ℤ → Module.End ℂ WakFock}
    (H : ∀ P : WakFock, ∃ A B : ℤ, ∀ p : ℤ, (p < A ∨ B < p) → T p P = 0) : LocFin T := by
  intro P
  obtain ⟨A, B, hAB⟩ := H P
  refine Set.Finite.subset (Set.finite_Icc A B) ?_
  intro p hp
  simp only [Function.mem_support] at hp
  rw [Set.mem_Icc]
  by_contra hc
  exact hp (hAB p (by omega))

/-- A family supported at a single index is locally finite. -/
theorem locFin_ite (p₀ : ℤ) (A : Module.End ℂ WakFock) :
    LocFin (fun p => if p = p₀ then A else 0) := by
  refine locFin_of_bounds fun P => ⟨p₀, p₀, fun p hp => ?_⟩
  rw [if_neg (show ¬ p = p₀ by omega)]
  simp

/-- The operator sum of a family supported at a single index. -/
theorem opSum_ite (p₀ : ℤ) (A : Module.End ℂ WakFock) :
    opSum (fun p => if p = p₀ then A else 0) = A := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (locFin_ite p₀ A) P,
    finsum_eq_single _ p₀ (fun x hx => by rw [if_neg hx]; rfl), if_pos rfl]

/-- Local finiteness is preserved by pointwise addition. -/
theorem LocFin.add {T U : ℤ → Module.End ℂ WakFock} (hT : LocFin T) (hU : LocFin U) :
    LocFin (fun p => T p + U p) := by
  intro P
  refine Set.Finite.subset ((hT P).union (hU P)) ?_
  intro p hp
  simp only [Function.mem_support, LinearMap.add_apply] at hp
  by_contra hc
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
  exact hp (by rw [hc.1, hc.2, add_zero])

/-- Local finiteness is preserved by scaling. -/
theorem LocFin.smul (c : ℂ) {T : ℤ → Module.End ℂ WakFock} (hT : LocFin T) :
    LocFin (fun p => c • T p) := by
  intro P
  refine Set.Finite.subset (hT P) ?_
  intro p hp
  simp only [Function.mem_support, LinearMap.smul_apply] at hp ⊢
  intro hz; exact hp (by rw [hz, smul_zero])

/-- Operator sums are additive. -/
theorem opSum_add {T U : ℤ → Module.End ℂ WakFock} (hT : LocFin T) (hU : LocFin U) :
    opSum (fun p => T p + U p) = opSum T + opSum U := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (hT.add hU) P]
  simp only [LinearMap.add_apply]
  rw [opSum_apply hT P, opSum_apply hU P, ← finsum_add_distrib (hT P) (hU P)]

/-- Operator sums commute with scaling. -/
theorem opSum_smul (c : ℂ) {T : ℤ → Module.End ℂ WakFock} (hT : LocFin T) :
    opSum (fun p => c • T p) = c • opSum T := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (hT.smul c) P, LinearMap.smul_apply, opSum_apply hT P,
    smul_finsum' c (hT P)]
  exact finsum_congr fun p => rfl

/-- **The commutator passes through an operator sum.** -/
theorem opSum_lie {T : ℤ → Module.End ℂ WakFock} (hT : LocFin T) (S : Module.End ℂ WakFock)
    (h' : LocFin fun p => ⁅T p, S⁆) : ⁅opSum T, S⁆ = opSum (fun p => ⁅T p, S⁆) := by
  refine LinearMap.ext fun P => ?_
  have hs : (Function.support fun p : ℤ => S (T p P)).Finite := by
    refine Set.Finite.subset (hT P) ?_
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    intro hz; exact hp (by rw [hz, map_zero])
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [opSum_apply hT (S P), opSum_apply hT P, opSum_apply h' P, map_finsum S (hT P),
    ← finsum_sub_distrib (hT (S P)) hs]
  refine finsum_congr fun p => ?_
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]

/-- Leibniz rule for the commutator in the left slot. -/
theorem lie_mul_left (A B C : Module.End ℂ WakFock) :
    ⁅A * B, C⁆ = A * ⁅B, C⁆ + ⁅A, C⁆ * B := by
  simp only [Ring.lie_def]; noncomm_ring

/-- Leibniz rule for the commutator in the right slot. -/
theorem lie_mul_right (A B C : Module.End ℂ WakFock) :
    ⁅A, B * C⁆ = ⁅A, B⁆ * C + B * ⁅A, C⁆ := by
  simp only [Ring.lie_def]; noncomm_ring

/-- `γ` modes commute, in multiplicative form. -/
theorem Gam_comm (m n : ℤ) : Gam m * Gam n = Gam n * Gam m := by
  have h := Gam_Gam_lie m n
  rw [Ring.lie_def, sub_eq_zero] at h
  exact h

/-! ## §7  The normal-ordered composite modes

`:βγ:_n`, `:γγ:_s`, `:aγ:_n` and `:βγγ:_n`, each as a locally finite operator sum with the
creation modes standing to the left. -/

/-- The summand family of `:βγ:_n`. -/
noncomputable def bgFam (n p : ℤ) : Module.End ℂ WakFock :=
  if p ≤ -1 then Bet p * Gam (n - p) else Gam (n - p) * Bet p

/-- The summand family of `:γγ:_s`. -/
noncomputable def ggFam (s q : ℤ) : Module.End ℂ WakFock :=
  if q ≤ 0 then Gam q * Gam (s - q) else Gam (s - q) * Gam q

/-- The summand family of `:aγ:_n`. -/
noncomputable def agFam (k : ℂ) (n p : ℤ) : Module.End ℂ WakFock :=
  if p ≤ -1 then Aos k p * Gam (n - p) else Gam (n - p) * Aos k p

theorem bgFam_locFin (n : ℤ) : LocFin (bgFam n) := by
  refine locFin_of_bounds fun P => ⟨min (n - NB P + 1) 0, NB P - 1, fun p hp => ?_⟩
  have h2 := two_le_NB P
  rcases hp with hp | hp
  · rw [bgFam, if_pos (by omega), Module.End.mul_apply, Gam_apply_eq_zero (by omega), map_zero]
  · rw [bgFam, if_neg (by omega), Module.End.mul_apply, Bet_apply_eq_zero (by omega), map_zero]

theorem ggFam_locFin (s : ℤ) : LocFin (ggFam s) := by
  refine locFin_of_bounds fun P => ⟨min (s - NB P + 1) 0, NB P - 1, fun q hq => ?_⟩
  have h2 := two_le_NB P
  rcases hq with hq | hq
  · rw [ggFam, if_pos (show q ≤ 0 by omega), Module.End.mul_apply,
      Gam_apply_eq_zero (P := P) (n := s - q) (by omega), map_zero]
  · rw [ggFam, if_neg (show ¬ q ≤ 0 by omega), Module.End.mul_apply,
      Gam_apply_eq_zero (P := P) (n := q) (by omega), map_zero]

theorem agFam_locFin (k : ℂ) (n : ℤ) : LocFin (agFam k n) := by
  refine locFin_of_bounds fun P => ⟨min (n - NB P + 1) 0, NB P - 1, fun p hp => ?_⟩
  have h2 := two_le_NB P
  rcases hp with hp | hp
  · rw [agFam, if_pos (by omega), Module.End.mul_apply, Gam_apply_eq_zero (by omega), map_zero]
  · rw [agFam, if_neg (by omega), Module.End.mul_apply, Aos_apply_eq_zero k (by omega), map_zero]

/-- The normal-ordered product `:βγ:_n`. -/
noncomputable def BG (n : ℤ) : Module.End ℂ WakFock := opSum (bgFam n)

/-- The product `:γγ:_s` (the `γ`'s commute, so only the relative order with `β` matters). -/
noncomputable def GG (s : ℤ) : Module.End ℂ WakFock := opSum (ggFam s)

/-- The normal-ordered product `:aγ:_n`. -/
noncomputable def AG (k : ℂ) (n : ℤ) : Module.End ℂ WakFock := opSum (agFam k n)

/-- `:γγ:_s` annihilates `P` once `s ≥ 2·NB P`. -/
theorem GG_apply_eq_zero {P : WakFock} {s : ℤ} (h : 2 * NB P ≤ s) : GG s P = 0 := by
  have h2 := two_le_NB P
  rw [GG, opSum_apply (ggFam_locFin s) P]
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  by_cases hq : q ≤ 0
  · rw [ggFam, if_pos hq, Module.End.mul_apply,
      Gam_apply_eq_zero (P := P) (n := s - q) (by omega), map_zero]
  · by_cases hq2 : NB P ≤ q
    · rw [ggFam, if_neg hq, Module.End.mul_apply,
        Gam_apply_eq_zero (P := P) (n := q) hq2, map_zero]
    · rw [ggFam, if_neg hq, Gam_comm, Module.End.mul_apply,
        Gam_apply_eq_zero (P := P) (n := s - q) (by omega), map_zero]

/-- The summand family of `:βγγ:_n`. -/
noncomputable def bggFam (n p : ℤ) : Module.End ℂ WakFock :=
  if p ≤ -1 then Bet p * GG (n - p) else GG (n - p) * Bet p

theorem bggFam_locFin (n : ℤ) : LocFin (bggFam n) := by
  refine locFin_of_bounds fun P => ⟨min (n - 2 * NB P + 1) 0, NB P - 1, fun p hp => ?_⟩
  have h2 := two_le_NB P
  rcases hp with hp | hp
  · rw [bggFam, if_pos (by omega), Module.End.mul_apply, GG_apply_eq_zero (by omega), map_zero]
  · rw [bggFam, if_neg (by omega), Module.End.mul_apply, Bet_apply_eq_zero (by omega), map_zero]

/-- The normal-ordered product `:βγγ:_n`. -/
noncomputable def BGG (n : ℤ) : Module.End ℂ WakFock := opSum (bggFam n)


/-! ## §8  The commutator table of the composites against the free fields

Every one of these is proved by pushing the commutator through the operator sum
(`opSum_lie`), applying the Leibniz rule to each summand, and observing that the canonical
commutators collapse the sum to one or two surviving terms. -/

theorem locFin_zero : LocFin (fun _ : ℤ => (0 : Module.End ℂ WakFock)) :=
  locFin_of_bounds fun _ => ⟨0, 0, fun _ _ => rfl⟩

theorem opSum_zero : opSum (fun _ : ℤ => (0 : Module.End ℂ WakFock)) = 0 := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply locFin_zero P]
  simp

/-- `[γ_n, β_m] = -δ_{m+n,0}`. -/
theorem Gam_Bet_lie (m n : ℤ) :
    ⁅Gam n, Bet m⁆ = -(if m + n = 0 then (1 : Module.End ℂ WakFock) else 0) := by
  rw [lie_swap, Bet_Gam_lie]

/-- `[γ_n, a_m] = 0`. -/
theorem Gam_Aos_lie (k : ℂ) (n m : ℤ) : ⁅Gam n, Aos k m⁆ = 0 := by
  rw [lie_swap, Aos_Gam_lie, neg_zero]

/-- `[β_n, a_m] = 0`. -/
theorem Bet_Aos_lie (k : ℂ) (n m : ℤ) : ⁅Bet n, Aos k m⁆ = 0 := by
  rw [lie_swap, Aos_Bet_lie, neg_zero]

/-- `[:βγ:_n, β_r] = -β_{n+r}`. -/
theorem BG_lie_Bet (n r : ℤ) : ⁅BG n, Bet r⁆ = -Bet (n + r) := by
  have hfam : (fun p => ⁅bgFam n p, Bet r⁆)
      = fun p => if p = n + r then -Bet (n + r) else 0 := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_left, Bet_Bet_lie, zero_mul, add_zero, Gam_Bet_lie]
      by_cases h : p = n + r
      · rw [if_pos (show r + (n - p) = 0 by omega), if_pos h, mul_neg, mul_one, h]
      · rw [if_neg (show ¬ (r + (n - p) = 0) by omega), if_neg h, neg_zero, mul_zero]
    · rw [bgFam, if_neg hp, lie_mul_left, Bet_Bet_lie, mul_zero, zero_add, Gam_Bet_lie]
      by_cases h : p = n + r
      · rw [if_pos (show r + (n - p) = 0 by omega), if_pos h, neg_mul, one_mul, h]
      · rw [if_neg (show ¬ (r + (n - p) = 0) by omega), if_neg h, neg_zero, zero_mul]
  rw [BG, opSum_lie (bgFam_locFin n) (Bet r) (by rw [hfam]; exact locFin_ite _ _), hfam,
    opSum_ite]

/-- `[:βγ:_n, γ_u] = γ_{n+u}`. -/
theorem BG_lie_Gam (n u : ℤ) : ⁅BG n, Gam u⁆ = Gam (n + u) := by
  have hfam : (fun p => ⁅bgFam n p, Gam u⁆)
      = fun p => if p = -u then Gam (n + u) else 0 := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_left, Gam_Gam_lie, mul_zero, zero_add, Bet_Gam_lie]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, one_mul,
          show n - p = n + u by omega]
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, zero_mul]
    · rw [bgFam, if_neg hp, lie_mul_left, Gam_Gam_lie, zero_mul, add_zero, Bet_Gam_lie]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, mul_one,
          show n - p = n + u by omega]
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, mul_zero]
  rw [BG, opSum_lie (bgFam_locFin n) (Gam u) (by rw [hfam]; exact locFin_ite _ _), hfam,
    opSum_ite]

/-- `[:βγ:_n, a_u] = 0`. -/
theorem BG_lie_Aos (k : ℂ) (n u : ℤ) : ⁅BG n, Aos k u⁆ = 0 := by
  have hfam : (fun p => ⁅bgFam n p, Aos k u⁆) = fun _ => (0 : Module.End ℂ WakFock) := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_left, Gam_Aos_lie, Bet_Aos_lie, mul_zero, zero_mul, add_zero]
    · rw [bgFam, if_neg hp, lie_mul_left, Gam_Aos_lie, Bet_Aos_lie, mul_zero, zero_mul, add_zero]
  rw [BG, opSum_lie (bgFam_locFin n) (Aos k u) (by rw [hfam]; exact locFin_zero), hfam,
    opSum_zero]

/-- Collapse of the `δ` from the outer `γ` in `GG_lie_Bet`. -/
theorem gg_delta1 (s r q : ℤ) :
    (if r + (s - q) = 0 then (1 : Module.End ℂ WakFock) else 0) = if q = s + r then 1 else 0 := by
  by_cases h : q = s + r
  · rw [if_pos (show r + (s - q) = 0 by omega), if_pos h]
  · rw [if_neg (show ¬ (r + (s - q) = 0) by omega), if_neg h]

/-- Collapse of the `δ` from the inner `γ` in `GG_lie_Bet`. -/
theorem gg_delta2 (r q : ℤ) :
    (if r + q = 0 then (1 : Module.End ℂ WakFock) else 0) = if q = -r then 1 else 0 := by
  by_cases h : q = -r
  · rw [if_pos (show r + q = 0 by omega), if_pos h]
  · rw [if_neg (show ¬ (r + q = 0) by omega), if_neg h]

/-- `[:γγ:_s, β_r] = -2·γ_{s+r}`. -/
theorem GG_lie_Bet (s r : ℤ) : ⁅GG s, Bet r⁆ = (-2 : ℂ) • Gam (s + r) := by
  have hfam : (fun q => ⁅ggFam s q, Bet r⁆)
      = fun q => (if q = s + r then -Gam (s + r) else 0)
          + (if q = -r then -Gam (s + r) else 0) := by
    funext q
    by_cases hq : q ≤ 0
    · rw [ggFam, if_pos hq, lie_mul_left, Gam_Bet_lie, Gam_Bet_lie, gg_delta1, gg_delta2]
      congr 1
      · by_cases h1 : q = s + r
        · rw [if_pos h1, if_pos h1, mul_neg, mul_one, h1]
        · rw [if_neg h1, if_neg h1, neg_zero, mul_zero]
      · by_cases h2 : q = -r
        · rw [if_pos h2, if_pos h2, neg_mul, one_mul, show s - q = s + r by omega]
        · rw [if_neg h2, if_neg h2, neg_zero, zero_mul]
    · rw [ggFam, if_neg hq, lie_mul_left, Gam_Bet_lie, Gam_Bet_lie, gg_delta1, gg_delta2,
        add_comm (if q = s + r then -Gam (s + r) else 0) (if q = -r then -Gam (s + r) else 0)]
      congr 1
      · by_cases h2 : q = -r
        · rw [if_pos h2, if_pos h2, mul_neg, mul_one, show s - q = s + r by omega]
        · rw [if_neg h2, if_neg h2, neg_zero, mul_zero]
      · by_cases h1 : q = s + r
        · rw [if_pos h1, if_pos h1, neg_mul, one_mul, h1]
        · rw [if_neg h1, if_neg h1, neg_zero, zero_mul]
  rw [GG, opSum_lie (ggFam_locFin s) (Bet r)
      (by rw [hfam]; exact (locFin_ite _ _).add (locFin_ite _ _)), hfam,
    opSum_add (locFin_ite _ _) (locFin_ite _ _), opSum_ite, opSum_ite]
  module

/-- `[:γγ:_s, γ_u] = 0`. -/
theorem GG_lie_Gam (s u : ℤ) : ⁅GG s, Gam u⁆ = 0 := by
  have hfam : (fun q => ⁅ggFam s q, Gam u⁆) = fun _ => (0 : Module.End ℂ WakFock) := by
    funext q
    by_cases hq : q ≤ 0
    · rw [ggFam, if_pos hq, lie_mul_left, Gam_Gam_lie, Gam_Gam_lie, mul_zero, zero_mul, add_zero]
    · rw [ggFam, if_neg hq, lie_mul_left, Gam_Gam_lie, Gam_Gam_lie, mul_zero, zero_mul, add_zero]
  rw [GG, opSum_lie (ggFam_locFin s) (Gam u) (by rw [hfam]; exact locFin_zero), hfam, opSum_zero]

/-- `[:γγ:_s, a_u] = 0`. -/
theorem GG_lie_Aos (k : ℂ) (s u : ℤ) : ⁅GG s, Aos k u⁆ = 0 := by
  have hfam : (fun q => ⁅ggFam s q, Aos k u⁆) = fun _ => (0 : Module.End ℂ WakFock) := by
    funext q
    by_cases hq : q ≤ 0
    · rw [ggFam, if_pos hq, lie_mul_left, Gam_Aos_lie, Gam_Aos_lie, mul_zero, zero_mul, add_zero]
    · rw [ggFam, if_neg hq, lie_mul_left, Gam_Aos_lie, Gam_Aos_lie, mul_zero, zero_mul, add_zero]
  rw [GG, opSum_lie (ggFam_locFin s) (Aos k u) (by rw [hfam]; exact locFin_zero), hfam,
    opSum_zero]

/-- `[:aγ:_n, β_r] = -a_{n+r}`. -/
theorem AG_lie_Bet (k : ℂ) (n r : ℤ) : ⁅AG k n, Bet r⁆ = -Aos k (n + r) := by
  have hfam : (fun p => ⁅agFam k n p, Bet r⁆)
      = fun p => if p = n + r then -Aos k (n + r) else 0 := by
    funext p
    by_cases hp : p ≤ -1
    · rw [agFam, if_pos hp, lie_mul_left, Aos_Bet_lie, zero_mul, add_zero, Gam_Bet_lie]
      by_cases h : p = n + r
      · rw [if_pos (show r + (n - p) = 0 by omega), if_pos h, mul_neg, mul_one, h]
      · rw [if_neg (show ¬ (r + (n - p) = 0) by omega), if_neg h, neg_zero, mul_zero]
    · rw [agFam, if_neg hp, lie_mul_left, Aos_Bet_lie, mul_zero, zero_add, Gam_Bet_lie]
      by_cases h : p = n + r
      · rw [if_pos (show r + (n - p) = 0 by omega), if_pos h, neg_mul, one_mul, h]
      · rw [if_neg (show ¬ (r + (n - p) = 0) by omega), if_neg h, neg_zero, zero_mul]
  rw [AG, opSum_lie (agFam_locFin k n) (Bet r) (by rw [hfam]; exact locFin_ite _ _), hfam,
    opSum_ite]

/-- `[:aγ:_n, γ_u] = 0`. -/
theorem AG_lie_Gam (k : ℂ) (n u : ℤ) : ⁅AG k n, Gam u⁆ = 0 := by
  have hfam : (fun p => ⁅agFam k n p, Gam u⁆) = fun _ => (0 : Module.End ℂ WakFock) := by
    funext p
    by_cases hp : p ≤ -1
    · rw [agFam, if_pos hp, lie_mul_left, Gam_Gam_lie, Aos_Gam_lie, mul_zero, zero_mul, add_zero]
    · rw [agFam, if_neg hp, lie_mul_left, Gam_Gam_lie, Aos_Gam_lie, mul_zero, zero_mul, add_zero]
  rw [AG, opSum_lie (agFam_locFin k n) (Gam u) (by rw [hfam]; exact locFin_zero), hfam,
    opSum_zero]

/-- `[:aγ:_n, a_u] = -2(k+2)·u·γ_{n+u}`. -/
theorem AG_lie_Aos (k : ℂ) (n u : ℤ) :
    ⁅AG k n, Aos k u⁆ = (-(2 * (k + 2)) * (u : ℂ)) • Gam (n + u) := by
  have hfam : (fun p => ⁅agFam k n p, Aos k u⁆)
      = fun p => if p = -u then (-(2 * (k + 2)) * (u : ℂ)) • Gam (n + u) else 0 := by
    funext p
    by_cases hp : p ≤ -1
    · rw [agFam, if_pos hp, lie_mul_left, Gam_Aos_lie, mul_zero, zero_add, Aos_Aos_lie]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, smul_mul_assoc, one_mul,
          show n - p = n + u by omega, h]
        congr 1
        push_cast
        ring
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, zero_mul]
    · rw [agFam, if_neg hp, lie_mul_left, Gam_Aos_lie, zero_mul, add_zero, Aos_Aos_lie]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, mul_smul_comm, mul_one,
          show n - p = n + u by omega, h]
        congr 1
        push_cast
        ring
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, mul_zero]
  rw [AG, opSum_lie (agFam_locFin k n) (Aos k u) (by rw [hfam]; exact locFin_ite _ _), hfam,
    opSum_ite]

/-- `[:βγγ:_n, β_r] = -2·:βγ:_{n+r}`. -/
theorem BGG_lie_Bet (n r : ℤ) : ⁅BGG n, Bet r⁆ = (-2 : ℂ) • BG (n + r) := by
  have hfam : (fun p => ⁅bggFam n p, Bet r⁆) = fun p => (-2 : ℂ) • bgFam (n + r) p := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bggFam, if_pos hp, lie_mul_left, Bet_Bet_lie, zero_mul, add_zero, GG_lie_Bet,
        mul_smul_comm, bgFam, if_pos hp, show n - p + r = n + r - p by ring]
    · rw [bggFam, if_neg hp, lie_mul_left, Bet_Bet_lie, mul_zero, zero_add, GG_lie_Bet,
        smul_mul_assoc, bgFam, if_neg hp, show n - p + r = n + r - p by ring]
  rw [BGG, opSum_lie (bggFam_locFin n) (Bet r)
      (by rw [hfam]; exact (bgFam_locFin (n + r)).smul _), hfam,
    opSum_smul _ (bgFam_locFin (n + r)), BG]

/-- `[:βγγ:_n, γ_u] = :γγ:_{n+u}`. -/
theorem BGG_lie_Gam (n u : ℤ) : ⁅BGG n, Gam u⁆ = GG (n + u) := by
  have hfam : (fun p => ⁅bggFam n p, Gam u⁆)
      = fun p => if p = -u then GG (n + u) else 0 := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bggFam, if_pos hp, lie_mul_left, GG_lie_Gam, mul_zero, zero_add, Bet_Gam_lie]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, one_mul, show n - p = n + u by omega]
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, zero_mul]
    · rw [bggFam, if_neg hp, lie_mul_left, GG_lie_Gam, zero_mul, add_zero, Bet_Gam_lie]
      by_cases h : p = -u
      · rw [if_pos (show p + u = 0 by omega), if_pos h, mul_one, show n - p = n + u by omega]
      · rw [if_neg (show ¬ (p + u = 0) by omega), if_neg h, mul_zero]
  rw [BGG, opSum_lie (bggFam_locFin n) (Gam u) (by rw [hfam]; exact locFin_ite _ _), hfam,
    opSum_ite]

/-- `[:βγγ:_n, a_u] = 0`. -/
theorem BGG_lie_Aos (k : ℂ) (n u : ℤ) : ⁅BGG n, Aos k u⁆ = 0 := by
  have hfam : (fun p => ⁅bggFam n p, Aos k u⁆) = fun _ => (0 : Module.End ℂ WakFock) := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bggFam, if_pos hp, lie_mul_left, GG_lie_Aos, Bet_Aos_lie, mul_zero, zero_mul, add_zero]
    · rw [bggFam, if_neg hp, lie_mul_left, GG_lie_Aos, Bet_Aos_lie, mul_zero, zero_mul, add_zero]
  rw [BGG, opSum_lie (bggFam_locFin n) (Aos k u) (by rw [hfam]; exact locFin_zero), hfam,
    opSum_zero]


/-! ## §9  The Wakimoto currents

```
e_n = β_n,      h_n = -2·:βγ:_n + a_n,      f_n = -:βγγ:_n + :aγ:_n - k·n·γ_n .
```
-/

/-- The Wakimoto current `e_n = β_n`. -/
noncomputable def Ecur (n : ℤ) : Module.End ℂ WakFock := Bet n

/-- The Wakimoto current `h_n = -2·:βγ:_n + a_n`. -/
noncomputable def Hcur (k : ℂ) (n : ℤ) : Module.End ℂ WakFock := (-2 : ℂ) • BG n + Aos k n

/-- The Wakimoto current `f_n = -:βγγ:_n + :aγ:_n - k·n·γ_n`. -/
noncomputable def Fcur (k : ℂ) (n : ℤ) : Module.End ℂ WakFock :=
  -BGG n + AG k n - (k * (n : ℂ)) • Gam n

theorem Ecur_lie_Bet (m r : ℤ) : ⁅Ecur m, Bet r⁆ = 0 := Bet_Bet_lie m r

theorem Ecur_lie_Gam (m u : ℤ) :
    ⁅Ecur m, Gam u⁆ = if m + u = 0 then (1 : Module.End ℂ WakFock) else 0 := Bet_Gam_lie m u

theorem Ecur_lie_Aos (k : ℂ) (m u : ℤ) : ⁅Ecur m, Aos k u⁆ = 0 := Bet_Aos_lie k m u

/-- `[h_m, β_r] = 2 β_{m+r}`. -/
theorem Hcur_lie_Bet (k : ℂ) (m r : ℤ) : ⁅Hcur k m, Bet r⁆ = (2 : ℂ) • Bet (m + r) := by
  rw [Hcur, add_lie, smul_lie, BG_lie_Bet, Aos_Bet_lie, add_zero]
  module

/-- `[h_m, γ_u] = -2 γ_{m+u}`. -/
theorem Hcur_lie_Gam (k : ℂ) (m u : ℤ) : ⁅Hcur k m, Gam u⁆ = (-2 : ℂ) • Gam (m + u) := by
  rw [Hcur, add_lie, smul_lie, BG_lie_Gam, Aos_Gam_lie, add_zero]

/-- `[h_m, a_u] = 2(k+2)·m·δ_{m+u,0}`. -/
theorem Hcur_lie_Aos (k : ℂ) (m u : ℤ) :
    ⁅Hcur k m, Aos k u⁆
      = if m + u = 0 then ((2 * (k + 2)) * (m : ℂ)) • (1 : Module.End ℂ WakFock) else 0 := by
  rw [Hcur, add_lie, smul_lie, BG_lie_Aos, Aos_Aos_lie, smul_zero, zero_add]

/-- `[f_n, β_r] = -h_{n+r} + k·n·δ_{n+r,0}` — the relation that carries the level. -/
theorem Fcur_lie_Bet (k : ℂ) (n r : ℤ) :
    ⁅Fcur k n, Bet r⁆
      = -Hcur k (n + r)
        + (if n + r = 0 then (k * (n : ℂ)) • (1 : Module.End ℂ WakFock) else 0) := by
  rw [Fcur, sub_lie, add_lie, neg_lie, BGG_lie_Bet, AG_lie_Bet, smul_lie, Gam_Bet_lie, Hcur]
  by_cases h : n + r = 0
  · rw [if_pos h, if_pos (show r + n = 0 by omega)]
    module
  · rw [if_neg h, if_neg (show ¬ (r + n = 0) by omega)]
    module

/-- `[f_n, γ_u] = -:γγ:_{n+u}`. -/
theorem Fcur_lie_Gam (k : ℂ) (n u : ℤ) : ⁅Fcur k n, Gam u⁆ = -GG (n + u) := by
  rw [Fcur, sub_lie, add_lie, neg_lie, BGG_lie_Gam, AG_lie_Gam, smul_lie, Gam_Gam_lie,
    smul_zero, add_zero, sub_zero]

/-- `[f_n, a_u] = -2(k+2)·u·γ_{n+u}`. -/
theorem Fcur_lie_Aos (k : ℂ) (n u : ℤ) :
    ⁅Fcur k n, Aos k u⁆ = (-(2 * (k + 2)) * (u : ℂ)) • Gam (n + u) := by
  rw [Fcur, sub_lie, add_lie, neg_lie, BGG_lie_Aos, AG_lie_Aos, smul_lie, Gam_Aos_lie,
    smul_zero, sub_zero, neg_zero, zero_add]

/-! ## §10  The vacuum is a highest-weight vector -/

theorem BG_one {n : ℤ} (h : 0 ≤ n) : BG n (1 : WakFock) = 0 := by
  rw [BG, opSum_apply (bgFam_locFin n) 1]
  refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
  by_cases hp : p ≤ -1
  · rw [bgFam, if_pos hp, Module.End.mul_apply, Gam_one (by omega), map_zero]
  · rw [bgFam, if_neg hp, Module.End.mul_apply, Bet_one (by omega), map_zero]

theorem AG_one (k : ℂ) {n : ℤ} (h : 0 ≤ n) : AG k n (1 : WakFock) = 0 := by
  rw [AG, opSum_apply (agFam_locFin k n) 1]
  refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
  by_cases hp : p ≤ -1
  · rw [agFam, if_pos hp, Module.End.mul_apply, Gam_one (by omega), map_zero]
  · rw [agFam, if_neg hp, Module.End.mul_apply, Aos_one k (by omega), map_zero]

theorem GG_one {s : ℤ} (h : 1 ≤ s) : GG s (1 : WakFock) = 0 := by
  rw [GG, opSum_apply (ggFam_locFin s) 1]
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  by_cases hq : q ≤ 0
  · rw [ggFam, if_pos hq, Module.End.mul_apply,
      Gam_one (n := s - q) (by omega), map_zero]
  · rw [ggFam, if_neg hq, Module.End.mul_apply,
      Gam_one (n := q) (by omega), map_zero]

theorem BGG_one {n : ℤ} (h : 0 ≤ n) : BGG n (1 : WakFock) = 0 := by
  rw [BGG, opSum_apply (bggFam_locFin n) 1]
  refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
  by_cases hp : p ≤ -1
  · rw [bggFam, if_pos hp, Module.End.mul_apply, GG_one (by omega), map_zero]
  · rw [bggFam, if_neg hp, Module.End.mul_apply, Bet_one (by omega), map_zero]

/-- `e_n |0⟩ = 0` for `n ≥ 0`. -/
theorem Ecur_one {n : ℤ} (h : 0 ≤ n) : Ecur n (1 : WakFock) = 0 := Bet_one h

/-- `h_n |0⟩ = 0` for `n ≥ 0`. -/
theorem Hcur_one (k : ℂ) {n : ℤ} (h : 0 ≤ n) : Hcur k n (1 : WakFock) = 0 := by
  rw [Hcur, LinearMap.add_apply, LinearMap.smul_apply, BG_one h, Aos_one k h, smul_zero, add_zero]

/-- `f_n |0⟩ = 0` for `n ≥ 0`. -/
theorem Fcur_one (k : ℂ) {n : ℤ} (h : 0 ≤ n) : Fcur k n (1 : WakFock) = 0 := by
  rw [Fcur, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, BGG_one h, AG_one k h,
    neg_zero, add_zero, LinearMap.smul_apply]
  by_cases h1 : 1 ≤ n
  · rw [Gam_one h1, smul_zero, sub_zero]
  · have hn : n = 0 := by omega
    rw [hn]
    simp

/-! ## §11  The first three affine relations, unconditionally

`[e,e]`, `[h,e]` and — crucially — `[e,f]`, the relation that carries the **level**. -/

/-- **`[e_m, e_n] = 0`**. -/
theorem rel_ee (m n : ℤ) : ⁅Ecur m, Ecur n⁆ = 0 := Bet_Bet_lie m n

/-- **`[h_m, e_n] = 2 e_{m+n}`**. -/
theorem rel_he (k : ℂ) (m n : ℤ) : ⁅Hcur k m, Ecur n⁆ = (2 : ℂ) • Ecur (m + n) :=
  Hcur_lie_Bet k m n

/-- **`[e_m, f_n] = h_{m+n} + m·k·δ_{m+n,0}`** — the affine relation carrying the level `k`. -/
theorem rel_ef (k : ℂ) (m n : ℤ) :
    ⁅Ecur m, Fcur k n⁆
      = Hcur k (m + n)
        + (if m + n = 0 then ((m : ℂ) * k) • (1 : Module.End ℂ WakFock) else 0) := by
  rw [Ecur, lie_swap, Fcur_lie_Bet, show n + m = m + n by ring]
  by_cases h : m + n = 0
  · rw [if_pos h, if_pos h]
    have hnm : (n : ℂ) = -(m : ℂ) := by
      have h' : n = -m := by omega
      rw [h']; push_cast; ring
    rw [neg_add, neg_neg, hnm]
    module
  · rw [if_neg h, if_neg h]
    module


/-! ## §12  Extensionality by creation operators, and rigidity

An endomorphism is determined by its value on the vacuum together with its commutators with the
multiplication (= creation) operators.  If in addition it commutes with the annihilation modes it
is a scalar. -/

/-- **Extensionality by creation.** -/
theorem ext_creation {S T : Module.End ℂ WakFock} (h1 : S 1 = T 1)
    (hX : ∀ v : Fin 3 × ℕ, ⁅S, mulL (X v)⁆ = ⁅T, mulL (X v)⁆) : S = T := by
  refine LinearMap.ext fun P => ?_
  have key : ∀ (U : Module.End ℂ WakFock) (Q : WakFock) (v : Fin 3 × ℕ),
      U (Q * X v) = X v * U Q + ⁅U, mulL (X v)⁆ Q := by
    intro U Q v
    rw [Ring.lie_def]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, mulL_apply]
    rw [mul_comm Q (X v)]
    abel
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [show (MvPolynomial.C a : WakFock) = a • (1 : WakFock) from by
          rw [smul_eq_C_mul, mul_one], map_smul, map_smul, h1]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p v hp => rw [key S p v, key T p v, hp, hX v]

/-- An endomorphism commuting with every multiplication operator is a multiplication. -/
theorem eq_mulL_of_lie_mulX {S : Module.End ℂ WakFock}
    (hX : ∀ v : Fin 3 × ℕ, ⁅S, mulL (X v)⁆ = 0) : S = mulL (S (1 : WakFock)) := by
  refine ext_creation (by rw [mulL_apply, mul_one]) fun v => ?_
  rw [hX v, mulL_lie_mulL]

/-- The coefficient identity behind "all partials vanish ⇒ constant". -/
theorem coeff_X_mul_pderiv (v : Fin 3 × ℕ) (d : Fin 3 × ℕ →₀ ℕ) (Q : WakFock) :
    coeff d (X v * pderiv v Q) = (d v : ℂ) * coeff d Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
      by_cases h : s = d
      · subst h; simp [nsmul_eq_mul]
      · simp [h]
  | add p q hp hq =>
      rw [map_add, mul_add, coeff_add, coeff_add, hp, hq]; ring

/-- A polynomial all of whose partial derivatives vanish is a constant. -/
theorem eq_C_of_pderiv_eq_zero {Q : WakFock} (h : ∀ v, pderiv v Q = 0) :
    Q = MvPolynomial.C (coeff 0 Q) := by
  rw [← MvPolynomial.vars_eq_empty_iff_eq_C]
  by_contra hne
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [MvPolynomial.mem_vars_iff_mem_support] at hv
  obtain ⟨d, hd, hdv⟩ := hv
  have h0 : coeff d (X v * pderiv v Q) = 0 := by rw [h v, mul_zero, coeff_zero]
  rw [coeff_X_mul_pderiv] at h0
  rcases mul_eq_zero.mp h0 with hc | hc
  · exact absurd (Nat.cast_eq_zero.mp hc) (Finsupp.mem_support_iff.mp hdv)
  · exact (MvPolynomial.mem_support_iff.mp hd) hc

/-! ## §13  The weight and charge grading operators -/

/-- The `ℂ`-derivation of `WakFock` determined by `X v ↦ w v · X v` — a weighted Euler
operator. -/
noncomputable def Eul (w : Fin 3 × ℕ → ℂ) : Module.End ℂ WakFock :=
  (mkDerivation ℂ (fun v => w v • (X v : WakFock))).toLinearMap

theorem Eul_apply (w : Fin 3 × ℕ → ℂ) (P : WakFock) :
    Eul w P = mkDerivation ℂ (fun v => w v • (X v : WakFock)) P := rfl

theorem Eul_X (w : Fin 3 × ℕ → ℂ) (v : Fin 3 × ℕ) : Eul w (X v) = w v • X v := by
  rw [Eul_apply]; exact mkDerivation_X ℂ _ v

theorem Eul_one' (w : Fin 3 × ℕ → ℂ) : Eul w (1 : WakFock) = 0 := by
  rw [Eul_apply]
  exact (mkDerivation ℂ (fun v => w v • (X v : WakFock))).map_one_eq_zero

theorem Eul_C' (w : Fin 3 × ℕ → ℂ) (a : ℂ) : Eul w (MvPolynomial.C a : WakFock) = 0 := by
  rw [show (MvPolynomial.C a : WakFock) = a • (1 : WakFock) from by rw [smul_eq_C_mul, mul_one],
    map_smul, Eul_one', smul_zero]

theorem Eul_mul (w : Fin 3 × ℕ → ℂ) (P Q : WakFock) :
    Eul w (P * Q) = Eul w P * Q + P * Eul w Q := by
  have h := (mkDerivation ℂ (fun v => w v • (X v : WakFock))).leibniz P Q
  simp only [smul_eq_mul] at h
  simp only [Eul_apply]
  rw [h]; ring

/-- `[Eul w, Q·] = (Eul w Q)·` — the derivation property in operator form. -/
theorem Eul_lie_mulL (w : Fin 3 × ℕ → ℂ) (Q : WakFock) :
    ⁅Eul w, mulL Q⁆ = mulL (Eul w Q) := by
  refine LinearMap.ext fun P => ?_
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, mulL_apply]
  rw [Eul_mul]
  ring

/-- `Eul w` acts on `∂_v` with eigenvalue `-(w v)`. -/
theorem Eul_pderiv (w : Fin 3 × ℕ → ℂ) (v : Fin 3 × ℕ) (P : WakFock) :
    Eul w (pderiv v P) - pderiv v (Eul w P) = (-(w v)) • pderiv v P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Eul_C']
  | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, smul_add, ← hp, ← hq]; abel
  | mul_X p u ih =>
      have hEX : Eul w (X u) = MvPolynomial.C (w u) * X u := by rw [Eul_X, smul_eq_C_mul]
      have hE : Eul w (p * X u) = Eul w p * X u + MvPolynomial.C (w u) * (p * X u) := by
        rw [Eul_mul, hEX]; ring
      simp only [smul_eq_C_mul, map_neg] at ih ⊢
      by_cases h : v = u
      · subst h
        have hd : pderiv v (p * X v) = pderiv v p * X v + p := by
          rw [pderiv_mul, pderiv_X_self, mul_one]
        have h1 : Eul w (pderiv v (p * X v))
            = Eul w (pderiv v p) * X v + MvPolynomial.C (w v) * (pderiv v p * X v) + Eul w p := by
          rw [hd, map_add, Eul_mul, hEX]; ring
        have h2 : pderiv v (Eul w (p * X v))
            = pderiv v (Eul w p) * X v + Eul w p
              + MvPolynomial.C (w v) * (pderiv v p * X v + p) := by
          rw [hE, map_add, pderiv_mul, pderiv_X_self, mul_one, pderiv_C_mul, hd]
        rw [h1, h2, hd]
        linear_combination (X v) * ih
      · have hne : u ≠ v := fun hc => h hc.symm
        have hd : pderiv v (p * X u) = pderiv v p * X u := by
          rw [pderiv_mul, pderiv_X_of_ne hne, mul_zero, add_zero]
        have h1 : Eul w (pderiv v (p * X u))
            = Eul w (pderiv v p) * X u + MvPolynomial.C (w u) * (pderiv v p * X u) := by
          rw [hd, Eul_mul, hEX]; ring
        have h2 : pderiv v (Eul w (p * X u))
            = pderiv v (Eul w p) * X u + MvPolynomial.C (w u) * (pderiv v p * X u) := by
          rw [hE, map_add, pderiv_mul, pderiv_X_of_ne hne, mul_zero, add_zero, pderiv_C_mul, hd]
        rw [h1, h2, hd]
        linear_combination (X u) * ih

theorem Eul_lie_dV (w : Fin 3 × ℕ → ℂ) (v : Fin 3 × ℕ) :
    ⁅Eul w, dV v⁆ = (-(w v)) • dV v := by
  refine LinearMap.ext fun P => ?_
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dV_apply, LinearMap.smul_apply]
  exact Eul_pderiv w v P


theorem mulL_smul (c : ℂ) (Q : WakFock) : mulL (c • Q) = c • mulL Q := by
  refine LinearMap.ext fun P => ?_
  simp only [mulL_apply, LinearMap.smul_apply, smul_mul_assoc]

theorem lie_one' (A : Module.End ℂ WakFock) : ⁅A, (1 : Module.End ℂ WakFock)⁆ = 0 := by
  rw [Ring.lie_def, mul_one, one_mul, sub_self]

/-- The conformal weight of a variable: `bᵢ` and `Aᵢ` have weight `i`, `c_j` has weight `j`. -/
noncomputable def wtFn : Fin 3 × ℕ → ℂ := fun v => if v.1 = 1 then (v.2 : ℂ) else ((v.2 : ℂ) + 1)

/-- The `βγ`-charge of a variable: `bᵢ` has charge `1`, `c_j` charge `-1`, `Aᵢ` charge `0`. -/
noncomputable def chFn : Fin 3 × ℕ → ℂ :=
  fun v => if v.1 = 0 then 1 else if v.1 = 1 then -1 else 0

/-- The **conformal-weight grading operator** (the `-ℓ₀` of the Fock space). -/
noncomputable def Dwt : Module.End ℂ WakFock := Eul wtFn

/-- The **charge grading operator** (the `βγ`-ghost number). -/
noncomputable def Dch : Module.End ℂ WakFock := Eul chFn

theorem natCast_toNat_sub_one {i : ℤ} (h : 1 ≤ i) : (((i - 1).toNat : ℕ) : ℂ) = (i : ℂ) - 1 := by
  have h1 : (((i - 1).toNat : ℕ) : ℤ) = i - 1 := Int.toNat_of_nonneg (by omega)
  have h2 : ((((i - 1).toNat : ℕ) : ℤ) : ℂ) = ((i - 1 : ℤ) : ℂ) := by rw [h1]
  push_cast at h2
  exact h2

theorem natCast_toNat {j : ℤ} (h : 0 ≤ j) : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by
  have h1 : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg h
  have h2 : (((j.toNat : ℕ) : ℤ) : ℂ) = ((j : ℤ) : ℂ) := by rw [h1]
  push_cast at h2
  exact h2

theorem wtFn_b {i : ℤ} (h : 1 ≤ i) : wtFn ((0 : Fin 3), (i - 1).toNat) = (i : ℂ) := by
  change (if ((0 : Fin 3) = 1) then (((i - 1).toNat : ℕ) : ℂ)
      else (((i - 1).toNat : ℕ) : ℂ) + 1) = (i : ℂ)
  rw [if_neg (by decide : ¬ ((0 : Fin 3) = 1)), natCast_toNat_sub_one h]
  ring

theorem wtFn_c {j : ℤ} (h : 0 ≤ j) : wtFn ((1 : Fin 3), j.toNat) = (j : ℂ) := by
  change (if ((1 : Fin 3) = 1) then ((j.toNat : ℕ) : ℂ) else ((j.toNat : ℕ) : ℂ) + 1) = (j : ℂ)
  rw [if_pos rfl, natCast_toNat h]

theorem wtFn_a {i : ℤ} (h : 1 ≤ i) : wtFn ((2 : Fin 3), (i - 1).toNat) = (i : ℂ) := by
  change (if ((2 : Fin 3) = 1) then (((i - 1).toNat : ℕ) : ℂ)
      else (((i - 1).toNat : ℕ) : ℂ) + 1) = (i : ℂ)
  rw [if_neg (by decide : ¬ ((2 : Fin 3) = 1)), natCast_toNat_sub_one h]
  ring

theorem chFn_b (i : ℕ) : chFn ((0 : Fin 3), i) = 1 := by
  change (if ((0 : Fin 3) = 0) then (1 : ℂ) else if ((0 : Fin 3) = 1) then -1 else 0) = 1
  rw [if_pos rfl]

theorem chFn_c (j : ℕ) : chFn ((1 : Fin 3), j) = -1 := by
  change (if ((1 : Fin 3) = 0) then (1 : ℂ) else if ((1 : Fin 3) = 1) then -1 else 0) = -1
  rw [if_neg (by decide : ¬ ((1 : Fin 3) = 0)), if_pos rfl]

theorem chFn_a (i : ℕ) : chFn ((2 : Fin 3), i) = 0 := by
  change (if ((2 : Fin 3) = 0) then (1 : ℂ) else if ((2 : Fin 3) = 1) then -1 else 0) = 0
  rw [if_neg (by decide : ¬ ((2 : Fin 3) = 0)), if_neg (by decide : ¬ ((2 : Fin 3) = 1))]

/-- `[Dwt, β_m] = -m β_m`. -/
theorem Dwt_lie_Bet (m : ℤ) : ⁅Dwt, Bet m⁆ = (-(m : ℂ)) • Bet m := by
  by_cases hm : m ≤ -1
  · rw [Bet_of_neg hm, Dwt, Eul_lie_mulL, bV_of_pos (by omega), Eul_X, wtFn_b (by omega),
      mulL_smul]
    push_cast
    module
  · rw [Bet_of_nonneg (by omega), cD_of_nonneg (by omega), Dwt, Eul_lie_dV,
      wtFn_c (show (0:ℤ) ≤ m by omega)]

/-- `[Dwt, γ_n] = -n γ_n`. -/
theorem Dwt_lie_Gam (n : ℤ) : ⁅Dwt, Gam n⁆ = (-(n : ℂ)) • Gam n := by
  by_cases hn : n ≤ 0
  · rw [Gam_of_nonpos hn, Dwt, Eul_lie_mulL, cV_of_nonneg (by omega), Eul_X,
      wtFn_c (show (0:ℤ) ≤ -n by omega), mulL_smul]
    push_cast
    module
  · rw [Gam_of_pos (by omega), bD_of_pos (by omega), Dwt, lie_neg, Eul_lie_dV,
      wtFn_b (show (1:ℤ) ≤ n by omega)]
    module

/-- `[Dwt, a_u] = -u a_u`. -/
theorem Dwt_lie_Aos (k : ℂ) (u : ℤ) : ⁅Dwt, Aos k u⁆ = (-(u : ℂ)) • Aos k u := by
  by_cases hu : u ≤ -1
  · rw [Aos_of_neg k hu, Dwt, Eul_lie_mulL, aV_of_pos (by omega), Eul_X,
      wtFn_a (show (1:ℤ) ≤ -u by omega), mulL_smul]
    push_cast
    module
  · rw [Aos_of_nonneg k (by omega)]
    by_cases hu1 : 1 ≤ u
    · rw [aD_of_pos hu1, Dwt, lie_smul, Eul_lie_dV, wtFn_a hu1]
      module
    · rw [aD_of_nonpos (by omega), smul_zero, lie_zero, smul_zero]

/-- `[Dch, β_m] = β_m`. -/
theorem Dch_lie_Bet (m : ℤ) : ⁅Dch, Bet m⁆ = Bet m := by
  by_cases hm : m ≤ -1
  · rw [Bet_of_neg hm, Dch, Eul_lie_mulL, bV_of_pos (by omega), Eul_X, chFn_b, one_smul,
      ← bV_of_pos (show (1:ℤ) ≤ -m by omega)]
  · rw [Bet_of_nonneg (by omega), cD_of_nonneg (by omega), Dch, Eul_lie_dV, chFn_c]
    module

/-- `[Dch, γ_n] = -γ_n`. -/
theorem Dch_lie_Gam (n : ℤ) : ⁅Dch, Gam n⁆ = -Gam n := by
  by_cases hn : n ≤ 0
  · rw [Gam_of_nonpos hn, Dch, Eul_lie_mulL, cV_of_nonneg (by omega), Eul_X, chFn_c,
      ← cV_of_nonneg (show (0:ℤ) ≤ -n by omega), mulL_smul]
    module
  · rw [Gam_of_pos (by omega), bD_of_pos (by omega), Dch, lie_neg, Eul_lie_dV, chFn_b]
    module

/-- `[Dch, a_u] = 0`. -/
theorem Dch_lie_Aos (k : ℂ) (u : ℤ) : ⁅Dch, Aos k u⁆ = 0 := by
  by_cases hu : u ≤ -1
  · rw [Aos_of_neg k hu, Dch, Eul_lie_mulL, aV_of_pos (by omega), Eul_X, chFn_a, zero_smul,
      mulL_zero]
  · rw [Aos_of_nonneg k (by omega)]
    by_cases hu1 : 1 ≤ u
    · rw [aD_of_pos hu1, Dch, lie_smul, Eul_lie_dV, chFn_a]
      module
    · rw [aD_of_nonpos (by omega), smul_zero, lie_zero]

/-! ## §14  Rigidity: an endomorphism commuting with every mode is a scalar -/

theorem pderiv_eq_zero_of_lie_mulL {Q : WakFock} {v : Fin 3 × ℕ}
    (h : ⁅mulL Q, dV v⁆ = 0) : pderiv v Q = 0 := by
  have h1 := congrArg (fun T : Module.End ℂ WakFock => T (1 : WakFock)) h
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, mulL_apply, dV_apply,
    pderiv_one, mul_zero, LinearMap.zero_apply, mul_one, zero_sub, neg_eq_zero] at h1
  exact h1

theorem fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> decide

/-- An endomorphism commuting with every free-field mode is a multiplication operator. -/
theorem eq_mulL_of_lie_modes {k : ℂ} {S : Module.End ℂ WakFock}
    (hB : ∀ r : ℤ, ⁅S, Bet r⁆ = 0) (hG : ∀ u : ℤ, ⁅S, Gam u⁆ = 0)
    (hA : ∀ u : ℤ, ⁅S, Aos k u⁆ = 0) : S = mulL (S (1 : WakFock)) := by
  refine eq_mulL_of_lie_mulX fun v => ?_
  obtain ⟨a, i⟩ := v
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [show (X ((0 : Fin 3), i) : WakFock) = bV ((i : ℤ) + 1) from by
        rw [bV_of_pos (by omega), show ((i : ℤ) + 1 - 1).toNat = i from by omega],
      show mulL (bV ((i : ℤ) + 1)) = Bet (-((i : ℤ) + 1)) from by
        rw [Bet_of_neg (by omega), neg_neg]]
    exact hB _
  · rw [show (X ((1 : Fin 3), i) : WakFock) = cV (i : ℤ) from by
        rw [cV_of_nonneg (by omega), show ((i : ℤ)).toNat = i from by omega],
      show mulL (cV (i : ℤ)) = Gam (-(i : ℤ)) from by rw [Gam_of_nonpos (by omega), neg_neg]]
    exact hG _
  · rw [show (X ((2 : Fin 3), i) : WakFock) = aV ((i : ℤ) + 1) from by
        rw [aV_of_pos (by omega), show ((i : ℤ) + 1 - 1).toNat = i from by omega],
      show mulL (aV ((i : ℤ) + 1)) = Aos k (-((i : ℤ) + 1)) from by
        rw [Aos_of_neg k (by omega), neg_neg]]
    exact hA _

/-- **Rigidity.**  At non-critical level (`k + 2 ≠ 0`) an endomorphism commuting with every
free-field mode is a scalar multiple of the identity. -/
theorem exists_smul_id_of_lie_modes {k : ℂ} (hk : k + 2 ≠ 0) {S : Module.End ℂ WakFock}
    (hB : ∀ r : ℤ, ⁅S, Bet r⁆ = 0) (hG : ∀ u : ℤ, ⁅S, Gam u⁆ = 0)
    (hA : ∀ u : ℤ, ⁅S, Aos k u⁆ = 0) :
    ∃ lam : ℂ, S = lam • (1 : Module.End ℂ WakFock) := by
  have hS := eq_mulL_of_lie_modes hB hG hA
  have hd : ∀ v : Fin 3 × ℕ, pderiv v (S (1 : WakFock)) = 0 := by
    intro v
    obtain ⟨a, i⟩ := v
    refine pderiv_eq_zero_of_lie_mulL ?_
    rw [← hS]
    rcases fin3_cases a with rfl | rfl | rfl
    · have hv : dV ((0 : Fin 3), i) = -Gam ((i : ℤ) + 1) := by
        rw [Gam_of_pos (by omega), bD_of_pos (by omega),
          show ((i : ℤ) + 1 - 1).toNat = i from by omega, neg_neg]
      rw [hv, lie_neg, hG, neg_zero]
    · have hv : dV ((1 : Fin 3), i) = Bet (i : ℤ) := by
        rw [Bet_of_nonneg (by omega), cD_of_nonneg (by omega),
          show ((i : ℤ)).toNat = i from by omega]
      rw [hv, hB]
    · have hc : (2 * (k + 2)) * (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero hk) ?_
        have : ((i : ℤ) + 1 : ℤ) ≠ 0 := by omega
        exact_mod_cast this
      have hv : Aos k ((i : ℤ) + 1)
          = ((2 * (k + 2)) * (((i : ℤ) + 1 : ℤ) : ℂ)) • dV ((2 : Fin 3), i) := by
        rw [Aos_of_nonneg k (by omega), aD_of_pos (by omega),
          show ((i : ℤ) + 1 - 1).toNat = i from by omega]
      have h0 := hA ((i : ℤ) + 1)
      rw [hv, lie_smul, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 hc
      · exact h0
  obtain ⟨lam, hQ⟩ : ∃ lam : ℂ, S (1 : WakFock) = MvPolynomial.C lam :=
    ⟨coeff 0 (S (1 : WakFock)), eq_C_of_pderiv_eq_zero hd⟩
  refine ⟨lam, ?_⟩
  rw [hS, hQ]
  refine LinearMap.ext fun P => ?_
  simp only [mulL_apply, LinearMap.smul_apply, Module.End.one_apply, smul_eq_C_mul]

/-- An endomorphism commuting with every mode and carrying a nonzero grading eigenvalue is `0`. -/
theorem eq_zero_of_lie_modes_of_eigen {k : ℂ} (hk : k + 2 ≠ 0) {S : Module.End ℂ WakFock}
    (hB : ∀ r : ℤ, ⁅S, Bet r⁆ = 0) (hG : ∀ u : ℤ, ⁅S, Gam u⁆ = 0)
    (hA : ∀ u : ℤ, ⁅S, Aos k u⁆ = 0) {D : Module.End ℂ WakFock} {c : ℂ} (hc : c ≠ 0)
    (hDS : ⁅D, S⁆ = c • S) : S = 0 := by
  obtain ⟨lam, hlam⟩ := exists_smul_id_of_lie_modes hk hB hG hA
  rw [hlam] at hDS ⊢
  rw [lie_smul, lie_one', smul_zero] at hDS
  have h1 := congrArg (fun T : Module.End ℂ WakFock => T (1 : WakFock)) hDS
  simp only [LinearMap.zero_apply, LinearMap.smul_apply, Module.End.one_apply, smul_smul] at h1
  have h2 : c * lam = 0 := by
    rcases smul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h one_ne_zero
  rw [(mul_eq_zero.mp h2).resolve_left hc, zero_smul]


/-! ## §15  Shifted operator sums and the `:γγ:` commutators -/

/-- **The commutator passes through an operator sum** (left slot). -/
theorem lie_opSum {T : ℤ → Module.End ℂ WakFock} (hT : LocFin T) (S : Module.End ℂ WakFock)
    (h' : LocFin fun p => ⁅S, T p⁆) : ⁅S, opSum T⁆ = opSum (fun p => ⁅S, T p⁆) := by
  refine LinearMap.ext fun P => ?_
  have hs : (Function.support fun p : ℤ => S (T p P)).Finite := by
    refine Set.Finite.subset (hT P) ?_
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    intro hz; exact hp (by rw [hz, map_zero])
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [opSum_apply hT (S P), opSum_apply hT P, opSum_apply h' P, map_finsum S (hT P),
    ← finsum_sub_distrib hs (hT (S P))]
  refine finsum_congr fun p => ?_
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]

theorem LocFin.shift (c : ℤ) {T : ℤ → Module.End ℂ WakFock} (hT : LocFin T) :
    LocFin (fun p => T (c + p)) := by
  intro P
  have hinj : Function.Injective (fun p : ℤ => c + p) := add_right_injective c
  have h2 : (Function.support fun p : ℤ => T (c + p) P)
      = (fun p : ℤ => c + p) ⁻¹' (Function.support fun q : ℤ => T q P) := rfl
  rw [h2]
  exact Set.Finite.preimage hinj.injOn (hT P)

/-- Operator sums are invariant under an index shift. -/
theorem opSum_shift (c : ℤ) {T : ℤ → Module.End ℂ WakFock} (hT : LocFin T) :
    opSum (fun p => T (c + p)) = opSum T := by
  refine LinearMap.ext fun P => ?_
  rw [opSum_apply (hT.shift c) P, opSum_apply hT P]
  exact finsum_comp_equiv (Equiv.addLeft c) (f := fun q : ℤ => T q P)

/-- The `γ`'s commute, so `ggFam` has no ordering ambiguity. -/
theorem ggFam_eq (t q : ℤ) : ggFam t q = Gam q * Gam (t - q) := by
  rw [ggFam]
  by_cases hq : q ≤ 0
  · rw [if_pos hq]
  · rw [if_neg hq, Gam_comm]

theorem Gam_lie_GG (x t : ℤ) : ⁅Gam x, GG t⁆ = 0 := by rw [lie_swap, GG_lie_Gam, neg_zero]

theorem Aos_lie_GG (k : ℂ) (u t : ℤ) : ⁅Aos k u, GG t⁆ = 0 := by
  rw [lie_swap, GG_lie_Aos, neg_zero]

theorem Bet_lie_GG (r s : ℤ) : ⁅Bet r, GG s⁆ = (2 : ℂ) • Gam (s + r) := by
  rw [lie_swap, GG_lie_Bet]; module

/-- `[:γγ:_s, :γγ:_t] = 0`. -/
theorem GG_lie_GG (s t : ℤ) : ⁅GG s, GG t⁆ = 0 := by
  have hfam : (fun q => ⁅ggFam s q, GG t⁆) = fun _ => (0 : Module.End ℂ WakFock) := by
    funext q
    rw [ggFam_eq, lie_mul_left, Gam_lie_GG, Gam_lie_GG, mul_zero, zero_mul, add_zero]
  rw [GG, opSum_lie (ggFam_locFin s) (GG t) (by rw [hfam]; exact locFin_zero), hfam, opSum_zero]

/-- `[:βγ:_u, :γγ:_s] = 2·:γγ:_{s+u}`. -/
theorem BG_lie_GG (u s : ℤ) : ⁅BG u, GG s⁆ = (2 : ℂ) • GG (s + u) := by
  have hfam : (fun p => ⁅bgFam u p, GG s⁆) = fun p => (2 : ℂ) • ggFam (s + u) (s + p) := by
    funext p
    have hgg : ggFam (s + u) (s + p) = Gam (s + p) * Gam (u - p) := by
      rw [ggFam_eq, show s + u - (s + p) = u - p by ring]
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_left, Gam_lie_GG, Bet_lie_GG, mul_zero, zero_add, hgg,
        smul_mul_assoc]
    · rw [bgFam, if_neg hp, lie_mul_left, Gam_lie_GG, Bet_lie_GG, zero_mul, add_zero, hgg,
        mul_smul_comm, Gam_comm]
  have hlf : LocFin (fun p => (2 : ℂ) • ggFam (s + u) (s + p)) :=
    ((ggFam_locFin (s + u)).shift s).smul 2
  rw [BG, opSum_lie (bgFam_locFin u) (GG s) (by rw [hfam]; exact hlf), hfam,
    opSum_smul 2 ((ggFam_locFin (s + u)).shift s), opSum_shift s (ggFam_locFin (s + u)), GG]

/-- `[h_m, :γγ:_s] = -4·:γγ:_{m+s}`. -/
theorem Hcur_lie_GG (k : ℂ) (m s : ℤ) : ⁅Hcur k m, GG s⁆ = (-4 : ℂ) • GG (m + s) := by
  rw [Hcur, add_lie, smul_lie, BG_lie_GG, Aos_lie_GG, add_zero, show s + m = m + s by ring,
    smul_smul]
  norm_num

theorem GG_lie_Hcur (k : ℂ) (m s : ℤ) : ⁅GG s, Hcur k m⁆ = (4 : ℂ) • GG (m + s) := by
  rw [lie_swap, Hcur_lie_GG]; module

/-! ## §16  The gradings of the composite operators -/

theorem Dch_lie_BG (n : ℤ) : ⁅Dch, BG n⁆ = 0 := by
  have hfam : (fun p => ⁅Dch, bgFam n p⁆) = fun _ => (0 : Module.End ℂ WakFock) := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_right, Dch_lie_Bet, Dch_lie_Gam, mul_neg]; abel
    · rw [bgFam, if_neg hp, lie_mul_right, Dch_lie_Bet, Dch_lie_Gam, neg_mul]; abel
  rw [BG, lie_opSum (bgFam_locFin n) Dch (by rw [hfam]; exact locFin_zero), hfam, opSum_zero]

theorem Dch_lie_GG (s : ℤ) : ⁅Dch, GG s⁆ = (-2 : ℂ) • GG s := by
  have hfam : (fun q => ⁅Dch, ggFam s q⁆) = fun q => (-2 : ℂ) • ggFam s q := by
    funext q
    rw [ggFam_eq, lie_mul_right, Dch_lie_Gam, Dch_lie_Gam, neg_mul, mul_neg]
    module
  rw [GG, lie_opSum (ggFam_locFin s) Dch (by rw [hfam]; exact (ggFam_locFin s).smul _), hfam,
    opSum_smul _ (ggFam_locFin s)]

theorem Dch_lie_AG (k : ℂ) (n : ℤ) : ⁅Dch, AG k n⁆ = (-1 : ℂ) • AG k n := by
  have hfam : (fun p => ⁅Dch, agFam k n p⁆) = fun p => (-1 : ℂ) • agFam k n p := by
    funext p
    by_cases hp : p ≤ -1
    · rw [agFam, if_pos hp, lie_mul_right, Dch_lie_Aos, Dch_lie_Gam, zero_mul, mul_neg]
      module
    · rw [agFam, if_neg hp, lie_mul_right, Dch_lie_Aos, Dch_lie_Gam, mul_zero, neg_mul]
      module
  rw [AG, lie_opSum (agFam_locFin k n) Dch (by rw [hfam]; exact (agFam_locFin k n).smul _), hfam,
    opSum_smul _ (agFam_locFin k n)]

theorem Dch_lie_BGG (n : ℤ) : ⁅Dch, BGG n⁆ = (-1 : ℂ) • BGG n := by
  have hfam : (fun p => ⁅Dch, bggFam n p⁆) = fun p => (-1 : ℂ) • bggFam n p := by
    funext p
    by_cases hp : p ≤ -1
    · rw [bggFam, if_pos hp, lie_mul_right, Dch_lie_Bet, Dch_lie_GG, mul_smul_comm]
      module
    · rw [bggFam, if_neg hp, lie_mul_right, Dch_lie_Bet, Dch_lie_GG, smul_mul_assoc]
      module
  rw [BGG, lie_opSum (bggFam_locFin n) Dch (by rw [hfam]; exact (bggFam_locFin n).smul _), hfam,
    opSum_smul _ (bggFam_locFin n)]

theorem Dwt_lie_BG (n : ℤ) : ⁅Dwt, BG n⁆ = (-(n : ℂ)) • BG n := by
  have hfam : (fun p => ⁅Dwt, bgFam n p⁆) = fun p => (-(n : ℂ)) • bgFam n p := by
    funext p
    have hc : (-(p : ℂ)) + (-(((n - p : ℤ)) : ℂ)) = -(n : ℂ) := by push_cast; ring
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, lie_mul_right, Dwt_lie_Bet, Dwt_lie_Gam, smul_mul_assoc,
        mul_smul_comm, ← add_smul, hc]
    · rw [bgFam, if_neg hp, lie_mul_right, Dwt_lie_Bet, Dwt_lie_Gam, smul_mul_assoc,
        mul_smul_comm, ← add_smul, add_comm, hc]
  rw [BG, lie_opSum (bgFam_locFin n) Dwt (by rw [hfam]; exact (bgFam_locFin n).smul _), hfam,
    opSum_smul _ (bgFam_locFin n)]

theorem Dch_lie_Ecur (n : ℤ) : ⁅Dch, Ecur n⁆ = Ecur n := Dch_lie_Bet n

theorem Dch_lie_Hcur (k : ℂ) (n : ℤ) : ⁅Dch, Hcur k n⁆ = 0 := by
  rw [Hcur, lie_add, lie_smul, Dch_lie_BG, Dch_lie_Aos, smul_zero, add_zero]

theorem Dch_lie_Fcur (k : ℂ) (n : ℤ) : ⁅Dch, Fcur k n⁆ = (-1 : ℂ) • Fcur k n := by
  rw [Fcur, lie_sub, lie_add, lie_neg, Dch_lie_BGG, Dch_lie_AG, lie_smul, Dch_lie_Gam]
  module

theorem Dwt_lie_Hcur (k : ℂ) (n : ℤ) : ⁅Dwt, Hcur k n⁆ = (-(n : ℂ)) • Hcur k n := by
  rw [Hcur, lie_add, lie_smul, Dwt_lie_BG, Dwt_lie_Aos]
  module


/-! ## §17  The central term of `[h_m, h_n]`

The one genuinely arithmetic input: the value of `[h_m, h_{-m}]` on the vacuum. -/

/-- Moving an operator past another: `A (B P) = [A,B] P + B (A P)`. -/
theorem apply_comp (A B : Module.End ℂ WakFock) (P : WakFock) :
    A (B P) = ⁅A, B⁆ P + B (A P) := by
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  abel

/-- `β_j c_j = 1` for `j ≥ 0`. -/
theorem Bet_cV_self {j : ℤ} (h : 0 ≤ j) : Bet j (cV j) = (1 : WakFock) := by
  rw [Bet_of_nonneg h, cD_of_nonneg h, cV_of_nonneg h, dV_apply, pderiv_X_self]

/-- `h_m` kills `c_j` when `m ≥ 1` and `j = m + p` with `p ≤ -1`. -/
theorem Hcur_cV_vanish (k : ℂ) {m j : ℤ} (hm : 0 ≤ m) (hj : 0 ≤ j) (hlt : j < m) :
    Hcur k m (cV j) = 0 := by
  rw [show cV j = Gam (-j) (1 : WakFock) from by rw [Gam_one_nonpos (by omega), neg_neg],
    apply_comp, Hcur_lie_Gam, Hcur_one k hm, map_zero, add_zero, LinearMap.smul_apply,
    Gam_one (show 1 ≤ m + -j by omega), smul_zero]

/-- The vacuum value of `h_m` applied to `:βγ:_{-m}|0⟩`. -/
theorem Hcur_BG_vac (k : ℂ) {m : ℤ} (hm : 1 ≤ m) :
    Hcur k m (BG (-m) (1 : WakFock)) = ((2 : ℂ) * (m : ℂ)) • (1 : WakFock) := by
  have hfin := bgFam_locFin (-m) (1 : WakFock)
  rw [BG, opSum_apply (bgFam_locFin (-m)) 1, map_finsum (Hcur k m) hfin]
  have hterm : ∀ p : ℤ, Hcur k m (bgFam (-m) p (1 : WakFock))
      = if (-m ≤ p ∧ p ≤ -1) then (2 : ℂ) • (1 : WakFock) else 0 := by
    intro p
    by_cases hp : p ≤ -1
    · rw [bgFam, if_pos hp, Module.End.mul_apply]
      by_cases hp2 : -m ≤ p
      · rw [if_pos ⟨hp2, hp⟩, Gam_one_nonpos (show -m - p ≤ 0 by omega),
          show -(-m - p) = m + p by ring, apply_comp, Hcur_lie_Bet,
          Hcur_cV_vanish k (by omega) (by omega) (by omega), map_zero, add_zero,
          LinearMap.smul_apply, Bet_cV_self (show (0:ℤ) ≤ m + p by omega)]
      · rw [if_neg (by omega), Gam_one (show 1 ≤ -m - p by omega), map_zero, map_zero]
    · rw [bgFam, if_neg hp, Module.End.mul_apply, Bet_one (by omega), map_zero, map_zero,
        if_neg (by omega)]
  rw [finsum_congr hterm]
  have hsupp : (Function.support fun p : ℤ =>
      if (-m ≤ p ∧ p ≤ -1) then ((2 : ℂ) • (1 : WakFock)) else 0)
      ⊆ ↑(Finset.Icc (-m) (-1)) := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hp (if_neg hc)
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp,
    Finset.sum_congr rfl (fun p hp => if_pos (by simp only [Finset.mem_Icc] at hp; exact hp)),
    Finset.sum_const,
    show (Finset.Icc (-m) (-1)).card = m.toNat from by rw [Int.card_Icc]; congr 1; omega,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, natCast_toNat (show (0:ℤ) ≤ m by omega)]
  congr 1
  ring

/-- **The central term.**  `[h_m, h_{-m}]|0⟩ = 2 k m |0⟩` for `m ≥ 1`. -/
theorem Hcur_lie_Hcur_vac (k : ℂ) {m : ℤ} (hm : 1 ≤ m) :
    ⁅Hcur k m, Hcur k (-m)⁆ (1 : WakFock) = ((2 : ℂ) * k * (m : ℂ)) • (1 : WakFock) := by
  rw [Ring.lie_def]
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [Hcur_one k (show (0:ℤ) ≤ m by omega), map_zero, sub_zero]
  have hH : Hcur k (-m) (1 : WakFock) = (-2 : ℂ) • BG (-m) (1 : WakFock) + aV m := by
    rw [Hcur, LinearMap.add_apply, LinearMap.smul_apply, Aos_one_neg k (by omega), neg_neg]
  rw [hH, map_add, map_smul, Hcur_BG_vac k hm]
  have hA : Hcur k m (aV m) = ((2 * (k + 2)) * (m : ℂ)) • (1 : WakFock) := by
    rw [show aV m = Aos k (-m) (1 : WakFock) from by rw [Aos_one_neg k (by omega), neg_neg],
      apply_comp, Hcur_lie_Aos, Hcur_one k (show (0:ℤ) ≤ m by omega), map_zero, add_zero,
      if_pos (show m + -m = 0 by omega), LinearMap.smul_apply, Module.End.one_apply]
  rw [hA, smul_smul, ← add_smul]
  congr 1
  ring


/-! ## §18  The relation `[h_m, h_n] = 2 k m δ_{m+n,0}` -/

theorem lie_lie' (A B C : Module.End ℂ WakFock) : ⁅⁅A, B⁆, C⁆ = ⁅A, ⁅B, C⁆⁆ - ⁅B, ⁅A, C⁆⁆ := by
  simp only [Ring.lie_def]; noncomm_ring

theorem lie_lie_left (A B C : Module.End ℂ WakFock) :
    ⁅A, ⁅B, C⁆⁆ = ⁅⁅A, B⁆, C⁆ + ⁅B, ⁅A, C⁆⁆ := by
  simp only [Ring.lie_def]; noncomm_ring

theorem one_lie' (A : Module.End ℂ WakFock) : ⁅(1 : Module.End ℂ WakFock), A⁆ = 0 := by
  rw [Ring.lie_def, one_mul, mul_one, sub_self]

/-- A scalar operator commutes with everything. -/
theorem central_lie (c : ℂ) (A : Module.End ℂ WakFock) :
    ⁅c • (1 : Module.End ℂ WakFock), A⁆ = 0 := by rw [smul_lie, one_lie', smul_zero]

theorem HH_lie_Bet (k : ℂ) (m n r : ℤ) : ⁅⁅Hcur k m, Hcur k n⁆, Bet r⁆ = 0 := by
  rw [lie_lie', Hcur_lie_Bet, Hcur_lie_Bet, lie_smul, lie_smul, Hcur_lie_Bet, Hcur_lie_Bet,
    show m + (n + r) = n + (m + r) by ring, sub_self]

theorem HH_lie_Gam (k : ℂ) (m n u : ℤ) : ⁅⁅Hcur k m, Hcur k n⁆, Gam u⁆ = 0 := by
  rw [lie_lie', Hcur_lie_Gam, Hcur_lie_Gam, lie_smul, lie_smul, Hcur_lie_Gam, Hcur_lie_Gam,
    show m + (n + u) = n + (m + u) by ring, sub_self]

theorem HH_lie_Aos (k : ℂ) (m n u : ℤ) : ⁅⁅Hcur k m, Hcur k n⁆, Aos k u⁆ = 0 := by
  rw [lie_lie', Hcur_lie_Aos, Hcur_lie_Aos]
  by_cases h1 : n + u = 0 <;> by_cases h2 : m + u = 0 <;> simp [h1, h2, lie_one']

/-- The vacuum value of `[h_m, h_n]` when `m + n = 0`. -/
theorem Hcur_lie_Hcur_vac' (k : ℂ) {m n : ℤ} (h : m + n = 0) :
    ⁅Hcur k m, Hcur k n⁆ (1 : WakFock) = ((2 : ℂ) * k * (m : ℂ)) • (1 : WakFock) := by
  have hn : n = -m := by omega
  subst hn
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hkey := Hcur_lie_Hcur_vac k (show (1 : ℤ) ≤ -m by omega)
    rw [neg_neg] at hkey
    rw [lie_swap, LinearMap.neg_apply, hkey, ← neg_smul]
    congr 1
    push_cast
    ring
  · subst hm
    rw [neg_zero, lie_self, LinearMap.zero_apply]
    norm_num
  · exact Hcur_lie_Hcur_vac k (by omega)

/-- **`[h_m, h_n] = 2 k m δ_{m+n,0}`** (non-critical level). -/
theorem rel_hh (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅Hcur k m, Hcur k n⁆
      = if m + n = 0 then ((2 : ℂ) * k * (m : ℂ)) • (1 : Module.End ℂ WakFock) else 0 := by
  set R : Module.End ℂ WakFock :=
    if m + n = 0 then ((2 : ℂ) * k * (m : ℂ)) • (1 : Module.End ℂ WakFock) else 0 with hR
  have hRc : ∀ A : Module.End ℂ WakFock, ⁅R, A⁆ = 0 := by
    intro A
    rw [hR]
    by_cases h : m + n = 0
    · rw [if_pos h, central_lie]
    · rw [if_neg h, zero_lie]
  set D : Module.End ℂ WakFock := ⁅Hcur k m, Hcur k n⁆ - R with hD
  have hDlie : ∀ A : Module.End ℂ WakFock, ⁅D, A⁆ = ⁅⁅Hcur k m, Hcur k n⁆, A⁆ := by
    intro A; rw [hD, sub_lie, hRc, sub_zero]
  have hB : ∀ r : ℤ, ⁅D, Bet r⁆ = 0 := fun r => by rw [hDlie, HH_lie_Bet]
  have hG : ∀ u : ℤ, ⁅D, Gam u⁆ = 0 := fun u => by rw [hDlie, HH_lie_Gam]
  have hA : ∀ u : ℤ, ⁅D, Aos k u⁆ = 0 := fun u => by rw [hDlie, HH_lie_Aos]
  have hDzero : D = 0 := by
    by_cases hmn : m + n = 0
    · -- the scalar is pinned by the vacuum value
      obtain ⟨lam, hlam⟩ := exists_smul_id_of_lie_modes hk hB hG hA
      have hv : D (1 : WakFock) = 0 := by
        rw [hD, LinearMap.sub_apply, Hcur_lie_Hcur_vac' k hmn, hR, if_pos hmn,
          LinearMap.smul_apply, Module.End.one_apply, sub_self]
      rw [hlam] at hv ⊢
      simp only [LinearMap.smul_apply, Module.End.one_apply] at hv
      rcases smul_eq_zero.mp hv with h | h
      · rw [h, zero_smul]
      · exact absurd h one_ne_zero
    · have hc : (-(m : ℂ)) + (-(n : ℂ)) ≠ 0 := by
        have h0 : ((m + n : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hmn
        push_cast at h0
        intro hcon
        exact h0 (by linear_combination -hcon)
      have heig : ⁅Dwt, D⁆ = ((-(m : ℂ)) + (-(n : ℂ))) • D := by
        rw [hD, hR, if_neg hmn, sub_zero, lie_lie_left, Dwt_lie_Hcur, Dwt_lie_Hcur, smul_lie,
          lie_smul, add_smul]
      exact eq_zero_of_lie_modes_of_eigen hk hB hG hA hc heig
  rw [← sub_eq_zero]
  exact hDzero


/-! ## §19  The relation `[h_m, f_n] = -2 f_{m+n}` -/

theorem lie_ite_central (A : Module.End ℂ WakFock) (P : Prop) [Decidable P] (c : ℂ) :
    ⁅A, if P then c • (1 : Module.End ℂ WakFock) else 0⁆ = 0 := by
  by_cases h : P
  · rw [if_pos h, lie_smul, lie_one', smul_zero]
  · rw [if_neg h, lie_zero]

theorem HF_lie_Bet (k : ℂ) (hk : k + 2 ≠ 0) (m n r : ℤ) :
    ⁅⁅Hcur k m, Fcur k n⁆, Bet r⁆ - (-2 : ℂ) • ⁅Fcur k (m + n), Bet r⁆ = 0 := by
  rw [lie_lie', Fcur_lie_Bet k n r, Hcur_lie_Bet k m r, lie_add, lie_neg, rel_hh k hk,
    lie_ite_central, add_zero, lie_smul, Fcur_lie_Bet k n (m + r), Fcur_lie_Bet k (m + n) r,
    show m + (n + r) = m + n + r from by ring, show n + (m + r) = m + n + r from by ring]
  by_cases hz : m + n + r = 0
  · rw [if_pos hz, if_pos hz, if_pos hz]
    push_cast
    module
  · rw [if_neg hz, if_neg hz, if_neg hz]
    module

theorem HF_lie_Gam (k : ℂ) (m n u : ℤ) :
    ⁅⁅Hcur k m, Fcur k n⁆, Gam u⁆ - (-2 : ℂ) • ⁅Fcur k (m + n), Gam u⁆ = 0 := by
  rw [lie_lie', Fcur_lie_Gam k n u, Hcur_lie_Gam k m u, lie_neg, Hcur_lie_GG, lie_smul,
    Fcur_lie_Gam k n (m + u), Fcur_lie_Gam k (m + n) u,
    show m + (n + u) = m + n + u from by ring, show n + (m + u) = m + n + u from by ring]
  module

theorem HF_lie_Aos (k : ℂ) (m n u : ℤ) :
    ⁅⁅Hcur k m, Fcur k n⁆, Aos k u⁆ - (-2 : ℂ) • ⁅Fcur k (m + n), Aos k u⁆ = 0 := by
  rw [lie_lie', Fcur_lie_Aos k n u, Hcur_lie_Aos k m u, lie_smul, Hcur_lie_Gam,
    lie_ite_central, sub_zero, Fcur_lie_Aos k (m + n) u,
    show m + (n + u) = m + n + u from by ring]
  module

/-- **`[h_m, f_n] = -2 f_{m+n}`** (non-critical level). -/
theorem rel_hf (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅Hcur k m, Fcur k n⁆ = (-2 : ℂ) • Fcur k (m + n) := by
  set D : Module.End ℂ WakFock := ⁅Hcur k m, Fcur k n⁆ - (-2 : ℂ) • Fcur k (m + n) with hD
  have hB : ∀ r : ℤ, ⁅D, Bet r⁆ = 0 := by
    intro r; rw [hD, sub_lie, smul_lie]; exact HF_lie_Bet k hk m n r
  have hG : ∀ u : ℤ, ⁅D, Gam u⁆ = 0 := by
    intro u; rw [hD, sub_lie, smul_lie]; exact HF_lie_Gam k m n u
  have hA : ∀ u : ℤ, ⁅D, Aos k u⁆ = 0 := by
    intro u; rw [hD, sub_lie, smul_lie]; exact HF_lie_Aos k m n u
  have heig : ⁅Dch, D⁆ = (-1 : ℂ) • D := by
    rw [hD, lie_sub, lie_lie_left Dch (Hcur k m) (Fcur k n), Dch_lie_Hcur, zero_lie, zero_add,
      Dch_lie_Fcur k n, lie_smul, lie_smul, Dch_lie_Fcur k (m + n)]
    module
  have h0 := eq_zero_of_lie_modes_of_eigen hk hB hG hA (show (-1 : ℂ) ≠ 0 by norm_num) heig
  rw [← sub_eq_zero]
  exact h0

/-! ## §20  The relation `[f_m, f_n] = 0` -/

theorem FGG_lie_Bet (k : ℂ) (b t r : ℤ) :
    ⁅⁅Fcur k b, GG t⁆, Bet r⁆ = (6 : ℂ) • GG (b + t + r) := by
  rw [lie_lie', GG_lie_Bet t r, Fcur_lie_Bet k b r, lie_smul, Fcur_lie_Gam, lie_add, lie_neg,
    GG_lie_Hcur, lie_ite_central, add_zero,
    show b + (t + r) = b + t + r from by ring, show b + r + t = b + t + r from by ring]
  module

theorem FGG_lie_Gam (k : ℂ) (b t u : ℤ) : ⁅⁅Fcur k b, GG t⁆, Gam u⁆ = 0 := by
  rw [lie_lie', GG_lie_Gam, Fcur_lie_Gam k b u, lie_zero, zero_sub, lie_neg, GG_lie_GG,
    neg_zero, neg_zero]

theorem FGG_lie_Aos (k : ℂ) (b t u : ℤ) : ⁅⁅Fcur k b, GG t⁆, Aos k u⁆ = 0 := by
  rw [lie_lie', GG_lie_Aos, Fcur_lie_Aos k b u, lie_zero, zero_sub, lie_smul, GG_lie_Gam,
    smul_zero, neg_zero]

/-- **The shift lemma**: `[f_a, :γγ:_s]` depends only on `a + s`.  This is what unlocks
`[f, f] = 0`. -/
theorem Fcur_lie_GG_shift (k : ℂ) (hk : k + 2 ≠ 0) {a s a' s' : ℤ} (h : a + s = a' + s') :
    ⁅Fcur k a, GG s⁆ = ⁅Fcur k a', GG s'⁆ := by
  set D : Module.End ℂ WakFock := ⁅Fcur k a, GG s⁆ - ⁅Fcur k a', GG s'⁆ with hD
  have hB : ∀ r : ℤ, ⁅D, Bet r⁆ = 0 := by
    intro r; rw [hD, sub_lie, FGG_lie_Bet, FGG_lie_Bet, h, sub_self]
  have hG : ∀ u : ℤ, ⁅D, Gam u⁆ = 0 := by
    intro u; rw [hD, sub_lie, FGG_lie_Gam, FGG_lie_Gam, sub_self]
  have hA : ∀ u : ℤ, ⁅D, Aos k u⁆ = 0 := by
    intro u; rw [hD, sub_lie, FGG_lie_Aos, FGG_lie_Aos, sub_self]
  have heig : ⁅Dch, D⁆ = (-3 : ℂ) • D := by
    rw [hD, lie_sub, lie_lie_left Dch (Fcur k a) (GG s), lie_lie_left Dch (Fcur k a') (GG s'),
      Dch_lie_Fcur k a, Dch_lie_Fcur k a', Dch_lie_GG s, Dch_lie_GG s',
      smul_lie, smul_lie, lie_smul, lie_smul]
    module
  have h0 := eq_zero_of_lie_modes_of_eigen hk hB hG hA (show (-3 : ℂ) ≠ 0 by norm_num) heig
  rw [← sub_eq_zero]
  exact h0

theorem FF_lie_Bet (k : ℂ) (hk : k + 2 ≠ 0) (m n r : ℤ) :
    ⁅⁅Fcur k m, Fcur k n⁆, Bet r⁆ = 0 := by
  rw [lie_lie', Fcur_lie_Bet k n r, Fcur_lie_Bet k m r, lie_add, lie_add, lie_neg, lie_neg,
    lie_ite_central, lie_ite_central, add_zero, add_zero,
    lie_swap (Fcur k m) (Hcur k (n + r)), lie_swap (Fcur k n) (Hcur k (m + r)),
    rel_hf k hk, rel_hf k hk, show n + r + m = m + r + n from by ring]
  module

theorem FF_lie_Gam (k : ℂ) (hk : k + 2 ≠ 0) (m n u : ℤ) :
    ⁅⁅Fcur k m, Fcur k n⁆, Gam u⁆ = 0 := by
  rw [lie_lie', Fcur_lie_Gam k n u, Fcur_lie_Gam k m u, lie_neg, lie_neg,
    Fcur_lie_GG_shift k hk (a := m) (s := n + u) (a' := n) (s' := m + u) (by ring)]
  abel

theorem FF_lie_Aos (k : ℂ) (m n u : ℤ) : ⁅⁅Fcur k m, Fcur k n⁆, Aos k u⁆ = 0 := by
  rw [lie_lie', Fcur_lie_Aos k n u, Fcur_lie_Aos k m u, lie_smul, lie_smul, Fcur_lie_Gam,
    Fcur_lie_Gam, show m + (n + u) = n + (m + u) from by ring, sub_self]

/-- **`[f_m, f_n] = 0`** (non-critical level) — the hardest of the six relations. -/
theorem rel_ff (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) : ⁅Fcur k m, Fcur k n⁆ = 0 := by
  have heig : ⁅Dch, ⁅Fcur k m, Fcur k n⁆⁆ = (-2 : ℂ) • ⁅Fcur k m, Fcur k n⁆ := by
    rw [lie_lie_left Dch (Fcur k m) (Fcur k n), Dch_lie_Fcur k m, Dch_lie_Fcur k n,
      smul_lie, lie_smul]
    module
  exact eq_zero_of_lie_modes_of_eigen hk (fun r => FF_lie_Bet k hk m n r)
    (fun u => FF_lie_Gam k hk m n u) (fun u => FF_lie_Aos k m n u)
    (show (-2 : ℂ) ≠ 0 by norm_num) heig


/-! ## §21  The conformal weight of the composites and of `f` -/

theorem Dwt_lie_GG (s : ℤ) : ⁅Dwt, GG s⁆ = (-(s : ℂ)) • GG s := by
  have hfam : (fun q => ⁅Dwt, ggFam s q⁆) = fun q => (-(s : ℂ)) • ggFam s q := by
    funext q
    have hc : (-(q : ℂ)) + (-(((s - q : ℤ)) : ℂ)) = -(s : ℂ) := by push_cast; ring
    rw [ggFam_eq, lie_mul_right, Dwt_lie_Gam, Dwt_lie_Gam, smul_mul_assoc, mul_smul_comm,
      ← add_smul, hc]
  rw [GG, lie_opSum (ggFam_locFin s) Dwt (by rw [hfam]; exact (ggFam_locFin s).smul _), hfam,
    opSum_smul _ (ggFam_locFin s)]

theorem Dwt_lie_AG (k : ℂ) (n : ℤ) : ⁅Dwt, AG k n⁆ = (-(n : ℂ)) • AG k n := by
  have hfam : (fun p => ⁅Dwt, agFam k n p⁆) = fun p => (-(n : ℂ)) • agFam k n p := by
    funext p
    have hc : (-(p : ℂ)) + (-(((n - p : ℤ)) : ℂ)) = -(n : ℂ) := by push_cast; ring
    by_cases hp : p ≤ -1
    · rw [agFam, if_pos hp, lie_mul_right, Dwt_lie_Aos, Dwt_lie_Gam, smul_mul_assoc,
        mul_smul_comm, ← add_smul, hc]
    · rw [agFam, if_neg hp, lie_mul_right, Dwt_lie_Aos, Dwt_lie_Gam, smul_mul_assoc,
        mul_smul_comm, ← add_smul, add_comm, hc]
  rw [AG, lie_opSum (agFam_locFin k n) Dwt (by rw [hfam]; exact (agFam_locFin k n).smul _), hfam,
    opSum_smul _ (agFam_locFin k n)]

theorem Dwt_lie_BGG (n : ℤ) : ⁅Dwt, BGG n⁆ = (-(n : ℂ)) • BGG n := by
  have hfam : (fun p => ⁅Dwt, bggFam n p⁆) = fun p => (-(n : ℂ)) • bggFam n p := by
    funext p
    have hc : (-(p : ℂ)) + (-(((n - p : ℤ)) : ℂ)) = -(n : ℂ) := by push_cast; ring
    by_cases hp : p ≤ -1
    · rw [bggFam, if_pos hp, lie_mul_right, Dwt_lie_Bet, Dwt_lie_GG, smul_mul_assoc,
        mul_smul_comm, ← add_smul, hc]
    · rw [bggFam, if_neg hp, lie_mul_right, Dwt_lie_Bet, Dwt_lie_GG, smul_mul_assoc,
        mul_smul_comm, ← add_smul, add_comm, hc]
  rw [BGG, lie_opSum (bggFam_locFin n) Dwt (by rw [hfam]; exact (bggFam_locFin n).smul _), hfam,
    opSum_smul _ (bggFam_locFin n)]

theorem Dwt_lie_Fcur (k : ℂ) (n : ℤ) : ⁅Dwt, Fcur k n⁆ = (-(n : ℂ)) • Fcur k n := by
  rw [Fcur, lie_sub, lie_add, lie_neg, Dwt_lie_BGG, Dwt_lie_AG, lie_smul, Dwt_lie_Gam]
  module

theorem Dwt_lie_Ecur (n : ℤ) : ⁅Dwt, Ecur n⁆ = (-(n : ℂ)) • Ecur n := Dwt_lie_Bet n


/-! ## §22  The colour-indexed currents and the full affine commutator -/

/-- The Wakimoto current of colour `a` (`0 = e`, `1 = f`, `2 = h`), matching the Chevalley
labelling `colE, colF, colH` of `Examples.AffineSl2`. -/
noncomputable def Jw (k : ℂ) (a : Fin 3) (n : ℤ) : Module.End ℂ WakFock :=
  if a = 0 then Ecur n else if a = 1 then Fcur k n else Hcur k n

theorem Jw_E (k : ℂ) (n : ℤ) : Jw k 0 n = Ecur n := by rw [Jw, if_pos rfl]

theorem Jw_F (k : ℂ) (n : ℤ) : Jw k 1 n = Fcur k n := by
  rw [Jw, if_neg (by decide : ¬ ((1 : Fin 3) = 0)), if_pos rfl]

theorem Jw_H (k : ℂ) (n : ℤ) : Jw k 2 n = Hcur k n := by
  rw [Jw, if_neg (by decide : ¬ ((2 : Fin 3) = 0)), if_neg (by decide : ¬ ((2 : Fin 3) = 1))]

/-- `[e_m, h_n] = -2 e_{m+n}`. -/
theorem rel_eh (k : ℂ) (m n : ℤ) : ⁅Ecur m, Hcur k n⁆ = (-2 : ℂ) • Ecur (m + n) := by
  rw [lie_swap, rel_he, show n + m = m + n from by ring]
  module

/-- `[f_m, h_n] = 2 f_{m+n}`. -/
theorem rel_fh (k : ℂ) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅Fcur k m, Hcur k n⁆ = (2 : ℂ) • Fcur k (m + n) := by
  rw [lie_swap, rel_hf k hk, show n + m = m + n from by ring]
  module

/-- `[f_m, e_n] = -h_{m+n} + m k δ_{m+n,0}`. -/
theorem rel_fe (k : ℂ) (m n : ℤ) :
    ⁅Fcur k m, Ecur n⁆
      = (-1 : ℂ) • Hcur k (m + n)
        + (if m + n = 0 then ((m : ℂ) * k) • (1 : Module.End ℂ WakFock) else 0) := by
  rw [lie_swap, rel_ef k n m, show n + m = m + n from by ring, neg_add]
  by_cases h : m + n = 0
  · rw [if_pos h, if_pos h]
    have hnm : (n : ℂ) = -(m : ℂ) := by
      have h' : n = -m := by omega
      rw [h']; push_cast; ring
    rw [hnm]
    module
  · rw [if_neg h, if_neg h]
    module

set_option maxHeartbeats 1000000 in
-- The nine-case Chevalley bash multiplies out three-term sums of operators in each case, which
-- exceeds the default elaboration budget.
/-- **The full affine `𝔰𝔩₂` commutator on the Wakimoto Fock space** — the exact analogue of
`AffineVOA.current_comm`, but on a free module with a manifest monomial basis:
`[J^a_m, J^b_n] = ∑_c f^{ab}_c J^c_{m+n} + m k κ(a,b) δ_{m+n,0}`. -/
theorem Jw_comm (k : ℂ) (hk : k + 2 ≠ 0) (a b : Fin 3) (m n : ℤ) :
    ⁅Jw k a m, Jw k b n⁆
      = (∑ c, AffineVOA.fabc a b c • Jw k c (m + n))
        + (if m + n = 0 then ((m : ℂ) * k * AffineVOA.kappa a b) •
            (1 : Module.End ℂ WakFock) else 0) := by
  rcases fin3_cases a with rfl | rfl | rfl <;> rcases fin3_cases b with rfl | rfl | rfl <;>
    simp only [Jw_E, Jw_F, Jw_H, Fin.sum_univ_three, AffineVOA.fabc, AffineVOA.kappa]
  · rw [rel_ee]; simp
  · rw [rel_ef k m n]
    by_cases h : m + n = 0
    · rw [if_pos h, if_pos h]; module
    · rw [if_neg h, if_neg h]; module
  · rw [rel_eh k m n]; simp
  · rw [rel_fe k m n]
    by_cases h : m + n = 0
    · rw [if_pos h, if_pos h]; module
    · rw [if_neg h, if_neg h]; module
  · rw [rel_ff k hk]; simp
  · rw [rel_fh k hk m n]; simp
  · rw [rel_he k m n]; simp
  · rw [rel_hf k hk m n]; simp
  · rw [rel_hh k hk m n]
    by_cases h : m + n = 0
    · rw [if_pos h, if_pos h]; module
    · rw [if_neg h, if_neg h]; module


/-! ## §23  The loop representation `(ℤ →₀ 𝔰𝔩₂) → End WakFock` -/

/-- The colour-linear extension `x ↦ ∑_a xₐ J^a_n` of the Wakimoto currents. -/
noncomputable def wakLoopₗ (k : ℂ) (n : ℤ) : AffineVOA.Sl2 →ₗ[ℂ] Module.End ℂ WakFock where
  toFun x := ∑ a, x a • Jw k a n
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

theorem wakLoopₗ_apply (k : ℂ) (n : ℤ) (x : AffineVOA.Sl2) :
    wakLoopₗ k n x = ∑ a, x a • Jw k a n := rfl

set_option maxHeartbeats 2000000 in
-- A nine-term bilinear expansion of `Jw_comm` over the Chevalley basis; the default budget is
-- not enough for the `module` normalisation.
/-- The affine commutator, extended bilinearly in the colour: this is the shape of the
`AffineLie` bracket with the cocycle realised by the level `k`. -/
theorem wakLoop_comm (k : ℂ) (hk : k + 2 ≠ 0) (x y : AffineVOA.Sl2) (m n : ℤ) :
    ⁅wakLoopₗ k m x, wakLoopₗ k n y⁆
      = wakLoopₗ k (m + n) ⁅x, y⁆
        + (if m + n = 0 then ((m : ℂ) * AffineVOA.kappaForm x y) •
            (k • (1 : Module.End ℂ WakFock)) else 0) := by
  simp only [wakLoopₗ_apply, AffineVOA.bracket_apply, AffineVOA.kappaForm_apply,
    Fin.sum_univ_three, add_lie, lie_add, smul_lie, lie_smul, Jw_comm k hk, smul_add,
    AffineVOA.fabc, AffineVOA.kappa]
  by_cases h : m + n = 0
  · simp only [if_pos h, smul_smul]
    module
  · simp only [if_neg h, smul_zero, add_zero]
    module

/-- The loop-algebra representation `(ℤ →₀ 𝔰𝔩₂) →ₗ[ℂ] End WakFock`. -/
noncomputable def Lw (k : ℂ) : (ℤ →₀ AffineVOA.Sl2) →ₗ[ℂ] Module.End ℂ WakFock :=
  Finsupp.lsum ℂ (fun n => wakLoopₗ k n)

@[simp] theorem Lw_single (k : ℂ) (n : ℤ) (x : AffineVOA.Sl2) :
    Lw k (Finsupp.single n x) = wakLoopₗ k n x := by
  rw [Lw, Finsupp.lsum_single]

theorem Dwt_lie_Jw (k : ℂ) (a : Fin 3) (n : ℤ) : ⁅Dwt, Jw k a n⁆ = (-(n : ℂ)) • Jw k a n := by
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [Jw_E, Dwt_lie_Ecur]
  · rw [Jw_F, Dwt_lie_Fcur]
  · rw [Jw_H, Dwt_lie_Hcur]

theorem Dwt_lie_Lw (k : ℂ) (g : ℤ →₀ AffineVOA.Sl2) :
    ⁅-Dwt, Lw k g⁆ = Lw k (loopDeriv g) := by
  induction g using Finsupp.induction_linear with
  | zero => rw [map_zero, lie_zero, map_zero, map_zero]
  | add g₁ g₂ h₁ h₂ => rw [map_add, lie_add, h₁, h₂, map_add, map_add]
  | single n y =>
      rw [Lw_single, loopDeriv_single, Lw_single, wakLoopₗ_apply, wakLoopₗ_apply, neg_lie]
      simp only [Fin.sum_univ_three, lie_add, lie_smul, Dwt_lie_Jw, Pi.smul_apply, smul_eq_mul,
        smul_smul, neg_add]
      module

theorem Lw_comm (k : ℂ) (hk : k + 2 ≠ 0) (f g : ℤ →₀ AffineVOA.Sl2) :
    ⁅Lw k f, Lw k g⁆
      = Lw k (loopBracket f g)
        + (cocycle AffineVOA.kappaForm f g) • (k • (1 : Module.End ℂ WakFock)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      have hsplit : ⁅Lw k (f₁ + f₂), Lw k g⁆ = ⁅Lw k f₁, Lw k g⁆ + ⁅Lw k f₂, Lw k g⁆ := by
        rw [map_add, add_lie]
      rw [hsplit, h₁, h₂]
      simp only [map_add, LinearMap.add_apply, add_smul]
      abel
  | single m x =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ h₁ h₂ =>
          have hsplit : ⁅Lw k (Finsupp.single m x), Lw k (g₁ + g₂)⁆
              = ⁅Lw k (Finsupp.single m x), Lw k g₁⁆ + ⁅Lw k (Finsupp.single m x), Lw k g₂⁆ := by
            rw [map_add, lie_add]
          rw [hsplit, h₁, h₂]
          simp only [map_add, add_smul]
          abel
      | single n y =>
          rw [Lw_single, Lw_single, wakLoop_comm k hk, loopBracket_single, Lw_single,
            cocycle_single]
          by_cases h : m + n = 0
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, zero_smul]


/-! ## §24  The Wakimoto representation of the affine algebra `𝔰𝔩₂^` -/

/-- The product model of the affine algebra `𝔰𝔩₂^`. -/
noncomputable abbrev opW : ((ℤ →₀ AffineVOA.Sl2) × ℂ × ℂ) ≃ AffineVOA.AffSl2 :=
  AffineLie.ofProd AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant

/-- The underlying linear map of the Wakimoto representation: the loop part acts by the
currents, `C` by the level `k`, and `ℓ₀` by `-Dwt`. -/
noncomputable def wakRhoₗ (k : ℂ) : AffineVOA.AffSl2 →ₗ[ℂ] Module.End ℂ WakFock where
  toFun X :=
    Lw k (opW.symm X).1 + ((opW.symm X).2.1) • (k • (1 : Module.End ℂ WakFock))
      + ((opW.symm X).2.2) • (-Dwt)
  map_add' X Y := by
    simp only [AffineLie.of_symm_add, Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' r X := by
    simp only [AffineLie.of_symm_smul, Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply,
      smul_add, smul_smul]
    module

theorem wakRhoₗ_apply (k : ℂ) (X : AffineVOA.AffSl2) :
    wakRhoₗ k X = Lw k (opW.symm X).1 + ((opW.symm X).2.1) • (k • (1 : Module.End ℂ WakFock))
      + ((opW.symm X).2.2) • (-Dwt) := rfl

theorem lie_central_left (c k : ℂ) (A : Module.End ℂ WakFock) :
    ⁅c • (k • (1 : Module.End ℂ WakFock)), A⁆ = 0 := by rw [smul_smul, central_lie]

theorem lie_central_right (c k : ℂ) (A : Module.End ℂ WakFock) :
    ⁅A, c • (k • (1 : Module.End ℂ WakFock))⁆ = 0 := by
  rw [lie_swap, lie_central_left, neg_zero]

set_option maxHeartbeats 1000000 in
-- The `map_lie'` bookkeeping expands a nine-term bracket of three-component elements.
/-- **The Wakimoto representation** `𝔰𝔩₂^ →ₗ⁅ℂ⁆ End ℂ WakFock` at any non-critical level `k`. -/
noncomputable def wakRho (k : ℂ) (hk : k + 2 ≠ 0) :
    AffineVOA.AffSl2 →ₗ⁅ℂ⁆ Module.End ℂ WakFock :=
  { wakRhoₗ k with
    map_lie' := by
      intro X Y
      change wakRhoₗ k ⁅X, Y⁆ = ⁅wakRhoₗ k X, wakRhoₗ k Y⁆
      set f := (opW.symm X).1 with hf
      set c := (opW.symm X).2.1 with hc
      set d := (opW.symm X).2.2 with hd
      set g := (opW.symm Y).1 with hg
      set c' := (opW.symm Y).2.1 with hc'
      set d' := (opW.symm Y).2.2 with hd'
      have hbr : opW.symm ⁅X, Y⁆
          = AffineLie.bracketP AffineVOA.kappaForm (opW.symm X) (opW.symm Y) :=
        Equiv.symm_apply_apply _ _
      have hL : wakRhoₗ k ⁅X, Y⁆
          = Lw k (loopBracket f g + d • loopDeriv g - d' • loopDeriv f)
            + (cocycle AffineVOA.kappaForm f g) • (k • (1 : Module.End ℂ WakFock)) := by
        rw [wakRhoₗ_apply, hbr]
        simp only [AffineLie.bracketP, zero_smul, add_zero]
        rw [← hf, ← hd, ← hg, ← hd']
      have hR : ⁅wakRhoₗ k X, wakRhoₗ k Y⁆
          = ⁅Lw k f, Lw k g⁆ + d' • ⁅Lw k f, -Dwt⁆ + d • ⁅-Dwt, Lw k g⁆ := by
        rw [wakRhoₗ_apply, wakRhoₗ_apply, ← hf, ← hc, ← hd, ← hg, ← hc', ← hd']
        simp only [add_lie, lie_add, smul_lie, lie_smul, one_lie', lie_one', lie_self,
          smul_zero, add_zero]
        abel
      have hDf : ⁅Lw k f, -Dwt⁆ = -Lw k (loopDeriv f) := by
        rw [lie_swap, Dwt_lie_Lw]
      rw [hL, hR, Lw_comm k hk, Dwt_lie_Lw, hDf, map_sub, map_add, map_smul, map_smul]
      module }

@[simp] theorem wakRho_ofLoop (k : ℂ) (hk : k + 2 ≠ 0) (x : AffineVOA.Sl2) (n : ℤ) :
    wakRho k hk (AffineLie.ofLoop AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant x n)
      = wakLoopₗ k n x := by
  change wakRhoₗ k _ = _
  rw [wakRhoₗ_apply]
  simp only [AffineLie.ofLoop, Equiv.symm_apply_apply, Lw_single, zero_smul, add_zero]

@[simp] theorem wakRho_C (k : ℂ) (hk : k + 2 ≠ 0) :
    wakRho k hk (AffineLie.C AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant)
      = k • (1 : Module.End ℂ WakFock) := by
  change wakRhoₗ k _ = _
  rw [wakRhoₗ_apply]
  simp only [AffineLie.C, Equiv.symm_apply_apply, map_zero, zero_add, one_smul, zero_smul,
    add_zero]

@[simp] theorem wakRho_ell0 (k : ℂ) (hk : k + 2 ≠ 0) :
    wakRho k hk (AffineLie.ell0 AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant) = -Dwt := by
  change wakRhoₗ k _ = _
  rw [wakRhoₗ_apply]
  simp only [AffineLie.ell0, Equiv.symm_apply_apply, map_zero, zero_add, zero_smul, one_smul]


/-! ## §25  The `pbw`-free evaluation `V^k(𝔰𝔩₂) → WakFock` -/

/-- Shorthand for the universal enveloping algebra `U(𝔰𝔩₂^)`. -/
noncomputable abbrev UW :=
  AffineLie.UEnv AffineVOA.Sl2 AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant

/-- The generator `ι(eₐ ⊗ tᵐ) ∈ U(𝔰𝔩₂^)`. -/
noncomputable def genW (a : Fin 3) (m : ℤ) : UW :=
  UniversalEnvelopingAlgebra.ι ℂ
    (AffineLie.ofLoop AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant
      (AffineVOA.basis a) m)

/-- The algebra map `U(𝔰𝔩₂^) → End ℂ WakFock` of the Wakimoto representation. -/
noncomputable def evAlgW (k : ℂ) (hk : k + 2 ≠ 0) : UW →ₐ[ℂ] Module.End ℂ WakFock :=
  UniversalEnvelopingAlgebra.lift ℂ (wakRho k hk)

theorem evAlgW_ι (k : ℂ) (hk : k + 2 ≠ 0) (X : AffineVOA.AffSl2) :
    evAlgW k hk (UniversalEnvelopingAlgebra.ι ℂ X) = wakRho k hk X := by
  rw [evAlgW, UniversalEnvelopingAlgebra.lift_ι_apply]

/-- The Wakimoto **vacuum evaluation** `w ↦ ρ(w)|0⟩`, a `ℂ`-linear map `U(𝔰𝔩₂^) → WakFock`. -/
noncomputable def valW (k : ℂ) (hk : k + 2 ≠ 0) : UW →ₗ[ℂ] WakFock where
  toFun w := evAlgW k hk w (1 : WakFock)
  map_add' w w' := by rw [map_add, LinearMap.add_apply]
  map_smul' r w := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem valW_apply (k : ℂ) (hk : k + 2 ≠ 0) (w : UW) :
    valW k hk w = evAlgW k hk w (1 : WakFock) := rfl

@[simp] theorem valW_one (k : ℂ) (hk : k + 2 ≠ 0) : valW k hk 1 = (1 : WakFock) := by
  have h : evAlgW k hk 1 = 1 := map_one (evAlgW k hk)
  calc valW k hk 1 = evAlgW k hk 1 (1 : WakFock) := rfl
    _ = (1 : Module.End ℂ WakFock) (1 : WakFock) := by rw [h]
    _ = (1 : WakFock) := rfl

theorem wakRho_basis (k : ℂ) (hk : k + 2 ≠ 0) (a : Fin 3) (m : ℤ) :
    wakRho k hk (AffineLie.ofLoop AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant
      (AffineVOA.basis a) m) = Jw k a m := by
  rw [wakRho_ofLoop, wakLoopₗ_apply, Finset.sum_eq_single a]
  · rw [AffineVOA.basis, Pi.single_eq_same, one_smul]
  · intro b _ hb
    rw [AffineVOA.basis, Pi.single_eq_of_ne hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The evaluation intertwines the generators with the Wakimoto currents. -/
theorem valW_gen (k : ℂ) (hk : k + 2 ≠ 0) (a : Fin 3) (m : ℤ) (w : UW) :
    valW k hk (genW a m * w) = Jw k a m (valW k hk w) := by
  rw [valW_apply, map_mul, Module.End.mul_apply, genW, evAlgW_ι, wakRho_basis, valW_apply]

theorem Jw_vac (k : ℂ) (a : Fin 3) {n : ℤ} (h : 0 ≤ n) : Jw k a n (1 : WakFock) = 0 := by
  rcases fin3_cases a with rfl | rfl | rfl
  · rw [Jw_E]; exact Ecur_one h
  · rw [Jw_F]; exact Fcur_one k h
  · rw [Jw_H]; exact Hcur_one k h

theorem wakLoop_vac (k : ℂ) {n : ℤ} (h : 0 ≤ n) (x : AffineVOA.Sl2) :
    wakLoopₗ k n x (1 : WakFock) = 0 := by
  rw [wakLoopₗ_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Jw_vac k _ h, smul_zero,
    Finset.sum_const_zero]

/-- The generators of the vacuum ideal are killed at the Fock vacuum. -/
theorem valW_vacuumGens (k : ℂ) (hk : k + 2 ≠ 0) (a : UW)
    (ha : a ∈ AffineLie.vacuumGens AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant k) :
    valW k hk a = 0 := by
  rcases ha with ⟨x, n, hn, rfl⟩ | rfl | rfl
  · rw [valW_apply, evAlgW_ι, wakRho_ofLoop]
    exact wakLoop_vac k hn x
  · rw [valW_apply, map_sub, LinearMap.sub_apply, evAlgW_ι, wakRho_C, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, sub_self]
  · rw [valW_apply, evAlgW_ι, wakRho_ell0, LinearMap.neg_apply, Dwt, Eul_one', neg_zero]

/-- The whole vacuum ideal is killed at the Fock vacuum. -/
theorem valW_vacuumIdeal (k : ℂ) (hk : k + 2 ≠ 0) (w : UW)
    (hw : w ∈ AffineLie.vacuumIdeal AffineVOA.kappaForm AffineVOA.kappaForm_isInvariant k) :
    valW k hk w = 0 := by
  induction hw using Submodule.span_induction with
  | mem g hg => exact valW_vacuumGens k hk g hg
  | zero => rw [map_zero]
  | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | smul r u _ hu =>
      rw [show (r • u : UW) = r * u from rfl, valW_apply, map_mul, Module.End.mul_apply,
        ← valW_apply, hu, map_zero]


/-! ## §26  The main result: `sl2Singular ≠ 0` at `k = -4/3`, `pbw`-free -/

theorem vacuumA_mk (k : ℂ) : AffineVOA.vacuumA k = Submodule.Quotient.mk (1 : UW) := rfl

theorem J_mk (k : ℂ) (a : Fin 3) (m : ℤ) (w : UW) :
    AffineVOA.J k a m (Submodule.Quotient.mk w) = Submodule.Quotient.mk (genW a m * w) := by
  rw [AffineVOA.J_eq, AffineLie.vacuumRho_mk]
  rfl

/-- The word `e₋₃ ∈ U(𝔰𝔩₂^)`. -/
noncomputable def wM1 : UW := genW 0 (-3) * 1
/-- The word `e₋₂ h₋₁`. -/
noncomputable def wM2 : UW := genW 0 (-2) * (genW 2 (-1) * 1)
/-- The word `h₋₂ e₋₁`. -/
noncomputable def wM3 : UW := genW 2 (-2) * (genW 0 (-1) * 1)
/-- The word `e₋₁ e₋₁ f₋₁`. -/
noncomputable def wM4 : UW := genW 0 (-1) * (genW 0 (-1) * (genW 1 (-1) * 1))
/-- The word `e₋₁ h₋₁ h₋₁`. -/
noncomputable def wM5 : UW := genW 0 (-1) * (genW 2 (-1) * (genW 2 (-1) * 1))

/-- The word representing the weight-3 singular vector. -/
noncomputable def wSing : UW :=
  (20 : ℂ) • wM1 + (-12 : ℂ) • wM2 + (-6 : ℂ) • wM3 + (36 : ℂ) • wM4 + (9 : ℂ) • wM5

theorem M1_mk (k : ℂ) : Sl2Sing.M1 k = Submodule.Quotient.mk wM1 := by
  rw [Sl2Sing.M1_def, vacuumA_mk, J_mk]; rfl

theorem M2_mk (k : ℂ) : Sl2Sing.M2 k = Submodule.Quotient.mk wM2 := by
  rw [Sl2Sing.M2_def, vacuumA_mk, J_mk, J_mk]; rfl

theorem M3_mk (k : ℂ) : Sl2Sing.M3 k = Submodule.Quotient.mk wM3 := by
  rw [Sl2Sing.M3_def, vacuumA_mk, J_mk, J_mk]; rfl

theorem M4_mk (k : ℂ) : Sl2Sing.M4 k = Submodule.Quotient.mk wM4 := by
  rw [Sl2Sing.M4_def, vacuumA_mk, J_mk, J_mk, J_mk]; rfl

theorem M5_mk (k : ℂ) : Sl2Sing.M5 k = Submodule.Quotient.mk wM5 := by
  rw [Sl2Sing.M5_def, vacuumA_mk, J_mk, J_mk, J_mk]; rfl

theorem sl2Singular_mk : Sl2Sing.sl2Singular = Submodule.Quotient.mk wSing := by
  rw [Sl2Sing.sl2Singular_def, Sl2Sing.ansatz_def, M1_mk, M2_mk, M3_mk, M4_mk, M5_mk, wSing]
  simp only [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]

theorem valW_wSing (k : ℂ) (hk : k + 2 ≠ 0) :
    valW k hk wSing
      = (20 : ℂ) • Ecur (-3) (1 : WakFock)
        + (-12 : ℂ) • Ecur (-2) (Hcur k (-1) (1 : WakFock))
        + (-6 : ℂ) • Hcur k (-2) (Ecur (-1) (1 : WakFock))
        + (36 : ℂ) • Ecur (-1) (Ecur (-1) (Fcur k (-1) (1 : WakFock)))
        + (9 : ℂ) • Ecur (-1) (Hcur k (-1) (Hcur k (-1) (1 : WakFock))) := by
  rw [wSing, wM1, wM2, wM3, wM4, wM5]
  simp only [map_add, map_smul, valW_gen, valW_one, Jw_E, Jw_F, Jw_H]

/-! ### The separating functional: `γ₃` followed by the constant term -/

theorem Gam_Ecur_lie (u n : ℤ) :
    ⁅Gam u, Ecur n⁆ = -(if n + u = 0 then (1 : Module.End ℂ WakFock) else 0) := Gam_Bet_lie n u

theorem Gam_Hcur_lie (k : ℂ) (u n : ℤ) : ⁅Gam u, Hcur k n⁆ = (2 : ℂ) • Gam (n + u) := by
  rw [lie_swap, Hcur_lie_Gam]; module

theorem Gam_Fcur_lie (k : ℂ) (u n : ℤ) : ⁅Gam u, Fcur k n⁆ = GG (n + u) := by
  rw [lie_swap, Fcur_lie_Gam, neg_neg]

/-- `γ₃` applied to `h₋₁|0⟩` vanishes. -/
theorem Gam3_H1 (k : ℂ) : Gam 3 (Hcur k (-1) (1 : WakFock)) = 0 := by
  rw [apply_comp, Gam_Hcur_lie, Gam_one (show (1 : ℤ) ≤ 3 by norm_num), map_zero, add_zero,
    LinearMap.smul_apply, show (-1 : ℤ) + 3 = 2 from by norm_num,
    Gam_one (show (1 : ℤ) ≤ 2 by norm_num), smul_zero]

/-- `γ₂` applied to `h₋₁|0⟩` vanishes. -/
theorem Gam2_H1 (k : ℂ) : Gam 2 (Hcur k (-1) (1 : WakFock)) = 0 := by
  rw [apply_comp, Gam_Hcur_lie, Gam_one (show (1 : ℤ) ≤ 2 by norm_num), map_zero, add_zero,
    LinearMap.smul_apply, show (-1 : ℤ) + 2 = 1 from by norm_num,
    Gam_one (show (1 : ℤ) ≤ 1 by norm_num), smul_zero]

theorem Gam3_M1 : Gam 3 (Ecur (-3) (1 : WakFock)) = -(1 : WakFock) := by
  rw [apply_comp, Gam_Ecur_lie, Gam_one (show (1 : ℤ) ≤ 3 by norm_num), map_zero, add_zero,
    if_pos (show (-3 : ℤ) + 3 = 0 by norm_num)]
  simp

theorem Gam3_M2 (k : ℂ) : Gam 3 (Ecur (-2) (Hcur k (-1) (1 : WakFock))) = 0 := by
  rw [apply_comp, Gam3_H1, map_zero, add_zero, Gam_Ecur_lie,
    if_neg (show ¬((-2 : ℤ) + 3 = 0) by norm_num)]
  simp

theorem Gam3_M3 (k : ℂ) :
    Gam 3 (Hcur k (-2) (Ecur (-1) (1 : WakFock))) = (-2 : ℂ) • (1 : WakFock) := by
  have hE : Gam 3 (Ecur (-1) (1 : WakFock)) = 0 := by
    rw [apply_comp, Gam_Ecur_lie, Gam_one (show (1 : ℤ) ≤ 3 by norm_num), map_zero, add_zero,
      if_neg (show ¬((-1 : ℤ) + 3 = 0) by norm_num)]
    simp
  have hG1 : Gam 1 (Ecur (-1) (1 : WakFock)) = -(1 : WakFock) := by
    rw [apply_comp, Gam_Ecur_lie, Gam_one (show (1 : ℤ) ≤ 1 by norm_num), map_zero, add_zero,
      if_pos (show (-1 : ℤ) + 1 = 0 by norm_num)]
    simp
  rw [apply_comp, hE, map_zero, add_zero, Gam_Hcur_lie, LinearMap.smul_apply,
    show (-2 : ℤ) + 3 = 1 from by norm_num, hG1]
  module

theorem Gam3_M4 (k : ℂ) :
    Gam 3 (Ecur (-1) (Ecur (-1) (Fcur k (-1) (1 : WakFock)))) = 0 := by
  have hF : Gam 3 (Fcur k (-1) (1 : WakFock)) = 0 := by
    rw [apply_comp, Gam_Fcur_lie, Gam_one (show (1 : ℤ) ≤ 3 by norm_num), map_zero, add_zero,
      show (-1 : ℤ) + 3 = 2 from by norm_num, GG_one (show (1 : ℤ) ≤ 2 by norm_num)]
  have hstep : ∀ Q : WakFock, Gam 3 Q = 0 → Gam 3 (Ecur (-1) Q) = 0 := by
    intro Q hQ
    rw [apply_comp, hQ, map_zero, add_zero, Gam_Ecur_lie,
      if_neg (show ¬((-1 : ℤ) + 3 = 0) by norm_num)]
    simp
  exact hstep _ (hstep _ hF)

theorem Gam3_M5 (k : ℂ) :
    Gam 3 (Ecur (-1) (Hcur k (-1) (Hcur k (-1) (1 : WakFock)))) = 0 := by
  have hHH : Gam 3 (Hcur k (-1) (Hcur k (-1) (1 : WakFock))) = 0 := by
    rw [apply_comp, Gam3_H1, map_zero, add_zero, Gam_Hcur_lie, LinearMap.smul_apply,
      show (-1 : ℤ) + 3 = 2 from by norm_num, Gam2_H1, smul_zero]
  rw [apply_comp, hHH, map_zero, add_zero, Gam_Ecur_lie,
    if_neg (show ¬((-1 : ℤ) + 3 = 0) by norm_num)]
  simp

/-- **The separating computation**: `γ₃` sends the Wakimoto image of the singular vector to the
nonzero constant `-8`. -/
theorem Gam3_valW_wSing (k : ℂ) (hk : k + 2 ≠ 0) :
    Gam 3 (valW k hk wSing) = (-8 : ℂ) • (1 : WakFock) := by
  rw [valW_wSing k hk]
  simp only [map_add, map_smul, Gam3_M1, Gam3_M2, Gam3_M3, Gam3_M4, Gam3_M5, smul_zero]
  module

theorem hk43 : (-4 / 3 : ℂ) + 2 ≠ 0 := by norm_num

/-- **The singular vector of `V^{-4/3}(𝔰𝔩₂)` is nonzero** — proved `pbw`-free by the
Wakimoto free-field realization.  This discharges the standing conditional of
`Examples.AffineSl2Indep`. -/
theorem sl2Singular_ne_zero : Sl2Sing.sl2Singular ≠ 0 := by
  intro h
  have hmem : wSing ∈ AffineLie.vacuumIdeal AffineVOA.kappaForm
      AffineVOA.kappaForm_isInvariant (-4 / 3 : ℂ) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← sl2Singular_mk]
    exact h
  have h0 : valW (-4 / 3 : ℂ) hk43 wSing = 0 := valW_vacuumIdeal _ hk43 _ hmem
  have h1 := Gam3_valW_wSing (-4 / 3 : ℂ) hk43
  rw [h0, map_zero] at h1
  have h2 : ((-8 : ℂ) • (1 : WakFock)) ≠ 0 := by
    rw [smul_ne_zero_iff]
    exact ⟨by norm_num, one_ne_zero⟩
  exact h2 h1.symm

/-- **The five weight-3 charge-2 monomials are linearly independent at `k = -4/3`.** -/
theorem M_indep_sing :
    LinearIndependent ℂ ![Sl2Sing.M1 (-4 / 3 : ℂ), Sl2Sing.M2 (-4 / 3 : ℂ),
      Sl2Sing.M3 (-4 / 3 : ℂ), Sl2Sing.M4 (-4 / 3 : ℂ), Sl2Sing.M5 (-4 / 3 : ℂ)] :=
  Sl2Indep.indep_iff_sl2Singular_ne_zero.mpr sl2Singular_ne_zero

/-- The vacuum of `V^k(𝔰𝔩₂)` is nonzero, `pbw`-free, for every non-critical level. -/
theorem vacuumA_ne_zero_free (k : ℂ) (hk : k + 2 ≠ 0) : AffineVOA.vacuumA k ≠ 0 := by
  intro h
  have hmem : (1 : UW) ∈ AffineLie.vacuumIdeal AffineVOA.kappaForm
      AffineVOA.kappaForm_isInvariant k := by
    rw [← Submodule.Quotient.mk_eq_zero, ← vacuumA_mk]
    exact h
  have h0 : valW k hk 1 = 0 := valW_vacuumIdeal _ hk _ hmem
  rw [valW_one] at h0
  exact one_ne_zero h0

end VOA.Wak
