/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VertexOperatorAlgebra
import VOA.Foundations.FormalCalculus
import VOA.Foundations.Locality
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The rank-`r` Heisenberg Fock space  (Gannon §5.2.2, rank `r`)

The mechanical rank-`r` generalization of the rank-1 Heisenberg foundations
(`Examples/HeisenbergFock`).  Everything is re-derived under the dedicated namespace
`VOA.HeisenbergN`; no rank-1 short-names are shadowed.

## The model
The Fock space is `FockN r := MvPolynomial (ℕ × Fin r) ℂ`: the variable `(i,a)`
stands for the negative mode `aᵃ₋(i+1)` of the `a`-th boson, and the monomial
`∏ X₍ᵢ,ₐ₎^{e₍ᵢ,ₐ₎}` is the corresponding creation state on the vacuum.

* **Oscillators** `oscN r k a n : FockN r →ₗ[ℂ] FockN r` (level `k`, family `a : Fin r`):
  - `n < 0` (creation `aᵃ₋ₘ`): multiplication by `X ((-n-1).toNat, a)`;
  - `n > 0` (annihilation `aᵃₙ`): `(n : ℂ) • k • pderiv ((n-1).toNat, a)`;
  - `n = 0`: `0`.
* **Commutation** (Gannon 3.2.12a, rank `r`):
  `[aᵃₘ, aᵇₙ] = m δ_{m+n,0} δ^{ab} k · id` — the Kronecker `δ^{ab}` on the family index
  is the only change from rank-1.
* **Vacuum** `1`, with `aᵃₙ 1 = 0` for `n ≥ 0`.
* **L₀-grading**: `weightFnN (i,a) = i + 1`, independent of the family `a`.
* **Currents** `currentN r k a j = oscN r k a (-j-1)`, mode `oscN r k a m`.
* **Self/cross-locality**: `(z₁-z₂)²·[αᵃ(z₁),αᵇ(z₂)] = 0` for **all** `a,b`: distinct
  families commute exactly (`N = 0`), same family is the rank-1 `δ`-derivative (`N = 2`);
  `mulBySubPow 2` kills both.

## Status
Concrete model, fully axiom-clean
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.2.2, eqs. (5.2.5); FLM Ch. 2; Kac §3.5; Lepowsky–Li Ch. 6.
-/

namespace VOA

namespace HeisenbergN

open scoped BigOperators
open MvPolynomial

/-! ## The Fock space and the oscillators -/

/-- The rank-`r` Heisenberg **Fock space** `FockN r = MvPolynomial (ℕ × Fin r) ℂ`. The
variable `(i, a)` represents the negative mode `aᵃ₋(i+1)` of the `a`-th boson. -/
abbrev FockN (r : ℕ) : Type := MvPolynomial (ℕ × Fin r) ℂ

/-- The **multiplication** endomorphism `p ↦ X_{(i,a)} · p` of the rank-`r` Fock space. -/
noncomputable def mulXN {r : ℕ} (i : ℕ) (a : Fin r) : FockN r →ₗ[ℂ] FockN r :=
  (LinearMap.mul ℂ (FockN r) (X (i, a))).comp (LinearMap.id)

/-- Evaluating a creation endomorphism multiplies the polynomial by its oscillator variable. This connects the linear-map packaging to ordinary polynomial multiplication. -/
@[simp] theorem mulXN_apply {r : ℕ} (i : ℕ) (a : Fin r) (p : FockN r) :
    mulXN i a p = X (i, a) * p := rfl

/-- The partial-derivative endomorphism `pderiv (i,a)` of the rank-`r` Fock space. -/
noncomputable def pderivLMN {r : ℕ} (i : ℕ) (a : Fin r) : FockN r →ₗ[ℂ] FockN r :=
  (pderiv (i, a) : Derivation ℂ (FockN r) (FockN r)).toLinearMap

/-- Evaluating the annihilation derivative endomorphism is exactly the ordinary partial derivative. No change of normalization occurs when passing to linear maps. -/
@[simp] theorem pderivLMN_apply {r : ℕ} (i : ℕ) (a : Fin r) (p : FockN r) :
    pderivLMN i a p = pderiv (i, a) p := rfl

/-- The rank-`r` Heisenberg **oscillators** `aᵃₙ = oscN r k a n` on the Fock space, level
`k`, family `a : Fin r` (Gannon §5.2.2, rank `r`):

* `n < 0` (creation `aᵃ₋ₘ`): multiplication by `X ((-n-1).toNat, a)`;
* `n > 0` (annihilation `aᵃₙ`): `(n : ℂ) • k • pderiv ((n-1).toNat, a)`;
* `n = 0`: `0`. -/
noncomputable def oscN (r : ℕ) (k : ℂ) (a : Fin r) (n : ℤ) : FockN r →ₗ[ℂ] FockN r :=
  if n < 0 then mulXN (-n - 1).toNat a
  else if 0 < n then (n : ℂ) • k • pderivLMN (n - 1).toNat a
  else 0

/-- A negative oscillator mode is the creation endomorphism at index -n-1. The nonnegative polynomial index encodes the positive energy -n. -/
@[simp] theorem oscN_neg (r : ℕ) (k : ℂ) (a : Fin r) {n : ℤ} (hn : n < 0) :
    oscN r k a n = mulXN (-n - 1).toNat a := by
  rw [oscN, if_pos hn]

/-- A positive oscillator mode is differentiation multiplied by the mode number and the Heisenberg level. This factor produces the central term in the oscillator commutator. -/
@[simp] theorem oscN_pos (r : ℕ) (k : ℂ) (a : Fin r) {n : ℤ} (hn : 0 < n) :
    oscN r k a n = (n : ℂ) • k • pderivLMN (n - 1).toNat a := by
  rw [oscN, if_neg (by omega), if_pos hn]

/-- The neutral Fock module has zero current charge: its zero oscillator mode is the zero operator on every polynomial. -/
@[simp] theorem oscN_zero (r : ℕ) (k : ℂ) (a : Fin r) : oscN r k a 0 = 0 := by
  rw [oscN, if_neg (by omega), if_neg (by omega)]

/-- Creation-mode application: `aᵃ₋ₘ p = X_{(m-1,a)} · p`. -/
theorem oscN_apply_neg (r : ℕ) (k : ℂ) (a : Fin r) {n : ℤ} (hn : n < 0) (p : FockN r) :
    oscN r k a n p = X ((-n - 1).toNat, a) * p := by
  rw [oscN_neg r k a hn, mulXN_apply]

/-- Annihilation-mode application: `aᵃₙ p = (n·k) · ∂_{X_{(n-1,a)}} p`. -/
theorem oscN_apply_pos (r : ℕ) (k : ℂ) (a : Fin r) {n : ℤ} (hn : 0 < n) (p : FockN r) :
    oscN r k a n p = (n : ℂ) • k • pderiv ((n - 1).toNat, a) p := by
  rw [oscN_pos r k a hn]; rfl

/-! ## The fundamental per-variable commutators -/

/-- The canonical commutator on the rank-`r` Fock space, same variable:
`∂_{(i,a)}(X_{(i,a)}·p) - X_{(i,a)}·∂_{(i,a)}p = p`. -/
theorem pderiv_comm_mulXN_self {r : ℕ} (i : ℕ) (a : Fin r) (p : FockN r) :
    pderiv (i, a) (X (i, a) * p) - X (i, a) * pderiv (i, a) p = p := by
  rw [pderiv_mul, pderiv_X_self, one_mul]
  ring

/-- Different variables commute: `∂_{(j,b)}(X_{(i,a)}·p) = X_{(i,a)}·∂_{(j,b)}p` when
`(j,b) ≠ (i,a)` (covers both `i ≠ j` and the cross-family `a ≠ b` case). -/
theorem pderiv_comm_mulXN_of_ne {r : ℕ} {i j : ℕ} {a b : Fin r} (h : (j, b) ≠ (i, a))
    (p : FockN r) :
    pderiv (j, b) (X (i, a) * p) = X (i, a) * pderiv (j, b) p := by
  rw [pderiv_mul, pderiv_X_of_ne (Ne.symm h), zero_mul, zero_add]

/-- Partial derivatives commute on the rank-`r` Fock space. -/
theorem pderiv_commN {r : ℕ} (u v : ℕ × Fin r) (p : FockN r) :
    pderiv u (pderiv v p) = pderiv v (pderiv u p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s h =>
    rw [pderiv_mul, pderiv_mul, map_add, map_add, pderiv_mul, pderiv_mul]
    simp only [pderiv_X, Pi.single_apply, h]
    by_cases hsu : s = u <;> by_cases hsv : s = v <;>
      simp_all <;> ring

/-! ## The commutation relation `[aᵃₘ, aᵇₙ] = m δ_{m+n,0} δ^{ab} k`  (Gannon 3.2.12a) -/

/-- **The rank-`r` Heisenberg commutation relation** (Gannon 3.2.12a, rank `r`):
`[aᵃₘ, aᵇₙ] = m δ_{m+n,0} δ^{ab} k · id`. The Kronecker `δ^{ab}` on the family index is the
only change from rank-1: the cross-family (`a ≠ b`) operators commute on the nose because
they act on disjoint variable families. -/
theorem oscN_comm (r : ℕ) (k : ℂ) (a b : Fin r) (m n : ℤ) :
    oscN r k a m * oscN r k b n - oscN r k b n * oscN r k a m
      = (if a = b ∧ m + n = 0 then (m : ℂ) * k else 0) • LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
  show oscN r k a m (oscN r k b n p) - oscN r k b n (oscN r k a m p)
      = (if a = b ∧ m + n = 0 then (m : ℂ) * k else 0) • p
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · -- both creation: mults by X commute, and m+n ≠ 0
      rw [oscN_apply_neg r k a hm, oscN_apply_neg r k b hn,
          oscN_apply_neg r k b hn, oscN_apply_neg r k a hm]
      rw [if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
      rw [mul_left_comm (X ((-m - 1).toNat, a)), sub_self]
    · -- n = 0
      subst hn
      rw [oscN_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero,
          if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
    · -- m < 0 < n : creation × annihilation
      rw [oscN_apply_neg r k a hm, oscN_apply_pos r k b hn,
          oscN_apply_pos r k b hn, oscN_apply_neg r k a hm]
      set i := (-m - 1).toNat with hi
      set j := (n - 1).toNat with hj
      rw [mul_smul_comm, mul_smul_comm, ← smul_sub, ← smul_sub]
      by_cases hab : a = b
      · subst hab
        by_cases hmn : m + n = 0
        · -- same family, same variable: coefficient m·k
          have hji : j = i := by rw [hj, hi]; omega
          rw [if_pos ⟨rfl, hmn⟩, hji]
          have hcore : X (i, a) * pderiv (i, a) p - pderiv (i, a) (X (i, a) * p) = -p := by
            have := pderiv_comm_mulXN_self i a p; linear_combination -this
          rw [hcore]
          have hnm : (n : ℂ) = -(m : ℂ) := by
            have : n = -m := by omega
            rw [this]; push_cast; ring
          rw [smul_neg, smul_neg, smul_smul, ← neg_smul]
          congr 1
          rw [hnm]; ring
        · -- same family, different variable: commute, RHS = 0
          have hji : (j, a) ≠ (i, a) := by
            simp only [ne_eq, Prod.mk.injEq, and_true]; rw [hj, hi]; omega
          rw [if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
          rw [pderiv_comm_mulXN_of_ne hji p, sub_self, smul_zero, smul_zero]
      · -- different family: disjoint variables, commute, RHS = 0
        have hji : (j, b) ≠ (i, a) := by
          simp only [ne_eq, Prod.mk.injEq]; exact fun h => hab (h.2.symm)
        rw [if_neg (by rintro ⟨h, _⟩; exact hab h), zero_smul]
        rw [pderiv_comm_mulXN_of_ne hji p, sub_self, smul_zero, smul_zero]
  · -- m = 0
    subst hm
    rw [oscN_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero]
    by_cases h : a = b ∧ (0 : ℤ) + n = 0
    · rw [if_pos h]; simp
    · rw [if_neg h, zero_smul]
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · -- n < 0 < m : annihilation × creation (mirror)
      rw [oscN_apply_pos r k a hm, oscN_apply_neg r k b hn,
          oscN_apply_neg r k b hn, oscN_apply_pos r k a hm]
      set i := (-n - 1).toNat with hi
      set j := (m - 1).toNat with hj
      rw [mul_smul_comm, mul_smul_comm, ← smul_sub, ← smul_sub]
      by_cases hab : a = b
      · subst hab
        by_cases hmn : m + n = 0
        · have hji : j = i := by rw [hj, hi]; omega
          rw [if_pos ⟨rfl, hmn⟩, hji]
          have hcore : pderiv (i, a) (X (i, a) * p) - X (i, a) * pderiv (i, a) p = p :=
            pderiv_comm_mulXN_self i a p
          rw [hcore, smul_smul]
        · have hji : (j, a) ≠ (i, a) := by
            simp only [ne_eq, Prod.mk.injEq, and_true]; rw [hj, hi]; omega
          rw [if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
          rw [pderiv_comm_mulXN_of_ne hji p, sub_self, smul_zero, smul_zero]
      · have hji : (j, a) ≠ (i, b) := by
          simp only [ne_eq, Prod.mk.injEq]; exact fun h => hab h.2
        rw [if_neg (by rintro ⟨h, _⟩; exact hab h), zero_smul]
        rw [pderiv_comm_mulXN_of_ne hji p, sub_self, smul_zero, smul_zero]
    · subst hn
      rw [oscN_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero,
          if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
    · -- both annihilation: pderivs commute, m+n ≠ 0
      rw [oscN_apply_pos r k a hm, oscN_apply_pos r k b hn,
          oscN_apply_pos r k a hm, oscN_apply_pos r k b hn]
      rw [if_neg (by rintro ⟨_, h⟩; omega), zero_smul]
      rw [Derivation.map_smul, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul]
      rw [pderiv_commN ((m - 1).toNat, a) ((n - 1).toNat, b) p]
      rw [smul_smul, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
      rw [show (m : ℂ) * k * (n : ℂ) * k = (n : ℂ) * k * (m : ℂ) * k from by ring]
      rw [sub_self]

/-! ## The vacuum -/

/-- The **vacuum vector** `1 ∈ FockN r`, killed by all non-negative modes of every family. -/
noncomputable def vacuumN (r : ℕ) : FockN r := (1 : FockN r)

/-- The vacuum is killed by every non-negative mode of every family: `aᵃₙ 1 = 0` for
`n ≥ 0`. -/
theorem oscN_vacuum (r : ℕ) (k : ℂ) (a : Fin r) (n : ℤ) (hn : 0 ≤ n) :
    oscN r k a n (vacuumN r) = 0 := by
  rcases hn.lt_or_eq with hpos | hzero
  · rw [oscN_apply_pos r k a hpos, vacuumN, pderiv_one, smul_zero, smul_zero]
  · rw [← hzero, oscN_zero]; rfl

/-! ## The basic currents and their modes -/

/-- The **basic currents** `αᵃ(z) = Y(aᵃ₋₁1, z) = ∑ₙ aᵃₙ z^{-n-1}`, one per family
`a : Fin r`.  Its `zʲ`-coefficient is `oscN r k a (-j-1)`, so its `m`-th mode is `aᵃₘ`. -/
noncomputable def currentN (r : ℕ) (k : ℂ) (a : Fin r) :
    FormalDist (Module.End ℂ (FockN r)) := fun j => oscN r k a (-j - 1)

/-- The coefficient of z to the power j in the current is oscillator mode -j-1. This is the Laurent-series indexing convention used by vertex operators. -/
@[simp] theorem currentN_apply (r : ℕ) (k : ℂ) (a : Fin r) (j : ℤ) :
    currentN r k a j = oscN r k a (-j - 1) := rfl

/-- The modes of the basic currents are the oscillators: `mode (αᵃ(z)) m = aᵃₘ`. -/
theorem currentN_mode (r : ℕ) (k : ℂ) (a : Fin r) (m : ℤ) :
    mode (currentN r k a) m = oscN r k a m := by
  rw [mode_apply, currentN_apply, show -(-m - 1) - 1 = m from by ring]

/-! ## Self/cross-locality: the `(z₁-z₂)²` OPE bound (Gannon 5.2.5c, rank `r`) -/

/-- The OPE coefficient distribution `cᵃᵇ(z₂) = δ^{ab} k · id`: constant in `z₂`, equal to
`δ^{ab} k · id` at order `0` and `0` elsewhere.  The commutator `[αᵃ(z₁), αᵇ(z₂)]` is
`cᵃᵇ · ∂_{z₂}δ(z₁/z₂)`. -/
noncomputable def opeCoeffN (r : ℕ) (k : ℂ) (a b : Fin r) :
    FormalDist (Module.End ℂ (FockN r)) :=
  fun t => if t = 0 then (if a = b then k else 0) • LinearMap.id else 0

/-- The commutator distribution of two basic currents is a single `δ`-derivative:
`[αᵃ(z₁), αᵇ(z₂)] = cᵃᵇ · ∂_{z₂} δ(z₁/z₂)` with `cᵃᵇ = δ^{ab} k·id` (Gannon 5.2.5c, rank
`r`). For `a ≠ b` the coefficient is `0` and the whole bracket vanishes. -/
theorem bracketDist_currentN_eq_deltaDeriv (r : ℕ) (k : ℂ) (a b : Fin r) :
    bracketDist (currentN r k a) (currentN r k b) = deltaDeriv 1 (opeCoeffN r k a b) := by
  refine FormalDist₂.ext fun m n => ?_
  rw [bracketDist_apply, currentN_apply, currentN_apply]
  rw [oscN_comm r k a b (-m - 1) (-n - 1)]
  rw [deltaDeriv_apply, opeCoeffN]
  simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero, Nat.cast_one]
  by_cases hab : a = b
  · by_cases hmn : m + n + 1 + 1 = 0
    · rw [if_pos ⟨hab, by omega⟩, if_pos hmn, if_pos hab]
      rw [← smul_smul,
          ← Int.cast_smul_eq_zsmul ℂ (-m - 1 : ℤ) (k • LinearMap.id : Module.End ℂ (FockN r))]
    · rw [if_neg (by rintro ⟨_, h⟩; omega), if_neg hmn]
      simp
  · rw [if_neg (by rintro ⟨h, _⟩; exact hab h)]
    by_cases hmn : m + n + 1 + 1 = 0
    · rw [if_pos hmn, if_neg hab]; simp
    · rw [if_neg hmn]; simp

/-- **Self/cross-locality** of the basic currents (Gannon 5.2.5c, rank `r`): two factors of
`(z₁-z₂)` kill the commutator, `(z₁-z₂)²·[αᵃ(z₁),αᵇ(z₂)] = 0`, for **all** families `a,b`.
Distinct families commute exactly (`N = 0`), same-family is the single `δ`-derivative
`k·∂_{z₂}δ` (`N = 2`); `mulBySubPow 2` annihilates both. -/
theorem currentN_self_local (r : ℕ) (k : ℂ) (a b : Fin r) :
    mulBySubPow 2 (bracketDist (currentN r k a) (currentN r k b)) = 0 := by
  rw [bracketDist_currentN_eq_deltaDeriv]
  exact mulBySubPow_deltaDeriv_eq_zero (by norm_num) (opeCoeffN r k a b)

/-- The basic currents are mutually local (`Local` with `N = 2`) for **all** families
`a,b` — the locality hypothesis behind VA4. -/
theorem currentN_local (r : ℕ) (k : ℂ) (a b : Fin r) :
    Local (currentN r k a) (currentN r k b) :=
  ⟨2, currentN_self_local r k a b⟩

/-! ## The L₀-grading by weight (Gannon 5.2.5e, rank `r`) -/

/-- The **weight function**: the variable `(i,a)` (representing `aᵃ₋(i+1)`) has weight
`i + 1`, independent of the family index `a`. -/
def weightFnN {r : ℕ} : ℕ × Fin r → ℕ := fun u => u.1 + 1

/-- An oscillator variable at index i has energy i+1, regardless of its boson colour. Hence every polynomial variable has strictly positive energy. -/
@[simp] theorem weightFnN_apply {r : ℕ} (u : ℕ × Fin r) : weightFnN u = u.1 + 1 := rfl

/-- The **L₀-graded piece** `(FockN r)_w`: the weighted-homogeneous component of total
weight `w`. Indexed by `ℕ`, the grading is automatically **bounded below** by `0`. -/
def gradingWN (r : ℕ) (w : ℕ) : Submodule ℂ (FockN r) :=
  weightedHomogeneousSubmodule ℂ weightFnN w

/-- Belonging to the weight-w Fock subspace means that every nonzero monomial coefficient has weighted degree w. Thus grading arguments can be checked directly on occupations. -/
theorem mem_gradingWN {r : ℕ} {w : ℕ} {p : FockN r} :
    p ∈ gradingWN r w ↔ p.IsWeightedHomogeneous weightFnN w := Iff.rfl

/-- The vacuum sits in the bottom graded piece: `1 ∈ (FockN r)₀`. -/
theorem vacuumN_mem_gradingWN (r : ℕ) : vacuumN r ∈ gradingWN r 0 :=
  isWeightedHomogeneous_one ℂ weightFnN

/-- **Creation raises weight by `m`** (`aᵃ₋ₘ : F_w → F_{w+m}`): the creation oscillator
multiplies by `X ((-n-1).toNat, a)`, of weight `(-n-1)+1 = -n = m`. -/
theorem oscN_neg_weight (r : ℕ) (k : ℂ) (a : Fin r) {n : ℤ} (hn : n < 0) {w : ℕ}
    {p : FockN r} (hp : p ∈ gradingWN r w) :
    oscN r k a n p ∈ gradingWN r (w + (-n).toNat) := by
  rw [oscN_apply_neg r k a hn]
  rw [mem_gradingWN] at hp ⊢
  have hX : (X ((-n - 1).toNat, a) : FockN r).IsWeightedHomogeneous weightFnN ((-n).toNat) := by
    have := isWeightedHomogeneous_X ℂ (weightFnN (r := r)) ((-n - 1).toNat, a)
    rw [weightFnN_apply] at this
    rwa [show (-n - 1).toNat + 1 = (-n).toNat from by omega] at this
  have := hX.mul hp
  rwa [add_comm ((-n).toNat) w] at this

/-- **Annihilation lowers weight by `m`** (`aᵃₘ : F_w → F_{w-m}`): the annihilation
oscillator differentiates by `X ((n-1).toNat, a)`, of weight `(n-1)+1 = n = m`. The target
weight `w'` is given explicitly to avoid truncated subtraction. -/
theorem oscN_pos_weight (r : ℕ) (k : ℂ) (a : Fin r) {n : ℤ} (hn : 0 < n) {w w' : ℕ}
    (hww : w' + n.toNat = w) {p : FockN r} (hp : p ∈ gradingWN r w) :
    oscN r k a n p ∈ gradingWN r w' := by
  rw [oscN_apply_pos r k a hn]
  rw [mem_gradingWN] at hp ⊢
  have hpd : (pderiv ((n - 1).toNat, a) p).IsWeightedHomogeneous weightFnN w' := by
    refine IsWeightedHomogeneous.pderiv hp ?_
    rw [weightFnN_apply, show ((n - 1).toNat, a).1 = (n - 1).toNat from rfl,
        show (n - 1).toNat + 1 = n.toNat from by omega, hww]
  exact (weightedHomogeneousSubmodule ℂ weightFnN w').smul_mem _
    ((weightedHomogeneousSubmodule ℂ weightFnN w').smul_mem _ hpd)

/-- The grading is **bounded below**: every graded weight is `≥ 0`, since the grading is
indexed by `ℕ`. -/
theorem gradingWN_bddBelow (w : ℕ) : (0 : ℕ) ≤ w := Nat.zero_le w

end HeisenbergN

end VOA
