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
# The rank-1 Heisenberg Fock space  (Gannon §5.2.2)

A fully concrete, axiom-clean model of the rank-1 Heisenberg (free-boson) oscillator
algebra acting on a polynomial Fock space, together with the basic current and its
self-locality (the `(z₁-z₂)²` OPE bound). This is the Stage-1 input consumed by the
Stage-2/3 construction of the full vertex operator `Y` and the VOA axioms.

## The model

The Fock space is `F := MvPolynomial ℕ ℂ`: the variable `i : ℕ` stands for the negative
mode `a₋(i+1)`, and the monomial `∏ Xᵢ^{eᵢ}` is the state `a₋(i+1)^{eᵢ} ⋯ 1`.

* **Oscillators** `osc k n : F →ₗ[ℂ] F` (level `k : ℂ`):
  - `n < 0` (creation `a₋ₘ`, `m = -n ≥ 1`): multiplication by `X (-n-1).toNat`;
  - `n > 0` (annihilation `aₙ`): `(n : ℂ) • k • pderiv (n-1).toNat`;
  - `n = 0`: `0`.
* **Commutation** (Gannon 3.2.12a): `[aₘ, aₙ] = m δ_{m+n,0} k`.
* **Vacuum** `1 : F`, with `aₙ 1 = 0` for `n ≥ 0`.
* **L₀-grading**: the weight `w = ∑ (i+1)·eᵢ`; `a₋ₘ : F_w → F_{w+m}`, `aₘ : F_w → F_{w-m}`.
* **Basic current** `current k j = osc k (-j-1)`, so `Y(a₋₁1,z) = ∑ₙ aₙ z^{-n-1}` and
  `mode (current k) m = osc k m`.
* **Self-locality** (Gannon 5.2.5c): `(z₁-z₂)²·[α(z₁),α(z₂)] = 0`, i.e.
  `mulBySubPow 2 (bracketDist (current k) (current k)) = 0` — the commutator is `k·∂δ`,
  a single δ-derivative, killed by two factors of `(z₁-z₂)`.

## Dependencies
* `VOA.Core.VertexOperatorAlgebra`, `VOA.Foundations.FormalCalculus`,
  `VOA.Foundations.Locality`, `Mathlib.Algebra.MvPolynomial.PDeriv`.

## Status
Concrete model, fully axiom-clean
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.2.2, eqs. (5.2.5); FLM Ch. 2; Kac §3.5; Lepowsky–Li Ch. 6.
-/

namespace VOA

open scoped BigOperators
open MvPolynomial

universe u

/-! ## The Fock space and the oscillators -/

/-- The rank-1 Heisenberg **Fock space** `F = MvPolynomial ℕ ℂ`. The variable `i : ℕ`
represents the negative mode `a₋(i+1)`; the monomial `∏ Xᵢ^{eᵢ}` is the state
`a₋(i+1)^{eᵢ} ⋯ 1` (Gannon §5.2.2, eq. 5.2.5a). -/
abbrev Fock : Type := MvPolynomial ℕ ℂ

/-- The **multiplication** endomorphism `p ↦ Xᵢ · p` of the Fock space, as a `ℂ`-linear
map. This is the creation operator (up to reindexing). -/
noncomputable def mulX (i : ℕ) : Fock →ₗ[ℂ] Fock :=
  (LinearMap.mul ℂ Fock (X i)).comp (LinearMap.id)

@[simp] theorem mulX_apply (i : ℕ) (p : Fock) : mulX i p = X i * p := rfl

/-- The partial-derivative endomorphism `pderiv i` of the Fock space, as a `ℂ`-linear map.
This is (the unscaled part of) the annihilation operator. -/
noncomputable def pderivLM (i : ℕ) : Fock →ₗ[ℂ] Fock :=
  (pderiv i : Derivation ℂ Fock Fock).toLinearMap

@[simp] theorem pderivLM_apply (i : ℕ) (p : Fock) : pderivLM i p = pderiv i p := rfl

/-- The rank-1 Heisenberg **oscillators** `aₙ = osc k n` on the Fock space, level `k`
(Gannon §5.2.2):

* `n < 0` (creation `a₋ₘ`, `m = -n`): multiplication by `X (-n-1).toNat`;
* `n > 0` (annihilation `aₙ`): `(n : ℂ) • k • pderiv (n-1).toNat`;
* `n = 0`: `0`.

Each branch is a genuine `ℂ`-linear endomorphism (multiplication and `pderiv` are
linear). -/
noncomputable def osc (k : ℂ) (n : ℤ) : Fock →ₗ[ℂ] Fock :=
  if n < 0 then mulX (-n - 1).toNat
  else if 0 < n then (n : ℂ) • k • pderivLM (n - 1).toNat
  else 0

@[simp] theorem osc_neg (k : ℂ) {n : ℤ} (hn : n < 0) :
    osc k n = mulX (-n - 1).toNat := by
  rw [osc, if_pos hn]

@[simp] theorem osc_pos (k : ℂ) {n : ℤ} (hn : 0 < n) :
    osc k n = (n : ℂ) • k • pderivLM (n - 1).toNat := by
  rw [osc, if_neg (by omega), if_pos hn]

@[simp] theorem osc_zero (k : ℂ) : osc k 0 = 0 := by
  rw [osc, if_neg (by omega), if_neg (by omega)]

/-- Creation-mode application: `a₋ₘ p = X_{m-1} · p` (here `n = -m < 0`). -/
theorem osc_apply_neg (k : ℂ) {n : ℤ} (hn : n < 0) (p : Fock) :
    osc k n p = X (-n - 1).toNat * p := by
  rw [osc_neg k hn, mulX_apply]

/-- Annihilation-mode application: `aₙ p = (n·k) · ∂_{X_{n-1}} p` (here `n > 0`). -/
theorem osc_apply_pos (k : ℂ) {n : ℤ} (hn : 0 < n) (p : Fock) :
    osc k n p = (n : ℂ) • k • pderiv (n - 1).toNat p := by
  rw [osc_pos k hn]; rfl

/-! ## The fundamental per-variable commutator `[Xᵢ•, ∂ⱼ]` -/

/-- The Leibniz/canonical commutator on the Fock space: `[Xᵢ•, ∂ᵢ] = -id`, equivalently
`∂ᵢ(Xᵢ·p) - Xᵢ·∂ᵢp = p`. This is the algebraic core of `[aₘ,aₙ] = m δ k`. -/
theorem pderiv_comm_mulX_self (i : ℕ) (p : Fock) :
    pderiv i (X i * p) - X i * pderiv i p = p := by
  rw [pderiv_mul, pderiv_X_self, one_mul]
  ring

/-- Different variables: `∂ⱼ` and `Xᵢ•` commute when `i ≠ j`, i.e.
`∂ⱼ(Xᵢ·p) = Xᵢ·∂ⱼp`. -/
theorem pderiv_comm_mulX_of_ne {i j : ℕ} (h : j ≠ i) (p : Fock) :
    pderiv j (X i * p) = X i * pderiv j p := by
  rw [pderiv_mul, pderiv_X_of_ne (Ne.symm h), zero_mul, zero_add]

/-- Partial derivatives commute: `∂ᵢ∂ⱼ p = ∂ⱼ∂ᵢ p` on the Fock space. (Mixed partials
agree — Schwarz's theorem for formal polynomial derivatives.) -/
theorem pderiv_comm (i j : ℕ) (p : Fock) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s h =>
    rw [pderiv_mul, pderiv_mul, map_add, map_add, pderiv_mul, pderiv_mul]
    simp only [pderiv_X, Pi.single_apply, h]
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
      simp_all <;> ring

/-! ## The commutation relation `[aₘ, aₙ] = m δ_{m+n,0} k`  (Gannon 3.2.12a) -/

/-- **The Heisenberg commutation relation** (Gannon 3.2.12a):
`[aₘ, aₙ] = m δ_{m+n,0} k · id`. The technical heart of this file.

Cases. Both creation (`m,n<0`) or both annihilation (`m,n>0`): the operators commute and
`m+n ≠ 0`. A vanishing mode (`m=0` or `n=0`): the operator is `0`. Creation × annihilation
(`m<0<n` or `n<0<m`): the per-variable canonical commutator `[Xᵢ•,∂ⱼ]` is `-δ_{ij}·id`,
and `m+n=0 ↔ i=j`, giving the signed coefficient `m·k`. -/
theorem osc_comm (k : ℂ) (m n : ℤ) :
    osc k m * osc k n - osc k n * osc k m
      = (if m + n = 0 then (m : ℂ) * k else 0) • LinearMap.id := by
  -- Work pointwise.
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
  show osc k m (osc k n p) - osc k n (osc k m p)
      = (if m + n = 0 then (m : ℂ) * k else 0) • p
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · -- both creation: mults by X commute, and m+n ≠ 0
      rw [osc_apply_neg k hm, osc_apply_neg k hn, osc_apply_neg k hm, osc_apply_neg k hn]
      rw [if_neg (by omega), zero_smul]
      rw [mul_left_comm (X (-m - 1).toNat), sub_self]
    · -- n = 0
      subst hn
      rw [osc_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero,
          if_neg (by omega), zero_smul]
    · -- m < 0 < n : creation × annihilation (the key case)
      rw [osc_apply_neg k hm, osc_apply_pos k hn, osc_apply_pos k hn, osc_apply_neg k hm]
      -- name the two variable indices
      set i := (-m - 1).toNat with hi
      set j := (n - 1).toNat with hj
      -- factor the `n•k•` out of both `X_i * (…)` and the second term
      rw [mul_smul_comm, mul_smul_comm, ← smul_sub, ← smul_sub]
      by_cases hmn : m + n = 0
      · -- same variable: j = i, coefficient m·k
        have hji : j = i := by rw [hj, hi]; omega
        rw [if_pos hmn, hji]
        -- (n·k)·(Xᵢ·∂ᵢp - ∂ᵢ(Xᵢ·p)) = (n·k)·(-p)
        have hcore : X i * pderiv i p - pderiv i (X i * p) = -p := by
          have := pderiv_comm_mulX_self i p; linear_combination -this
        rw [hcore]
        -- reconcile scalars: (n)k•(-p) = (m·k)•p, with n = -m
        have hnm : (n : ℂ) = -(m : ℂ) := by
          have : n = -m := by omega
          rw [this]; push_cast; ring
        rw [smul_neg, smul_neg, smul_smul, ← neg_smul]
        congr 1
        rw [hnm]; ring
      · -- different variable: j ≠ i, operators commute, RHS = 0
        have hji : j ≠ i := by rw [hj, hi]; omega
        rw [if_neg hmn, zero_smul]
        rw [pderiv_comm_mulX_of_ne hji p, sub_self, smul_zero, smul_zero]
  · -- m = 0
    subst hm
    rw [osc_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero]
    simp
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · -- n < 0 < m : annihilation × creation (key case, mirror)
      rw [osc_apply_pos k hm, osc_apply_neg k hn, osc_apply_neg k hn, osc_apply_pos k hm]
      set i := (-n - 1).toNat with hi
      set j := (m - 1).toNat with hj
      rw [mul_smul_comm, mul_smul_comm, ← smul_sub, ← smul_sub]
      by_cases hmn : m + n = 0
      · have hji : j = i := by rw [hj, hi]; omega
        rw [if_pos hmn, hji]
        -- (m·k)·(∂ᵢ(Xᵢ·p) - Xᵢ·∂ᵢp) = (m·k)·p
        have hcore : pderiv i (X i * p) - X i * pderiv i p = p :=
          pderiv_comm_mulX_self i p
        rw [hcore, smul_smul]
      · have hji : j ≠ i := by rw [hj, hi]; omega
        rw [if_neg hmn, zero_smul]
        rw [pderiv_comm_mulX_of_ne hji p, sub_self, smul_zero, smul_zero]
    · subst hn
      rw [osc_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero,
          if_neg (by omega), zero_smul]
    · -- both annihilation: pderivs commute, m+n ≠ 0
      rw [osc_apply_pos k hm, osc_apply_pos k hn, osc_apply_pos k hm, osc_apply_pos k hn]
      rw [if_neg (by omega), zero_smul]
      -- pull the inner `↑n•k•` / `↑m•k•` out through the outer `pderiv`
      rw [Derivation.map_smul, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul]
      rw [pderiv_comm (m - 1).toNat (n - 1).toNat p]
      -- both summands now collapse to a single scalar, equal by commutativity
      rw [smul_smul, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
      rw [show (m : ℂ) * k * (n : ℂ) * k = (n : ℂ) * k * (m : ℂ) * k from by ring]
      rw [sub_self]

/-! ## The vacuum -/

/-- The **vacuum vector** `1 ∈ F` (the constant polynomial), the highest-weight state
killed by all non-negative modes. -/
noncomputable def vacuum : Fock := (1 : Fock)

/-- The vacuum is killed by every non-negative mode: `aₙ 1 = 0` for `n ≥ 0`
(`n = 0`: `osc 0 = 0`; `n > 0`: `∂` of a constant is `0`). -/
theorem osc_vacuum (k : ℂ) (n : ℤ) (hn : 0 ≤ n) : osc k n vacuum = 0 := by
  rcases hn.lt_or_eq with hpos | hzero
  · rw [osc_apply_pos k hpos, vacuum, pderiv_one, smul_zero, smul_zero]
  · rw [← hzero, osc_zero]; rfl

/-! ## The basic current and its modes -/

/-- The **basic current** `α(z) = Y(a₋₁1, z) = ∑ₙ aₙ z^{-n-1}` as a formal distribution
of `End ℂ Fock` (Gannon 5.2.5b). Its `zʲ`-coefficient is the mode `osc k (-j-1)`, so that
its `m`-th mode (in the `Y(·,z) = ∑ u₍ₘ₎ z^{-m-1}` indexing) is exactly `osc k m`. -/
noncomputable def current (k : ℂ) : FormalDist (Module.End ℂ Fock) := fun j => osc k (-j - 1)

@[simp] theorem current_apply (k : ℂ) (j : ℤ) : current k j = osc k (-j - 1) := rfl

/-- The modes of the basic current are the oscillators: `mode (α(z)) m = aₘ` (Gannon 5.2.5b,
the `Y(u,z) = ∑ u₍ₘ₎ z^{-m-1}` mode indexing of `FormalCalculus`). -/
theorem current_mode (k : ℂ) (m : ℤ) : mode (current k) m = osc k m := by
  rw [mode_apply, current_apply, show -(-m - 1) - 1 = m from by ring]

/-! ## Self-locality: the `(z₁-z₂)²` OPE bound (Gannon 5.2.5c) -/

/-- The OPE coefficient distribution `c(z₂) = k · id`: the constant distribution whose
`z₂⁰`-coefficient is `k · id` and which vanishes elsewhere. The commutator
`[α(z₁), α(z₂)]` is `c · ∂_{z₂}δ(z₁/z₂)`. -/
noncomputable def opeCoeff (k : ℂ) : FormalDist (Module.End ℂ Fock) :=
  fun t => if t = 0 then k • LinearMap.id else 0

/-- The commutator distribution of the basic current with itself is a single
`δ`-derivative: `[α(z₁), α(z₂)] = c · ∂_{z₂} δ(z₁/z₂)` with `c = k·id` (Gannon 5.2.5c).
This is the algebraic content of the OPE `α(z₁)α(z₂) ∼ k/(z₁-z₂)²`. -/
theorem bracketDist_current_eq_deltaDeriv (k : ℂ) :
    bracketDist (current k) (current k) = deltaDeriv 1 (opeCoeff k) := by
  refine FormalDist₂.ext fun m n => ?_
  rw [bracketDist_apply, current_apply, current_apply]
  -- the bracket of two oscillators
  rw [osc_comm k (-m - 1) (-n - 1)]
  rw [deltaDeriv_apply, opeCoeff]
  simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero, Nat.cast_one]
  -- the index condition `(-m-1)+(-n-1)=0` ↔ `m+n+1+1 = 0`
  by_cases hmn : m + n + 1 + 1 = 0
  · rw [if_pos (by omega), if_pos hmn]
    -- `((-m-1:ℤ):ℂ)*k • id = (-m-1:ℤ) • (k • id)`
    rw [← smul_smul, ← Int.cast_smul_eq_zsmul ℂ (-m - 1 : ℤ) (k • LinearMap.id : Module.End ℂ Fock)]
  · rw [if_neg (by omega), if_neg hmn]
    simp

/-- **Self-locality** of the basic current (Gannon 5.2.5c): two factors of `(z₁-z₂)` kill
the commutator, `(z₁-z₂)²·[α(z₁),α(z₂)] = 0`. The locality bound is `N = 2`: the commutator
is a single `δ`-derivative `k·∂_{z₂}δ(z₁/z₂)`, and `mulBySubPow 2` annihilates any single
`δ`-derivative (`mulBySubPow_deltaDeriv_eq_zero`). This is the Stage-1 input to VA4. -/
theorem current_self_local (k : ℂ) :
    mulBySubPow 2 (bracketDist (current k) (current k)) = 0 := by
  rw [bracketDist_current_eq_deltaDeriv]
  exact mulBySubPow_deltaDeriv_eq_zero (by norm_num) (opeCoeff k)

/-- The basic current is mutually local with itself (`Local` with `N = 2`), the locality
hypothesis behind the vertex-algebra axiom VA4. -/
theorem current_local (k : ℂ) : Local (current k) (current k) :=
  ⟨2, current_self_local k⟩

/-! ## The L₀-grading by weight (Gannon 5.2.5e) -/

/-- The **weight function**: the variable `i` (representing `a₋(i+1)`) has weight `i + 1`.
The L₀-weight of a state `∏ Xᵢ^{eᵢ}` is `∑ (i+1)·eᵢ`. -/
def weightFn : ℕ → ℕ := fun i => i + 1

@[simp] theorem weightFn_apply (i : ℕ) : weightFn i = i + 1 := rfl

/-- The **L₀-graded piece** `F_w`: the weighted-homogeneous component of total weight `w`,
spanned by the monomials `∏ Xᵢ^{eᵢ}` with `∑ (i+1)·eᵢ = w` (Gannon 5.2.5e). Indexed by
`ℕ`, the grading is automatically **bounded below** by `0`. -/
def gradingW (w : ℕ) : Submodule ℂ Fock :=
  weightedHomogeneousSubmodule ℂ weightFn w

theorem mem_gradingW {w : ℕ} {p : Fock} :
    p ∈ gradingW w ↔ p.IsWeightedHomogeneous weightFn w := Iff.rfl

/-- The vacuum sits in the bottom graded piece: `1 ∈ F₀`. -/
theorem vacuum_mem_gradingW : vacuum ∈ gradingW 0 :=
  isWeightedHomogeneous_one ℂ weightFn

/-- **Creation raises weight by `m`** (`a₋ₘ : F_w → F_{w+m}`, `m = -n ≥ 1`): the creation
oscillator multiplies by `X (-n-1)`, of weight `(-n-1)+1 = -n = m`, so it sends a
weight-`w` state to a weight-`(w + (-n).toNat)` state (Gannon 5.2.5e). -/
theorem osc_neg_weight (k : ℂ) {n : ℤ} (hn : n < 0) {w : ℕ} {p : Fock}
    (hp : p ∈ gradingW w) : osc k n p ∈ gradingW (w + (-n).toNat) := by
  rw [osc_apply_neg k hn]
  rw [mem_gradingW] at hp ⊢
  -- `X (-n-1).toNat` is weighted-homogeneous of weight `weightFn (-n-1).toNat = (-n-1)+1`
  have hX : (X (-n - 1).toNat : Fock).IsWeightedHomogeneous weightFn ((-n).toNat) := by
    have := isWeightedHomogeneous_X ℂ weightFn (-n - 1).toNat
    rw [weightFn_apply] at this
    rwa [show (-n - 1).toNat + 1 = (-n).toNat from by omega] at this
  have := hX.mul hp
  rwa [add_comm ((-n).toNat) w] at this

/-- **Annihilation lowers weight by `m`** (`aₘ : F_w → F_{w-m}`, `m = n ≥ 1`): the
annihilation oscillator differentiates by `X (n-1)`, of weight `(n-1)+1 = n = m`, so it
sends a weight-`w` state to a weight-`w'` state with `w' + n = w` (Gannon 5.2.5e). The
target weight `w'` is given explicitly to avoid truncated subtraction. -/
theorem osc_pos_weight (k : ℂ) {n : ℤ} (hn : 0 < n) {w w' : ℕ} (hww : w' + n.toNat = w)
    {p : Fock} (hp : p ∈ gradingW w) : osc k n p ∈ gradingW w' := by
  rw [osc_apply_pos k hn]
  rw [mem_gradingW] at hp ⊢
  -- the scaled `pderiv` lowers weight by `weightFn (n-1).toNat = (n-1)+1 = n`
  have hpd : (pderiv (n - 1).toNat p).IsWeightedHomogeneous weightFn w' := by
    refine IsWeightedHomogeneous.pderiv hp ?_
    rw [weightFn_apply, show (n - 1).toNat + 1 = n.toNat from by omega, hww]
  -- scaling by `(n:ℂ)` and `k` preserves weighted-homogeneity
  exact (weightedHomogeneousSubmodule ℂ weightFn w').smul_mem _
    ((weightedHomogeneousSubmodule ℂ weightFn w').smul_mem _ hpd)

/-- The grading is **bounded below**: every graded weight is `≥ 0`, since the grading is
indexed by `ℕ` (there is no graded piece in negative weight). This is the half of VOA4
(`𝒱ₙ = 0` for `n < 0`) that the Fock model realizes by construction. -/
theorem gradingW_bddBelow (w : ℕ) : (0 : ℕ) ≤ w := Nat.zero_le w

end VOA
