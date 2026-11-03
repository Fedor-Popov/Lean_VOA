/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.BetaGamma
import VOA.Core.SuperReconstruction
import Mathlib.RingTheory.Derivation.Lie

/-!
# `βγ` symplectic bosons: lower truncation and the translation operator

The foundation layer that `Examples.BetaGamma` is missing: the two generating distributions as
genuine **fields** (`IsField`), a **translation operator** `T` with both generators
`T`-covariant, and the vacuum-creation values.  These are exactly the hypotheses
`hfield`, `hTcov`, `hTvac`, `hcre0`, `hcreneg` of `Core.SuperReconstruction.reconstructε`.

## ⚠ The indexing of `Examples.BetaGamma` is reversed

Throughout this library a `FormalDist` is indexed by the **`z`-exponent**: `a(z) = ∑ⱼ aⱼ zʲ`,
so the VA mode `a₍ₙ₎` sits at `j = -n-1`, and `IsField a` (`Core.Dong`) is lower truncation,
`aⱼ x = 0` for `j ≪ 0`.  Creation modes must therefore live at `j ≥ 0` and annihilation modes
at `j ≤ -1`.  `Examples.SymplecticFermion.chi` follows this convention explicitly.

`Examples.BetaGamma.beta` / `.gamma` are indexed the other way round — annihilation (`der`, a
`pderiv`) at `j ≥ 0` and creation (`mulX`, multiplication by a variable) at `j < 0`.  So

  `BetaGamma.beta j = mulX (Sum.inl (-j-1).toNat)` for every `j < 0`,

which is injective and never kills a nonzero polynomial.  Hence **`IsField BetaGamma.beta` is
false** (likewise for `gamma`): the distribution is *upper* truncated, not lower truncated.
`Examples.FreeFermion.psi` has the identical defect.  Since `IsField` is the very first
hypothesis of every reconstruction route, this explains why nothing downstream of
`BetaGamma.lean` was ever built.

Nothing else in `BetaGamma.lean` is affected: locality is proved through `localε_of_car`, whose
hypothesis `[aₘ, bₙ] = δ_{m+n+1,0}·S` is invariant under applying `j ↦ -j-1` to *both* slots
(the condition `m+n+1 = 0` is symmetric under that involution), so `beta_local`, `gamma_local`,
`beta_gamma_local` remain true statements.

This file therefore leaves `BetaGamma.lean` untouched and works with the reindexed fields

  `betaZ j = BetaGamma.beta (-j-1)`,   `gammaZ j = BetaGamma.gamma (-j-1)`

spelled out directly (`betaZ_eq`, `gammaZ_eq` record the identification), which *are* fields.

## The translation operator

For the polynomial Fock space `Fock = ℂ[xᵢ]` the translation operator is simply the derivation

  `T (X i) = (lvl i + 1) · X (up i)`,

built with `MvPolynomial.mkDerivation` — no dual-number detour is needed (contrast
`Examples.SymplecticFermionT`, where the Clifford algebra forces one).  Here `lvl` is the level
of a variable and `up` raises it by one.  On modes this is `β₍₋ₖ₋₁₎ ↦ (k+1)·β₍₋ₖ₋₂₎`, and the
commutator with an annihilation mode comes out as `[T, ∂ᵢ] = -lvl(i)·∂_{down i}`, which is the
`j ≤ -1` half of `[T, aⱼ] = (j+1)·a_{j+1}`.

## Weights (not formalized here)

With `T = L₋₁` as above, `β` and `γ` both carry conformal weight `1/2` in the standard
symplectic-boson normalization (`λ = 1/2`, `1 - λ = 1/2`), the first genuinely half-integer
weight in the library.  The grading and the conformal vector are the next layer and are *not*
claimed in this file.
-/

namespace VOA.BG

open MvPolynomial
open VOA.BetaGamma

/-! ## §0  Variable bookkeeping

A variable index is `Sum.inl k` or `Sum.inr k`; `lvl` reads off `k`, `up` raises it and `down`
lowers it (truncated at `0`, which is harmless because every use of `down` is multiplied by
`lvl`). -/

/-- The level of a variable index. -/
def lvl : ℕ ⊕ ℕ → ℕ := Sum.elim id id

/-- Raise a variable index by one level. -/
def up : ℕ ⊕ ℕ → ℕ ⊕ ℕ := Sum.map (· + 1) (· + 1)

/-- Lower a variable index by one level (truncated at level `0`). -/
def down : ℕ ⊕ ℕ → ℕ ⊕ ℕ := Sum.map (· - 1) (· - 1)

@[simp] theorem lvl_inl (k : ℕ) : lvl (Sum.inl k) = k := rfl
@[simp] theorem lvl_inr (k : ℕ) : lvl (Sum.inr k) = k := rfl
@[simp] theorem up_inl (k : ℕ) : up (Sum.inl k) = Sum.inl (k + 1) := rfl
@[simp] theorem up_inr (k : ℕ) : up (Sum.inr k) = Sum.inr (k + 1) := rfl
@[simp] theorem down_inl (k : ℕ) : down (Sum.inl k) = Sum.inl (k - 1) := rfl
@[simp] theorem down_inr (k : ℕ) : down (Sum.inr k) = Sum.inr (k - 1) := rfl

@[simp] theorem lvl_up (i : ℕ ⊕ ℕ) : lvl (up i) = lvl i + 1 := by cases i <;> rfl

@[simp] theorem down_up (i : ℕ ⊕ ℕ) : down (up i) = i := by cases i <;> simp

theorem up_down {i : ℕ ⊕ ℕ} (h : lvl i ≠ 0) : up (down i) = i := by
  rcases i with k | k
  · rw [lvl_inl] at h
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    simp
  · rw [lvl_inr] at h
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    simp

/-! ## §1  The correctly oriented fields

`betaZ j = β₍₋ⱼ₋₁₎`, `gammaZ j = γ₍₋ⱼ₋₁₎`: creation (multiplication by a variable) at `j ≥ 0`,
annihilation (a partial derivative) at `j ≤ -1`. -/

/-- **`β(z)` in `z`-exponent indexing.**  `βⱼ = β₍₋ⱼ₋₁₎`: multiplication by an `inl` variable
for `j ≥ 0`, differentiation in an `inr` variable for `j ≤ -1`. -/
noncomputable def betaZ : FormalDist (Module.End ℂ Fock) :=
  fun j => if 0 ≤ j then mulX (Sum.inl j.toNat) else der (Sum.inr (-j - 1).toNat)

/-- **`γ(z)` in `z`-exponent indexing.**  `γⱼ = γ₍₋ⱼ₋₁₎`; the sign on the annihilation branch is
inherited from `BetaGamma.gamma` and is what makes the pairing come out as `+δ`. -/
noncomputable def gammaZ : FormalDist (Module.End ℂ Fock) :=
  fun j => if 0 ≤ j then mulX (Sum.inr j.toNat) else -der (Sum.inl (-j - 1).toNat)

theorem betaZ_of_nonneg {j : ℤ} (hj : 0 ≤ j) : betaZ j = mulX (Sum.inl j.toNat) := by
  show (if 0 ≤ j then mulX (Sum.inl j.toNat) else der (Sum.inr (-j - 1).toNat)) = _
  rw [if_pos hj]

theorem betaZ_of_neg {j : ℤ} (hj : ¬ 0 ≤ j) : betaZ j = der (Sum.inr (-j - 1).toNat) := by
  show (if 0 ≤ j then mulX (Sum.inl j.toNat) else der (Sum.inr (-j - 1).toNat)) = _
  rw [if_neg hj]

theorem gammaZ_of_nonneg {j : ℤ} (hj : 0 ≤ j) : gammaZ j = mulX (Sum.inr j.toNat) := by
  show (if 0 ≤ j then mulX (Sum.inr j.toNat) else -der (Sum.inl (-j - 1).toNat)) = _
  rw [if_pos hj]

theorem gammaZ_of_neg {j : ℤ} (hj : ¬ 0 ≤ j) : gammaZ j = -der (Sum.inl (-j - 1).toNat) := by
  show (if 0 ≤ j then mulX (Sum.inr j.toNat) else -der (Sum.inl (-j - 1).toNat)) = _
  rw [if_neg hj]

/-- The reindexing that fixes the orientation: `betaZ j = BetaGamma.beta (-j-1)`. -/
theorem betaZ_eq (j : ℤ) : betaZ j = BetaGamma.beta (-j - 1) := by
  show (if 0 ≤ j then mulX (Sum.inl j.toNat) else der (Sum.inr (-j - 1).toNat))
      = if 0 ≤ -j - 1 then der (Sum.inr (-j - 1).toNat)
        else mulX (Sum.inl (-(-j - 1) - 1).toNat)
  by_cases h : 0 ≤ j
  · rw [if_pos h, if_neg (by omega), show (-(-j - 1) - 1).toNat = j.toNat by omega]
  · rw [if_neg h, if_pos (by omega)]

/-- The reindexing that fixes the orientation: `gammaZ j = BetaGamma.gamma (-j-1)`. -/
theorem gammaZ_eq (j : ℤ) : gammaZ j = BetaGamma.gamma (-j - 1) := by
  show (if 0 ≤ j then mulX (Sum.inr j.toNat) else -der (Sum.inl (-j - 1).toNat))
      = if 0 ≤ -j - 1 then -der (Sum.inl (-j - 1).toNat)
        else mulX (Sum.inr (-(-j - 1) - 1).toNat)
  by_cases h : 0 ≤ j
  · rw [if_pos h, if_neg (by omega), show (-(-j - 1) - 1).toNat = j.toNat by omega]
  · rw [if_neg h, if_pos (by omega)]

/-! ## §2  The commutation relations and locality survive the reindexing

The delta condition `m + n + 1 = 0` is invariant under `(m,n) ↦ (-m-1, -n-1)`, so every
`localε_of_car` input transfers verbatim. -/

theorem betaZ_comm (j k : ℤ) : betaZ j * betaZ k - betaZ k * betaZ j = 0 := by
  rw [betaZ_eq, betaZ_eq]; exact BetaGamma.beta_comm _ _

theorem gammaZ_comm (j k : ℤ) : gammaZ j * gammaZ k - gammaZ k * gammaZ j = 0 := by
  rw [gammaZ_eq, gammaZ_eq]; exact BetaGamma.gamma_comm _ _

/-- **The `βγ` canonical commutation relation** in `z`-exponent indexing:
`[βⱼ, γₖ] = δ_{j+k+1,0}`. -/
theorem betaZ_gammaZ_comm (j k : ℤ) :
    betaZ j * gammaZ k - gammaZ k * betaZ j = if j + k + 1 = 0 then 1 else 0 := by
  rw [betaZ_eq, gammaZ_eq, BetaGamma.beta_gamma_comm]
  by_cases h : j + k + 1 = 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem betaZ_local : Local betaZ betaZ := by
  rw [← localε_one_iff]
  exact localε_of_car 0 (by intro m n; rw [one_smul]; simpa using betaZ_comm m n)

theorem gammaZ_local : Local gammaZ gammaZ := by
  rw [← localε_one_iff]
  exact localε_of_car 0 (by intro m n; rw [one_smul]; simpa using gammaZ_comm m n)

/-- Mutual locality at `ε = 1`: `βγ` are **commuting** fields, however they are moded. -/
theorem betaZ_gammaZ_local : Local betaZ gammaZ := by
  rw [← localε_one_iff]
  exact localε_of_car 1 (by intro m n; rw [one_smul]; exact betaZ_gammaZ_comm m n)

/-- Both generators are even, so the Koszul sign is `1`. -/
theorem betaZ_gammaZ_localε_koszul : Localε (koszul 0 0) betaZ gammaZ := by
  rw [koszul_zero_left, localε_one_iff]
  exact betaZ_gammaZ_local

/-! ## §3  Lower truncation: `IsField`

A polynomial involves only finitely many variables, so all sufficiently high partial
derivatives kill it.  That is the entire content of `IsField` here. -/

/-- **Only finitely many variables occur in a polynomial.**  For a fixed `f`, all partial
derivatives at level `≥ N` annihilate `f`. -/
theorem exists_pderiv_eq_zero (f : Fock) :
    ∃ N : ℕ, ∀ i : ℕ ⊕ ℕ, N ≤ lvl i → pderiv i f = 0 := by
  classical
  refine ⟨(f.vars.image lvl).sup id + 1, fun i hi => ?_⟩
  refine pderiv_eq_zero_of_notMem_vars (fun hmem => ?_)
  have h1 : lvl i ∈ f.vars.image lvl := Finset.mem_image_of_mem lvl hmem
  have h2 : lvl i ≤ (f.vars.image lvl).sup id := Finset.le_sup (f := id) h1
  omega

/-- **`βZ` is a field**: lower truncated on every vector.  This is exactly the statement
that fails for `BetaGamma.beta` with its reversed indexing. -/
theorem betaZ_isField : IsField betaZ := by
  intro x
  obtain ⟨N, hN⟩ := exists_pderiv_eq_zero x
  refine ⟨-(N : ℤ), fun j hj => ?_⟩
  rw [betaZ_of_neg (by omega), der_apply,
    hN (Sum.inr (-j - 1).toNat) (by rw [lvl_inr]; omega)]

/-- **`γZ` is a field.** -/
theorem gammaZ_isField : IsField gammaZ := by
  intro x
  obtain ⟨N, hN⟩ := exists_pderiv_eq_zero x
  refine ⟨-(N : ℤ), fun j hj => ?_⟩
  rw [gammaZ_of_neg (by omega), LinearMap.neg_apply, der_apply,
    hN (Sum.inl (-j - 1).toNat) (by rw [lvl_inl]; omega), neg_zero]

/-! ### The orientation defect, as a theorem

The reindexing above is not a matter of taste: with the indexing actually used in
`Examples.BetaGamma` the two distributions are **provably not** fields, because every
sufficiently negative mode is multiplication by a variable, which is injective. -/

/-- ⚠ **`BetaGamma.beta` is not a field.**  Its `j ≪ 0` modes are multiplications by
variables, so no lower truncation bound exists — already on the vacuum `1`. -/
theorem beta_not_isField : ¬ IsField BetaGamma.beta := by
  intro h
  obtain ⟨B, hB⟩ := h (1 : Fock)
  have h0 : ¬ (0 ≤ min B 0 - 1) := by omega
  have hval := hB (min B 0 - 1) (by omega)
  rw [show BetaGamma.beta (min B 0 - 1) = mulX (Sum.inl (-(min B 0 - 1) - 1).toNat) by
        show (if 0 ≤ min B 0 - 1 then der (Sum.inr (min B 0 - 1).toNat)
            else mulX (Sum.inl (-(min B 0 - 1) - 1).toNat)) = _
        rw [if_neg h0],
    mulX_apply, mul_one] at hval
  exact X_ne_zero _ hval

/-- ⚠ **`BetaGamma.gamma` is not a field**, for the same reason. -/
theorem gamma_not_isField : ¬ IsField BetaGamma.gamma := by
  intro h
  obtain ⟨B, hB⟩ := h (1 : Fock)
  have h0 : ¬ (0 ≤ min B 0 - 1) := by omega
  have hval := hB (min B 0 - 1) (by omega)
  rw [show BetaGamma.gamma (min B 0 - 1) = mulX (Sum.inr (-(min B 0 - 1) - 1).toNat) by
        show (if 0 ≤ min B 0 - 1 then -der (Sum.inl (min B 0 - 1).toNat)
            else mulX (Sum.inr (-(min B 0 - 1) - 1).toNat)) = _
        rw [if_neg h0],
    mulX_apply, mul_one] at hval
  exact X_ne_zero _ hval

/-! ## §4  The translation operator `T`

`T` is the derivation of the polynomial algebra sending `X i ↦ (lvl i + 1) · X (up i)`.
`MvPolynomial.mkDerivation` builds it from its values on the variables. -/

/-- The values of `T` on the variables: `X i ↦ (lvl i + 1) · X (up i)`. -/
noncomputable def tGen (i : ℕ ⊕ ℕ) : Fock := ((lvl i : ℂ) + 1) • X (up i)

/-- The translation operator as a bundled derivation. -/
noncomputable def Tder : Derivation ℂ Fock Fock := mkDerivation ℂ tGen

/-- **The translation operator** `T = L₋₁` on the `βγ` Fock space. -/
noncomputable def T : Module.End ℂ Fock := Tder.toLinearMap

theorem T_apply (f : Fock) : T f = Tder f := rfl

/-- `T` on a variable. -/
@[simp] theorem T_X (i : ℕ ⊕ ℕ) : T (X i) = ((lvl i : ℂ) + 1) • X (up i) := by
  show mkDerivation ℂ tGen (X i) = _
  rw [mkDerivation_X]
  rfl

/-- **`T` is a derivation.** -/
theorem T_mul (f g : Fock) : T (f * g) = f * T g + T f * g := by
  show Tder (f * g) = f * Tder g + Tder f * g
  rw [Tder.leibniz]
  simp only [smul_eq_mul]
  rw [mul_comm g (Tder f)]

/-- `T` kills the vacuum. -/
@[simp] theorem T_one : T (1 : Fock) = 0 := Tder.map_one_eq_zero

/-- `T` kills the constants. -/
@[simp] theorem T_C (a : ℂ) : T (MvPolynomial.C a : Fock) = 0 := derivation_C Tder a

/-! ### The commutator of `T` with a partial derivative

`[∂ᵢ, T] = lvl(i)·∂_{down i}`.  Both sides are derivations, so it suffices to check on the
variables — `MvPolynomial.derivation_ext` applied to the Lie bracket of derivations. -/

/-- The generator computation behind `[∂ᵢ, T] = lvl(i)·∂_{down i}`. -/
theorem pderiv_Tder_X (i m : ℕ ⊕ ℕ) :
    (pderiv i) (Tder (X m)) = (lvl i : ℂ) • (pderiv (down i)) (X m) := by
  have hT : Tder (X m) = ((lvl m : ℂ) + 1) • X (up m) := T_X m
  rw [hT, Derivation.map_smul, pderiv_X, pderiv_X, Pi.single_apply, Pi.single_apply]
  by_cases h : up m = i
  · subst h
    rw [if_pos rfl, if_pos (down_up m).symm, lvl_up, Nat.cast_add, Nat.cast_one]
  · rw [if_neg h]
    by_cases h2 : m = down i
    · have hz : lvl i = 0 := by
        by_contra hz
        exact h (by rw [h2, up_down hz])
      rw [hz]
      simp
    · rw [if_neg h2]
      simp

/-- `T` kills `∂ᵢ (X m)`, which is a constant. -/
theorem Tder_pderiv_X (i m : ℕ ⊕ ℕ) : Tder ((pderiv i) (X m)) = 0 := by
  rw [pderiv_X, Pi.single_apply]
  by_cases h : m = i
  · rw [if_pos h]; exact Tder.map_one_eq_zero
  · rw [if_neg h]; exact map_zero _

/-- **`[∂ᵢ, T] = lvl(i)·∂_{down i}`** as an identity of derivations. -/
theorem pderiv_Tder_bracket (i : ℕ ⊕ ℕ) :
    ⁅(pderiv i : Derivation ℂ Fock Fock), Tder⁆
      = (lvl i : ℂ) • (pderiv (down i) : Derivation ℂ Fock Fock) := by
  ext m
  rw [Derivation.commutator_apply, pderiv_Tder_X, Tder_pderiv_X, sub_zero,
    Derivation.smul_apply]

theorem pderiv_Tder_comm (i : ℕ ⊕ ℕ) (f : Fock) :
    (pderiv i) (Tder f) - Tder ((pderiv i) f) = (lvl i : ℂ) • (pderiv (down i)) f := by
  have h := DFunLike.congr_fun (pderiv_Tder_bracket i) f
  rwa [Derivation.commutator_apply, Derivation.smul_apply] at h

/-! ### The two operator brackets -/

/-- `[T, X i ·] = (lvl i + 1)·(X (up i) ·)` — the creation half. -/
theorem T_mulX (i : ℕ ⊕ ℕ) :
    T * mulX i - mulX i * T = ((lvl i : ℂ) + 1) • mulX (up i) := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, mulX_apply, LinearMap.smul_apply]
  rw [T_mul, add_sub_cancel_left, T_X, smul_mul_assoc]

/-- `[T, ∂ᵢ] = -lvl(i)·∂_{down i}` — the annihilation half. -/
theorem T_der (i : ℕ ⊕ ℕ) :
    T * der i - der i * T = -((lvl i : ℂ) • der (down i)) := by
  refine LinearMap.ext fun f => ?_
  have h := pderiv_Tder_comm i f
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, der_apply, T_apply]
  rw [← h]
  abel

/-- Conjugation by `T` is additive, so it flips sign with its argument. -/
theorem T_bracket_neg (A : Module.End ℂ Fock) :
    T * (-A) - (-A) * T = -(T * A - A * T) := by
  rw [mul_neg, neg_mul]; abel

/-! ## §5  Translation covariance of the two generators -/

/-- **`βZ` is `T`-covariant**: `[T, βⱼ] = (j+1)·β_{j+1}`. -/
theorem betaZ_DCovariant : Reconstruction.DCovariant T betaZ := by
  intro j
  by_cases hj : 0 ≤ j
  · -- creation side
    rw [betaZ_of_nonneg hj, betaZ_of_nonneg (by omega : (0 : ℤ) ≤ j + 1), T_mulX, lvl_inl, up_inl,
      show (j + 1).toNat = j.toNat + 1 by omega, ← Int.cast_smul_eq_zsmul ℂ (j + 1)]
    congr 1
    have hc : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by
      have h : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj
      exact_mod_cast h
    rw [hc]
    push_cast
    ring
  · by_cases hj1 : j = -1
    · -- the mode that maps to zero
      subst hj1
      rw [betaZ_of_neg hj, show ((-1 : ℤ) + 1) = 0 by ring, zero_smul,
        show (-(-1 : ℤ) - 1).toNat = 0 by omega, T_der, lvl_inr]
      simp
    · -- annihilation side
      rw [betaZ_of_neg hj, betaZ_of_neg (by omega : ¬ (0 : ℤ) ≤ j + 1), T_der, lvl_inr, down_inr,
        show (-j - 1).toNat - 1 = (-(j + 1) - 1).toNat by omega,
        ← Int.cast_smul_eq_zsmul ℂ (j + 1), ← neg_smul]
      congr 1
      have hc : ((((-j - 1).toNat : ℕ)) : ℂ) = -(j : ℂ) - 1 := by
        have h : (((-j - 1).toNat : ℕ) : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h
      rw [hc]
      push_cast
      ring

/-- **`γZ` is `T`-covariant**: `[T, γⱼ] = (j+1)·γ_{j+1}`. -/
theorem gammaZ_DCovariant : Reconstruction.DCovariant T gammaZ := by
  intro j
  by_cases hj : 0 ≤ j
  · -- creation side
    rw [gammaZ_of_nonneg hj, gammaZ_of_nonneg (by omega : (0 : ℤ) ≤ j + 1), T_mulX, lvl_inr,
      up_inr, show (j + 1).toNat = j.toNat + 1 by omega, ← Int.cast_smul_eq_zsmul ℂ (j + 1)]
    congr 1
    have hc : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by
      have h : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj
      exact_mod_cast h
    rw [hc]
    push_cast
    ring
  · by_cases hj1 : j = -1
    · subst hj1
      rw [gammaZ_of_neg hj, show ((-1 : ℤ) + 1) = 0 by ring, zero_smul,
        show (-(-1 : ℤ) - 1).toNat = 0 by omega, T_bracket_neg, T_der, lvl_inl]
      simp
    · rw [gammaZ_of_neg hj, gammaZ_of_neg (by omega : ¬ (0 : ℤ) ≤ j + 1), T_bracket_neg, T_der,
        neg_neg, lvl_inl, down_inl, show (-j - 1).toNat - 1 = (-(j + 1) - 1).toNat by omega,
        ← Int.cast_smul_eq_zsmul ℂ (j + 1), smul_neg, ← neg_smul]
      congr 1
      have hc : ((((-j - 1).toNat : ℕ)) : ℂ) = -(j : ℂ) - 1 := by
        have h : (((-j - 1).toNat : ℕ) : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h
      rw [hc]
      push_cast
      ring

/-! ## §6  The vacuum and the creation values

The vacuum is the constant polynomial `1`.  Both generators annihilate it in every negative
degree and create their own generating variable in degree `0` — the `hcreneg` / `hcre0`
hypotheses of `reconstructε`. -/

/-- The vacuum vector of the `βγ` Fock space. -/
noncomputable def vac : Fock := 1

/-- `T` kills the vacuum (the `hTvac` hypothesis). -/
@[simp] theorem T_vac : T vac = 0 := T_one

/-- `β` annihilates the vacuum in every negative degree (the `hcreneg` hypothesis). -/
theorem betaZ_vac_of_neg {j : ℤ} (hj : j < 0) : betaZ j vac = 0 := by
  rw [betaZ_of_neg (by omega), der_apply]
  show pderiv (Sum.inr (-j - 1).toNat) (1 : Fock) = 0
  exact pderiv_one

/-- `γ` annihilates the vacuum in every negative degree (the `hcreneg` hypothesis). -/
theorem gammaZ_vac_of_neg {j : ℤ} (hj : j < 0) : gammaZ j vac = 0 := by
  rw [gammaZ_of_neg (by omega), LinearMap.neg_apply, der_apply]
  show -(pderiv (Sum.inl (-j - 1).toNat) (1 : Fock)) = 0
  rw [pderiv_one, neg_zero]

/-- The creation tower on the vacuum: in degree `j ≥ 0`, `β` produces the `j`-th `inl`
variable. -/
theorem betaZ_vac_of_nonneg {j : ℤ} (hj : 0 ≤ j) : betaZ j vac = X (Sum.inl j.toNat) := by
  rw [betaZ_of_nonneg hj, mulX_apply]
  show X (Sum.inl j.toNat) * (1 : Fock) = X (Sum.inl j.toNat)
  rw [mul_one]

/-- The creation tower on the vacuum: in degree `j ≥ 0`, `γ` produces the `j`-th `inr`
variable. -/
theorem gammaZ_vac_of_nonneg {j : ℤ} (hj : 0 ≤ j) : gammaZ j vac = X (Sum.inr j.toNat) := by
  rw [gammaZ_of_nonneg hj, mulX_apply]
  show X (Sum.inr j.toNat) * (1 : Fock) = X (Sum.inr j.toNat)
  rw [mul_one]

/-- `β` creates its own variable out of the vacuum (the `hcre0` hypothesis). -/
theorem betaZ_vac_zero : betaZ 0 vac = X (Sum.inl 0) := betaZ_vac_of_nonneg le_rfl

/-- `γ` creates its own variable out of the vacuum (the `hcre0` hypothesis). -/
theorem gammaZ_vac_zero : gammaZ 0 vac = X (Sum.inr 0) := gammaZ_vac_of_nonneg le_rfl

end VOA.BG
