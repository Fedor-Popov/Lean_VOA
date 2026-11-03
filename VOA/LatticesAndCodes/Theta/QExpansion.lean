/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Theta.ModularForm
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The `q`-expansion of the theta function of an even lattice

For an even positive definite lattice `Γ`,

  `ϑ_Γ(τ) = ∑_{m ≥ 0} r_Γ(2m) q^m`,   `q = e^{2πiτ}`,

where `r_Γ` is the representation number `IntegralLattice.repCount` of `Theta/Counting.lean`.
When `Γ` is in addition unimodular, `ϑ_Γ` is a modular form of weight `n/2` (M20), and
`IntegralLattice.coeff_qExpansion_thetaModularForm` identifies the `m`-th coefficient of
Mathlib's `UpperHalfPlane.qExpansion` of that modular form with `r_Γ(2m)`.

## Why this file exists

It is the **bridge between the analytic and the combinatorial layer**.  Every downstream
statement of the shape "such-and-such a lattice has this many vectors of norm `2m`" is obtained
by writing `ϑ_Γ` as a polynomial in `E₄` and `Δ` — an identity between modular forms — and then
comparing `q`-expansions.  Without the bridge those identities say nothing about lattice vectors.
It is a shared prerequisite of Gleason's theorem (M21), Ebeling's Proposition 2.8 and
`ϑ_Λ = E₄³ − 720Δ` for the Leech lattice (M22), and the cusp-form statement of Corollary 3.3
(M24), which is why it lives in its own file rather than inside any of them.

## The proof

`IntegralLattice.hasSum_theta` is the whole mathematical content: partition `Γ` into the fibres
of `IntegralLattice.halfNorm`, on each of which the summand `e^{πiτ·x²}` is the *constant* `q^m`,
and sum fibrewise with `HasSum.sigma`.  Each fibre is `IntegralLattice.repFinset`, already known
finite, so the fibre sum is `r_Γ(2m) q^m` by `Finset.sum_const`.  No new analysis is needed: the
summability is M18's `IntegralLattice.summable_thetaTerm`.

Mathlib then does the rest.  `UpperHalfPlane.qExpansion` is *defined* as the Taylor series of the
cusp function, but `ModularFormClass.qExpansion_coeff_unique` says that any convergent
`q`-expansion computes those coefficients, so no contact with `cuspFunction` is needed.

## Main results

* `IntegralLattice.hasSum_theta` — the grouping identity, for any even positive definite lattice.
* `IntegralLattice.coeff_qExpansion_thetaModularForm` — the bridge.
* `IntegralLattice.repCount_eq_of_hasSum_thetaFun` — the form downstream wants: if `ϑ_Γ` is known
  to have some `q`-expansion, its coefficients *are* the representation numbers.

## References

Ebeling, *Lattices and Codes*, §2.1 and §2.8.
-/

open Complex UpperHalfPlane
open scoped MatrixGroups Real

namespace IntegralLattice

variable {Γ : IntegralLattice}

/-! ### Half-norms -/

/-- Half the norm of a lattice vector, as a natural number.  On an even positive definite lattice
`2 * halfNorm x = normSq x`, so `halfNorm` indexes the fibres of the norm. -/
noncomputable def halfNorm (Γ : IntegralLattice) (x : Γ) : ℕ := (normSq x / 2).toNat

theorem two_mul_halfNorm (h : Γ.IsPosDef) (he : Γ.IsEven) (x : Γ) :
    2 * (Γ.halfNorm x : ℤ) = normSq x := by
  obtain ⟨k, hk⟩ := he x
  have hnn : (0 : ℤ) ≤ normSq x := h.normSq_nonneg x
  rw [halfNorm, hk]
  omega

theorem halfNorm_eq_iff (h : Γ.IsPosDef) (he : Γ.IsEven) {x : Γ} {m : ℕ} :
    Γ.halfNorm x = m ↔ normSq x = 2 * (m : ℤ) := by
  have hx := two_mul_halfNorm h he x
  omega

/-! ### Grouping the theta series by norm -/

/-- The fibre of `halfNorm` over `m` is the set of vectors of norm `2m`. -/
def fiberEquiv (h : Γ.IsPosDef) (he : Γ.IsEven) (m : ℕ) :
    {x : Γ // Γ.halfNorm x = m} ≃ {x : Γ // x ∈ Γ.repFinset h (2 * (m : ℤ))} :=
  Equiv.subtypeEquivRight fun x => by rw [mem_repFinset, halfNorm_eq_iff h he]

/-- On the fibre `normSq x = 2m` every term of the theta series is `q^m`, so the fibre contributes
`r_Γ(2m) q^m`. -/
theorem hasSum_thetaTerm_fiber (h : Γ.IsPosDef) (he : Γ.IsEven) (τ : ℂ) (m : ℕ) :
    HasSum (fun b : {x : Γ // Γ.halfNorm x = m} => Γ.thetaTerm (b : Γ) τ)
      ((Γ.repCount (2 * (m : ℤ)) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m) := by
  have hterm : ∀ x ∈ Γ.repFinset h (2 * (m : ℤ)),
      Γ.thetaTerm x τ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m := by
    intro x hx
    have hx' : normSq x = 2 * (m : ℤ) := mem_repFinset.mp hx
    rw [thetaTerm, hx', ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hval : ∑ x ∈ Γ.repFinset h (2 * (m : ℤ)), Γ.thetaTerm x τ
      = (Γ.repCount (2 * (m : ℤ)) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_repFinset, nsmul_eq_mul]
  have key : HasSum (fun b : {x : Γ // x ∈ Γ.repFinset h (2 * (m : ℤ))} => Γ.thetaTerm (b : Γ) τ)
      ((Γ.repCount (2 * (m : ℤ)) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m) := by
    rw [← hval]
    exact Finset.hasSum _ _
  exact (Equiv.hasSum_iff (fiberEquiv h he m)).mpr key

/-- **The `q`-expansion of the theta function**, as a summation identity:
`ϑ_Γ(τ) = ∑_{m ≥ 0} r_Γ(2m) q^m` with `q = e^{2πiτ}`. -/
theorem hasSum_theta (h : Γ.IsPosDef) (he : Γ.IsEven) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℕ =>
        (Γ.repCount (2 * (m : ℤ)) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m)
      (Γ.theta τ) := by
  have hsum : HasSum (fun x : Γ => Γ.thetaTerm x τ) (Γ.theta τ) :=
    (Γ.summable_thetaTerm h hτ).hasSum
  have hsig : HasSum
      (fun p : (m : ℕ) × {x : Γ // Γ.halfNorm x = m} => Γ.thetaTerm (p.2 : Γ) τ) (Γ.theta τ) :=
    (Equiv.sigmaFiberEquiv Γ.halfNorm).hasSum_iff.mpr hsum
  exact hsig.sigma fun m => hasSum_thetaTerm_fiber h he τ m

/-! ### The bridge to `Mathlib`'s `q`-expansion -/

/-- **The `q`-expansion bridge.**  The `m`-th coefficient of the `q`-expansion of `ϑ_Γ`, taken as
a modular form of weight `n/2` for the full modular group, is the representation number
`r_Γ(2m)`.

This is what connects the analytic layer to the combinatorial one: statements about the
coefficients of a modular form become statements about how many lattice vectors have a given
norm. -/
theorem coeff_qExpansion_thetaModularForm (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular)
    (m : ℕ) :
    (qExpansion 1 (Γ.thetaModularForm h he hu)).coeff m = (Γ.repCount (2 * (m : ℤ)) : ℂ) := by
  refine (ModularFormClass.qExpansion_coeff_unique (h := 1) (Γ := 𝒮ℒ) one_pos
    one_mem_strictPeriods_SL (f := Γ.thetaModularForm h he hu)
    (c := fun j => (Γ.repCount (2 * (j : ℤ)) : ℂ)) (fun τ => ?_) m).symm
  have hfun : (fun j : ℕ => (Γ.repCount (2 * (j : ℤ)) : ℂ) •
        (Function.Periodic.qParam 1 (τ : ℂ)) ^ j)
      = fun j : ℕ => (Γ.repCount (2 * (j : ℤ)) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ j := by
    funext j
    rw [smul_eq_mul, Function.Periodic.qParam]
    norm_num
  rw [hfun]
  exact hasSum_theta h he τ.im_pos

/-- The constant term of `ϑ_Γ` is `1`. -/
theorem coeff_qExpansion_thetaModularForm_zero (h : Γ.IsPosDef) (he : Γ.IsEven)
    (hu : Γ.IsUnimodular) : (qExpansion 1 (Γ.thetaModularForm h he hu)).coeff 0 = 1 := by
  rw [coeff_qExpansion_thetaModularForm h he hu 0]
  norm_num [Γ.repCount_zero h]

/-- **Reading representation numbers off a `q`-expansion.**  If the theta function of an even
unimodular positive definite lattice is known to be given by the series `∑ c_j q^j` — typically
because `ϑ_Γ` has been identified with a polynomial in `E₄` and `Δ` whose expansion is known —
then `c_m = r_Γ(2m)`. -/
theorem repCount_eq_of_hasSum_thetaFun (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular)
    {c : ℕ → ℂ}
    (hc : ∀ τ : ℍ, HasSum (fun j : ℕ => c j • Function.Periodic.qParam 1 (τ : ℂ) ^ j)
      (Γ.thetaModularForm h he hu τ)) (m : ℕ) :
    c m = (Γ.repCount (2 * (m : ℤ)) : ℂ) := by
  rw [ModularFormClass.qExpansion_coeff_unique (h := 1) (Γ := 𝒮ℒ) one_pos
    one_mem_strictPeriods_SL (f := Γ.thetaModularForm h he hu) hc m,
    coeff_qExpansion_thetaModularForm h he hu m]

end IntegralLattice
