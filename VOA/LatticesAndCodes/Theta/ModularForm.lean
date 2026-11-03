/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Theta.Transformation
import VOA.LatticesAndCodes.ModularForms.LevelOne
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Theorem 2.1: the theta function of an even unimodular lattice

**Ebeling, Theorem 2.1.**  If `Γ` is an even unimodular positive definite lattice of rank `n`,
then `8 ∣ n` and `ϑ_Γ` is a modular form of weight `n/2` for the full modular group.

## What is delivered

`IntegralLattice.thetaModularForm` is an honest `ModularForm 𝒮ℒ (n/2)` term, not merely the pair
of transformation identities: the later milestones (Gleason, the Leech lattice, the
Hecke–Schoeneberg theory) consume the bundled object.  `IntegralLattice.theta_isModularForm` is
the statement of the theorem, and `IntegralLattice.eight_dvd_rank` the divisibility on its own.

## The route

Three inputs, each already available:

* **`S`.**  Proposition 2.1 (M18) reads `ϑ_Γ(-1/τ) = (τ/i)^{n/2} (1/√det) ϑ_{Γ*}(τ)`, with `Γ*`
  the dual of the *Euclidean realisation* of `Γ`.  Unimodularity turns the right-hand side back
  into `ϑ_Γ`: `IntegralLattice.dual_range_toEuclidean` proves that the realisation is self-dual,
  and `IntegralLattice.det_eq_one` that the covolume is `1`.  Self-duality is where
  unimodularity is really used — the inverse Gram matrix `IntegralLattice.gramInv` is integral,
  so each dual basis vector is again a lattice vector.
* **`T`.**  Evenness gives `ϑ_Γ(τ + 1) = ϑ_Γ(τ)` term by term
  (`IntegralLattice.theta_add_one`); no convergence is involved.
* **`8 ∣ n`.**  Composing the two round the relation `(ST)³ = 1`.  Starting from `τ = i` and
  applying `T, S, T, S, T` returns to `i`, and the product of the three automorphy factors is
  `((1-i)/2)^{n/2} (1-i)^{n/2}` — this is `IntegralLattice.theta_chain`, and it equals `1`
  because `ϑ_Γ(i) = ∑_x e^{-π x²} > 0` is a sum of positive reals
  (`IntegralLattice.theta_I_ne_zero`).

  The identity is then read twice.  Squaring it removes the branch cut: the exponents add
  (`Complex.cpow_add`) to the *integer* `n`, giving `(-i)^n = 1`, hence `4 ∣ n`.  Knowing
  `4 ∣ n`, the exponent `n/2` is itself a natural number, so the unsquared identity may be read
  with an ordinary power: it becomes `(-1)^{n/4} = 1`, hence `8 ∣ n`.  No logarithm and no
  argument computation is needed anywhere, and no nonvanishing statement beyond `ϑ_Γ(i) ≠ 0`.

  This is why the base point is `i` and not the fixed point `ρ` of `τ ↦ -1/(τ+1)`: at `ρ` the
  three factors coincide and the relation is shorter, but `ϑ_Γ(ρ) = ∑_j r_Γ(2j)(-1)^j e^{-π√3 j}`
  is an alternating series whose nonvanishing is not free.

Boundedness at the cusps is the crude bound `‖ϑ_Γ(τ)‖ ≤ ϑ_Γ(i)` for `Im τ ≥ 1`; holomorphy is
`IntegralLattice.theta_holomorphic` (M18) transported through `UpperHalfPlane.mdifferentiable_iff`.

## Main results

* `IntegralLattice.dual_range_toEuclidean` — a unimodular lattice realises as a self-dual
  `ℤ`-lattice in Euclidean space.
* `IntegralLattice.theta_neg_inv_self` — `ϑ_Γ(-1/τ) = (τ/i)^{n/2} ϑ_Γ(τ)`.
* `IntegralLattice.theta_add_one` — `ϑ_Γ(τ+1) = ϑ_Γ(τ)`.
* `IntegralLattice.eight_dvd_rank` — `8 ∣ n`.
* `IntegralLattice.thetaModularForm`, `IntegralLattice.theta_isModularForm` — Theorem 2.1.

## References

Ebeling, *Lattices and Codes*, §2.1 (Theorem 2.1).
-/

noncomputable section

open Complex ModularForm SlashInvariantForm InnerProductSpace Filter
open scoped Real Manifold MatrixGroups UpperHalfPlane RealInnerProductSpace ModularForm

namespace IntegralLattice

variable {Γ : IntegralLattice}

/-! ### The determinant of a positive definite unimodular lattice -/

/-- A positive definite lattice has positive determinant: its real Gram matrix is positive
definite. -/
theorem det_pos (h : Γ.IsPosDef) : 0 < Γ.det := by
  have hd := (Γ.posDef_gramReal h).det_pos
  rw [Γ.det_gramReal] at hd
  exact_mod_cast hd

/-- A positive definite unimodular lattice has determinant `1`, so covolume `1`. -/
theorem det_eq_one (h : Γ.IsPosDef) (hu : Γ.IsUnimodular) : Γ.det = 1 := by
  rcases Γ.isUnimodular_iff.mp hu with h1 | h1
  · exact h1
  · have := Γ.det_pos h
    omega

/-! ### Self-duality of the Euclidean realisation

For a unimodular lattice the inverse Gram matrix is again integral, so every vector of the dual
basis is itself a lattice vector.  This is the only place unimodularity enters Theorem 2.1
besides the covolume. -/

section SelfDual

/-- The inverse of the Gram matrix in the chosen basis.  For a unimodular lattice it is
integral, which is what makes the Euclidean realisation self-dual. -/
def gramInv (Γ : IntegralLattice) : Matrix (Fin Γ.rank) (Fin Γ.rank) ℤ :=
  (Γ.gram Γ.chooseBasis)⁻¹

theorem isUnit_det_gram (hu : Γ.IsUnimodular) : IsUnit (Γ.gram Γ.chooseBasis).det := by
  rw [← Γ.det_eq_det_gram_chooseBasis]; exact hu

theorem gramInv_mul_gram (hu : Γ.IsUnimodular) : Γ.gramInv * Γ.gram Γ.chooseBasis = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_gram hu)

/-- The lattice vector whose Euclidean image is the `i`-th vector of the dual basis. -/
def dualVec (Γ : IntegralLattice) (i : Fin Γ.rank) : Γ :=
  ∑ k, Γ.gramInv i k • Γ.chooseBasis k

theorem bilin_dualVec (hu : Γ.IsUnimodular) (i j : Fin Γ.rank) :
    Γ.bilin (Γ.dualVec i) (Γ.chooseBasis j) = if j = i then 1 else 0 := by
  classical
  have h1 : Γ.bilin (Γ.dualVec i) (Γ.chooseBasis j)
      = ∑ k, Γ.gramInv i k * Γ.gram Γ.chooseBasis k j := by
    rw [dualVec, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [bilin_smul_left, gram_apply]
  rw [h1, ← Matrix.mul_apply, gramInv_mul_gram hu]
  by_cases hij : j = i
  · subst hij
    simp
  · rw [Matrix.one_apply_ne fun hc => hij hc.symm, if_neg hij]

theorem inner_toEuclidean_dualVec (h : Γ.IsPosDef) (hu : Γ.IsUnimodular) (i j : Fin Γ.rank) :
    ⟪Γ.toEuclidean h (Γ.dualVec i), Γ.euclideanBasis h j⟫ = if j = i then 1 else 0 := by
  simp only [coe_euclideanBasis]
  rw [Γ.inner_toEuclidean h, bilin_dualVec hu]
  split_ifs <;> norm_num

/-- Each dual basis vector of the Euclidean realisation is the image of a lattice vector.
This is the content of unimodularity. -/
theorem dualBasis_eq_toEuclidean (h : Γ.IsPosDef) (hu : Γ.IsUnimodular) (i : Fin Γ.rank) :
    ZSpan.dualBasis (Γ.euclideanBasis h) i = Γ.toEuclidean h (Γ.dualVec i) :=
  ext_inner_right_basis (Γ.euclideanBasis h) fun j => by
    rw [ZSpan.inner_dualBasis, inner_toEuclidean_dualVec h hu]

/-- Conversely — and this needs only integrality — each basis vector is an integral combination
of the dual basis, with the Gram matrix as coefficients. -/
theorem euclideanBasis_eq_sum_dualBasis (h : Γ.IsPosDef) (i : Fin Γ.rank) :
    Γ.euclideanBasis h i
      = ∑ k, ((Γ.gram Γ.chooseBasis i k : ℤ) : ℝ) • ZSpan.dualBasis (Γ.euclideanBasis h) k := by
  classical
  refine ext_inner_right_basis (Γ.euclideanBasis h) fun j => ?_
  rw [sum_inner]
  have hR : ∑ k, ⟪((Γ.gram Γ.chooseBasis i k : ℤ) : ℝ) • ZSpan.dualBasis (Γ.euclideanBasis h) k,
      Γ.euclideanBasis h j⟫ = ((Γ.gram Γ.chooseBasis i j : ℤ) : ℝ) := by
    simp only [real_inner_smul_left, ZSpan.inner_dualBasis, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [hR]
  simp only [coe_euclideanBasis]
  rw [Γ.inner_toEuclidean h, gram_apply]

/-- **The Euclidean realisation of a positive definite unimodular lattice is self-dual.**
This is what turns Proposition 2.1 into a transformation law for `ϑ_Γ` itself. -/
theorem dual_range_toEuclidean (h : Γ.IsPosDef) (hu : Γ.IsUnimodular) :
    ZLattice.dual (EuclideanSpace ℝ (Fin Γ.rank)) (LinearMap.range (Γ.toEuclidean h))
      = LinearMap.range (Γ.toEuclidean h) := by
  have hspan := Γ.range_toEuclidean_eq_span h
  rw [hspan, ZLattice.dual_span]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : Γ.toEuclidean h (Γ.dualVec i) ∈ LinearMap.range (Γ.toEuclidean h) :=
      LinearMap.mem_range_self _ _
    rw [hspan] at hmem
    rw [SetLike.mem_coe, dualBasis_eq_toEuclidean h hu]
    exact hmem
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, euclideanBasis_eq_sum_dualBasis h]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end SelfDual

/-! ### The two transformation laws -/

/-- **Ebeling, Proposition 2.1 for an even unimodular lattice**:
`ϑ_Γ(-1/τ) = (τ/i)^{n/2} ϑ_Γ(τ)`. -/
theorem theta_neg_inv_self (h : Γ.IsPosDef) (hu : Γ.IsUnimodular) {τ : ℂ} (hτ : 0 < τ.im) :
    Γ.theta (-1 / τ) = (τ / Complex.I) ^ ((Γ.rank : ℂ) / 2) * Γ.theta τ := by
  rw [Γ.theta_neg_inv h hτ, dual_range_toEuclidean h hu, ← Γ.theta_eq_euclidean h,
    det_eq_one h hu]
  norm_num

/-- Evenness gives `T`-invariance, `ϑ_Γ(τ + 1) = ϑ_Γ(τ)`, term by term.  No convergence is
involved, so this holds for every `τ ∈ ℂ`. -/
theorem theta_add_one (he : Γ.IsEven) (τ : ℂ) : Γ.theta (τ + 1) = Γ.theta τ := by
  refine tsum_congr fun x => ?_
  obtain ⟨j, hj⟩ := he x
  have key : (Real.pi : ℂ) * Complex.I * (τ + 1) * (((2 * j : ℤ)) : ℂ)
      = (Real.pi : ℂ) * Complex.I * τ * (((2 * j : ℤ)) : ℂ)
        + ((j : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [thetaTerm, thetaTerm, hj, key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### `ϑ_Γ(i) ≠ 0` -/

theorem thetaTerm_I (x : Γ) :
    Γ.thetaTerm x Complex.I = ((Real.exp (-(Real.pi * ((normSq x : ℤ) : ℝ))) : ℝ) : ℂ) := by
  rw [thetaTerm, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((Real.pi : ℂ) * ((normSq x : ℤ) : ℂ)) * Complex.I_sq

/-- `ϑ_Γ(i) = ∑_x e^{-π x²}` is a sum of positive reals, so it does not vanish.  This is the
only nonvanishing input Theorem 2.1 needs. -/
theorem theta_I_ne_zero (h : Γ.IsPosDef) : Γ.theta Complex.I ≠ 0 := by
  have hs : Summable (fun x : Γ => Real.exp (-(Real.pi * ((normSq x : ℤ) : ℝ)))) :=
    Γ.summable_exp_neg_mul_normSq h Real.pi_pos
  have hval : Γ.theta Complex.I
      = ((∑' x : Γ, Real.exp (-(Real.pi * ((normSq x : ℤ) : ℝ))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, theta]
    exact tsum_congr fun x => thetaTerm_I x
  have hpos : 0 < ∑' x : Γ, Real.exp (-(Real.pi * ((normSq x : ℤ) : ℝ))) :=
    hs.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  rw [hval]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)

/-! ### `8 ∣ n` -/

section Divisibility

private theorem cpow_two_mul {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z ^ (2 * s) = (z ^ s) ^ 2 := by
  rw [two_mul, Complex.cpow_add _ _ hz, sq]

private theorem base_mul : ((1 - Complex.I) / 2) * (1 - Complex.I) = -Complex.I := by
  linear_combination Complex.I_sq / 2

private theorem one_sub_I_ne : (1 - Complex.I : ℂ) ≠ 0 := by simp [Complex.ext_iff]

private theorem one_sub_I_div_two_ne : ((1 - Complex.I) / 2 : ℂ) ≠ 0 := by
  simp [Complex.ext_iff]

/-- The relation `(ST)³ = 1`, run from `τ = i`, applied to `ϑ_Γ`.  Five moves — `T, S, T, S, T` —
carry `i` back to `i`, and the two nontrivial automorphy factors multiply to the left-hand side
below. -/
theorem theta_chain (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular) :
    ((1 - Complex.I) / 2) ^ ((Γ.rank : ℂ) / 2) * (1 - Complex.I) ^ ((Γ.rank : ℂ) / 2) = 1 := by
  have hI1 : (0 : ℝ) < (Complex.I + 1).im := by simp
  have hI2 : (0 : ℝ) < ((1 + Complex.I) / 2 : ℂ).im := by norm_num
  have p1 : (-1 : ℂ) / (Complex.I + 1) = (-1 + Complex.I) / 2 := by
    rw [div_eq_iff (by simp [Complex.ext_iff] : (Complex.I + 1 : ℂ) ≠ 0)]
    linear_combination -Complex.I_sq / 2
  have q1 : ((Complex.I + 1) / Complex.I : ℂ) = 1 - Complex.I := by
    rw [div_eq_iff Complex.I_ne_zero]
    linear_combination Complex.I_sq
  have p3 : (-1 : ℂ) / ((1 + Complex.I) / 2) = -1 + Complex.I := by
    rw [div_div_eq_mul_div, div_eq_iff (by simp [Complex.ext_iff] : (1 + Complex.I : ℂ) ≠ 0)]
    linear_combination -Complex.I_sq
  have q3 : (((1 + Complex.I) / 2) / Complex.I : ℂ) = (1 - Complex.I) / 2 := by
    rw [div_div, div_eq_iff (by simp [Complex.ext_iff] : (2 * Complex.I : ℂ) ≠ 0)]
    linear_combination Complex.I_sq
  have e2 := theta_neg_inv_self h hu hI1
  have e4 := theta_neg_inv_self h hu hI2
  rw [p1, q1] at e2
  rw [p3, q3] at e4
  have t1 : Γ.theta (Complex.I + 1) = Γ.theta Complex.I := theta_add_one he Complex.I
  have t2 : Γ.theta ((-1 + Complex.I) / 2 + 1) = Γ.theta ((-1 + Complex.I) / 2) :=
    theta_add_one he _
  have t3 : Γ.theta (-1 + Complex.I + 1) = Γ.theta (-1 + Complex.I) := theta_add_one he _
  rw [show ((-1 + Complex.I) / 2 + 1 : ℂ) = (1 + Complex.I) / 2 from by ring] at t2
  rw [show (-1 + Complex.I + 1 : ℂ) = Complex.I from by ring] at t3
  have hround : Γ.theta Complex.I
      = ((1 - Complex.I) / 2) ^ ((Γ.rank : ℂ) / 2)
        * ((1 - Complex.I) ^ ((Γ.rank : ℂ) / 2) * Γ.theta Complex.I) := by
    conv_lhs => rw [t3]
    rw [e4, t2, e2, t1]
  refine mul_right_cancel₀ (theta_I_ne_zero h) ?_
  rw [one_mul, mul_assoc]
  exact hround.symm

/-- **Ebeling, Theorem 2.1, first half.**  The rank of an even unimodular positive definite
lattice is divisible by `8`. -/
theorem eight_dvd_rank (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular) : 8 ∣ Γ.rank := by
  have key := theta_chain h he hu
  -- Squaring removes the branch cut: the exponents add to the integer `n`.
  have h4 : 4 ∣ Γ.rank := by
    have hsq : (((1 - Complex.I) / 2) ^ ((Γ.rank : ℂ) / 2)
        * (1 - Complex.I) ^ ((Γ.rank : ℂ) / 2)) ^ 2 = 1 := by rw [key]; ring
    rw [mul_pow, ← cpow_two_mul one_sub_I_div_two_ne, ← cpow_two_mul one_sub_I_ne,
      show (2 : ℂ) * ((Γ.rank : ℂ) / 2) = ((Γ.rank : ℕ) : ℂ) from by ring,
      Complex.cpow_natCast, Complex.cpow_natCast, ← mul_pow, base_mul] at hsq
    have hroot : IsPrimitiveRoot (-Complex.I : ℂ) 4 := by
      apply IsPrimitiveRoot.mk_of_lt _ (by norm_num)
      · rw [show 4 = 2 * 2 by norm_num, pow_mul]
        rw [show (-Complex.I : ℂ) ^ 2 = -1 by linear_combination Complex.I_sq]
        norm_num
      · intro l hl hlt
        interval_cases l
        · intro hEq
          have him := congrArg Complex.im hEq
          norm_num at him
        · intro hEq
          have hre := congrArg Complex.re hEq
          norm_num [pow_two, Complex.I_sq] at hre
        · intro hEq
          have him := congrArg Complex.im hEq
          norm_num [pow_succ, pow_two, Complex.I_sq] at him
    exact (hroot.pow_eq_one_iff_dvd _).mp hsq
  -- Knowing `4 ∣ n`, the exponent `n/2` is a natural number and the identity is elementary.
  obtain ⟨m, hm⟩ := h4
  rw [show ((Γ.rank : ℂ) / 2) = (((2 * m : ℕ)) : ℂ) from by rw [hm]; push_cast; ring,
    Complex.cpow_natCast, Complex.cpow_natCast, ← mul_pow, base_mul, pow_mul,
    show ((-Complex.I) ^ 2 : ℂ) = -1 from by linear_combination Complex.I_sq] at key
  obtain ⟨p, hp⟩ := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp key
  exact ⟨p, by omega⟩

end Divisibility

/-! ### The bundled modular form -/

section Bundle

/-- `ϑ_Γ` read as a function on the upper half plane. -/
def thetaFun (Γ : IntegralLattice) : ℍ → ℂ := fun z => Γ.theta (z : ℂ)

@[simp] theorem thetaFun_apply (Γ : IntegralLattice) (z : ℍ) :
    Γ.thetaFun z = Γ.theta (z : ℂ) := rfl

theorem thetaFun_slash_T (he : Γ.IsEven) (k : ℤ) :
    Γ.thetaFun ∣[k] ModularGroup.T = Γ.thetaFun := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul]
  have hd : UpperHalfPlane.denom (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) z = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.T]
    simp
  rw [hd, one_zpow, mul_one, thetaFun_apply, thetaFun_apply, UpperHalfPlane.coe_vadd]
  rw [show ((1 : ℝ) : ℂ) + (z : ℂ) = (z : ℂ) + 1 from by push_cast; ring]
  exact theta_add_one he _

theorem thetaFun_slash_S (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular) :
    Γ.thetaFun ∣[((Γ.rank / 2 : ℕ) : ℤ)] ModularGroup.S = Γ.thetaFun := by
  obtain ⟨p, hp⟩ := eight_dvd_rank h he hu
  have hhalf : Γ.rank / 2 = 4 * p := by omega
  ext z
  have him : (0 : ℝ) < (z : ℂ).im := z.im_pos
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hfac : ((z : ℂ) / Complex.I) ^ ((Γ.rank : ℂ) / 2) = (z : ℂ) ^ (4 * p) := by
    rw [show ((Γ.rank : ℂ) / 2) = (((4 * p : ℕ)) : ℂ) from by rw [hp]; push_cast; ring,
      Complex.cpow_natCast, div_pow,
      show ((Complex.I) ^ (4 * p) : ℂ) = 1 from by rw [pow_mul, Complex.I_pow_four, one_pow],
      div_one]
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
  show Γ.theta ((-(z : ℂ))⁻¹) * (z : ℂ) ^ (-((Γ.rank / 2 : ℕ) : ℤ)) = Γ.theta (z : ℂ)
  rw [show ((-(z : ℂ))⁻¹) = -1 / (z : ℂ) from by rw [inv_neg, neg_div, one_div],
    theta_neg_inv_self h hu him, hfac, hhalf, zpow_neg, zpow_natCast]
  field_simp

theorem thetaFun_isBoundedAtImInfty (h : Γ.IsPosDef) :
    UpperHalfPlane.IsBoundedAtImInfty Γ.thetaFun := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑' x : Γ, Real.exp (-(Real.pi * ((normSq x : ℤ) : ℝ))), 1, fun z hz => ?_⟩
  have him : (0 : ℝ) < (z : ℂ).im := z.im_pos
  have hpi : 0 < Real.pi * (z : ℂ).im := by positivity
  have hsum1 : Summable (fun x : Γ => ‖Γ.thetaTerm x (z : ℂ)‖) :=
    (Γ.summable_exp_neg_mul_normSq h hpi).congr fun x => (Γ.norm_thetaTerm x _).symm
  have hsum0 : Summable (fun x : Γ => Real.exp (-(Real.pi * ((normSq x : ℤ) : ℝ)))) :=
    Γ.summable_exp_neg_mul_normSq h Real.pi_pos
  have hz' : (1 : ℝ) ≤ (z : ℂ).im := hz
  calc ‖Γ.thetaFun z‖ = ‖∑' x : Γ, Γ.thetaTerm x (z : ℂ)‖ := rfl
    _ ≤ ∑' x : Γ, ‖Γ.thetaTerm x (z : ℂ)‖ := norm_tsum_le_tsum_norm hsum1
    _ ≤ ∑' x : Γ, Real.exp (-(Real.pi * ((normSq x : ℤ) : ℝ))) := by
        refine Summable.tsum_le_tsum (fun x => ?_) hsum1 hsum0
        rw [Γ.norm_thetaTerm]
        refine Real.exp_le_exp.mpr ?_
        have hnn : (0 : ℝ) ≤ ((normSq x : ℤ) : ℝ) := by exact_mod_cast h.normSq_nonneg x
        have hstep : Real.pi * 1 * ((normSq x : ℤ) : ℝ)
            ≤ Real.pi * (z : ℂ).im * ((normSq x : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz' Real.pi_pos.le) hnn
        linarith

theorem thetaFun_mdifferentiable (h : Γ.IsPosDef) : MDiff Γ.thetaFun := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := Γ.theta)
    (fun w hw => (Γ.theta_holomorphic h hw).differentiableWithinAt) fun w hw => ?_
  simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]

/-- **Ebeling, Theorem 2.1.**  The theta function of an even unimodular positive definite lattice
of rank `n` is a modular form of weight `n/2` for the full modular group. -/
def thetaModularForm (Γ : IntegralLattice) (h : Γ.IsPosDef) (he : Γ.IsEven)
    (hu : Γ.IsUnimodular) : ModularForm 𝒮ℒ ((Γ.rank / 2 : ℕ) : ℤ) where
  toFun := Γ.thetaFun
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z (thetaFun_slash_S h he hu) (thetaFun_slash_T he _) A
  holo' := thetaFun_mdifferentiable h
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z (thetaFun_slash_S h he hu) (thetaFun_slash_T he _) γ]
    exact thetaFun_isBoundedAtImInfty h

@[simp] theorem coe_thetaModularForm (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular) :
    ⇑(Γ.thetaModularForm h he hu) = Γ.thetaFun := rfl

/-- **Ebeling, Theorem 2.1.**  For an even unimodular positive definite lattice of rank `n`,
`8 ∣ n` and `ϑ_Γ` is a modular form of weight `n/2` for `SL(2,ℤ)`. -/
theorem theta_isModularForm (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular) :
    8 ∣ Γ.rank ∧
      ∃ f : ModularForm 𝒮ℒ ((Γ.rank / 2 : ℕ) : ℤ), ∀ z : ℍ, f z = Γ.theta (z : ℂ) :=
  ⟨eight_dvd_rank h he hu, Γ.thetaModularForm h he hu, fun _ => rfl⟩

end Bundle

end IntegralLattice
