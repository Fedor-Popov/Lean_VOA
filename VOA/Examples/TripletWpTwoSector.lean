/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpAmbient
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Finite Fock coordinates for the lattice triplet `W(2)`

This file packages two pieces of free-field linear algebra used by the remaining `W(2)`
computations.

* `EEVec_eq_weight_bounded_sum` replaces the convolution `finsum` defining `EEVec` on a
  weight-homogeneous Fock state by an explicit finite interval.  This is the common expansion
  needed by the three mixed screening products.
* the later sections package the finite monomial basis of the charge-zero weight-ten sector and
  the detector reduction for the Adamovic--Milas identity.

No PBW theorem is involved: the bosonic Fock space is a multivariate polynomial ring with its
manifest monomial basis.
-/

namespace VOA.LatGen.WpTwoSector

open scoped BigOperators TensorProduct
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2

variable {L : IntegralLattice}

/-! ## An explicit bounded expansion of `EEVec` -/

/-- On a bosonic Fock vector of weight `w`, the convolution defining `EE(α)_s` has indices

`max 0 s ≤ m ≤ w + s`.

The lower bounds say respectively that the creation half has nonnegative index and the
annihilation half has nonpositive index.  The upper bound is the grading-positivity statement that
an annihilation operator of degree greater than `w` kills a weight-`w` polynomial. -/
theorem EEVec_eq_weight_bounded_sum (α : L.carrier) (s : ℤ) {w : ℕ}
    {x : FockN (rank L)} (hx : x ∈ gradingWN (rank L) w) :
    EEVec L α s x = ∑ m ∈ Finset.Icc (max 0 s) ((w : ℤ) + s),
      vSchur L α m.toNat * aExpVec L α (m - s).toNat x := by
  rw [EEVec_apply_conv L α s x]
  let f : ℤ → FockN (rank L) := fun m =>
    EminusVecField L α m (EplusVecField L α (s - m) x)
  have hsupp : Function.support f ⊆ Finset.Icc (max 0 s) ((w : ℤ) + s) := by
    intro m hm
    rw [Function.mem_support] at hm
    have hm0 : 0 ≤ m := by
      by_contra h
      rw [show f m = EminusVecField L α m (EplusVecField L α (s - m) x) from rfl,
        EminusVecField_neg L α (by omega), LinearMap.zero_apply] at hm
      exact hm rfl
    have hsm : s ≤ m := by
      by_contra h
      rw [show f m = EminusVecField L α m (EplusVecField L α (s - m) x) from rfl,
        EplusVecField_apply, if_neg (by omega), LinearMap.zero_apply, map_zero] at hm
      exact hm rfl
    have hmws : m ≤ (w : ℤ) + s := by
      by_contra h
      have hgrade := aExpVec_mem_gradingZN L α (m - s).toNat hx
      have hneg : (w : ℤ) - ((m - s).toNat : ℤ) < 0 := by omega
      rw [gradingZN_of_neg hneg, Submodule.mem_bot] at hgrade
      rw [show f m = EminusVecField L α m (EplusVecField L α (s - m) x) from rfl,
        EplusVecField_nonpos L α (by omega),
        show (-(s - m)).toNat = (m - s).toNat by ring,
        hgrade, map_zero] at hm
      exact hm rfl
    exact Finset.mem_Icc.mpr ⟨by omega, hmws⟩
  rw [show (fun m : ℤ => EminusVecField L α m (EplusVecField L α (s - m) x)) = f from rfl,
    finsum_eq_sum_of_support_subset f hsupp]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
  have hm0 : 0 ≤ m := le_trans (le_max_left 0 s) hmlo
  have hsm : s ≤ m := le_trans (le_max_right 0 s) hmlo
  rw [show f m = EminusVecField L α m (EplusVecField L α (s - m) x) from rfl,
    EminusVecField_apply, if_pos hm0, EplusVecField_nonpos L α (by omega),
    show (-(s - m)).toNat = (m - s).toNat by ring,
    EminusVec, LinearMap.mulLeft_apply]

/-! ## The exact finite monomial basis of a bosonic weight space -/

/-- The weighted monomial indexed by `d`, regarded as an element of the weight-`w` subspace. -/
noncomputable def weightMonomialN (r w : ℕ) (d : weightDegSetN r w) : gradingWN r w :=
  ⟨MvPolynomial.monomial d.1 (1 : ℂ),
    MvPolynomial.isWeightedHomogeneous_monomial weightFnN d.1 (1 : ℂ) d.2⟩

@[simp] theorem weightMonomialN_val (r w : ℕ) (d : weightDegSetN r w) :
    ((weightMonomialN r w d : gradingWN r w) : FockN r) =
      MvPolynomial.monomial d.1 (1 : ℂ) := rfl

/-- Distinct weighted exponent vectors give linearly independent monomials inside the graded
subspace. -/
theorem weightMonomialN_linearIndependent (r w : ℕ) :
    LinearIndependent ℂ (weightMonomialN r w) := by
  refine LinearIndependent.of_comp (gradingWN r w).subtype ?_
  simpa only [Function.comp_apply, weightMonomialN_val, MvPolynomial.coe_basisMonomials] using
    (MvPolynomial.basisMonomials (ℕ × Fin r) ℂ).linearIndependent.comp
      (fun d : weightDegSetN r w => d.1) Subtype.val_injective

/-- The weighted monomials span the whole graded Fock subspace. -/
theorem weightMonomialN_span (r w : ℕ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (weightMonomialN r w)) := by
  have hinj : Function.Injective (gradingWN r w).subtype := Subtype.val_injective
  have hrange : Set.range (fun d : weightDegSetN r w =>
      (MvPolynomial.monomial d.1 (1 : ℂ) : FockN r)) = weightMonSetN r w := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d.1, d.2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  have hmap : Submodule.map (gradingWN r w).subtype
        (Submodule.span ℂ (Set.range (weightMonomialN r w)))
      = Submodule.map (gradingWN r w).subtype ⊤ := by
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    change Submodule.span ℂ (Set.range (fun d : weightDegSetN r w =>
      (MvPolynomial.monomial d.1 (1 : ℂ) : FockN r))) = gradingWN r w
    rw [hrange]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨d, hd, rfl⟩
      exact MvPolynomial.isWeightedHomogeneous_monomial weightFnN d (1 : ℂ) hd
    · exact gradingWN_le_span r w
  have := Submodule.map_injective_of_injective hinj hmap
  rw [this]

/-- The weighted-exponent index set has an explicit finite type, from the existing box injection. -/
noncomputable instance weightDegSetNFintype (r w : ℕ) : Fintype (weightDegSetN r w) :=
  (weightDegSetN_finite r w).fintype

/-- The manifest monomial basis of the rank-`r` bosonic Fock space at weight `w`.  The index type
is finite by `weightDegSetN_finite`; no PBW principle is used. -/
noncomputable def weightMonomialBasisN (r w : ℕ) :
    Module.Basis (weightDegSetN r w) ℂ (gradingWN r w) :=
  Module.Basis.mk (weightMonomialN_linearIndependent r w) (weightMonomialN_span r w)

@[simp] theorem weightMonomialBasisN_apply (r w : ℕ) (d : weightDegSetN r w) :
    weightMonomialBasisN r w d = weightMonomialN r w d := Module.Basis.mk_apply _ _ d

/-- The exact graded dimension is the cardinality of the finite weighted-exponent set. -/
theorem finrank_gradingWN_eq_weightDegSetN (r w : ℕ) :
    Module.finrank ℂ (gradingWN r w) = Fintype.card (weightDegSetN r w) :=
  Module.finrank_eq_card_basis (weightMonomialBasisN r w)

/-! ## Transport to an exact lattice charge sector -/

/-- Tensoring with the charge vector `e^α` identifies a bosonic weight space with its lattice
bigraded sector.  The inverse is the existing charge-coordinate extractor `coordEα`. -/
noncomputable def gradeToBigradEquiv (L : IntegralLattice) (w : ℕ) (α : L.carrier) :
    gradingWN (rank L) w ≃ₗ[ℂ] bigradα L ((w : ℤ), α) where
  toFun x := ⟨mkEα L α x.1, ⟨x.1, mem_gradingZN_of_gradingWN x.2, rfl⟩⟩
  invFun y := ⟨coordEα L α y.1, by
    obtain ⟨p, hp, hpy⟩ := y.2
    rw [← hpy, mkEα_apply, coordEα_apply, if_pos rfl]
    rwa [gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hp⟩
  left_inv x := by
    apply Subtype.ext
    change coordEα L α (mkEα L α x.1) = x.1
    rw [mkEα_apply, coordEα_apply, if_pos rfl]
  right_inv y := by
    apply Subtype.ext
    obtain ⟨p, hp, hpy⟩ := y.2
    change mkEα L α (coordEα L α y.1) = y.1
    have hcoord : coordEα L α (mkEα L α p) = p := by
      rw [mkEα_apply, coordEα_apply, if_pos rfl]
    rw [← hpy, hcoord]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (mkEα L α) x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (mkEα L α) c x.1

/-- The exact finite monomial basis of a lattice sector with fixed charge and boson weight. -/
noncomputable def bigradMonomialBasis (L : IntegralLattice) (w : ℕ) (α : L.carrier) :
    Module.Basis (weightDegSetN (rank L) w) ℂ (bigradα L ((w : ℤ), α)) :=
  (weightMonomialBasisN (rank L) w).map (gradeToBigradEquiv L w α)

/-- Coordinates in the transported monomial basis. -/
noncomputable def bigradMonomialCoord (L : IntegralLattice) (w : ℕ) (α : L.carrier)
    (d : weightDegSetN (rank L) w) : bigradα L ((w : ℤ), α) →ₗ[ℂ] ℂ :=
  Finsupp.lapply d ∘ₗ (bigradMonomialBasis L w α).repr.toLinearMap

/-- Equality in a fixed lattice sector is exactly equality of all weighted-monomial
coordinates. -/
theorem bigrad_ext (L : IntegralLattice) (w : ℕ) (α : L.carrier)
    {x y : bigradα L ((w : ℤ), α)}
    (h : ∀ d : weightDegSetN (rank L) w,
      bigradMonomialCoord L w α d x = bigradMonomialCoord L w α d y) : x = y := by
  apply (bigradMonomialBasis L w α).repr.injective
  apply Finsupp.ext
  intro d
  exact h d

/-! ### The `p = 2`, charge-zero, weight-ten sector -/

/-- The exact finite coordinate sector containing every term of the `p = 2` Adamovic--Milas
identity. -/
abbrev ChargeZeroWeightTen : Type := bigradα (latP 2) ((10 : ℤ), (0 : (latP 2).carrier))

/-- Its manifest monomial basis, indexed exactly by the weighted exponent vectors of weight ten.
In rank one this index set has the mathematical cardinality `42` (the number of partitions of
`10`); no equivalence with `Fin 42` or numeral `finrank` theorem is asserted here. -/
noncomputable def chargeZeroWeightTenBasis :
    Module.Basis (weightDegSetN (rank (latP 2)) 10) ℂ ChargeZeroWeightTen :=
  bigradMonomialBasis (latP 2) 10 0

/-- A coordinate functional on the charge-zero weight-ten sector. -/
noncomputable def chargeZeroWeightTenCoord (d : weightDegSetN (rank (latP 2)) 10) :
    ChargeZeroWeightTen →ₗ[ℂ] ℂ := bigradMonomialCoord (latP 2) 10 0 d

/-- The finite coordinate-separation theorem consumed by the `p = 2` AM computation. -/
theorem chargeZeroWeightTen_ext {x y : ChargeZeroWeightTen}
    (h : ∀ d : weightDegSetN (rank (latP 2)) 10,
      chargeZeroWeightTenCoord d x = chargeZeroWeightTenCoord d y) : x = y :=
  bigrad_ext (latP 2) 10 0 h

/-! ## A detector endpoint for the Adamovic--Milas coefficient -/

/-- The finite-coordinate calculation before proving the distinguished coefficient nonzero: the
screened charge state is in the span of the `H_{-5}H` line, the `L_{-2}^5` line, and `VirDeep`. -/
def AMLinearDecompositionTwo (hp : 1 ≤ 2) : Prop :=
  ∃ A B : ℂ, ∃ z ∈ VirDeep 2 hp,
    Qwp 2 hp (Qwp 2 hp
      (latChargeGen (latP 2) (-alphaP 2 + -alphaP 2))) =
        A • (tripletLatticeVOA 2 hp).smul (Htrip 2) (-5) (Htrip 2)
          + B • omegaPowAmb 2 hp 5 + z

/-- A linear functional separating the screened charge state from `VirDeep` and the
`H_{-5}H` line.  Such a detector proves that the coefficient of `L_{-2}^5` in any finite
decomposition is nonzero; it need not be normalized. -/
structure AMDetectorTwo (hp : 1 ≤ 2) where
  eval : LatModuleGen (latP 2) →ₗ[ℂ] ℂ
  virDeep_le_ker : VirDeep 2 hp ≤ LinearMap.ker eval
  eval_H : eval ((tripletLatticeVOA 2 hp).smul (Htrip 2) (-5) (Htrip 2)) = 0
  eval_screened_ne_zero :
    eval (Qwp 2 hp (Qwp 2 hp
      (latChargeGen (latP 2) (-alphaP 2 + -alphaP 2)))) ≠ 0

/-- The exact finite-linear-algebra endpoint for the AM residual.  A coordinate expansion gives
`AMLinearDecompositionTwo`; one separating row of the same coordinate matrix gives
`AMDetectorTwo`.  Together they imply the full identity with a nonzero `L_{-2}^5` coefficient. -/
theorem amOmegaIdentity_two_of_decomposition_detector (hp : 1 ≤ 2)
    (hdec : AMLinearDecompositionTwo hp) (D : AMDetectorTwo hp) :
    AMOmegaIdentity 2 hp 5 := by
  obtain ⟨A, B, z, hz, heq⟩ := hdec
  refine ⟨A, B, ?_, z, hz, ?_⟩
  · intro hB
    apply D.eval_screened_ne_zero
    have hz0 : D.eval z = 0 := D.virDeep_le_ker hz
    rw [heq, map_add, map_add, map_smul, map_smul, D.eval_H, hB, zero_smul,
      smul_zero, zero_add, hz0]
    simp
  · convert heq using 1 <;> norm_num

end VOA.LatGen.WpTwoSector
