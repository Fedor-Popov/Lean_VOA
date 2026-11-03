/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaNonvanishing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor Fock families with fixed highest weight

A pair of background-free bosons at momenta z and iz has central charge two
and highest weight zero for every z. Tensoring this pair with a charged Fock
realization of (c-2,h) gives a polynomial family of representations of the
SAME Verma module M(c,h). Negative modes depend linearly on z. This supplies
a route to Verma independence without specializing a singular-vector formula.
This file constructs the family; it does not assert its faithfulness.
-/
namespace VOA.InverseDS.VirasoroVerma
open Module (End)
open scoped TensorProduct
open VirModule VirDeformModes LeeYangWardClosure
open LeeYangFockExponential LeeYangFockVirasoro
open LieAlgebra LieAlgebra.Extension

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Two actions on different tensor factors commute. This is the cancellation
which prevents cross terms from altering the Virasoro commutator. -/
theorem tensor_factors_commute (a : End ℂ V) (b : End ℂ W) :
    Commute (a.rTensor W) (b.lTensor V) := by
  show (a.rTensor W).comp (b.lTensor V) = (b.lTensor V).comp (a.rTensor W)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- On a tensor product, each mode is the sum of its two factor actions.
The central charges add because the mixed commutators vanish. -/
noncomputable def tensorVirasoroData (A : CentralVirasoroData V)
    (B : CentralVirasoroData W) : CentralVirasoroData (V ⊗[ℂ] W) where
  L n := (A.L n).rTensor W + (B.L n).lTensor V
  central := A.central.rTensor W + B.central.lTensor V
  comm m n := by
    let F := End.rTensorAlgHom ℂ V W
    let G := End.lTensorAlgHom ℂ W V
    have ha := congrArg F (A.comm m n)
    have hb := congrArg G (B.comm m n)
    simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul, map_add,
      map_smul] at ha hb
    change (F (A.L m)+G (B.L m))*(F (A.L n)+G (B.L n)) -
      (F (A.L n)+G (B.L n))*(F (A.L m)+G (B.L m)) = _
    have h1 := (tensor_factors_commute (A.L m) (B.L n)).eq
    have h2 := (tensor_factors_commute (A.L n) (B.L m)).eq
    change F (A.L m)*G (B.L n)=G (B.L n)*F (A.L m) at h1
    change F (A.L n)*G (B.L m)=G (B.L m)*F (A.L n) at h2
    have he : (F (A.L m)+G (B.L m))*(F (A.L n)+G (B.L n)) -
        (F (A.L n)+G (B.L n))*(F (A.L m)+G (B.L m)) =
        (F (A.L m)*F (A.L n)-F (A.L n)*F (A.L m)) +
        (G (B.L m)*G (B.L n)-G (B.L n)*G (B.L m)) := by
      simp only [add_mul,mul_add]
      rw [h1,h2]
      abel
    rw [he]
    by_cases hh : m+n=0
    · simp only [if_pos hh, map_smul] at ha hb
      simp only [if_pos hh, smul_add]
      rw [ha,hb]
      dsimp [F,G,End.rTensorAlgHom,End.lTensorAlgHom]
      module
    · simp only [if_neg hh, map_zero, add_zero] at ha hb
      simp only [if_neg hh, add_zero, smul_add]
      rw [ha,hb]
      rfl
  central_comm n := by
    exact ((A.central_comm n).map (End.rTensorAlgHom ℂ V W)).add_right
      (tensor_factors_commute A.central (B.L n)) |>.add_left
      ((tensor_factors_commute (A.L n) B.central).symm.add_right
        ((B.central_comm n).map (End.lTensorAlgHom ℂ W V)))

/-- Scalar central actions on the factors combine to their sum on the tensor
product. This is an equality of actual endomorphisms. -/
theorem tensorVirasoroData_central (A : CentralVirasoroData V)
    (B : CentralVirasoroData W) (a b : ℂ)
    (ha : A.central=a • 1) (hb : B.central=b • 1) :
    (tensorVirasoroData A B).central=(a+b) • 1 := by
  change End.rTensorAlgHom ℂ V W A.central + End.lTensorAlgHom ℂ W V B.central = _
  rw [ha,hb,map_smul,map_smul,map_one,map_one,add_smul]

/-- Tensoring two scalar-charge mode systems gives a full Virasoro
representation at the sum charge. -/
noncomputable def tensorVirasoroRep (A : CentralVirasoroData V)
    (B : CentralVirasoroData W) (a b : ℂ)
    (ha : A.central=a • 1) (hb : B.central=b • 1) : VirRep (V ⊗[ℂ] W) where
  ρ := fixedRho (tensorVirasoroData A B) (tensorVirasoroData_central A B a b ha hb)
  centralCharge := a+b
  acts_central := fixedRho_C _ _

/-- A tensor mode acts by the Leibniz sum on a pure tensor. -/
theorem tensorVirasoroRep_mode (A : CentralVirasoroData V)
    (B : CentralVirasoroData W) (a b : ℂ)
    (ha : A.central=a • 1) (hb : B.central=b • 1) (n : ℤ) (v : V) (w : W) :
    virMode (tensorVirasoroRep A B a b ha hb) n (v ⊗ₜ[ℂ] w) =
      A.L n v ⊗ₜ[ℂ] w + v ⊗ₜ[ℂ] B.L n w := by
  rw [show virMode (tensorVirasoroRep A B a b ha hb) n =
    (tensorVirasoroData A B).L n from fixedRho_L _ (tensorVirasoroData_central A B a b ha hb) n]
  simp [tensorVirasoroData]

/-- The two-boson carrier used to vary momentum while keeping the total
highest weight zero. The two tensor factors remain independent oscillators. -/
abbrev IsotropicFock := LeeYangFock ⊗[ℂ] LeeYangFock

/-- Background-free bosons at momenta z and iz form an isotropic pair:
their vacuum weights cancel, while their central charges add to two. -/
noncomputable def isotropicFockData (z : ℂ) : CentralVirasoroData IsotropicFock :=
  tensorVirasoroData (chargedFockData 0 z) (chargedFockData 0 (Complex.I*z))

/-- The pair has central charge two, independently of its free momentum. -/
theorem isotropicFock_central (z : ℂ) :
    (isotropicFockData z).central=(2:ℂ) • (1 : End ℂ IsotropicFock) := by
  convert tensorVirasoroData_central (chargedFockData 0 z)
    (chargedFockData 0 (Complex.I*z)) 1 1 (by simp [chargedFockData])
      (by simp [chargedFockData]) using 1 <;> norm_num

/-- The tensor of the two polynomial vacua is the pair's highest vector. -/
noncomputable def isotropicVacuum : IsotropicFock :=
  HeisenbergN.vacuumN 1 ⊗ₜ[ℂ] HeisenbergN.vacuumN 1

/-- Both summands of a positive pair mode kill the tensor vacuum. -/
theorem isotropicFock_positive (z : ℂ) (n : ℤ) (hn : 0<n) :
    (isotropicFockData z).L n isotropicVacuum=0 := by
  simp only [isotropicFockData,tensorVirasoroData,chargedFockData,isotropicVacuum,
    LinearMap.add_apply,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul]
  rw [chargedFock_positive_vacuum 0 z n hn,
    chargedFock_positive_vacuum 0 (Complex.I*z) n hn]
  simp

/-- The momentum squares z² and (iz)² cancel exactly. Thus the free
parameter changes no highest-weight equation. -/
theorem isotropicFock_zero (z : ℂ) :
    (isotropicFockData z).L 0 isotropicVacuum=0 := by
  simp only [isotropicFockData,tensorVirasoroData,chargedFockData,isotropicVacuum,
    LinearMap.add_apply,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul]
  rw [chargedFock_zero_vacuum,chargedFock_zero_vacuum]
  simp only [mul_zero,zero_mul,sub_zero,TensorProduct.smul_tmul,TensorProduct.tmul_smul,
    ← add_smul]
  have hh : z^2+(Complex.I*z)^2=0 := by rw [mul_pow,Complex.I_sq]; ring
  rw [hh,zero_smul]

/-- Three bosons: an isotropic pair followed by one fixed charged sector.
The latter supplies the desired central charge and highest weight. -/
abbrev VermaFockFamily := IsotropicFock ⊗[ℂ] LeeYangFock

/-- The actual variable-momentum Virasoro modes on the three-boson carrier. -/
noncomputable def vermaFockFamilyData (ell p z : ℂ) :
    CentralVirasoroData VermaFockFamily :=
  tensorVirasoroData (isotropicFockData z) (chargedFockData ell p)

/-- The family central charge does not depend on z. -/
theorem vermaFockFamily_central (ell p z : ℂ) :
    (vermaFockFamilyData ell p z).central=(3-24*ell^2) • 1 := by
  convert tensorVirasoroData_central (isotropicFockData z) (chargedFockData ell p)
    2 (1-24*ell^2) (isotropicFock_central z) rfl using 1 <;> congr 1 <;> ring

/-- The family is a full representation of Virasoro at one fixed charge,
for every value of its free momentum. -/
noncomputable def vermaFockFamilyRep (ell p z : ℂ) : VirRep VermaFockFamily where
  ρ := fixedRho (vermaFockFamilyData ell p z) (vermaFockFamily_central ell p z)
  centralCharge := 3-24*ell^2
  acts_central := fixedRho_C _ (vermaFockFamily_central ell p z)

/-- The full Lie action recovers the explicitly summed family modes. -/
theorem vermaFockFamilyRep_mode (ell p z : ℂ) (n : ℤ) :
    virMode (vermaFockFamilyRep ell p z) n=(vermaFockFamilyData ell p z).L n :=
  fixedRho_L _ (vermaFockFamily_central ell p z) n

/-- The threefold polynomial vacuum is constant throughout the family. -/
noncomputable def vermaFockFamilyVacuum : VermaFockFamily :=
  isotropicVacuum ⊗ₜ[ℂ] HeisenbergN.vacuumN 1

/-- All family members have the same highest-weight vector, of weight
p²-2 ell p. No free-momentum specialization or denominator is required. -/
theorem vermaFockFamily_isHighest (ell p z : ℂ) :
    IsHighestWeightVector (vermaFockFamilyRep ell p z) vermaFockFamilyVacuum
      (3-24*ell^2) (p^2-2*ell*p) where
  centralCharge := rfl
  pos_annihilate n hn := by
    rw [vermaFockFamilyRep_mode]
    simp only [vermaFockFamilyData,tensorVirasoroData,vermaFockFamilyVacuum,
      LinearMap.add_apply,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul,
      chargedFockData]
    rw [isotropicFock_positive z n hn,chargedFock_positive_vacuum ell p n hn]
    simp
  zero_acts := by
    rw [vermaFockFamilyRep_mode]
    simp only [vermaFockFamilyData,tensorVirasoroData,vermaFockFamilyVacuum,
      LinearMap.add_apply,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul,
      chargedFockData]
    rw [isotropicFock_zero,chargedFock_zero_vacuum]
    simp

/-- Every prescribed pair (c,h) is realized by the fixed sector of an entire
free-momentum family, not just by an isolated Fock representation. -/
theorem exists_vermaFockFamily_parameters (c h : ℂ) :
    ∃ ell p : ℂ, 3-24*ell^2=c ∧ p^2-2*ell*p=h := by
  obtain ⟨ell,p,hc,hh⟩ := exists_chargedFock_parameters (c-2) h
  exact ⟨ell,p,by linear_combination hc,hh⟩

/-- Universal evaluation into each family member starts from the same
Verma module. Injectivity or separation of these maps is a further theorem. -/
noncomputable def vermaFockFamilyMap (ell p z : ℂ) :
    Verma (3-24*ell^2) (p^2-2*ell*p) →ₗ[ℂ] VermaFockFamily :=
  universalMap _ _ (vermaFockFamily_isHighest ell p z)

/-- Evaluation sends the formal highest vector to the fixed tensor vacuum. -/
theorem vermaFockFamilyMap_highest (ell p z : ℂ) :
    vermaFockFamilyMap ell p z (highestVector (3-24*ell^2) (p^2-2*ell*p)) =
      vermaFockFamilyVacuum := universalMap_highestVector _ _ _

/-- For a negative mode, background-free charged action depends linearly
on the momentum; the zero-mode square term is absent. -/
theorem sectorVirasoro_negative_linear (z : ℂ) (i : ℕ) :
    sectorVirasoro 0 z (-(i:ℤ)-1)=sectorVirasoro 0 0 (-(i:ℤ)-1) +
      z • alphaMode (-(i:ℤ)-1) := by
  simp [sectorVirasoro,sectorSugawara,sectorBackgroundCurrent,
    show -(i:ℤ)-1 ≠ 0 by omega]

/-- The coefficient of the free momentum in a negative family mode. It
creates an oscillator in the first factor plus i times one in the second. -/
noncomputable def vermaMomentumMode (i : ℕ) : End ℂ VermaFockFamily :=
  ((alphaMode (-(i:ℤ)-1)).rTensor LeeYangFock +
    Complex.I • (alphaMode (-(i:ℤ)-1)).lTensor LeeYangFock).rTensor LeeYangFock

/-- Every negative mode in the actual fixed-weight family is affine linear
in z. This includes L₋₁, which the vacuum-module basis argument omits. -/
theorem vermaFockFamily_negative_linear (ell p z : ℂ) (i : ℕ) :
    (vermaFockFamilyData ell p z).L (-(i:ℤ)-1) =
      (vermaFockFamilyData ell p 0).L (-(i:ℤ)-1) + z • vermaMomentumMode i := by
  simp only [vermaFockFamilyData,tensorVirasoroData,isotropicFockData,chargedFockData]
  rw [sectorVirasoro_negative_linear z,sectorVirasoro_negative_linear (Complex.I*z)]
  simp only [mul_zero]
  simp only [vermaMomentumMode,LinearMap.rTensor_add,LinearMap.lTensor_add,
    LinearMap.rTensor_smul,LinearMap.lTensor_smul]
  module

/-- Remove a polynomial tensor factor by taking its constant coefficient.
This is a linear projection, not a Virasoro intertwiner. -/
noncomputable def fockConstantProjection (V : Type*) [AddCommGroup V] [Module ℂ V] :
    V ⊗[ℂ] LeeYangFock →ₗ[ℂ] V :=
  (TensorProduct.rid ℂ V).toLinearMap.comp
    (TensorProduct.map LinearMap.id (MvPolynomial.lcoeff ℂ 0))

/-- On pure tensors, removing the Fock factor multiplies by its constant term. -/
theorem fockConstantProjection_tmul (v : V) (f : LeeYangFock) :
    fockConstantProjection V (v ⊗ₜ[ℂ] f)=MvPolynomial.coeff 0 f • v := by
  simp [fockConstantProjection]

/-- Remove the second and third bosons, retaining the first oscillator ring. -/
noncomputable def vermaSymbolProjection : VermaFockFamily →ₗ[ℂ] LeeYangFock :=
  (fockConstantProjection LeeYangFock).comp (fockConstantProjection IsotropicFock)

/-- The symbol projection of the fixed tensor vacuum is the scalar one. -/
theorem vermaSymbolProjection_vacuum :
    vermaSymbolProjection vermaFockFamilyVacuum=1 := by
  simp [vermaSymbolProjection,vermaFockFamilyVacuum,isotropicVacuum,
    fockConstantProjection_tmul,HeisenbergN.vacuumN]

/-- The tensor vacuum is nonzero, since its projection is the constant one. -/
theorem vermaFockFamilyVacuum_ne_zero : vermaFockFamilyVacuum ≠ 0 := by
  intro hz
  have hh := vermaSymbolProjection_vacuum
  rw [hz,map_zero] at hh
  exact zero_ne_one hh

/-- Negative current modes create one oscillator variable in the polynomial
carrier, including the first variable for mode minus one. -/
theorem alphaMode_negative_apply (i : ℕ) (v : LeeYangFock) :
    alphaMode (-(i:ℤ)-1) v=MvPolynomial.X (i,(0:Fin 1))*v := by
  rw [alphaMode,HeisenbergN.oscN_apply_neg 1 2 0 (by omega)]
  have hh : (-(-(i:ℤ)-1)-1).toNat=i := by omega
  rw [hh]

/-- Projecting a momentum coefficient discards the second-boson creation
term and leaves multiplication by the first-boson variable. This is the
leading-symbol separation mechanism for all Verma creation modes. -/
theorem vermaSymbolProjection_momentum (i : ℕ) (v : VermaFockFamily) :
    vermaSymbolProjection (vermaMomentumMode i v)=
      MvPolynomial.X (i,(0:Fin 1))*vermaSymbolProjection v := by
  suffices he : vermaSymbolProjection.comp (vermaMomentumMode i) =
      (HeisenbergN.mulXN i 0).comp vermaSymbolProjection by
    exact LinearMap.congr_fun he v
  apply TensorProduct.ext'
  intro ab d
  induction ab using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [vermaMomentumMode,vermaSymbolProjection,fockConstantProjection_tmul,
      alphaMode_negative_apply,HeisenbergN.mulXN_apply,
      ← MvPolynomial.constantCoeff_eq,smul_eq_mul]
  | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,mul_add] at *; rw [ha,hb]

end VOA.InverseDS.VirasoroVerma
