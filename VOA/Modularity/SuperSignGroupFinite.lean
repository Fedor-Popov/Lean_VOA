/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSectorSystem

/-!
# Finiteness of the canonical super sign group

For a half-integrally graded super VOA, the conformal sign `kappa` and parity `sigma` commute
and square to one.  This file realizes the subgroup they generate as the image of the concrete
four-label type `Bool x Bool`:

`(a,b) |-> kappa^a sigma^b`.

The map is proved surjective, not injective.  Thus all degeneracies are retained: `kappa` or
`sigma` may be trivial, and they may coincide.  The resulting subgroup is a finite abelian group
whose exponent divides two and whose cardinality is at most four.  Equality with four is not
asserted.

Applying the parameterization independently to the spatial and temporal entries enumerates the
**outer** `SignBoundaryPair`s.  Their commutation follows from abelianness of the actual image
subgroup.  The enumeration has at most sixteen values, again without an injectivity or exact-card
claim.  These outer pairs are not the inner `SpinPair` eigenspace labels of `SuperSectorSystem`.

No spin--statistics relation is assumed.
-/

namespace VOA

open GammaThetaStmt

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {W : SuperVertexOperatorAlgebra VType}

/-! ## A concrete four-label parameterization -/

/-- Select either the identity or one group element according to one Boolean bit. -/
def signBit (g : SuperAut W) (b : Bool) : SuperAut W :=
  if b then g else 1

/-- The four-label word `kappa^a sigma^b`.  Distinct labels may have the same value. -/
noncomputable def superSignParam (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (z : Bool × Bool) : SuperAut W :=
  signBit (W.conformalSign hhalf) z.1 * signBit W.parityAut z.2

@[simp] theorem superSignParam_ff (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) : superSignParam W hhalf (false, false) = 1 := by
  simp [superSignParam, signBit]

@[simp] theorem superSignParam_tf (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    superSignParam W hhalf (true, false) = W.conformalSign hhalf := by
  simp [superSignParam, signBit]

@[simp] theorem superSignParam_ft (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    superSignParam W hhalf (false, true) = W.parityAut := by
  simp [superSignParam, signBit]

theorem signBit_commute_of_commute {g h : SuperAut W} (hgh : Commute g h)
    (a b : Bool) : Commute (signBit g a) (signBit h b) := by
  rcases a with (_ | _) <;> rcases b with (_ | _)
  · simp [signBit]
  · simp [signBit]
  · simp [signBit]
  · simpa [signBit] using hgh

theorem signBit_mul_of_mul_self {g : SuperAut W} (hg : g * g = 1)
    (a b : Bool) : signBit g a * signBit g b = signBit g (Bool.xor a b) := by
  rcases a with (_ | _) <;> rcases b with (_ | _) <;> simp [signBit, hg]

theorem signBit_mul_self_of_mul_self {g : SuperAut W} (hg : g * g = 1)
    (b : Bool) : signBit g b * signBit g b = 1 := by
  rcases b with (_ | _) <;> simp [signBit, hg]

/-- The range of the four-label word map is itself a subgroup. -/
noncomputable def superSignParamSubgroup (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) : Subgroup (SuperAut W) where
  carrier := Set.range (superSignParam W hhalf)
  one_mem' := ⟨(false, false), superSignParam_ff W hhalf⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, b⟩, rfl⟩ ⟨⟨c, d⟩, rfl⟩
    refine ⟨(Bool.xor a c, Bool.xor b d), ?_⟩
    have hk2 : W.conformalSign hhalf * W.conformalSign hhalf = 1 := by
      simpa [pow_two] using W.conformalSign_sq hhalf
    have hs2 : W.parityAut * W.parityAut = 1 := by
      simpa [pow_two] using W.parityAut_sq
    symm
    change signBit (W.conformalSign hhalf) a * signBit W.parityAut b *
        (signBit (W.conformalSign hhalf) c * signBit W.parityAut d) = _
    rw [(signBit_commute_of_commute
      (W.conformalSign_commute_parityAut hhalf).symm b c).mul_mul_mul_comm,
      signBit_mul_of_mul_self hk2, signBit_mul_of_mul_self hs2]
    rfl
  inv_mem' := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    refine ⟨(a, b), ?_⟩
    have hkInv : (W.conformalSign hhalf)⁻¹ = W.conformalSign hhalf :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using W.conformalSign_sq hhalf)
    have hsInv : W.parityAut⁻¹ = W.parityAut :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using W.parityAut_sq)
    have hcomm : W.parityAut * W.conformalSign hhalf =
        W.conformalSign hhalf * W.parityAut :=
      (W.conformalSign_commute_parityAut hhalf).eq.symm
    rcases a with (_ | _) <;> rcases b with (_ | _) <;>
      simp [superSignParam, signBit, hkInv, hsInv, hcomm]

/-- The concrete range subgroup is exactly the closure used in the sign-group construction. -/
theorem superSignParamSubgroup_eq (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    superSignParamSubgroup W hhalf = W.superSignSubgroup hhalf := by
  apply le_antisymm
  · rintro x ⟨⟨a, b⟩, rfl⟩
    rcases a with (_ | _) <;> rcases b with (_ | _)
    · exact (W.superSignSubgroup hhalf).one_mem
    · exact W.parityAut_mem_superSignSubgroup hhalf
    · exact W.conformalSign_mem_superSignSubgroup hhalf
    · exact (W.superSignSubgroup hhalf).mul_mem
        (W.conformalSign_mem_superSignSubgroup hhalf)
        (W.parityAut_mem_superSignSubgroup hhalf)
  · change Subgroup.closure
      ({W.conformalSign hhalf, W.parityAut} : Set (SuperAut W)) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with (rfl | hx)
    · exact ⟨(true, false), superSignParam_tf W hhalf⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨(false, true), superSignParam_ft W hhalf⟩

/-- The four-label map with codomain restricted to the generated subgroup. -/
noncomputable def superSignParamToSubgroup (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (z : Bool × Bool) : W.superSignSubgroup hhalf :=
  ⟨superSignParam W hhalf z, by
    rw [← superSignParamSubgroup_eq W hhalf]
    exact ⟨z, rfl⟩⟩

/-- Every element of the generated sign subgroup has one of the four Boolean labels. -/
theorem superSignParamToSubgroup_surjective (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    Function.Surjective (superSignParamToSubgroup W hhalf) := by
  rintro ⟨x, hx⟩
  rw [← superSignParamSubgroup_eq W hhalf] at hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z, rfl⟩

/-! ## Abelian exponent-two structure and finiteness -/

theorem superSignParam_commute (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (z w : Bool × Bool) :
    Commute (superSignParam W hhalf z) (superSignParam W hhalf w) := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  have hAC : Commute (signBit (W.conformalSign hhalf) a)
      (signBit (W.conformalSign hhalf) c) :=
    signBit_commute_of_commute (Commute.refl _) a c
  have hAD : Commute (signBit (W.conformalSign hhalf) a)
      (signBit W.parityAut d) :=
    signBit_commute_of_commute (W.conformalSign_commute_parityAut hhalf) a d
  have hBC : Commute (signBit W.parityAut b)
      (signBit (W.conformalSign hhalf) c) :=
    signBit_commute_of_commute (W.conformalSign_commute_parityAut hhalf).symm b c
  have hBD : Commute (signBit W.parityAut b) (signBit W.parityAut d) :=
    signBit_commute_of_commute (Commute.refl _) b d
  exact (hAC.mul_right hAD).mul_left (hBC.mul_right hBD)

/-- Any two actual elements of the sign subgroup commute. -/
theorem superSignSubgroup_commute (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (x y : W.superSignSubgroup hhalf) :
    Commute (x : SuperAut W) (y : SuperAut W) := by
  obtain ⟨z, rfl⟩ := superSignParamToSubgroup_surjective W hhalf x
  obtain ⟨w, rfl⟩ := superSignParamToSubgroup_surjective W hhalf y
  exact superSignParam_commute W hhalf z w

theorem superSignSubgroup_mul_comm (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (x y : W.superSignSubgroup hhalf) :
    x * y = y * x :=
  Subtype.ext (superSignSubgroup_commute W hhalf x y).eq

/-- The actual sign subgroup is abelian, including in every degenerate case. -/
noncomputable instance superSignSubgroupCommGroup
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    CommGroup (W.superSignSubgroup hhalf) :=
  { (inferInstance : Group (W.superSignSubgroup hhalf)) with
    mul_comm := superSignSubgroup_mul_comm W hhalf }

theorem superSignParam_sq (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (z : Bool × Bool) :
    superSignParam W hhalf z ^ 2 = 1 := by
  have hk2 : W.conformalSign hhalf * W.conformalSign hhalf = 1 := by
    simpa [pow_two] using W.conformalSign_sq hhalf
  have hs2 : W.parityAut * W.parityAut = 1 := by
    simpa [pow_two] using W.parityAut_sq
  rcases z with ⟨a, b⟩
  rw [pow_two, superSignParam]
  rw [(signBit_commute_of_commute
    (W.conformalSign_commute_parityAut hhalf).symm b a).mul_mul_mul_comm]
  rw [signBit_mul_self_of_mul_self hk2,
    signBit_mul_self_of_mul_self hs2, one_mul]

/-- Every element has square one.  This is the degeneration-safe exponent-two formulation. -/
theorem superSignSubgroup_sq (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (x : W.superSignSubgroup hhalf) : x ^ 2 = 1 := by
  obtain ⟨z, rfl⟩ := superSignParamToSubgroup_surjective W hhalf x
  apply Subtype.ext
  exact superSignParam_sq W hhalf z

/-- The group exponent divides two.  It can equal one when the subgroup is trivial. -/
theorem superSignSubgroup_exponent_dvd_two (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    Monoid.exponent (W.superSignSubgroup hhalf) ∣ 2 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one (superSignSubgroup_sq W hhalf)

/-- A concrete noncomputable `Fintype` obtained from the proved four-label surjection. -/
noncomputable instance superSignSubgroupFintype
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    Fintype (W.superSignSubgroup hhalf) := by
  classical
  exact Fintype.ofSurjective (superSignParamToSubgroup W hhalf)
    (superSignParamToSubgroup_surjective W hhalf)

/-- Degeneracy-safe cardinality bound for the actual sign subgroup. -/
theorem superSignSubgroup_card_le_four (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    Fintype.card (W.superSignSubgroup hhalf) ≤ 4 := by
  classical
  simpa using Fintype.card_le_of_surjective (superSignParamToSubgroup W hhalf)
    (superSignParamToSubgroup_surjective W hhalf)

/-! ## Enumeration of commuting outer boundary pairs -/

/-- Every ordered pair of actual sign-subgroup elements defines a commuting outer pair. -/
noncomputable def signBoundaryPairOfSubgroup
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (g h : W.superSignSubgroup hhalf) : SignBoundaryPair W hhalf where
  spatial := g
  temporal := h
  commute := superSignSubgroup_commute W hhalf g h
  spatial_mem := g.property
  temporal_mem := h.property

/-- The sixteen-label parameterization of outer sign-supported boundary pairs. -/
noncomputable def superSignBoundaryPairParam
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (z : (Bool × Bool) × (Bool × Bool)) : SignBoundaryPair W hhalf :=
  signBoundaryPairOfSubgroup W hhalf
    (superSignParamToSubgroup W hhalf z.1)
    (superSignParamToSubgroup W hhalf z.2)

/-- Every sign-supported outer boundary pair occurs in the sixteen-label enumeration. -/
theorem superSignBoundaryPairParam_surjective
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    Function.Surjective (superSignBoundaryPairParam W hhalf) := by
  intro b
  obtain ⟨z, hz⟩ := superSignParamToSubgroup_surjective W hhalf
    ⟨b.spatial, b.spatial_mem⟩
  obtain ⟨w, hw⟩ := superSignParamToSubgroup_surjective W hhalf
    ⟨b.temporal, b.temporal_mem⟩
  refine ⟨(z, w), ?_⟩
  apply SignBoundaryPair.ext
  apply BoundaryPair.ext
  · exact congrArg Subtype.val hz
  · exact congrArg Subtype.val hw

noncomputable instance signBoundaryPairFintype
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    Fintype (SignBoundaryPair W hhalf) := by
  classical
  exact Fintype.ofSurjective (superSignBoundaryPairParam W hhalf)
    (superSignBoundaryPairParam_surjective W hhalf)

/-- The ambient family of sign-supported commuting outer pairs has at most sixteen elements. -/
theorem signBoundaryPair_card_le_sixteen
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    Fintype.card (SignBoundaryPair W hhalf) ≤ 16 := by
  classical
  simpa using Fintype.card_le_of_surjective (superSignBoundaryPairParam W hhalf)
    (superSignBoundaryPairParam_surjective W hhalf)

/-- The image finset of all sixteen Boolean labels.  Duplicate values are collapsed rather than
ruled out. -/
noncomputable def superSignBoundaryPairEnumeration
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    Finset (SignBoundaryPair W hhalf) := by
  classical
  exact Finset.univ.image (superSignBoundaryPairParam W hhalf)

theorem mem_superSignBoundaryPairEnumeration
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (b : SignBoundaryPair W hhalf) :
    b ∈ superSignBoundaryPairEnumeration W hhalf := by
  classical
  obtain ⟨z, rfl⟩ := superSignBoundaryPairParam_surjective W hhalf b
  exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩

theorem superSignBoundaryPairEnumeration_card_le_sixteen
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    (superSignBoundaryPairEnumeration W hhalf).card ≤ 16 := by
  classical
  rw [superSignBoundaryPairEnumeration]
  calc
    (Finset.univ.image (superSignBoundaryPairParam W hhalf)).card ≤
        (Finset.univ : Finset ((Bool × Bool) × (Bool × Bool))).card :=
      Finset.card_image_le
    _ = 16 := by simp

end VOA
