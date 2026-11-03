/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaGram

/-!
# Actual finite joint eigenspaces of the affine Verma module

Fixing energy alone leaves infinitely many horizontal lowering powers.
Fixing energy and Cartan charge together gives exactly the finite occupation
index already used by the actual Gram matrix, at every pair of parameters.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Wak.Charged (Occupation JointIndex occupationWord occupationEnergy occupationCharge)
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := Wak.Charged.jointIndexFintype n c

/-- Actual energy of an occupation basis state, under D=-energy. -/
theorem degree_basis (k h : ℂ) (d : Occupation) :
    rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) (occupationBasis k h d)=
      (-(occupationEnergy d : ℂ)) • occupationBasis k h d := by
  rw [occupationBasis_apply,degree_word,Wak.Charged.occupationWord_energy,Int.cast_natCast]

/-- Actual Cartan eigenvalue of each occupation basis state. -/
theorem cartan_basis (k h : ℂ) (d : Occupation) :
    mode k h 2 0 (occupationBasis k h d)=
      (h+2*(occupationCharge d : ℂ)) • occupationBasis k h d := by
  rw [occupationBasis_apply,cartan_word,Wak.Charged.occupationWord_charge]

/-- A diagonal operator has the corresponding diagonal action on every
coordinate, not just on individual basis vectors. -/
private theorem basis_coordinate_diagonal (k h : ℂ) (T : End ℂ (Verma k h))
    (z : Occupation→ℂ) (hz : ∀ d,T (occupationBasis k h d)=z d • occupationBasis k h d)
    (v : Verma k h) (d : Occupation) :
    (occupationBasis k h).repr (T v) d=z d*(occupationBasis k h).repr v d := by
  let C : Verma k h→ₗ[ℂ]ℂ := (Finsupp.lapply d).comp (occupationBasis k h).repr.toLinearMap
  have he : C.comp T=z d • C := by
    apply (occupationBasis k h).ext
    intro e
    change (occupationBasis k h).repr (T (occupationBasis k h e)) d=
      z d*(occupationBasis k h).repr (occupationBasis k h e) d
    rw [hz,map_smul,Finsupp.smul_apply,Module.Basis.repr_self,smul_eq_mul]
    by_cases he : e=d
    · subst e; simp
    · simp [he,Ne.symm he]
  exact LinearMap.congr_fun he v

/-- Exact degree action on arbitrary occupation coordinates. -/
theorem degree_coordinate (k h : ℂ) (v : Verma k h) (d : Occupation) :
    (occupationBasis k h).repr (rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) v) d=
      (-(occupationEnergy d : ℂ))*(occupationBasis k h).repr v d :=
  basis_coordinate_diagonal k h _ _ (degree_basis k h) v d

/-- Exact Cartan action on arbitrary occupation coordinates. -/
theorem cartan_coordinate (k h : ℂ) (v : Verma k h) (d : Occupation) :
    (occupationBasis k h).repr (mode k h 2 0 v) d=
      (h+2*(occupationCharge d : ℂ))*(occupationBasis k h).repr v d :=
  basis_coordinate_diagonal k h _ _ (cartan_basis k h) v d

/-- The actual span at a fixed energy and root charge. -/
def jointSpace (k h : ℂ) (n : ℕ) (c : ℤ) : Submodule ℂ (Verma k h) :=
  Submodule.span ℂ (Set.range (fun d : JointIndex n c => occupationBasis k h d.val))

/-- Restricting the genuine PBW family to one joint index remains independent. -/
theorem jointWords_independent (k h : ℂ) (n : ℕ) (c : ℤ) :
    LinearIndependent ℂ (fun d : JointIndex n c => occupationBasis k h d.val) :=
  (occupationBasis k h).linearIndependent.comp _ Subtype.val_injective

/-- The finite basis of the actual joint Verma span. -/
def jointBasis (k h : ℂ) (n : ℕ) (c : ℤ) : Module.Basis (JointIndex n c) ℂ (jointSpace k h n c) :=
  Module.Basis.span (jointWords_independent k h n c)

/-- The joint basis is the same actual word family as the global basis. -/
theorem jointBasis_apply (k h : ℂ) (n : ℕ) (c : ℤ) (d : JointIndex n c) :
    (jointBasis k h n c d : Verma k h)=occupationBasis k h d.val :=
  Module.Basis.coe_span_apply _ d

/-- The actual joint dimension is exactly the finite occupation count;
this is not a dimension assertion for a simple quotient. -/
theorem jointSpace_finrank (k h : ℂ) (n : ℕ) (c : ℤ) :
    Module.finrank ℂ (jointSpace k h n c)=Fintype.card (JointIndex n c) :=
  Module.finrank_eq_card_basis (jointBasis k h n c)

/-- The finite joint word span equals the ACTUAL simultaneous degree and
Cartan eigenspace, at every level and highest weight. -/
theorem mem_jointSpace_iff (k h : ℂ) (n : ℕ) (c : ℤ) (v : Verma k h) :
    v∈jointSpace k h n c ↔
      rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant) v=(-(n : ℂ)) • v ∧
      mode k h 2 0 v=(h+2*(c : ℂ)) • v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨d,rfl⟩ := hv
        rw [degree_basis,cartan_basis,d.property.1,d.property.2]
        exact ⟨rfl,rfl⟩
    | zero => simp
    | add u v hu hv ihu ihv => simp only [map_add,ihu.1,ihv.1,ihu.2,ihv.2,smul_add,and_self]
    | smul z v hv ih => simp only [map_smul,ih.1,ih.2,smul_comm z,and_self]
  · rintro ⟨hd,hc⟩
    rw [← (occupationBasis k h).linearCombination_repr v]
    change (∑ d∈((occupationBasis k h).repr v).support,
      (occupationBasis k h).repr v d • occupationBasis k h d)∈_
    apply Submodule.sum_mem
    intro d hdmem
    have hd0 : (occupationBasis k h).repr v d≠0 := Finsupp.mem_support_iff.mp hdmem
    have hed := degree_coordinate k h v d
    have hec := cartan_coordinate k h v d
    rw [hd,map_smul,Finsupp.smul_apply,smul_eq_mul] at hed
    rw [hc,map_smul,Finsupp.smul_apply,smul_eq_mul] at hec
    have hde : occupationEnergy d=n := by
      have he := mul_right_cancel₀ hd0 hed
      have he' : (occupationEnergy d : ℂ)=(n : ℂ) := by linear_combination he
      exact_mod_cast he'
    have hdc : occupationCharge d=c := by
      have he := mul_right_cancel₀ hd0 hec
      have he' : (occupationCharge d : ℂ)=(c : ℂ) := by linear_combination -(1/2 : ℂ)*he
      exact_mod_cast he'
    exact (jointSpace k h n c).smul_mem _ (Submodule.subset_span ⟨⟨d,hde,hdc⟩,rfl⟩)

end
end VOA.AffineVOA.HighestModule
