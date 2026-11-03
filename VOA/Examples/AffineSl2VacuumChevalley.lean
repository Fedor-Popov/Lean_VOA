/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumJointSequence
import VOA.Examples.AffineSl2CurrentRealization

/-!
# The actual Chevalley involution on the affine vacuum module

The finite sl2 automorphism sends e to -f, f to -e and h to -h. Its
Killing-form-preserving affine action evaluates on the actual vacuum
quotient and gives an involution preserving energy and reversing charge.
This identifies the ordinary Verma convention with the VOA bilinear convention.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule AffineLie
open Module (End)
open NormalOrdering (currentWord)
noncomputable section

/-- The finite Chevalley involution with the signs required by the VOA
bilinear adjoint convention. It is complex linear. -/
def chevalleySl2 : Sl2→ₗ[ℂ]Sl2 where
  toFun x a := -x (adjointColour a)
  map_add' x y := by ext a; simp; abel
  map_smul' z x := by ext a; simp

/-- Each basis colour is sent to minus its opposite Chevalley colour. -/
theorem chevalleySl2_basis (a : Fin 3) : chevalleySl2 (basis a)=-basis (adjointColour a) := by
  ext b
  change -basis a (adjointColour b) = -basis (adjointColour a) b
  have he : adjointColour b=a ↔ b=adjointColour a := by
    constructor
    · intro h
      simpa only [adjointColour_involutive] using congrArg adjointColour h
    · intro h
      simpa only [adjointColour_involutive] using congrArg adjointColour h
  simp only [basis, Pi.single_apply, he]

/-- The finite map preserves the actual sl2 Lie bracket. -/
theorem chevalleySl2_lie (x y : Sl2) : chevalleySl2 ⁅x,y⁆=⁅chevalleySl2 x,chevalleySl2 y⁆ := by
  ext a
  fin_cases a <;> simp [chevalleySl2,bracket_apply,fabc,adjointColour,Fin.sum_univ_three] <;> ring

/-- It also preserves the normalized Killing form, hence the affine cocycle. -/
theorem chevalleySl2_kappa (x y : Sl2) : kappaForm (chevalleySl2 x) (chevalleySl2 y)=kappaForm x y := by
  simp [kappaForm_apply,chevalleySl2,kappa,adjointColour,Fin.sum_univ_three]
  ring

/-- Twist the actual vacuum loop action by the finite Chevalley involution. -/
def chevalleyLoop (k : ℂ) (n : ℤ) : Sl2→ₗ[ℂ]End ℂ (WakModule k) :=
  (vacuumRho kappaForm kappaForm_isInvariant k).toLinearMap.comp
    ((ofLoopₗ kappaForm kappaForm_isInvariant n).comp chevalleySl2)

/-- Twisted loops satisfy the full actual affine bracket at the original level. -/
theorem chevalleyLoop_comm (k : ℂ) (x y : Sl2) (m n : ℤ) :
    ⁅chevalleyLoop k m x,chevalleyLoop k n y⁆=
      chevalleyLoop k (m+n) ⁅x,y⁆+
        if m+n=0 then ((m : ℂ)*kappaForm x y) • (k • (1 : End ℂ (WakModule k))) else 0 := by
  change ⁅vacuumRho kappaForm kappaForm_isInvariant k
    (ofLoop kappaForm kappaForm_isInvariant (chevalleySl2 x) m),
    vacuumRho kappaForm kappaForm_isInvariant k
    (ofLoop kappaForm kappaForm_isInvariant (chevalleySl2 y) n)⁆=_
  rw [← (vacuumRho kappaForm kappaForm_isInvariant k).map_lie,affine_bracket,map_add,
    ← chevalleySl2_lie,chevalleySl2_kappa]
  congr 1
  split_ifs <;> simp only [map_smul,vacuum_acts_central,map_zero] <;> rfl

/-- The same affine degree differentiates the twisted loops at their actual index. -/
theorem chevalleyLoop_degree (k : ℂ) (x : Sl2) (n : ℤ) :
    ⁅vacuumRho kappaForm kappaForm_isInvariant k (ell0 kappaForm kappaForm_isInvariant),
      chevalleyLoop k n x⁆=(n : ℂ) • chevalleyLoop k n x := by
  change ⁅vacuumRho kappaForm kappaForm_isInvariant k _,vacuumRho kappaForm kappaForm_isInvariant k _⁆=_
  rw [← (vacuumRho kappaForm kappaForm_isInvariant k).map_lie]
  change vacuumRho kappaForm kappaForm_isInvariant k
    ⁅ell0 kappaForm kappaForm_isInvariant,ofLoop kappaForm kappaForm_isInvariant (chevalleySl2 x) n⁆=_
  rw [ell0_lie_ofLoop,map_smul]
  rfl

/-- Genuine vacuum current data for the twisted action, with no representation premise. -/
def chevalleyCurrentData (k : ℂ) : AffineCurrentData k (WakModule k) where
  loopMode := chevalleyLoop k
  degree := vacuumRho kappaForm kappaForm_isInvariant k (ell0 kappaForm kappaForm_isInvariant)
  vacuum := vacuumVector kappaForm kappaForm_isInvariant k
  loop_comm := chevalleyLoop_comm k
  degree_comm := chevalleyLoop_degree k
  pos_annihilate x n hn := vacuum_pos_annihilate _ _ _ _ _ hn
  degree_vacuum := vacuum_ell0_annihilate _ _ _

/-- The actual linear Chevalley map on the universal affine vacuum quotient. -/
def vacuumChevalley (k : ℂ) : WakModule k→ₗ[ℂ]WakModule k :=
  (chevalleyCurrentData k).toVacuumCurrentRealization.eval

/-- The actual map fixes the vacuum with coefficient one. -/
theorem vacuumChevalley_vacuum (k : ℂ) : vacuumChevalley k (vacuumA k)=vacuumA k :=
  VacuumCurrentRealization.eval_vacuum _

/-- Each actual current is intertwined with minus its opposite colour,
with its original integer index unchanged. -/
theorem vacuumChevalley_current (k : ℂ) (a : Fin 3) (n : ℤ) (v : WakModule k) :
    vacuumChevalley k (J k a n v)=-J k (adjointColour a) n (vacuumChevalley k v) := by
  rw [vacuumChevalley,VacuumCurrentRealization.eval_J,
    AffineCurrentData.toVacuumCurrentRealization_current]
  change chevalleyLoop k n (basis a) _=_
  simp only [chevalleyLoop,LinearMap.comp_apply,chevalleySl2_basis,map_neg]
  rfl

/-- The Chevalley map commutes with the actual degree operator. -/
theorem vacuumChevalley_degree (k : ℂ) (v : WakModule k) :
    vacuumChevalley k (ell0OpA k v)=ell0OpA k (vacuumChevalley k v) := by
  change vacuumChevalley k (vacuumRho kappaForm kappaForm_isInvariant k
    (ell0 kappaForm kappaForm_isInvariant) v)=_
  rw [vacuumChevalley,VacuumCurrentRealization.eval_action]
  change (chevalleyCurrentData k).rho (ell0 kappaForm kappaForm_isInvariant) _=_
  rw [AffineCurrentData.rho_ell0]
  rfl

/-- Applying the actual map twice restores every vacuum word, hence every
state of the universal module at a noncritical level. -/
theorem vacuumChevalley_involutive (k : ℂ) (hk : k+2≠0) : Function.Involutive (vacuumChevalley k) := by
  have hw : ∀w : List (Fin 3×ℕ),vacuumChevalley k (vacuumChevalley k (wordStateA k w))=wordStateA k w := by
    intro w
    induction w with
    | nil => rw [wordStateA_nil,vacuumChevalley_vacuum,vacuumChevalley_vacuum]
    | cons an w ih =>
      rw [wordStateA_cons,vacuumChevalley_current,map_neg,vacuumChevalley_current,
        neg_neg,adjointColour_involutive,ih]
  have he : (vacuumChevalley k).comp (vacuumChevalley k)=LinearMap.id := by
    apply (currentPBWBasis k hk).ext
    intro d
    simp only [LinearMap.comp_apply,LinearMap.id_apply,currentPBWBasis_apply]
    exact hw _
  exact LinearMap.congr_fun he

/-- The involution maps an actual joint space to the opposite-charge
space at the same energy. -/
theorem vacuumChevalley_mem_joint (k : ℂ) (hk : k+2≠0) (n c : ℤ) (v : WakModule k)
    (hv : v∈jointSpace k hk n c) : vacuumChevalley k v∈jointSpace k hk n (-c) := by
  have hh := (mem_jointSpace_iff k hk n c v).mp hv
  apply (mem_jointSpace_iff k hk n (-c) _).mpr
  constructor
  · have hg := jointSpace_le_grading k hk n c hv
    have hd : ell0OpA k v=(-(n : ℂ)) • v := by
      change v∈Module.End.eigenspace (ell0OpA k) (-(n : ℂ)) at hg
      exact Module.End.mem_eigenspace_iff.mp hg
    apply (universal k hk).L_zero_grading
    change vacuumChevalley k v∈Module.End.eigenspace (ell0OpA k) (-(n : ℂ))
    rw [Module.End.mem_eigenspace_iff,← vacuumChevalley_degree,hd,map_smul]
  · have he := congrArg (vacuumChevalley k) hh.2
    rw [map_smul] at he
    change vacuumChevalley k (J k 2 0 v)=_ at he
    rw [vacuumChevalley_current] at he
    change -J k 2 0 (vacuumChevalley k v)=(c : ℂ) • vacuumChevalley k v at he
    simpa only [Int.cast_neg,neg_smul,neg_neg] using congrArg Neg.neg he

end
end VOA.AffineSl2GeneralRigidity
