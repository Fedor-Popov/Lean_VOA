/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AdmissibleNullVector

/-!
# Genuine simple-quotient dimensions below the admissible root

The simple quotient agrees with the universal PBW count in every joint
energy/charge block strictly below the first admissible energy. These are
actual quotient dimensions, not a proposed character used as a definition.
The all-degree character theorem is not asserted here.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule VertexOperatorAlgebra
noncomputable section

/-- The actual joint piece in the simple affine quotient. -/
def simpleJointPiece (k : ℂ) (hk : k + 2 ≠ 0) (n h : ℤ) :=
  (jointSpace k hk n h).map (QuotVOA.maxGradedIdeal (universal k hk)).mkQ

/-- Below the first admissible root, the actual simple quotient map is
injective on each joint energy/charge space. -/
theorem admissible_joint_quotient_injective (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q) (n : ℕ) (c : ℤ) (hn : n < q * (p - 1)) :
    Function.Injective
      ((QuotVOA.maxGradedIdeal (universal _ (admissible_level_noncritical p q hp hq))).mkQ.domRestrict
        (jointSpace _ (admissible_level_noncritical p q hp hq) n (2 * c))) := by
  intro x y he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply admissible_null_eq_zero_below_all p q hp hq hcop n c hn (x.val - y.val)
    (Submodule.sub_mem _ x.property y.property)
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (QuotVOA.maxGradedIdeal
    (universal _ (admissible_level_noncritical p q hp hq))).mkQ (x.val - y.val) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr he

/-- The simple affine joint dimension is exactly the universal PBW count
through every degree strictly below the first admissible root. -/
theorem admissible_simpleJointPiece_finrank_below (p q : ℕ) (hp : 2 ≤ p)
    (hq : 0 < q) (hcop : p.Coprime q) (n : ℕ) (c : ℤ)
    (hn : n < q * (p - 1)) :
    Module.finrank ℂ (simpleJointPiece _ (admissible_level_noncritical p q hp hq)
      n (2 * c)) = Fintype.card (JointIndex n (2 * c)) := by
  have hr := LinearMap.finrank_range_of_inj
    (admissible_joint_quotient_injective p q hp hq hcop n c hn)
  rw [LinearMap.range_domRestrict] at hr
  exact hr.trans (jointSpace_finrank _ _ n (2 * c))

end
end VOA.AffineSl2GeneralRigidity
