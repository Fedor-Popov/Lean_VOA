/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3GammaNormalizer

/-!
# The actual negative Serre relations

Partial ghost charge excludes the two nonexistent negative root spaces.
Jacobi supplies the required raising equations, and the gamma-normalizer
property is proved from the explicit current formulas. No Serre premise
or abstract highest-weight existence assumption is used.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- An optional scalar term commutes in the first argument as well. -/
theorem ite_scalar_comm (D : Module.End ℂ Fock) (z : ℂ) (P : Prop) [Decidable P] :
    ⁅if P then z • (1 : Module.End ℂ Fock) else 0,D⁆=0 := by
  rw [← lie_skew,comm_ite_scalar,neg_zero]

/-- The first negative Serre operator commutes with the second raising current. -/
theorem E2_firstSerre (k : ℂ) (m n r : ℤ) :
    ⁅E2 r,⁅F1 k m,F12 k n⁆⁆=0 := by
  rw [leibniz_lie,E2_F1,E2_F12,zero_lie,zero_add,F1_self]

/-- The first negative Serre operator commutes with the highest raising current. -/
theorem E12_firstSerre (k : ℂ) (m n r : ℤ) :
    ⁅E12 r,⁅F1 k m,F12 k n⁆⁆=0 := by
  rw [leibniz_lie,E12_F1,E12_F12]
  simp only [neg_lie,E2_F12,lie_add,F1_H1,F1_H2,comm_ite_scalar,add_zero,
    show r+m+n=m+(r+n) by ring]
  module

/-- The second negative Serre operator commutes with the second raising current. -/
theorem E2_secondSerre (k : ℂ) (m n r : ℤ) :
    ⁅E2 r,⁅F2 k m,F12 k n⁆⁆=0 := by
  rw [leibniz_lie,E2_F2,E2_F12]
  simp only [add_lie,H2_F12,ite_scalar_comm,F2_F1,add_zero,
    show r+m+n=m+(r+n) by ring]
  module

/-- The second negative Serre operator commutes with the highest raising current. -/
theorem E12_secondSerre (k : ℂ) (m n r : ℤ) :
    ⁅E12 r,⁅F2 k m,F12 k n⁆⁆=0 := by
  rw [leibniz_lie,E12_F2,E12_F12]
  simp only [E1_F12,lie_add,F2_H1,F2_H2,comm_ite_scalar,add_zero,
    show r+m+n=m+(r+n) by ring]
  module

/-- The root -2 alpha1-alpha2 is absent: the first simple lowering
commutes with the highest lowering at every pair of mode indices. -/
theorem F1_F12 (k : ℂ) (m n : ℤ) : ⁅F1 k m,F12 k n⁆=0 := by
  apply zero_of_normalizer_partial_weight _ (-3 : ℂ)
  · exact (F1_gammaNormalizer k m).lie (F12_gammaNormalizer k n)
  · intro i hi r; rcases hi with rfl | rfl
    · change ⁅⁅F1 k m,F12 k n⁆,E2 r⁆=0
      rw [← lie_skew,E2_firstSerre,neg_zero]
    · change ⁅⁅F1 k m,F12 k n⁆,E12 r⁆=0
      rw [← lie_skew,E12_firstSerre,neg_zero]
  · norm_num
  · norm_num
  · rw [leibniz_lie,partialCharge_F1,partialCharge_F12,zero_lie,
      comm_smul_right,zero_add]

/-- The root -alpha1-2 alpha2 is absent as well. This is the second
negative Serre relation for the actual currents, at arbitrary level. -/
theorem F2_F12 (k : ℂ) (m n : ℤ) : ⁅F2 k m,F12 k n⁆=0 := by
  apply zero_of_normalizer_partial_weight _ (-6 : ℂ)
  · exact (F2_gammaNormalizer k m).lie (F12_gammaNormalizer k n)
  · intro i hi r; rcases hi with rfl | rfl
    · change ⁅⁅F2 k m,F12 k n⁆,E2 r⁆=0
      rw [← lie_skew,E2_secondSerre,neg_zero]
    · change ⁅⁅F2 k m,F12 k n⁆,E12 r⁆=0
      rw [← lie_skew,E12_secondSerre,neg_zero]
  · norm_num
  · norm_num
  · rw [leibniz_lie,partialCharge_F2,partialCharge_F12,comm_smul_left,comm_smul_right]
    module

/-- The highest lowering current commutes with itself, by Jacobi and
both proved negative Serre relations. -/
theorem F12_self (k : ℂ) (m n : ℤ) : ⁅F12 k m,F12 k n⁆=0 := by
  change ⁅⁅F2 k m,F1 k 0⁆,F12 k n⁆=0
  rw [lie_lie,F1_F12,F2_F12,lie_zero,lie_zero,sub_self]

end
end VOA.AffineSl3.FreeField
