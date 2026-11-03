/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3LoweringSelf

/-!
# Uniform gamma-pair shifts

The same ghost-charge argument applies to every pair of gamma colours.
This supplies the index-shift identities needed for the mixed lowering
current, not merely the three pairs used in self-commutation.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical
set_option maxHeartbeats 800000

/-- An optionally present scalar endomorphism is still central. -/
theorem comm_ite_scalar (D : Module.End ℂ Fock) (z : ℂ) (P : Prop) [Decidable P] :
    ⁅D,if P then z • (1 : Module.End ℂ Fock) else 0⁆=0 := by
  by_cases h : P <;> simp only [h,ite_true,ite_false,comm_scalar,lie_zero]

/-- The beta derivatives of F1 acting on any gamma pair depend only on
the total Fourier index; all central contributions commute away. -/
theorem F1GG_beta_total (k : ℂ) (b c i : Fin 3) (m n r : ℤ) :
    ⁅⁅F1 k m,GG b c n⁆,beta i r⁆ = ⁅⁅F1 k (m+n),GG b c 0⁆,beta i r⁆ := by
  simp only [lie_lie,GG_beta,F1_beta]
  fin_cases b <;> fin_cases c <;> fin_cases i <;>
    simp [F1_gamma,comm_smul_right,lie_add,lie_sub,lie_neg,GG_BG,GG_boson,
      GG_beta,comm_one,comm_ite_scalar,colourDelta,
      show m+(n+r)=m+n+r by ring,show n+(m+r)=m+n+r by ring] <;> module

/-- The same total-index property holds for F2 and every gamma pair. -/
theorem F2GG_beta_total (k : ℂ) (b c i : Fin 3) (m n r : ℤ) :
    ⁅⁅F2 k m,GG b c n⁆,beta i r⁆ = ⁅⁅F2 k (m+n),GG b c 0⁆,beta i r⁆ := by
  simp only [lie_lie,GG_beta,F2_beta]
  fin_cases b <;> fin_cases c <;> fin_cases i <;>
    simp [F2_gamma,H2,E1,comm_smul_right,lie_add,lie_sub,lie_neg,GG_BG,GG_boson,
      GG_beta,comm_one,comm_ite_scalar,colourDelta,
      show m+(n+r)=m+n+r by ring,show n+(m+r)=m+n+r by ring] <;> module

/-- Every F1/gamma-pair commutator depends only on the sum of its two
mode indices, as an equality of actual endomorphisms. -/
theorem F1GG_shift (k : ℂ) (b c : Fin 3) {m n m' n' : ℤ} (h : m+n=m'+n') :
    ⁅F1 k m,GG b c n⁆=⁅F1 k m',GG b c n'⁆ := by
  apply sub_eq_zero.mp
  apply zero_of_ghost_commuting_weight _ (-1-ghostWeight b-ghostWeight c)
  · intro i r
    rw [sub_lie,F1GG_beta_total k b c i m n r,F1GG_beta_total k b c i m' n' r,h,sub_self]
  · intro i r; rw [sub_lie,F1GG_gamma,F1GG_gamma,sub_self]
  · fin_cases b <;> fin_cases c <;> norm_num [ghostWeight,Fin.ext_iff]
  · rw [lie_sub,leibniz_lie ghostCharge (F1 k m) (GG b c n),
      leibniz_lie ghostCharge (F1 k m') (GG b c n'),ghostCharge_F1,ghostCharge_F1,
      ghostCharge_GG,ghostCharge_GG]
    simp only [comm_smul_left,comm_smul_right]
    module

/-- Every F2/gamma-pair commutator has the same total-index property. -/
theorem F2GG_shift (k : ℂ) (b c : Fin 3) {m n m' n' : ℤ} (h : m+n=m'+n') :
    ⁅F2 k m,GG b c n⁆=⁅F2 k m',GG b c n'⁆ := by
  apply sub_eq_zero.mp
  apply zero_of_ghost_commuting_weight _ (-1-ghostWeight b-ghostWeight c)
  · intro i r
    rw [sub_lie,F2GG_beta_total k b c i m n r,F2GG_beta_total k b c i m' n' r,h,sub_self]
  · intro i r; rw [sub_lie,F2GG_gamma,F2GG_gamma,sub_self]
  · fin_cases b <;> fin_cases c <;> norm_num [ghostWeight,Fin.ext_iff]
  · rw [lie_sub,leibniz_lie ghostCharge (F2 k m) (GG b c n),
      leibniz_lie ghostCharge (F2 k m') (GG b c n'),ghostCharge_F2,ghostCharge_F2,
      ghostCharge_GG,ghostCharge_GG]
    simp only [comm_smul_left,comm_smul_right]
    module

end
end VOA.AffineSl3.FreeField
