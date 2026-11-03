/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3LoweringShift

/-!
# Self-commutation of the two simple lowering currents

All identities hold for the actual polynomial operators at every complex
level. Ghost charge detects the vanishing commutator after Jacobi and the
proved cubic shift identities establish commutation with all ghosts.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- Reversed first simple Cartan/lowering bracket. -/
theorem F1_H1 (k : ℂ) (m n : ℤ) : ⁅F1 k m,H1 k n⁆=(2 : ℂ) • F1 k (m+n) := by
  rw [← lie_skew,H1_F1,add_comm n m]; module

/-- Reversed second simple Cartan/lowering bracket. -/
theorem F2_H2 (k : ℂ) (m n : ℤ) : ⁅F2 k m,H2 k n⁆=(2 : ℂ) • F2 k (m+n) := by
  rw [← lie_skew,H2_F2,add_comm n m]; module

/-- Scalar multiples of the identity are central also in the first argument. -/
theorem scalar_comm (D : Module.End ℂ Fock) (z : ℂ) :
    ⁅z • (1 : Module.End ℂ Fock),D⁆=0 := by
  rw [← lie_skew,comm_scalar,neg_zero]

/-- The first lowering self-commutator commutes with the first raising current. -/
theorem F1self_E1 (k : ℂ) (m n r : ℤ) : ⁅⁅F1 k m,F1 k n⁆,E1 r⁆=0 := by
  have he : ⁅E1 r,⁅F1 k m,F1 k n⁆⁆=0 := by
    rw [leibniz_lie,E1_F1,E1_F1]
    simp only [add_lie,lie_add,
      zero_lie,lie_zero,ite_self,H1_F1,F1_H1,add_zero,zero_add,
      show r+m+n=m+(r+n) by ring]
    by_cases h1 : r+m=0 <;> by_cases h2 : r+n=0 <;>
      simp only [h1,h2,ite_true,ite_false,scalar_comm,comm_scalar,zero_lie,lie_zero] <;> module
  rw [← lie_skew,he,neg_zero]

/-- The first lowering self-commutator commutes with the second raising current. -/
theorem F1self_E2 (k : ℂ) (m n r : ℤ) : ⁅⁅F1 k m,F1 k n⁆,E2 r⁆=0 := by
  have he : ⁅E2 r,⁅F1 k m,F1 k n⁆⁆=0 := by
    rw [leibniz_lie,E2_F1,E2_F1]; simp
  rw [← lie_skew,he,neg_zero]

/-- The highest raising current also commutes with the first lowering
self-commutator, by its known bracket with F1. -/
theorem F1self_E12 (k : ℂ) (m n r : ℤ) : ⁅⁅F1 k m,F1 k n⁆,E12 r⁆=0 := by
  have hrev (a b : ℤ) : ⁅F1 k a,E2 b⁆=0 := by rw [← lie_skew,E2_F1,neg_zero]
  have he : ⁅E12 r,⁅F1 k m,F1 k n⁆⁆=0 := by
    rw [leibniz_lie,E12_F1,E12_F1]; simp [neg_lie,lie_neg,E2_F1,hrev]
  rw [← lie_skew,he,neg_zero]

/-- The second lowering self-commutator commutes with the first raising current. -/
theorem F2self_E1 (k : ℂ) (m n r : ℤ) : ⁅⁅F2 k m,F2 k n⁆,E1 r⁆=0 := by
  have he : ⁅E1 r,⁅F2 k m,F2 k n⁆⁆=0 := by
    rw [leibniz_lie,E1_F2,E1_F2]; simp
  rw [← lie_skew,he,neg_zero]

/-- The second lowering self-commutator commutes with its matching raising current. -/
theorem F2self_E2 (k : ℂ) (m n r : ℤ) : ⁅⁅F2 k m,F2 k n⁆,E2 r⁆=0 := by
  have he : ⁅E2 r,⁅F2 k m,F2 k n⁆⁆=0 := by
    rw [leibniz_lie,E2_F2,E2_F2]
    simp only [add_lie,lie_add,
      zero_lie,lie_zero,ite_self,H2_F2,F2_H2,add_zero,zero_add,
      show r+m+n=m+(r+n) by ring]
    by_cases h1 : r+m=0 <;> by_cases h2 : r+n=0 <;>
      simp only [h1,h2,ite_true,ite_false,scalar_comm,comm_scalar,zero_lie,lie_zero] <;> module
  rw [← lie_skew,he,neg_zero]

/-- The highest raising current commutes with the second lowering self-commutator. -/
theorem F2self_E12 (k : ℂ) (m n r : ℤ) : ⁅⁅F2 k m,F2 k n⁆,E12 r⁆=0 := by
  have hrev (a b : ℤ) : ⁅F2 k a,E1 b⁆=0 := by rw [← lie_skew,E1_F2,neg_zero]
  have he : ⁅E12 r,⁅F2 k m,F2 k n⁆⁆=0 := by
    rw [leibniz_lie,E12_F2,E12_F2]; simp [E1_F2,hrev]
  rw [← lie_skew,he,neg_zero]

/-- The first lowering self-commutator commutes with every gamma oscillator. -/
theorem F1self_gamma (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F1 k m,F1 k n⁆,gamma i r⁆=0 := by
  fin_cases i
  · change ⁅⁅F1 k m,F1 k n⁆,gamma 0 r⁆=0
    rw [lie_lie,F1_gamma,F1_gamma]
    simp only [ite_true,lie_neg,sub_eq_zero,neg_inj]
    exact F1GG00_shift k (by ring)
  · change ⁅⁅F1 k m,F1 k n⁆,gamma 1 r⁆=0
    rw [lie_lie,F1_gamma,F1_gamma]
    simp [F1_gamma,lie_neg]
  · change ⁅⁅F1 k m,F1 k n⁆,gamma 2 r⁆=0
    rw [lie_lie,F1_gamma,F1_gamma]
    simp [F1_gamma]

/-- The second lowering self-commutator commutes with every gamma oscillator. -/
theorem F2self_gamma (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F2 k m,F2 k n⁆,gamma i r⁆=0 := by
  fin_cases i
  · change ⁅⁅F2 k m,F2 k n⁆,gamma 0 r⁆=0
    rw [lie_lie,F2_gamma,F2_gamma]
    simp only [ite_true,lie_add]
    rw [F2GG01_eq,F2GG01_eq,F2_gamma,F2_gamma]
    simp [show m+(n+r)=n+(m+r) by ring]
  · change ⁅⁅F2 k m,F2 k n⁆,gamma 1 r⁆=0
    rw [lie_lie,F2_gamma,F2_gamma]
    simp only [show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,lie_neg,
      sub_eq_zero,neg_inj]
    exact F2GG11_shift k (by ring)
  · change ⁅⁅F2 k m,F2 k n⁆,gamma 2 r⁆=0
    rw [lie_lie,F2_gamma,F2_gamma]
    simp only [show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,
      ite_false,lie_neg,sub_eq_zero,neg_inj]
    exact F2GG12_shift k (by ring)

/-- All beta oscillators commute with the F1 self-commutator. The first
beta is recovered from E1 and its beta-gamma correction. -/
theorem F1self_beta (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F1 k m,F1 k n⁆,beta i r⁆=0 := by
  fin_cases i
  · have hb : ∀ s, ⁅⁅F1 k m,F1 k n⁆,beta 2 s⁆=0 := fun s => F1self_E12 k m n s
    have hg : ∀ s, ⁅⁅F1 k m,F1 k n⁆,gamma 1 s⁆=0 := fun s => F1self_gamma k m n s 1
    have he := F1self_E1 k m n r
    have hbg := commuting_BG ⁅F1 k m,F1 k n⁆ 2 1 r hb hg
    simpa [E1,lie_sub,hbg] using he
  · exact F1self_E2 k m n r
  · exact F1self_E12 k m n r

/-- The actual F1 current commutes with itself at all Fourier indices
and every complex level. No representation or noncriticality premise is used. -/
theorem F1_self (k : ℂ) (m n : ℤ) : ⁅F1 k m,F1 k n⁆=0 := by
  apply zero_of_ghost_commuting_weight _ (-2 : ℂ)
  · exact fun i r => F1self_beta k m n r i
  · exact fun i r => F1self_gamma k m n r i
  · norm_num
  · rw [leibniz_lie,ghostCharge_F1,ghostCharge_F1,comm_smul_left,comm_smul_right]
    module

/-- All beta oscillators commute with the F2 self-commutator. The first
beta is recovered from E1 and its beta-gamma correction. -/
theorem F2self_beta (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F2 k m,F2 k n⁆,beta i r⁆=0 := by
  fin_cases i
  · have hb : ∀ s, ⁅⁅F2 k m,F2 k n⁆,beta 2 s⁆=0 := fun s => F2self_E12 k m n s
    have hg : ∀ s, ⁅⁅F2 k m,F2 k n⁆,gamma 1 s⁆=0 := fun s => F2self_gamma k m n s 1
    have he := F2self_E1 k m n r
    have hbg := commuting_BG ⁅F2 k m,F2 k n⁆ 2 1 r hb hg
    simpa [E1,lie_sub,hbg] using he
  · exact F2self_E2 k m n r
  · exact F2self_E12 k m n r

/-- The actual F2 current commutes with itself at all Fourier indices
and every complex level. No representation or noncriticality premise is used. -/
theorem F2_self (k : ℂ) (m n : ℤ) : ⁅F2 k m,F2 k n⁆=0 := by
  apply zero_of_ghost_commuting_weight _ (-2 : ℂ)
  · exact fun i r => F2self_beta k m n r i
  · exact fun i r => F2self_gamma k m n r i
  · norm_num
  · rw [leibniz_lie,ghostCharge_F2,ghostCharge_F2,comm_smul_left,comm_smul_right]
    module

end
end VOA.AffineSl3.FreeField
