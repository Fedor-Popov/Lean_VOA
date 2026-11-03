/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3GammaPairShift

/-!
# The highest lowering current

The mixed simple-lowering bracket depends only on total Fourier index.
This is proved on the actual oscillator representation before defining
F12. It does not yet assert the negative Serre relations.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- The first Cartan acts on the second lowering current with weight one. -/
theorem F2_H1 (k : ℂ) (m n : ℤ) : ⁅F2 k m,H1 k n⁆= -F2 k (m+n) := by
  rw [← lie_skew,H1_F2,one_smul,add_comm n m]

/-- The second Cartan acts on the first lowering current with weight one. -/
theorem F1_H2 (k : ℂ) (m n : ℤ) : ⁅F1 k m,H2 k n⁆= -F1 k (m+n) := by
  rw [← lie_skew,H2_F1,one_smul,add_comm n m]

/-- Reversed second simple raising/lowering bracket, with its central term. -/
theorem F2_E2 (k : ℂ) (m n : ℤ) : ⁅F2 k m,E2 n⁆=
    -(H2 k (n+m)+(if n+m=0 then (k*(n : ℂ)) • (1 : Module.End ℂ Fock) else 0)) := by
  rw [← lie_skew,E2_F2]

/-- First raising action on the mixed lowering bracket. -/
theorem E1_mixed (k : ℂ) (m n r : ℤ) :
    ⁅E1 r,⁅F2 k m,F1 k n⁆⁆= -F2 k (m+n+r) := by
  rw [leibniz_lie,E1_F2,E1_F1]
  simp only [zero_lie,zero_add,lie_add,F2_H1,comm_ite_scalar,add_zero,
    show m+(r+n)=m+n+r by ring]

/-- Second raising action on the mixed lowering bracket. -/
theorem E2_mixed (k : ℂ) (m n r : ℤ) :
    ⁅E2 r,⁅F2 k m,F1 k n⁆⁆= F1 k (m+n+r) := by
  rw [leibniz_lie,E2_F2,E2_F1]
  have hc : ⁅if r+m=0 then (k*(r : ℂ)) • (1 : Module.End ℂ Fock) else 0,F1 k n⁆=0 := by
    by_cases h : r+m=0 <;> simp only [h,ite_true,ite_false,scalar_comm,zero_lie]
  simp only [lie_zero,add_zero,add_lie,H2_F1,hc,one_smul,
    show r+m+n=m+n+r by ring]

/-- The highest raising action has the sum of the two Cartans and the
central term of a root of squared length two. -/
theorem E12_mixed (k : ℂ) (m n r : ℤ) :
    ⁅E12 r,⁅F2 k m,F1 k n⁆⁆= H1 k (m+n+r)+H2 k (m+n+r)+
      (if m+n+r=0 then (k*(r : ℂ)) • (1 : Module.End ℂ Fock) else 0) := by
  rw [leibniz_lie,E12_F2,E12_F1,lie_neg,E1_F1,F2_E2,neg_neg]
  have h1 : r+m+n=m+n+r := by ring
  have h2 : r+n+m=m+n+r := by ring
  simp only [h1,h2]
  by_cases hz : m+n+r=0
  · have hs : (m : ℂ)+(n : ℂ)+(r : ℂ)=0 := by exact_mod_cast hz
    simp only [hz,ite_true,Int.cast_add]
    have hc : k*((r : ℂ)+m)+k*((r : ℂ)+n)=k*r := by linear_combination k*hs
    calc
      _ = H1 k 0+H2 k 0+
        ((k*((r : ℂ)+m)+k*((r : ℂ)+n)) • (1 : Module.End ℂ Fock)) := by module
      _ = _ := by rw [hc]
  · simp [hz] <;> module

/-- Gamma commutators of the mixed lowering bracket depend only on its
total Fourier index. -/
theorem mixed_gamma_total (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F2 k m,F1 k n⁆,gamma i r⁆ = ⁅⁅F2 k (m+n),F1 k 0⁆,gamma i r⁆ := by
  fin_cases i
  · change ⁅⁅F2 k m,F1 k n⁆,gamma 0 r⁆ = ⁅⁅F2 k (m+n),F1 k 0⁆,gamma 0 r⁆
    simp only [lie_lie,F1_gamma,F2_gamma,ite_true,lie_neg,lie_add,
      show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,
      ite_false,lie_zero,sub_zero,zero_add]
    rw [F2GG_shift k 0 0 (m:=m) (n:=n+r) (m':=m+n) (n':=r) (by ring),
      F1GG_shift k 0 1 (m:=n) (n:=m+r) (m':=0) (n':=m+n+r) (by ring)]
  · change ⁅⁅F2 k m,F1 k n⁆,gamma 1 r⁆ = ⁅⁅F2 k (m+n),F1 k 0⁆,gamma 1 r⁆
    simp only [lie_lie,F1_gamma,F2_gamma,show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,
      ite_true,ite_false,lie_neg,neg_neg,zero_add]
    rw [F1GG_shift k 1 1 (m:=n) (n:=m+r) (m':=0) (n':=m+n+r) (by ring)]
    simp only [show m+(n+r)=m+n+r by ring]
  · change ⁅⁅F2 k m,F1 k n⁆,gamma 2 r⁆ = ⁅⁅F2 k (m+n),F1 k 0⁆,gamma 2 r⁆
    simp only [lie_lie,F1_gamma,F2_gamma,show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide,ite_false,lie_zero,zero_sub,lie_neg,neg_neg]
    rw [F1GG_shift k 1 2 (m:=n) (n:=m+r) (m':=0) (n':=m+n+r) (by ring)]

/-- The actual mixed bracket depends only on total mode index. -/
theorem mixed_eq_total (k : ℂ) (m n : ℤ) : ⁅F2 k m,F1 k n⁆=⁅F2 k (m+n),F1 k 0⁆ := by
  let D := ⁅F2 k m,F1 k n⁆-⁅F2 k (m+n),F1 k 0⁆
  have hg : ∀ i r, ⁅D,gamma i r⁆=0 := by
    intro i r
    dsimp [D]
    rw [sub_lie,mixed_gamma_total k m n r i,sub_self]
  have he1 : ∀ r, ⁅E1 r,D⁆=0 := by
    intro r; simp only [D,lie_sub,E1_mixed,add_zero,sub_self]
  have he2 : ∀ r, ⁅E2 r,D⁆=0 := by
    intro r; simp only [D,lie_sub,E2_mixed,add_zero,sub_self]
  have he3 : ∀ r, ⁅E12 r,D⁆=0 := by
    intro r; simp only [D,lie_sub,E12_mixed,add_zero,sub_self]
  have hb2 : ∀ r, ⁅D,beta 1 r⁆=0 := by
    intro r; change ⁅D,E2 r⁆=0; rw [← lie_skew,he2,neg_zero]
  have hb3 : ∀ r, ⁅D,beta 2 r⁆=0 := by
    intro r; change ⁅D,E12 r⁆=0; rw [← lie_skew,he3,neg_zero]
  have hb : ∀ i r, ⁅D,beta i r⁆=0 := by
    intro i r; fin_cases i
    · have hbg := commuting_BG D 2 1 r hb3 (hg 1)
      have he : ⁅D,E1 r⁆=0 := by rw [← lie_skew,he1,neg_zero]
      simpa [E1,lie_sub,hbg] using he
    · exact hb2 r
    · exact hb3 r
  apply sub_eq_zero.mp
  apply zero_of_ghost_commuting_weight D (-2 : ℂ) hb hg (by norm_num)
  dsimp [D]
  rw [lie_sub,leibniz_lie ghostCharge (F2 k m) (F1 k n),
    leibniz_lie ghostCharge (F2 k (m+n)) (F1 k 0)]
  simp only [ghostCharge_F1,ghostCharge_F2,comm_smul_left,comm_smul_right]
  module

/-- The highest lowering current, defined using the index-independent
mixed bracket of actual simple lowering modes. -/
def F12 (k : ℂ) (n : ℤ) : Module.End ℂ Fock := ⁅F2 k n,F1 k 0⁆

/-- The mixed negative-root current relation has the expected sum of indices. -/
theorem F2_F1 (k : ℂ) (m n : ℤ) : ⁅F2 k m,F1 k n⁆=F12 k (m+n) := mixed_eq_total k m n

/-- First raising action on the highest lowering current. -/
theorem E1_F12 (k : ℂ) (m n : ℤ) : ⁅E1 m,F12 k n⁆= -F2 k (m+n) := by
  simp only [F12,E1_mixed,add_zero,add_comm n m]

/-- Second raising action on the highest lowering current. -/
theorem E2_F12 (k : ℂ) (m n : ℤ) : ⁅E2 m,F12 k n⁆=F1 k (m+n) := by
  simp only [F12,E2_mixed,add_zero,add_comm n m]

/-- The opposite highest-root bracket has H1+H2 and central coefficient km. -/
theorem E12_F12 (k : ℂ) (m n : ℤ) : ⁅E12 m,F12 k n⁆=
    H1 k (m+n)+H2 k (m+n)+
      (if m+n=0 then (k*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0) := by
  simp only [F12,E12_mixed,add_zero,add_comm n m]

/-- The highest lowering has first Cartan weight minus one. -/
theorem H1_F12 (k : ℂ) (m n : ℤ) : ⁅H1 k m,F12 k n⁆= -F12 k (m+n) := by
  rw [F12,leibniz_lie,H1_F2,H1_F1,comm_smul_left,comm_smul_right]
  simp only [F2_F1,add_zero,one_smul]
  rw [add_comm n m]
  module

/-- The highest lowering has second Cartan weight minus one. -/
theorem H2_F12 (k : ℂ) (m n : ℤ) : ⁅H2 k m,F12 k n⁆= -F12 k (m+n) := by
  rw [F12,leibniz_lie,H2_F2,H2_F1,comm_smul_left,comm_smul_right]
  simp only [F2_F1,add_zero,one_smul]
  rw [add_comm n m]
  module

/-- Nonnegative highest-lowering modes annihilate the actual vacuum. -/
theorem F12_vacuum (k : ℂ) {n : ℤ} (hn : 0 ≤ n) : F12 k n 1=0 := by
  simp [F12,Ring.lie_def,Module.End.mul_apply,F1_vacuum k (n:=0) (by omega),F2_vacuum k hn]

end
end VOA.AffineSl3.FreeField
