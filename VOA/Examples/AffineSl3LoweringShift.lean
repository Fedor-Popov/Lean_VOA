/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3GhostCharge

/-!
# Shift identities for the lowering currents

Jacobi reduces the relevant cubic gamma commutators to oscillator
commutators. Their difference at fixed total index commutes with every
ghost and has nonzero ghost charge, so it vanishes as an actual operator.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- Scalar endomorphisms commute with every polynomial endomorphism. -/
theorem comm_scalar (D : Module.End ℂ Fock) (z : ℂ) :
    ⁅D,z • (1 : Module.End ℂ Fock)⁆=0 := by
  rw [comm_smul_right]
  change z • (D*1-1*D)=0
  simp

/-- The identity endomorphism is central. -/
theorem comm_one (D : Module.End ℂ Fock) : ⁅D,(1 : Module.End ℂ Fock)⁆=0 := by
  change D*1-1*D=0
  simp

/-- A beta-gamma current acts on each gamma factor separately, including
both contractions when the gamma colours coincide. -/
theorem BG_GG (i j b c : Fin 3) (m n : ℤ) :
    ⁅BG i j m,GG b c n⁆ = colourDelta i c • GG b j (m+n)+
      colourDelta i b • GG j c (m+n) := by
  have hg (l : Fin 3) (s : ℤ) : ⁅BG i j m,gamma l s⁆ = colourDelta i l • gamma j (m+s) := by
    by_cases h : i=l <;> simp [BG_lie_gamma,colourDelta,h]
  have hf : (fun p => ⁅BG i j m,ggFam b c n p⁆) =
      fun p => colourDelta i c • ggFam b j (m+n) p +
        colourDelta i b • ggFam j c (m+n) (m+p) := by
    funext p
    simp only [ggFam_eq,lie_mul_right,hg,mul_smul_comm,smul_mul_assoc,
      show m+n-p=m+(n-p) by ring,show m+n-(m+p)=n-p by ring]
    module
  have ht := ggFam_locFin b j (m+n)
  have hu := ggFam_locFin j c (m+n)
  change ⁅BG i j m,opSum (ggFam b c n)⁆ = _
  rw [lie_opSum (ggFam_locFin b c n) _ (by rw [hf]; exact (ht.smul _).add ((hu.shift m).smul _)),
    hf,opSum_add (ht.smul _) ((hu.shift m).smul _),opSum_smul _ ht,
    opSum_smul _ (hu.shift m),opSum_shift m hu]
  rfl

/-- Reversed action of a gamma pair on a beta-gamma current. -/
theorem GG_BG (b c i j : Fin 3) (m n : ℤ) :
    ⁅GG b c m,BG i j n⁆ = -(colourDelta i c • GG b j (m+n)+
      colourDelta i b • GG j c (m+n)) := by
  rw [← lie_skew,BG_GG,add_comm n m]

/-- Gamma pairs commute with Cartan bosons. -/
theorem GG_boson (k : ℂ) (b c : Fin 3) (i : Fin 2) (m n : ℤ) :
    ⁅GG b c m,boson k i n⁆=0 := by rw [← lie_skew,boson_GG,neg_zero]

/-- First-lowering commutators with the beta oscillators, with the actual
normal-ordering derivative coefficient k+1. -/
theorem F1_beta (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅F1 k m,beta i n⁆ = if i=0 then
      (2 : ℂ) • BG 0 0 (m+n)-boson k 0 (m+n)+
        (if m+n=0 then ((k+1)*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0)
      else if i=1 then 0 else beta 1 (m+n) := by
  fin_cases i <;> by_cases hz : m+n=0 <;>
    simp [F1,sub_lie,neg_lie,add_lie,comm_smul_left,BGG_beta,BG_lie_beta,
      gamma_beta,AG_beta,hz,show n+m=m+n by ring] <;> module

/-- Second-lowering commutators with the beta oscillators. -/
theorem F2_beta (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅F2 k m,beta i n⁆ = if i=0 then -BG 0 1 (m+n)
      else if i=1 then -H2 k (m+n)+
        (if m+n=0 then (k*(m : ℂ)) • (1 : Module.End ℂ Fock) else 0)
      else -E1 (m+n) := by
  fin_cases i <;> by_cases hz : m+n=0 <;>
    simp [F2,H2,E1,sub_lie,neg_lie,add_lie,comm_smul_left,BGG_beta,BG_lie_beta,
      gamma_beta,AG_beta,hz,show n+m=m+n by ring] <;> module

/-- The beta derivative of the first relevant cubic gamma commutator
is supported only on the first colour. -/
theorem F1GG00_beta (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F1 k m,GG 0 0 n⁆,beta i r⁆ = if i=0 then (6 : ℂ) • GG 0 0 (m+n+r) else 0 := by
  rw [lie_lie,GG_beta,F1_beta]
  fin_cases i <;> by_cases hz : m+r=0 <;>
    simp [F1_gamma,comm_smul_right,lie_add,lie_sub,lie_neg,GG_BG,GG_boson,
      GG_beta,comm_scalar,comm_one,hz,colourDelta,show m+(n+r)=n+(m+r) by ring,
      show m+n+r=n+(m+r) by ring] <;> module

/-- The second-colour cubic gamma commutator has the analogous derivative. -/
theorem F2GG11_beta (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F2 k m,GG 1 1 n⁆,beta i r⁆ = if i=1 then (6 : ℂ) • GG 1 1 (m+n+r) else 0 := by
  rw [lie_lie,GG_beta,F2_beta]
  fin_cases i <;> by_cases hz : m+r=0 <;>
    simp [F2_gamma,H2,E1,comm_smul_right,lie_add,lie_sub,lie_neg,GG_BG,GG_boson,
      GG_beta,comm_scalar,comm_one,hz,colourDelta,show m+(n+r)=n+(m+r) by ring,
      show m+n+r=n+(m+r) by ring] <;> module

/-- The mixed gamma commutator differentiates to the two indicated gamma pairs. -/
theorem F2GG12_beta (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F2 k m,GG 1 2 n⁆,beta i r⁆ = if i=0 then 0 else if i=1 then
      (4 : ℂ) • GG 1 2 (m+n+r) else (2 : ℂ) • GG 1 1 (m+n+r) := by
  rw [lie_lie,GG_beta,F2_beta]
  fin_cases i <;> by_cases hz : m+r=0 <;>
    simp [F2_gamma,H2,E1,comm_smul_right,lie_add,lie_sub,lie_neg,GG_BG,GG_boson,
      GG_beta,comm_scalar,comm_one,hz,colourDelta,show m+(n+r)=n+(m+r) by ring,
      show m+n+r=n+(m+r) by ring] <;> module

/-- Gamma derivatives of a lowering/gamma-pair commutator vanish for F1. -/
theorem F1GG_gamma (k : ℂ) (b c i : Fin 3) (m n r : ℤ) :
    ⁅⁅F1 k m,GG b c n⁆,gamma i r⁆=0 := by
  rw [lie_lie,GG_gamma,F1_gamma]
  fin_cases i <;> simp [lie_neg,GG_GG,GG_gamma]

/-- Gamma derivatives of a lowering/gamma-pair commutator vanish for F2. -/
theorem F2GG_gamma (k : ℂ) (b c i : Fin 3) (m n r : ℤ) :
    ⁅⁅F2 k m,GG b c n⁆,gamma i r⁆=0 := by
  rw [lie_lie,GG_gamma,F2_gamma]
  fin_cases i <;> simp [lie_add,lie_neg,GG_GG,GG_gamma]

/-- At fixed total mode index, the F1 commutator with this gamma pair
is unchanged. Ghost-charge detection proves equality of actual operators. -/
theorem F1GG00_shift (k : ℂ) {a s a' s' : ℤ} (h : a+s=a'+s') :
    ⁅F1 k a,GG 0 0 s⁆=⁅F1 k a',GG 0 0 s'⁆ := by
  apply sub_eq_zero.mp
  apply zero_of_ghost_commuting_weight _ (-3 : ℂ)
  · intro i r
    rw [sub_lie,F1GG00_beta,F1GG00_beta,h,sub_self]
  · intro i r
    rw [sub_lie,F1GG_gamma,F1GG_gamma,sub_self]
  · norm_num
  · rw [lie_sub,leibniz_lie ghostCharge (F1 k a) (GG 0 0 s),
      leibniz_lie ghostCharge (F1 k a') (GG 0 0 s'),ghostCharge_F1,ghostCharge_F1,
      ghostCharge_GG,ghostCharge_GG]
    simp only [comm_smul_left,comm_smul_right,ghostWeight,
      show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide,
      ite_false,ite_true]
    module

/-- At fixed total mode index, the F2 commutator with this gamma pair
is unchanged. Ghost-charge detection proves equality of actual operators. -/
theorem F2GG11_shift (k : ℂ) {a s a' s' : ℤ} (h : a+s=a'+s') :
    ⁅F2 k a,GG 1 1 s⁆=⁅F2 k a',GG 1 1 s'⁆ := by
  apply sub_eq_zero.mp
  apply zero_of_ghost_commuting_weight _ (-3 : ℂ)
  · intro i r
    rw [sub_lie,F2GG11_beta,F2GG11_beta,h,sub_self]
  · intro i r
    rw [sub_lie,F2GG_gamma,F2GG_gamma,sub_self]
  · norm_num
  · rw [lie_sub,leibniz_lie ghostCharge (F2 k a) (GG 1 1 s),
      leibniz_lie ghostCharge (F2 k a') (GG 1 1 s'),ghostCharge_F2,ghostCharge_F2,
      ghostCharge_GG,ghostCharge_GG]
    simp only [comm_smul_left,comm_smul_right,ghostWeight,
      show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide,
      ite_false,ite_true]
    module

/-- At fixed total mode index, the F2 commutator with this gamma pair
is unchanged. Ghost-charge detection proves equality of actual operators. -/
theorem F2GG12_shift (k : ℂ) {a s a' s' : ℤ} (h : a+s=a'+s') :
    ⁅F2 k a,GG 1 2 s⁆=⁅F2 k a',GG 1 2 s'⁆ := by
  apply sub_eq_zero.mp
  apply zero_of_ghost_commuting_weight _ (-4 : ℂ)
  · intro i r
    rw [sub_lie,F2GG12_beta,F2GG12_beta,h,sub_self]
  · intro i r
    rw [sub_lie,F2GG_gamma,F2GG_gamma,sub_self]
  · norm_num
  · rw [lie_sub,leibniz_lie ghostCharge (F2 k a) (GG 1 2 s),
      leibniz_lie ghostCharge (F2 k a') (GG 1 2 s'),ghostCharge_F2,ghostCharge_F2,
      ghostCharge_GG,ghostCharge_GG]
    simp only [comm_smul_left,comm_smul_right,ghostWeight,
      show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide,
      ite_false,ite_true]
    module

/-- Differentiating the mixed first/second gamma pair gives exactly the
beta derivative of the (second, highest) gamma pair. -/
theorem F2GG01_beta (k : ℂ) (m n r : ℤ) (i : Fin 3) :
    ⁅⁅F2 k m,GG 0 1 n⁆,beta i r⁆ = ⁅GG 1 2 (m+n),beta i r⁆ := by
  rw [lie_lie,GG_beta,F2_beta]
  fin_cases i <;> by_cases hz : m+r=0 <;>
    simp [F2_gamma,H2,E1,comm_smul_right,lie_add,lie_sub,lie_neg,GG_BG,GG_boson,
      GG_beta,comm_one,hz,colourDelta,show m+(n+r)=n+(m+r) by ring,
      show m+n+r=n+(m+r) by ring] <;> module

/-- This mixed lowering/gamma-pair bracket is itself a gamma pair.
The identity includes all normal-ordering contributions. -/
theorem F2GG01_eq (k : ℂ) (m n : ℤ) : ⁅F2 k m,GG 0 1 n⁆=GG 1 2 (m+n) := by
  apply sub_eq_zero.mp
  apply zero_of_ghost_commuting_weight _ (-3 : ℂ)
  · intro i r; rw [sub_lie,F2GG01_beta,sub_self]
  · intro i r; rw [sub_lie,F2GG_gamma,GG_gamma,sub_self]
  · norm_num
  · rw [lie_sub,leibniz_lie ghostCharge (F2 k m) (GG 0 1 n),ghostCharge_F2,
      ghostCharge_GG,ghostCharge_GG]
    simp only [comm_smul_left,comm_smul_right,ghostWeight,
      show (0 : Fin 3) ≠ 2 by decide,show (1 : Fin 3) ≠ 2 by decide,
      ite_false,ite_true]
    module

end
end VOA.AffineSl3.FreeField
