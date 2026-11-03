/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArBranchEquiv

/-! # Genuine logarithmic conformal exponentials and dual pairings

The contragredient L(0), its canonical semisimple and nilpotent parts, and their
actual exponentials are transposes on the restricted-dual pairing. The
conformal twist therefore commutes with genuine contragredient duality.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
variable (N : LogVModule W M)

/-- The actual opposite conformal zero mode is the actual L(0) operator. -/
theorem oppB_conformal_one : oppB N.toWeakModule W.conformalVector 1 = N.L0op := by
  rw [oppB_homog N.toWeakModule W.conformal_mem 1]
  rw [show (2:ℤ).toNat+1=3 from rfl]
  rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_one]
  rw [show (1:ℕ)=0+1 from rfl,show (2:ℕ)=1+1 from rfl,
    C2Rigid.L_one_pow_succ_conformalVector W 0,C2Rigid.L_one_pow_succ_conformalVector W 1]
  simp only [map_zero,mode_zero,smul_zero,add_zero,
    Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,pow_zero,Module.End.one_apply]
  norm_num
  rfl

/-- Genuine contragredient L(0) is the transpose on all actual module vectors. -/
theorem pair_contra_L0 (x : M) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW x ((contraLog N).L0op t) =
      C2Rigid.dualPairing N.toGW (N.L0op x) t := by
  change C2Rigid.dualPairing N.toGW x (mode ((contraLog N).YM W.conformalVector) 1 t) = _
  rw [pair_contra_opposite N W.conformal_mem 1,oppB_conformal_one]

/-- Genuine foreign weight pieces pair to zero. -/
theorem pair_weights_zero {a b : ℂ} {x : M} {t : C2Rigid.RestrictedDual N.toGW}
    (hx : x ∈ N.weight a) (ht : t ∈ (contraLog N).weight b) (hab : b ≠ a) :
    C2Rigid.dualPairing N.toGW x t = 0 := by
  obtain ⟨g,rfl⟩ := ht
  erw [C2Rigid.dualPairing_lof N.toGW x b g]
  rw [C2Rigid.internalProjTo_eq_zero_of_ne N.toGW hx hab,map_zero]

/-- The actual canonical semisimple grading operator also transposes. -/
theorem pair_contra_L0ss (x : M) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW x ((contraLog N).L0ss t) =
      C2Rigid.dualPairing N.toGW (N.L0ss x) t := by
  refine LogFin.induction_on N (C := fun x =>
    C2Rigid.dualPairing N.toGW x ((contraLog N).L0ss t) =
      C2Rigid.dualPairing N.toGW (N.L0ss x) t) x ?_ ?_ ?_
  · intro a x hx
    refine LogFin.induction_on (contraLog N) (C := fun t =>
      C2Rigid.dualPairing N.toGW x ((contraLog N).L0ss t) =
        C2Rigid.dualPairing N.toGW (N.L0ss x) t) t ?_ ?_ ?_
    · intro b t ht
      rw [(contraLog N).L0ss_apply_of_mem ht,N.L0ss_apply_of_mem hx,map_smul,C2Rigid.dualPairing_smul_left]
      by_cases hab : b=a
      · rw [hab]
      · rw [pair_weights_zero N hx ht hab,smul_zero,smul_zero]
    · dsimp only
      rw [map_zero,map_zero,map_zero]
    · intro t s ht hs
      dsimp only at ht hs ⊢
      rw [map_add,map_add,map_add,ht,hs]
  · dsimp only
    change C2Rigid.dualPairingFlip N.toGW ((contraLog N).L0ss t) 0 = _
    rw [map_zero,map_zero]
    change (0:ℂ) = C2Rigid.dualPairingFlip N.toGW t 0
    exact (map_zero _).symm
  · intro x y hx hy
    dsimp only at hx hy ⊢
    rw [C2Rigid.dualPairing_add_left,map_add,C2Rigid.dualPairing_add_left,hx,hy]

/-- Genuine Jordan nilpotent parts transpose without discarding logarithmic terms. -/
theorem pair_contra_L0nil (x : M) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW x ((contraLog N).L0nil t) =
      C2Rigid.dualPairing N.toGW (N.L0nil x) t := by
  simp only [LogVModule.L0nil,LinearMap.sub_apply,map_sub]
  rw [pair_contra_L0,pair_contra_L0ss]
  change C2Rigid.dualPairingFlip N.toGW t (N.L0op x) - C2Rigid.dualPairingFlip N.toGW t (N.L0ss x) =
    C2Rigid.dualPairingFlip N.toGW t (N.L0op x-N.L0ss x)
  rw [map_sub]

theorem pair_contra_L0nil_pow (k : ℕ) (x : M) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW x (((contraLog N).L0nil ^ k) t) =
      C2Rigid.dualPairing N.toGW ((N.L0nil ^ k) x) t := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ',Module.End.mul_apply]
    rw [pair_contra_L0nil,ih]
    congr 1
    rw [← Module.End.mul_apply,← pow_succ, pow_succ',Module.End.mul_apply]

/-- The actual finite Jordan exponential transposes on every actual pairing. -/
theorem pair_contra_nilExp (s : ℂ) (x : M) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW x (nilExp (contraLog N) s t) =
      C2Rigid.dualPairing N.toGW (nilExp N s x) t := by
  obtain ⟨p,hp⟩ := L0nil_locallyNilpotent N x
  obtain ⟨q,hq⟩ := L0nil_locallyNilpotent (contraLog N) t
  have hpx : (N.L0nil ^ (p+q)) x=0 := pow_apply_eq_zero_of_le hp (by omega)
  have hqt : ((contraLog N).L0nil ^ (p+q)) t=0 := pow_apply_eq_zero_of_le hq (by omega)
  rw [nilExp_finite N s hpx,nilExp_finite (contraLog N) s hqt,map_sum]
  change _ = C2Rigid.dualPairingFlip N.toGW t
    (∑ j ∈ Finset.range (p+q), (s^j/(j.factorial:ℂ)) • (N.L0nil^j) x)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul,map_smul,C2Rigid.dualPairingFlip_apply,pair_contra_L0nil_pow]

/-- Genuine conformal exponentials, retaining all Jordan terms, transpose. -/
theorem pair_contra_L0exp (s : ℂ) (x : M) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW x (L0exp (contraLog N) s t) =
      C2Rigid.dualPairing N.toGW (L0exp N s x) t := by
  refine LogFin.induction_on N (C := fun x =>
    C2Rigid.dualPairing N.toGW x (L0exp (contraLog N) s t) =
      C2Rigid.dualPairing N.toGW (L0exp N s x) t) x ?_ ?_ ?_
  · intro a x hx
    refine LogFin.induction_on (contraLog N) (C := fun t =>
      C2Rigid.dualPairing N.toGW x (L0exp (contraLog N) s t) =
        C2Rigid.dualPairing N.toGW (L0exp N s x) t) t ?_ ?_ ?_
    · intro b t ht
      rw [L0exp_apply_of_mem N s hx,L0exp_apply_of_mem (contraLog N) s ht,
        map_smul,C2Rigid.dualPairing_smul_left,pair_contra_nilExp]
      by_cases hab : b=a
      · rw [hab]
      · rw [pair_weights_zero N (nilExp_mem_weight N s hx) ht hab,smul_zero,smul_zero]
    · dsimp only
      rw [map_zero,map_zero,map_zero]
    · intro t r ht hr
      dsimp only at ht hr ⊢
      rw [map_add,map_add,map_add,ht,hr]
  · dsimp only
    change C2Rigid.dualPairingFlip N.toGW (L0exp (contraLog N) s t) 0 = _
    rw [map_zero,map_zero]
    change (0:ℂ) = C2Rigid.dualPairingFlip N.toGW t 0
    exact (map_zero _).symm
  · intro x y hx hy
    dsimp only at hx hy ⊢
    rw [C2Rigid.dualPairing_add_left,map_add,C2Rigid.dualPairing_add_left,hx,hy]

/-- The actual conformal twist is self-transpose on the genuine contragredient. -/
theorem pair_contra_twist (x : M) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW x (twist (contraLog N) t) =
      C2Rigid.dualPairing N.toGW (twist N x) t := pair_contra_L0exp N _ x t

/-- Genuine contragredient duality sends the actual logarithmic twist to the dual twist. -/
theorem transposeLog_twistHom :
    (transposeLog N N (twistHom N)).toLinearMap = (twistHom (contraLog N)).toLinearMap := by
  apply LinearMap.ext
  intro t
  apply C2Rigid.restrictedDual_ext_of_pairing N.toGW
  intro a x hx
  rw [transposeLog_pair]
  exact (pair_contra_twist N x t).symm

end VOA.LogTensor.Ar
