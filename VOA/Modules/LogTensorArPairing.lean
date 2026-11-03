/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArFiniteness
import VOA.Modules.LogTensorArOpposite
import VOA.Modules.LogTensorPrecompose
import VOA.Modules.LogTensorPzJacobiDerivative

/-! # Genuine zeroth A-transform pairings for logarithmic modules

The actual Jordan half-turn is a module automorphism. Preparing the first
input by that automorphism makes the genuine zeroth A-coefficient exactly the
FHL opposite coefficient family. The restricted-dual pairing holds on all inputs.
-/
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

private def identityHom (A : WeakModule W M₂) : A.Hom A :=
  ⟨LinearMap.id,fun _ _ _ => rfl⟩

/-- Actual nilpotent half-turns commute with every genuine L(1) power. -/
theorem nilExp_L1_pow (N : LogVModule W M₁) (s : ℂ) (j : ℕ) (x : M₁) :
    nilExp N s ((L1w N.toWeakModule ^ j) x) =
      (L1w N.toWeakModule ^ j) (nilExp N s x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ',Module.End.mul_apply]
    have h : ∀ z, nilExp N s (L1w N.toWeakModule z) =
        L1w N.toWeakModule (nilExp N s z) := (nilExpHom N s).map_act W.conformalVector 2
    rw [h,ih]

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- The genuine logarithmic operator prepared by the actual Jordan half-turn. -/
noncomputable def prepared :
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule :=
  precompose (nilExpHom N₁ (phase 0)) (identityHom N₂.toWeakModule) Y

/-- The actual zeroth logarithmic family of a genuine operator. -/
noncomputable def zeroFamily : IntertwiningModes M₁ M₂ M₃ := fun n => Y.1 n 0

/-- Its genuine Jacobi and truncation are inherited at actual log degree zero. -/
theorem zeroFamily_isJacobi :
    IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule (zeroFamily N₁ N₂ N₃ Y) where
  truncation x y n := by
    obtain ⟨K,hK⟩ := Y.2.truncation x y n
    exact ⟨K,fun j hj => hK j hj 0⟩
  jacobi u x y ell m n := Y.2.jacobi u x y ell m n 0

/-- The actual opposite coefficient has the correct generalized output weight. -/
theorem twI_mem_weight_log {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (n : ℂ) :
    twI N₁.toGW (zeroFamily N₁ N₂ N₃ Y) a n x y ∈ N₃.weight (b+n+1-a) := by
  obtain ⟨J,hJ⟩ := L1w_pow_eventually N₁.toGW x
  rw [twI_apply_eq_sum N₁.toGW _ a n hJ y]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_))
  have hm := Y.2.mem_weight (L1_pow_mem_weight N₁.toGW hx j) hy (2*a-n-2-j) 0
  convert hm using 2 <;> ring

/-- The zeroth first-state term contains the genuine nilpotent half-turn. -/
theorem firstTermEnd_zero {a : ℂ} {x : M₁} (hx : x ∈ N₁.weight a) (j : ℕ) :
    firstTermEnd N₁ (phase 0) j 0 x =
      statePhase a • nilExp N₁ (phase 0) ((L1w N₁.toWeakModule ^ j) x) := by
  change (L1w N₁.toWeakModule ^ j) (L0exp N₁ (phase 0) x) = _
  rw [L0exp_apply_of_mem N₁ (phase 0) hx,map_smul,nilExp_L1_pow]
  congr 1
  unfold phase statePhase
  norm_num

/-- The literal zeroth coefficient equals the FHL opposite family of the genuinely
Jordan-prepared logarithmic operator. -/
theorem functional_zero_eq_twI (n : ℂ) {a : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight a) (t : C2Rigid.RestrictedDual N₃.toGW) (y : M₂) :
    functional N₁ N₂ N₃ Y 0 n 0 a x t y =
      C2Rigid.dualPairing N₃.toGW
        (twI N₁.toGW (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) a n x y) t := by
  have hK : ∀ j, L1Cutoff N₁ a ≤ j → (L1w N₁.toWeakModule ^ j) x = 0 :=
    fun j hj => L1Cutoff_spec N₁ a j hj x hx
  rw [twI_apply_eq_sum N₁.toGW _ a n hK y]
  change _ = C2Rigid.dualPairingFlip N₃.toGW t
    (statePhase a • ∑ j ∈ Finset.range (L1Cutoff N₁ a), (j.factorial:ℂ)⁻¹ •
      (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) (2*a-n-2-j)
        ((L1w N₁.toWeakModule ^ j) x) y)
  rw [map_smul,map_sum]
  simp only [functional,LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,
    Nat.zero_add,Finset.sum_range_one,coefficient,Nat.zero_sub,Nat.factorial_zero,Nat.cast_one,pow_zero,
    inv_one,mul_one,zero_sub,Nat.sub_zero,map_smul,smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [matrixTerm_apply,firstTermEnd_zero N₁ hx j]
  change (j.factorial:ℂ)⁻¹ * C2Rigid.dualPairingFlip N₃.toGW t
      (Y.1 (2*a-j-n-2) 0 (statePhase a • nilExp N₁ (phase 0) ((L1w N₁.toWeakModule ^ j) x)) y) = _
  have hn : 2*a-j-n-2 = 2*a-n-2-j := by ring
  rw [hn]
  simp only [zeroFamily,prepared,precompose_apply,identityHom,LinearMap.id_apply,
    map_smul,LinearMap.smul_apply,smul_eq_mul,nilExpHom,LinearEquiv.coe_coe]
  ring

/-- The genuine zeroth pairing on homogeneous vectors, including foreign weights. -/
theorem pair_modes_zero_homogeneous (n : ℂ) {a b c : ℂ} {x : M₁} {y : M₂}
    {t : C2Rigid.RestrictedDual N₃.toGW}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (ht : t ∈ (contraLog N₃).weight c) :
    C2Rigid.dualPairing N₂.toGW y (modes N₁ N₂ N₃ Y 0 n 0 x t) =
      C2Rigid.dualPairing N₃.toGW
        (twI N₁.toGW (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) a n x y) t := by
  rw [pair_modes N₁ N₂ N₃ Y 0 n 0 hx hy ht,functional_zero_eq_twI N₁ N₂ N₃ Y n hx t y]
  split_ifs with h
  · rfl
  · obtain ⟨f,rfl⟩ := ht
    have hm := twI_mem_weight_log N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y) hx hy n
    have hne : c ≠ b+n+1-a := by intro he; apply h; linear_combination -he
    erw [C2Rigid.dualPairing_lof N₃.toGW _ c f]
    rw [C2Rigid.internalProjTo_eq_zero_of_ne N₃.toGW hm hne,map_zero]

/-- The actual zeroth A-transform pairing holds on every target and dual vector. -/
theorem pair_modes_zero (n : ℂ) {a : ℂ} {x : M₁} (hx : x ∈ N₁.weight a)
    (t : C2Rigid.RestrictedDual N₃.toGW) (y : M₂) :
    C2Rigid.dualPairing N₂.toGW y (modes N₁ N₂ N₃ Y 0 n 0 x t) =
      C2Rigid.dualPairing N₃.toGW
        (twI N₁.toGW (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) a n x y) t := by
  refine LogFin.induction_on (contraLog N₃) (C := fun t =>
    C2Rigid.dualPairing N₂.toGW y (modes N₁ N₂ N₃ Y 0 n 0 x t) =
      C2Rigid.dualPairing N₃.toGW
        (twI N₁.toGW (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) a n x y) t)
    t ?_ ?_ ?_
  · intro c t ht
    refine LogFin.induction_on N₂ (C := fun y =>
      C2Rigid.dualPairing N₂.toGW y (modes N₁ N₂ N₃ Y 0 n 0 x t) =
        C2Rigid.dualPairing N₃.toGW
          (twI N₁.toGW (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) a n x y) t)
      y ?_ ?_ ?_
    · intro b y hy
      exact pair_modes_zero_homogeneous N₁ N₂ N₃ Y n hx hy ht
    · change C2Rigid.dualPairingFlip N₂.toGW (modes N₁ N₂ N₃ Y 0 n 0 x t) 0 =
        C2Rigid.dualPairingFlip N₃.toGW t
          (twI N₁.toGW (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) a n x 0)
      rw [map_zero,map_zero,map_zero]
    · intro y z hy hz
      dsimp only at hy hz ⊢
      rw [C2Rigid.dualPairing_add_left,map_add,C2Rigid.dualPairing_add_left,hy,hz]
  · dsimp only
    rw [map_zero,map_zero,map_zero]
  · intro t s ht hs
    dsimp only at ht hs ⊢
    rw [map_add,map_add,map_add,ht,hs]

/-- Genuine contragredient module modes transpose the actual weak opposite modes,
on arbitrary vectors of the actual generalized module. -/
theorem pair_contra_opposite (N : LogVModule W M₂) {d : ℤ} {u : V}
    (hu : u ∈ W.grading d) (p : ℤ) (y : M₂) (t : C2Rigid.RestrictedDual N.toGW) :
    C2Rigid.dualPairing N.toGW y (mode ((contraLog N).YM u) p t) =
      C2Rigid.dualPairing N.toGW (oppB N.toWeakModule u p y) t := by
  refine LogFin.induction_on N (C := fun y =>
    C2Rigid.dualPairing N.toGW y (mode ((contraLog N).YM u) p t) =
      C2Rigid.dualPairing N.toGW (oppB N.toWeakModule u p y) t) y ?_ ?_ ?_
  · intro a y hy
    change C2Rigid.dualPairing N.toGW y (mode (C2Rigid.YMdual N.toGW u) p t) = _
    rw [C2Rigid.dualPairing_mode_dualAdj N.toGW hu p t hy,
      C2Rigid.dualAdj_clean N.toGW hu p hy]
    rw [oppB_homog N.toWeakModule hu p]
    simp only [LinearMap.smul_apply,LinearMap.coe_sum,Finset.sum_apply]
    rfl
  · change C2Rigid.dualPairingFlip N.toGW (mode ((contraLog N).YM u) p t) 0 =
      C2Rigid.dualPairingFlip N.toGW t (oppB N.toWeakModule u p 0)
    rw [map_zero,map_zero,map_zero]
  · intro y z hy hz
    dsimp only at hy hz ⊢
    rw [C2Rigid.dualPairing_add_left,map_add,C2Rigid.dualPairing_add_left,hy,hz]

end VOA.LogTensor.Ar
