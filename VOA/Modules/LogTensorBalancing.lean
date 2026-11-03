/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzNilCovariance
import VOA.Modules.LogTensorArBranches

/-! # Genuine logarithmic double-skew conformal transport

The two half-turns compose into a full logarithmic branch shift and its actual
mode phase. Genuine Jordan covariance identifies this with the actual L(0)
exponentials, retaining every logarithmic coefficient.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor
open Module (End)
open scoped BigOperators
open Pz Contra Ar
noncomputable section
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- Scalar phase transport of the actual coefficients at each complex exponent. -/
def modeScale (c : ℂ → ℂ) (Y : LogModes M₁ M₂ M₃) : LogModes M₁ M₂ M₃ :=
  fun n k => c n • Y n k

@[simp] theorem modeScale_apply (c : ℂ → ℂ) (Y : LogModes M₁ M₂ M₃)
    (n : ℂ) (k : ℕ) (x : M₁) (y : M₂) : modeScale c Y n k x y = c n • Y n k x y := rfl

theorem logFin_modeScale {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) (c : ℂ → ℂ) :
    LogFin (modeScale c Y) := by
  intro x y n
  obtain ⟨K,hK⟩ := hY x y n
  exact ⟨K,fun k hk => by rw [modeScale_apply,hK k hk,smul_zero]⟩

/-- Actual finite logarithmic shifts commute with exponent-dependent scalar phases. -/
theorem logShift_modeScale {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) (c : ℂ → ℂ) (s : ℂ) :
    logShift s (modeScale c Y) = modeScale c (logShift s Y) := by
  funext n k
  ext x y
  obtain ⟨K,hK⟩ := hY x y n
  rw [logShift_eq_sum (logFin_modeScale hY c) K (fun j hj => by rw [modeScale_apply,hK j hj,smul_zero]),
    modeScale_apply,logShift_eq_sum hY K hK,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [modeScale_apply,smul_comm]

/-- The actual full-turn phase for exponent -n-1. -/
def monodromyPhase (n : ℂ) : ℂ := Complex.exp (-(2*Real.pi*Complex.I)*(n+1))

/-- Actual consecutive half-turn branches differ by the full-turn mode phase. -/
theorem omegaPhase_next (r : ℤ) (n : ℂ) :
    omegaPhase (r+1) n = monodromyPhase n * omegaPhase r n := by
  rw [omegaPhase,monodromyPhase,omegaPhase,← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Changing the front half-turn phase scales every actual finite skew coefficient. -/
theorem skewK_phase {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
    {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y)
    (c d e : ℂ → ℂ) (hc : ∀ n, c n=d n*e n) :
    skewK A₃ c Y = modeScale d (skewK A₃ e Y) := by
  funext n k
  ext y x
  rw [modeScale_apply,hY.skewK_apply c,hY.skewK_apply e,hc n,smul_smul]

/-- Two actual consecutive Ω branches differ by the genuine full logarithmic shift. -/
theorem omega_next {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
    {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y) (r : ℤ) :
    omega A₃ (r+1) Y = modeScale monodromyPhase (logShift (2*Real.pi*Complex.I) (omega A₃ r Y)) := by
  have hK := hY.isLogIntertwining_skewK (omegaPhase_succ r) (omegaPhase_ne_zero r)
  have hparam : (2*((r+1:ℤ):ℂ)+1)*(Real.pi*Complex.I) =
      (2*Real.pi*Complex.I)+(2*(r:ℂ)+1)*(Real.pi*Complex.I) := by push_cast; ring
  change logShift ((2*((r+1:ℤ):ℂ)+1)*(Real.pi*Complex.I)) (skewK A₃ (omegaPhase (r+1)) Y) =
    modeScale monodromyPhase (logShift (2*Real.pi*Complex.I)
      (logShift ((2*(r:ℂ)+1)*(Real.pi*Complex.I)) (skewK A₃ (omegaPhase r) Y)))
  rw [skewK_phase hY _ _ _ (omegaPhase_next r),logShift_modeScale hK.logFin,hparam,
    ← logShift_logShift hK.logFin]

/-- The actual Ω0 composed twice is its full logarithmic monodromy. -/
theorem omega_zero_twice {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
    {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y) :
    omega A₃ 0 (omega A₃ 0 Y) = modeScale monodromyPhase (logShift (2*Real.pi*Complex.I) Y) := by
  have h := omega_next (hY.isLogIntertwining_omega 0) (-1)
  have hid := hY.omega_omega 0
  norm_num only [Int.neg_zero,zero_sub] at hid
  rw [show (-1:ℤ)+1=0 from rfl,hid] at h
  exact h

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- Actual full L(0) transport on homogeneous inputs is genuine logarithmic monodromy. -/
theorem L0exp_monodromy_homogeneous (n : ℂ) (k : ℕ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) :
    L0exp N₃ (2*Real.pi*Complex.I)
      (Y.1 n k (L0exp N₁ (-(2*Real.pi*Complex.I)) x) (L0exp N₂ (-(2*Real.pi*Complex.I)) y)) =
      monodromyPhase n • logShift (2*Real.pi*Complex.I) Y.1 n k x y := by
  let s : ℂ := 2*Real.pi*Complex.I
  have hm := Y.2.mem_weight (nilExp_mem_weight N₁ (-s) hx) (nilExp_mem_weight N₂ (-s) hy) n k
  change L0exp N₃ s (Y.1 n k (L0exp N₁ (-s) x) (L0exp N₂ (-s) y)) = _
  rw [L0exp_apply_of_mem N₁ (-s) hx,L0exp_apply_of_mem N₂ (-s) hy]
  simp only [map_smul,LinearMap.smul_apply]
  rw [L0exp_apply_of_mem N₃ s hm,nilExp_logShift_all N₁ N₂ N₃ Y s n k x y,smul_smul,smul_smul]
  congr 1
  rw [← Complex.exp_add,← Complex.exp_add]
  unfold monodromyPhase
  congr 1
  dsimp only [s]
  ring

/-- The genuine logarithmic double skew is actual conformal twist transport. -/
theorem omega_zero_twice_twist :
    omegaEquiv N₂.toWeakModule N₁.toWeakModule N₃.toWeakModule 0
      (omegaEquiv N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule 0 Y) =
    postcompose (twistHom N₃)
      (precompose (branchTurnHom N₁ (-1)) (branchTurnHom N₂ (-1)) Y) := by
  apply Subtype.ext
  rw [show (omegaEquiv N₂.toWeakModule N₁.toWeakModule N₃.toWeakModule 0
      (omegaEquiv N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule 0 Y)).1 =
    omega N₃.toWeakModule 0 (omega N₃.toWeakModule 0 Y.1) from rfl,omega_zero_twice Y.2]
  funext n k
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  simp only [modeScale_apply,postcompose_apply,precompose_apply,twistHom,twist,
    branchTurnHom,branchTurn,LinearEquiv.coe_coe,Int.cast_neg,Int.cast_one]
  change monodromyPhase n • logShift (2*Real.pi*Complex.I) Y.1 n k x y =
    L0exp N₃ (2*Real.pi*Complex.I)
      (Y.1 n k (L0exp N₁ ((-1:ℂ)*(2*Real.pi*Complex.I)) x)
        (L0exp N₂ ((-1:ℂ)*(2*Real.pi*Complex.I)) y))
  rw [neg_one_mul]
  exact (L0exp_monodromy_homogeneous N₁ N₂ N₃ Y n k hx hy).symm

/-- The actual full L(0) exponential at zero is the identity. -/
theorem L0exp_zero_apply {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (x : M) : L0exp N 0 x = x := by
  refine LogFin.induction_on N (C := fun x => L0exp N 0 x=x) x ?_ ?_ ?_
  · intro a x hx
    rw [L0exp_apply_of_mem N 0 hx,zero_mul,Complex.exp_zero,one_smul]
    exact VOA.Huang.LiRegular.expOp_zero (L0nil_locallyNilpotent N) x
  · exact map_zero _
  · intro x y hx hy
    dsimp only at hx hy ⊢
    rw [map_add,hx,hy]

/-- The actual negative branch turn cancels the actual conformal twist. -/
theorem branchTurn_minus_one_twist {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (x : M) : branchTurn N (-1) (twist N x) = x := by
  simp only [branchTurn,twist,Int.cast_neg,Int.cast_one]
  change L0exp N ((-1:ℂ)*(2*Real.pi*Complex.I)) (L0exp N (2*Real.pi*Complex.I) x)=x
  rw [neg_one_mul]
  have h := DFunLike.congr_fun (L0exp_add N (-(2*Real.pi*Complex.I)) (2*Real.pi*Complex.I)) x
  change L0exp N (-(2*Real.pi*Complex.I)) (L0exp N (2*Real.pi*Complex.I) x) = _ at h
  rw [neg_add_cancel,L0exp_zero_apply] at h
  exact h

/-- Genuine all-log balancing of double skew and the actual conformal twist. -/
theorem omega_zero_twice_balancing :
    precompose (twistHom N₁) (twistHom N₂)
      (omegaEquiv N₂.toWeakModule N₁.toWeakModule N₃.toWeakModule 0
        (omegaEquiv N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule 0 Y)) =
      postcompose (twistHom N₃) Y := by
  rw [omega_zero_twice_twist]
  apply Subtype.ext
  funext n k
  ext x y
  change twist N₃ (Y.1 n k (branchTurn N₁ (-1) (twist N₁ x))
      (branchTurn N₂ (-1) (twist N₂ y))) = twist N₃ (Y.1 n k x y)
  rw [branchTurn_minus_one_twist,branchTurn_minus_one_twist]

end
end VOA.LogTensor
