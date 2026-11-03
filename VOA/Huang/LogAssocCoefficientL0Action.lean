import VOA.Modules.LogTensorPzL0
import VOA.Modules.LogTensorPzNilExponential
import VOA.Modules.LogTensorUniformNil

/-! Genuine conformal zero mode on the full algebraic tensor dual.
The actual source Jordan operators commute with this operator; no
semisimple-source equation is imposed. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open VOA.Huang.PzTensorRho
open Module (End)
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]

/-- The actual conformal zero mode of the P(1) dual action. -/
def dualL0 (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) :
    End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) :=
  tauEnd N₁.toWeakModule N₂.toWeakModule 2 W.conformalVector 1

/-- The full conformal action includes the insertion-point translation. -/
theorem tau_conformal (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (F : BilinearDual (M₁ := M₁) (M₂ := M₂)) (x : M₁) (y : M₂) :
    tauHat A₁ A₂ 2 W.conformalVector 1 F x y =
      F x (L0 A₂ y) + F (Lm1 A₁ x) y + F (L0 A₁ x) y := by
  unfold tauHat
  rw [show (2:ℤ).toNat+1=3 from rfl]
  rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_one]
  rw [show (1:ℕ)=0+1 from rfl,show (2:ℕ)=1+1 from rfl,
    C2Rigid.L_one_pow_succ_conformalVector W 0,C2Rigid.L_one_pow_succ_conformalVector W 1]
  simp only [rhoL_zero_state,smul_zero,add_zero,Nat.factorial_zero,Nat.cast_one,
    inv_one,one_smul,pow_zero,Module.End.one_apply]
  norm_num
  exact rho_conformal_one A₁ A₂ F x y

@[simp] theorem dualL0_apply (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (F : BilinearDual (M₁ := M₁) (M₂ := M₂)) (x : M₁) (y : M₂) :
    dualL0 N₁ N₂ F x y = F x (N₂.L0op y)+F (Lm1 N₁.toWeakModule x) y+F (N₁.L0op x) y := by
  rw [dualL0,tauEnd_apply,tau_conformal]
  rfl

/-- Actual precomposition in the first source slot of the algebraic tensor dual. -/
def preFirst (E : End ℂ M₁) : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) where
  toFun F := LinearMap.comp F E
  map_add' F G := by ext x y; rfl
  map_smul' s F := by ext x y; rfl

/-- Actual precomposition in the second source slot. -/
def preSecond (E : End ℂ M₂) : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) where
  toFun F := F.compl₂ E
  map_add' F G := by ext x y; rfl
  map_smul' s F := by ext x y; rfl

@[simp] theorem preFirst_apply (E : End ℂ M₁) (F : BilinearDual (M₁ := M₁) (M₂ := M₂))
    (x : M₁) (y : M₂) : preFirst E F x y=F (E x) y := rfl
@[simp] theorem preSecond_apply (E : End ℂ M₂) (F : BilinearDual (M₁ := M₁) (M₂ := M₂))
    (x : M₁) (y : M₂) : preSecond E F x y=F x (E y) := rfl

@[simp] theorem preFirst_pow_apply (E : End ℂ M₁) (j : ℕ)
    (F : BilinearDual (M₁ := M₁) (M₂ := M₂)) (x : M₁) (y : M₂) :
    (preFirst E^j) F x y=F ((E^j) x) y := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,preFirst_apply,ih]
    rw [← Module.End.mul_apply,← pow_succ,pow_succ',Module.End.mul_apply]

@[simp] theorem preSecond_pow_apply (E : End ℂ M₂) (j : ℕ)
    (F : BilinearDual (M₁ := M₁) (M₂ := M₂)) (x : M₁) (y : M₂) :
    (preSecond E^j) F x y=F x ((E^j) y) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,preSecond_apply,ih]
    rw [← Module.End.mul_apply,← pow_succ,pow_succ',Module.End.mul_apply]

/-- Two source precomposition operators commute when their source endomorphisms do. -/
theorem preFirst_commute {E F : End ℂ M₁} (h : Commute E F) :
    Commute (preFirst (M₂ := M₂) E) (preFirst F) := by
  ext G x y
  change G (F (E x)) y=G (E (F x)) y
  rw [← Module.End.mul_apply,← Module.End.mul_apply,h.eq]

/-- Source precomposition in separate slots always commutes. -/
theorem preFirstSecond_commute (E : End ℂ M₁) (F : End ℂ M₂) :
    Commute (preFirst E) (preSecond F) := by
  ext G x y
  rfl

/-- The genuine first source nilpotent operator commutes with the full P(1) L(0). -/
theorem dualL0_commute_firstNil (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) :
    Commute (dualL0 N₁ N₂) (preFirst N₁.L0nil) := by
  ext F x y
  simp only [Module.End.mul_apply,dualL0_apply,preFirst_apply]
  have h0 := DFunLike.congr_fun (L0nil_comm_mode N₁ W.conformalVector 1) x
  have hm := DFunLike.congr_fun (L0nil_comm_mode N₁ W.conformalVector 0) x
  change N₁.L0nil (N₁.L0op x)=N₁.L0op (N₁.L0nil x) at h0
  change N₁.L0nil (Lm1 N₁.toWeakModule x)=Lm1 N₁.toWeakModule (N₁.L0nil x) at hm
  rw [h0,hm]

/-- The genuine second source nilpotent operator commutes with the full P(1) L(0). -/
theorem dualL0_commute_secondNil (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) :
    Commute (dualL0 N₁ N₂) (preSecond N₂.L0nil) := by
  ext F x y
  simp only [Module.End.mul_apply,dualL0_apply,preSecond_apply]
  have h0 := DFunLike.congr_fun (L0nil_comm_mode N₂ W.conformalVector 1) y
  change N₂.L0nil (N₂.L0op y)=N₂.L0op (N₂.L0nil y) at h0
  rw [h0]

/-- Genuine finite generation supplies global nilpotence on the actual tensor dual. -/
theorem firstNil_isNilpotent_of_finGen (N₁ : LogVModule W M₁) (hfg : FinGen N₁.toWeakModule) :
    IsNilpotent (preFirst (M₂ := M₂) N₁.L0nil) := by
  obtain ⟨j,hj⟩ := L0nil_isNilpotent_of_finGen N₁ hfg
  refine ⟨j,?_⟩
  ext F x y
  rw [preFirst_pow_apply,hj,LinearMap.zero_apply,map_zero,LinearMap.zero_apply]
  rfl

/-- The same genuine global bound applies in the second source slot. -/
theorem secondNil_isNilpotent_of_finGen (N₂ : LogVModule W M₂) (hfg : FinGen N₂.toWeakModule) :
    IsNilpotent (preSecond (M₁ := M₁) N₂.L0nil) := by
  obtain ⟨j,hj⟩ := L0nil_isNilpotent_of_finGen N₂ hfg
  refine ⟨j,?_⟩
  ext F x y
  rw [preSecond_pow_apply,hj,LinearMap.zero_apply,map_zero]
  rfl

end
end VOA.Huang.LogAssocCoefficientL0
