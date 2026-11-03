import VOA.Huang.LogGenusOneTraceModes
import VOA.Modules.LogTensorContraL0Exp

/-! Actual L(0) transport on finite generalized weight spaces and honest
module zero-mode traces. The genuine target Jordan part is retained in the
operator and eliminated from these traces by proved nilpotent trace algebra.
Convergence and modular transformation are separate analytic statements. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogGenusOne
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open Module (End)
open scoped BigOperators
universe u
local instance (X : Type*) [AddCommGroup X] [Module ℂ X] : Module ℚ X :=
  Module.restrictScalars ℚ ℂ X
local instance (X : Type*) [AddCommGroup X] [Module ℂ X] : IsScalarTower ℚ ℂ X :=
  IsScalarTower.restrictScalars ℚ ℂ X

/-- Genuine nilpotent transport has no additional ordinary trace terms
against a commuting operator. -/
theorem trace_mul_nilExp {X : Type u} [AddCommGroup X] [Module ℂ X]
    (E J : End ℂ X) (hJ : IsNilpotent J) (hE : Commute E J) (s : ℂ) :
    LinearMap.trace ℂ X (E*IsNilpotent.exp (s•J))=LinearMap.trace ℂ X E := by
  have hS := hJ.smul s
  have he : Commute E (IsNilpotent.exp (s•J)) := by
    have hc := Module.End.commute_exp_left_of_commute hS hS
      (show (s•J) ∘ₗ E=E ∘ₗ (s•J) from (hE.smul_right s).eq.symm)
    exact hc.symm
  have hn : IsNilpotent (IsNilpotent.exp (s•J)-algebraMap ℂ (End ℂ X) 1) := by
    simpa only [map_one] using IsNilpotent.isNilpotent_exp_sub_one hS
  simpa only [Module.End.mul_eq_comp,one_mul] using
    LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (1 : ℂ) he hn

variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The literal actual L(0) exponential on a true generalized weight block. -/
def weightL0Exp (N : LogVModule W M) (b s : ℂ) : End ℂ (N.weight b) :=
  Complex.exp (s*b) • IsNilpotent.exp (s•weightNil N b)

/-- This block operator is exactly the restriction of genuine module L(0)
transport, including all target Jordan terms. -/
theorem weightL0Exp_coe (N : LogVModule W M) (b s : ℂ) (y : N.weight b) :
    (weightL0Exp N b s y : M)=L0exp N s y := by
  rw [weightL0Exp,LinearMap.smul_apply,SetLike.val_smul,exp_weightNil_coe,
    L0exp_apply_of_mem N s y.2]

/-- The actual character trace on a finite generalized block is its true
weight scalar times the dimension, even when its L(0) is not semisimple. -/
theorem trace_weightL0Exp (N : LogVModule W M) (b s : ℂ) :
    LinearMap.trace ℂ (N.weight b) (weightL0Exp N b s)=
      Complex.exp (s*b)*(Module.finrank ℂ (N.weight b) : ℂ) := by
  haveI := N.finrank b
  have ht := trace_mul_nilExp (1 : End ℂ (N.weight b)) (weightNil N b)
    (weightNil_nilpotent N b) (Commute.one_left _) s
  simp only [one_mul] at ht
  rw [weightL0Exp,map_smul,smul_eq_mul,ht]
  exact congrArg (fun c : ℂ => Complex.exp (s*b)*c) (LinearMap.trace_id ℂ (N.weight b))

/-- The genuine module zero mode of a homogeneous VOA state preserves every
actual generalized weight block. -/
def moduleZeroModePiece (N : LogVModule W M) {d : ℤ} {v : V}
    (hv : v∈W.grading d) (b : ℂ) : End ℂ (N.weight b) :=
  ((mode (N.YM v) (d-1)).comp (N.weight b).subtype).codRestrict (N.weight b) (fun y => by
    have h := N.mode_mem_weight hv y.2 (d-1)
    convert h using 1 <;> push_cast <;> ring)

@[simp] theorem moduleZeroModePiece_coe (N : LogVModule W M) {d : ℤ} {v : V}
    (hv : v∈W.grading d) (b : ℂ) (y : N.weight b) :
    (moduleZeroModePiece N hv b y : M)=mode (N.YM v) (d-1) y := rfl

/-- Actual VOA modes commute with the genuine target Jordan part. -/
theorem moduleZeroModePiece_commute_nil (N : LogVModule W M) {d : ℤ} {v : V}
    (hv : v∈W.grading d) (b : ℂ) :
    Commute (moduleZeroModePiece N hv b) (weightNil N b) := by
  ext y
  change mode (N.YM v) (d-1) (N.L0nil y)=N.L0nil (mode (N.YM v) (d-1) y)
  exact (DFunLike.congr_fun (L0nil_comm_mode N v (d-1)) y.val).symm

/-- The literal genus-one module trace term, with the genuine L(0) transport. -/
def moduleTraceTerm (N : LogVModule W M) {d : ℤ} {v : V}
    (hv : v∈W.grading d) (b s : ℂ) : ℂ :=
  LinearMap.trace ℂ (N.weight b) (moduleZeroModePiece N hv b*weightL0Exp N b s)

/-- Honest module zero-mode trace terms have the precise scalar weight
factor. This is an identity of the actual operators, without ordinary-module
or rationality assumptions. -/
theorem moduleTraceTerm_eq (N : LogVModule W M) {d : ℤ} {v : V}
    (hv : v∈W.grading d) (b s : ℂ) :
    moduleTraceTerm N hv b s=Complex.exp (s*b)*
      LinearMap.trace ℂ (N.weight b) (moduleZeroModePiece N hv b) := by
  rw [moduleTraceTerm,weightL0Exp,mul_smul_comm,map_smul,smul_eq_mul,
    trace_mul_nilExp _ _ (weightNil_nilpotent N b) (moduleZeroModePiece_commute_nil N hv b)]

end VOA.Huang.LogGenusOne
