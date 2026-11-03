import VOA.Modules.LogTensorPzNilCovariance
import Mathlib.LinearAlgebra.Trace

/-! Genuine logarithmic zero-mode traces on finite generalized weight spaces.
The Jordan commutator preserves the full logarithmic recurrence; no ordinary,
rationality, convergence or modularity premise is used in these identities. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogGenusOne
open VOA VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V U M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V}
variable (N₀ : LogVModule W U) (N : LogVModule W M)
  (Y : LogIntertwiningOperator N₀.toWeakModule N.toWeakModule N.toWeakModule)

/-- The actual degree-zero log mode acts on every true generalized weight piece. -/
def zeroModePiece (a b : ℂ) (k : ℕ) (x : N₀.weight a) : Module.End ℂ (N.weight b) :=
  ((Y.1 (a-1) k x.val).comp (N.weight b).subtype).codRestrict (N.weight b) (fun y => by
    have h := Y.2.mem_weight x.property y.property (a-1) k
    convert h using 1 <;> ring)

@[simp] theorem zeroModePiece_coe (a b : ℂ) (k : ℕ) (x : N₀.weight a) (y : N.weight b) :
    (zeroModePiece N₀ N Y a b k x y : M)=Y.1 (a-1) k x.val y.val := rfl

/-- The genuine source/target Jordan parts satisfy the coupled all-log operator identity. -/
theorem zeroModePiece_nil_commutator (a b : ℂ) (k : ℕ) (x : N₀.weight a) :
    weightNil N b*zeroModePiece N₀ N Y a b k x-
      zeroModePiece N₀ N Y a b k x*weightNil N b-
      zeroModePiece N₀ N Y a b k (weightNil N₀ a x)=
        ((k : ℂ)+1) • zeroModePiece N₀ N Y a b (k+1) x := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  have h := congrArg (fun B => B x.val y.val) (nilDefect_logCoeff N₀ N N Y (a-1) k)
  simp only [nilDefect,bilinearDefect_apply,LinearMap.smul_apply] at h
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Submodule.coe_sub,SetLike.val_smul,weightNil,LinearMap.restrict_apply,zeroModePiece_coe]
  convert h using 1 <;> module

/-- Trace of the genuine logarithmic zero mode, on its actual finite weight space. -/
def logModeTrace (a b : ℂ) (k : ℕ) (x : N₀.weight a) : ℂ :=
  letI := N.finrank b
  LinearMap.trace ℂ (N.weight b) (zeroModePiece N₀ N Y a b k x)

/-- Taking the actual trace kills the target Jordan commutator and retains
exactly the source Jordan contribution to the next logarithmic coefficient. -/
theorem logModeTrace_succ (a b : ℂ) (k : ℕ) (x : N₀.weight a) :
    ((k : ℂ)+1)*logModeTrace N₀ N Y a b (k+1) x=
      -logModeTrace N₀ N Y a b k (weightNil N₀ a x) := by
  haveI := N.finrank b
  have h := congrArg (LinearMap.trace ℂ (N.weight b))
    (zeroModePiece_nil_commutator N₀ N Y a b k x)
  rw [map_sub,map_sub,map_smul,LinearMap.trace_mul_comm,
    sub_self,zero_sub] at h
  exact h.symm

/-- Every logarithmic trace coefficient is the source Jordan coefficient,
with the exact factorial and sign. -/
theorem logModeTrace_factorial (a b : ℂ) (k : ℕ) (x : N₀.weight a) :
    (k.factorial : ℂ)*logModeTrace N₀ N Y a b k x=
      (-1 : ℂ)^k*logModeTrace N₀ N Y a b 0 ((weightNil N₀ a^k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hs := logModeTrace_succ N₀ N Y a b k x
    have hi := ih (weightNil N₀ a x)
    have hp : (weightNil N₀ a^k) (weightNil N₀ a x)=(weightNil N₀ a^(k+1)) x := by
      rw [pow_succ,Module.End.mul_apply]
    rw [hp] at hi
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hsign : (-1 : ℂ)^(k+1)=-(-1 : ℂ)^k := by rw [pow_succ]; ring
    rw [hsign]
    linear_combination (k.factorial : ℂ)*hs-hi

/-- Vanishing of the source Jordan power forces the actual trace coefficient to vanish. -/
theorem logModeTrace_zero_of_jordan (a b : ℂ) (k : ℕ) (x : N₀.weight a)
    (hk : (weightNil N₀ a^k) x=0) : logModeTrace N₀ N Y a b k x=0 := by
  have h := logModeTrace_factorial N₀ N Y a b k x
  rw [hk] at h
  have hz : logModeTrace N₀ N Y a b 0 0=0 := by
    have hp : zeroModePiece N₀ N Y a b 0 0=0 := by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      simp [zeroModePiece]
    simp only [logModeTrace,hp,map_zero]
  rw [hz,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero k)

/-- Honest L0 eigenvectors have no higher logarithmic trace coefficients, even
when the traced module itself has genuine Jordan blocks. -/
theorem logModeTrace_no_higher_of_source_eigen (a b : ℂ) (k : ℕ) (x : N₀.weight a)
    (hx : weightNil N₀ a x=0) : logModeTrace N₀ N Y a b (k+1) x=0 := by
  apply logModeTrace_zero_of_jordan
  rw [pow_succ,Module.End.mul_apply,hx,map_zero]

end VOA.Huang.LogGenusOne
