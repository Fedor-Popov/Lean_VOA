import VOA.Classification.COne.McRaeM2LogAssociator
import VOA.Modules.LogTensorPzPointEvaluation

/-! The five actual logarithmic tensor expansions in the common pentagon
chart: physical insertion points 1+s+r, 1+s, 1, 0. All point blocks retain
their genuine logarithmic sums and the chosen branches. Convergence and
sewing are substantive theorems proved separately for these literal terms. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 2000000
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The five genuine parenthesizations in the actual logarithmic pentagon. -/
inductive FiveTree where
  | left | inner | middle | right | pair
  deriving DecidableEq

/-- Each shape is the actual iterated universal tensor object. -/
def fivePointObject (N P Q R : LogModuleCat W) : FiveTree → LogModuleCat W
  | .left => tensorObject hC2 (tensorObject hC2 (tensorObject hC2 N P) Q) R
  | .inner => tensorObject hC2 (tensorObject hC2 N (tensorObject hC2 P Q)) R
  | .middle => tensorObject hC2 N (tensorObject hC2 (tensorObject hC2 P Q) R)
  | .right => tensorObject hC2 N (tensorObject hC2 P (tensorObject hC2 Q R))
  | .pair => tensorObject hC2 (tensorObject hC2 N P) (tensorObject hC2 Q R)

/-- The genuine chosen-branch evaluation of the actual canonical tensor operator. -/
abbrev pointTensor (N P : LogModuleCat W) (ell : ℂ) :
    N →ₗ[ℂ] P →ₗ[ℂ] Completion (tensorObject hC2 N P).act :=
  evaluatePoint N.act P.act (tensorObject hC2 N P).act
    (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration) ell

/-- A genuine generalized-weight block of the actual canonical tensor evaluation. -/
abbrev pointTensorBlock (N P : LogModuleCat W) (ell a b c : ℂ) :
    N.act.weight a →ₗ[ℂ] P.act.weight b →ₗ[ℂ] (tensorObject hC2 N P).act.weight c :=
  pointEvaluationBlock N.act P.act (tensorObject hC2 N P).act
    (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration) ell a b c

/-- Every scalar term is a literal composition of the genuine point blocks.
The two actual generalized internal weights are gamma and delta. -/
def fivePointTerm (N P Q R : LogModuleCat W) (tree : FiveTree)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ) (γ δ : ℂ) : ℂ :=
  match tree with
  | .left =>
      let T := tensorObject hC2 N P
      let L := tensorObject hC2 T Q
      let u := pointTensor hC2 N P (Complex.log r) x y γ
      let v := pointTensorBlock hC2 T Q (Complex.log s) γ c δ u z
      f ((pointTensorBlock hC2 L R 0 δ d β v w : (tensorObject hC2 L R).carrier))
  | .inner =>
      let T := tensorObject hC2 P Q
      let L := tensorObject hC2 N T
      let u := pointTensor hC2 P Q (Complex.log s) y z γ
      let v := pointTensorBlock hC2 N T (Complex.log (s+r)) a γ δ x u
      f ((pointTensorBlock hC2 L R 0 δ d β v w : (tensorObject hC2 L R).carrier))
  | .middle =>
      let T := tensorObject hC2 P Q
      let L := tensorObject hC2 T R
      let u := pointTensor hC2 P Q (Complex.log s) y z γ
      let v := pointTensorBlock hC2 T R 0 γ d δ u w
      f ((pointTensorBlock hC2 N L (Complex.log (1+s+r)) a δ β x v : (tensorObject hC2 N L).carrier))
  | .right =>
      let T := tensorObject hC2 Q R
      let L := tensorObject hC2 P T
      let u := pointTensor hC2 Q R 0 z w γ
      let v := pointTensorBlock hC2 P T (Complex.log (1+s)) b γ δ y u
      f ((pointTensorBlock hC2 N L (Complex.log (1+s+r)) a δ β x v : (tensorObject hC2 N L).carrier))
  | .pair =>
      let T := tensorObject hC2 N P
      let L := tensorObject hC2 Q R
      let u := pointTensor hC2 N P (Complex.log r) x y γ
      let v := pointTensor hC2 Q R 0 z w δ
      f ((pointTensorBlock hC2 T L (Complex.log (1+s)) γ δ β u v : (tensorObject hC2 T L).carrier))

/-- The full true two-weight completed expansion at a pentagon vertex. -/
def fivePointEvaluation (N P Q R : LogModuleCat W) (tree : FiveTree)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ) : ℂ :=
  ∑' p : ℂ × ℂ,fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f p.1 p.2

/-- Both real sewing coordinates lie in the literal common pentagon region. -/
def FivePointDomain (r s : ℝ) : Prop := 0<r ∧ r<s ∧ r+s<1

end VOA.Huang.LogAssocFivePoint
