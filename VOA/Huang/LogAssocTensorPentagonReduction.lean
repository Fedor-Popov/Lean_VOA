import VOA.Classification.COne.McRaeM2LogAssociator
import VOA.Classification.COne.McRaeM2TensorFourfoldGeneration

/-! The two actual logarithmic pentagon paths and their exact canonical-mode
comparison. These are concrete maps of the proved tensor objects. Equality
of the paths reduces to the literal three nested canonical coefficients;
this reduction does not assert the remaining analytic sewing identity. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.C2Rigid.LocalInjective
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual nested categorical tensor objects require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The two-associator path across the actual fourfold tensor pentagon. -/
def tensorPentagonShort (N P Q R : LogModuleCat W) :
    tensorObject hC2 (tensorObject hC2 (tensorObject hC2 N P) Q) R ⟶
      tensorObject hC2 N (tensorObject hC2 P (tensorObject hC2 Q R)) :=
  (associatorIso hC2 (tensorObject hC2 N P) Q R).hom ≫
    (associatorIso hC2 N P (tensorObject hC2 Q R)).hom

-- Actual nested categorical tensor objects require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The three-associator path across the actual fourfold tensor pentagon. -/
def tensorPentagonLong (N P Q R : LogModuleCat W) :
    tensorObject hC2 (tensorObject hC2 (tensorObject hC2 N P) Q) R ⟶
      tensorObject hC2 N (tensorObject hC2 P (tensorObject hC2 Q R)) :=
  tensorMorphism hC2 (associatorIso hC2 N P Q).hom (𝟙 R) ≫
    (associatorIso hC2 N (tensorObject hC2 P Q) R).hom ≫
      tensorMorphism hC2 (𝟙 N) (associatorIso hC2 P Q R).hom

-- Actual fourfold coefficient carriers require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Exact canonical-mode reduction for the concrete logarithmic pentagon.
Every tested vector is an actual fourfold canonical coefficient, and these
vectors span the entire genuine fourfold tensor carrier. -/
theorem tensorPentagon_eq_iff_canonical (N P Q R : LogModuleCat W) :
    tensorPentagonLong hC2 N P Q R=tensorPentagonShort hC2 N P Q R ↔
      ∀ n m p (x : N) (y : P) (z : Q) (w : R),
        (tensorPentagonLong hC2 N P Q R).1
          (leftFourCoefficient hC2 N.act P.act N.finiteGeneration P.finiteGeneration
            Q.act Q.finiteGeneration R.act R.finiteGeneration n m p x y z w)=
        (tensorPentagonShort hC2 N P Q R).1
          (leftFourCoefficient hC2 N.act P.act N.finiteGeneration P.finiteGeneration
            Q.act Q.finiteGeneration R.act R.finiteGeneration n m p x y z w) := by
  constructor
  · intro he n m p x y z w
    rw [he]
  · intro h
    apply Subtype.ext
    exact leftFour_linearMap_ext hC2 N.act P.act N.finiteGeneration P.finiteGeneration
      Q.act Q.finiteGeneration R.act R.finiteGeneration h

end VOA.LogTensor.LogModuleCat
