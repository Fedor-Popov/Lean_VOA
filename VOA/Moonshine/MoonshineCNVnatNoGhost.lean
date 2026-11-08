import VOA.Moonshine.MoonshineCNVnatLongitudinalQuotient
import VOA.Moonshine.MoonshineCNStringComparison

/-! # The Aut(V♮)-equivariant no-ghost isometry at nonzero momentum

The norm convention is `2*x*y`; the matter weight is exactly `1-x*y`.
Every form and every operator here is the concrete one on `Vnat ⊗ hypFock`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster SimpleNat
open scoped TensorProduct

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup

local instance stringSectorWeightAddCommGroup (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) (N : ℤ) :
    AddCommGroup ((stringSector x y h).wt N) := Submodule.addCommGroup _

local instance stringSectorSliceAddCommGroup (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0)
    (U : Submodule ℂ (Vnat ⊗[ℂ] hypFock)) (N : ℤ) :
    AddCommGroup ((stringSector x y h).weightSlice U N) := Submodule.addCommGroup _

/-- The transverse space at any weight is the matter space at the shifted weight. -/
def stringSectorTransverseMatterEquiv (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) (N : ℤ) :
    (stringSector x y h).weightSlice (stringSector x y h).transverse N ≃ₗ[ℂ]
      VnatVOA.grading (N - x * y) :=
  ((stringSector x y h).transverseKQuotientEquiv (stringSector_lightConeSplit x y h) N).trans
    (vnatKVacuumQuotientEquiv x y (stringSectorFamily x y h) N)

/-- The actual physical radical quotient at weight one, with no unproved data as inputs. -/
def stringSectorNoGhostEquiv (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    (stringSector x y h).weightRadicalQuotient (stringSector x y h).physical 1 ≃ₗ[ℂ]
      VnatVOA.grading (1 - x * y) :=
  ((stringSector x y h).physicalKQuotientEquiv (stringSector_charge x y h)
    (stringSector_lightConeSplit x y h)).trans
      (vnatKVacuumQuotientEquiv x y (stringSectorFamily x y h) 1)

theorem stringSectorNoGhostEquiv_isometry (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0)
    (u v : (stringSector x y h).weightRadicalQuotient (stringSector x y h).physical 1) :
    natForm (stringSectorNoGhostEquiv x y h u) (stringSectorNoGhostEquiv x y h v) =
      (stringSector x y h).radicalQuotientForm (stringSector x y h).physical 1 u v := by
  exact (vnatKVacuumQuotientEquiv_isometry x y (stringSectorFamily x y h) 1 _ _).trans
    ((stringSector x y h).physicalKQuotientEquiv_isometry (stringSector_charge x y h)
      (stringSector_lightConeSplit x y h) u v)

theorem stringSectorNoGhostEquiv_equivariant (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0)
    (g : AutVnat)
    (u : (stringSector x y h).weightRadicalQuotient (stringSector x y h).physical 1) :
    stringSectorNoGhostEquiv x y h
      ((stringSectorAction x y h).stableWeightQuotientAction _
        (stringSectorAction x y h).action_preserves_physical 1 g u) =
      GriessAut.autRestrict g (1 - x * y) (stringSectorNoGhostEquiv x y h u) := by
  simp only [stringSectorNoGhostEquiv, LinearEquiv.trans_apply]
  rw [(stringSectorAction x y h).physicalKQuotientEquiv_equivariant]
  exact vnatKVacuumQuotientEquiv_equivariant x y (stringSectorFamily x y h) 1 g _

end VOA.Moonshine.ConwayNorton
