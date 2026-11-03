import VOA.Classification.COne.McRaeM1Cover
import Mathlib.RingTheory.Noetherian.Orzech

/-! A genuine surjective cycle of weak-module morphisms gives an actual
isomorphism on finite-length objects. This algebraic step supports the
associator inverse after actual analytic surjectivity is established. -/
set_option maxSynthPendingDepth 3
namespace VOA.C2Rigid.LocalInjective
open VOA VOA.Classification.COne VOA.Classification.COne.McRaeM1
universe u
variable {V X Y Z : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z] {W : VertexOperatorAlgebra V}

/-- A genuine onto endomorphism of a finite-length weak module is injective,
by its actual mode algebra. No finite-dimensionality of the whole vector
space or semisimplicity is required. -/
theorem weakEnd_injective_of_surjective (A : WeakModule W X)
    (hA : IsFiniteLength (modeAlg A) X) (f : A.Hom A)
    (hf : Function.Surjective f.toLinearMap) : Function.Injective f.toLinearMap := by
  haveI : IsNoetherian (modeAlg A) X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).1
  exact IsNoetherian.injective_of_surjective_endomorphism (endoLinear f) hf

/-- An actual three-object surjective cycle forces its first arrow to be an
isomorphism when its source has finite length. -/
theorem weakCycle_bijective (A : WeakModule W X) (B : WeakModule W Y) (C : WeakModule W Z)
    (hA : IsFiniteLength (modeAlg A) X) (f : A.Hom B) (g : B.Hom C) (h : C.Hom A)
    (hf : Function.Surjective f.toLinearMap) (hg : Function.Surjective g.toLinearMap)
    (hh : Function.Surjective h.toLinearMap) : Function.Bijective f.toLinearMap := by
  let c := homComp h (homComp g f)
  have hc : Function.Surjective c.toLinearMap := hh.comp (hg.comp hf)
  have hi := weakEnd_injective_of_surjective A hA c hc
  refine ⟨fun x y hxy => hi ?_,hf⟩
  change h.toLinearMap (g.toLinearMap (f.toLinearMap x))=
    h.toLinearMap (g.toLinearMap (f.toLinearMap y))
  rw [hxy]

end VOA.C2Rigid.LocalInjective
