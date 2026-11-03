import VOA.Classification.COne.OrbPos10Simple
import VOA.Huang.HKLRationalOrdinary

/-! # Simple targets of exceptional induction

Strong rationality supplies underlying complements and finite Hom spaces.
Neither positivity of the fixed VOA nor rigidity is used.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos10
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat VOA.Huang.HKLRational
open VOA.Huang.TensorCat.RepPackaging CategoryTheory CategoryTheory.Limits MonoidalCategory
open OrbPos9 OrbPos2
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Every ordinary-module monomorphism over a strongly rational VOA splits. -/
theorem ordinary_mono_splits (hW : StronglyRational W) {Y X : Ordinary W}
    (f : Y ⟶ X) (hf : Mono f) : ∃ r : X ⟶ Y, f ≫ r = 𝟙 Y := by
  let P := rangeSub f.property
  obtain ⟨Q, hQ⟩ := ordinary_complements hW X P
  have hi := (mono_iff_injective f).mp hf
  let e := LinearEquiv.ofInjective f.val hi
  let pr := P.carrier.projectionOnto Q.carrier hQ
  let r : X ⟶ Y := ⟨e.symm.toLinearMap.comp pr, by
    intro a n x
    apply hi
    change f.val (e.symm (pr (mode (X.isMod.YM a) n x))) =
      f.val (mode (Y.isMod.YM a) n (e.symm (pr x)))
    rw [f.property]
    have he (z : P.carrier) : f.val (e.symm z) = z.val :=
      congrArg Subtype.val (e.apply_symm_apply z)
    rw [he, he]
    exact projectionOnto_comm hQ _
      (fun y hy => P.act_mem a n hy) (fun y hy => Q.act_mem a n hy) x⟩
  refine ⟨r, Ordinary.hom_ext _ _ (fun y => ?_)⟩
  change e.symm (pr (f.val y)) = y
  have he : pr (f.val y) = e y := Submodule.projectionOnto_apply_left hQ (e y)
  rw [he, e.symm_apply_apply]

/-- General VOA specialization of the simple quotient theorem. -/
theorem ordinary_action_simple_quotient (hW : StronglyRational W) (F : FusionChoice W) :
    letI := monoidalCategoryOfStronglyRational_pbw F hW
    ∀ (A : Ordinary W) [MonObj A] (X : Ordinary W) (aX : A ⊗ X ⟶ X),
      IsLeftAct aX → 𝟙 X ≠ 0 →
      ∃ Q : SimpleAction A, ∃ q : X ⟶ Q.obj, IsLinear aX Q.act q ∧ Epi q := by
  letI := monoidalCategoryOfStronglyRational_pbw F hW
  letI := VOA.Huang.TensorCat.BraidRibbon.monoidalPreadditive_pbw F hW
  letI : ∀ X Y : Ordinary W, FiniteDimensional ℂ (X ⟶ Y) :=
    finiteDimensional_hom_pbw hW
  intro A _ X aX hX hn
  exact exists_simple_quotient (fun f hf => ordinary_mono_splits hW f hf) X aX hX hn

/-- The full simple-target obligation. -/
theorem exceptionalFreeSimpleTargets : ExceptionalFreeSimpleTargets := by
  intro G hG hSR E X hX
  let F := fusionChoice_pbw hSR
  letI := monoidalCategoryOfStronglyRational_pbw F hSR
  letI := E.monoid
  letI := exceptionalV2Group_finite hG
  have hn : 𝟙 (ambient G ⊗ X) ≠ 0 := by
    intro hz
    have hi := inductionUnit_injective G F X
    have hall : ∀ x : X.carrier, x = 0 := by
      intro x
      apply hi
      have he := congrArg (fun k : ambient G ⊗ X ⟶ ambient G ⊗ X =>
        k.val ((inductionUnit G F X).val x)) hz
      simpa only [Ordinary.id_apply, LinearMap.zero_apply, map_zero] using he
    letI := hX.1
    obtain ⟨x, hx⟩ := exists_ne (0 : X.carrier)
    exact hx (hall x)
  obtain ⟨Q, q, hq, he⟩ := ordinary_action_simple_quotient hSR F (ambient G)
    (ambient G ⊗ X) (freeAction X) (freeAction_laws X) hn
  refine ⟨Q, q, hq, ?_⟩
  intro hz
  letI := he
  apply Q.nonzero
  apply (cancel_epi q).mp
  simp [hz]

/-- DRX needs only the simple-action twisted dictionary. -/
theorem exceptionalDRXEmbedding_of_simpleActionTwisted
    (hTwisted : ExceptionalSimpleActionTwisted) : ExceptionalDRXEmbedding :=
  exceptionalDRXEmbedding_of_simple_targets_twisted exceptionalFreeSimpleTargets hTwisted

/-- B5 needs only the simple-action twisted dictionary. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_simpleActionTwisted
    (hTwisted : ExceptionalSimpleActionTwisted) : ExceptionalOrbifoldPositiveWeightsFact :=
  OrbPos8.exceptionalOrbifoldPositiveWeightsFact_of_drx
    (exceptionalDRXEmbedding_of_simpleActionTwisted hTwisted)

end VOA.Classification.COne.OrbPos10
