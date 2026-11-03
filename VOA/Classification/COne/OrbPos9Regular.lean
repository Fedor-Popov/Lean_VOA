import VOA.Classification.COne.OrbPos9Reduction

/-! # A genuine simple extension module and its untwisted realization

The regular algebra module is simple because the ambient VOA V₂ is simple.
It gives an actual test object for the open simple-action dictionary, and a
simple target of induction for the vacuum U-module. No general completeness
claim is inferred from this one object.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos9
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.HKLRational
open VOA.Huang.TensorCat.RepPackaging
open CategoryTheory CategoryTheory.Limits MonoidalCategory OrbPos2

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR)

set_option maxHeartbeats 800000 in
-- The concrete lattice carrier requires additional elaboration time.
/-- The canonical regular algebra module is genuinely simple, although its
underlying U-module can be reducible. -/
def regularSimpleAction :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    SimpleAction (ambient G) := by
  let F := fusionChoice_pbw hSR
  let A := ambient G
  letI := monoidalCategoryOfStronglyRational_pbw F hSR
  letI := E.monoid
  refine ⟨A, MonObj.mul, ⟨MonObj.one_mul A, MonObj.mul_assoc A⟩, ?_, ?_⟩
  · intro hz
    exact (V2m_stronglyRational 1 le_rfl).simple.vacuum_ne_zero
      (congrArg (fun f : A ⟶ A => f.val (V2m 1 le_rfl).vacuum) hz)
  · intro Y aY _ f hf hm
    have hs : ∀ v k x, x ∈ LinearMap.range f.val →
        (V2m 1 le_rfl).smul v k x ∈ LinearMap.range f.val := by
      intro v k x hx
      obtain ⟨y, rfl⟩ := hx
      refine ⟨aY.val ((F A Y).intertwiner.val (k : ℂ) v y), ?_⟩
      have he := congrArg (fun t : tensorObj F A Y ⟶ A =>
        t.val ((F A Y).intertwiner.val (k : ℂ) v y)) hf
      change (MonObj.mul : tensorObj F A A ⟶ A).val
        ((tensorHom F (𝟙 A) f).val ((F A Y).intertwiner.val (k : ℂ) v y)) = _ at he
      rw [E.mul_eq, tensorHom_intertwiner, Ordinary.id_apply,
        ambientMultiplication_intertwiner, moduleModes_apply_intCast] at he
      exact he.symm
    let P : WeakModule.Submodule' (adjointModule (V2m 1 le_rfl)).toWeakModule :=
      ⟨LinearMap.range f.val, hs⟩
    have hi := (isSimple_iff_adjointModule_isIrreducible (V2m 1 le_rfl)).mp
      (V2m_stronglyRational 1 le_rfl).simple
    rcases hi.2 P with h | h
    · exact Or.inl (Subtype.ext (LinearMap.range_eq_bot.mp h))
    · exact Or.inr ((isoOfBijective f
        ⟨(mono_iff_injective f).mp hm, LinearMap.range_eq_top.mp h⟩).isIso_hom)

/-- The simple-action dictionary is proved on this concrete nonzero object. -/
theorem regularSimpleAction_sector :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    SectorRealization G (regularSimpleAction G hSR E).obj := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  refine Or.inl ⟨_, inferInstance, inferInstance, adjointModule (V2m 1 le_rfl),
    (isSimple_iff_adjointModule_isIrreducible _).mp
      (V2m_stronglyRational 1 le_rfl).simple, ?_⟩
  exact ⟨{ toLinearEquiv := LinearEquiv.refl ℂ _
           map_act := fun _ _ _ => rfl }⟩

/-- Induction of the vacuum has a nonzero map to the regular simple algebra module.
This is a concrete case of `ExceptionalFreeSimpleTargets`, not its general proof. -/
theorem vacuum_free_simple_target :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    ∃ Q : SimpleAction (ambient G), ∃ q : ambient G ⊗ vacuumObject ⟶ Q.obj,
      IsLinear (freeAction vacuumObject) Q.act q ∧ q ≠ 0 := by
  let F := fusionChoice_pbw hSR
  let A := ambient G
  letI := monoidalCategoryOfStronglyRational_pbw F hSR
  letI := E.monoid
  refine ⟨regularSimpleAction G hSR E, (ρ_ A).hom, ?_, ?_⟩
  · change (A ◁ (ρ_ A).hom) ≫ MonObj.mul =
      ((α_ A A (𝟙_ _)).inv ≫ (MonObj.mul ▷ (𝟙_ _))) ≫ (ρ_ A).hom
    rw [Category.assoc, MonoidalCategory.rightUnitor_naturality]
    monoidal
  · intro hz
    have he := congrArg (fun t : A ⟶ A => t.val (V2m 1 le_rfl).vacuum)
      (ρ_ A).inv_hom_id
    change (ρ_ A).hom.val ((ρ_ A).inv.val (V2m 1 le_rfl).vacuum) = _ at he
    rw [hz] at he
    exact (V2m_stronglyRational 1 le_rfl).simple.vacuum_ne_zero he.symm

end VOA.Classification.COne.OrbPos9
