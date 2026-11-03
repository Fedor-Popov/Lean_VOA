import VOA.Huang.RepPackagingSemisimple

/-! Completeness of the simple label dictionary and the scalar endomorphism theorem. -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA CategoryTheory CategoryTheory.Limits
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Categorical simplicity detects the usual VOA-module irreducibility. -/
theorem irreducible_of_simple (X : Ordinary W) [Simple X] : X.isMod.IsIrreducible := by
  have hn : Nontrivial X.carrier := by
    by_contra h
    haveI : Subsingleton X.carrier := not_nontrivial_iff_subsingleton.mp h
    exact id_nonzero X (Ordinary.hom_ext _ _ fun x => Subsingleton.elim _ _)
  refine ⟨hn, fun P => ?_⟩
  let S := Ordinary.of (X.isMod.submodule P)
  let i : S ⟶ X := ⟨P.carrier.subtype, fun _ _ _ => rfl⟩
  letI : Mono i := (mono_iff_injective i).mpr P.carrier.subtype_injective
  by_cases hz : i = 0
  · left
    apply bot_unique
    intro x hx
    exact congrArg (fun f : S ⟶ X => f.val ⟨x, hx⟩) hz
  · right
    letI := isIso_of_mono_of_nonzero hz
    have hs := (epi_iff_surjective i).mp inferInstance
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hs x
    exact hy ▸ y.property

theorem simple_iff_irreducible (X : Ordinary W) : Simple X ↔ X.isMod.IsIrreducible :=
  ⟨fun h => @irreducible_of_simple _ _ _ _ X h, simple_of_irreducible X⟩

/-- Every categorical simple is isomorphic to one and only one chosen module. -/
theorem simple_iff_iso_module (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (X : Ordinary W) : Simple X ↔ ∃! a : D.ι, Nonempty (X ≅ Ordinary.of (D.module a)) := by
  constructor
  · intro h
    letI := h
    obtain ⟨a, ⟨e⟩⟩ := hD.exhaust X.carrier X.isMod (irreducible_of_simple X)
    refine ⟨a, ⟨Ordinary.isoOfModuleEquiv e⟩, ?_⟩
    intro b hb
    exact module_injective D hD b a (hb.map fun eb => eb.symm ≪≫ Ordinary.isoOfModuleEquiv e)
  · rintro ⟨a, ⟨e⟩, _⟩
    letI := simple_module D hD a
    exact Simple.of_iso e

/-- The actual tensor unit is simple for every strongly rational VOA. -/
theorem vacuum_simple_of_stronglyRational (hW : StronglyRational W) :
    Simple (vacuumObject (W := W)) :=
  simple_of_irreducible _ ((isSimple_iff_adjointModule_isIrreducible W).mp hW.simple)

/-- The actual vacuum module is simple, using the vacuum label dictionary. -/
theorem vacuum_simple (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) :
    Simple (vacuumObject (W := W)) := by
  letI := simple_module D hD D.vac
  let e : Ordinary.of (D.module D.vac) ≅ vacuumObject (W := W) :=
    Ordinary.isoOfModuleEquiv hD.vac_iso.some
  exact Simple.of_iso e.symm

/-- Schur's scalar is unique as well as existent. -/
theorem end_simple_scalar_unique (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (a : D.ι) (f : Ordinary.of (D.module a) ⟶ Ordinary.of (D.module a)) :
    ∃! c : ℂ, c • 𝟙 (Ordinary.of (D.module a)) = f := by
  letI := simple_module D hD a
  obtain ⟨c, hc⟩ := end_simple_eq_smul D hD a f
  exact ⟨c, hc, fun d hd => smul_left_injective ℂ (id_nonzero _) (hd.trans hc.symm)⟩

/-- Endomorphisms of a labelled simple have complex dimension exactly one. -/
theorem end_simple_finrank (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (a : D.ι) : Module.finrank ℂ (Ordinary.of (D.module a) ⟶ Ordinary.of (D.module a)) = 1 := by
  letI := simple_module D hD a
  exact (finrank_eq_one_iff_of_nonzero' (𝟙 (Ordinary.of (D.module a))) (id_nonzero _)).mpr
    (end_simple_eq_smul D hD a)

end VOA.Huang.TensorCat.RepPackaging
