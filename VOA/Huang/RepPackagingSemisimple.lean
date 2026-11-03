import VOA.Huang.RepPackagingAbelian
import VOA.Huang.BraidRibbonRealization

/-! Finite semisimplicity and the precise modular-data label dictionary. -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory CategoryTheory.Limits
open VOA.Huang.PzTensorSemisimple VOA.Huang.PzTensorDecomp
open VOA.Classification.COne.ABDWeakAdmissible VOA.Classification.COne.AdmissibleOrdinary
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- An actual categorical isomorphism induces a module equivalence. -/
def moduleEquivOfIso {X Y : Ordinary W} (e : X ≅ Y) : ModuleEquiv W X.isMod Y.isMod where
  toLinearEquiv :=
    { e.hom.val with
      invFun := e.inv.val
      left_inv := fun x => congrArg (fun f : X ⟶ X => f.val x) e.hom_inv_id
      right_inv := fun y => congrArg (fun f : Y ⟶ Y => f.val y) e.inv_hom_id }
  map_act := e.hom.property

/-- Module irreducibility implies categorical simplicity for the actual morphisms. -/
theorem simple_of_irreducible (X : Ordinary W) (hX : X.isMod.IsIrreducible) : Simple X := by
  letI := hX.1
  constructor
  intro Y f hf
  constructor
  · intro hi hzero
    letI := hi
    have h : 𝟙 X = 0 := by simpa only [hzero, comp_zero] using (IsIso.inv_hom_id f).symm
    obtain ⟨x, hx⟩ := exists_ne (0 : X.carrier)
    exact hx (congrArg (fun k : X ⟶ X => k.val x) h)
  · intro hne
    have hf0 : f.val ≠ 0 := fun h => hne (Subtype.ext h)
    have hs : Function.Surjective f.val := by
      rcases hX.2 (rangeSub f.property) with h | h
      · exact (hf0 (LinearMap.range_eq_bot.mp h)).elim
      · exact LinearMap.range_eq_top.mp h
    exact (isoOfBijective f ⟨(mono_iff_injective f).mp hf, hs⟩).isIso_hom

/-- Rationality supplies weak-module complements for ordinary modules. -/
theorem ordinary_complements (hW : StronglyRational W) (X : Ordinary W) :
    ∀ P : WeakModule.Submodule' X.isMod.toWeakModule,
      ∃ Q : WeakModule.Submodule' X.isMod.toWeakModule, IsCompl P.carrier Q.carrier := by
  obtain ⟨A, hA⟩ := abdWeakIsAdmissible hW.c2Cofinite X.isMod.toWeakModule
  have h : ∀ P : WeakModule.Submodule' A.toWeakModule,
      ∃ Q : WeakModule.Submodule' A.toWeakModule, IsCompl P.carrier Q.carrier := hW.rational A
  rwa [hA] at h

/-- Every ordinary module is isomorphic to a finite biproduct of irreducible modules.
The independence assertion in the mode-algebra decomposition is retained here. -/
theorem semisimple_lw (hW : StronglyRational W) (hΦ : Finite (Φ W)) (X : Ordinary W) :
    ∃ (n : ℕ) (R : Fin n → LWModule W), (∀ j, (R j).IsIrreducibleLW) ∧
      Nonempty (X ≅ ⨁ fun j => Ordinary.of (R j).isMod) := by
  classical
  let A := X.isMod.toWeakModule
  have hOrd : IrrSubOrdinary A := irrSubOrdinary_of_ABD A
    (abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible abdWeakIsAdmissible) hW.c2Cofinite
  letI := isSemisimpleModule_of_compl A (ordinary_complements hW X)
  obtain ⟨n, S, π, hat, hind, hmem, hcomm, hsum⟩ :=
    exists_finite_decomp A (finite_of_indep A hOrd hΦ (boundedMult_ordinary X.isMod))
  let R : Fin n → LWModule W := fun j => lwOf A hOrd (S j) (hat j)
  let B := sumBicone (fun j => Ordinary.of (R j).isMod)
  let f : B.pt ⟶ X :=
    ⟨∑ j : Fin n, ((S j).restrictScalars ℂ).subtype.comp (LinearMap.proj (ULift.up j)), by
      intro a m x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      change (∑ j, ((S j).restrictScalars ℂ).subtype (mode ((R j).isMod.YM a) m (x (ULift.up j)))) = _
      change (∑ j, ((mode ((ordOf A hOrd (S j) (hat j)).YM a) m (x (ULift.up j)) : (S j).restrictScalars ℂ) : X.carrier)) = _
      simp_rw [ordOf_mode]
      exact (map_sum (mode (X.isMod.YM a) m) _ _).symm⟩
  have hf : Function.Bijective f.val := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have hz : ∑ j : Fin n, ((S j).restrictScalars ℂ).subtype (x (ULift.up j)) = 0 := by
        simpa only [f, LinearMap.sum_apply, LinearMap.comp_apply] using hx
      funext j
      apply Subtype.ext
      exact eq_zero_of_sum_indep hind (fun j => (x (ULift.up j)).property) hz j.down
    · intro x
      refine ⟨fun j => ⟨π j.down x, hmem j.down x⟩, ?_⟩
      simpa only [f, LinearMap.sum_apply, LinearMap.comp_apply] using hsum x
  exact ⟨n, R, fun j => lwOf_irr A hOrd (S j) (hat j),
    ⟨(isoOfBijective f hf).symm ≪≫ biproduct.uniqueUpToIso _ (sumBiconeIsBilimit _)⟩⟩

/-- Strong rationality alone supplies finite semisimplicity, using the existing PBW result. -/
theorem semisimple_lw_pbw (hW : StronglyRational W) (X : Ordinary W) :
    ∃ (n : ℕ) (R : Fin n → LWModule W), (∀ j, (R j).IsIrreducibleLW) ∧
      Nonempty (X ≅ ⨁ fun j => Ordinary.of (R j).isMod) :=
  semisimple_lw hW (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hW) X

/-- All Hom spaces of a strongly rational VOA are finite-dimensional. -/
theorem finiteDimensional_hom_pbw (hW : StronglyRational W) (X Y : Ordinary W) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  finiteDimensional_hom hW (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hW) X Y

/-- The finite chosen family already proves finiteness of irreducible isomorphism classes.
No PBW theorem is needed when valid modular data are supplied. -/
theorem finite_irreducibleClasses (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) : Finite (Φ W) := by
  let f : D.ι → Φ W := fun a => Quotient.mk (IrrModule.setoid W)
    ⟨D.carrier a, D.module a, hD.irred a⟩
  apply Finite.of_surjective f
  intro q
  induction q using Quotient.inductionOn with
  | h Q =>
    obtain ⟨a, ⟨e⟩⟩ := hD.exhaust Q.carrier Q.isMod Q.irreducible
    exact ⟨a, Quotient.sound ⟨e.symm⟩⟩

variable (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
include hD

/-- The chosen modular-data modules are categorical simples. -/
theorem simple_module (a : D.ι) : Simple (Ordinary.of (D.module a)) :=
  simple_of_irreducible _ (hD.irred a)

/-- Distinct labels give nonisomorphic categorical objects. -/
theorem module_injective (a b : D.ι)
    (e : Nonempty (Ordinary.of (D.module a) ≅ Ordinary.of (D.module b))) : a = b :=
  hD.distinct a b (e.map moduleEquivOfIso)

/-- Finite semisimplicity with the exact labels consumed by the realization. -/
theorem semisimple (hW : StronglyRational W) (hΦ : Finite (Φ W)) (X : Ordinary W) :
    ∃ (n : ℕ) (lab : Fin n → D.ι), Nonempty (X ≅ ⨁ fun j => Ordinary.of (D.module (lab j))) := by
  obtain ⟨n, R, hR, ⟨e⟩⟩ := semisimple_lw hW hΦ X
  choose lab he using fun j => hD.exhaust (R j).carrier (R j).isMod (hR j)
  exact ⟨n, lab, ⟨e ≪≫ biproduct.mapIso (fun j => Ordinary.isoOfModuleEquiv (he j).some)⟩⟩

/-- Finite semisimplicity under strong rationality and valid modular data alone. -/
theorem semisimple_of_modularData (hW : StronglyRational W) (X : Ordinary W) :
    ∃ (n : ℕ) (lab : Fin n → D.ι), Nonempty (X ≅ ⨁ fun j => Ordinary.of (D.module (lab j))) :=
  semisimple D hD hW (finite_irreducibleClasses D hD) X

/-- All ordinary Hom spaces are finite-dimensional; finiteness of labels is discharged. -/
theorem finiteDimensional_hom_of_modularData (hW : StronglyRational W) (X Y : Ordinary W) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  finiteDimensional_hom hW (finite_irreducibleClasses D hD) X Y

/-- Endomorphisms of a chosen simple are precisely complex scalars. -/
theorem end_simple_eq_smul (a : D.ι) (f : Ordinary.of (D.module a) ⟶ Ordinary.of (D.module a)) :
    ∃ c : ℂ, c • 𝟙 (Ordinary.of (D.module a)) = f := by
  letI := simple_module D hD a
  obtain ⟨h, hlow, hne⟩ := OrdVModule.exists_isLowestWeight_of_irreducible (D.module a) (hD.irred a)
  let P : LWModule W := ⟨D.carrier a, D.module a, h, hlow, hne⟩
  letI : FiniteDimensional ℂ (Ordinary.of (D.module a) ⟶ Ordinary.of (D.module a)) :=
    finiteDimensional_hom_source P (hD.irred a) (D.module a)
  exact endomorphism_simple_eq_smul_id ℂ f

end VOA.Huang.TensorCat.RepPackaging
