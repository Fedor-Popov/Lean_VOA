import VOA.Huang.TensorCatExternal
import VOA.Modules.OrdSubmodule
import Mathlib.CategoryTheory.Abelian.Basic

/-! Finite biproducts and kernels of actual ordinary modules. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The underlying linear map detects invertibility. -/
def isoOfBijective {X Y : Ordinary W} (f : X ⟶ Y) (hf : Function.Bijective f.val) : X ≅ Y :=
  Ordinary.isoOfModuleEquiv
    { toLinearEquiv := LinearEquiv.ofBijective f.val hf
      map_act := f.property }

/-- Finite direct sums, with the coordinate inclusions and projections. -/
def sumBicone {ι : Type} [Fintype ι] (X : ι → Ordinary W) : Bicone X := by
  classical
  letI : DecidableEq (ULift.{u} ι) := Classical.typeDecidableEq _
  exact
    { pt := Ordinary.of (sumOrd (fun i : ULift.{u} ι => (X i.down).isMod))
      π := fun i => sumProjection (fun i : ULift.{u} ι => (X i.down).isMod) (ULift.up i)
      ι := fun i => sumInclusion (fun i : ULift.{u} ι => (X i.down).isMod) (ULift.up i)
      ι_π := fun i j => by
        apply Ordinary.hom_ext
        intro x
        by_cases h : i = j
        · subst j
          simp only [dite_true, eqToHom_refl, Ordinary.id_apply]
          dsimp [sumInclusion, sumProjection, compHom, LinearMap.single, LinearMap.proj]
          exact Pi.single_eq_same (M := fun j : ULift.{u} ι => (X j.down).carrier) (ULift.up i) x
        · simp only [h, dite_false]
          dsimp [sumInclusion, sumProjection, compHom, LinearMap.single, LinearMap.proj]
          exact Pi.single_eq_of_ne (M := fun j : ULift.{u} ι => (X j.down).carrier) (fun he => h (ULift.up_injective he).symm) x }


/-- The coordinate sum is a categorical biproduct, including the empty sum. -/
def sumBiconeIsBilimit {ι : Type} [Fintype ι] (X : ι → Ordinary W) :
    (sumBicone X).IsBilimit := by
  classical
  letI : DecidableEq (ULift.{u} ι) := Classical.typeDecidableEq _
  apply isBilimitOfTotal
  apply Ordinary.hom_ext
  intro x
  change (∑ i : ι, compHom
    (sumInclusion (fun i : ULift.{u} ι => (X i.down).isMod) (ULift.up i))
    (sumProjection (fun i : ULift.{u} ι => (X i.down).isMod) (ULift.up i))).val x = x
  simp only [Submodule.coe_sum, LinearMap.sum_apply]
  funext j
  simp only [Finset.sum_apply]
  dsimp [sumInclusion, sumProjection, compHom, LinearMap.single, LinearMap.proj]
  rcases j with ⟨j⟩
  change (∑ i, (Pi.single (ULift.up i) (x (ULift.up i)) : ∀ j : ULift.{u} ι, (X j.down).carrier) (ULift.up j)) = x (ULift.up j)
  rw [Finset.sum_eq_single j]
  · exact Pi.single_eq_same (M := fun j : ULift.{u} ι => (X j.down).carrier) _ _
  · intro b _ hb
    exact Pi.single_eq_of_ne (M := fun j : ULift.{u} ι => (X j.down).carrier)
      (fun he => hb (ULift.up_injective he).symm) _
  · simp

instance ordinaryHasFiniteBiproducts : HasFiniteBiproducts (Ordinary W) :=
  ⟨fun _ => ⟨fun X => HasBiproduct.mk ⟨sumBicone X, sumBiconeIsBilimit X⟩⟩⟩

/-- The invariant kernel, equipped with its inherited ordinary grading. -/
def kernelObj {X Y : Ordinary W} (f : X ⟶ Y) : Ordinary W :=
  Ordinary.of (X.isMod.submodule (kerSub f.property))

def kernelι {X Y : Ordinary W} (f : X ⟶ Y) : kernelObj f ⟶ X :=
  ⟨(LinearMap.ker f.val).subtype, fun _ _ _ => rfl⟩

theorem kernelι_comp {X Y : Ordinary W} (f : X ⟶ Y) : kernelι f ≫ f = 0 := by
  apply Ordinary.hom_ext
  exact fun x => x.property

def kernelLift {X Y Z : Ordinary W} (f : X ⟶ Y) (g : Z ⟶ X) (h : g ≫ f = 0) :
    Z ⟶ kernelObj f :=
  ⟨g.val.codRestrict _ (fun x => congrArg (fun k : Z ⟶ Y => k.val x) h),
    fun a n x => Subtype.ext (g.property a n x)⟩

def kernelIsLimit {X Y : Ordinary W} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelι f) (kernelι_comp f)) := by
  apply KernelFork.IsLimit.ofι _ _ (fun g h => kernelLift f g h)
  · intros; rfl
  · intro Z g h m hm
    apply Ordinary.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k : Z ⟶ X => k.val x) hm

instance ordinaryHasKernels : HasKernels (Ordinary W) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- Categorical monomorphisms are exactly injective module maps. -/
theorem mono_iff_injective {X Y : Ordinary W} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f.val := by
  constructor
  · intro hf
    letI := hf
    have hz : kernelι f = 0 := (cancel_mono f).mp (by simp [kernelι_comp])
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact congrArg (fun k : kernelObj f ⟶ X => k.val ⟨x, hx⟩) hz
  · intro hf
    exact ⟨fun g h he => Ordinary.hom_ext _ _ fun x =>
      hf (congrArg (fun k => k.val x) he)⟩

/-- Schur finiteness extends to all ordinary sources using finite split presentations. -/
theorem finiteDimensional_hom (hW : StronglyRational W) (hΦ : Finite (Φ W))
    (X Y : Ordinary W) : FiniteDimensional ℂ (X ⟶ Y) := by
  obtain ⟨P⟩ := simplePresentation_nonempty hW hΦ X
  letI (j : Fin P.size) : FiniteDimensional ℂ (Ordinary.of (P.part j).isMod ⟶ Y) :=
    finiteDimensional_hom_source (P.part j) (P.irreducible j) Y.isMod
  let e : (X ⟶ Y) →ₗ[ℂ] (∀ j, Ordinary.of (P.part j).isMod ⟶ Y) :=
    { toFun f j := P.inc j ≫ f
      map_add' := fun f g => by funext j; exact Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun c f => by funext j; exact Linear.comp_smul _ _ _ _ _ _ }
  apply Module.Finite.of_injective e
  intro f g h
  apply Ordinary.hom_ext
  intro x
  rw [← P.total x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun k : Ordinary.of (P.part j).isMod ⟶ Y => k.val ((P.proj j).val x))
    (congrFun h j)

end VOA.Huang.TensorCat.RepPackaging
