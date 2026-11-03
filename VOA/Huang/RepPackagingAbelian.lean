import VOA.Huang.RepPackagingLimits

/-! The ordinary module category is abelian, with its actual module maps. -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA VOA.Huang.FusionUnit CategoryTheory CategoryTheory.Limits
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Quotients of ordinary modules by invariant subspaces are ordinary. -/
def quotientObj (X : Ordinary W) (P : WeakModule.Submodule' X.isMod.toWeakModule) : Ordinary W := by
  letI := X.isMod.isInternal.chooseDecomposition
  exact Ordinary.of (X.isMod.quotient P (X.isMod.submodule_isGraded P))

def quotientπ (X : Ordinary W) (P : WeakModule.Submodule' X.isMod.toWeakModule) : X ⟶ quotientObj X P :=
  ⟨P.carrier.mkQ, fun a n x => (WeakModule.quotient_action_mk _ _ a n x).symm⟩

def quotientDesc {X Z : Ordinary W} (P : WeakModule.Submodule' X.isMod.toWeakModule)
    (g : X ⟶ Z) (h : P.carrier ≤ LinearMap.ker g.val) : quotientObj X P ⟶ Z := by
  refine ⟨P.carrier.liftQ g.val h, ?_⟩
  intro a n q
  obtain ⟨x, rfl⟩ := P.carrier.mkQ_surjective q
  change (P.carrier.liftQ g.val h) (mode (WeakModule.YMquot X.isMod.toWeakModule P a) n
    (Submodule.Quotient.mk x)) = _
  rw [WeakModule.quotient_action_mk]
  exact g.property a n x

abbrev cokernelObj {X Y : Ordinary W} (f : X ⟶ Y) := quotientObj Y (rangeSub f.property)
abbrev cokernelπ {X Y : Ordinary W} (f : X ⟶ Y) := quotientπ Y (rangeSub f.property)

theorem comp_cokernelπ {X Y : Ordinary W} (f : X ⟶ Y) : f ≫ cokernelπ f = 0 := by
  apply Ordinary.hom_ext
  intro x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

def cokernelDesc {X Y Z : Ordinary W} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) :
    cokernelObj f ⟶ Z :=
  quotientDesc _ g (by
    rintro y ⟨x, rfl⟩
    exact congrArg (fun k : X ⟶ Z => k.val x) h)

def cokernelIsColimit {X Y : Ordinary W} (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)) := by
  apply CokernelCofork.IsColimit.ofπ _ _ (fun g h => cokernelDesc f g h)
  · intros; rfl
  · intro Z g h m hm
    apply Ordinary.hom_ext
    intro q
    obtain ⟨y, rfl⟩ := (LinearMap.range f.val).mkQ_surjective q
    exact congrArg (fun k : Y ⟶ Z => k.val y) hm

instance ordinaryHasCokernels : HasCokernels (Ordinary W) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

theorem epi_iff_surjective {X Y : Ordinary W} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f.val := by
  constructor
  · intro hf
    letI := hf
    have hz : cokernelπ f = 0 := (cancel_epi f).mp (by simp [comp_cokernelπ])
    intro y
    have h := congrArg (fun k : Y ⟶ cokernelObj f => k.val y) hz
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · intro hf
    refine ⟨fun g h he => Ordinary.hom_ext _ _ fun y => ?_⟩
    obtain ⟨x, rfl⟩ := hf y
    exact congrArg (fun k => k.val x) he

/-- A monomorphism is the kernel of its ordinary quotient. -/
@[implicit_reducible]
def normalMono {X Y : Ordinary W} (f : X ⟶ Y) [Mono f] : NormalMono f := by
  have hf := (mono_iff_injective f).mp inferInstance
  let e := LinearEquiv.ofInjective f.val hf
  refine ⟨cokernelObj f, cokernelπ f, comp_cokernelπ f, ?_⟩
  apply KernelFork.IsLimit.ofι'
  intro Z g hg
  have hr (x : Z.carrier) : g.val x ∈ LinearMap.range f.val :=
    (Submodule.Quotient.mk_eq_zero _).mp (congrArg (fun k : Z ⟶ cokernelObj f => k.val x) hg)
  let l := e.symm.toLinearMap.comp (g.val.codRestrict _ hr)
  have hl (x : Z.carrier) : f.val (l x) = g.val x :=
    congrArg Subtype.val (e.apply_symm_apply ⟨g.val x, hr x⟩)
  refine ⟨⟨l, ?_⟩, Ordinary.hom_ext _ _ hl⟩
  intro a n x
  apply hf
  rw [hl, f.property, hl, g.property]

/-- A surjective module map is a cokernel of the inclusion of its kernel. -/
@[implicit_reducible]
def normalEpi {X Y : Ordinary W} (f : X ⟶ Y) [Epi f] : NormalEpi f := by
  have hf := (epi_iff_surjective f).mp inferInstance
  let e := f.val.quotKerEquivOfSurjective hf
  refine ⟨kernelObj f, kernelι f, kernelι_comp f, ?_⟩
  apply CokernelCofork.IsColimit.ofπ'
  intro Z g hg
  have hk : LinearMap.ker f.val ≤ LinearMap.ker g.val := by
    intro x hx
    exact congrArg (fun k : kernelObj f ⟶ Z => k.val ⟨x, hx⟩) hg
  let l := ((LinearMap.ker f.val).liftQ g.val hk).comp e.symm.toLinearMap
  have hl (x : X.carrier) : l (f.val x) = g.val x := by
    change ((LinearMap.ker f.val).liftQ g.val hk) (e.symm (e (Submodule.Quotient.mk x))) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨⟨l, ?_⟩, Ordinary.hom_ext _ _ hl⟩
  intro a n y
  obtain ⟨x, rfl⟩ := hf y
  rw [← f.property, hl, hl, g.property]

/-- Abelianity requires no rationality or tensor-product assumption. -/
instance ordinaryAbelian : Abelian (Ordinary W) where
  normalMonoOfMono f := ⟨normalMono f⟩
  normalEpiOfEpi f := ⟨normalEpi f⟩

end VOA.Huang.TensorCat.RepPackaging
