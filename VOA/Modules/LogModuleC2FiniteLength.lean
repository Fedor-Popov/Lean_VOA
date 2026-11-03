import VOA.Modules.LogModuleC2Exact
import VOA.Modules.LogTensorTargets
import VOA.Classification.COne.McRaeM2FinLen
import VOA.Classification.COne.ABDWeakAdmissibleComplete
import VOA.Modularity.ConformalWeightChoice

/-! # C₂-cofiniteness of every actual finite-length weak module

Simple weak modules are ordinary under C₂-cofiniteness and satisfy Buhl's
module spanning theorem. Right exactness of the genuine C₂ quotient then
propagates this finiteness through a composition series. The middle weak
module need not have semisimple L(0), be irreducible, or be rational.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.ModuleC2
open VOA.Huang.FusionC2 VOA.Huang.BuhlSpanning
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.AdmissibleOrdinary VOA.Classification.COne.ABDWeakAdmissible
open VOA.Classification.COne.McRaeM1 VOA.C2Rigid
open VOA.Classification.COne.PlusFiniteLength

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Simple weak modules are module-C₂-cofinite with their actual given action. -/
theorem cofinite_of_weak_irreducible (hC2 : C2Cofinite W) {X : Type u}
    [AddCommGroup X] [Module ℂ X] (B : WeakModule W X)
    (hB : Nontrivial X ∧ ∀ P : WeakModule.Submodule' B, P.carrier = ⊥ ∨ P.carrier = ⊤) :
    ModuleC2Cofinite B := by
  obtain ⟨O,hO⟩ := abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible
    abdWeakIsAdmissible hC2 B hB
  have hOirr : O.IsIrreducible := by rw [OrdVModule.IsIrreducible,hO]; exact hB
  let I : IrrModule W := { carrier := X, isMod := O, irreducible := hOirr }
  have hw := hasConformalWeight_conformalWeightOf I
  let P : LWModule W :=
    { carrier := X
      isMod := O
      h := conformalWeightOf I
      isLow := hw.2
      realized := hw.1 }
  have h := moduleC2Cofinite_of_irreducibleLW hC2 P hOirr
  rwa [show P.isMod.toWeakModule = B from hO] at h

/-- Every finite-length weak module of a C₂-cofinite VOA is genuinely module-C₂-cofinite. -/
theorem cofinite_of_finiteLength (hC2 : C2Cofinite W) (B : WeakModule W M)
    (hfl : IsFiniteLength (modeAlg B) M) : ModuleC2Cofinite B := by
  obtain ⟨hNo,hAr⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI : WellFoundedGT (Submodule (modeAlg B) M) := isNoetherian_iff'.mp hNo
  haveI : WellFoundedLT (Submodule (modeAlg B) M) := hAr
  have hall : ∀ P : Submodule (modeAlg B) M, ModuleC2Cofinite (subW B P) := by
    intro P
    induction P using WellFoundedLT.induction with
    | ind P ih =>
      by_cases hP : P = ⊥
      · subst P
        haveI : Subsingleton (ofR B (⊥ : Submodule (modeAlg B) M)).carrier := by
          refine ⟨fun x y => Subtype.ext ?_⟩
          have hx : (x : M) = 0 := x.2
          have hy : (y : M) = 0 := y.2
          rw [hx,hy]
        change FiniteDimensional ℂ (_ ⧸ _)
        infer_instance
      obtain ⟨Q,hQlt,hQmax⟩ := (wellFounded_gt (α := Submodule (modeAlg B) M)).has_min
        {Q | Q < P} ⟨⊥,bot_lt_iff_ne_bot.mpr hP⟩
      have hQP : Q ⋖ P := ⟨hQlt,fun c hQc hcP => hQmax c hcP hQc⟩
      have hQ := ih Q hQlt
      have hS := cofinite_of_weak_irreducible hC2 (quoW B P Q)
        (isSimple_subquotient B P Q hQP)
      let f : (subW B Q).Hom (subW B P) :=
        { toLinearMap :=
            { toFun := fun x => ⟨(x : M),hQP.le x.2⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          map_act := fun _ _ _ => rfl }
      let g : (subW B P).Hom (quoW B P Q) :=
        WeakModule.quotientMk (subW B P) (subInW B P Q)
      have hg : Function.Surjective g.toLinearMap := Submodule.mkQ_surjective _
      have hex : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap := by
        ext x
        constructor
        · rintro ⟨y,rfl⟩
          change Submodule.Quotient.mk (f.toLinearMap y) = 0
          exact (Submodule.Quotient.mk_eq_zero _).mpr y.2
        · intro hx
          have hx0 : Submodule.Quotient.mk x = (0 : (ofR B P).carrier ⧸
              (subInW B P Q).carrier) := hx
          have hxQ : x ∈ (subInW B P Q).carrier :=
            (Submodule.Quotient.mk_eq_zero (subInW B P Q).carrier).mp hx0
          exact ⟨⟨(x : M),hxQ⟩,Subtype.ext rfl⟩
      exact cofinite_of_exact f g hex hg hQ hS
  let i := subIncl B (⊤ : Submodule (modeAlg B) M)
  have hi : Function.Surjective i.toLinearMap := fun x => ⟨⟨x,Submodule.mem_top⟩,rfl⟩
  exact cofinite_of_surjective i hi (hall ⊤)


/-- The same conclusion for every finitely generated actual weak module. -/
theorem cofinite_of_finGen (hC2 : C2Cofinite W) (B : WeakModule W M) (hgen : FinGen B) :
    ModuleC2Cofinite B := by
  obtain ⟨S,hS,hgen⟩ := hgen
  let P := Submodule.span (modeAlg B) S
  have hPt : P.restrictScalars ℂ = ⊤ := hgen (P.restrictScalars ℂ)
    (fun _ hx => Submodule.subset_span hx) (fun a n x hx => (ofR B P).act_mem a n hx)
  have hP : P = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have hx : x ∈ P.restrictScalars ℂ := hPt ▸ Submodule.mem_top
    exact hx
  have hfg : (⊤ : Submodule (modeAlg B) M).FG :=
    Submodule.fg_def.mpr ⟨S,hS,hP⟩
  have hfl := finiteLength_fg_of_c2Cofinite hC2 B ⊤ hfg
  exact cofinite_of_finiteLength hC2 B (Submodule.topEquiv.isFiniteLength hfl)

end VOA.LogTensor.ModuleC2
