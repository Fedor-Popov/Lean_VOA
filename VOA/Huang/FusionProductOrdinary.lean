import VOA.Huang.FusionProductDecomposition
import VOA.Classification.COne.AssociativityFinal

/-! # Finite decomposition of ordinary targets

Finite-dimensional weight spaces bound multiplicities: a map from an
irreducible module is determined by its value on any nonzero lowest vector.
The existing semisimple mode-algebra decomposition then becomes finite.
-/
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit Module
open VOA.Huang.PzTensorDecomp
open VOA.Classification.COne.ABDWeakAdmissible VOA.Classification.COne.AdmissibleOrdinary
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {N : Type u} [AddCommGroup N] [Module ℂ N]

/-- Finite-dimensional Hom from an irreducible module into any ordinary target. -/
theorem finiteDimensional_hom_source (R : LWModule W) (iR : R.IsIrreducibleLW)
    (AN : OrdVModule W N) : FiniteDimensional ℂ (homSpace R.isMod AN) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot R.realized
  let e : homSpace R.isMod AN →ₗ[ℂ] AN.weight R.h :=
    { toFun f := ⟨f.val v, hom_mem_weight f.property hv⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hz : f.val v = 0 := congrArg Subtype.val hf
    rcases iR.2 (kerSub f.property) with hk | hk
    · have hvker : v ∈ (kerSub f.property).carrier := hz
      rw [hk, Submodule.mem_bot] at hvker
      exact (hv0 hvker).elim
    · apply Subtype.ext
      exact LinearMap.ker_eq_top.mp hk
  letI := AN.finrank R.h
  exact Module.Finite.of_injective e hinj

/-- Ordinary weight-space finiteness supplies the bounded-multiplicity input. -/
theorem boundedMult_ordinary (AN : OrdVModule W N) : BoundedMult AN.toWeakModule := by
  intro R iR
  letI := finiteDimensional_hom_source R iR AN
  refine ⟨Module.finrank ℂ (homSpace R.isMod AN), fun n ψ hψ hli => ?_⟩
  let φ : Fin n → homSpace R.isMod AN := fun k => ⟨ψ k, hψ k⟩
  have hφ : LinearIndependent ℂ φ := LinearIndependent.of_comp (homSpace R.isMod AN).subtype hli
  simpa using hφ.fintype_card_le_finrank

/-- A complete family finitely dominates every ordinary module of a strongly
rational VOA, with finiteness of the set of irreducibles explicit. -/
theorem finiteTargets_of_stronglyRational (hV : StronglyRational W)
    (hΦ : Finite (Φ W)) {ι : Type u} (R : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (R i)) :
    FiniteTargets R := by
  intro N _ _ AN
  have hOrd : IrrSubOrdinary AN.toWeakModule := irrSubOrdinary_of_ABD _
    (abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible abdWeakIsAdmissible) hV.c2Cofinite
  obtain ⟨NA, hNA⟩ := abdWeakIsAdmissible hV.c2Cofinite AN.toWeakModule
  have hCR : ∀ P : WeakModule.Submodule' AN.toWeakModule,
      ∃ Q : WeakModule.Submodule' AN.toWeakModule, IsCompl P.carrier Q.carrier := by
    have h : ∀ P : WeakModule.Submodule' NA.toWeakModule,
        ∃ Q : WeakModule.Submodule' NA.toWeakModule, IsCompl P.carrier Q.carrier := hV.rational NA
    rwa [hNA] at h
  obtain ⟨r, S, iS, ψ, χ, hψ, hχ, htotal⟩ :=
    exists_decomp AN.toWeakModule hOrd hΦ (boundedMult_ordinary AN) hCR
  choose lab he using fun j => hcomplete (S j) (iS j)
  let e (j : Fin r) : ModuleEquiv W (S j).isMod (R (lab j)).isMod := Classical.choice (he j)
  let inc (j : Fin r) : homSpace (R (lab j)).isMod AN :=
    ⟨(ψ j).comp (e j).toLinearEquiv.symm.toLinearMap, fun a n x => by
      change ψ j ((e j).toLinearEquiv.symm (mode ((R (lab j)).isMod.YM a) n x)) = _
      have hh := (e j).symm.map_act a n x
      change (e j).toLinearEquiv.symm (mode ((R (lab j)).isMod.YM a) n x) =
        mode ((S j).isMod.YM a) n ((e j).toLinearEquiv.symm x) at hh
      rw [hh, hψ]; rfl⟩
  let proj (j : Fin r) : homSpace AN (R (lab j)).isMod :=
    ⟨(e j).toLinearEquiv.toLinearMap.comp (χ j), fun a n x => by
      change (e j).toLinearEquiv (χ j (mode (AN.YM a) n x)) = _
      rw [hχ]
      exact (e j).map_act a n (χ j x)⟩
  refine ⟨r, lab, inc, proj, fun x => ?_⟩
  simpa only [inc, proj, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using htotal x

/-- Version with the PBW datum discharged by the theorem `VOA.pbw`; it adds no axiom. -/
theorem finiteTargets_of_stronglyRational_pbw (hV : StronglyRational W)
    {ι : Type u} (R : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (R i)) :
    FiniteTargets R :=
  finiteTargets_of_stronglyRational hV
    (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV) R hcomplete

end VOA.Huang.FusionProduct
