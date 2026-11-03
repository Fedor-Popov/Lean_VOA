import VOA.Classification.COne.McRaeM2FiniteHomSocle
import VOA.Classification.COne.AdmissibleOrdinaryFinite
import VOA.Modularity.StronglyRationalFamily
import VOA.Modules.LogTensorFinLength

/-! # Canonical simple representatives for the actual weak-module socle

The C₂ ordinary-structure theorem identifies each simple weak submodule with
one canonical ordinary representative. This discharges the exhaustiveness
input of the finite-Hom socle theorem without any rationality assumption.
Finiteness of the representative index is supplied explicitly, or from
semisimple Zhu and the PBW bottom construction from the theorem `VOA.pbw`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.McRaeM1 VOA.Classification.COne.McRaeM2
open VOA.Classification.COne.AdmissibleOrdinary VOA.Classification.COne.ABDWeakAdmissible
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogFin
open VOA.VHat VOA.VHat.DLM3

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Irreducibility under actual modes is simplicity over the concrete mode algebra. -/
theorem simple_of_weak_irreducible {X : Type u} [AddCommGroup X] [Module ℂ X]
    (B : WeakModule W X)
    (hB : Nontrivial X ∧ ∀ P : WeakModule.Submodule' B, P.carrier = ⊥ ∨ P.carrier = ⊤) :
    IsSimpleModule (modeAlg B) X := by
  haveI := hB.1
  haveI : IsSimpleOrder (Submodule (modeAlg B) X) :=
    { eq_bot_or_eq_top := by
        intro P
        rcases hB.2 (ofR B P) with h | h
        · left
          apply eq_bot_iff.mpr
          intro x hx
          have hz : x ∈ (⊥ : Submodule ℂ X) := h ▸ hx
          exact hz
        · right
          apply eq_top_iff.mpr
          intro x _
          have hx : x ∈ (ofR B P).carrier := h ▸ Submodule.mem_top
          exact hx }
  exact {}

/-- Restricting the actual action to a simple submodule preserves irreducibility. -/
theorem weak_irreducible_submodule (B : WeakModule W M)
    (P : Submodule (modeAlg B) M) (hP : IsAtom P) :
    Nontrivial (ofR B P).carrier ∧
      ∀ Q : WeakModule.Submodule' (WeakModule.submodule B (ofR B P)),
        Q.carrier = ⊥ ∨ Q.carrier = ⊤ := by
  haveI : IsSimpleModule (modeAlg B) P := isSimpleModule_iff_isAtom.mpr hP
  have hnt : Nontrivial (ofR B P).carrier := by
    obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
    exact ⟨⟨⟨x,hx⟩,0,fun h => hx0 (congrArg Subtype.val h)⟩⟩
  refine ⟨hnt,?_⟩
  intro Q
  let i := subIncl B P
  let R := toR (WeakModule.submodule B (ofR B P)) Q
  have hle : modeMap i R ≤ P := by
    exact (modeMap_mono i le_top).trans (le_of_eq (modeMap_subIncl_top B P))
  rcases hP.le_iff.mp hle with h | h
  · left
    have hr : R = ⊥ := modeMap_injective i (subIncl_injective B P)
      (by rw [h,modeMap_bot])
    apply eq_bot_iff.mpr
    intro x hx
    have hz : x ∈ R := hx
    rw [hr] at hz
    exact hz
  · right
    have hr : R = ⊤ := modeMap_injective i (subIncl_injective B P)
      (h.trans (modeMap_subIncl_top B P).symm)
    apply eq_top_iff.mpr
    intro x _
    have hx : x ∈ R := hr ▸ Submodule.mem_top
    exact hx

/-- Every simple weak submodule is the actual image of a canonical irreducible module. -/
theorem canonical_simple_coverage (hC2 : C2Cofinite W) (B : WeakModule W M)
    (P : Submodule (modeAlg B) M) (hP : IsAtom P) :
    ∃ c : Φ W, ∃ f : moduleHomSpace (canonicalIrrModule c).isMod.toWeakModule B,
      modeMap (homOfSpace f) ⊤ = P := by
  let BP := WeakModule.submodule B (ofR B P)
  have hBP := weak_irreducible_submodule B P hP
  obtain ⟨O,hO⟩ := abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible
    abdWeakIsAdmissible hC2 BP hBP
  let I : IrrModule W :=
    { carrier := (ofR B P).carrier
      isMod := O
      irreducible := by rw [OrdVModule.IsIrreducible,hO]; exact hBP }
  obtain ⟨e⟩ : Nonempty (ModuleEquiv W (canonicalIrrModule I.toΦ).isMod O) :=
    Quotient.exact (canonicalIrrModule_toΦ I.toΦ)
  let f : (canonicalIrrModule I.toΦ).isMod.toWeakModule.Hom B :=
    { toLinearMap := (ofR B P).carrier.subtype.comp e.toLinearEquiv.toLinearMap
      map_act := by
        intro a n x
        simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,e.map_act]
        change (O.toWeakModule.act a n (e.toLinearEquiv x) : M) = _
        rw [hO]
        rfl }
  refine ⟨I.toΦ,⟨f.toLinearMap,f.map_act⟩,?_⟩
  apply le_antisymm
  · rintro _ ⟨x,-,rfl⟩
    exact (e.toLinearEquiv x).2
  · intro y hy
    obtain ⟨x,hx⟩ := e.toLinearEquiv.surjective (⟨y,hy⟩ : (ofR B P).carrier)
    refine ⟨x,Submodule.mem_top,?_⟩
    exact congrArg Subtype.val hx

theorem canonical_simple_finGen (c : Φ W) :
    FinGen (canonicalIrrModule c).isMod.toWeakModule := by
  have hs := simple_of_weak_irreducible (canonicalIrrModule c).isMod.toWeakModule
    (canonicalIrrModule c).irreducible
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp (finiteLength_of_simple hs)).1
  exact finGen_of_isNoetherian _

/-- Finite simple types and actual Hom-finiteness give a finite-length socle. -/
theorem finiteLength_socle_of_canonical_hom (hC2 : C2Cofinite W) (B : WeakModule W M)
    [Finite (Φ W)]
    [∀ c : Φ W, FiniteDimensional ℂ
      (moduleHomSpace (canonicalIrrModule c).isMod.toWeakModule B)] :
    IsFiniteLength (modeAlg B) (socle B) :=
  finiteLength_socle_of_finite_hom (fun c : Φ W => (canonicalIrrModule c).carrier)
    (fun c => (canonicalIrrModule c).isMod.toWeakModule) B hC2
    canonical_simple_finGen (canonical_simple_coverage hC2 B)

end VOA.C2Rigid.LocalInjective
