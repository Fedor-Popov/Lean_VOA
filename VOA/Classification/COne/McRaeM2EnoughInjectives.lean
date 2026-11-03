/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.WeakModuleProduct
import VOA.Classification.COne.McRaeM1Main
import VOA.Classification.COne.McRaeM2EssentialSocle

/-! # Enough genuine finite-length injectives under C₂-cofiniteness

The contragredient of the projective cover of a simple dual is its actual finite
injective hull. Products remain finite-length and injective. Descending induction
on kernels therefore embeds every finite-length weak module into a finite-length
injective, without tensor rigidity or rationality.
-/

namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.McRaeM1
open VOA.WeakModuleProduct
universe u
variable {V M N X : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup X] [Module ℂ X] {W : VertexOperatorAlgebra V}

/-- A genuine finite-length injective weak module, bundled to allow its actual carrier
to vary during finite product constructions. -/
structure FiniteInjective (W : VertexOperatorAlgebra V) where
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module ℂ carrier]
  act : WeakModule W carrier
  finiteLength : IsFiniteLength (modeAlg act) carrier
  injective : IsInjFL act

attribute [instance] FiniteInjective.acg FiniteInjective.mod

/-- Binary products of genuine relative injectives remain relative injective. -/
theorem isInjFL_prod (A : WeakModule W M) (B : WeakModule W N)
    (hA : IsInjFL A) (hB : IsInjFL B) : IsInjFL (WeakModuleProduct.prod A B) := by
  intro Y Z _ _ _ _ BY BZ hZ g hg f
  obtain ⟨a,ha⟩ := hA BY BZ hZ g hg (homComp (fstHom A B) f)
  obtain ⟨b,hb⟩ := hB BY BZ hZ g hg (homComp (sndHom A B) f)
  refine ⟨pairHom a b,fun y => ?_⟩
  apply Prod.ext
  · exact ha y
  · exact hb y

noncomputable def FiniteInjective.prod (A B : FiniteInjective W) : FiniteInjective W where
  carrier := A.carrier × B.carrier
  act := WeakModuleProduct.prod A.act B.act
  finiteLength := finiteLength_prod A.act B.act A.finiteLength B.finiteLength
  injective := isInjFL_prod A.act B.act A.injective B.injective

private noncomputable def zeroWeak {Z : Type u} [AddCommGroup Z] [Module ℂ Z] [Subsingleton Z] :
    WeakModule W Z where
  YM := 0
  vacuum_YM := by ext p x; exact Subsingleton.elim _ _
  truncation := fun _ _ => ⟨0,fun _ _ => Subsingleton.elim _ _⟩
  jacobi := fun _ _ _ _ _ _ => Subsingleton.elim _ _

private theorem zeroWeak_injective {Z : Type u} [AddCommGroup Z] [Module ℂ Z] [Subsingleton Z] :
    IsInjFL (zeroWeak (W := W) (Z := Z)) := by
  intro Y Z' _ _ _ _ BY BZ hZ g hg f
  exact ⟨⟨0,fun _ _ _ => Subsingleton.elim _ _⟩,fun _ => Subsingleton.elim _ _⟩

private noncomputable def zeroInjective (W : VertexOperatorAlgebra V) : FiniteInjective W where
  carrier := (⊥ : Submodule ℂ V)
  act := zeroWeak
  finiteLength := .of_subsingleton
  injective := zeroWeak_injective

/-- Every genuine simple weak module embeds into its actual finite-length injective hull. -/
theorem simple_injective_embedding (hC2 : C2Cofinite W) (B : WeakModule W M)
    (hB : IsSimpleModule (modeAlg B) M) :
    ∃ E : FiniteInjective W, ∃ f : B.Hom E.act, Function.Injective f.toLinearMap := by
  let G := gwOfFiniteLength hC2 B (finiteLength_of_simple hB)
  have hG := isGenGraded_gwOfFiniteLength hC2 B (finiteLength_of_simple hB)
  have hdual := isSimple_contra G hG hB
  obtain ⟨D⟩ := huangCoverFact_of_c2 hC2 (contra G).toWeakModule hdual
  obtain ⟨hI,hfl,i,hi,hsoc⟩ := injHull_of_cover hC2 B hB D
  let E : FiniteInjective W :=
    { carrier := RestrictedDual (gwOfFiniteLength hC2 D.BP D.finiteLength)
      act := (contra (gwOfFiniteLength hC2 D.BP D.finiteLength)).toWeakModule
      finiteLength := hfl
      injective := hI }
  exact ⟨E,i,hi⟩

private noncomputable def inclusion (B : WeakModule W M) (P : Submodule (modeAlg B) M) :
    (subW B P).Hom B where
  toLinearMap := (ofR B P).carrier.subtype
  map_act _ _ _ := rfl

/-- A mode-algebra atom remains simple for its own restricted weak-module action. -/
theorem isSimple_restricted_atom (B : WeakModule W M) (P : Submodule (modeAlg B) M)
    (hP : IsAtom P) : IsSimpleModule (modeAlg (subW B P)) (ofR B P).carrier := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
  haveI : Nontrivial (ofR B P).carrier :=
    ⟨⟨⟨x,hx⟩,0,by intro h; exact hx0 (congrArg Subtype.val h)⟩⟩
  haveI : IsSimpleOrder (Submodule (modeAlg (subW B P)) (ofR B P).carrier) := by
    apply IsSimpleOrder.of_forall_eq_top
    intro Q hQ
    have hle : modeMap (inclusion B P) Q ≤ P := by
      rintro _ ⟨x,hx,rfl⟩
      exact x.2
    have hn : modeMap (inclusion B P) Q ≠ ⊥ := by
      intro h
      apply hQ
      apply eq_bot_iff.mpr
      intro x hx
      have hmem : (x:M) ∈ modeMap (inclusion B P) Q := ⟨x,hx,rfl⟩
      rw [h,Submodule.mem_bot] at hmem
      exact Subtype.ext hmem
    have he : modeMap (inclusion B P) Q = P := (hP.le_iff_eq hn).mp hle
    apply eq_top_iff.mpr
    intro x hx
    have hmem : (x:M) ∈ modeMap (inclusion B P) Q := by rw [he]; exact x.2
    obtain ⟨y,hy,he⟩ := hmem
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  exact {}

/-- Separation on any chosen submodule is achieved by a genuine finite-length
injective; descending kernel induction makes the product finite. -/
theorem finite_injective_separates (hC2 : C2Cofinite W) (B : WeakModule W M)
    (hB : IsFiniteLength (modeAlg B) M) (P : Submodule (modeAlg B) M) :
    ∃ E : FiniteInjective W, ∃ f : B.Hom E.act, ∀ x ∈ P, f.toLinearMap x = 0 → x = 0 := by
  haveI : IsArtinian (modeAlg B) M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hB).2
  induction P using WellFoundedLT.induction with
  | ind P ih =>
    by_cases hP : P = ⊥
    · subst P
      haveI : Subsingleton (zeroInjective W).carrier := by
        change Subsingleton (⊥ : Submodule ℂ V)
        infer_instance
      refine ⟨zeroInjective W,⟨0,fun _ _ _ => Subsingleton.elim _ _⟩,?_⟩
      intro x hx hg
      exact (Submodule.mem_bot _).mp hx
    obtain ⟨S,hS,hSP⟩ := exists_atom_le hC2 B P hP
    obtain ⟨E,e,he⟩ := simple_injective_embedding hC2 (subW B S) (isSimple_restricted_atom B S hS)
    obtain ⟨g,hg⟩ := extend_submodule hC2 B E.act E.injective (ofR B S) e
    let K := P ⊓ modeComap g ⊥
    have hKP : K < P := by
      apply lt_of_le_of_ne inf_le_left
      intro h
      obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.ne_bot
      have hxK : x ∈ K := by
        change x ∈ P ⊓ modeComap g ⊥
        rw [h]
        exact hSP hx
      have hzero : g.toLinearMap x = 0 := by
        have hm := hxK.2
        exact (Submodule.mem_bot (modeAlg E.act)).mp hm
      have hh : e.toLinearMap ⟨x,hx⟩ = 0 := (hg ⟨x,hx⟩).symm.trans hzero
      have hx' : (⟨x,hx⟩ : (ofR B S).carrier) = 0 := he (hh.trans (map_zero _).symm)
      exact hx0 (congrArg Subtype.val hx')
    obtain ⟨F,f,hf⟩ := ih K hKP
    refine ⟨E.prod F,pairHom g f,?_⟩
    intro x hx hzero
    have hz₁ : g.toLinearMap x = 0 := congrArg Prod.fst hzero
    have hz₂ : f.toLinearMap x = 0 := congrArg Prod.snd hzero
    exact hf x ⟨hx,(Submodule.mem_bot (modeAlg E.act)).mpr hz₁⟩ hz₂

/-- Every genuinely finite-length weak module of a C₂-cofinite VOA embeds into a
finite-length relative injective. No semisimplicity or tensor-category input is assumed. -/
theorem finite_injective_embedding (hC2 : C2Cofinite W) (B : WeakModule W M)
    (hB : IsFiniteLength (modeAlg B) M) :
    ∃ E : FiniteInjective W, ∃ f : B.Hom E.act, Function.Injective f.toLinearMap := by
  obtain ⟨E,f,hf⟩ := finite_injective_separates hC2 B hB ⊤
  refine ⟨E,f,fun x y h => ?_⟩
  apply sub_eq_zero.mp
  exact hf (x-y) (Submodule.mem_top) (by rw [map_sub,h,sub_self])

end VOA.C2Rigid.LocalInjective
