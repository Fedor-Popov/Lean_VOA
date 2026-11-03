import VOA.Classification.COne.McRaeM2Swap
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Order.Zorn

/-! # Extending finite-length injectivity to arbitrary weak modules

Every cyclic weak module of a C₂-cofinite VOA has finite length. Zorn's lemma
therefore extends a homomorphism into a finite-length injective object from
any weak submodule. This is the extension step needed to bound the maximal
P(z)-compatible module by a finite sum of injective hulls.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Huang.LogRemovalAdmissible
open VOA.Classification.COne
open VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.PlusRational
open VOA.Classification.COne.PlusFiniteLength
open VOA.Classification.COne.ABDWeakAdmissible

universe u
variable {V M I : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup I] [Module ℂ I]
  {W : VertexOperatorAlgebra V}

/-- A partial linear map whose domain is stable and which intertwines every mode. -/
structure PartialHom (B : WeakModule W M) (BI : WeakModule W I)
    extends M →ₗ.[ℂ] I where
  act_mem : ∀ a n {x}, x ∈ domain → B.act a n x ∈ domain
  map_act : ∀ a n (x : domain),
    toLinearPMap ⟨B.act a n x, act_mem a n x.2⟩ = BI.act a n (toLinearPMap x)

namespace PartialHom
variable {B : WeakModule W M} {BI : WeakModule W I}

theorem toLinearPMap_injective :
    Function.Injective (toLinearPMap : PartialHom B BI → M →ₗ.[ℂ] I) := by
  rintro ⟨p,hp,fp⟩ ⟨q,hq,fq⟩ h
  cases h
  rfl

instance : PartialOrder (PartialHom B BI) :=
  PartialOrder.lift _ toLinearPMap_injective

/-- The stable domain as a weak submodule. -/
def submodule (p : PartialHom B BI) : WeakModule.Submodule' B where
  carrier := p.domain
  act_mem := p.act_mem

/-- A partial map is a genuine homomorphism on its domain. -/
def hom (p : PartialHom B BI) : (WeakModule.submodule B p.submodule).Hom BI where
  toLinearMap := p.toFun
  map_act := p.map_act

/-- Turn a homomorphism on a weak submodule into a partial homomorphism. -/
def ofHom (S : WeakModule.Submodule' B) (f : (WeakModule.submodule B S).Hom BI) :
    PartialHom B BI where
  domain := S.carrier
  toFun := f.toLinearMap
  act_mem := S.act_mem
  map_act := f.map_act

theorem chainDirected (c : Set (PartialHom B BI)) (hc : IsChain (· ≤ ·) c) :
    DirectedOn (· ≤ ·) (toLinearPMap '' c) := by
  apply IsChain.directedOn
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hne
  exact hc hp hq (fun h => hne (congrArg toLinearPMap h))

/-- The union of a nonempty chain of partial weak-module homomorphisms. -/
def chainSup (c : Set (PartialHom B BI)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : PartialHom B BI := by
  let d : Set (M →ₗ.[ℂ] I) := toLinearPMap '' c
  have hd : DirectedOn (· ≤ ·) d := chainDirected c hc
  let s := LinearPMap.sSup d hd
  have hs : ∀ {x : M}, x ∈ s.domain → ∃ p ∈ c, x ∈ p.domain := by
    intro x hx
    obtain ⟨_,⟨p,hp,rfl⟩,hx⟩ :=
      (LinearPMap.mem_domain_sSup_iff (hne.image _) hd).mp hx
    exact ⟨p,hp,hx⟩
  have hstable : ∀ a n {x}, x ∈ s.domain → B.act a n x ∈ s.domain := by
    intro a n x hx
    obtain ⟨p,hp,hxp⟩ := hs hx
    exact (LinearPMap.le_sSup hd ⟨p,hp,rfl⟩).1 (p.act_mem a n hxp)
  refine { toLinearPMap := s, act_mem := hstable, map_act := ?_ }
  intro a n x
  obtain ⟨p,hp,hxp⟩ := hs x.2
  have hps : p.toLinearPMap ≤ s := LinearPMap.le_sSup hd ⟨p,hp,rfl⟩
  calc
    s ⟨B.act a n x,hstable a n x.2⟩ =
        p.toLinearPMap ⟨B.act a n x,p.act_mem a n hxp⟩ :=
      (hps.2 (x := ⟨B.act a n x,p.act_mem a n hxp⟩)
        (y := ⟨B.act a n x,hstable a n x.2⟩) rfl).symm
    _ = BI.act a n (p.toLinearPMap ⟨x,hxp⟩) := p.map_act a n ⟨x,hxp⟩
    _ = BI.act a n (s x) := congrArg (BI.act a n)
      (hps.2 (x := ⟨x,hxp⟩) rfl)

theorem le_chainSup (c : Set (PartialHom B BI)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {p : PartialHom B BI} (hp : p ∈ c) :
    p ≤ chainSup c hc hne := by
  change p.toLinearPMap ≤ (chainSup c hc hne).toLinearPMap
  exact LinearPMap.le_sSup
    (c := toLinearPMap '' c) (chainDirected c hc) (Set.mem_image_of_mem _ hp)

/-- Glue two compatible partial homomorphisms on the sum of their domains. -/
def sup (p q : PartialHom B BI)
    (h : ∀ (x : p.domain) (y : q.domain), (x : M) = y →
      p.toLinearPMap x = q.toLinearPMap y) : PartialHom B BI := by
  let s := p.toLinearPMap.sup q.toLinearPMap h
  have hstable : ∀ a n {x}, x ∈ s.domain → B.act a n x ∈ s.domain := by
    intro a n x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    rw [WeakModule.act_add_right]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (p.act_mem a n hy))
      (Submodule.mem_sup_right (q.act_mem a n hz))
  refine { toLinearPMap := s, act_mem := hstable, map_act := ?_ }
  intro a n x
  obtain ⟨y,hy,z,hz,he⟩ := Submodule.mem_sup.mp x.2
  rw [LinearPMap.sup_apply h ⟨y,hy⟩ ⟨z,hz⟩ x he,
    WeakModule.act_add_right]
  change p.toLinearPMap.sup q.toLinearPMap h _ = _
  calc
    _ = p.toLinearPMap ⟨B.act a n y,p.act_mem a n hy⟩ +
        q.toLinearPMap ⟨B.act a n z,q.act_mem a n hz⟩ :=
      LinearPMap.sup_apply h
        ⟨B.act a n y,p.act_mem a n hy⟩ ⟨B.act a n z,q.act_mem a n hz⟩
        ⟨B.act a n x,hstable a n x.2⟩ (by rw [← WeakModule.act_add_right,he])
    _ = _ := congrArg₂ (· + ·) (p.map_act a n ⟨y,hy⟩) (q.map_act a n ⟨z,hz⟩)

theorem le_sup_left (p q : PartialHom B BI) (h) : p ≤ PartialHom.sup p q h := by
  change p.toLinearPMap ≤ p.toLinearPMap.sup q.toLinearPMap h
  exact p.toLinearPMap.left_le_sup q.toLinearPMap h

theorem le_sup_right (p q : PartialHom B BI) (h) : q ≤ PartialHom.sup p q h := by
  change q.toLinearPMap ≤ p.toLinearPMap.sup q.toLinearPMap h
  exact p.toLinearPMap.right_le_sup q.toLinearPMap h

end PartialHom

/-- Extend a partial homomorphism across the cyclic module generated by one vector. -/
theorem extend_one (hC2 : C2Cofinite W) (B : WeakModule W M) (BI : WeakModule W I)
    (hI : IsInjFL BI) (p : PartialHom B BI) (x : M) :
    ∃ q : PartialHom B BI, p ≤ q ∧ x ∈ q.domain := by
  let C := ofR B (cyclic B x)
  let BC := WeakModule.submodule B C
  let z : C.carrier := ⟨x,Submodule.mem_span_singleton_self x⟩
  have hC : IsFiniteLength (modeAlg BC) C.carrier := by
    have ht := cyclicFiniteLength_of_c2Cofinite hC2 BC z
    rw [show cyclic BC z = ⊤ from cyclic_restriction_eq_top B x] at ht
    exact Submodule.topEquiv.isFiniteLength ht
  let U : WeakModule.Submodule' BC :=
    { carrier := p.domain.comap C.carrier.subtype
      act_mem := fun a n _ hy => p.act_mem a n hy }
  let BU := WeakModule.submodule BC U
  let g : BU.Hom BC := { toLinearMap := U.carrier.subtype, map_act := fun _ _ _ => rfl }
  let t : U.carrier →ₗ[ℂ] p.domain :=
    { toFun := fun y => ⟨(y : C.carrier),y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f : BU.Hom BI :=
    { toLinearMap := p.toFun.comp t
      map_act := fun a n y => p.map_act a n ⟨(y : C.carrier),y.2⟩ }
  obtain ⟨k,hk⟩ := hI BU BC hC g Subtype.val_injective f
  let q := PartialHom.ofHom C k
  have hagree : ∀ (v : p.domain) (y : q.domain), (v : M) = y →
      p.toLinearPMap v = q.toLinearPMap y := by
    intro v y hvy
    have hyp : (y : M) ∈ p.domain := hvy ▸ v.2
    let u : U.carrier := ⟨y,hyp⟩
    have he := hk u
    change k.toLinearMap y = p.toLinearPMap ⟨(y : M),hyp⟩ at he
    change p.toLinearPMap v = k.toLinearMap y
    rw [he]
    congr 1
    exact Subtype.ext hvy
  refine ⟨PartialHom.sup p q hagree,PartialHom.le_sup_left p q hagree,?_⟩
  exact (PartialHom.le_sup_right p q hagree).1 z.2

/-- For a C₂-cofinite VOA, finite-length injectivity extends from every weak submodule.
No grading or finite-length assumption is imposed on the ambient weak module. -/
theorem extend_submodule (hC2 : C2Cofinite W) (B : WeakModule W M) (BI : WeakModule W I)
    (hI : IsInjFL BI) (S : WeakModule.Submodule' B)
    (f : (WeakModule.submodule B S).Hom BI) :
    ∃ g : B.Hom BI, ∀ x : S.carrier, g.toLinearMap x = f.toLinearMap x := by
  classical
  let p0 := PartialHom.ofHom S f
  let s : Set (PartialHom B BI) := {p | p0 ≤ p}
  obtain ⟨p,hp,hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    let q := PartialHom.chainSup c hc ⟨y,hy⟩
    refine ⟨q,?_,fun z hz => PartialHom.le_chainSup c hc ⟨y,hy⟩ hz⟩
    exact (hcs hy).trans (PartialHom.le_chainSup c hc ⟨y,hy⟩ hy)) p0 (by change p0 ≤ p0; exact le_rfl)
  have htop : p.domain = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨q,hpq,hxq⟩ := extend_one hC2 B BI hI p x
    have hq : q ∈ s := hp.trans hpq
    have hqp : q ≤ p := hmax.2 hq hpq
    exact hqp.1 hxq
  let g : B.Hom BI :=
    { toLinearMap :=
        { toFun := fun x => p.toLinearPMap ⟨x,htop ▸ Submodule.mem_top⟩
          map_add' := fun x y => by
            simpa using p.toFun.map_add (⟨x,htop ▸ Submodule.mem_top⟩ : p.domain)
              (⟨y,htop ▸ Submodule.mem_top⟩ : p.domain)
          map_smul' := fun c x => by
            simpa using p.toFun.map_smul c (⟨x,htop ▸ Submodule.mem_top⟩ : p.domain) }
      map_act := fun a n x => p.map_act a n ⟨x,htop ▸ Submodule.mem_top⟩ }
  refine ⟨g,fun x => ?_⟩
  exact (hp.2 (x := x) (y := ⟨x,htop ▸ Submodule.mem_top⟩) rfl).symm


/-- If an essential submodule embeds into an injective object, its ambient weak
module embeds into the same object. This applies to the finite socle of a
maximal compatible P(z)-module. -/
theorem embed_of_essential_submodule (hC2 : C2Cofinite W)
    (B : WeakModule W M) (BI : WeakModule W I) (hI : IsInjFL BI)
    (S : WeakModule.Submodule' B) (f : (WeakModule.submodule B S).Hom BI)
    (hf : Function.Injective f.toLinearMap)
    (hess : ∀ R : WeakModule.Submodule' B,
      S.carrier ⊓ R.carrier = ⊥ → R.carrier = ⊥) :
    ∃ g : B.Hom BI, Function.Injective g.toLinearMap ∧
      ∀ x : S.carrier, g.toLinearMap x = f.toLinearMap x := by
  obtain ⟨g,hg⟩ := extend_submodule hC2 B BI hI S f
  let K : WeakModule.Submodule' B :=
    { carrier := g.toLinearMap.ker
      act_mem := by
        intro a n x hx
        change g.toLinearMap (B.act a n x) = 0
        rw [g.map_act,hx,WeakModule.act_zero_right] }
  have hSK : S.carrier ⊓ K.carrier = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : f.toLinearMap (⟨x,hx.1⟩ : S.carrier) = 0 := by
      rw [← hg]
      exact hx.2
    have hz : (⟨x,hx.1⟩ : S.carrier) = 0 := hf (by simpa using he)
    exact congrArg Subtype.val hz
  have hker : g.toLinearMap.ker = ⊥ := hess K hSK
  exact ⟨g,LinearMap.ker_eq_bot.mp hker,hg⟩

/-- An essential submodule embedding in a finite-length injective hull makes
its entire weak module finite-length. No finiteness premise on that ambient
module is used. -/
theorem finiteLength_of_essential_embedding (hC2 : C2Cofinite W)
    (B : WeakModule W M) (BI : WeakModule W I) (hI : IsInjFL BI)
    (hfl : IsFiniteLength (modeAlg BI) I) (S : WeakModule.Submodule' B)
    (f : (WeakModule.submodule B S).Hom BI) (hf : Function.Injective f.toLinearMap)
    (hess : ∀ R : WeakModule.Submodule' B,
      S.carrier ⊓ R.carrier = ⊥ → R.carrier = ⊥) :
    IsFiniteLength (modeAlg B) M := by
  obtain ⟨g,hg,-⟩ := embed_of_essential_submodule hC2 B BI hI S f hf hess
  exact VOA.Classification.COne.McRaeM1.finiteLength_of_injective_hom g hg hfl

end VOA.C2Rigid.LocalInjective
