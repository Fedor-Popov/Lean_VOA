import VOA.Classification.COne.OrbMcRaeMain

/-!
# McRae's route: projective covers from finite-length projectives

`OrbMcRae.HuangCoverFact W` asks for a projective cover (finite length, projective relative to
finite-length weak modules, superfluous kernel) of every simple weak module.  Huang
(arXiv:0712.4109, Thm 3.23) builds it in two steps:

1. a finite-length projective `M_N(E)` mapping onto the simple module (Thm 3.22: generalized Verma
   module of a projective `A_N(V)`-module `E`);
2. the passage from "projective mapping onto `S`" to "projective cover of `S`" (the
   indecomposable-summand argument in the proof of Thm 3.23).

This file proves step 2 **in general**, for an arbitrary vertex operator algebra and an arbitrary
target weak module, with no Zhu-algebra input.  So `HuangCoverFact W` is reduced EXACTLY to
`EnoughProjFL W` (every simple weak module is the image of a finite-length projective):

* `huangCover_of_projFL` — a finite-length `IsProjFL` weak module `P ↠ B` contains a
  submodule `Q` that is a projective cover `Q ↠ B`.
* `huangCoverFact_iff_enoughProjFL : HuangCoverFact W ↔ EnoughProjFL W`.
* `enoughProjFL_iff_nonzero` — it is enough to have a NONZERO map onto each simple module.

## The argument (a minimality version of Bass's argument, no Fitting lemma)

Let `p : P ↠ B` with `P` of finite length and projective.  Choose a submodule `Q ≤ P` that is
minimal among submodules with `p(Q) = B` (Artinian).  Minimality is exactly the statement that the
kernel of `p|_Q` is superfluous in `Q`.  Projectivity of `P` lifts `p` along `p|_Q` to
`g : P → Q`; the endomorphism `γ = g|_Q` of `Q` again maps onto `B`, so `γ(Q) = Q` by minimality.
A surjective endomorphism of a Noetherian module is injective, so `γ` is an automorphism, and
`γ⁻¹ ∘ g` is a retraction of `P` onto `Q`.  A retract of a projective is projective.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.McRaeM1

open VOA VertexOperatorAlgebra PlusSplitting OrbMcRae

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Basic

variable {X Y Z : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]

/-- Composition of weak-module homomorphisms. -/
def homComp {A : WeakModule W X} {B : WeakModule W Y} {C : WeakModule W Z}
    (g : B.Hom C) (f : A.Hom B) : A.Hom C where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_act u n x := by simp only [LinearMap.comp_apply, f.map_act, g.map_act]

@[simp] theorem homComp_apply {A : WeakModule W X} {B : WeakModule W Y} {C : WeakModule W Z}
    (g : B.Hom C) (f : A.Hom B) (x : X) :
    (homComp g f).toLinearMap x = g.toLinearMap (f.toLinearMap x) := rfl

theorem mem_modeMap {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B)
    (P : Submodule (modeAlg A) X) (y : Y) :
    y ∈ modeMap π P ↔ ∃ x, x ∈ P ∧ π.toLinearMap x = y := Iff.rfl

theorem modeMap_homComp {A : WeakModule W X} {B : WeakModule W Y} {C : WeakModule W Z}
    (g : B.Hom C) (f : A.Hom B) (P : Submodule (modeAlg A) X) :
    modeMap (homComp g f) P = modeMap g (modeMap f P) := by
  ext z
  simp only [mem_modeMap, homComp_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f.toLinearMap x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem modeMap_top_of_surjective {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B)
    (hπ : Function.Surjective π.toLinearMap) : modeMap π ⊤ = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨x, rfl⟩ := hπ y
  exact ⟨x, Submodule.mem_top, rfl⟩

theorem surjective_of_modeMap_top {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B)
    (h : modeMap π ⊤ = ⊤) : Function.Surjective π.toLinearMap := by
  intro y
  have hy : y ∈ modeMap π ⊤ := h ▸ Submodule.mem_top
  obtain ⟨x, -, hx⟩ := hy
  exact ⟨x, hx⟩

theorem modeComap_modeMap_of_injective {A : WeakModule W X} {B : WeakModule W Y}
    (π : A.Hom B) (hπ : Function.Injective π.toLinearMap) (P : Submodule (modeAlg A) X) :
    modeComap π (modeMap π P) = P := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := (mem_modeMap π P _).mp hx
    exact hπ he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem modeMap_injective {A : WeakModule W X} {B : WeakModule W Y}
    (π : A.Hom B) (hπ : Function.Injective π.toLinearMap) :
    Function.Injective (modeMap π) := by
  intro P Q h
  rw [← modeComap_modeMap_of_injective π hπ P, h, modeComap_modeMap_of_injective π hπ Q]

/-- Finite length descends along an injective weak-module homomorphism (the source's own mode
algebra is used on the source). -/
theorem finiteLength_of_injective_hom {A : WeakModule W X} {B : WeakModule W Y}
    (π : A.Hom B) (hπ : Function.Injective π.toLinearMap)
    (hB : IsFiniteLength (modeAlg B) Y) : IsFiniteLength (modeAlg A) X := by
  have hf : StrictMono (modeMap π) :=
    (modeMap_mono π).strictMono_of_injective (modeMap_injective π hπ)
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hB
  letI := hN
  letI := hA
  haveI : WellFoundedLT (Submodule (modeAlg A) X) := hf.wellFoundedLT
  haveI : WellFoundedGT (Submodule (modeAlg A) X) := hf.wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff'.mpr inferInstance, inferInstance⟩

/-- A weak-module endomorphism commutes with the whole mode algebra. -/
theorem endo_comm {A : WeakModule W X} (γ : A.Hom A) {f : Module.End ℂ X}
    (hf : f ∈ modeAlg A) : ∀ x, γ.toLinearMap (f x) = f (γ.toLinearMap x) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨u, n, rfl⟩ := hf
    intro x
    exact γ.map_act u n x
  | algebraMap c =>
    intro x
    simp only [Module.algebraMap_end_apply, map_smul]
  | add f g _ _ hf hg =>
    intro x
    simp only [LinearMap.add_apply, map_add, hf, hg]
  | mul f g _ _ hf hg =>
    intro x
    simp only [Module.End.mul_apply, hf, hg]

/-- A weak-module endomorphism as a `modeAlg`-linear map. -/
def endoLinear {A : WeakModule W X} (γ : A.Hom A) : X →ₗ[modeAlg A] X where
  toFun := γ.toLinearMap
  map_add' := map_add _
  map_smul' r x := endo_comm γ r.2 x

/-- A bijective weak-module homomorphism has a weak-module inverse. -/
def homInv {A : WeakModule W X} {B : WeakModule W Y} (γ : A.Hom B)
    (hγ : Function.Bijective γ.toLinearMap) : B.Hom A where
  toLinearMap := (LinearEquiv.ofBijective γ.toLinearMap hγ).symm.toLinearMap
  map_act u n y := by
    apply hγ.1
    have h1 : ∀ z, γ.toLinearMap ((LinearEquiv.ofBijective γ.toLinearMap hγ).symm z) = z :=
      fun z => (LinearEquiv.ofBijective γ.toLinearMap hγ).apply_symm_apply z
    simp only [LinearEquiv.coe_coe]
    rw [h1, γ.map_act, h1]

theorem homInv_apply_hom {A : WeakModule W X} {B : WeakModule W Y} (γ : A.Hom B)
    (hγ : Function.Bijective γ.toLinearMap) (x : X) :
    (homInv γ hγ).toLinearMap (γ.toLinearMap x) = x :=
  (LinearEquiv.ofBijective γ.toLinearMap hγ).symm_apply_apply x

/-- The inclusion of a mode-stable submodule, as a weak-module homomorphism. -/
def subIncl (A : WeakModule W X) (Q : Submodule (modeAlg A) X) :
    (WeakModule.submodule A (ofR A Q)).Hom A where
  toLinearMap := (ofR A Q).carrier.subtype
  map_act _ _ _ := rfl

theorem subIncl_injective (A : WeakModule W X) (Q : Submodule (modeAlg A) X) :
    Function.Injective (subIncl A Q).toLinearMap := Subtype.val_injective

theorem modeMap_subIncl_top (A : WeakModule W X) (Q : Submodule (modeAlg A) X) :
    modeMap (subIncl A Q) ⊤ = Q := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Submodule.mem_top, rfl⟩

/-- A retract of an `IsProjFL` weak module is `IsProjFL`. -/
theorem isProjFL_of_retract {A : WeakModule W X} {B : WeakModule W Y} (hB : IsProjFL B)
    (ι : A.Hom B) (r : B.Hom A) (hr : ∀ x, r.toLinearMap (ι.toLinearMap x) = x) :
    IsProjFL A := by
  intro Y' Z' _ _ _ _ BY BZ hY g hg f
  obtain ⟨k, hk⟩ := hB BY BZ hY g hg (homComp f r)
  refine ⟨homComp k ι, fun x => ?_⟩
  rw [homComp_apply, hk, homComp_apply, hr]

end Basic

/-! ## The cover extraction -/

section Cover

variable {X P : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup P] [Module ℂ P]

/-- **Projective covers from finite-length projectives** (the cover half of Huang's
Thm 3.23, for an arbitrary VOA and arbitrary target).  If a finite-length weak module `P`,
projective relative to finite-length weak modules, maps onto `B`, then `B` has a projective cover
(`HuangCover`), realized as a direct summand of `P`. -/
theorem huangCover_of_projFL (B : WeakModule W X) (BP : WeakModule W P)
    (hFL : IsFiniteLength (modeAlg BP) P) (hproj : IsProjFL BP) (p : BP.Hom B)
    (hp : Function.Surjective p.toLinearMap) : Nonempty (HuangCover B) := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hFL
  letI := hA
  -- a minimal submodule mapping onto `B`
  obtain ⟨Q0, hQ0, hmin⟩ := WellFounded.has_min wellFounded_lt
    {N : Submodule (modeAlg BP) P | modeMap p N = ⊤} ⟨⊤, modeMap_top_of_surjective p hp⟩
  have hQ0 : modeMap p Q0 = ⊤ := hQ0
  let BQ : WeakModule W (ofR BP Q0).carrier := WeakModule.submodule BP (ofR BP Q0)
  let ι : BQ.Hom BP := subIncl BP Q0
  have hι : Function.Injective ι.toLinearMap := subIncl_injective BP Q0
  let pQ : BQ.Hom B := homComp p ι
  -- minimality: every submodule of `Q` mapping onto `B` is all of `Q`
  have hsup : ∀ N : Submodule (modeAlg BQ) (ofR BP Q0).carrier, modeMap pQ N = ⊤ → N = ⊤ := by
    intro N hN'
    have hle : modeMap ι N ≤ Q0 :=
      calc modeMap ι N ≤ modeMap ι ⊤ := modeMap_mono ι le_top
        _ = Q0 := modeMap_subIncl_top BP Q0
    have hon : modeMap p (modeMap ι N) = ⊤ := by rw [← modeMap_homComp]; exact hN'
    have heq : modeMap ι N = Q0 := by
      rcases hle.lt_or_eq with hlt | he
      · exact absurd hlt (hmin _ hon)
      · exact he
    apply modeMap_injective ι hι
    rw [heq]
    exact (modeMap_subIncl_top BP Q0).symm
  have hFLQ : IsFiniteLength (modeAlg BQ) (ofR BP Q0).carrier :=
    finiteLength_of_injective_hom ι hι hFL
  have hpQ : Function.Surjective pQ.toLinearMap := by
    apply surjective_of_modeMap_top
    rw [modeMap_homComp, modeMap_subIncl_top]
    exact hQ0
  -- lift `p` through `p|_Q`
  obtain ⟨g, hg⟩ := hproj BQ B hFLQ pQ hpQ p
  let γ : BQ.Hom BQ := homComp g ι
  have hγs : Function.Surjective γ.toLinearMap := by
    apply surjective_of_modeMap_top
    apply hsup
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨x, rfl⟩ := hpQ y
    refine ⟨γ.toLinearMap x, ⟨x, Submodule.mem_top, rfl⟩, ?_⟩
    change pQ.toLinearMap (g.toLinearMap (ι.toLinearMap x)) = pQ.toLinearMap x
    rw [hg]
    rfl
  have hγi : Function.Injective γ.toLinearMap := by
    obtain ⟨hNQ, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hFLQ
    letI := hNQ
    exact IsNoetherian.injective_of_surjective_endomorphism (endoLinear γ) hγs
  let r : BP.Hom BQ := homComp (homInv γ ⟨hγi, hγs⟩) g
  have hr : ∀ x, r.toLinearMap (ι.toLinearMap x) = x := fun x =>
    homInv_apply_hom γ ⟨hγi, hγs⟩ x
  exact ⟨{ P := (ofR BP Q0).carrier, BP := BQ, p := pQ, finiteLength := hFLQ,
            proj := isProjFL_of_retract hproj ι r hr, surj := hpQ, superfluous := hsup }⟩

end Cover

/-! ## The exact reduction of `HuangCoverFact` -/

/-- **Enough finite-length projectives**: every simple weak module is the image of a finite-length
weak module that is projective relative to finite-length weak modules.  Named `Prop`; for
`C₂`-cofinite `W` it follows from `McRaeM1Main.huangCoverFact_of_c2` and the equivalence below.
This is Huang's Thm 3.22 content (generalized Verma modules `M_N(E)` of
projective `A_N(V)`-modules). -/
def EnoughProjFL (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X),
    IsSimpleModule (modeAlg B) X →
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module ℂ P) (BP : WeakModule W P),
        IsFiniteLength (modeAlg BP) P ∧ IsProjFL BP ∧
          ∃ p : BP.Hom B, Function.Surjective p.toLinearMap

/-- The same with a merely NONZERO map onto the simple module. -/
def EnoughProjFLNonzero (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X),
    IsSimpleModule (modeAlg B) X →
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module ℂ P) (BP : WeakModule W P),
        IsFiniteLength (modeAlg BP) P ∧ IsProjFL BP ∧
          ∃ p : BP.Hom B, p.toLinearMap ≠ 0

/-- A nonzero homomorphism onto a simple weak module is surjective. -/
theorem surjective_of_ne_zero {X P : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup P]
    [Module ℂ P] {B : WeakModule W X} (hS : IsSimpleModule (modeAlg B) X) {BP : WeakModule W P}
    (p : BP.Hom B) (hp : p.toLinearMap ≠ 0) : Function.Surjective p.toLinearMap := by
  apply surjective_of_modeMap_top
  rcases hS.eq_bot_or_eq_top (modeMap p ⊤) with h | h
  · exfalso
    apply hp
    ext x
    have hx : p.toLinearMap x ∈ modeMap p ⊤ := ⟨x, Submodule.mem_top, rfl⟩
    rw [h] at hx
    exact (Submodule.mem_bot _).mp hx
  · exact h

theorem enoughProjFL_iff_nonzero : EnoughProjFL W ↔ EnoughProjFLNonzero W := by
  constructor
  · intro h X _ _ B hS
    obtain ⟨P, _, _, BP, hFL, hpr, p, hp⟩ := h B hS
    refine ⟨P, _, _, BP, hFL, hpr, p, fun h0 => ?_⟩
    obtain ⟨x, hx⟩ : ∃ x : X, x ≠ 0 := by
      obtain ⟨x, y, hxy⟩ := (IsSimpleModule.nontrivial (modeAlg B) X).exists_pair_ne
      by_cases hx : x = 0
      · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
      · exact ⟨x, hx⟩
    obtain ⟨z, hz⟩ := hp x
    rw [h0] at hz
    exact hx hz.symm
  · intro h X _ _ B hS
    obtain ⟨P, _, _, BP, hFL, hpr, p, hp⟩ := h B hS
    exact ⟨P, _, _, BP, hFL, hpr, p, surjective_of_ne_zero hS p hp⟩

/-- `EnoughProjFL ⟹ HuangCoverFact`. -/
theorem huangCoverFact_of_enoughProjFL (h : EnoughProjFL W) : HuangCoverFact W := by
  intro X _ _ B hS
  obtain ⟨P, _, _, BP, hFL, hpr, p, hp⟩ := h B hS
  exact huangCover_of_projFL B BP hFL hpr p hp

/-- The reduction is exact: `HuangCoverFact W ↔ EnoughProjFL W`. -/
theorem huangCoverFact_iff_enoughProjFL : HuangCoverFact W ↔ EnoughProjFL W := by
  refine ⟨fun h X _ _ B hS => ?_, huangCoverFact_of_enoughProjFL⟩
  obtain ⟨C⟩ := h B hS
  exact ⟨C.P, _, _, C.BP, C.finiteLength, C.proj, C.p, C.surj⟩

end VOA.Classification.COne.McRaeM1
