import VOA.Classification.COne.OrbMcRaeCover
import VOA.Classification.COne.OrbTopZhu

/-!
# McRae's Zhu criterion = the categorical half (covers), and its consumers

`OrbMcRaeCover` proves the Zhu half of McRae arXiv:2108.01898v3 §5.3 (case `A = V`):
`C₂` + semisimple `A(W)` + McRae covers ⟹ admissibly rational, and that the cover hypothesis is
exactly equivalent to rationality under `C₂` + semisimple `A(W)`.  Here:

* `McRaeCategoricalFact` — the categorical half of McRae's theorem as ONE named `Prop` (NOT proved,
  NOT an axiom): every strongly finite VOA with semisimple Zhu algebra has McRae covers.
* `zhuSemisimpleRationalityFact_iff_mcRaeCategorical` — `OrbRat.ZhuSemisimpleRationalityFact`
  (McRae's Main Theorem 3) is EQUIVALENT to `McRaeCategoricalFact`.
* `cubicModel_admissiblyRational_iff_mcRaeCover` — B3 for `A₄` is EXACTLY
  `McRaeCoverFact cubicModel`.
* `v2mPlusRationalFactGe2_of_mcRaeCover` — B1 from covers for `V_{2m}⁺`.
* `gannonRayhaunConverse_of_mcRaeCategorical` — the universe-zero converse with McRae's theorem
  replaced by its categorical half.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbMcRae

open VOA VertexOperatorAlgebra

universe u

/-! ## The two literature inputs inside a McRae cover -/

section Split

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- A projective cover in the sense of Bass (projective, superfluous kernel), relative to
finite-length weak modules.  Huang (arXiv:0712.4109, JPAA 213 (2009)) constructs these for every
simple module of a `C₂`-cofinite VOA. -/
structure HuangCover {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X) where
  /-- The carrier of the cover. -/
  P : Type u
  [acg : AddCommGroup P]
  [mod : Module ℂ P]
  /-- The weak-module structure of the cover. -/
  BP : WeakModule W P
  /-- The covering surjection. -/
  p : BP.Hom B
  finiteLength : IsFiniteLength (modeAlg BP) P
  proj : IsProjFL BP
  surj : Function.Surjective p.toLinearMap
  superfluous : ∀ N : Submodule (modeAlg BP) P, PlusSplitting.modeMap p N = ⊤ → N = ⊤

attribute [instance] HuangCover.acg HuangCover.mod

/-- **Huang's projective covers** (arXiv:0712.4109): every simple weak module has one.
Named `Prop`; NOT proved, NOT an axiom. -/
def HuangCoverFact (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X),
    IsSimpleModule (modeAlg B) X → Nonempty (HuangCover B)

/-- **Unimodular socle**: every projective cover of a simple `S` has essential socle `S`
(McRae Prop 5.14 via factorizability and ENO unimodularity, plus projective = injective in a
rigid category, EGNO Prop 6.1.3).  Named `Prop`; NOT proved, NOT an axiom. -/
def UnimodularSocleFact (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X),
    IsSimpleModule (modeAlg B) X → ∀ C : HuangCover B,
      ∃ i : B.Hom C.BP, Function.Injective i.toLinearMap ∧
        ∀ N : Submodule (modeAlg C.BP) C.P, N ≠ ⊥ → PlusSplitting.modeMap i ⊤ ≤ N

/-- The two inputs assemble into McRae covers. -/
theorem mcRaeCoverFact_of_huang_unimodular (hH : HuangCoverFact W)
    (hU : UnimodularSocleFact W) : McRaeCoverFact W := by
  intro X _ _ B hS
  obtain ⟨C⟩ := hH B hS
  obtain ⟨i, hi, hsoc⟩ := hU B hS C
  exact ⟨{ P := C.P, BP := C.BP, p := C.p, i := i, finiteLength := C.finiteLength,
            proj := C.proj, surj := C.surj, superfluous := C.superfluous, inj := hi,
            socle := hsoc }⟩

/-- Rationality from Huang's covers and the unimodular socle. -/
theorem admissiblyRational_of_huang_unimodular (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) (hH : HuangCoverFact W)
    (hU : UnimodularSocleFact W) : AdmissiblyRational W :=
  admissiblyRational_of_mcRaeCover hC2 hss (mcRaeCoverFact_of_huang_unimodular hH hU)

end Split

/-- **The categorical half of McRae's Main Theorem 3** (Huang's projective covers + rigidity +
factorizability ⟹ unimodular covers), as a named `Prop`: NOT proved, NOT an axiom. -/
def McRaeCategoricalFact : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyFinite W → (letI := instRingA W; IsSemisimpleRing (VOA.A W)) → McRaeCoverFact W

/-- McRae's criterion from its categorical half. -/
theorem zhuSemisimpleRationalityFact_of_mcRaeCategorical (h : McRaeCategoricalFact.{u}) :
    OrbRat.ZhuSemisimpleRationalityFact.{u} :=
  fun 𝒱 _ _ W hW hss => admissiblyRational_of_mcRaeCover hW.c2Cofinite hss (h 𝒱 W hW hss)

/-- The two named `Prop`s are equivalent: nothing is lost by the reduction. -/
theorem zhuSemisimpleRationalityFact_iff_mcRaeCategorical :
    OrbRat.ZhuSemisimpleRationalityFact.{u} ↔ McRaeCategoricalFact.{u} :=
  ⟨fun h 𝒱 _ _ W hW hss =>
      mcRaeCoverFact_of_admissiblyRational hW.c2Cofinite hss (h 𝒱 W hW hss),
    zhuSemisimpleRationalityFact_of_mcRaeCategorical⟩

/-- **B3 for `A₄`, exactly**: the tetrahedral model `V₂^{A₄}` is rational iff its simple
modules have McRae covers. -/
theorem cubicModel_admissiblyRational_iff_mcRaeCover :
    AdmissiblyRational OrbRat2.cubicModel ↔ McRaeCoverFact OrbRat2.cubicModel :=
  (mcRaeCoverFact_iff_admissiblyRational OrbTop.cubicModel_stronglyFinite.c2Cofinite
    OrbTop.cubicModel_zhuSemisimple).symm

/-- `V_{2m}⁺` (`m ≥ 2`) is rational given McRae covers. -/
theorem v2mPlusRationalFactGe2_of_mcRaeCover
    (h : ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → McRaeCoverFact (V2mPlus m hm)) :
    V2mPlusRationalFactGe2 :=
  fun m hm hm2 => admissiblyRational_of_mcRaeCover (V2mPlus_c2Cofinite m hm)
    (V2mPlus_zhuSemisimple m hm hm2) (h m hm hm2)

/-- The universe-zero converse, with McRae's theorem replaced by its categorical half. -/
theorem gannonRayhaunConverse_of_mcRaeCategorical (hM : McRaeCategoricalFact.{0})
    (hZexc : OrbRat.FiniteV2OrbifoldZhuSemisimpleOfC2Fact)
    (hSolv : SolvableExceptionalOrbifoldC2Fact) (hXu : XuIcosahedralPoissonRelations)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact) : GannonRayhaunConverse.{0} :=
  OrbRat.gannonRayhaunConverse_of_zhuCriterion
    (zhuSemisimpleRationalityFact_of_mcRaeCategorical hM) hZexc hSolv hXu hPU

/-- B3 for `A₄` from Huang's covers and the unimodular socle of the tetrahedral model. -/
theorem cubicModel_admissiblyRational_of_huang_unimodular
    (hH : HuangCoverFact OrbRat2.cubicModel) (hU : UnimodularSocleFact OrbRat2.cubicModel) :
    AdmissiblyRational OrbRat2.cubicModel :=
  admissiblyRational_of_huang_unimodular OrbTop.cubicModel_stronglyFinite.c2Cofinite
    OrbTop.cubicModel_zhuSemisimple hH hU

end VOA.Classification.COne.OrbMcRae
