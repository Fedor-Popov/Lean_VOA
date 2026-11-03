import VOA.Classification.COne.OrbRatStatement
import VOA.Classification.COne.OrbRatSplitting
import VOA.Classification.COne.PlusTwistCharacters
import VOA.Huang.ZhuSemisimple
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom

/-!
# McRae's Zhu-algebra rationality criterion and the `V_{2m}⁺` converse

R. McRae, *On rationality for `C₂`-cofinite vertex operator algebras*, arXiv:2108.01898v3,
**Main Theorem 3 = Corollary 5.19**: an `ℕ`-graded, simple, self-contragredient, `C₂`-cofinite
("strongly finite") VOA whose Zhu algebra is semisimple is rational.  McRae's rationality (his
§2.2 clause (4): every `½ℕ`-gradable weak module is a direct sum of irreducible grading-restricted
modules) implies the library's `AdmissiblyRational`.  The criterion is stated here as the named
`Prop` `ZhuSemisimpleRationalityFact` — NOT proved, NOT an axiom.  McRae explicitly lists `V_L⁺` as
an example of a VOA whose rationality this criterion recovers (§1.1).

Consequences proved here (`#print axioms`-clean; conditional on the named `Prop`s):

* `V2mPlus_stronglyFinite` — unconditional: `V_{2m}⁺` is strongly finite (all `m ≥ 1`), from the
  general orbifold theorem `orbifold_stronglyFinite` and `V2mPlus_c2Cofinite`.
* `v2mPlusRationalFactGe2_of_zhuSemisimpleRationality` — McRae's criterion ⟹
  `V2mPlusRationalFactGe2`,
  because the Zhu algebra of `V_{2m}⁺` is already proved semisimple (`V2mPlus_zhuSemisimple`).
* `zhuSemisimpleRationality_iff_resonant` — the criterion is EQUIVALENT to resonant whole splitting
  for every strongly finite VOA with semisimple Zhu algebra (`OrbRatSplitting`).
* `v2mPlusRationalFactGe2_iff_resonantWholeSplitting` — the exact `V_{2m}⁺` residual.
* `admissiblyRational_iff_zhuSemisimple_of_criterion` — for strongly finite `W`, rationality ⟺ Zhu
  semisimplicity, given the criterion (the `⟹` half is Zhu/DLM, proved in the library relative to
  `VOA.pbw`).
* `gannonRayhaunConverse_of_zhuCriterion` — the universe-zero converse from the criterion, Zhu
  semisimplicity of `C₂`-cofinite finite orbifolds of `V₂`, and the three exceptional inputs.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat

open VOA VertexOperatorAlgebra VOA.VHat VOA.VHat.DLM3

universe u

/-- **McRae, arXiv:2108.01898v3, Main Theorem 3 / Corollary 5.19.**  A strongly finite VOA with
semisimple Zhu algebra is (admissibly) rational.  OPEN here (stated, not proved). -/
def ZhuSemisimpleRationalityFact : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyFinite W → (letI := instRingA W; IsSemisimpleRing (VOA.A W)) → AdmissiblyRational W

/-- The criterion is exactly resonant whole splitting, over strongly finite VOAs with semisimple
Zhu algebra.  Nothing is gained or lost by the reformulation. -/
theorem zhuSemisimpleRationality_iff_resonant :
    ZhuSemisimpleRationalityFact.{u} ↔
      ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
        StronglyFinite W → (letI := instRingA W; IsSemisimpleRing (VOA.A W)) →
          ResonantWholeSplitting W := by
  constructor
  · intro h 𝒱 _ _ W hW hss
    exact (admissiblyRational_iff_resonantWholeSplitting hW.c2Cofinite hss).mp (h 𝒱 W hW hss)
  · intro h 𝒱 _ _ W hW hss
    exact (admissiblyRational_iff_resonantWholeSplitting hW.c2Cofinite hss).mpr (h 𝒱 W hW hss)

/-- The `θ`-orbifold group is finite. -/
instance finite_zpowers_thetaV2m (m : ℕ) (hm : 1 ≤ m) :
    Finite (Subgroup.zpowers (thetaV2m m hm)) :=
  finite_zpowers_of_isOfFinOrder (isOfFinOrder_of_mul_self (thetaV2m_mul_self m hm))

/-- **`V_{2m}⁺` is strongly finite** (simple, self-dual, `C₂`-cofinite), for every `m ≥ 1`. -/
theorem V2mPlus_stronglyFinite (m : ℕ) (hm : 1 ≤ m) : StronglyFinite (V2mPlus m hm) :=
  orbifold_stronglyFinite (V2m_stronglyRational m hm).toStronglyFinite _ (V2mPlus_c2Cofinite m hm)

/-- **McRae's Zhu criterion closes the `V_{2m}⁺` rationality gap**: the Zhu algebra of
`V_{2m}⁺` is proved semisimple (`V2mPlus_zhuSemisimple`), and `V_{2m}⁺` is strongly finite. -/
theorem v2mPlusRationalFactGe2_of_zhuSemisimpleRationality
    (h : ZhuSemisimpleRationalityFact.{0}) : V2mPlusRationalFactGe2 :=
  fun m hm hm2 => h _ _ (V2mPlus_stronglyFinite m hm) (V2mPlus_zhuSemisimple m hm hm2)

/-- `V_{2m}⁺` is strongly rational (`m ≥ 2`), given McRae's Zhu criterion. -/
theorem V2mPlus_stronglyRational_of_zhuSemisimpleRationality
    (h : ZhuSemisimpleRationalityFact.{0}) (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    StronglyRational (V2mPlus m hm) :=
  { V2mPlus_stronglyFinite m hm with
    rational := v2mPlusRationalFactGe2_of_zhuSemisimpleRationality h m hm hm2 }

/-- **The exact remaining `V_{2m}⁺` statement**: rationality for all `m ≥ 2` is equivalent to
resonant whole splitting for all `m ≥ 2`. -/
theorem v2mPlusRationalFactGe2_iff_resonantWholeSplitting :
    V2mPlusRationalFactGe2 ↔
      ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ResonantWholeSplitting (V2mPlus m hm) :=
  ⟨fun h m hm hm2 => (admissiblyRational_iff_resonantWholeSplitting (V2mPlus_c2Cofinite m hm)
      (V2mPlus_zhuSemisimple m hm hm2)).mp (h m hm hm2),
    fun h m hm hm2 => (admissiblyRational_iff_resonantWholeSplitting (V2mPlus_c2Cofinite m hm)
      (V2mPlus_zhuSemisimple m hm hm2)).mpr (h m hm hm2)⟩

/-- For a strongly finite VOA, rationality is equivalent to Zhu semisimplicity, given McRae's
criterion.  The forward half is Zhu / DLM (`isSemisimpleRing_A_of_admissiblyRational`), whose PBW
datum is supplied by the theorem `VOA.pbw`. -/
theorem admissiblyRational_iff_zhuSemisimple_of_criterion (h : ZhuSemisimpleRationalityFact.{u})
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (hW : StronglyFinite W) :
    AdmissiblyRational W ↔ (letI := instRingA W; IsSemisimpleRing (VOA.A W)) :=
  ⟨fun hR => VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational
      (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hR,
    fun hss => h 𝒱 W hW hss⟩

/-- Zhu semisimplicity of `C₂`-cofinite finite orbifolds of `V₂`.  TRUE (it follows from their
rationality, McRae arXiv:1910.13226v2 Cor. 4.23, by Zhu's theorem), OPEN here. -/
def FiniteV2OrbifoldZhuSemisimpleOfC2Fact : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G], C2Cofinite (orbifoldVOA G) →
    letI := instRingA (orbifoldVOA G); IsSemisimpleRing (VOA.A (orbifoldVOA G))

/-- McRae's Zhu criterion plus Zhu semisimplicity gives the exceptional rationality input. -/
theorem finiteV2OrbifoldRationalOfC2Fact_of_zhu (h : ZhuSemisimpleRationalityFact.{0})
    (hz : FiniteV2OrbifoldZhuSemisimpleOfC2Fact) : FiniteV2OrbifoldRationalOfC2Fact :=
  fun G _ hC2 => h _ _ (orbifold_stronglyFinite (V2m_stronglyRational 1 le_rfl).toStronglyFinite
    G hC2) (hz G hC2)

/-- Conversely the Zhu input is implied by the rationality input (Zhu/DLM, relative to
`VOA.pbw`), so `FiniteV2OrbifoldZhuSemisimpleOfC2Fact` is no stronger than what it replaces. -/
theorem finiteV2OrbifoldZhuSemisimpleOfC2Fact_of_rational (h : FiniteV2OrbifoldRationalOfC2Fact) :
    FiniteV2OrbifoldZhuSemisimpleOfC2Fact :=
  fun G _ hC2 => VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational
    (voaPBWBottomProjection (parabolicRepOfAMod _ (regularAMod _))) (h G hC2)

/-- **The Gannon–Rayhaun converse (carrier universe zero) via McRae's Zhu criterion.**  The
`V_{2m}⁺` clause needs ONLY the criterion (Zhu semisimplicity is proved); the exceptional clauses
need the criterion, their Zhu semisimplicity, Miyamoto's `C₂` for `A₄, S₄`, Xu's relations, and
positivity.  NOT unconditional. -/
theorem gannonRayhaunConverse_of_zhuCriterion (hZ : ZhuSemisimpleRationalityFact.{0})
    (hZexc : FiniteV2OrbifoldZhuSemisimpleOfC2Fact)
    (hSolv : SolvableExceptionalOrbifoldC2Fact) (hXu : XuIcosahedralPoissonRelations)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact) : GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_exceptional_inputs
    (v2mPlusRationalFactGe2_of_zhuSemisimpleRationality hZ) hSolv hXu
    (finiteV2OrbifoldRationalOfC2Fact_of_zhu hZ hZexc) hPU

end VOA.Classification.COne.OrbRat
