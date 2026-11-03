import VOA.Classification.COne.OrbRatStructure
import VOA.Classification.COne.ExceptionalOrbifoldNice
import VOA.Classification.COne.LatticeStronglyRational

/-!
# Orbifold rationality from `C₂`-cofiniteness: the general statement and its specializations

This file states, as named `Prop`s (never axioms), the general orbifold rationality theorem in
three nested strengths, and proves the implications from them to the two rationality inputs of
the Gannon–Rayhaun converse:

* `OrbifoldRationalOfC2` — for every strongly rational `W` and every finite `G ≤ Aut W`, if `W^G`
  is `C₂`-cofinite then `W^G` is admissibly rational.
  Source: R. McRae, *Twisted modules and G-equivariantization in logarithmic conformal field
  theory*, CMP 383 (2021) 1939–2019, arXiv:1910.13226v2, Corollary 4.23 (strong rationality of
  `W^G` for strongly rational `W` and finite `G`, assuming `W^G` is `C₂`-cofinite).  For solvable
  `G` also Carnahan–Miyamoto, arXiv:1603.05645v4, Corollary 5.25.
* `CyclicOrbifoldRationalOfC2` — the same for `G = ⟨g⟩` with `g` of finite order (Carnahan–Miyamoto
  §5 treats exactly this case before inducting over a solvable series).
* `InvolutionOrbifoldRationalOfC2` — the same for `g² = 1`.

Proved here (all `#print axioms`-clean, CONDITIONAL on the named `Prop`):
* `orbifoldRational_cyclic`, `cyclic_involution` — the nesting;
* `orbifold_stronglyRational_of_c2` — with simplicity/self-duality from `OrbRatStructure`;
* `finiteV2OrbifoldRationalOfC2Fact_of_orbifoldRational` — McRae ⟹
  `FiniteV2OrbifoldRationalOfC2Fact`;
* `v2mPlusRationalFactGe2_of_involution` — the involution case ⟹ `V2mPlusRationalFactGe2`
  (the only open piece of the `V_{2m}⁺` converse; `C₂` is `V2mPlus_c2Cofinite`);
* `gannonRayhaunConverse_of_orbifoldRational` — the universe-zero converse from ONE general
  orbifold theorem plus the three exceptional `C₂`/positivity inputs.

⚠ Why no proof of `OrbifoldRationalOfC2` is attempted on top of the library's Huang/HKL machinery:
every known proof (McRae Cor 4.23; Carnahan–Miyamoto §§3–5) works in the category of
grading-restricted *generalized* (logarithmic) `W^G`-modules, which is a braided tensor category by
Huang–Lepowsky–Zhang / Huang (arXiv:0712.4109) precisely because `W^G` is `C₂`-cofinite — *before*
rationality is known.  The library's tensor category (`monoidalCategoryOfStronglyRational_pbw`)
and its HKL extension theory (`hklRationalInput_holds`) take `StronglyRational` of the BASE algebra
as a hypothesis; for the orbifold the base is `W^G`, so using them would assume the conclusion.
HKL runs in the extension direction (`U` nice ⟹ extension rational); orbifold rationality is the
descent direction.
-/

namespace VOA.Classification.COne.OrbRat

open VOA VertexOperatorAlgebra

universe u

/-- **McRae, Corollary 4.23** (arXiv:1910.13226v2): a `C₂`-cofinite finite orbifold of a strongly
rational VOA is rational.  OPEN here (stated, not proved). -/
def OrbifoldRationalOfC2 : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
    (G : Subgroup (Aut W)), Finite G → StronglyRational W →
      C2Cofinite (orbifoldVOA G) → AdmissiblyRational (orbifoldVOA G)

/-- The cyclic case (Carnahan–Miyamoto, arXiv:1603.05645v4, §5).  OPEN here. -/
def CyclicOrbifoldRationalOfC2 : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
    (g : Aut W), IsOfFinOrder g → StronglyRational W →
      C2Cofinite (orbifoldVOA (Subgroup.zpowers g)) →
        AdmissiblyRational (orbifoldVOA (Subgroup.zpowers g))

/-- The involution case `g² = 1`; this is all `V_{2m}⁺` needs.  OPEN here. -/
def InvolutionOrbifoldRationalOfC2 : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
    (g : Aut W), g * g = 1 → StronglyRational W →
      C2Cofinite (orbifoldVOA (Subgroup.zpowers g)) →
        AdmissiblyRational (orbifoldVOA (Subgroup.zpowers g))

/-- An element of finite order generates a finite subgroup. -/
theorem finite_zpowers_of_isOfFinOrder {G : Type*} [Group G] {g : G} (hg : IsOfFinOrder g) :
    Finite (Subgroup.zpowers g) :=
  hg.finite_zpowers.to_subtype

/-- An involution has finite order. -/
theorem isOfFinOrder_of_mul_self {G : Type*} [Group G] {g : G} (hg : g * g = 1) :
    IsOfFinOrder g :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by rw [pow_two]; exact hg⟩

theorem orbifoldRational_cyclic (h : OrbifoldRationalOfC2.{u}) : CyclicOrbifoldRationalOfC2.{u} :=
  fun 𝒱 _ _ W _ hg hW hC2 => h 𝒱 W _ (finite_zpowers_of_isOfFinOrder hg) hW hC2

theorem cyclic_involution (h : CyclicOrbifoldRationalOfC2.{u}) :
    InvolutionOrbifoldRationalOfC2.{u} :=
  fun 𝒱 _ _ W g hg hW hC2 => h 𝒱 W g (isOfFinOrder_of_mul_self hg) hW hC2

/-- **Strong rationality of a `C₂`-cofinite finite orbifold**, from the general rationality
statement; simplicity and self-duality are proved (`OrbRatStructure`). -/
theorem orbifold_stronglyRational_of_c2 (h : OrbifoldRationalOfC2.{u})
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (hW : StronglyRational W) (G : Subgroup (Aut W)) [hG : Finite G]
    (hC2 : C2Cofinite (orbifoldVOA G)) : StronglyRational (orbifoldVOA G) :=
  (orbifold_stronglyRational_iff hW.toStronglyFinite G).mpr ⟨hC2, h 𝒱 W G hG hW hC2⟩

/-- McRae's general theorem gives the exceptional rationality input. -/
theorem finiteV2OrbifoldRationalOfC2Fact_of_orbifoldRational (h : OrbifoldRationalOfC2.{0}) :
    FiniteV2OrbifoldRationalOfC2Fact :=
  fun G hG hC2 => h _ (V2m 1 le_rfl) G hG (V2m_stronglyRational 1 le_rfl) hC2

/-- `θ` is an involution of `V_{2m}`. -/
theorem thetaV2m_mul_self (m : ℕ) (hm : 1 ≤ m) : thetaV2m m hm * thetaV2m m hm = 1 :=
  VOA.LatGen.thetaAut_sq _ _ _

/-- The involution case of orbifold rationality gives the `V_{2m}⁺` rationality input
(`C₂`-cofiniteness of `V_{2m}⁺` is the proved `V2mPlus_c2Cofinite`). -/
theorem v2mPlusRationalFactGe2_of_involution (h : InvolutionOrbifoldRationalOfC2.{0}) :
    V2mPlusRationalFactGe2 :=
  fun m hm _ => h _ (V2m m hm) (thetaV2m m hm) (thetaV2m_mul_self m hm)
    (V2m_stronglyRational m hm) (V2mPlus_c2Cofinite m hm)

/-- `V_{2m}⁺` is strongly rational for every `m ≥ 1`, given the involution case. -/
theorem V2mPlus_stronglyRational_of_involution (h : InvolutionOrbifoldRationalOfC2.{0})
    (m : ℕ) (hm : 1 ≤ m) : StronglyRational (V2mPlus m hm) := by
  haveI : Finite (Subgroup.zpowers (thetaV2m m hm)) :=
    finite_zpowers_of_isOfFinOrder (isOfFinOrder_of_mul_self (thetaV2m_mul_self m hm))
  exact (orbifold_stronglyRational_iff (V2m_stronglyRational m hm).toStronglyFinite _).mpr
    ⟨V2mPlus_c2Cofinite m hm, h _ (V2m m hm) (thetaV2m m hm) (thetaV2m_mul_self m hm)
      (V2m_stronglyRational m hm) (V2mPlus_c2Cofinite m hm)⟩

/-- **The Gannon–Rayhaun converse (carrier universe zero) from the general orbifold
rationality theorem**, the Miyamoto `C₂` input for `A₄, S₄`, Xu's icosahedral relations, and the
exceptional positivity input.  Two of the five previous inputs (`V2mPlusRationalFactGe2`,
`FiniteV2OrbifoldRationalOfC2Fact`) are replaced by the single literature theorem
`OrbifoldRationalOfC2` (McRae Cor. 4.23).  NOT unconditional. -/
theorem gannonRayhaunConverse_of_orbifoldRational (hOrb : OrbifoldRationalOfC2.{0})
    (hSolv : SolvableExceptionalOrbifoldC2Fact) (hXu : XuIcosahedralPoissonRelations)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact) : GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_exceptional_inputs
    (v2mPlusRationalFactGe2_of_involution (cyclic_involution (orbifoldRational_cyclic hOrb)))
    hSolv hXu (finiteV2OrbifoldRationalOfC2Fact_of_orbifoldRational hOrb) hPU

end VOA.Classification.COne.OrbRat
