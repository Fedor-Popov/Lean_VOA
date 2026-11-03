import VOA.Classification.COne.PlusSplitZhuBottom

/-!
# The precise generator-stability remainder in resonant splitting

Abe, https://arxiv.org/html/math/0311210, Propositions 7.3--7.4 and
Lemma 7.5, supply the hard existence statement: choose a linear complement
and prove it is preserved by the Heisenberg fixed-point action and the charged
field. Here the promotion from the three generating fields to every field is
proved, and the resulting residual is proved equivalent to the original one.
No fusion rule or existence of a complement is claimed here.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusSplitting
open PlusRational PlusUnitary VOA.Huang.BottomRecovery
universe u v
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- All modes of one state preserve a given linear subspace. -/
def ModesPreserve (A : WeakModule W M) (S : Submodule ℂ M) (a : 𝒱) : Prop :=
  ∀ (n : ℤ) (x : M), x ∈ S → A.act a n x ∈ S

/-- Mode stability propagates through the VOA product by the module iterate
identity; only the linear subspace axioms are needed. -/
theorem modesPreserve_smul (A : WeakModule W M) (S : Submodule ℂ M)
    {a b : 𝒱} (ha : ModesPreserve A S a) (hb : ModesPreserve A S b) (p : ℤ) :
    ModesPreserve A S (W.smul a p b) := by
  intro n x hx
  rw [WeakModule.act_def, module_iterate0]
  apply VOA.Huang.BottomRecovery.finsum_mem_submodule
  intro i
  exact S.smul_mem _ (S.sub_mem (ha _ _ (hb _ _ hx)) (S.smul_mem _ (hb _ _ (ha _ _ hx))))

theorem modesPreserve_of_isIterProd (A : WeakModule W M) (S : Submodule ℂ M)
    {G : Set 𝒱} (hG : ∀ a ∈ G, ModesPreserve A S a) {a : 𝒱}
    (ha : IsIterProd W G a) : ModesPreserve A S a := by
  induction ha with
  | vacuum =>
    intro n x hx
    rw [WeakModule.act_def, A.vacuum_YM, mode_one]
    split_ifs <;> simp_all
  | step a ha p _ b _ ih => exact modesPreserve_smul A S (hG a ha) ih (-p)

theorem modesPreserve_of_mem_iterProdSpan (A : WeakModule W M) (S : Submodule ℂ M)
    {G : Set 𝒱} (hG : ∀ a ∈ G, ModesPreserve A S a) {a : 𝒱}
    (ha : a ∈ iterProdSpan W G) : ModesPreserve A S a := by
  induction ha using Submodule.span_induction with
  | mem a ha => exact modesPreserve_of_isIterProd A S hG ha
  | zero => intro n x _; simp [WeakModule.act_def]
  | add a b _ _ ha hb =>
    intro n x hx
    simpa [WeakModule.act_def] using S.add_mem (ha n x hx) (hb n x hx)
  | smul c a _ ha =>
    intro n x hx
    simpa [WeakModule.act_def] using S.smul_mem c (ha n x hx)

/-- For the plus family, stability under all modes of the three certified
generators is equivalent to full weak-module stability. -/
theorem plus_modesPreserve_of_generators (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (A : WeakModule (V2mPlus m hm) M) (S : Submodule ℂ M)
    (hgen : ∀ i : Fin 3, ModesPreserve A S (gP m hm i)) :
    ∀ a, ModesPreserve A S a := by
  let G := Set.range (gP m hm)
  let T := {a | IsIterProd (V2mPlus m hm) G a}
  have hG : ∀ a ∈ G, ModesPreserve A S a := by
    rintro a ⟨i, rfl⟩; exact hgen i
  have hhom : ∀ a ∈ T, IsHomog (V2mPlus m hm) a := by
    intro a ha
    exact isIterProd_homog (by rintro a ⟨i, rfl⟩; exact ⟨_, gP_mem_grading m hm i⟩) ha
  have htop : iterProdSpan (V2mPlus m hm) T = ⊤ :=
    iterProdSpan_eq_top _ T hhom (top_eq_span_iterProd m hm hm2)
  intro a
  exact modesPreserve_of_mem_iterProdSpan A S
    (fun b hb => modesPreserve_of_isIterProd A S hG hb)
    (by change a ∈ iterProdSpan (V2mPlus m hm) T; rw [htop]; trivial)

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusSplitting PlusUnitary

/-- OPEN Abe Section 7 input, expressed entirely as relative linear
complements and stability under the three known generating fields. Stability
means every mode, not just the zero modes. Both resonance orientations and
all strict two-step intervals are retained. -/
def V2mPlusResonantGeneratorComplements : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (N : AdmissibleModule (V2mPlus m hm) M)
      (a b c : Submodule (modeAlg N.toWeakModule) M) (h k : ℂ),
      a ⋖ b → b ⋖ c → FactorBottom N.toWeakModule a b h →
      FactorBottom N.toWeakModule b c k →
      (∃ z : ℤ, z ≠ 0 ∧ k = h + (z : ℂ)) →
      ∃ S : Submodule ℂ M,
        a.restrictScalars ℂ ≤ S ∧ S ≤ c.restrictScalars ℂ ∧
        b.restrictScalars ℂ ⊓ S = a.restrictScalars ℂ ∧
        b.restrictScalars ℂ ⊔ S = c.restrictScalars ℂ ∧
        ∀ i : Fin 3, ModesPreserve N.toWeakModule S (gP m hm i)

/-- No weakening: the three-generator complement condition is exactly the
resonant residual `V2mPlusResonantBottomSplitting`. -/
theorem resonantBottomSplitting_iff_generatorComplements :
    V2mPlusResonantBottomSplitting ↔ V2mPlusResonantGeneratorComplements := by
  constructor
  · intro hs m hm hm2 M _ _ N a b c h k hab hbc hh hk hz
    obtain ⟨d, had, hdc, hi, hu⟩ := hs m hm hm2 N a b c h k hab hbc hh hk hz
    refine ⟨d.restrictScalars ℂ, had, hdc, ?_, ?_, ?_⟩
    · simpa using congrArg (Submodule.restrictScalars ℂ) hi
    · simpa using congrArg (Submodule.restrictScalars ℂ) hu
    · intro i n x hx
      exact (ofR N.toWeakModule d).act_mem _ _ hx
  · intro hs m hm hm2 M _ _ N a b c h k hab hbc hh hk hz
    obtain ⟨S, haS, hSc, hi, hu, hgen⟩ := hs m hm hm2 N a b c h k hab hbc hh hk hz
    let d := toR N.toWeakModule {
      carrier := S
      act_mem := fun a n x hx => plus_modesPreserve_of_generators m hm hm2
        N.toWeakModule S hgen a n x hx }
    refine ⟨d, haS, hSc, ?_, ?_⟩
    · ext x
      exact Iff.of_eq (congrArg (fun T : Submodule ℂ M => x ∈ T) hi)
    · apply (Submodule.restrictScalars_injective ℂ)
      simpa only [Submodule.restrictScalars_sup] using hu

/-- Assembly with explicit Zhu dimension/character inputs and the exact
three-generator resonant input. The equal-bottom bridge remains explicit. -/
theorem generalizedGeneratorSplitting_of_character_bottom_generator_inputs
    (hdim : V2mPlusZhuDimensionBound) (hchar : V2mPlusZhuDistinctCharacters)
    (hlift : V2mPlusEqualBottomZhuLifting) (hgen : V2mPlusResonantGeneratorComplements) :
    V2mPlusGeneralizedGeneratorSplittingFactGe2 :=
  generalizedGeneratorSplitting_of_dimension_characters_lifting_resonant hdim hchar hlift
    (resonantBottomSplitting_iff_generatorComplements.mpr hgen)

/-- Conditional rationality with every remaining classical input visible. -/
theorem rationality_of_character_bottom_generator_inputs
    (hdim : V2mPlusZhuDimensionBound) (hchar : V2mPlusZhuDistinctCharacters)
    (hlift : V2mPlusEqualBottomZhuLifting) (hgen : V2mPlusResonantGeneratorComplements) :
    V2mPlusRationalFactGe2 :=
  v2mPlusRationalFactGe2_iff_generalizedGeneratorSplitting.mpr
    (generalizedGeneratorSplitting_of_character_bottom_generator_inputs hdim hchar hlift hgen)

end VOA.Classification.COne
