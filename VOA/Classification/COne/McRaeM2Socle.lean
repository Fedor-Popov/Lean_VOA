import VOA.Classification.COne.McRaeM2Dual

/-!
# McRae's route: McRae's Prop 5.14 argument (`P_S ≅ (P_{S'})'` ⟹ essential socle `S`)

McRae (arXiv:2108.01898v3, Prop 5.14) deduces `S ↪ P_S` from unimodularity in the form
`P_S ≅ (P_{S'})'` (ENO Prop 4.5, EGNO §6.4–6.5): dualize the cover `p : P_{S'} ↠ S'`.  This file
formalizes that dualization step for graded weak modules:

* `transpose_le_of_superfluous` — if `q : G ↠ T` has superfluous kernel and `T` is simple, the
  image of `q' : T' ↪ G'` lies in EVERY nonzero submodule of `G'` (it is the essential simple
  socle);
* `CoverDualFact W` — named `Prop` (NOT proved, NOT an axiom): the cover of each simple `S` is the
  contragredient of a module `G` with a superfluous-kernel surjection onto a simple `T` with
  `T' ≅ S`.  This is the module form of McRae's "`P_S ≅ (P_{S'})'`" (take `G = P_{S'}`, `T = S'`,
  and `S'' ≅ S`);
* `unimodularSocleFact_of_coverDual : CoverDualFact W → UnimodularSocleFact W`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.OrbMcRae VOA.Classification.COne.McRaeM1
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂] {W : VertexOperatorAlgebra V}

section Socle
variable (N₁ : GWModule W M₁) (N₂ : GWModule W M₂)
  (f : N₁.toWeakModule.Hom N₂.toWeakModule)
  (hf : ∀ α : ℂ, ∀ x ∈ N₁.weight α, f.toLinearMap x ∈ N₂.weight α)

/-- The adjunction `⟨f' g, x⟩ = ⟨g, f x⟩` for every (not necessarily homogeneous) `x`. -/
theorem pairing_transposeL_all (x : M₁) (g : RestrictedDual N₂) :
    dualPairing N₁ x (transposeL N₁ N₂ f hf g) = dualPairing N₂ (f.toLinearMap x) g := by
  obtain ⟨s, -, hsum⟩ := exists_sum_cmp N₁ x
  rw [← hsum, pr_sum_left, map_sum, pr_sum_left]
  exact Finset.sum_congr rfl fun α _ => pairing_transposeL N₁ N₂ f hf (cmp_mem N₁ α x) g

/-- In a module with a superfluous-kernel surjection onto a simple module, every proper
submodule lies in the kernel. -/
theorem le_ker_of_superfluous {X Y : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {A : WeakModule W X} {B : WeakModule W Y} (q : A.Hom B)
    (hsup : ∀ L : Submodule (modeAlg A) X, modeMap q L = ⊤ → L = ⊤)
    (hB : IsSimpleModule (modeAlg B) Y) (L : Submodule (modeAlg A) X) (hL : L ≠ ⊤) :
    L ≤ modeComap q ⊥ := by
  rcases hB.eq_bot_or_eq_top (modeMap q L) with h | h
  · exact (modeMap_le_iff q L ⊥).mp (le_of_eq h)
  · exact absurd (hsup L h) hL

/-- **The dual of a superfluous-kernel cover of a simple module is an essential simple
socle**: the image of the transpose lies in every nonzero submodule of the contragredient. -/
theorem transpose_le_of_superfluous (h₁ : IsGenGraded N₁) (h₂ : IsGenGraded N₂)
    (hsup : ∀ L : Submodule (modeAlg N₁.toWeakModule) M₁, modeMap f L = ⊤ → L = ⊤)
    (hS : IsSimpleModule (modeAlg N₂.toWeakModule) M₂)
    (N : Submodule (modeAlg (contra N₁).toWeakModule) (RestrictedDual N₁)) (hN : N ≠ ⊥) :
    modeMap (transpose N₁ N₂ f hf) ⊤ ≤ N := by
  have hO := subsGraded_of_isGenGraded N₁ h₁
  have hD := subsGraded_of_isGenGraded (contra N₁) (isGenGraded_contra N₁ h₁)
  -- `N^⊥` is a proper submodule, hence lies in `ker f`
  have hperp : perpD N₁ hO hD N ≠ ⊤ := by
    intro htop
    apply hN
    have h := perpA_perpD N₁ hO hD N
    rw [htop] at h
    rw [← h]
    refine eq_bot_iff.mpr fun g hg => ?_
    have hz : ∀ x : M₁, dualPairing N₁ x g = 0 := fun x => hg x Submodule.mem_top
    have : g = 0 := restrictedDual_ext_of_pairing N₁ fun α x _ => by
      rw [hz x, LinearMap.map_zero]
    rw [this]; exact Submodule.zero_mem _
  have hle := le_ker_of_superfluous f hsup hS _ hperp
  -- the image of the transpose annihilates `ker f`, hence lies in `N^⊥⊥ = N`
  rintro _ ⟨g, -, rfl⟩
  rw [← perpA_perpD N₁ hO hD N]
  intro x hx
  rw [transpose_apply, pairing_transposeL_all N₁ N₂ f hf x g]
  have hx0 : f.toLinearMap x = 0 := hle hx
  rw [hx0]
  exact pr_zero_left N₂ g

end Socle

/-- **Unimodularity in module form** (McRae Prop 5.14 input; ENO Prop 4.5 + EGNO §6.4–6.5 for a
factorizable category).  Named `Prop`; NOT proved, NOT an axiom.  For every simple `S` with Huang
cover `C`, the cover is (isomorphic to) the contragredient of a generalized-eigenspace-graded
module `G` with a superfluous-kernel surjection onto a simple `T` whose contragredient is `S`.
In McRae's proof: `G = P_{S'}`, `T = S'`, `T' = S'' ≅ S`. -/
def CoverDualFact (W : VertexOperatorAlgebra V) : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X),
    IsSimpleModule (modeAlg B) X → ∀ C : HuangCover B,
      ∃ (Y Z : Type u) (_ : AddCommGroup Y) (_ : Module ℂ Y) (_ : AddCommGroup Z)
        (_ : Module ℂ Z) (G : GWModule W Y) (T : GWModule W Z) (_ : IsGenGraded G)
        (_ : IsGenGraded T) (q : G.toWeakModule.Hom T.toWeakModule)
        (_ : Function.Surjective q.toLinearMap)
        (_ : ∀ L : Submodule (modeAlg G.toWeakModule) Y, modeMap q L = ⊤ → L = ⊤)
        (_ : IsSimpleModule (modeAlg T.toWeakModule) Z)
        (e : (contra G).toWeakModule.Hom C.BP) (_ : Function.Bijective e.toLinearMap)
        (s : B.Hom (contra T).toWeakModule), Function.Bijective s.toLinearMap

/-- **McRae's Prop 5.14 argument**: the module form of unimodularity gives the unimodular
socle. -/
theorem unimodularSocleFact_of_coverDual (h : CoverDualFact W) : UnimodularSocleFact W := by
  intro X _ _ B hB C
  obtain ⟨Y, Z, _, _, _, _, G, T, hG, hT, q, hqs, hsup, hTs, e, he, s, hs⟩ := h B hB C
  have hq := gradedHom_of_isGenGraded G T q hG hT
  let qt := transpose G T q hq
  have hqt : Function.Injective qt.toLinearMap := transpose_injective_of_surjective G T q hq hqs
  refine ⟨homComp e (homComp qt s), ?_, ?_⟩
  · intro a b hab
    exact hs.1 (hqt (he.1 hab))
  · intro N hN
    have hN' : modeComap e N ≠ ⊥ := by
      intro hbot
      apply hN
      refine eq_bot_iff.mpr fun y hy => ?_
      obtain ⟨z, rfl⟩ := he.2 y
      have hz : z ∈ modeComap e N := hy
      rw [hbot] at hz
      rw [(Submodule.mem_bot _).mp hz, map_zero]
      exact Submodule.zero_mem _
    have hle := transpose_le_of_superfluous G T q hq hG hT hsup hTs _ hN'
    rw [modeMap_homComp, modeMap_homComp]
    calc modeMap e (modeMap qt (modeMap s ⊤)) ≤ modeMap e (modeComap e N) :=
          modeMap_mono e (le_trans (modeMap_mono qt le_top) hle)
      _ ≤ N := (modeMap_le_iff e _ N).mpr le_rfl

end VOA.C2Rigid
