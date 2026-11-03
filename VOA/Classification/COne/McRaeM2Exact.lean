import VOA.Classification.COne.McRaeM1Main

/-!
# McRae's route: `UnimodularSocleFact` is exactly rationality (under `C₂` + semisimple `A(W)`)

`OrbMcRae.UnimodularSocleFact W` (every Huang cover `P_S ↠ S` of a simple weak module has an
essential simple socle `S ↪ P_S`) is the single open input of the McRae route to B3
(`McRaeM1.admissiblyRational_of_unimodularSocle`).  This file proves the converse:

* `unimodularSocleFact_of_admissiblyRational (hC2) (hss) (hR)`: if `W` is rational, every Huang
  cover is an isomorphism, so its socle is the whole (simple) cover.
* `unimodularSocleFact_iff_admissiblyRational (hC2) (hss) :
    UnimodularSocleFact W ↔ AdmissiblyRational W`.
* `cubicModel_unimodularSocleFact_iff`: B3 for `A₄` is EXACTLY `UnimodularSocleFact cubicModel`.

Consequence: for the exceptional
orbifolds (`C₂`, semisimple Zhu algebra), there is no route to `UnimodularSocleFact` that is
"cheaper than rationality".  Any proof of it is a proof of rationality, so it must use `C₂`
globally (finiteness of the category), not only self-duality and finite length.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.McRaeM2

open VOA VertexOperatorAlgebra PlusRational PlusSplitting ABDWeakAdmissible OrbMcRae McRaeM1
open VOA.Huang.LogRemovalAdmissible VOA.Huang.BottomRecovery

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Basic

variable {X Y : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

theorem modeMap_bot {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B) :
    modeMap π ⊥ = ⊥ := by
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := (mem_modeMap π ⊥ y).mp hy
  rw [(Submodule.mem_bot _).mp hx, map_zero]
  exact Submodule.zero_mem _

/-- A surjective weak-module map whose kernel is complemented and superfluous is injective. -/
theorem injective_of_superfluous_compl {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B)
    (hsup : ∀ N : Submodule (modeAlg A) X, modeMap π N = ⊤ → N = ⊤)
    (hsurj : Function.Surjective π.toLinearMap)
    {Q : Submodule (modeAlg A) X} (hQ : IsCompl (modeComap π ⊥) Q) :
    Function.Injective π.toLinearMap := by
  have hQtop : modeMap π Q = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ modeComap π ⊥ ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    refine (mem_modeMap π Q _).mpr ⟨q, hq, ?_⟩
    have ha0 : π.toLinearMap a = 0 := ha
    rw [map_add, ha0, zero_add]
  have hQ' : Q = ⊤ := hsup Q hQtop
  have hker : modeComap π ⊥ = ⊥ := by
    have := hQ.inf_eq_bot
    rwa [hQ', inf_top_eq] at this
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hx' : x ∈ modeComap π ⊥ := hx
  rw [hker] at hx'
  exact (Submodule.mem_bot ℂ).mpr ((Submodule.mem_bot _).mp hx')

end Basic

/-- In a rational `C₂`-cofinite VOA with semisimple Zhu algebra, every weak module is semisimple
over its mode algebra. -/
theorem isSemisimple_of_admissiblyRational (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (hR : AdmissiblyRational W)
    {Y : Type u} [AddCommGroup Y] [Module ℂ Y] (BY : WeakModule W Y) :
    IsSemisimpleModule (modeAlg BY) Y := by
  have hres : OrbRat.ResonantWholeSplitting W := by
    intro Y _ _ BY Pa h k a b c d e
    exact OrbRat.resonantWholeSplitting_of_admissiblyRational hC2 hR BY Pa h k a b c d e
  exact semisimple_of_generalized_cyclic_splitting hC2 BY (fun _ x _ =>
    twoStepSplitting_submodule
      (OrbRat.twoStepSplitting_of_resonantWholeSplitting hC2 hss hres BY) (cyclic BY x))

/-- **Rational ⟹ unimodular socle**: every Huang cover of a simple module of a rational
`C₂`-cofinite VOA with semisimple Zhu algebra is an isomorphism, so it has essential simple
socle. -/
theorem unimodularSocleFact_of_admissiblyRational (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) (hR : AdmissiblyRational W) :
    UnimodularSocleFact W := by
  intro X _ _ B hsimple C
  haveI := isSemisimple_of_admissiblyRational hC2 hss hR C.BP
  obtain ⟨Q, hQ⟩ := exists_isCompl (modeComap C.p ⊥)
  have hinj := injective_of_superfluous_compl C.p C.superfluous C.surj hQ
  have hbij : Function.Bijective C.p.toLinearMap := ⟨hinj, C.surj⟩
  refine ⟨homInv C.p hbij, ?_, ?_⟩
  · intro y₁ y₂ h
    have h1 := congrArg C.p.toLinearMap h
    have e1 : ∀ y, C.p.toLinearMap ((homInv C.p hbij).toLinearMap y) = y :=
      fun y => (LinearEquiv.ofBijective C.p.toLinearMap hbij).apply_symm_apply y
    rwa [e1, e1] at h1
  · intro N hN
    have hNtop : N = ⊤ := by
      apply C.superfluous
      rcases hsimple.eq_bot_or_eq_top (modeMap C.p N) with h | h
      · exfalso
        apply hN
        apply modeMap_injective C.p hinj
        rw [h, modeMap_bot]
      · exact h
    rw [hNtop]
    exact le_top

/-- **The open input is exactly rationality.** For a `C₂`-cofinite VOA with semisimple Zhu
algebra, the unimodular-socle property of Huang covers is equivalent to (admissible) rationality. -/
theorem unimodularSocleFact_iff_admissiblyRational (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) :
    UnimodularSocleFact W ↔ AdmissiblyRational W :=
  ⟨admissiblyRational_of_unimodularSocle hC2 hss,
    unimodularSocleFact_of_admissiblyRational hC2 hss⟩

/-- **B3 for `A₄`, exactly**: the tetrahedral model is rational iff its Huang covers have
essential simple socle. -/
theorem cubicModel_unimodularSocleFact_iff :
    UnimodularSocleFact OrbRat2.cubicModel ↔ AdmissiblyRational OrbRat2.cubicModel :=
  unimodularSocleFact_iff_admissiblyRational OrbTop.cubicModel_stronglyFinite.c2Cofinite
    OrbTop.cubicModel_zhuSemisimple

end VOA.Classification.COne.McRaeM2
