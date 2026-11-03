import VOA.Classification.COne.McRaeM1Universal
import VOA.Modules.ProjCoverFreeParabolic

/-!
# McRae M1 closed: Huang's projective covers for every `C₂`-cofinite VOA

* `OmegaN_le_omegaN` — the module-level `Ω_N(A)` (`McRaeM1.OmegaN`) lies in DLM's `Ω_N` of the
  `V̂`-representation `weakRep A` (in fact they are equal; only `≤` is needed).
* `universalOmegaVector` — `UniversalOmegaVector W N` holds for EVERY vertex operator algebra and
  every `N`, from DLM's induced module of the free parabolic module
  (`VHat.DLM3.exists_universal_omegaN_vector`).
* `huangCoverFact_of_c2 (hC2 : C2Cofinite W) : HuangCoverFact W` — Huang's projective covers
  (arXiv:0712.4109, Thm 3.23), for every simple weak module of a `C₂`-cofinite VOA.

Consumers: the McRae route rests on the single categorical input `UnimodularSocleFact`:
* `mcRaeCoverFact_of_unimodularSocle (hC2) (hU)`;
* `admissiblyRational_of_unimodularSocle (hC2) (hss) (hU)`;
* `cubicModel_admissiblyRational_of_unimodularSocle (hU)` — B3 for `A₄` from the unimodular socle.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.McRaeM1

open VOA VertexOperatorAlgebra VOA.VHat VOA.VHat.DLM3 OrbMcRae

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The module-level `Ω_N` sits in DLM's `Ω_N` of the associated `V̂`-representation. -/
theorem OmegaN_le_omegaN {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (N : ℕ) : OmegaN A N ≤ omegaN W N (weakRep A) := by
  intro w hw g hg
  refine Submodule.span_induction (p := fun g _ => weakRep A g w = 0) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨β, m, a, ha, hd, rfl⟩
    rw [weakRep_gen]
    simp only [deepSet, Set.mem_setOf_eq] at hd
    exact hw β a ha m (by omega)
  · simp only [map_zero, LinearMap.zero_apply]
  · intro x y _ _ hx hy
    simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  · intro c x _ hx
    simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]

/-- **Universal `Ω_N`-vectors exist** for every VOA and every `N` (DLM3 induced module of the
free parabolic module). -/
theorem universalOmegaVector (W : VertexOperatorAlgebra 𝒱) (N : ℕ) : UniversalOmegaVector W N := by
  obtain ⟨G, _, _, BG, v, hv⟩ := exists_universal_omegaN_vector W N
  exact ⟨G, _, _, BG, v, fun A w hw => hv A w (OmegaN_le_omegaN A N hw)⟩

/-- **Huang's projective covers** (arXiv:0712.4109, Thm 3.23): every simple weak module of a
`C₂`-cofinite VOA has a projective cover relative to finite-length weak modules. -/
theorem huangCoverFact_of_c2 (hC2 : C2Cofinite W) : HuangCoverFact W :=
  huangCoverFact_of_universalOmegaVector hC2 (universalOmegaVector W)

theorem huangCoverFact_of_stronglyFinite (hW : StronglyFinite W) : HuangCoverFact W :=
  huangCoverFact_of_c2 hW.c2Cofinite

/-- McRae covers from the unimodular socle alone (`C₂`). -/
theorem mcRaeCoverFact_of_unimodularSocle (hC2 : C2Cofinite W) (hU : UnimodularSocleFact W) :
    McRaeCoverFact W :=
  mcRaeCoverFact_of_huang_unimodular (huangCoverFact_of_c2 hC2) hU

/-- Rationality from `C₂`, semisimple Zhu algebra and the unimodular socle. -/
theorem admissiblyRational_of_unimodularSocle (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W)) (hU : UnimodularSocleFact W) :
    AdmissiblyRational W :=
  admissiblyRational_of_huang_unimodular hC2 hss (huangCoverFact_of_c2 hC2) hU

/-- **B3 for `A₄` from the unimodular socle alone.** -/
theorem cubicModel_admissiblyRational_of_unimodularSocle
    (hU : UnimodularSocleFact OrbRat2.cubicModel) : AdmissiblyRational OrbRat2.cubicModel :=
  cubicModel_admissiblyRational_of_huang_unimodular
    (huangCoverFact_of_c2 OrbTop.cubicModel_stronglyFinite.c2Cofinite) hU

end VOA.Classification.COne.McRaeM1
