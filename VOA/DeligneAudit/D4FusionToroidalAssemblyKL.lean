import VOA.DeligneAudit.D4FusionToroidalAssemblyFinite

/-! The proposition-valued KL input package and its local-Weyl consequence. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The target and symbol map at a fixed multiplicity. -/
def KLTarget (m : ℕ) (hm : 1 ≤ m) (F : Type)
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F] : Prop :=
  ∃ (ρF : ToroidalModule D4sector.f m F) (vF : F)
    (φ : Gr D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ] F)
    (F₀ : Submodule ℂ F),
    φ (grGenerator D4sector.f (ravFam D4sector m 0) m) = vF ∧
    (∀ c i s x, φ ((grToroidal_D4 m hm).op c i s x) =
      ρF.op c i s (φ x)) ∧
    Function.Surjective φ ∧ vF ∈ F₀ ∧
    (∀ c s, F₀ ≤ F₀.comap (ρF.op c 0 s)) ∧
    29 ^ m ≤ Module.finrank ℂ F ∧ Module.finrank ℂ F₀ ≤ 28 ^ m

/-- KL-G inputs, including the still separate graded-rank inequality G2. -/
def KLInputs (m : ℕ) (hm : 1 ≤ m) : Prop :=
  FiniteDimensional ℂ (UModG D4sector.f (ravFam D4sector m 0)) ∧
  FiniteDimensional ℂ (Gr D4sector.f (ravFam D4sector m 0) m) ∧
  Module.finrank ℂ (Gr D4sector.f (ravFam D4sector m 0) m) ≤
    Module.finrank ℂ (UModG D4sector.f (ravFam D4sector m 0)) ∧
  Module.finrank ℂ (UModG D4sector.f (ravFam D4sector m 0)) ≤ 29 ^ m ∧
  ∃ (F : Type) (hA : AddCommGroup F),
    letI : AddCommGroup F := hA
    ∃ (hM : Module ℂ F),
      letI : Module ℂ F := hM
      ∃ (hFD : FiniteDimensional ℂ F),
        letI : FiniteDimensional ℂ F := hFD
        KLTarget m hm F

theorem trunc_rank_of_KLInputs (m : ℕ) (hm : 1 ≤ m)
    (h : KLInputs m hm) :
    FiniteDimensional ℂ
      (FusionToroidal.truncMod D4sector.f (ravFam D4sector m 0) m) ∧
    Module.finrank ℂ
      (FusionToroidal.truncMod D4sector.f (ravFam D4sector m 0) m) ≤ 28 ^ m := by
  rcases h with ⟨hfdU, hfdG, hgr, hU, F, hA, hM, hFD, ht⟩
  letI : FiniteDimensional ℂ (UModG D4sector.f (ravFam D4sector m 0)) := hfdU
  letI : FiniteDimensional ℂ (Gr D4sector.f (ravFam D4sector m 0) m) := hfdG
  letI : AddCommGroup F := hA
  letI : Module ℂ F := hM
  letI : FiniteDimensional ℂ F := hFD
  rcases ht with ⟨ρF, vF, φ, F₀, hgen, heq, hs, hv, hst, hF, hF₀⟩
  exact ⟨inferInstance, assembly_rank hm ρF vF φ hgen heq hs F₀ hv hst
    hgr hU hF hF₀⟩

theorem local_rank_of_KLInputs (m : ℕ) (hm : 1 ≤ m)
    (h : KLInputs m hm) :
    FiniteDimensional ℂ (UModG D4sector.f (lwSpec D4sector m)) ∧
    Module.finrank ℂ (UModG D4sector.f (lwSpec D4sector m)) ≤ 28 ^ m := by
  obtain ⟨hfd, hrank⟩ := trunc_rank_of_KLInputs m hm h
  letI := hfd
  obtain ⟨hlocal, hle⟩ := local_rank_le_trunc m hm
  exact ⟨hlocal, hle.trans hrank⟩

theorem fusionTotalDimG_of_KLInputs
    (h : ∀ m, (hm : 1 ≤ m) → KLInputs m hm) :
    FiniteG.FusionTotalDimG D4sector := by
  apply fusionTotalDimG_of_univTruncatedRank
  intro m hm
  exact local_rank_of_KLInputs m hm (h m hm)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.trunc_rank_of_KLInputs
#print axioms VOA.DeligneAudit.Toroidal.local_rank_of_KLInputs
#print axioms VOA.DeligneAudit.Toroidal.fusionTotalDimG_of_KLInputs
