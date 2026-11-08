/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroSurjective
import VOA.Moonshine.MoonshineCNGenusZeroLevel

/-!
# Genus zero on the abstract interface: the main genus-zero theorem

The Hauptmodul fields assembled, and the final assembly (blueprint
`Notes/moonshine/MOON_M8_LEAN.md`).

* `isNormalizedHauptmodul_symmetryGroup`: if `f = qSeriesFun c` is `J`-dominated, has property P
  and its symmetry group contains some `Γ₁(M)`, then `f` is a normalised Hauptmodul of its
  symmetry group: all eight fields of the fixed statement's `IsNormalizedHauptmodul`, as stated
  there (holomorphic, invariant, normalised: the `q`-series estimates and the definition; cusp
  values exist (`cuspData_of_other`), are not attained (`qSeriesFun_ne_of_tendsto_comp_smul`),
  separate inequivalent cusps (`exists_mem_lowerLeft_eq_zero_of_tendsto_eq`); injective:
  property P; surjective (`surjective_of_gamma1GL_le`)).
* `ReplicableFamily.exists_hauptmodul_gammaOne` (**the genus-zero theorem for replicable
  families**): conditional on the prime Hecke identity (`PrimeHeckeIdentity`) and
  non-injectivity modulo translations (`NotInjectiveModTranslations`), both proved on the LR
  side, as explicit hypotheses.
* `conwayNortonGammaOne_of_completelyReplicable` and, with the committed bridge
  `conwayNorton_of_gammaOne`, `conwayNorton_of_completelyReplicable`: the Conway–Norton
  conjecture from complete replicability, finite order of all automorphisms, the prime Hecke
  identity and non-injectivity modulo translations for the McKay–Thompson families. The variant
  `conwayNorton_of_completelyReplicable_of_families` takes these two inputs in the form of general
  theorems about all replicable families.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open AutMonster
open scoped MatrixGroups Manifold

/-- **A `J`-dominated `q`-series with property P whose symmetry group contains `Γ₁(M)` is the
normalised Hauptmodul of its symmetry group.** -/
theorem isNormalizedHauptmodul_symmetryGroup {c : ℕ → ℂ} (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {M : ℕ} (hM : 0 < M) (hΓ1 : gamma1GL M ≤ symmetryGroup (qSeriesFun c)) :
    IsNormalizedHauptmodul (symmetryGroup (qSeriesFun c)) (qSeriesFun c) := by
  have hcomm := commensurable_symmetryGroup_of_gamma1GL_le hc hP hM hΓ1
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hsend : ∀ ρ : SL(2, ℤ), SendsInftyTo (mapGL ℝ ρ) (mapGL ℝ ρ • cuspInfty) :=
    fun ρ => ⟨by rw [det_val_mapGL]; exact one_pos, rfl⟩
  refine ⟨mdifferentiable_qSeriesFun hc, fun γ hγ τ => hγ.2 τ,
    tendsto_qSeriesFun_sub_inv_qPar hc, ?_, hP, ?_, ?_,
    surjective_of_gamma1GL_le hc hP hM hΓ1 hcomm⟩
  · -- `cuspFinite`: the cusp value exists
    intro cc hcc
    obtain ⟨ρ, hρ, hother⟩ := exists_SL2Z_of_isOtherCusp hcomm hcc
    obtain ⟨-, hlim, -⟩ := cuspData_of_other hc hP (det_val_mapGL ρ) hMR
      (conj_glUpperUnipotent_mem_of_gamma1GL_le hΓ1 ρ) hother
    rw [hρ]
    exact ⟨_, hasCuspValue_of_tendsto_comp_smul hlim⟩
  · -- `cuspValue_not_attained`: the cusp value is not attained in `ℍ`
    intro cc w hcc hw τ
    obtain ⟨ρ, hρ, hother⟩ := exists_SL2Z_of_isOtherCusp hcomm hcc
    rw [hρ] at hw
    exact qSeriesFun_ne_of_tendsto_comp_smul hc hP (det_val_mapGL ρ) hMR
      (conj_glUpperUnipotent_mem_of_gamma1GL_le hΓ1 ρ) hother (hw _ (hsend ρ)) τ
  · -- `cuspValue_injective`: equal cusp values force equivalent cusps
    intro c₁ c₂ w h₁ h₂ hw₁ hw₂
    obtain ⟨ρ₁, hρ₁, hother₁⟩ := exists_SL2Z_of_isOtherCusp hcomm h₁
    obtain ⟨ρ₂, hρ₂, hother₂⟩ := exists_SL2Z_of_isOtherCusp hcomm h₂
    rw [hρ₁] at hw₁ ⊢
    rw [hρ₂] at hw₂ ⊢
    obtain ⟨γ, hγ, h0⟩ := exists_mem_lowerLeft_eq_zero_of_tendsto_eq hc hP (det_val_mapGL ρ₁)
      (det_val_mapGL ρ₂) hMR hMR (conj_glUpperUnipotent_mem_of_gamma1GL_le hΓ1 ρ₁)
      (conj_glUpperUnipotent_mem_of_gamma1GL_le hΓ1 ρ₂) hother₁ hother₂
      (hw₁ _ (hsend ρ₁)) (hw₂ _ (hsend ρ₂))
    refine ⟨γ, hγ, ?_⟩
    have h1 : ((mapGL ℝ ρ₂)⁻¹ * γ * mapGL ℝ ρ₁) • cuspInfty = cuspInfty :=
      OnePoint.smul_infty_eq_self_iff.mpr h0
    calc γ • mapGL ℝ ρ₁ • cuspInfty
        = mapGL ℝ ρ₂ • ((mapGL ℝ ρ₂)⁻¹ * γ * mapGL ℝ ρ₁) • cuspInfty := by
          simp only [← mul_smul]; congr 1; group
      _ = mapGL ℝ ρ₂ • cuspInfty := by rw [h1]

/-- **The genus-zero theorem for replicable families** (`Γ₁` form). Let `F` be a
replicable family of period `N > 0` satisfying the prime Hecke identity at every admissible prime
for every member and with no member injective modulo translations (both inputs proved on the LR
side). Then every member `qSeriesFun (F.c k)` is the normalised Hauptmodul of a group `Γ` of
determinant one, containing some `Γ₁(N′)` and commensurable with `SL(2, ℤ)`; namely
`Γ = symmetryGroup (qSeriesFun (F.c k))`. -/
theorem ReplicableFamily.exists_hauptmodul_gammaOne {N : ℕ} (hN : 0 < N)
    (F : ReplicableFamily N) (hB1 : ∀ k, PrimeHeckeIdentity F k)
    (hD7 : F.NotInjectiveModTranslations) (k : ℕ) :
    ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N' : ℕ), 0 < N' ∧ Γ.HasDetOne ∧ gamma1GL N' ≤ Γ ∧
      Subgroup.Commensurable Γ 𝒮ℒ ∧ IsNormalizedHauptmodul Γ (qSeriesFun (F.c k)) := by
  have hc := F.isJDominated k
  have hP : ∀ z w : ℍ, qSeriesFun (F.c k) z = qSeriesFun (F.c k) w →
      ∃ γ ∈ symmetryGroup (qSeriesFun (F.c k)), γ • z = w :=
    fun _ _ h => exists_mem_symmetryGroup_smul_eq hN F k (hB1 k) h
  obtain ⟨N', hN', -, hΓ1⟩ :=
    ReplicableFamily.exists_gamma1GL_le_symmetryGroup hN F k (hB1 k) (hD7 k)
  exact ⟨symmetryGroup _, N', hN', hasDetOne_symmetryGroup _, hΓ1,
    commensurable_symmetryGroup_of_gamma1GL_le hc hP hN' hΓ1,
    isNormalizedHauptmodul_symmetryGroup hc hP hN' hΓ1⟩

/-- The McKay–Thompson series of `g` is member `1` of its replicable family. -/
lemma mckayThompsonFun_eq_qSeriesFun_family (hrep : CompletelyReplicable) (g : AutVnat)
    (hg : IsOfFinOrder g) :
    mckayThompsonFun g = qSeriesFun ((mckayThompsonReplicableFamily hrep g hg).c 1) := by
  rw [mckayThompsonFun_eq_qSeriesFun]
  congr 1

/-- **The `Γ₁` form of Conway–Norton from complete replicability**, conditional on two inputs
proved on the LR side: `hB1`, the prime Hecke identity for every member of every McKay–Thompson
family, and `hD7`, no member of a McKay–Thompson family is injective modulo translations. -/
theorem conwayNortonGammaOne_of_completelyReplicable (hrep : CompletelyReplicable)
    (hB1 : ∀ (g : AutVnat) (hg : IsOfFinOrder g) (k : ℕ),
      PrimeHeckeIdentity (mckayThompsonReplicableFamily hrep g hg) k)
    (hD7 : ∀ (g : AutVnat) (hg : IsOfFinOrder g),
      (mckayThompsonReplicableFamily hrep g hg).NotInjectiveModTranslations) :
    ConwayNortonGammaOne := by
  intro g hg
  obtain ⟨hpos, -⟩ := mckayThompson_replicableFamily_exists hrep g hg
  obtain ⟨Γ, N', hN', hdet, hΓ1, hcomm, hH⟩ := ReplicableFamily.exists_hauptmodul_gammaOne hpos
    (mckayThompsonReplicableFamily hrep g hg) (hB1 g hg) (hD7 g hg) 1
  refine ⟨Γ, N', hN', hdet, hΓ1, hcomm, ?_⟩
  rw [mckayThompsonFun_eq_qSeriesFun_family hrep g hg]
  exact hH

/-- **The Conway–Norton conjecture** from complete replicability (`hrep`), finite order of every
automorphism of `V♮` (`hfin`), the prime Hecke identity (`hB1`) and non-injectivity modulo
translations (`hD7`) for the McKay–Thompson families; via the committed `Γ₁ ⇒ Γ₀` bridge
`conwayNorton_of_gammaOne`. -/
theorem conwayNorton_of_completelyReplicable (hfin : ∀ g : AutVnat, IsOfFinOrder g)
    (hrep : CompletelyReplicable)
    (hB1 : ∀ (g : AutVnat) (hg : IsOfFinOrder g) (k : ℕ),
      PrimeHeckeIdentity (mckayThompsonReplicableFamily hrep g hg) k)
    (hD7 : ∀ (g : AutVnat) (hg : IsOfFinOrder g),
      (mckayThompsonReplicableFamily hrep g hg).NotInjectiveModTranslations) :
    ConwayNortonConjecture :=
  conwayNorton_of_gammaOne hfin (conwayNortonGammaOne_of_completelyReplicable hrep hB1 hD7) hrep

/-- **The Conway–Norton conjecture**, with the prime Hecke identity and non-injectivity modulo
translations in the form of general theorems about all replicable families: `hB1` the prime
Hecke identity for every member of every replicable family, `hD7` nontriviality for every
replicable family of positive period satisfying the prime Hecke identity. -/
theorem conwayNorton_of_completelyReplicable_of_families (hfin : ∀ g : AutVnat, IsOfFinOrder g)
    (hrep : CompletelyReplicable)
    (hB1 : ∀ (N : ℕ) (F : ReplicableFamily N) (k : ℕ), PrimeHeckeIdentity F k)
    (hD7 : ∀ (N : ℕ), 0 < N → ∀ F : ReplicableFamily N, (∀ k, PrimeHeckeIdentity F k) →
      F.NotInjectiveModTranslations) :
    ConwayNortonConjecture :=
  conwayNorton_of_completelyReplicable hfin hrep (fun _ _ k => hB1 _ _ k)
    fun g hg => hD7 _ (mckayThompson_replicableFamily_exists hrep g hg).1 _ fun k => hB1 _ _ k

end VOA.Moonshine.ConwayNorton
