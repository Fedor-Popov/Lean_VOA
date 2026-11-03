/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionUnivGSectorRelations
import VOA.DeligneAudit.DeligneFusionSqueezeG

/-!
# The universal characters of a Deligne sector and the squeeze inputs

For sector data `S : DeligneSectorData`:

* `lwSpec S m`: the local Weyl/fusion relations as a `RelSpec`; `localWeylRelG_iff`:
  `LocalWeylRelG S ρ w m ↔ Sat S.f ρ w (lwSpec S m)`.
* `M0G S m := McharG S.f (lwSpec S m)`, the character of the universal `W_loc(mθ)`-type module.
* Named input `FusionTotalBoundG S` (type-generic analogue of the `FusionTotalBound`): every
  module with `LocalWeylRelG S · · m` has finite-dimensional degree pieces and total dimension
  `≤ (dim 𝔤)^m`. It gives `UnivFD` at `a = 0` (`univFD_zero`), the universal bound `huniv_M0G` and
  `total_le_M0G`.
* For **any** relation family `spec : ℕ → ℕ → RelSpec S.n` with `spec 0 m = lwSpec S m` (per type:
  Ravinder's `M_{a,b}`), `MuniG S spec a b := McharG S.f (spec a b)`:
  - `nonneg` is free (`McharG_nonneg`);
  - `huniv` is `huniv_MuniG` (from `FusionTotalBoundG`);
  - `total_le` is `total_le_MuniG` (from `FusionTotalBoundG`);
  - `dem_le` is generic given a realization: `dem_le_of_realizationG` (the
    `DeligneFusionDemazure` pattern, with `DemazureRealizationG`).
  So the squeeze inputs reduce to `rec_le` and the finiteness of the `a ≥ 1` universal pieces
  (`fusionSqueezeInputsG_of_univ`), and U5 follows (`fusionModuleBoundG_of_univ`).
-/

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.A2

noncomputable section

variable (S : DeligneSectorData)

/-- **Named input (type-generic `FusionTotalBound`)**: every module with the local Weyl/fusion
relations for `mθ` has finite-dimensional degree pieces and total dimension `≤ (dim 𝔤)^m`. -/
def FusionTotalBoundG : Prop :=
  ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
    LocalWeylRelG S ρ w m → (∀ b, FiniteDimensional ℂ (cycDeg ρ w b)) ∧
      ∀ B : ℕ, ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ S.n ^ m

/-- The character of the universal `W_loc(mθ)`-type module. -/
def M0G (m : ℕ) : PowerSeries ℚ := McharG S.f (lwSpec S m)

variable {S}

theorem univFD_zero (hF : FusionTotalBoundG S) (m : ℕ) : UnivFD S.f (lwSpec S m) :=
  (hF m _ _ _ (univ_localWeylRelG S m)).1

/-- **`huniv` for `M0G`.** -/
theorem huniv_M0G (hF : FusionTotalBoundG S) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M0G S m) :=
  fun m _ _ _ _ _ hw b =>
    finrank_le_McharG S.f (univFD_zero hF m) ((localWeylRelG_iff S _ _ m).mp hw) b

/-- **`total_le` for `M0G`.** -/
theorem total_le_M0G (hF : FusionTotalBoundG S) (m B : ℕ) :
    ∑ N ∈ Finset.range B, coeff N (M0G S m) ≤ (S.n : ℚ) ^ m := by
  have := (hF m _ _ _ (univ_localWeylRelG S m)).2 B
  simp only [M0G, McharG, coeff_mk]
  exact_mod_cast this

/-! ## A full relation family -/

variable (S) in
/-- **The universal characters of a relation family** (`spec a b`: the relations of `M_{a,b}`). -/
def MuniG (spec : ℕ → ℕ → RelSpec S.n) (a b : ℕ) : PowerSeries ℚ := McharG S.f (spec a b)

variable {spec : ℕ → ℕ → RelSpec S.n}

theorem MuniG_nonneg (a b N : ℕ) : 0 ≤ coeff N (MuniG S spec a b) := McharG_nonneg _ _ _

theorem MuniG_zero (hspec : ∀ m, spec 0 m = lwSpec S m) (m : ℕ) : MuniG S spec 0 m = M0G S m := by
  rw [MuniG, hspec]; rfl

/-- `huniv` for `MuniG`. -/
theorem huniv_MuniG (hspec : ∀ m, spec 0 m = lwSpec S m) (hF : FusionTotalBoundG S) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m →
        ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (MuniG S spec 0 m) := by
  intro m V _ _ ρ w hw b
  rw [MuniG_zero hspec]
  exact huniv_M0G hF m V ρ w hw b

theorem total_le_MuniG (hspec : ∀ m, spec 0 m = lwSpec S m) (hF : FusionTotalBoundG S) (m B : ℕ) :
    ∑ N ∈ Finset.range B, coeff N (MuniG S spec 0 m) ≤ (S.n : ℚ) ^ m := by
  rw [MuniG_zero hspec]; exact total_le_M0G hF m B

variable (S) in
/-- **Named input (U7, realization form, type-generic)**: a cyclic module with the relations of
`spec n 0` whose degree pieces dominate `Dem n`. -/
def DemazureRealizationG (spec : ℕ → ℕ → RelSpec S.n) (Dem : ℕ → PowerSeries ℚ) (n : ℕ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : CurrentModule S.f V) (w : V),
    Sat S.f ρ w (spec n 0) ∧ ∀ N, coeff N (Dem n) ≤ (Module.finrank ℂ (cycDeg ρ w N) : ℚ)

/-- **`dem_le` is generic**: the universal bound plus a realization. -/
theorem dem_le_of_realizationG {Dem : ℕ → PowerSeries ℚ} {n : ℕ} (hfd : UnivFD S.f (spec n 0))
    (hD : DemazureRealizationG S spec Dem n) : CoeffLe (Dem n) (MuniG S spec n 0) := by
  obtain ⟨V, _, _, ρ, w, hrel, hdim⟩ := hD
  intro N
  exact (hdim N).trans (finrank_le_McharG S.f hfd hrel N)

/-- **The squeeze inputs for the universal characters**: `nonneg`, `total_le` and `dem_le` are
type-generic; only `rec_le`, the finiteness of the `a ≥ 1` pieces, `FusionTotalBoundG` and the
realizations remain. -/
theorem fusionSqueezeInputsG_of_univ {Dem : ℕ → PowerSeries ℚ}
    (hspec : ∀ m, spec 0 m = lwSpec S m) (hF : FusionTotalBoundG S)
    (hfd : ∀ a b, UnivFD S.f (spec (a + 1) b))
    (hrec : ∀ a b, CoeffLe (MuniG S spec (a + 1) b)
      (MuniG S spec a (b + 1) + X ^ (2 * a + b + 1) * MuniG S spec a b))
    (hD : ∀ n, DemazureRealizationG S spec Dem n) :
    FusionSqueezeInputsG Dem S.n (MuniG S spec) where
  nonneg := MuniG_nonneg
  rec_le := hrec
  dem_le n := by
    refine dem_le_of_realizationG ?_ (hD n)
    rcases n with _ | n
    · rw [hspec]; exact univFD_zero hF 0
    · exact hfd n 0
  total_le := total_le_MuniG hspec hF

/-- **U5 for any sector** from the universal relation family: `FusionTotalBoundG`, `rec_le`,
the `a ≥ 1` finiteness, the realizations and the count. -/
theorem fusionModuleBoundG_of_univ {Dem : ℕ → PowerSeries ℚ}
    (hspec : ∀ m, spec 0 m = lwSpec S m) (hF : FusionTotalBoundG S)
    (hfd : ∀ a b, UnivFD S.f (spec (a + 1) b))
    (hrec : ∀ a b, CoeffLe (MuniG S spec (a + 1) b)
      (MuniG S spec a (b + 1) + X ^ (2 * a + b + 1) * MuniG S spec a b))
    (hD : ∀ n, DemazureRealizationG S spec Dem n)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (fusionOf Dem m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (fusionOf Dem m) = (S.n : ℚ) ^ m) :
    FusionModuleBoundG S (fusionOf Dem) :=
  fusionModuleBoundG_of_squeeze S rfl (fusionSqueezeInputsG_of_univ hspec hF hfd hrec hD) hcount
    (huniv_MuniG hspec hF)

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.localWeylRelG_iff
#print axioms VOA.DeligneAudit.UnivG.huniv_M0G
#print axioms VOA.DeligneAudit.UnivG.total_le_M0G
#print axioms VOA.DeligneAudit.UnivG.dem_le_of_realizationG
#print axioms VOA.DeligneAudit.UnivG.fusionSqueezeInputsG_of_univ
#print axioms VOA.DeligneAudit.UnivG.fusionModuleBoundG_of_univ
end AxiomAudit
