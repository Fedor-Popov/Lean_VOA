/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterReduction
import VOA.Examples.TwoSeriesLevels
import VOA.Examples.VirasoroSingularGram

/-!
# The jet relations of `M(2, 2n+3)` and the refined PBW character from the total count

* `twoSeriesLevels_c_eq_bsaCharge` — the target charge is the BSA charge `bsaCharge (2n+2)`;
* `twoSeries_hasJetRelations_all` — the jet relations of order `n+1` hold at the target charge
  for **every** `n` (for `n ≥ 1` from the vacuum BSA singular vector, for `n = 0` from
  `L_{-2}|0⟩` at `c = 0`);
* `twoSeries_hpbw_of_gordonLowerBound` — the length-refined PBW lower bound `hpbw` for the
  Andrews–Gordon coefficient `TwoSeriesCharacter.gordonCoeff n`, from the **total** Andrews–Gordon
  lower bound `GordonLowerBound c_{2,2n+3} n`.

The coset-transfer consequence (Affine GU ⇒ GU of `M(2,2n+3)`, conditional on `hA`, `hinv`, `hlow`),
`twoSeries_gradedUnitary_of_affine_invariants_gordon`, is in `TwoSeriesCharacterGU.lean`
so that this file does not import the graded-unitarity (Koszul/BRST) files; it is
used, unconditionally, by the Virasoro classical-freeness theorem.
-/

namespace VOA.TwoSeries

open VirGradedUnitarity VirGoodFil
open scoped BigOperators

noncomputable section

/-- The target charge of the `n`th member is the BSA charge at level `2n+2`. -/
theorem twoSeriesLevels_c_eq_bsaCharge (n : ℕ) :
    (twoSeriesLevels n).c = VOA.VirModule.bsaCharge (2 * n + 2) := by
  rw [twoSeriesLevels_c]
  unfold boundaryCharge boundaryMinimalCentralCharge VOA.VirModule.bsaCharge
  have h1 : (2 * ((n + 1 : ℕ) : ℂ) + 1) ≠ 0 := by
    have : (2 * ((n + 1 : ℕ) : ℂ) + 1) = ((2 * n + 3 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 2 * n + 3 ≠ 0)
  have h2 : (((2 * n + 2 : ℕ) : ℂ) + 1) ≠ 0 := by
    have : (((2 * n + 2 : ℕ) : ℂ) + 1) = ((2 * n + 3 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 2 * n + 3 ≠ 0)
  push_cast at h1 h2 ⊢
  field_simp
  ring

/-- `L_{-2}|0⟩` is singular at `c = 0`. -/
theorem negWordVir_two_mem_maxIdeal_zero :
    VOA.VirModule.negWordVir 0 [0] ∈ VOA.VirSimple.maxIdealVir 0 := by
  have hv : VOA.VirModule.negWordVir 0 [0] ∈ VOA.VirModule.gradingVir 0 ((2 : ℕ) : ℤ) :=
    virFil_le_grading 0 1 _ (VOA.LeeYangCharacter.negWordVir_mem_virFil 0 (w := [0]) (ℓ := 1)
      (N := 2) (by simp) rfl)
  refine VOA.VirDeformModes.NormalOrdering.singular_mem_maxIdeal 0 (n := 2) (by norm_num) _ hv
    ?_ ?_
  · rw [VOA.VirModule.negWordVir_cons, VOA.VirModule.negWordVir_nil,
      VOA.VirModule.Lop_apply_bracket, VOA.VirModule.Lop_vacuum 0 (by norm_num),
      VOA.VirModule.Lop_vacuum 0 (by norm_num)]
    simp
  · rw [VOA.VirModule.negWordVir_cons, VOA.VirModule.negWordVir_nil,
      VOA.VirModule.Lop_apply_bracket, VOA.VirModule.Lop_vacuum 0 (by norm_num),
      VOA.VirModule.Lop_vacuum 0 (by norm_num)]
    simp

/-- **The jet relations at the target charge, for every `n`.** -/
theorem twoSeries_hasJetRelations_all (n : ℕ) :
    VOA.TwoSeriesCharacter.HasJetRelations (twoSeriesLevels n).c n := by
  rw [twoSeriesLevels_c_eq_bsaCharge]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc : VOA.VirModule.bsaCharge (2 * 0 + 2) = 0 := by
      norm_num [VOA.VirModule.bsaCharge]
    rw [hc]
    refine VOA.TwoSeriesCharacter.hasJetRelations_of_singular 0 0 _
      negWordVir_two_mem_maxIdeal_zero 1 one_ne_zero ?_
    simp
  · exact VOA.TwoSeriesCharacter.twoSeries_hasJetRelations n hn

/-- **The refined PBW input `hpbw` for the Andrews–Gordon coefficient, from the total lower
bound.** -/
theorem twoSeries_hpbw_of_gordonLowerBound (n : ℕ)
    (hlow : VOA.TwoSeriesCharacter.GordonLowerBound (twoSeriesLevels n).c n) :
    ∀ (N : ℤ) (p : ℕ), ∑ r ∈ Finset.range (p + 1), VOA.TwoSeriesCharacter.gordonCoeff n N r ≤
      Module.finrank ℂ ((virGradedFlag (twoSeriesLevels n).c).pieceIn p N) :=
  VOA.TwoSeriesCharacter.hpbw_of_gordonLowerBound _ n (twoSeries_hasJetRelations_all n) hlow

end

end VOA.TwoSeries
