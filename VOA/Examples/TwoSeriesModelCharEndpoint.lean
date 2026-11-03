/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharCountG

/-!
# The model character bound, for every `n`

* `twoSeriesModelCharacter_all` — **`TwoSeriesModelCharacter n` is proved outright for every
  `n ≥ 1`**: the `q^N` coefficient of the Arakawa–Dai product `((q^{2n+1};q^{2n+1})_∞/(q;q)_∞)³`
  is at most `Σ_{r ≤ N} dim S_{n,r,N}`.  Proof: the product equals the Chern–Tran–Wakhare
  fermionic series (`fermSeries_eq_product`, a Bailey-chain computation), and the fermionic
  series is a lower bound for the model (`fermSeries_le_model`: independent Gordon-profile
  functionals built from block covariants `T^c G` and symmetrized Feigin–Stoyanovsky functions).
* `twoSeries_gradedUnitary_of_strictModel_det` — **Affine GU ⇒ GU of `M(2, 2n+3)` for every
  `n ≥ 1`**, conditional only on `hA`, detection `TwoSeriesModelDetects n` and the model socle
  data `ModelSocleSpectrum n r`; `twoSeriesStrictModel_all` gives the strict symbol maps from
  detection alone.
* The `n = 2` special case is also recorded separately (`twoSeriesModelCharacter_two`, via the
  colour-`≤ 1` lower bound `fermSeries_two_le_model`, which holds for every `n ≥ 2`).
* `TwoSeriesModelFermionicLower n` — the fermionic lower bound as a standalone statement,
  equivalent to the model character bound; proved for every `n ≥ 1`
  (`twoSeriesModelFermionicLower_all`).

Everything is proved; the endpoints are `#print axioms`-clean, conditional on the displayed
hypotheses.
-/

namespace VOA.TwoSeries.ModelChar

open VOA.TwoSeries.StrictModel VOA.GradedUnitaryCohomology VirGradedUnitarity
open Sl2CosetConcrete VOA.TwoSeries

noncomputable section

/-- **The model character bound at `n = 2`, proved outright.** -/
theorem twoSeriesModelCharacter_two : TwoSeriesModelCharacter 2 := by
  intro N
  rw [← fermSeries_eq_product 2]
  exact fermSeries_two_le_model le_rfl N

/-- **The fermionic lower bound at index `n`**: the `q^N` coefficient of the `n`-colour
Chern–Tran–Wakhare series is at most `Σ_{r ≤ N} dim S_{n,r,N}` (proved for all `n ≥ 1` below). -/
def TwoSeriesModelFermionicLower (n : ℕ) : Prop :=
  ∀ N : ℕ, PowerSeries.coeff N (fermSeries n) ≤
    ∑ r ∈ Finset.range (N + 1), (Module.finrank ℂ (modelDeg (Rn n) (tn n) r (N : ℤ)) : ℚ)

/-- The fermionic lower bound implies the model character bound. -/
theorem twoSeriesModelCharacter_of_fermionicLower {n : ℕ} (h : TwoSeriesModelFermionicLower n) :
    TwoSeriesModelCharacter n := by
  intro N
  rw [← fermSeries_eq_product n]
  exact h N

/-- Conversely, the model character bound implies the fermionic lower bound. -/
theorem fermionicLower_of_twoSeriesModelCharacter {n : ℕ} (h : TwoSeriesModelCharacter n) :
    TwoSeriesModelFermionicLower n := by
  intro N
  rw [fermSeries_eq_product n]
  exact h N

theorem twoSeriesModelFermionicLower_one : TwoSeriesModelFermionicLower 1 :=
  fermionicLower_of_twoSeriesModelCharacter twoSeriesModelCharacter_one

theorem twoSeriesModelFermionicLower_two : TwoSeriesModelFermionicLower 2 :=
  fun N => fermSeries_two_le_model le_rfl N

/-- **Strict symbol maps `gr_r L_{-8/5} ↪ S_{2,r}`**, conditional only on detection. -/
def twoSeriesStrictModel_two (det : TwoSeriesModelDetects 2) (r : ℕ) : StrictModelMap 2 r :=
  twoSeriesStrictModel (by norm_num) det twoSeriesModelCharacter_two r

/-- **Affine GU ⇒ GU of `M(2, 7)`**, `#print axioms`-clean, conditional on `hA`, detection
at `n = 2`, and the model socle data; the model character bound is discharged. -/
theorem twoSeries_gradedUnitary_two_of_strictModel
    (hA : GradedUnitary (affineForm (twoSeriesLevels 2)) (affineRealStructure (twoSeriesLevels 2))
      (affineFlag (twoSeriesLevels 2)))
    (det : TwoSeriesModelDetects 2) (spec : ∀ r, ModelSocleSpectrum 2 r) :
    VirGradedUnitary (twoSeriesLevels 2).c (targetRealStructure (twoSeriesLevels 2)) :=
  twoSeries_gradedUnitary_of_strictModel 2 (by norm_num) hA det twoSeriesModelCharacter_two spec

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, with the model character bound replaced by the
fermionic lower bound `TwoSeriesModelFermionicLower n`. -/
theorem twoSeries_gradedUnitary_of_fermionicLower (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (ferm : TwoSeriesModelFermionicLower n)
    (spec : ∀ r, ModelSocleSpectrum n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel n hn hA det
    (twoSeriesModelCharacter_of_fermionicLower ferm) spec

/-! ### Every `n` -/

/-- **The model character bound, proved outright for every `n ≥ 1`.** -/
theorem twoSeriesModelCharacter_all (n : ℕ) (hn : 1 ≤ n) : TwoSeriesModelCharacter n := by
  intro N
  rw [← fermSeries_eq_product n]
  exact fermSeries_le_model hn N

/-- The fermionic lower bound holds for every `n ≥ 1`. -/
theorem twoSeriesModelFermionicLower_all (n : ℕ) (hn : 1 ≤ n) : TwoSeriesModelFermionicLower n :=
  fun N => fermSeries_le_model hn N

/-- **Strict symbol maps `gr_r L_{k_n} ↪ S_{n,r}` for every `n ≥ 1`**, conditional only on
detection. -/
def twoSeriesStrictModel_all {n : ℕ} (hn : 1 ≤ n) (det : TwoSeriesModelDetects n) (r : ℕ) :
    StrictModelMap n r :=
  twoSeriesStrictModel hn det (twoSeriesModelCharacter_all n hn) r

/-- **Affine GU ⇒ GU of `M(2, 2n+3)` for every `n ≥ 1`**, `#print axioms`-clean,
conditional only on `hA`, detection `TwoSeriesModelDetects n`, and the model socle data; the
model character bound is discharged. -/
theorem twoSeries_gradedUnitary_of_strictModel_det (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (spec : ∀ r, ModelSocleSpectrum n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel n hn hA det (twoSeriesModelCharacter_all n hn) spec

end

end VOA.TwoSeries.ModelChar
