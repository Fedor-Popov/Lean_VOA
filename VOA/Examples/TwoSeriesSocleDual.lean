/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSocleDualCore
import VOA.Examples.TwoSeriesSocleCountGordon

/-!
# The socle input from socle data on `gr_r L_k(sl₂)`

`twoSeries_gradedUnitary_of_socleInput` (Affine GU ⇒ GU of `M(2, 2n+3)`) needs, besides `hA`,
the input `TwoSeriesSocleInput n`: jointly cyclic dual vectors on `gr_r L_{k_n}` with prescribed
degree, charge and Cartan relations.  This file replaces that input — a *construction* of
functionals — by two *statements about the singular vectors* of `gr_r L_{k_n}`, which is the
form in which the numerical evidence observes it.

* `grDeg_iSup`, `grDeg_neg`, `grDeg_finiteDimensional`, `grRho_grDeg`, `grRho_hf` — the
  grading facts for the actual `gr_r L_k` at every level, packaged as
  `grModeGrading : ModeGrading (grRho L r) (grDeg L r)`.  Proved outright.
* `grCart L r N` — the image of the Cartan ideal `I_N` acting on `gr_r L_k`.
* `TwoSeriesSocleSpectrum n` — OPEN (affine input, two clauses):
  1. `rank_le` — the lowest-weight `𝔤[t]`-singular vectors of `gr_r L_k` of conformal degree `d`
     and `h₀`-charge `c` span a space of dimension at most the number of socle words `x` of
     total size `r` with `socleDegree x = d` and `c = -2·length x`;
  2. `transverse` — such a singular vector of charge `-2N` is never congruent, modulo other
     conformal degrees and other `h₀`-charges, to an element of `I_N · gr_r L_k`.
* `TwoSeriesSocleSpectrum.toSocleInput : TwoSeriesSocleInput n`, and
  `twoSeries_gradedUnitary_of_socleSpectrum` — **Affine GU ⇒ GU of `M(2, 2n+3)`,
  conditional only on `hA` and `TwoSeriesSocleSpectrum n`.**
-/

namespace VOA.TwoSeries

open VOA.SocleDual VOA.SocleEval VOA.CyclicEval VOA.InvariantSymbol MvPolynomial Module
open VOA.ConcreteHodge VOA.KoszulConcrete VOA.SymbolModel VOA.GradedUnitaryCohomology
open VirGradedUnitarity Sl2CosetConcrete

noncomputable section

variable (L : CosetLevels)

/-! ### The grading of `gr_r L_k` -/

theorem piece_le_aFil' (r : ℕ) (d : ℤ) : (affineFlag L).piece r d ≤ aFil L r :=
  le_iSup (fun m => (affineFlag L).piece r m) d

theorem grDeg_iSup (r : ℕ) : ⨆ d, grDeg L r d = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact Submodule.iSup_induction' (fun m : ℤ => (affineFlag L).piece r m)
    (motive := fun z hz => Submodule.Quotient.mk (p := grKer L r) (⟨z, hz⟩ : aFil L r) ∈
      ⨆ d, grDeg L r d)
    (fun d z hz => Submodule.mem_iSup_of_mem d (Submodule.mem_map.mpr ⟨_, hz, rfl⟩))
    (by dsimp only
        rw [show (⟨0, _⟩ : aFil L r) = 0 from rfl, Submodule.Quotient.mk_zero]
        exact Submodule.zero_mem _)
    (fun a b ha hb hha hhb => by
      dsimp only at hha hhb ⊢
      rw [show (⟨a + b, _⟩ : aFil L r) = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, Submodule.Quotient.mk_add]
      exact add_mem hha hhb) hy

theorem grDeg_neg (r : ℕ) (d : ℤ) (hd : d < 0) : grDeg L r d = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  have h1 : (y : ASpace L) ∈ (AVOA L).grading d := (affineFlag L).le_grading r d hy
  rw [(AVOA L).positivity d hd, Submodule.mem_bot] at h1
  have : y = 0 := Subtype.ext h1
  rw [this, map_zero]
  exact Submodule.zero_mem _

instance piece_finiteDimensional' (r : ℕ) (d : ℤ) :
    FiniteDimensional ℂ ((affineFlag L).piece r d) :=
  haveI := (AVOA L).finrank d
  Submodule.finiteDimensional_of_le ((affineFlag L).le_grading r d)

theorem grDeg_finiteDimensional (r : ℕ) (d : ℤ) : FiniteDimensional ℂ (grDeg L r d) := by
  haveI : FiniteDimensional ℂ (((affineFlag L).piece r d).comap (aFil L r).subtype) :=
    LinearEquiv.finiteDimensional
      (Submodule.comapSubtypeEquivOfLe (piece_le_aFil' L r d)).symm
  unfold grDeg
  infer_instance

theorem grRho_grDeg (r : ℕ) (k : Fin 3 × ℕ) (d : ℤ) :
    ∀ m ∈ grDeg L r d, grRho L r k m ∈ grDeg L r (d - (k.2 : ℤ)) := by
  rintro _ ⟨y, hy, rfl⟩
  refine Submodule.mem_map.mpr ⟨⟨aMode L k.1 k.2 y, aMode_aFil L k.1 k.2 r y y.2⟩, ?_, rfl⟩
  have h := aMode_flag L k.1 k.2 r d y hy
  rw [eN_natCast, add_zero] at h
  exact h

theorem aMode_hf :
    aMode L 2 0 * aMode L 1 0 - aMode L 1 0 * aMode L 2 0 = (-2 : ℂ) • aMode L 1 0 := by
  have h := (aAction L).current_comm 2 1 0 0
  change mode ((ASVA L).Y ((aAction L).current 2)) (0 : ℕ) *
      mode ((ASVA L).Y ((aAction L).current 1)) (0 : ℕ) -
    mode ((ASVA L).Y ((aAction L).current 1)) (0 : ℕ) *
      mode ((ASVA L).Y ((aAction L).current 2)) (0 : ℕ) =
    (-2 : ℂ) • mode ((ASVA L).Y ((aAction L).current 1)) (0 : ℕ)
  push_cast
  rw [h, Fin.sum_univ_three]
  have h0 : AffineVOA.fabc 2 1 0 = 0 := rfl
  have h1 : AffineVOA.fabc 2 1 1 = -2 := rfl
  have h2 : AffineVOA.fabc 2 1 2 = 0 := rfl
  simp [h0, h1, h2]

theorem grRho_hf (r : ℕ) :
    grRho L r (2, 0) * grRho L r (1, 0) - grRho L r (1, 0) * grRho L r (2, 0) =
      (-2 : ℂ) • grRho L r (1, 0) := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply,
    Module.End.mul_apply, grRho_mk, LinearMap.smul_apply]
  rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (aMode_hf L) x

/-- **The grading hypotheses hold on the actual `gr_r L_k`**, at every level. -/
theorem grModeGrading (r : ℕ) : ModeGrading (grRho L r) (grDeg L r) where
  span := grDeg_iSup L r
  neg := grDeg_neg L r
  fin := grDeg_finiteDimensional L r
  deg := grRho_grDeg L r
  hf := grRho_hf L r

/-! ### The socle data and the socle input -/

/-- The image `I_N · gr_r L_k` of the Cartan ideal `I_N`, acting through the negative-transpose
calculus `H_{i+1} ↦ -J^h_{i+1}`. -/
def grCart (r N : ℕ) : Submodule ℂ (GrA L r) :=
  ⨆ (F : MvPolynomial ℕ ℂ) (_ : F ∈ cartanIdeal N), LinearMap.range (grCartanCalc L r F)

/-- OPEN (affine input, the dual form of `TwoSeriesSocleInput n`): **the socle data of
`gr_r L_k(sl₂)`**, `k = -2 + 2/(2n+1)`.

* `rank_le`: the lowest-weight `𝔤[t]`-singular vectors of `gr_r L_k` (killed by `J^a_{j+1}` and
  `f₀`) of conformal degree `d` and `h₀`-charge `c` span at most as many dimensions as there are
  socle words `x` of total size `r` with `socleDegree x = d` and `c = -2·length x`;
* `transverse`: a singular vector of degree `d` and charge `-2N` lying in
  `I_N · gr_r + Σ_{d' ≠ d} gr_{r,d'} + range (h₀ + 2N)` is zero.

Numerically (not a proof; with the Chevalley involution
exchanging highest- and lowest-weight conventions) `rank_le` holds with equality. -/
structure TwoSeriesSocleSpectrum (n : ℕ) : Prop where
  rank_le : ∀ (r : ℕ) (d : ℤ) (c : ℂ),
    finrank ℂ (sing (grRho (twoSeriesLevels n) r) (grDeg (twoSeriesLevels n) r) d c) ≤
      Nat.card {i : SocleIndex n r //
        (socleDegree i.2.1 : ℤ) = d ∧ c = -(2 * (((i.1 : ℕ) : ℕ) : ℂ))}
  transverse : ∀ (r : ℕ) (d : ℤ) (N : ℕ),
    Disjoint (sing (grRho (twoSeriesLevels n) r) (grDeg (twoSeriesLevels n) r) d
        (-(2 * (N : ℂ))))
      (avoid (grRho (twoSeriesLevels n) r) (grDeg (twoSeriesLevels n) r)
        (grCart (twoSeriesLevels n) r) d N)

theorem TwoSeriesSocleSpectrum.toSpectrum {n : ℕ} (S : TwoSeriesSocleSpectrum n) (r : ℕ) :
    SocleSpectrum (grRho (twoSeriesLevels n) r) (grDeg (twoSeriesLevels n) r)
      (fun i : SocleIndex n r => socleDegree i.2.1) (fun i => (i.1 : ℕ))
      (grCart (twoSeriesLevels n) r) where
  rank_le := S.rank_le r
  transverse := S.transverse r

theorem TwoSeriesSocleSpectrum.exists_duals {n : ℕ} (S : TwoSeriesSocleSpectrum n) (r : ℕ) :
    ∃ w : SocleIndex n r → Module.Dual ℂ (GrA (twoSeriesLevels n) r),
      (∀ m, (∀ i l, w i (word (grRho (twoSeriesLevels n) r) l m) = 0) → m = 0) ∧
      (∀ i (d : ℤ), d ≠ (socleDegree i.2.1 : ℤ) → ∀ m ∈ grDeg (twoSeriesLevels n) r d,
        w i m = 0) ∧
      (∀ i, w i ∘ₗ grRho (twoSeriesLevels n) r (2, 0) = (-(2 * ((i.1 : ℕ) : ℂ))) • w i) ∧
      (∀ i, ∀ m ∈ grCart (twoSeriesLevels n) r (i.1 : ℕ), w i m = 0) :=
  exists_socleDuals _ _ _ (grModeGrading _ r) (S.toSpectrum r)

/-- **The socle data give the socle input.** -/
def TwoSeriesSocleSpectrum.toSocleInput {n : ℕ} (S : TwoSeriesSocleSpectrum n) :
    TwoSeriesSocleInput n where
  w r := (S.exists_duals r).choose
  cyclic r := (S.exists_duals r).choose_spec.1
  supp r := (S.exists_duals r).choose_spec.2.1
  charge r := (S.exists_duals r).choose_spec.2.2.1
  cartan r i F hF := by
    refine LinearMap.ext fun m => ?_
    refine (S.exists_duals r).choose_spec.2.2.2 i _ ?_
    exact Submodule.mem_iSup_of_mem F (Submodule.mem_iSup_of_mem hF (LinearMap.mem_range_self _ m))

/-- **Affine GU ⇒ GU of `M(2, 2n+3)` from the socle data.**  `#print axioms`-clean,
conditional only on `hA` and the socle data `S : TwoSeriesSocleSpectrum n`. -/
theorem twoSeries_gradedUnitary_of_socleSpectrum (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (S : TwoSeriesSocleSpectrum n) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_socleInput n hA S.toSocleInput

end

end VOA.TwoSeries
