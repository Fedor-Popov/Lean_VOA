/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSpectrumCore
import VOA.Examples.TwoSeriesSocleDual
import VOA.Examples.TwoSeriesKoszulLeeYang

/-!
# The socle data at `n = 1` (Lee–Yang, `k = -4/3`), proved

`twoSeries_gradedUnitary_of_socleSpectrum n hA S` needs, besides `hA`, the socle data
`S : TwoSeriesSocleSpectrum n` of `gr_r L_{k_n}(sl₂)`.  At `n = 1` the socle words of size `r`
reduce to one word (`r` clusters of size one, degree `r`, charge `-2r`), and the data are
proved here from the proved Lee–Yang chain.

* `aMode_comm_zero`, `grRho_comm_zero` — `[J^a_m, J^b_0] = Σ_c f^{ab}_c J^c_m` on the simple
  affine factor and on `gr_r L_k`, every level.
* `grZeroModeRel : ZeroModeRel (grRho L r)` — the commutation facts with `e₀`, every level.
* The `h₀`-charge bound on the jet image: `jetDer_h0_genCoeff` (the generators `u², uv, v²,
  u'v - uv'` have charges `2, 0, -2, 0`), `jetImage_le_chargeAbove`, and
  `jetImage_charge_bound` — an `h₀`-eigenvector in `A_r` has eigenvalue `-2r + m`, `m ∈ ℕ`.
* `levelOneGrJetStrict r : GrJetStrict r` — the proved strict symbol maps
  `gr_r L_{-4/3} ↪ A_r`, for every `r` (the same proved inputs as `levelOneGrCyclicVector`).
* `levelOne_gr_charge_bound` — hence the same bound on `gr_r L_{-4/3}`.
* `twoSeriesSocleSpectrum_one : TwoSeriesSocleSpectrum 1` — **the socle data at `n = 1`,
  proved outright** (via `socleSpectrum_of_cyclic`).
* `leeYang_gradedUnitary_viaSocleSpectrum` — sanity check: the general theorem
  `twoSeries_gradedUnitary_of_socleSpectrum` at `n = 1` gives Lee–Yang GU conditional only on
  `hA`.  So the socle-data input is satisfiable and is not vacuous.
-/

namespace VOA.TwoSeries

open VOA.SocleDual VOA.SocleEval VOA.CyclicEval VOA.InvariantSymbol MvPolynomial Module
open VOA.ConcreteHodge VOA.KoszulConcrete VOA.SymbolModel VOA.GradedUnitaryCohomology
open VirGradedUnitarity Sl2CosetConcrete

noncomputable section

/-! ### Commutation with the zero modes, every level -/

section Level

variable (L : CosetLevels)

theorem aMode_comm_zero (a b : Fin 3) (m : ℕ) (x : ASpace L) :
    aMode L a m (aMode L b 0 x) =
      aMode L b 0 (aMode L a m x) + ∑ c, AffineVOA.fabc a b c • aMode L c m x := by
  have h := (aAction L).current_comm a b m 0
  have h' : mode ((ASVA L).Y ((aAction L).current a)) (m : ℤ) *
        mode ((ASVA L).Y ((aAction L).current b)) 0 -
      mode ((ASVA L).Y ((aAction L).current b)) 0 *
        mode ((ASVA L).Y ((aAction L).current a)) (m : ℤ) =
      ∑ c, AffineVOA.fabc a b c • mode ((ASVA L).Y ((aAction L).current c)) (m : ℤ) := by
    rw [h]
    split_ifs with hm
    · have hm0 : m = 0 := by omega
      subst hm0
      simp
    · simp
  have h2 := LinearMap.congr_fun h' x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply] at h2
  change mode ((ASVA L).Y ((aAction L).current a)) m
      (mode ((ASVA L).Y ((aAction L).current b)) 0 x) =
    mode ((ASVA L).Y ((aAction L).current b)) 0 (mode ((ASVA L).Y ((aAction L).current a)) m x) +
      ∑ c, AffineVOA.fabc a b c • mode ((ASVA L).Y ((aAction L).current c)) m x
  rw [← sub_eq_iff_eq_add', h2]

theorem grRho_comm_zero (r : ℕ) (a b : Fin 3) (m : ℕ) (y : GrA L r) :
    grRho L r (a, m) (grRho L r (b, 0) y) =
      grRho L r (b, 0) (grRho L r (a, m) y) + ∑ c, AffineVOA.fabc a b c • grRho L r (c, m) y := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [grRho_mk, Fin.sum_univ_three]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  have h := aMode_comm_zero L a b m x
  rw [Fin.sum_univ_three] at h
  simpa using h

/-- **The commutation facts with `e₀` hold on `gr_r L_k`**, at every level. -/
theorem grZeroModeRel (r : ℕ) : ZeroModeRel (grRho L r) where
  pos a j x hx := by
    rw [grRho_comm_zero, hx a, map_zero, zero_add]
    exact Finset.sum_eq_zero fun c _ => by rw [hx c, smul_zero]
  fe x := by
    rw [grRho_comm_zero, Fin.sum_univ_three]
    have h0 : AffineVOA.fabc 1 0 0 = 0 := rfl
    have h1 : AffineVOA.fabc 1 0 1 = 0 := rfl
    have h2 : AffineVOA.fabc 1 0 2 = -1 := rfl
    rw [h0, h1, h2]
    simp only [zero_smul, zero_add, neg_one_smul]
    abel
  he x := by
    rw [grRho_comm_zero, Fin.sum_univ_three]
    have h0 : AffineVOA.fabc 2 0 0 = 2 := rfl
    have h1 : AffineVOA.fabc 2 0 1 = 0 := rfl
    have h2 : AffineVOA.fabc 2 0 2 = 0 := rfl
    rw [h0, h1, h2]
    simp only [zero_smul, add_zero]

end Level

/-! ### The `h₀`-charge bound on the jet image `A_r` -/

/-- The `h₀`-charges `2, 0, -2, 0` of the generators `u², uv, v², u'v - uv'`, shifted by `2`. -/
def genShift : Fin 4 → ℕ := ![4, 2, 0, 2]

theorem serD_h0_genSer (g : Fin 4) :
    serD (jetDer (2, 0)).toLinearMap (genSer g) =
      PowerSeries.C (MvPolynomial.C (-2 + (genShift g : ℂ)) : JetPoly) * genSer g := by
  fin_cases g
  · change serD _ xSer = PowerSeries.C (MvPolynomial.C (-2 + (genShift 0 : ℂ))) * genSer 0
    rw [show (-2 + (genShift 0 : ℂ)) = 2 by simp [genShift]; norm_num]
    rw [serD_xSer, serD_h_u, map_ofNat, map_ofNat, genSer_zero, xSer]
    simp only [pow_zero, one_mul]
    ring
  · change serD _ ySer = PowerSeries.C (MvPolynomial.C (-2 + (genShift 1 : ℂ))) * genSer 1
    rw [show (-2 + (genShift 1 : ℂ)) = 0 by simp [genShift]]
    rw [serD_ySer, serD_h_u, serD_h_v, map_zero, map_zero, zero_mul]
    simp only [pow_zero, one_mul]
    ring
  · change serD _ zSer = PowerSeries.C (MvPolynomial.C (-2 + (genShift 2 : ℂ))) * genSer 2
    rw [show (-2 + (genShift 2 : ℂ)) = -2 by simp [genShift]]
    rw [serD_zSer, serD_h_v, map_neg, map_neg, map_ofNat, map_ofNat, genSer_two, zSer]
    simp only [pow_zero, one_mul]
    ring
  · change serD _ jSer = PowerSeries.C (MvPolynomial.C (-2 + (genShift 3 : ℂ))) * genSer 3
    rw [show (-2 + (genShift 3 : ℂ)) = 0 by simp [genShift]]
    rw [serD_jSer, serD_h_u, serD_h_v, map_zero, map_zero, zero_mul]
    simp only [pow_zero, one_mul, map_neg]
    ring

theorem jetDer_h0_genCoeff (g : Fin 4) (a : ℕ) :
    jetDer (2, 0) (genCoeff g a) = (-2 + (genShift g : ℂ)) • genCoeff g a := by
  rw [jetDer_genCoeff, serD_h0_genSer, PowerSeries.coeff_C_mul, MvPolynomial.smul_eq_C_mul]
  rfl

/-- The `h₀`-eigenspaces of the jet ring. -/
abbrev jetEig (μ : ℂ) : Submodule ℂ JetPoly := (jetRho (2, 0)).eigenspace μ

theorem mem_jetEig {μ : ℂ} {Q : JetPoly} : Q ∈ jetEig μ ↔ jetDer (2, 0) Q = μ • Q := by
  rw [jetEig, Module.End.mem_eigenspace_iff, jetRho_apply]

theorem mul_mem_jetEig {μ ν : ℂ} {P Q : JetPoly} (hP : P ∈ jetEig μ) (hQ : Q ∈ jetEig ν) :
    P * Q ∈ jetEig (μ + ν) := by
  rw [mem_jetEig] at *
  rw [Derivation.leibniz, hP, hQ, smul_eq_mul, smul_eq_mul, add_smul]
  simp only [Algebra.smul_def]
  ring

/-- The sum of the eigenspaces of eigenvalue `-2r + m`, `m ∈ ℕ`. -/
def chargeAbove (r : ℕ) : Submodule ℂ JetPoly := ⨆ m : ℕ, jetEig (-(2 * (r : ℂ)) + m)

theorem chargeAbove_mul (a b : ℕ) : chargeAbove a * chargeAbove b ≤ chargeAbove (a + b) := by
  rw [chargeAbove, chargeAbove, Submodule.iSup_mul]
  refine iSup_le fun i => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun j => ?_
  refine Submodule.mul_le.mpr fun P hP Q hQ => ?_
  refine Submodule.mem_iSup_of_mem (i + j) ?_
  have h := mul_mem_jetEig hP hQ
  convert h using 2
  push_cast; ring

theorem one_le_chargeAbove_zero : (1 : Submodule ℂ JetPoly) ≤ chargeAbove 0 := by
  rw [Submodule.one_le]
  refine Submodule.mem_iSup_of_mem 0 ?_
  rw [mem_jetEig, Derivation.map_one_eq_zero]
  simp

theorem genSpan_le_chargeAbove : genSpan ≤ chargeAbove 1 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨g, a⟩, rfl⟩
  refine Submodule.mem_iSup_of_mem (genShift g) ?_
  rw [mem_jetEig, jetDer_h0_genCoeff]
  congr 1
  push_cast; ring

theorem jetImage_le_chargeAbove (r : ℕ) : jetImage r ≤ chargeAbove r := by
  induction r with
  | zero => rw [jetImage, pow_zero]; exact one_le_chargeAbove_zero
  | succ r ih =>
    rw [jetImage, pow_succ]
    exact Submodule.mul_le.mpr fun x hx y hy =>
      chargeAbove_mul r 1 (Submodule.mul_mem_mul (ih hx) (genSpan_le_chargeAbove hy))

/-- **The charge bound on `A_r`**: an `h₀`-eigenvector of `A_r` has eigenvalue `-2r + m`. -/
theorem jetImage_charge_bound {r : ℕ} {Q : JetPoly} (hQ : Q ∈ jetImage r) (hQ0 : Q ≠ 0)
    {μ : ℂ} (hμ : jetDer (2, 0) Q = μ • Q) : ∃ m : ℕ, μ = -(2 * (r : ℂ)) + m := by
  by_contra hne
  push Not at hne
  have hdisj := (Module.End.eigenspaces_iSupIndep (jetRho (2, 0))) μ
  have hle : chargeAbove r ≤ ⨆ (ν : ℂ) (_ : ν ≠ μ), (jetRho (2, 0)).eigenspace ν :=
    iSup_le fun m => le_iSup₂_of_le (-(2 * (r : ℂ)) + m) (fun h => hne m h.symm) le_rfl
  have hmem : Q ∈ (jetRho (2, 0)).eigenspace μ := mem_jetEig.mpr hμ
  exact hQ0 ((Submodule.disjoint_def.mp hdisj) Q hmem (hle (jetImage_le_chargeAbove r hQ)))

/-! ### The strict symbol maps and the charge bound on `gr_r L_{-4/3}` -/

open VOA.AdamovicSymbol in
/-- The proved strict symbol maps `gr_r L_{-4/3}(sl₂) ↪ A_r`, every `r`. -/
def levelOneGrJetStrict : ∀ r : ℕ, GrJetStrict r
  | 0 => grJetStrict_zero
  | r + 1 => grJetStrict_of_leadingSymbol_product
      (jetLeadingSymbols_of_descends fun r => Desc.wordSymbolDescends (r + 2))
      (VOA.JetProduct.jetProductBound_of_lower VOA.JetFermionic.jetFermionicLower) r

/-- **The charge bound on `gr_r L_{-4/3}`.** -/
theorem levelOne_gr_charge_bound (r : ℕ) (c : ℂ) (x : SymbolModel.GrA r) (hx : x ≠ 0)
    (hc : SymbolModel.grRho r (2, 0) x = c • x) : ∃ m : ℕ, c = -(2 * (r : ℂ)) + m := by
  let S := levelOneGrJetStrict r
  have hfx : S.f x ≠ 0 := fun h => hx (S.injective (by rw [h, map_zero]))
  have he := LinearMap.congr_fun (S.intertwine (2, 0)) x
  simp only [LinearMap.comp_apply] at he
  rw [hc, map_smul] at he
  refine jetImage_charge_bound (S.f x).2 (fun h => hfx (Subtype.ext h)) (μ := c) ?_
  have := congrArg Subtype.val he
  rw [jetImgRho_coe] at this
  exact this.symm

/-! ### The socle data at `n = 1` -/

/-- The unique socle label at `n = 1`: `r` clusters of size one. -/
def levelOneSocleLabel (r : ℕ) : SocleIndex 1 r :=
  ⟨Fin.last r, ⟨fun _ => 0, by
    simp only [Fin.val_zero, zero_add, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact Fintype.card_fin _⟩⟩

theorem levelOneSocleLabel_degree (r : ℕ) : socleDegree (levelOneSocleLabel r).2.1 = r := by
  unfold socleDegree
  rw [Finset.Ico_self, Finset.sum_empty, add_zero]
  have : inversions (levelOneSocleLabel r).2.1 = 0 := by
    unfold inversions
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p - ⟨-, h⟩
    exact lt_irrefl _ h
  rw [this, add_zero]
  rfl

theorem levelOne_cart (r : ℕ) (V : GrCyclicVector r) :
    ∀ m ∈ grCart (twoSeriesLevels 1) r r, V.w m = 0 := by
  intro m hm
  have hle : grCart (twoSeriesLevels 1) r r ≤ LinearMap.ker V.w := by
    refine iSup_le fun F => iSup_le fun hF => ?_
    rintro _ ⟨y, rfl⟩
    change V.w (grCartanCalc (twoSeriesLevels 1) r F y) = 0
    have heq : grCartanCalc (twoSeriesLevels 1) r F =
        cartanCalc (SymbolModel.grRho r) bHPos (grCartanCommute r) F := by
      rw [eq_cartanCalc (grCartanCommute r) (grCartanCalc (twoSeriesLevels 1) r)
        (grCartanCalc_X (twoSeriesLevels 1) r)]
      rfl
    rw [heq]
    exact LinearMap.congr_fun (V.cartan F hF) y
  exact hle hm

/-- **The socle data at `n = 1`, proved outright.** -/
theorem twoSeriesSocleSpectrum_one : TwoSeriesSocleSpectrum 1 := by
  have key : ∀ r, SocleSpectrum (grRho (twoSeriesLevels 1) r) (grDeg (twoSeriesLevels 1) r)
      (fun i : SocleIndex 1 r => socleDegree i.2.1) (fun i => (i.1 : ℕ))
      (grCart (twoSeriesLevels 1) r) := by
    intro r
    let V : GrCyclicVector r := (levelOneGrJetStrict r).toGrCyclicVector
    exact socleSpectrum_of_cyclic (grZeroModeRel (twoSeriesLevels 1) r) V.w V.cyclic V.supp
      V.charge (levelOne_gr_charge_bound r) (levelOne_cart r V) (levelOneSocleLabel r)
      (levelOneSocleLabel_degree r) rfl
  exact ⟨fun r => (key r).rank_le, fun r => (key r).transverse⟩

/-- **Sanity check.**  The general theorem `twoSeries_gradedUnitary_of_socleSpectrum` at
`n = 1`, with the socle data proved, gives GU of `M(2, 5)` conditional only on `hA`. -/
theorem leeYang_gradedUnitary_viaSocleSpectrum
    (hA : GradedUnitary (affineForm (twoSeriesLevels 1)) (affineRealStructure (twoSeriesLevels 1))
      (affineFlag (twoSeriesLevels 1))) :
    VirGradedUnitary (twoSeriesLevels 1).c (targetRealStructure (twoSeriesLevels 1)) :=
  twoSeries_gradedUnitary_of_socleSpectrum 1 hA twoSeriesSocleSpectrum_one

end

end VOA.TwoSeries
