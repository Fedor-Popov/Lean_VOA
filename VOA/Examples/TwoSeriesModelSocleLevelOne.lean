/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelSocleEndpoint

/-!
# Sanity check: the membership bound holds at `n = 1`

At `n = 1` the coefficient ring is `R_1 = ℂ` (`T_j = 0`), the model `S_{1,r}` is the
`ℂ`-span of the jet word symbols, homogeneous of polynomial degree `2r`, and there is exactly
one socle word of size `r` (all clusters of size one, `N = r`, degree `r`).

* `genCoeff_isHomogeneous`, `wordSym_isHomogeneous` — the jet word symbols of length `r` are
  homogeneous of degree `2r`;
* (`mword_one`, from `TwoSeriesStrictLevelOne`: at `n = 1` the model word symbols are the jet
  word symbols;)
* `vMem_one_ne_bot` — a nonzero membership space at `n = 1` forces `N = r` and `d = r`;
* `modelSocleMembership_one` — **`ModelSocleMembership 1 r` holds for every `r`**, so the
  remaining input is satisfiable and of the right shape; `modelSocleSpectrum_one` — the model
  socle data at `n = 1` through the new route.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.SocleDual VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.AffineVOA.CorrectedR (Generator)

noncomputable section

/-! ### Homogeneity of the jet word symbols -/

/-- Every coefficient of the series is homogeneous of degree `1`. -/
def SerH (f : JetSer) : Prop := ∀ j, (PowerSeries.coeff j f).IsHomogeneous 1

theorem serH_colSer (b : Fin 2) : SerH (colSer b) := fun j => by
  rw [colSer, PowerSeries.coeff_mk]; exact isHomogeneous_X _ _

theorem serH_dS {f : JetSer} (hf : SerH f) : SerH (dS f) := fun j => by
  rw [PowerSeries.coeff_derivative]
  have h := (hf (j + 1)).mul (isHomogeneous_C (Fin 2 × ℕ) ((j : ℂ) + 1))
  simpa [MvPolynomial.C_add] using h

theorem coeff_mul_isHomogeneous {f g : JetSer} (hf : SerH f) (hg : SerH g) (j : ℕ) :
    (PowerSeries.coeff j (f * g)).IsHomogeneous 2 := by
  rw [PowerSeries.coeff_mul]
  exact IsHomogeneous.sum _ _ _ fun p _ => (hf p.1).mul (hg p.2)

theorem genCoeff_isHomogeneous (g : Fin 4) (a : ℕ) : (genCoeff g a).IsHomogeneous 2 := by
  rw [genCoeff]
  fin_cases g
  · exact coeff_mul_isHomogeneous (serH_colSer 0) (serH_colSer 0) a
  · exact coeff_mul_isHomogeneous (serH_colSer 0) (serH_colSer 1) a
  · exact coeff_mul_isHomogeneous (serH_colSer 1) (serH_colSer 1) a
  · change (PowerSeries.coeff a
      (dS (colSer 0) * colSer 1 - colSer 0 * dS (colSer 1))).IsHomogeneous 2
    rw [map_sub]
    exact (coeff_mul_isHomogeneous (serH_dS (serH_colSer 0)) (serH_colSer 1) a).sub
      (coeff_mul_isHomogeneous (serH_colSer 0) (serH_dS (serH_colSer 1)) a)

theorem genSpan_le_homogeneous : genSpan ≤ homogeneousSubmodule (Fin 2 × ℕ) ℂ 2 := by
  rw [genSpan, Submodule.span_le]
  rintro _ ⟨⟨g, a⟩, rfl⟩
  exact (mem_homogeneousSubmodule _ _).mpr (genCoeff_isHomogeneous g a)

theorem wordSym_isHomogeneous (w : List (Generator × ℕ)) :
    (wordSym w).IsHomogeneous (2 * w.length) := by
  induction w with
  | nil => simpa using isHomogeneous_one (Fin 2 × ℕ) ℂ
  | cons l w ih =>
    rw [wordSym_cons, List.length_cons, show 2 * (w.length + 1) = 2 + 2 * w.length by ring]
    exact ((mem_homogeneousSubmodule _ _).mp
      (genSpan_le_homogeneous (letterSym_mem_genSpan l))).mul ih

/-! ### The model at `n = 1` -/

theorem rn1_eq_algebraMap (τ : Rn 1) : τ = algebraMap ℂ (Rn 1) (εn 1 le_rfl τ) := by
  apply εn_one_injective
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem algebraMap_rn1_injective : Function.Injective (algebraMap ℂ (Rn 1)) := by
  intro a b h
  have := congrArg (εn 1 le_rfl) h
  rwa [AlgHom.commutes, AlgHom.commutes] at this

theorem θn_one (τ : Rn 1) : θn 1 τ = τ := by
  rw [rn1_eq_algebraMap τ, AlgHom.commutes]

theorem Θ_X (R : Type) [CommRing R] [Algebra ℂ R] (θ : R →ₐ[ℂ] R) (x : Fin 2 × ℕ) :
    Θ R θ (X x) = MvPolynomial.C (algebraMap ℂ R ((2 : ℂ) ^ x.2)) * X x := by
  simp [Θ]

theorem modelDeg_one_le (r : ℕ) (d : ℤ) :
    modelDeg (Rn 1) (tn 1) r d ≤
      (homogeneousSubmodule (Fin 2 × ℕ) ℂ (2 * r)).map (ι (Rn 1)).toLinearMap := by
  rw [modelDeg, Submodule.span_le]
  rintro _ ⟨w, hw, -, rfl⟩
  refine ⟨wordSym w, ?_, (mword_one w).symm⟩
  rw [SetLike.mem_coe, mem_homogeneousSubmodule, ← hw]
  exact wordSym_isHomogeneous w

/-- **At `n = 1`, a nonzero membership space forces `N = r` and `d = r`.** -/
theorem vMem_one_ne_bot {r : ℕ} {d : ℤ} {N : ℕ} {τ : Rn 1}
    (hτ : τ ∈ vMem (Rn 1) (tn 1) r d (2 * N)) (hτ0 : τ ≠ 0) : N = r ∧ d = r := by
  have hQ : vLift (Rn 1) (2 * N) τ ∈ modelDeg (Rn 1) (tn 1) r d := hτ
  set c := εn 1 le_rfl τ with hc
  have hc0 : c ≠ 0 := by
    intro h; apply hτ0; rw [rn1_eq_algebraMap τ, ← hc, h, map_zero]
  have hι : vLift (Rn 1) (2 * N) τ = ι (Rn 1) (MvPolynomial.C c * X (1, 0) ^ (2 * N)) := by
    rw [vLift_apply, map_mul, map_pow, ι_X, ι_C, ← rn1_eq_algebraMap]
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP, hPe⟩ := modelDeg_one_le r d hQ
    rw [hι] at hPe
    have hPe' := ι_one_injective hPe
    rw [SetLike.mem_coe, mem_homogeneousSubmodule, hPe'] at hP
    have h2 := isHomogeneous_C_mul_X_pow c ((1 : Fin 2), 0) (2 * N)
    have hne : (MvPolynomial.C c * X (1, 0) ^ (2 * N) : JetPoly) ≠ 0 :=
      mul_ne_zero (fun h => hc0 (by simpa using h)) (pow_ne_zero _ (X_ne_zero _))
    have := h2.inj_right hP hne
    omega
  · have h1 := Module.End.mem_eigenspace_iff.mp (Θ_modelDeg (Rn 1) (tn 1) (θn 1) (θn_tn 1) r d hQ)
    rw [AlgHom.toLinearMap_apply, vLift_apply, map_mul, map_pow, Θ_C, Θ_X, θn_one] at h1
    simp only [pow_zero, map_one, one_mul] at h1
    have hne : (MvPolynomial.C τ * X (1, 0) ^ (2 * N) : MPoly (Rn 1)) ≠ 0 := fun h =>
      hτ0 (C_mul_pow_eq_zero (Rn 1) h)
    have h2 : ((2 : ℂ) ^ (d - r) - 1) •
        (MvPolynomial.C τ * X (1, 0) ^ (2 * N) : MPoly (Rn 1)) = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · have h3 : (2 : ℂ) ^ (d - r) = (2 : ℂ) ^ (0 : ℤ) := by rw [zpow_zero]; exact sub_eq_zero.mp h
      have := two_zpow_injective h3
      omega
    · exact absurd h hne

/-- The one socle label at `n = 1`. -/
def levelOneLabel (r : ℕ) : SocleIndex 1 r :=
  ⟨⟨r, Nat.lt_succ_self r⟩, ⟨fun _ => 0, by simp⟩⟩

theorem levelOneLabel_degree (r : ℕ) : socleDegree (levelOneLabel r).2.1 = r := by
  simp only [levelOneLabel, socleDegree, inversions]
  simp

/-- **The membership bound holds at `n = 1`.** -/
theorem modelSocleMembership_one (r : ℕ) : ModelSocleMembership 1 r := by
  intro d N
  have hle1 : Module.rank ℂ (vMem (Rn 1) (tn 1) r d (2 * N)) ≤ 1 := by
    have hinj : Function.Injective ((εn 1 le_rfl).toLinearMap ∘ₗ
        (vMem (Rn 1) (tn 1) r d (2 * N)).subtype) := fun a b h =>
      Subtype.ext (εn_one_injective h)
    have := LinearMap.rank_le_of_injective _ hinj
    rwa [Module.rank_self] at this
  by_cases hex : ∃ τ ∈ vMem (Rn 1) (tn 1) r d (2 * N), τ ≠ 0
  · obtain ⟨τ, hτ, hτ0⟩ := hex
    obtain ⟨hN, hd⟩ := vMem_one_ne_bot hτ hτ0
    refine hle1.trans ?_
    have hpos : 0 < Nat.card {i : SocleIndex 1 r //
        ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N} := by
      haveI : Nonempty {i : SocleIndex 1 r //
          ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N} :=
        ⟨⟨levelOneLabel r, by rw [levelOneLabel_degree, hd], by simp [levelOneLabel, hN]⟩⟩
      exact Nat.card_pos
    exact_mod_cast hpos
  · push Not at hex
    have hbot : vMem (Rn 1) (tn 1) r d (2 * N) = ⊥ := by
      rw [eq_bot_iff]; intro τ hτ; rw [Submodule.mem_bot]; exact hex τ hτ
    rw [hbot, rank_bot]
    exact zero_le

/-- The model socle data at `n = 1`, through the membership route. -/
theorem modelSocleSpectrum_one (r : ℕ) : ModelSocleSpectrum 1 r :=
  modelSocleSpectrum_of_membership (modelSocleMembership_one r)

end

end VOA.TwoSeries.StrictModel
