/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelSocleCartan
import VOA.Examples.TwoSeriesDetectFunctional

/-!
# The model socle data from one membership bound

The socle data `ModelSocleSpectrum n r` of the model `S_{n,r}` have two halves.  The
transversality half is proved outright (`model_transverse`).  This file reduces the rank half to
a statement about one commutative algebra:

* `vMem R t r d q` — the space of `τ ∈ R` with `τ · v₀^q` in the degree-`d` piece of `S_r`;
* `vMem_odd` — it vanishes for odd `q` (the sign automorphism `u, v ↦ -u, -v` fixes `S_r`);
* `singToVMem` / `singToVMem_injective` — a singular vector of degree `d` and charge `-q`
  is `τ · v₀^q` with `τ ∈ vMem R t r d q`, and `s ↦ τ` is injective;
* `model_rank_le` — hence the rank half follows from rank bounds on `vMem` at even `q = 2N`;
* `ModelSocleMembership n r` — **the remaining input**, in plain words: *for every conformal
  degree `d` and every `N`, the space of `τ ∈ R_n` with `v₀^{2N} τ` in the degree-`d` piece of
  `S_{n,r}` has dimension at most the number of socle words of size `r` with `N` letters and
  degree `d`*;
* `modelSocleSpectrum_of_membership` — `ModelSocleMembership n r ⇒ ModelSocleSpectrum n r`;
* `twoSeries_gradedUnitary_of_strictModel_membership` and
  `twoSeries_gradedUnitary_of_coinv_membership` — the two endpoints with the socle-data input
  replaced by the membership bound.

Everything is proved outright from the stated hypotheses.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.SocleDual VOA.CyclicEval VOA.InvariantSymbol
open VOA.SocleEval VOA.AdamovicSymbol Module
open VOA.AffineVOA.CorrectedR (Generator)
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

/-! ### The sign automorphism -/

/-- `u_j, v_j ↦ -u_j, -v_j` on the jet ring. -/
def sgnJ : JetPoly →ₐ[ℂ] JetPoly := aeval fun x => -X x

/-- `sgnJ` as a ring hom. -/
abbrev sgnJR : JetPoly →+* JetPoly := sgnJ

theorem map_sgnJ_colSer (b : Fin 2) : PowerSeries.map sgnJR (colSer b) = -colSer b := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_mk]
  simp [sgnJ]

theorem map_sgnJ_dS (f : JetSer) :
    PowerSeries.map sgnJR (dS f) = dS (PowerSeries.map sgnJR f) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

theorem map_sgnJ_genSer (g : Fin 4) : PowerSeries.map sgnJR (genSer g) = genSer g := by
  fin_cases g
  · simp [genSer_zero, xSer, map_sgnJ_colSer]
  · simp [genSer_one, ySer, map_sgnJ_colSer]
  · simp [genSer_two, zSer, map_sgnJ_colSer]
  · simp [genSer_three, jSer, map_sgnJ_dS, map_sgnJ_colSer]

theorem sgnJ_genCoeff (g : Fin 4) (a : ℕ) : sgnJ (genCoeff g a) = genCoeff g a := by
  rw [genCoeff, show sgnJ (PowerSeries.coeff a (genSer g)) =
    PowerSeries.coeff a (PowerSeries.map sgnJR (genSer g)) by rw [PowerSeries.coeff_map]; rfl,
    map_sgnJ_genSer]

theorem sgnJ_genSpan : ∀ x ∈ genSpan, sgnJ x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨g, a⟩, rfl⟩ := hx; exact sgnJ_genCoeff g a
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-- `u_j, v_j ↦ -u_j, -v_j` on the model ring. -/
def sgnM : MPoly R →ₐ[R] MPoly R := aeval fun x => -X x

theorem sgnM_ι (P : JetPoly) : sgnM R (ι R P) = ι R (sgnJ P) := by
  have h : ((sgnM R).restrictScalars ℂ).comp (ι R) = (ι R).comp sgnJ := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [sgnM, sgnJ]
  exact AlgHom.congr_fun h P

omit [Algebra ℂ R] in
theorem sgnM_C (a : R) : sgnM R (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

variable (t : ℕ → R)

theorem sgnM_mletter (l : Generator × ℕ) : sgnM R (mletter R t l) = mletter R t l := by
  obtain ⟨g, n⟩ := l
  cases g with
  | current a =>
    change sgnM R (ι R (letterSym _)) = ι R (letterSym _)
    rw [sgnM_ι, sgnJ_genSpan _ (letterSym_mem_genSpan _)]
  | sugawara =>
    change sgnM R (ι R (letterSym _) + MvPolynomial.C (t n)) = ι R (letterSym _) + _
    rw [map_add, sgnM_ι, sgnJ_genSpan _ (letterSym_mem_genSpan _), sgnM_C]

theorem sgnM_mword (w : List (Generator × ℕ)) : sgnM R (mword R t w) = mword R t w := by
  induction w with
  | nil => simp
  | cons l w ih => rw [mword_cons, map_mul, sgnM_mletter, ih]

theorem sgnM_modelDeg (r : ℕ) (d : ℤ) : ∀ Q ∈ modelDeg R t r d, sgnM R Q = Q := by
  intro Q hQ
  induction hQ using Submodule.span_induction with
  | mem Q hQ => obtain ⟨w, -, -, rfl⟩ := hQ; exact sgnM_mword R t w
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [(sgnM R).map_smul_of_tower, hx]

/-! ### The membership spaces -/

/-- `τ ↦ τ · v₀^q`. -/
def vLift (q : ℕ) : R →ₗ[ℂ] MPoly R :=
  ((LinearMap.mulRight R (X (1, 0) ^ q : MPoly R)).comp
    (Algebra.linearMap R (MPoly R))).restrictScalars ℂ

@[simp] theorem vLift_apply (q : ℕ) (τ : R) :
    vLift R q τ = MvPolynomial.C τ * X (1, 0) ^ q := by
  simp [vLift, MvPolynomial.algebraMap_eq]

/-- **The membership space**: the `τ ∈ R` with `τ · v₀^q` in the degree-`d` piece of `S_r`. -/
def vMem (r : ℕ) (d : ℤ) (q : ℕ) : Submodule ℂ R := (modelDeg R t r d).comap (vLift R q)

omit [Algebra ℂ R] in
theorem C_mul_pow_eq_zero {τ : R} {q : ℕ} (h : MvPolynomial.C τ * X (1, 0) ^ q = (0 : MPoly R)) :
    τ = 0 := by
  have := congrArg (fun P => (evV R P).coeff q) h
  simpa using this

/-- **The membership spaces vanish in odd `v₀`-degree.** -/
theorem vMem_odd {q : ℕ} (hq : Odd q) (r : ℕ) (d : ℤ) : vMem R t r d q = ⊥ := by
  rw [eq_bot_iff]
  intro τ hτ
  rw [Submodule.mem_bot]
  have h1 := sgnM_modelDeg R t r d _ hτ
  rw [vLift_apply, map_mul, map_pow, sgnM_C, sgnM, aeval_X, neg_pow, hq.neg_one_pow] at h1
  have h2 : (2 : ℂ) • (MvPolynomial.C τ * X (1, 0) ^ q : MPoly R) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h1]
    ring
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact C_mul_pow_eq_zero R h

/-! ### Singular vectors land in the membership spaces -/

variable (r : ℕ)

/-- `s ↦ τ` with `s = τ · v₀^q`. -/
def singToVMem (d : ℤ) (q : ℕ) :
    sing (mImgRho R t r) (mImgDeg R t r) d (-(q : ℂ)) →ₗ[ℂ] vMem R t r d q :=
  ((lamImg R t r q).comp (sing (mImgRho R t r) (mImgDeg R t r) d (-(q : ℂ))).subtype).codRestrict
    _ fun s => by
      obtain ⟨hsing, hsd⟩ := mem_sing_model R t s.2
      change vLift R q ((evV R ((s : modelImage R t r) : MPoly R)).coeff q) ∈ modelDeg R t r d
      rw [vLift_apply, ← msing_eq_C_mul_pow R hsing]
      exact hsd

theorem singToVMem_injective (d : ℤ) (q : ℕ) : Function.Injective (singToVMem R t r d q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  obtain ⟨hsing, -⟩ := mem_sing_model R t s.2
  have h0 : (evV R ((s : modelImage R t r) : MPoly R)).coeff q = 0 :=
    congrArg Subtype.val hs
  have := msing_eq_C_mul_pow R hsing
  rw [h0, map_zero, zero_mul] at this
  exact Subtype.ext (Subtype.ext this)

/-- **The rank half of the model socle data from rank bounds on the membership spaces.** -/
theorem model_rank_le {ι : Type*} (deg cl : ι → ℕ)
    (hmem : ∀ (d : ℤ) (N : ℕ), Module.rank ℂ (vMem R t r d (2 * N)) ≤
      Nat.card {i : ι // (deg i : ℤ) = d ∧ cl i = N})
    (d : ℤ) (c : ℂ) :
    finrank ℂ (sing (mImgRho R t r) (mImgDeg R t r) d c) ≤
      Nat.card {i : ι // (deg i : ℤ) = d ∧ c = -(2 * (cl i : ℂ))} := by
  by_cases hc : ∃ q : ℕ, c = -(q : ℂ)
  · obtain ⟨q, rfl⟩ := hc
    have hr := LinearMap.rank_le_of_injective _ (singToVMem_injective R t r d q)
    rcases Nat.even_or_odd q with ⟨N, hN⟩ | hodd
    · have hq : q = 2 * N := by omega
      subst hq
      refine finrank_le_of_rank_le (hr.trans ((hmem d N).trans ?_))
      refine le_of_eq (congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)))
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [h2]; push_cast; ring
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have : ((2 * N : ℕ) : ℂ) = ((2 * cl i : ℕ) : ℂ) := by
          push_cast at h2 ⊢; linear_combination -h2
        have := Nat.cast_injective this
        omega
    · rw [vMem_odd R t hodd r d, rank_bot] at hr
      have : finrank ℂ (sing (mImgRho R t r) (mImgDeg R t r) d (-(q : ℂ))) = 0 :=
        finrank_eq_zero_of_rank_eq_zero (le_antisymm hr bot_le)
      rw [this]
      exact Nat.zero_le _
  · push Not at hc
    have hbot : sing (mImgRho R t r) (mImgDeg R t r) d c = ⊥ := by
      rw [eq_bot_iff]
      intro s hs
      rw [Submodule.mem_bot]
      exact Subtype.ext (msing_eq_zero_of_ne R (mem_sing_model R t hs).1 hc)
    rw [hbot, finrank_bot]
    exact Nat.zero_le _

/-! ### The remaining input and the endpoints -/

/-- **The membership bound** (remaining input of the socle half): for every conformal degree `d`
and every `N`, the space of `τ ∈ R_n` with `v₀^{2N} · τ` in the degree-`d` piece of `S_{n,r}`
has dimension at most the number of socle words of size `r` with `N` letters and degree `d`.
Numerically (exact linear algebra mod `p = 1000003`) the dimension *equals* that count for
`n = 2, 3`, `r ≤ 6`, weight `≤ 10` (numerical evidence, not a proof). -/
def ModelSocleMembership (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), Module.rank ℂ (vMem (Rn n) (tn n) r d (2 * N)) ≤
    Nat.card {i : SocleIndex n r // ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N}

/-- **The model socle data from the membership bound.** -/
theorem modelSocleSpectrum_of_membership {n r : ℕ} (h : ModelSocleMembership n r) :
    ModelSocleSpectrum n r where
  rank_le := model_rank_le (Rn n) (tn n) r (fun i : SocleIndex n r => socleDegree i.2.1)
    (fun i => (i.1 : ℕ)) h
  transverse := model_transverse (Rn n) (tn n) (θn n) (θn_tn n) r

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional on `hA`,
detection `det`, and the membership bound `mem` (the model character bound is discharged). -/
theorem twoSeries_gradedUnitary_of_strictModel_membership (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (mem : ∀ r, ModelSocleMembership n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  VOA.TwoSeries.ModelChar.twoSeries_gradedUnitary_of_strictModel_det n hn hA det
    fun r => modelSocleSpectrum_of_membership (mem r)

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`** from a coinvariant family and the membership bound. -/
theorem twoSeries_gradedUnitary_of_coinv_membership (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (Λ : TwoSeriesCoinvEvalFamily n) (mem : ∀ r, ModelSocleMembership n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_coinv n hn hA Λ fun r => modelSocleSpectrum_of_membership (mem r)

end

end VOA.TwoSeries.StrictModel
