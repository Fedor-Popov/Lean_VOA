/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictSqueeze
import VOA.Examples.TwoSeriesSpectrumModel
import VOA.Examples.AffineSl2BoundaryMainTheorems
import VOA.Examples.TwoSeriesJetRing

/-!
# Strict symbol maps `gr_r L_{k_n} ↪ S_{n,r}` for every `n`, from two named inputs

The coefficient ring of the model is `R_n = ℂ[T_j]/(jets of Tⁿ)` (`Rn n`), with `T_j ↦ tn n j`.
The model `S_{n,r}` is `modelImage (Rn n) (tn n) r`: the span of the products of `r` letters
among the jets of `u²`, `uv`, `v²` and `-(u'v - uv') + T` inside `R_n[u_j, v_j]`.

Proved here:

* `θn n` — the scaling automorphism `T_j ↦ 2^{j+1} T_j` of `R_n` (it preserves the jet ideal),
  hence the conformal pieces of `S_{n,r}` are independent (`modelDeg_iSupIndep`);
* `evR_aug_eq_zero` — **the `T`-free part of detection holds at every level** (any `k ∉ ℕ`,
  any ideal avoiding weight zero): the level-one vacuum-functional argument
  (`Desc.evalBase_eq_zero_of_mem`) applied after `T ↦ 0`.  So the remaining detection input
  concerns only the components of positive `T`-degree;
* `twoSeriesStrictModel` — **for every `n ≥ 1` and every `r`, an injective, grading-preserving,
  mode-intertwining map `gr_r L_{k_n} → S_{n,r}`**, conditional on the two inputs below;
* `twoSeriesSocleModel_of_strict` — the route-(a) package `TwoSeriesSocleModel n r` from these
  maps and the socle data of the model;
* `twoSeries_gradedUnitary_of_strictModel` — **Affine GU ⇒ GU of `M(2, 2n+3)`**,
  `#print axioms`-clean, conditional on `hA`, the two inputs and the model socle data.

The two inputs (stated, not assumed anywhere else):

* `TwoSeriesModelDetects n` — *the leading model symbol of any element of the maximal ideal of
  `V^{k_n}(sl₂)`, evaluated at the Drinfeld–Sokolov point `(u, v) = (0, 1)`, vanishes in `R_n`*.
  It is equivalent to the well-definedness of the model symbols on the simple quotient
  (`symbol_eq_zero_of_detect`, and conversely trivially); its `T`-free part is proved
  (`evR_aug_eq_zero`), and at `n = 1` it is proved outright (`twoSeriesModelDetects_one`).
  Numerical evidence (exact linear algebra mod `p = 1000003`, not a proof): every linear
  relation among sorted length-`r` word classes in `gr_r L_{k_n}` is satisfied by the model
  symbols modulo the jets of `Tⁿ`, for `n = 2`, weight `≤ 8`, and `n = 3`, weight `≤ 7`
  (both past the singular vector); with the jets of `T^{n+1}` instead the check fails.
* `TwoSeriesModelCharacter n` — *the `q^N` coefficient of the Arakawa–Dai product
  `character_eq_product n` is at most `Σ_{r ≤ N} dim S_{n,r,N}`*: a statement about one
  commutative algebra and a `q`-product only.  Proved at `n = 1`
  (`twoSeriesModelCharacter_one`, in `TwoSeriesStrictLevelOne`).
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.AdamovicSymbol
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR
open VOA.SocleDual VOA.SocleEval VOA.CyclicEval VOA.InvariantSymbol
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

/-! ### The coefficient ring `R_n`

`TPoly`, `tSer`, `jetIdealT`, `Rn`, `tn` are defined in `TwoSeriesJetRing`. -/

/-- The scaling `T_j ↦ 2^{j+1} T_j` of `ℂ[T_j]`. -/
def scaleT : TPoly →ₐ[ℂ] TPoly := aeval fun j => (2 : ℂ) ^ (j + 1) • X j

theorem map_scaleT_tSer :
    PowerSeries.map scaleT.toRingHom tSer = (2 : TPoly) • PowerSeries.rescale (2 : TPoly) tSer := by
  ext j
  simp only [tSer, PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_smul,
    PowerSeries.coeff_rescale, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, scaleT, aeval_X,
    smul_eq_mul]
  rw [MvPolynomial.smul_eq_C_mul, pow_succ]
  simp only [map_mul, map_pow, map_ofNat]
  ring_nf

theorem jetIdealT_le_comap (n : ℕ) : jetIdealT n ≤ (jetIdealT n).comap scaleT := by
  rw [jetIdealT, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  have h : scaleT (PowerSeries.coeff j (tSer ^ n)) =
      (2 : TPoly) ^ n * ((2 : TPoly) ^ j * PowerSeries.coeff j (tSer ^ n)) := by
    have := PowerSeries.coeff_map scaleT.toRingHom j (tSer ^ n)
    rw [map_pow, map_scaleT_tSer, smul_pow, ← map_pow, PowerSeries.coeff_smul,
      PowerSeries.coeff_rescale, smul_eq_mul] at this
    exact this.symm
  rw [h]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))

/-- The scaling automorphism of `R_n`. -/
def θn (n : ℕ) : Rn n →ₐ[ℂ] Rn n := Ideal.quotientMapₐ (jetIdealT n) scaleT (jetIdealT_le_comap n)

theorem θn_tn (n j : ℕ) : θn n (tn n j) = (2 : ℂ) ^ (j + 1) • tn n j := by
  simp only [θn, tn, Ideal.quotient_map_mkₐ, scaleT, aeval_X, map_smul]
  rfl

/-- **The conformal pieces of the model `S_{n,r}` are independent.** -/
theorem rn_modelDeg_iSupIndep (n r : ℕ) : iSupIndep (modelDeg (Rn n) (tn n) r) :=
  modelDeg_iSupIndep (Rn n) (θn n) (tn n) (θn_tn n) r

/-- The augmentation `T_j ↦ 0` of `R_n` (`n ≥ 1`). -/
def εn (n : ℕ) (hn : 1 ≤ n) : Rn n →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (jetIdealT n) (aeval fun _ => (0 : ℂ)) (by
    intro a ha
    have hle : jetIdealT n ≤ RingHom.ker (aeval fun _ : ℕ => (0 : ℂ)).toRingHom := by
      rw [jetIdealT, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 : PowerSeries.map (aeval fun _ : ℕ => (0 : ℂ)).toRingHom tSer = 0 := by
        ext i; simp [tSer]
      have := PowerSeries.coeff_map (aeval fun _ : ℕ => (0 : ℂ)).toRingHom j (tSer ^ n)
      rw [map_pow, h0, zero_pow (by omega), map_zero] at this
      exact this.symm
    exact hle ha)

theorem εn_tn (n : ℕ) (hn : 1 ≤ n) (j : ℕ) : εn n hn (tn n j) = 0 := by
  simp [εn, tn]

/-! ### The `T`-free part of detection, at every level -/

section Augmentation

variable {R : Type} [CommRing R] [Algebra ℂ R] {t : ℕ → R}

/-- Applying an augmentation `ε : R → ℂ` to the coefficients. -/
def πε (ε : R →ₐ[ℂ] ℂ) : MPoly R →ₐ[ℂ] JetPoly := MvPolynomial.mapAlgHom ε

theorem πε_ι (ε : R →ₐ[ℂ] ℂ) (P : JetPoly) : πε ε (ι R P) = P := by
  have h : (πε ε).comp (ι R) = AlgHom.id ℂ JetPoly :=
    MvPolynomial.algHom_ext fun x => by simp [πε, ι]
  exact AlgHom.congr_fun h P

theorem πε_mword (ε : R →ₐ[ℂ] ℂ) (hε : ∀ j, ε (t j) = 0) (w : List (Generator × ℕ)) :
    πε ε (mword R t w) = wordSym w := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [mword_cons, map_mul, ih, wordSym_cons]
    congr 1
    obtain ⟨g, n⟩ := l
    cases g with
    | current a => exact πε_ι ε _
    | sugawara =>
      change πε ε (ι R (letterSym _) + MvPolynomial.C (t n)) = _
      rw [map_add, πε_ι]
      simp [πε, hε]

theorem evalBase_πε (ε : R →ₐ[ℂ] ℂ) (Q : MPoly R) : evalBase (πε ε Q) = ε (evR R Q) := by
  have h : (evalBase.comp (πε ε)).toRingHom = (ε.comp ((evR R).restrictScalars ℂ)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [πε, evalBase, evR]
    · intro x; simp [πε, evalBase, evR, baseVal]
  exact RingHom.congr_fun h Q

theorem symModM_map_le (ε : R →ₐ[ℂ] ℂ) (hε : ∀ j, ε (t j) = 0) (k : ℂ) (hk : k + 2 ≠ 0)
    (r : ℕ) : symModM R t k hk r ≤
      (symMod k hk r).comap (LinearMap.prodMap LinearMap.id (πε ε).toLinearMap) := by
  refine sup_le ?_ ?_
  · rw [symPairsM, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    rw [πε_mword ε hε, ← hw]
    exact word_mem_symMod k hk w
  · rintro ⟨y, p⟩ ⟨hy, hp⟩
    change p ∈ (⊥ : Submodule ℂ (MPoly R)) at hp
    rw [Submodule.mem_bot] at hp
    subst hp
    rw [Submodule.mem_comap]
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, map_zero]
    exact lower_mem_symMod k hk hy

/-- **The `T`-free part of detection holds at every level `k ∉ ℕ`, for every ideal avoiding
weight zero**: the augmentation of the `R`-valued base-point evaluation vanishes. -/
theorem evR_aug_eq_zero (ε : R →ₐ[ℂ] ℂ) (hε : ∀ j, ε (t j) = 0) {k : ℂ} {hk : k + 2 ≠ 0}
    (hkN : ∀ i : ℕ, k ≠ i) {I : Submodule ℂ (WakModule k)}
    (hI : (affineSl2VOA_closed k hk).IsIdeal I) (hIN : I ≤ Desc.offZero k hk) (r : ℕ)
    {y : WakModule k} {Q : MPoly R} (hyQ : (y, Q) ∈ symModM R t k hk r) (hy : y ∈ I) :
    ε (evR R Q) = 0 := by
  rw [← evalBase_πε]
  exact Desc.evalBase_eq_zero_of_mem hkN hI hIN r (symModM_map_le ε hε k hk r hyQ) hy

end Augmentation

/-! ### The boundary levels -/

theorem level_ne_nat {n : ℕ} (hn : 1 ≤ n) (i : ℕ) :
    AffineSl2BoundarySingularFamily.level n ≠ (i : ℂ) := by
  intro h
  have h' : AffineSl2BoundarySingularFamily.level n =
      (((-2 : ℝ) + 2 / ((2 * n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    simp only [AffineSl2BoundarySingularFamily.level, AffineSl2BoundarySingularFamily.denominator]
    push_cast; ring_nf
  rw [h', show ((i : ℂ)) = ((i : ℝ) : ℂ) by push_cast; rfl] at h
  have h2 := Complex.ofReal_injective h
  have hd : (3 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    have : 3 ≤ 2 * n + 1 := by omega
    exact_mod_cast this
  have hq : 2 / ((2 * n + 1 : ℕ) : ℝ) ≤ 2 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

theorem twoSeriesLevels_kA_ne_nat {n : ℕ} (hn : 1 ≤ n) (i : ℕ) :
    (twoSeriesLevels n).kA ≠ (i : ℂ) := by
  rw [twoSeriesLevels_kA]; exact level_ne_nat hn i

theorem imaxL_le_offZero (L : CosetLevels) :
    ImaxL L ≤ Desc.offZero L.kA L.aNoncritical :=
  QuotVOA.le_iSup_ne_zero (QuotVOA.maxGradedIdeal_isGradedIdeal _)
    (QuotVOA.vacuum_not_mem_maxGradedIdeal _ (closed_vacuum_ne_zero _ _))

/-- **The `T`-free part of the detection input holds for every `n ≥ 1`.** -/
theorem twoSeries_detect_augmentation {n : ℕ} (hn : 1 ≤ n) (r : ℕ)
    {y : WakModule (twoSeriesLevels n).kA} {Q : MPoly (Rn n)}
    (hyQ : (y, Q) ∈ symModM (Rn n) (tn n) (twoSeriesLevels n).kA
      (twoSeriesLevels n).aNoncritical r)
    (hy : y ∈ ImaxL (twoSeriesLevels n)) : εn n hn (evR (Rn n) Q) = 0 :=
  evR_aug_eq_zero (εn n hn) (εn_tn n hn) (twoSeriesLevels_kA_ne_nat hn)
    (imaxL_isIdeal _) (imaxL_le_offZero _) r hyQ hy

/-! ### Sanity check: detection holds outright at `n = 1` -/

theorem sub_C_mem_span_X (p : TPoly) :
    p - MvPolynomial.C (constantCoeff p) ∈ Ideal.span (Set.range (X : ℕ → TPoly)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]; exact Ideal.add_mem _ hp hq
  | mul_X p j _ =>
    rw [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem jetIdealT_one : jetIdealT 1 = Ideal.span (Set.range (X : ℕ → TPoly)) := by
  rw [jetIdealT]
  congr 1
  ext p
  simp [tSer]

/-- At `n = 1` the augmentation is injective: `R_1 = ℂ`. -/
theorem εn_one_injective : Function.Injective (εn 1 le_rfl) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hc : constantCoeff p = 0 := by
    have h : εn 1 le_rfl (Ideal.Quotient.mk (jetIdealT 1) p) = constantCoeff p := by
      simp only [εn, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      change aeval (fun _ => (0 : ℂ)) p = constantCoeff p
      rw [show (fun _ : ℕ => (0 : ℂ)) = 0 from rfl, aeval_zero]
      rfl
    rw [← h]; exact ha
  rw [Ideal.Quotient.eq_zero_iff_mem, jetIdealT_one]
  have := sub_C_mem_span_X p
  rwa [hc, map_zero, sub_zero] at this

/-- **Sanity check**: the detection input holds outright at `n = 1` (so it is satisfiable,
and at `n = 1` the strict maps need only the model character bound). -/
theorem twoSeriesModelDetects_one :
    ModelDetects (twoSeriesLevels 1) (Rn 1) (tn 1) := by
  intro r y Q hyQ hy
  apply εn_one_injective
  rw [map_zero]
  exact twoSeries_detect_augmentation le_rfl r hyQ hy

/-! ### The two inputs at the boundary index `n` -/

/-- **Detection at the boundary index `n`** (input): the leading model symbol of any element of
the maximal ideal of `V^{k_n}(sl₂)`, evaluated at `(u, v) = (0, 1)`, vanishes in `R_n`. -/
def TwoSeriesModelDetects (n : ℕ) : Prop :=
  ModelDetects (twoSeriesLevels n) (Rn n) (tn n)

/-- **The model character bound at the boundary index `n`** (input): the `q^N` coefficient of
the boundary product is at most `Σ_{r ≤ N} dim S_{n,r,N}`. -/
def TwoSeriesModelCharacter (n : ℕ) : Prop :=
  ∀ N : ℕ, PowerSeries.coeff N (AffineSl2BoundaryCharacter.product n) ≤
    ∑ r ∈ Finset.range (N + 1), (Module.finrank ℂ (modelDeg (Rn n) (tn n) r (N : ℤ)) : ℚ)

theorem finrank_grading_twoSeries (n N : ℕ) :
    Module.finrank ℂ ((AVOA (twoSeriesLevels n)).grading (N : ℤ)) =
      Module.finrank ℂ ((AffineSl2BoundaryCharacter.vacuum n).grading (N : ℤ)) := by
  have key : ∀ (k l : ℂ) (hk : k + 2 ≠ 0) (hl : l + 2 ≠ 0), k = l →
      Module.finrank ℂ ((AffineSl2GeneralRigidity.simple k hk).grading (N : ℤ)) =
        Module.finrank ℂ ((AffineSl2GeneralRigidity.simple l hl).grading (N : ℤ)) := by
    intro k l hk hl h; subst h; rfl
  exact key _ _ _ _ (twoSeriesLevels_kA n)

theorem modelCharacterBound_of {n : ℕ} (hn : 1 ≤ n) (h : TwoSeriesModelCharacter n) :
    ModelCharacterBound (twoSeriesLevels n) (Rn n) (tn n) := by
  intro N
  have h1 := h N
  rw [← AffineSl2BoundaryCharacter.character_eq_product n hn,
    AffineSl2BoundaryCharacter.coeff_character, ← finrank_grading_twoSeries] at h1
  exact_mod_cast h1

/-! ### The strict maps and the socle-model package -/

theorem mImg_cartanCommute (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R) (r : ℕ) :
    CartanCommute (mImgRho R t r) bHPos := fun i j =>
  LinearMap.ext fun m => Subtype.ext
    (mder_comm_ι R _ _ (fun x => jetDer_h_comm (i + 1) (j + 1) (X x)) m)

theorem mImgDeg_finiteDimensional {L : CosetLevels} {R : Type} [CommRing R] [Algebra ℂ R]
    {t : ℕ → R} {r : ℕ} (S : ModelSymbol L R t r) (d : ℤ) :
    FiniteDimensional ℂ (mImgDeg R t r d) := by
  haveI := S.modelDeg_finiteDimensional d
  exact LinearEquiv.finiteDimensional
    (Submodule.comapSubtypeEquivOfLe (modelDeg_le R t r d)).symm

/-- **A strict model symbol map**: injective, grading-preserving, intertwining. -/
structure StrictModelMap (n r : ℕ) where
  f : GrA (twoSeriesLevels n) r →ₗ[ℂ] modelImage (Rn n) (tn n) r
  injective : Function.Injective f
  intertwine : ∀ k, f ∘ₗ grRho (twoSeriesLevels n) r k = mImgRho (Rn n) (tn n) r k ∘ₗ f
  degree : ∀ d, ∀ m ∈ grDeg (twoSeriesLevels n) r d, f m ∈ mImgDeg (Rn n) (tn n) r d

/-- **Strict symbol maps `gr_r L_{k_n} ↪ S_{n,r}` for every `n ≥ 1` and every `r`**, from
detection and the model character bound. -/
def twoSeriesStrictModel {n : ℕ} (hn : 1 ≤ n) (det : TwoSeriesModelDetects n)
    (chi : TwoSeriesModelCharacter n) (r : ℕ) : StrictModelMap n r where
  f := (modelSymbol det r).g
  injective := ModelSymbol.injective_of_bound _ _ _ (modelSymbol det)
    (rn_modelDeg_iSupIndep n) (modelCharacterBound_of hn chi) r
  intertwine := (modelSymbol det r).intertwine
  degree := (modelSymbol det r).degree

/-- The socle data required of the model `S_{n,r}` (input of the socle half). -/
def ModelSocleSpectrum (n r : ℕ) : Prop :=
  SocleSpectrum (mImgRho (Rn n) (tn n) r) (mImgDeg (Rn n) (tn n) r)
    (fun i : SocleIndex n r => socleDegree i.2.1) (fun i => (i.1 : ℕ))
    (modelCart (mImgRho (Rn n) (tn n) r) (mImg_cartanCommute (Rn n) (tn n) r))

/-- **The route-(a) package from the strict model maps and the model socle data.** -/
def twoSeriesSocleModel_of_strict {n : ℕ} (hn : 1 ≤ n) (det : TwoSeriesModelDetects n)
    (chi : TwoSeriesModelCharacter n) (r : ℕ) (spec : ModelSocleSpectrum n r) :
    TwoSeriesSocleModel n r where
  M := modelImage (Rn n) (tn n) r
  ρ := mImgRho (Rn n) (tn n) r
  deg := mImgDeg (Rn n) (tn n) r
  fin d := mImgDeg_finiteDimensional (modelSymbol det r) d
  comm := mImg_cartanCommute (Rn n) (tn n) r
  spectrum := spec
  f := (twoSeriesStrictModel hn det chi r).f
  injective := (twoSeriesStrictModel hn det chi r).injective
  intertwine := (twoSeriesStrictModel hn det chi r).intertwine
  degree := (twoSeriesStrictModel hn det chi r).degree

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`** for every `n ≥ 1`, `#print axioms`-clean,
conditional on `hA`, `det` (detection), `chi` (the model character bound) and `spec` (the
socle data of the model `S_{n,r}`). -/
theorem twoSeries_gradedUnitary_of_strictModel (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (chi : TwoSeriesModelCharacter n)
    (spec : ∀ r, ModelSocleSpectrum n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_socleModels n hA
    fun r => twoSeriesSocleModel_of_strict hn det chi r (spec r)

end

end VOA.TwoSeries.StrictModel
