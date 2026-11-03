/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictGrading
import VOA.Examples.TwoSeriesKoszulGr

/-!
# The model symbol map on `gr_r L_k`, at every level, from detection

For any coset level datum `L` (simple quotient `L_{kA}` of `V^{kA}(sl₂)` by its maximal graded
ideal), any coefficient ring `R` and any sequence `t : ℕ → R`, this file constructs the model
leading-symbol map

  `g : gr_r L_{kA} → modelImage R t r`,   `[|w⟩] ↦ mword R t w`  (`|w| = r`),

from a single hypothesis:

* `ModelDetects L R t` — **detection**: for every pair `(y, Q)` of the model pair module
  `symModM` with `y` in the maximal ideal, the `R`-valued base-point evaluation `evR Q`
  vanishes.  In plain words: *the leading model symbol of any element of the maximal ideal,
  evaluated at the Drinfeld–Sokolov point `(u, v) = (0, 1)`, is zero in `R`.*

From it everything is proved: the graph of the symbol relation is single-valued
(`graphM_single`, via `symbol_eq_zero_of_detect` = cyclicity over `R`), hence a linear map on
`F_r L` (`modelSymbolDescends`), which kills `F_{r-1} L`, intertwines the nonnegative modes with
the model derivations, maps conformal weight `d` into `modelDeg R t r d`, and is **onto** the
model image (`ModelSymbol`).

* `ModelSymbolDescends.toModelSymbol` — the leading-symbol package from well-definedness;
* `modelSymbolDescends` — well-definedness from detection;
* `ModelSymbol.map_grDeg` — `g(gr_{r,d}) = modelDeg r d` exactly (no grading on the model
  is used for this).

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.ConcreteHodge
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR VOA.VertexOperatorAlgebra
open AffineSl2GeneralRigidity
open VOA.AdamovicSymbol (wordWt lowerP word_mem_lowerP lowerP_le weightPiece_le_wordSpanWt
  wordSpanWt_le_piece correctedWordState_mem_grading)

noncomputable section

variable (L : CosetLevels) (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)

/-! ### The simple quotient at level `L` -/

/-- The maximal graded ideal of `V^{kA}(sl₂)`. -/
abbrev ImaxL : Submodule ℂ (WakModule L.kA) :=
  QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)

/-- The universal corrected piece `F_r V^{kA}(sl₂)`. -/
abbrev UPL (r : ℕ) : Submodule ℂ (WakModule L.kA) :=
  correctedAffineRPiece L.kA L.aNoncritical r

theorem imaxL_isIdeal : (affineSl2VOA_closed L.kA L.aNoncritical).IsIdeal (ImaxL L) :=
  QuotVOA.maxGradedIdeal_isIdeal _

theorem piece_eq_mapL (r : ℕ) (d : ℤ) :
    (affineFlag L).piece r d =
      (correctedAffineRWeightPiece L.kA L.aNoncritical r d).map (ImaxL L).mkQ :=
  rfl

/-- `F_r L = π (F_r V)`. -/
theorem aFil_eq_mapL (r : ℕ) : aFil L r = (UPL L r).map (ImaxL L).mkQ := by
  apply le_antisymm
  · exact iSup_le fun d => Submodule.map_mono inf_le_left
  · rw [Submodule.map_le_iff_le_comap, UPL, correctedAffineRPiece, Submodule.span_le]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem (wordWt w) ?_
    rw [piece_eq_mapL]
    exact Submodule.mem_map_of_mem ⟨correctedWordState_mem_piece _ _ w hw,
      correctedWordState_mem_grading _ _ w⟩

theorem mkQ_mem_aFilL {r : ℕ} {z : WakModule L.kA} (hz : z ∈ UPL L r) :
    (ImaxL L).mkQ z ∈ aFil L r := by
  rw [aFil_eq_mapL]; exact Submodule.mem_map_of_mem hz

theorem mkQ_mem_aFilLTL {r : ℕ} {z : WakModule L.kA}
    (hz : z ∈ lowerP L.kA L.aNoncritical r) : (ImaxL L).mkQ z ∈ aFilLT L r := by
  cases r with
  | zero =>
    rw [lowerP, Submodule.mem_bot] at hz
    rw [hz, map_zero]; exact Submodule.zero_mem _
  | succ q => exact mkQ_mem_aFilL L hz

/-- The class of a corrected word of length `≤ r` in `F_r L`. -/
def wordClassL {r : ℕ} (w : List (Generator × ℕ)) (hw : w.length ≤ r) : aFil L r :=
  ⟨(ImaxL L).mkQ (correctedWordState L.kA L.aNoncritical w),
    mkQ_mem_aFilL L (correctedWordState_mem_piece _ _ w hw)⟩

/-! ### The model action on the model image -/

/-- The model derivations restricted to the model image. -/
def mImgRho (r : ℕ) (kk : Fin 3 × ℕ) : Module.End ℂ (modelImage R t r) :=
  (mρ R kk).restrict fun _ hQ => mder_mem_modelImage R t kk r hQ

@[simp] theorem mImgRho_coe (r : ℕ) (kk : Fin 3 × ℕ) (m : modelImage R t r) :
    ((mImgRho R t r kk m : modelImage R t r) : MPoly R) = mder R kk m := rfl

/-- The conformal grading of the model image. -/
def mImgDeg (r : ℕ) (d : ℤ) : Submodule ℂ (modelImage R t r) :=
  (modelDeg R t r d).comap (modelImage R t r).subtype

/-! ### The well-definedness hypothesis, and what follows from it -/

/-- **Well-definedness of the model word symbols on `gr_r L`**: a linear map on `F_r L` killing
`F_{r-1} L` and sending the class of every length-`r` corrected word to its model symbol. -/
structure ModelSymbolDescends (r : ℕ) where
  σ : aFil L r →ₗ[ℂ] MPoly R
  lower : ∀ x : aFil L r, (x : ASpace L) ∈ aFilLT L r → σ x = 0
  word : ∀ (w : List (Generator × ℕ)) (hw : w.length = r), σ (wordClassL L w hw.le) = mword R t w

/-- **The model leading-symbol map**: a surjective, degree-preserving intertwiner
`gr_r L → modelImage r`. -/
structure ModelSymbol (r : ℕ) where
  g : GrA L r →ₗ[ℂ] modelImage R t r
  surjective : Function.Surjective g
  intertwine : ∀ kk, g ∘ₗ grRho L r kk = mImgRho R t r kk ∘ₗ g
  degree : ∀ d, ∀ m ∈ grDeg L r d, g m ∈ mImgDeg R t r d
  word : ∀ (w : List (Generator × ℕ)) (hw : w.length = r),
    (g (Submodule.Quotient.mk (wordClassL L w hw.le)) : MPoly R) = mword R t w

namespace ModelSymbolDescends

variable {L R t} {r : ℕ} (D : ModelSymbolDescends L R t r)

/-- `σ` pulled back to the universal piece. -/
def σU : UPL L r →ₗ[ℂ] MPoly R :=
  D.σ ∘ₗ ((ImaxL L).mkQ.domRestrict (UPL L r)).codRestrict (aFil L r)
    fun z => mkQ_mem_aFilL L z.2

theorem σU_apply (z : UPL L r) : D.σU z = D.σ ⟨(ImaxL L).mkQ z, mkQ_mem_aFilL L z.2⟩ := rfl

theorem σU_of_symModM {z : WakModule L.kA} {p : MPoly R}
    (hzp : (z, p) ∈ symModM R t L.kA L.aNoncritical r) (hz : z ∈ UPL L r) :
    D.σU ⟨z, hz⟩ = p := by
  have hle : symModM R t L.kA L.aNoncritical r ≤
      (LinearMap.graph D.σU).map ((UPL L r).subtype.prodMap LinearMap.id) := by
    refine sup_le ?_ ?_
    · rw [symPairsM, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨(⟨_, correctedWordState_mem_piece _ _ w hw.le⟩, mword R t w), ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_graph_iff, σU_apply]
      exact (D.word w hw).symm
    · rintro ⟨y, q⟩ ⟨hy, hq⟩
      change q ∈ (⊥ : Submodule ℂ (MPoly R)) at hq
      rw [Submodule.mem_bot] at hq
      subst hq
      refine ⟨(⟨y, lowerP_le _ _ r hy⟩, 0), ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_graph_iff, σU_apply]
      exact (D.lower _ (mkQ_mem_aFilLTL L hy)).symm
  obtain ⟨⟨z', p'⟩, hg, he⟩ := hle hzp
  simp only [LinearMap.prodMap_apply, Submodule.coe_subtype, LinearMap.id_apply,
    Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [SetLike.mem_coe, LinearMap.mem_graph_iff] at hg
  exact hg.symm

theorem σU_lower {z : WakModule L.kA} (hz : z ∈ lowerP L.kA L.aNoncritical r) :
    D.σU ⟨z, lowerP_le _ _ r hz⟩ = 0 :=
  D.σU_of_symModM (lower_mem_symModM R t _ _ hz) _

theorem σU_span_mem {S : Submodule ℂ (MPoly R)} {s : Set (WakModule L.kA)}
    (hs : Submodule.span ℂ s ≤ UPL L r)
    (h : ∀ z (hz : z ∈ s), D.σU ⟨z, hs (Submodule.subset_span hz)⟩ ∈ S) :
    ∀ z (hz : z ∈ Submodule.span ℂ s), D.σU ⟨z, hs hz⟩ ∈ S := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    rw [show (⟨0, hs (Submodule.zero_mem _)⟩ : UPL L r) = 0 from rfl, map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, hs (Submodule.add_mem _ hx hy)⟩ : UPL L r) = ⟨x, hs hx⟩ + ⟨y, hs hy⟩
      from rfl, map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx =>
    rw [show (⟨c • x, hs (Submodule.smul_mem _ c hx)⟩ : UPL L r) = c • ⟨x, hs hx⟩ from rfl,
      map_smul]
    exact Submodule.smul_mem _ c ihx

theorem σU_mem_modelImage (z : UPL L r) : D.σU z ∈ modelImage R t r := by
  obtain ⟨z, hz⟩ := z
  refine D.σU_span_mem (s := Set.range fun w : {w : List (Generator × ℕ) // w.length ≤ r} =>
    correctedWordState L.kA L.aNoncritical w.1) le_rfl ?_ z hz
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  rcases hw.lt_or_eq with hlt | heq
  · rw [D.σU_lower (word_mem_lowerP _ _ w hlt)]; exact Submodule.zero_mem _
  · rw [σU_apply]
    have h := D.word w heq
    rw [wordClassL] at h
    rw [h, ← heq]
    exact mword_mem_modelImage R t w

theorem σU_weight (d : ℤ) {z : WakModule L.kA}
    (hz : z ∈ correctedAffineRWeightPiece L.kA L.aNoncritical r d) :
    D.σU ⟨z, hz.1⟩ ∈ modelDeg R t r d := by
  have hz' := weightPiece_le_wordSpanWt _ _ r d hz
  refine D.σU_span_mem (wordSpanWt_le_piece _ _ r d) ?_ z hz'
  rintro _ ⟨w, hw, hwt, rfl⟩
  rcases hw.lt_or_eq with hlt | heq
  · rw [D.σU_lower (word_mem_lowerP _ _ w hlt)]; exact Submodule.zero_mem _
  · rw [σU_apply]
    have h := D.word w heq
    rw [wordClassL] at h
    rw [h, ← heq, ← hwt]
    exact mword_mem_modelDeg R t w

theorem σU_J (a : Fin 3) (μ : ℕ) {z : WakModule L.kA} (hz : z ∈ UPL L r) :
    D.σU ⟨J L.kA a μ z, correctedPiece_J_nonneg _ _ a (by positivity) hz⟩ =
      mder R (a, μ) (D.σU ⟨z, hz⟩) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨w, hw⟩, rfl⟩ := hx
    rcases hw.lt_or_eq with hlt | heq
    · have hJ : J L.kA a μ (correctedWordState L.kA L.aNoncritical w) ∈
          lowerP L.kA L.aNoncritical r := by
        cases r with
        | zero => omega
        | succ q =>
          exact correctedAffineRPiece_mono _ _ (by omega)
            (correctedWord_J_nonneg _ _ a (by positivity) w)
      rw [D.σU_lower hJ, D.σU_lower (word_mem_lowerP _ _ w hlt), map_zero]
    · have h := J_word_mem_symModM R t L.kA L.aNoncritical a μ w
      rw [heq] at h
      rw [D.σU_of_symModM h, D.σU_of_symModM (heq ▸ word_mem_symModM R t _ _ w)]
  | zero =>
    simp only [map_zero]
    rw [show (⟨0, _⟩ : UPL L r) = 0 from rfl, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    simp only [map_add]
    rw [show (⟨J L.kA a μ x + J L.kA a μ y, _⟩ : UPL L r) =
        ⟨J L.kA a μ x, correctedPiece_J_nonneg _ _ a (by positivity) hx⟩ +
          ⟨J L.kA a μ y, correctedPiece_J_nonneg _ _ a (by positivity) hy⟩ from rfl,
      show (⟨x + y, _⟩ : UPL L r) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, map_add, map_add,
      ihx, ihy]
  | smul c x hx ihx =>
    simp only [map_smul]
    rw [show (⟨c • J L.kA a μ x, _⟩ : UPL L r) =
        c • ⟨J L.kA a μ x, correctedPiece_J_nonneg _ _ a (by positivity) hx⟩ from rfl,
      show (⟨c • x, _⟩ : UPL L r) = c • ⟨x, hx⟩ from rfl, map_smul, map_smul, ihx]
    exact ((mρ R (a, μ)).map_smul c _).symm

theorem exists_lift (x : aFil L r) : ∃ (z : WakModule L.kA) (hz : z ∈ UPL L r),
    (ImaxL L).mkQ z = x ∧ D.σ x = D.σU ⟨z, hz⟩ := by
  have hx : (x : ASpace L) ∈ (UPL L r).map (ImaxL L).mkQ := by
    rw [← aFil_eq_mapL]; exact x.2
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨z, hz, hzx, ?_⟩
  rw [σU_apply]
  congr 1
  exact Subtype.ext hzx.symm

theorem σ_mem_modelImage (x : aFil L r) : D.σ x ∈ modelImage R t r := by
  obtain ⟨z, hz, -, h⟩ := D.exists_lift x
  rw [h]; exact D.σU_mem_modelImage _

/-- `σ` with codomain the model image. -/
def σM : aFil L r →ₗ[ℂ] modelImage R t r :=
  LinearMap.codRestrict (modelImage R t r) D.σ D.σ_mem_modelImage

theorem grKer_le : grKer L r ≤ LinearMap.ker D.σM := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  exact D.lower x hx

/-- The induced map on `gr_r L`. -/
def g : GrA L r →ₗ[ℂ] modelImage R t r := (grKer L r).liftQ D.σM D.grKer_le

@[simp] theorem g_mk (x : aFil L r) :
    (D.g (Submodule.Quotient.mk x) : MPoly R) = D.σ x := rfl

theorem g_intertwine (kk : Fin 3 × ℕ) : D.g ∘ₗ grRho L r kk = mImgRho R t r kk ∘ₗ D.g := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, grRho_mk, g_mk,
    mImgRho_coe]
  obtain ⟨z, hz, hzx, h⟩ := D.exists_lift x
  rw [h, ← D.σU_J kk.1 kk.2 hz, σU_apply]
  congr 1
  apply Subtype.ext
  change aMode L kk.1 (kk.2 : ℤ) (x : ASpace L) = (ImaxL L).mkQ (J L.kA kk.1 kk.2 z)
  rw [← hzx, aMode_mkQ]

theorem g_degree (d : ℤ) : ∀ m ∈ grDeg L r d, D.g m ∈ mImgDeg R t r d := by
  intro m hm
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hm
  change (y : ASpace L) ∈ (affineFlag L).piece r d at hy
  rw [piece_eq_mapL] at hy
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
  change (D.g (Submodule.Quotient.mk y) : MPoly R) ∈ modelDeg R t r d
  rw [g_mk, show y = ⟨(ImaxL L).mkQ z, mkQ_mem_aFilL L hz.1⟩ from Subtype.ext hzy.symm]
  exact D.σU_weight d hz

theorem g_wordClass (w : List (Generator × ℕ)) (hw : w.length = r) :
    (D.g (Submodule.Quotient.mk (wordClassL L w hw.le)) : MPoly R) = mword R t w := by
  rw [g_mk, D.word w hw]

theorem g_surjective : Function.Surjective D.g := by
  intro y
  have hy : (y : MPoly R) ∈ (LinearMap.range D.g).map (modelImage R t r).subtype := by
    refine (Submodule.span_le.mpr ?_) y.2
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨D.g (Submodule.Quotient.mk (wordClassL L w hw.le)), LinearMap.mem_range_self _ _,
      D.g_wordClass w hw⟩
  obtain ⟨m, ⟨x, rfl⟩, hm⟩ := hy
  exact ⟨x, Subtype.ext hm⟩

/-- **The model leading-symbol map from well-definedness of the model word symbols.** -/
def toModelSymbol : ModelSymbol L R t r where
  g := D.g
  surjective := D.g_surjective
  intertwine := D.g_intertwine
  degree := D.g_degree
  word := D.g_wordClass

end ModelSymbolDescends

/-! ### Every graded piece of the model is hit exactly -/

namespace ModelSymbol

variable {L R t} {r : ℕ} (S : ModelSymbol L R t r)

/-- A word class of length `r` and weight `d` lies in `gr_{r,d}`. -/
theorem wordClass_mem_grDeg (w : List (Generator × ℕ)) (hw : w.length = r) :
    (Submodule.Quotient.mk (wordClassL L w hw.le) : GrA L r) ∈ grDeg L r (wordWt w) := by
  refine Submodule.mem_map.mpr ⟨wordClassL L w hw.le, ?_, rfl⟩
  change (ImaxL L).mkQ (correctedWordState L.kA L.aNoncritical w) ∈ (affineFlag L).piece r _
  rw [piece_eq_mapL]
  exact Submodule.mem_map_of_mem ⟨correctedWordState_mem_piece _ _ w hw.le,
    correctedWordState_mem_grading _ _ w⟩

end ModelSymbol

/-! ### Well-definedness from detection -/

/-- **Detection at level `L`** (the input): for every `r`, every pair of the model pair module
whose first component lies in the maximal ideal has vanishing `R`-valued base-point
evaluation. -/
def ModelDetects : Prop :=
  ∀ r, Detects R t L.kA L.aNoncritical (ImaxL L) r

variable {L R t}

/-- The symbol relation pushed to the simple quotient. -/
def graphM (r : ℕ) : Submodule ℂ (ASpace L × MPoly R) :=
  (symModM R t L.kA L.aNoncritical r).map (LinearMap.prodMap (ImaxL L).mkQ LinearMap.id)

theorem graphM_single (hdet : ModelDetects L R t) (r : ℕ) :
    ∀ x : ASpace L × MPoly R, x ∈ graphM (L := L) (t := t) r → x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨⟨y, Q⟩, hyQ, rfl⟩ h0
  simp only [LinearMap.prodMap_apply, LinearMap.id_apply] at h0 ⊢
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  exact symbol_eq_zero_of_detect R t L.kA L.aNoncritical (imaxL_isIdeal L) r (hdet r) hyQ h0

theorem aFil_le_domainM (r : ℕ) :
    aFil L r ≤ (graphM (L := L) (t := t) r).map (LinearMap.fst ℂ _ _) := by
  rw [aFil_eq_mapL, UPL, correctedAffineRPiece, Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  rcases hw.lt_or_eq with hlt | heq
  · refine ⟨((ImaxL L).mkQ (correctedWordState L.kA L.aNoncritical w), 0),
      ⟨(correctedWordState L.kA L.aNoncritical w, 0), lower_mem_symModM R t _ _
        (word_mem_lowerP _ _ w hlt), rfl⟩, rfl⟩
  · refine ⟨((ImaxL L).mkQ (correctedWordState L.kA L.aNoncritical w), mword R t w),
      ⟨(correctedWordState L.kA L.aNoncritical w, mword R t w), ?_, rfl⟩, rfl⟩
    have h := word_mem_symModM R t L.kA L.aNoncritical w
    rwa [heq] at h

theorem graphM_apply_eq (hdet : ModelDetects L R t) (r : ℕ) {x : ASpace L}
    (hx : x ∈ (graphM (L := L) (t := t) r).map (LinearMap.fst ℂ _ _))
    {Q : MPoly R} (hxQ : (x, Q) ∈ graphM (L := L) (t := t) r) :
    (graphM (L := L) (t := t) r).toLinearPMap ⟨x, hx⟩ = Q := by
  have h1 := Submodule.mem_graph_toLinearPMap (graphM_single hdet r) ⟨x, hx⟩
  have h2 := sub_mem h1 hxQ
  have h3 := graphM_single hdet r _ h2 (by simp)
  simpa [sub_eq_zero] using h3

/-- **Well-definedness of the model word symbols from detection**, in every degree `r`. -/
def modelSymbolDescends (hdet : ModelDetects L R t) (r : ℕ) : ModelSymbolDescends L R t r where
  σ := (graphM (L := L) (t := t) r).toLinearPMap.toFun ∘ₗ
    Submodule.inclusion (aFil_le_domainM r)
  lower x hx := by
    change (graphM (L := L) (t := t) r).toLinearPMap ⟨(x : ASpace L), aFil_le_domainM r x.2⟩ = 0
    apply graphM_apply_eq hdet
    cases r with
    | zero =>
      change (x : ASpace L) ∈ (⊥ : Submodule ℂ (ASpace L)) at hx
      rw [Submodule.mem_bot] at hx
      rw [hx]; exact Submodule.zero_mem _
    | succ q =>
      change (x : ASpace L) ∈ aFil L q at hx
      rw [aFil_eq_mapL] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      refine ⟨(z, 0), lower_mem_symModM R t _ _ hz, ?_⟩
      simp [hzx]
  word w hw := by
    change (graphM (L := L) (t := t) r).toLinearPMap
      ⟨_, aFil_le_domainM r (wordClassL L w hw.le).2⟩ = mword R t w
    apply graphM_apply_eq hdet
    refine ⟨(correctedWordState L.kA L.aNoncritical w, mword R t w), ?_, rfl⟩
    have h := word_mem_symModM R t L.kA L.aNoncritical w
    rwa [hw] at h

/-- **The model leading-symbol maps, in every degree, from detection.** -/
def modelSymbol (hdet : ModelDetects L R t) (r : ℕ) : ModelSymbol L R t r :=
  (modelSymbolDescends hdet r).toModelSymbol

end

end VOA.TwoSeries.StrictModel
