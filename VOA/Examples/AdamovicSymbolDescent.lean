/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.AdamovicSymbolWords

/-!
# The leading-symbol map from well-definedness of the Adamović word symbols

`JetLeadingSymbol r` (the `sym` input of `leeYang_gradedUnitary_of_affine_leadingSymbol`) asks for
a surjective, degree-preserving intertwiner `gr_r L_{-4/3}(sl₂) → A_r`. This file reduces it to
the single statement that the intended map is *well defined*:

* `WordSymbolDescends r` (constructed for every `r` in `AdamovicDescCyclic.lean`:
  `Desc.wordSymbolDescends`) — a linear map `σ : F_r L → ℂ[u_j, v_j]` that kills `F_{r-1} L`
  and sends the class of every length-`r` corrected word to its Adamović symbol `wordSym w`
  (`e ↦ X, f ↦ -Z, h ↦ -2Y, T ↦ -J`). Equivalently: every linear relation among length-`≤ r`
  corrected words in the simple quotient that holds modulo `F_{r-1}` is satisfied by the
  length-`r` word symbols. This is exactly the content of "the filtered Adamović realization
  induces a map on `gr`"; nothing else is assumed here.

From it, everything else is **proved**:

* `WordSymbolDescends.toJetLeadingSymbol` — intertwining with the induced nonnegative mode action
  (the commutator calculus `J_word_mem_symMod`), the conformal degree (word weights and the
  independence of the conformal grading), and **surjectivity** (`A_r` is spanned by length-`r`
  word symbols);
* `WordSymbolDescends.ofLeadingSymbol` — conversely, any leading-symbol map that sends word
  classes to their symbols gives `WordSymbolDescends`, so the hypothesis is not stronger than
  the intended input;
* `wordSymbolDescends_zero` — the case `r = 0` is proved;
* `singular_symbol_vanishes` — sanity check: the corrected-degree-two symbol of the actual
  weight-3 singular vector `sl2Singular` (rewritten with the Sugawara vector) vanishes in the
  jet ring, as well-definedness requires;
* `leeYang_gradedUnitary_of_affine_wordSymbols` — **Affine GU ⇒ Lee–Yang GU**,
  `#print axioms`-clean, conditional on `hA` (the hypothesis), `desc` (well-definedness of the
  word symbols, `r ≥ 1`), `chi` (the jet-ring character bound), `lower` (classical
  Rogers–Ramanujan).
-/

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.ConcreteHodge VOA.LeeYangTransferAssembly Sl2CosetConcrete
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR VOA.VertexOperatorAlgebra
open AffineSl2GeneralRigidity MvPolynomial

noncomputable section

/-! ### Word weights in the universal algebra -/

section Weights

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The conformal weight of a corrected letter. -/
def letterWt : Generator × ℕ → ℤ
  | (.current _, n) => n + 1
  | (.sugawara, n) => n + 2

/-- The conformal weight of a corrected word. -/
def wordWt (w : List (Generator × ℕ)) : ℤ := (w.map letterWt).sum

theorem wordWt_eq (w : List (Generator × ℕ)) : wordWt w = wordJetWt w + w.length := by
  induction w with
  | nil => simp [wordWt, wordJetWt]
  | cons l w ih =>
    obtain ⟨g, n⟩ := l
    cases g <;> simp only [wordWt, wordJetWt, List.map_cons, List.sum_cons, letterWt,
      letterJetWt, List.length_cons] at ih ⊢ <;> push_cast <;> linarith

theorem correctedWordState_mem_grading (w : List (Generator × ℕ)) :
    correctedWordState k hk w ∈ (affineSl2VOA_closed k hk).grading (wordWt w) := by
  induction w with
  | nil => simpa [wordWt] using (affineSl2VOA_closed k hk).vacuum_mem_grading_zero
  | cons l w ih =>
    obtain ⟨g, n⟩ := l
    rw [correctedWordState_cons]
    cases g with
    | current a =>
      have h := (affineSl2VOA_closed k hk).grading_mode (currentState k a)
        (currentState_mem_grading k hk a) _ ih (-(n : ℤ) - 1)
      convert h using 2
      simp only [wordWt, List.map_cons, List.sum_cons, letterWt]; ring
    | sugawara =>
      have h := (affineSl2VOA_closed k hk).grading_mode
        (affineSl2VOA_closed k hk).conformalVector
        (affineSl2VOA_closed k hk).conformalVector_mem_grading_two _ ih (-(n : ℤ) - 1)
      convert h using 2
      simp only [wordWt, List.map_cons, List.sum_cons, letterWt]; ring

/-- The span of the corrected words of length `≤ r` and weight `d`. -/
def wordSpanWt (r : ℕ) (d : ℤ) : Submodule ℂ (WakModule k) :=
  Submodule.span ℂ
    {x | ∃ w : List (Generator × ℕ), w.length ≤ r ∧ wordWt w = d ∧ correctedWordState k hk w = x}

theorem wordSpanWt_le_grading (r : ℕ) (d : ℤ) :
    wordSpanWt k hk r d ≤ (affineSl2VOA_closed k hk).grading d := by
  rw [wordSpanWt, Submodule.span_le]
  rintro _ ⟨w, -, rfl, rfl⟩
  exact correctedWordState_mem_grading k hk w

theorem wordSpanWt_le_piece (r : ℕ) (d : ℤ) :
    wordSpanWt k hk r d ≤ correctedAffineRPiece k hk r := by
  rw [wordSpanWt, Submodule.span_le]
  rintro _ ⟨w, hw, -, rfl⟩
  exact correctedWordState_mem_piece k hk w hw

theorem piece_le_iSup_wordSpanWt (r : ℕ) :
    correctedAffineRPiece k hk r ≤ ⨆ d, wordSpanWt k hk r d := by
  rw [correctedAffineRPiece, Submodule.span_le]
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem (wordWt w) (Submodule.subset_span ⟨w, hw, rfl, rfl⟩)

/-- A weight-`d` element of `F_r` is a combination of weight-`d` words of length `≤ r`. -/
theorem weightPiece_le_wordSpanWt (r : ℕ) (d : ℤ) :
    correctedAffineRWeightPiece k hk r d ≤ wordSpanWt k hk r d := by
  rintro z ⟨hz1, hz2⟩
  exact mem_of_mem_iSup_indep (affineSl2VOA_closed k hk).isInternal.submodule_iSupIndep
    (wordSpanWt_le_grading k hk r) hz2 (piece_le_iSup_wordSpanWt k hk r hz1)

theorem lowerP_le (r : ℕ) : lowerP k hk r ≤ correctedAffineRPiece k hk r := by
  cases r with
  | zero => exact bot_le
  | succ q => exact correctedAffineRPiece_mono k hk (Nat.le_succ q)

theorem word_mem_lowerP {r : ℕ} (w : List (Generator × ℕ)) (hw : w.length < r) :
    correctedWordState k hk w ∈ lowerP k hk r := by
  cases r with
  | zero => omega
  | succ q => exact correctedWordState_mem_piece k hk w (by omega)

end Weights

/-! ### The simple quotient -/

/-- The maximal ideal of `V^{-4/3}(sl₂)`. -/
abbrev Imax : Submodule ℂ (WakModule ALevel) :=
  QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)

/-- The universal corrected piece `F_r V^{-4/3}(sl₂)`. -/
abbrev UP (r : ℕ) : Submodule ℂ (WakModule ALevel) := correctedAffineRPiece ALevel aNoncritical r

theorem piece_eq_map (r : ℕ) (d : ℤ) :
    affineFlag.piece r d = (correctedAffineRWeightPiece ALevel aNoncritical r d).map Imax.mkQ :=
  rfl

/-- `F_r L = π (F_r V)`. -/
theorem aFil_eq_map (r : ℕ) : aFil r = (UP r).map Imax.mkQ := by
  apply le_antisymm
  · exact iSup_le fun d => Submodule.map_mono inf_le_left
  · rw [Submodule.map_le_iff_le_comap, UP, correctedAffineRPiece, Submodule.span_le]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem (wordWt w) ?_
    rw [piece_eq_map]
    exact Submodule.mem_map_of_mem ⟨correctedWordState_mem_piece _ _ w hw,
      correctedWordState_mem_grading _ _ w⟩

theorem mkQ_mem_aFil {r : ℕ} {z : WakModule ALevel} (hz : z ∈ UP r) : Imax.mkQ z ∈ aFil r := by
  rw [aFil_eq_map]; exact Submodule.mem_map_of_mem hz

theorem mkQ_mem_aFilLT {r : ℕ} {z : WakModule ALevel}
    (hz : z ∈ lowerP ALevel aNoncritical r) : Imax.mkQ z ∈ aFilLT r := by
  cases r with
  | zero =>
    rw [lowerP, Submodule.mem_bot] at hz
    rw [hz, map_zero]; exact Submodule.zero_mem _
  | succ q => exact mkQ_mem_aFil hz

theorem wordClass_mem_aFil {r : ℕ} (w : List (Generator × ℕ)) (hw : w.length ≤ r) :
    Imax.mkQ (correctedWordState ALevel aNoncritical w) ∈ aFil r :=
  mkQ_mem_aFil (correctedWordState_mem_piece _ _ w hw)

/-- The class of a corrected word of length `≤ r` in `F_r L`. -/
def wordClass {r : ℕ} (w : List (Generator × ℕ)) (hw : w.length ≤ r) : aFil r :=
  ⟨Imax.mkQ (correctedWordState ALevel aNoncritical w), wordClass_mem_aFil w hw⟩

/-! ### The hypothesis -/

/-- **Well-definedness of the Adamović word symbols on `gr_r L_{-4/3}(sl₂)`** (constructed for
every `r`: `Desc.wordSymbolDescends`, `AdamovicDescCyclic.lean`): a linear map on `F_r L`
killing `F_{r-1} L` and sending the class of every length-`r` corrected word to `wordSym w`
(`e ↦ X, f ↦ -Z, h ↦ -2Y, T ↦ -J`). In the notes this is the leading-symbol map
induced by the filtered Adamović realization through the simple quotient. -/
structure WordSymbolDescends (r : ℕ) where
  σ : aFil r →ₗ[ℂ] JetPoly
  lower : ∀ x : aFil r, (x : ASpace) ∈ aFilLT r → σ x = 0
  word : ∀ (w : List (Generator × ℕ)) (hw : w.length = r), σ (wordClass w hw.le) = wordSym w

namespace WordSymbolDescends

variable {r : ℕ} (D : WordSymbolDescends r)

/-- `σ` pulled back to the universal piece. -/
def σU : UP r →ₗ[ℂ] JetPoly :=
  D.σ ∘ₗ (Imax.mkQ.domRestrict (UP r)).codRestrict (aFil r) fun z => mkQ_mem_aFil z.2

theorem σU_apply (z : UP r) : D.σU z = D.σ ⟨Imax.mkQ z, mkQ_mem_aFil z.2⟩ := rfl

/-- The pairs `symMod r` lie on the graph of `σU`. -/
theorem σU_of_symMod {z : WakModule ALevel} {p : JetPoly}
    (hzp : (z, p) ∈ symMod ALevel aNoncritical r) (hz : z ∈ UP r) : D.σU ⟨z, hz⟩ = p := by
  have hle : symMod ALevel aNoncritical r ≤
      (LinearMap.graph D.σU).map ((UP r).subtype.prodMap LinearMap.id) := by
    refine sup_le ?_ ?_
    · rw [symPairs, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨(⟨_, correctedWordState_mem_piece _ _ w hw.le⟩, wordSym w), ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_graph_iff, σU_apply]
      exact (D.word w hw).symm
    · rintro ⟨y, q⟩ ⟨hy, hq⟩
      change q ∈ (⊥ : Submodule ℂ JetPoly) at hq
      rw [Submodule.mem_bot] at hq
      subst hq
      refine ⟨(⟨y, lowerP_le _ _ r hy⟩, 0), ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_graph_iff, σU_apply]
      exact (D.lower _ (mkQ_mem_aFilLT hy)).symm
  obtain ⟨⟨z', p'⟩, hg, he⟩ := hle hzp
  simp only [LinearMap.prodMap_apply, Submodule.coe_subtype, LinearMap.id_apply,
    Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [SetLike.mem_coe, LinearMap.mem_graph_iff] at hg
  exact hg.symm

theorem σU_lower {z : WakModule ALevel} (hz : z ∈ lowerP ALevel aNoncritical r) :
    D.σU ⟨z, lowerP_le _ _ r hz⟩ = 0 :=
  D.σU_of_symMod (lower_mem_symMod _ _ hz) _

/-- Span induction for properties of `σU` that are closed under linear combinations. -/
theorem σU_span_mem {S : Submodule ℂ JetPoly} {s : Set (WakModule ALevel)}
    (hs : Submodule.span ℂ s ≤ UP r)
    (h : ∀ z (hz : z ∈ s), D.σU ⟨z, hs (Submodule.subset_span hz)⟩ ∈ S) :
    ∀ z (hz : z ∈ Submodule.span ℂ s), D.σU ⟨z, hs hz⟩ ∈ S := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    rw [show (⟨0, hs (Submodule.zero_mem _)⟩ : UP r) = 0 from rfl, map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, hs (Submodule.add_mem _ hx hy)⟩ : UP r) = ⟨x, hs hx⟩ + ⟨y, hs hy⟩ from rfl,
      map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx =>
    rw [show (⟨c • x, hs (Submodule.smul_mem _ c hx)⟩ : UP r) = c • ⟨x, hs hx⟩ from rfl,
      map_smul]
    exact Submodule.smul_mem _ c ihx

/-- `σU` lands in `A_r`. -/
theorem σU_mem_jetImage (z : UP r) : D.σU z ∈ jetImage r := by
  obtain ⟨z, hz⟩ := z
  refine D.σU_span_mem (s := Set.range fun w : {w : List (Generator × ℕ) // w.length ≤ r} =>
    correctedWordState ALevel aNoncritical w.1) le_rfl ?_ z hz
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  rcases hw.lt_or_eq with hlt | heq
  · rw [D.σU_lower (word_mem_lowerP _ _ w hlt)]; exact Submodule.zero_mem _
  · rw [σU_apply]
    have h := D.word w heq
    rw [wordClass] at h
    rw [h, ← heq]
    exact wordSym_mem_jetImage w

/-- `σU` respects conformal weight. -/
theorem σU_weight (d : ℤ) {z : WakModule ALevel}
    (hz : z ∈ correctedAffineRWeightPiece ALevel aNoncritical r d) :
    D.σU ⟨z, hz.1⟩ ∈ weightedHomogeneousSubmodule ℂ jetWt (d - r) := by
  have hz' := weightPiece_le_wordSpanWt _ _ r d hz
  refine D.σU_span_mem (wordSpanWt_le_piece _ _ r d) ?_ z hz'
  rintro _ ⟨w, hw, hwt, rfl⟩
  rcases hw.lt_or_eq with hlt | heq
  · rw [D.σU_lower (word_mem_lowerP _ _ w hlt)]; exact Submodule.zero_mem _
  · rw [σU_apply]
    have h := D.word w heq
    rw [wordClass] at h
    rw [h]
    have hj : wordJetWt w = d - r := by rw [← hwt, wordWt_eq, heq]; ring
    rw [← hj]
    exact wordSym_mem_weighted w

/-- `σU` intertwines the nonnegative current modes with the jet derivations. -/
theorem σU_J (a : Fin 3) (μ : ℕ) {z : WakModule ALevel} (hz : z ∈ UP r) :
    D.σU ⟨J ALevel a μ z, correctedPiece_J_nonneg _ _ a (by positivity) hz⟩ =
      jetDer (a, μ) (D.σU ⟨z, hz⟩) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨w, hw⟩, rfl⟩ := hx
    rcases hw.lt_or_eq with hlt | heq
    · have hJ : J ALevel a μ (correctedWordState ALevel aNoncritical w) ∈
          lowerP ALevel aNoncritical r := by
        cases r with
        | zero => omega
        | succ q =>
          exact correctedAffineRPiece_mono _ _ (by omega)
            (correctedWord_J_nonneg _ _ a (by positivity) w)
      rw [D.σU_lower hJ, D.σU_lower (word_mem_lowerP _ _ w hlt), map_zero]
    · have h := J_word_mem_symMod ALevel aNoncritical a μ w
      rw [heq] at h
      rw [D.σU_of_symMod h, D.σU_of_symMod (heq ▸ word_mem_symMod _ _ w)]
  | zero =>
    simp only [map_zero]
    rw [show (⟨0, _⟩ : UP r) = 0 from rfl, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    simp only [map_add]
    rw [show (⟨J ALevel a μ x + J ALevel a μ y, _⟩ : UP r) =
        ⟨J ALevel a μ x, correctedPiece_J_nonneg _ _ a (by positivity) hx⟩ +
          ⟨J ALevel a μ y, correctedPiece_J_nonneg _ _ a (by positivity) hy⟩ from rfl,
      show (⟨x + y, _⟩ : UP r) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, map_add, map_add, ihx, ihy]
  | smul c x hx ihx =>
    simp only [map_smul]
    rw [show (⟨c • J ALevel a μ x, _⟩ : UP r) =
        c • ⟨J ALevel a μ x, correctedPiece_J_nonneg _ _ a (by positivity) hx⟩ from rfl,
      show (⟨c • x, _⟩ : UP r) = c • ⟨x, hx⟩ from rfl, map_smul, map_smul, ihx,
      Derivation.map_smul]

theorem exists_lift (x : aFil r) : ∃ (z : WakModule ALevel) (hz : z ∈ UP r),
    Imax.mkQ z = x ∧ D.σ x = D.σU ⟨z, hz⟩ := by
  have hx : (x : ASpace) ∈ (UP r).map Imax.mkQ := by rw [← aFil_eq_map]; exact x.2
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨z, hz, hzx, ?_⟩
  rw [σU_apply]
  congr 1
  exact Subtype.ext hzx.symm

theorem σ_mem_jetImage (x : aFil r) : D.σ x ∈ jetImage r := by
  obtain ⟨z, hz, -, h⟩ := D.exists_lift x
  rw [h]; exact D.σU_mem_jetImage _

/-- `σ` with codomain `A_r`. -/
def σJ : aFil r →ₗ[ℂ] jetImage r := LinearMap.codRestrict (jetImage r) D.σ D.σ_mem_jetImage

theorem grKer_le : grKer r ≤ LinearMap.ker D.σJ := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  exact D.lower x hx

/-- The induced map on `gr_r L`. -/
def g : GrA r →ₗ[ℂ] jetImage r := (grKer r).liftQ D.σJ D.grKer_le

@[simp] theorem g_mk (x : aFil r) :
    (D.g (Submodule.Quotient.mk x) : JetPoly) = D.σ x := rfl

theorem g_intertwine (kk : Fin 3 × ℕ) : D.g ∘ₗ grRho r kk = jetImgRho r kk ∘ₗ D.g := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, grRho_mk, g_mk,
    jetImgRho_coe]
  obtain ⟨z, hz, hzx, h⟩ := D.exists_lift x
  rw [h, ← D.σU_J kk.1 kk.2 hz, σU_apply]
  congr 1
  apply Subtype.ext
  change aMode kk.1 (kk.2 : ℤ) (x : ASpace) = Imax.mkQ (J ALevel kk.1 kk.2 z)
  rw [← hzx, aMode_mkQ]

theorem g_degree (d : ℤ) : ∀ m ∈ grDeg r d, D.g m ∈ jetDeg r d := by
  intro m hm
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hm
  change (y : ASpace) ∈ affineFlag.piece r d at hy
  rw [piece_eq_map] at hy
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
  change (D.g (Submodule.Quotient.mk y) : JetPoly) ∈ weightedHomogeneousSubmodule ℂ jetWt (d - r)
  rw [g_mk, show y = ⟨Imax.mkQ z, mkQ_mem_aFil hz.1⟩ from Subtype.ext hzy.symm]
  exact D.σU_weight d hz

theorem g_wordClass (w : List (Generator × ℕ)) (hw : w.length = r) :
    (D.g (Submodule.Quotient.mk (wordClass w hw.le)) : JetPoly) = wordSym w := by
  rw [g_mk, D.word w hw]

theorem g_surjective : Function.Surjective D.g := by
  intro y
  have hy : (y : JetPoly) ∈ (LinearMap.range D.g).map (jetImage r).subtype := by
    refine jetImage_le_span_wordSym r y.2 |> fun h => ?_
    refine (Submodule.span_le.mpr ?_) h
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨D.g (Submodule.Quotient.mk (wordClass w hw.le)), LinearMap.mem_range_self _ _,
      D.g_wordClass w hw⟩
  obtain ⟨m, ⟨x, rfl⟩, hm⟩ := hy
  exact ⟨x, Subtype.ext hm⟩

/-- **The leading-symbol map from well-definedness of the word symbols.** -/
def toJetLeadingSymbol : JetLeadingSymbol r where
  g := D.g
  surjective := D.g_surjective
  intertwine := D.g_intertwine
  degree := D.g_degree

theorem toJetLeadingSymbol_wordClass (w : List (Generator × ℕ)) (hw : w.length = r) :
    (D.toJetLeadingSymbol.g (Submodule.Quotient.mk (wordClass w hw.le)) : JetPoly) =
      wordSym w :=
  D.g_wordClass w hw

/-- **Converse**: a leading-symbol map sending word classes to their symbols gives
`WordSymbolDescends`. So the hypothesis is equivalent to the existence of the intended map. -/
def ofLeadingSymbol (S : JetLeadingSymbol r)
    (hS : ∀ (w : List (Generator × ℕ)) (hw : w.length = r),
      (S.g (Submodule.Quotient.mk (wordClass w hw.le)) : JetPoly) = wordSym w) :
    WordSymbolDescends r where
  σ := (jetImage r).subtype ∘ₗ S.g ∘ₗ (grKer r).mkQ
  lower x hx := by
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero (grKer r)).mpr hx, map_zero, map_zero]
  word w hw := hS w hw

end WordSymbolDescends

/-! ### Degree zero -/

/-- The degree-zero word symbols are well defined (proved). -/
def wordSymbolDescends_zero : WordSymbolDescends 0 :=
  WordSymbolDescends.ofLeadingSymbol jetLeadingSymbol_zero fun w hw => by
    rw [List.length_eq_zero_iff] at hw
    subst hw
    change ((grJetStrict_zero.f (Submodule.Quotient.mk ⟨Imax.mkQ
      (correctedWordState ALevel aNoncritical []), _⟩)) : JetPoly) = 1
    have h : (Submodule.Quotient.mk ⟨Imax.mkQ (correctedWordState ALevel aNoncritical []),
        wordClass_mem_aFil [] le_rfl⟩ : GrA 0) = grVac := rfl
    rw [h, grJetStrict_zero_f_grVac]
    rfl

/-! ### Sanity check: the singular vector -/

/-- **The singular vector has vanishing corrected-degree-two symbol.** By the Sugawara relation
`(4/3) L_{-2}|0⟩ = 2 e_{-1}f_{-1}|0⟩ - h_{-2}|0⟩ + (1/2) h_{-1}h_{-1}|0⟩` at `k = -4/3`, the
singular vector `sl2Singular = 20 e_{-3} - 12 e_{-2}h_{-1} - 6 h_{-2}e_{-1} + 36 e_{-1}e_{-1}f_{-1}
+ 9 e_{-1}h_{-1}h_{-1}` (on `|0⟩`) equals
`20 e_{-3} - 12 e_{-2}h_{-1} - 6 h_{-2}e_{-1} + 24 e_{-1}L_{-2} + 18 e_{-1}h_{-2}` (hand
computation, not formalized here). It vanishes in `L`, so well-definedness requires the
length-two part of its symbol to vanish; this is that jet-ring identity (`XJ = X'Y - XY'` at
`s = 0`). -/
theorem singular_symbol_vanishes :
    -12 • wordSym [(.current 0, 1), (.current 2, 0)]
      - 6 • wordSym [(.current 2, 1), (.current 0, 0)]
      + 24 • wordSym [(.current 0, 0), (.sugawara, 0)]
      + 18 • wordSym [(.current 0, 0), (.current 2, 1)] = (0 : JetPoly) := by
  simp only [wordSym, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    letterSym, curSer, xSer, ySer, jSer, map_neg, map_add, map_sub, PowerSeries.coeff_mul,
    PowerSeries.coeff_derivative, colSer, PowerSeries.coeff_mk]
  simp [Finset.antidiagonal_zero, Finset.Nat.antidiagonal_succ]
  ring

/-! ### The endpoint -/

/-- **Affine GU ⇒ Lee–Yang GU, with the leading-symbol maps reduced to well-definedness of the
Adamović word symbols.** `#print axioms`-clean, conditional on `hA` (the hypothesis), `desc`
(`WordSymbolDescends (r+1)`; constructed: `Desc.wordSymbolDescends`), `chi` (`JetProductBound`;
proved: `JetProduct.jetProductBound_of_lower JetFermionic.jetFermionicLower`), `lower` (classical
Rogers–Ramanujan; proved: `RRLower.leeYangRRLowerBound_holds`). -/
theorem leeYang_gradedUnitary_of_affine_wordSymbols
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (desc : ∀ r : ℕ, WordSymbolDescends (r + 1)) (chi : JetProductBound)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  VOA.KoszulResidual.leeYang_gradedUnitary_of_affine_leadingSymbol hA
    (fun r => (desc r).toJetLeadingSymbol) chi lower

end

end VOA.AdamovicSymbol
