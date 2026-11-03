/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelJetCyclic

/-!
# Strictness from a surjective leading-symbol map and a character bound

`GrJetStrict r` asks for an *injective* degree-preserving intertwiner `gr_r L_{-4/3}(sl₂) → A_r`.
Injectivity is obtained by the
**kernel-zero character squeeze**: the filtered Adamović leading-symbol map `g : gr_r → A_r` is
surjective, and at fixed conformal weight `N` the sum over corrected degrees of `dim gr_{r,N}` is
`dim L_N`, which equals the sum of `dim A_{r,N}` by the character identity. Here that argument is
formalized for the actual corrected filtration.

* `JetLeadingSymbol r` — a **surjective** degree-preserving intertwiner `GrA r → jetImage r`
  (the filtered Adamović leading-symbol map; an input here, constructed for every `r` from
  `AdamovicSymbol.Desc.wordSymbolDescends` via `WordSymbolDescends.toJetLeadingSymbol`);
* `JetCharacterBound` — `dim L_N ≤ Σ_{r ≤ N} dim A_{r,N}` for every conformal weight `N`
  (the ordinary-character identity of the polynomial image; an input here, proved via
  `jetCharacterBound_of_product` and the proved `JetProductBound`);
* `sum_finrank_grDeg` — **telescoping**: `Σ_{r ≤ R} dim gr_{r,d} = dim F_R L_d` for the actual
  corrected filtration (proved);
* `JetLeadingSymbol.injective` — **kernel zero**: with the character bound, every leading-symbol
  map is injective, given leading-symbol maps in all degrees (proved);
* `grJetStrict_of_leadingSymbol` — strictness from the two inputs;
* `jetLeadingSymbol_zero` — the degree-zero leading-symbol map exists (proved), so only
  `r ≥ 1` is assumed.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.SymbolModel

open MvPolynomial VOA.LeeYangTransferAssembly Sl2CosetConcrete
open scoped BigOperators

noncomputable section

/-! ### Generic graded linear algebra -/

section Generic

variable {ι : Type*} {M N : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N]

/-- If `P e ≤ J e` with `J` independent, the `d`-component of an element of `⨆ P` that lies
in `J d` lies in `P d`. -/
theorem mem_of_mem_iSup_indep {J P : ι → Submodule ℂ N} (hJ : iSupIndep J)
    (hPJ : ∀ e, P e ≤ J e) {d : ι} {y : N} (hy : y ∈ J d) (hy' : y ∈ ⨆ e, P e) : y ∈ P d := by
  rw [iSup_split_single P d] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy'
  have hb' : b ∈ ⨆ (e) (_ : e ≠ d), J e :=
    (iSup_mono fun e => iSup_mono fun _ => hPJ e) hb
  have hbd : b ∈ J d := by
    have := sub_mem hy (hPJ d ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := (Submodule.disjoint_def.mp (hJ d)) b hbd hb'
  rw [hb0, add_zero]; exact ha

/-- A map respecting gradings, injective on each graded piece of a source exhausted by its
pieces, into a target with independent pieces, is injective. -/
theorem injective_of_graded {G : ι → Submodule ℂ M} {J : ι → Submodule ℂ N} (hJ : iSupIndep J)
    (hG : ⨆ e, G e = ⊤) (g : M →ₗ[ℂ] N) (hgJ : ∀ e, ∀ x ∈ G e, g x ∈ J e)
    (hinj : ∀ e, ∀ x ∈ G e, g x = 0 → x = 0) : Function.Injective g := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  have hxG : x ∈ ⨆ e, G e := by rw [hG]; exact Submodule.mem_top
  obtain ⟨f, rfl⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp G x).mp hxG
  let R : ∀ e, G e →ₗ[ℂ] J e := fun e => g.restrict (hgJ e)
  have hcomm : g ∘ₗ DFinsupp.lsum ℕ (fun e => (G e).subtype) =
      DFinsupp.lsum ℕ (fun e => (J e).subtype) ∘ₗ DFinsupp.mapRange.linearMap R := by
    refine DFinsupp.lhom_ext' fun e => LinearMap.ext fun v => ?_
    simp [R]
  have h1 : DFinsupp.lsum ℕ (fun e => (J e).subtype) (DFinsupp.mapRange.linearMap R f) =
      DFinsupp.lsum ℕ (fun e => (J e).subtype) 0 := by
    rw [map_zero, ← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply, hx]
  have h2 := hJ.dfinsupp_lsum_injective h1
  have hf : f = 0 := by
    ext e
    have h3 := DFunLike.congr_fun h2 e
    simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, DFinsupp.coe_zero,
      Pi.zero_apply] at h3
    have h4 : g (f e) = 0 := congrArg Subtype.val h3
    simpa using hinj e (f e) (f e).2 h4
  rw [hf, map_zero]

end Generic

/-! ### Independence of the two gradings -/

/-- The conformal weight spaces of `L_{-4/3}(sl₂)` are independent (`L₀`-eigenspaces). -/
theorem aGrading_iSupIndep : iSupIndep AVOA.grading := by
  have h := (Module.End.eigenspaces_iSupIndep
    (mode (AVOA.Y AVOA.conformalVector) 1)).comp (f := fun n : ℤ => (n : ℂ))
    (fun a b h => Int.cast_injective h)
  refine h.mono fun n x hx => ?_
  rw [Function.comp_apply, Module.End.mem_eigenspace_iff]
  exact AVOA.L0_grading x hx

/-- The jet-index weight pieces of the jet ring, reindexed by conformal weight `e ↦ e - r`. -/
def jetWtPiece (r : ℕ) (e : ℤ) : Submodule ℂ JetPoly :=
  weightedHomogeneousSubmodule ℂ jetWt (e - r)

theorem jetWtPiece_iSupIndep (r : ℕ) : iSupIndep (jetWtPiece r) := by
  classical
  have h : iSupIndep (weightedHomogeneousSubmodule ℂ jetWt) :=
    (weightedDecomposition ℂ jetWt).isInternal.submodule_iSupIndep
  exact h.comp (f := fun e : ℤ => e - r) (fun a b h => by simpa using h)

/-! ### The corrected filtration at fixed weight -/

/-- A state of weight `d` in `F_q` (all weights) lies in `F_q L_d`. -/
theorem mem_piece_of_mem_aFil {q : ℕ} {d : ℤ} {x : ASpace} (hx : x ∈ AVOA.grading d)
    (hq : x ∈ aFil q) : x ∈ affineFlag.piece q d :=
  mem_of_mem_iSup_indep aGrading_iSupIndep (fun m => affineFlag.le_grading q m) hx hq

/-- `F_{r-1} L_d`, with `F_{-1} = 0`. -/
def pieceLT : ℕ → ℤ → Submodule ℂ ASpace
  | 0, _ => ⊥
  | q + 1, d => affineFlag.piece q d

theorem pieceLT_le (r : ℕ) (d : ℤ) : pieceLT r d ≤ affineFlag.piece r d := by
  cases r with
  | zero => exact bot_le
  | succ q => exact affineFlag.mono d (Nat.le_succ q)

theorem piece_le_aFil (r : ℕ) (d : ℤ) : affineFlag.piece r d ≤ aFil r :=
  le_iSup (fun m => affineFlag.piece r m) d

/-- The class map `F_r L_d → gr_r`. -/
def pieceToGr (r : ℕ) (d : ℤ) : affineFlag.piece r d →ₗ[ℂ] GrA r :=
  (grKer r).mkQ ∘ₗ Submodule.inclusion (piece_le_aFil r d)

theorem range_pieceToGr (r : ℕ) (d : ℤ) : LinearMap.range (pieceToGr r d) = grDeg r d := by
  rw [pieceToGr, LinearMap.range_comp, Submodule.range_inclusion, grDeg]

theorem mem_ker_pieceToGr (r : ℕ) (d : ℤ) (x : affineFlag.piece r d) :
    x ∈ LinearMap.ker (pieceToGr r d) ↔ (x : ASpace) ∈ pieceLT r d := by
  rw [LinearMap.mem_ker, pieceToGr, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change (x : ASpace) ∈ aFilLT r ↔ _
  have hxd : (x : ASpace) ∈ AVOA.grading d := affineFlag.le_grading r d x.2
  cases r with
  | zero => rfl
  | succ q =>
    exact ⟨fun h => mem_piece_of_mem_aFil hxd h, fun h => piece_le_aFil q d h⟩

theorem ker_pieceToGr (r : ℕ) (d : ℤ) :
    LinearMap.ker (pieceToGr r d) = (pieceLT r d).comap (affineFlag.piece r d).subtype := by
  ext x; rw [mem_ker_pieceToGr]; rfl

instance piece_finiteDimensional (r : ℕ) (d : ℤ) :
    FiniteDimensional ℂ (affineFlag.piece r d) :=
  haveI := AVOA.finrank d
  Submodule.finiteDimensional_of_le (affineFlag.le_grading r d)

instance pieceLT_finiteDimensional (r : ℕ) (d : ℤ) : FiniteDimensional ℂ (pieceLT r d) :=
  Submodule.finiteDimensional_of_le (pieceLT_le r d)

instance grDeg_finiteDimensional (r : ℕ) (d : ℤ) : FiniteDimensional ℂ (grDeg r d) := by
  rw [← range_pieceToGr]; infer_instance

/-- `dim gr_{r,d} + dim F_{r-1} L_d = dim F_r L_d`. -/
theorem finrank_grDeg_add (r : ℕ) (d : ℤ) :
    Module.finrank ℂ (grDeg r d) + Module.finrank ℂ (pieceLT r d) =
      Module.finrank ℂ (affineFlag.piece r d) := by
  have h := LinearMap.finrank_range_add_finrank_ker (pieceToGr r d)
  rw [range_pieceToGr, ker_pieceToGr] at h
  rw [← h, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (pieceLT_le r d))]

/-- **Telescoping**: `Σ_{r ≤ R} dim gr_{r,d} = dim F_R L_d`. -/
theorem sum_finrank_grDeg (R : ℕ) (d : ℤ) :
    ∑ r ∈ Finset.range (R + 1), Module.finrank ℂ (grDeg r d) =
      Module.finrank ℂ (affineFlag.piece R d) := by
  induction R with
  | zero =>
    have h := finrank_grDeg_add 0 d
    rw [show pieceLT 0 d = ⊥ from rfl, finrank_bot ℂ ASpace, add_zero] at h
    simpa using h
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, add_comm, ← finrank_grDeg_add (R + 1) d]
    rfl

/-- Some corrected degree exhausts the weight space. -/
theorem exists_piece_eq_grading (d : ℤ) : ∃ R : ℕ, affineFlag.piece R d = AVOA.grading d := by
  haveI := AVOA.finrank d
  have hfg : (AVOA.grading d).FG := Module.Finite.iff_fg.mp inferInstance
  have hc := (Submodule.fg_iff_compact _).mp hfg
  have hdir : DirectedOn (· ≤ ·) (Set.range fun p : ℕ => affineFlag.piece p d) :=
    (affineFlag.directed d).directedOn_range
  obtain ⟨_, ⟨R, rfl⟩, hR⟩ :=
    (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).mp hc
      (Set.range fun p : ℕ => affineFlag.piece p d) (Set.range_nonempty _) hdir
      (by rw [sSup_range, affineFlag.exhaustive d])
  exact ⟨R, le_antisymm (affineFlag.le_grading R d) hR⟩

/-- The whole of `gr_r` is spanned by its conformal pieces. -/
theorem iSup_grDeg (r : ℕ) : ⨆ d, grDeg r d = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact Submodule.iSup_induction' (fun m : ℤ => affineFlag.piece r m)
    (motive := fun z hz => Submodule.Quotient.mk (p := grKer r) (⟨z, hz⟩ : aFil r) ∈
      ⨆ d, grDeg r d)
    (fun d z hz => Submodule.mem_iSup_of_mem d (Submodule.mem_map.mpr ⟨_, hz, rfl⟩))
    (by dsimp only
        rw [show (⟨0, _⟩ : aFil r) = 0 from rfl, Submodule.Quotient.mk_zero]
        exact Submodule.zero_mem _)
    (fun a b ha hb hha hhb => by
      dsimp only at hha hhb ⊢
      rw [show (⟨a + b, _⟩ : aFil r) = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, Submodule.Quotient.mk_add]
      exact add_mem hha hhb) hy

/-! ### The two inputs -/

/-- **The leading-symbol map** (an input here): a *surjective*, degree-preserving intertwiner
from the actual `gr_r L_{-4/3}(sl₂)` onto the polynomial image `A_r`. In the notes this is the
filtered Adamović leading-symbol map `e ↦ X, f ↦ -Z, h ↦ -2Y, T ↦ -J`
(the starting map of the squeeze).
Constructed for every `r`: `(AdamovicSymbol.Desc.wordSymbolDescends r).toJetLeadingSymbol`
(`AdamovicDescCyclic.lean`, `AdamovicSymbolDescent.lean`). -/
structure JetLeadingSymbol (r : ℕ) where
  g : GrA r →ₗ[ℂ] jetImage r
  surjective : Function.Surjective g
  intertwine : ∀ k, g ∘ₗ grRho r k = jetImgRho r k ∘ₗ g
  degree : ∀ d, ∀ m ∈ grDeg r d, g m ∈ jetDeg r d

/-- **The character bound** (an input here): at every conformal weight `N`,
`dim L_{-4/3}(sl₂)_N ≤ Σ_{r ≤ N} dim A_{r,N}`. This is one inequality of the ordinary-character
identity `ch L = ch A`. Proved:
`jetCharacterBound_of_product` (`JetStrictEndpoint.lean`) applied to the proved
`JetProductBound` (`JetProduct.jetProductBound_of_lower JetFermionic.jetFermionicLower`). -/
def JetCharacterBound : Prop :=
  ∀ N : ℕ, Module.finrank ℂ (AVOA.grading (N : ℤ)) ≤
    ∑ r ∈ Finset.range (N + 1), Module.finrank ℂ (jetDeg r (N : ℤ))

/-! ### Kernel zero -/

theorem jetDeg_coe_mem {r : ℕ} {d : ℤ} {y : jetImage r} (hy : y ∈ jetDeg r d) :
    (y : JetPoly) ∈ jetWtPiece r d := hy

namespace JetLeadingSymbol

variable {r : ℕ} (S : JetLeadingSymbol r)

/-- The symbol map composed into the jet ring. -/
def g' : GrA r →ₗ[ℂ] JetPoly := (jetImage r).subtype ∘ₗ S.g

theorem g'_mem (d : ℤ) : ∀ x ∈ grDeg r d, S.g' x ∈ jetWtPiece r d :=
  fun x hx => jetDeg_coe_mem (S.degree d x hx)

/-- The graded pieces are hit: `A_{r,d} ⊆ g(gr_{r,d})`. -/
theorem jetDeg_le_map (d : ℤ) : jetDeg r d ≤ (grDeg r d).map S.g := by
  intro y hy
  obtain ⟨x, rfl⟩ := S.surjective y
  have hx : x ∈ ⨆ e, grDeg r e := by rw [iSup_grDeg]; exact Submodule.mem_top
  have hx' : S.g' x ∈ ⨆ e, (grDeg r e).map S.g' := by
    rw [← Submodule.map_iSup]; exact Submodule.mem_map_of_mem hx
  have h := mem_of_mem_iSup_indep (jetWtPiece_iSupIndep r)
    (P := fun e => (grDeg r e).map S.g')
    (fun e => Submodule.map_le_iff_le_comap.mpr fun z hz => S.g'_mem e z hz)
    (jetDeg_coe_mem hy) hx'
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp h
  exact Submodule.mem_map.mpr ⟨z, hz, Subtype.ext hzx⟩

theorem map_grDeg (d : ℤ) : (grDeg r d).map S.g = jetDeg r d :=
  le_antisymm (Submodule.map_le_iff_le_comap.mpr fun x hx => S.degree d x hx) (S.jetDeg_le_map d)

theorem jetDeg_finiteDimensional (S : JetLeadingSymbol r) (d : ℤ) :
    FiniteDimensional ℂ (jetDeg r d) := by
  rw [← S.map_grDeg d]; infer_instance

theorem finrank_jetDeg_le (S : JetLeadingSymbol r) (d : ℤ) :
    Module.finrank ℂ (jetDeg r d) ≤ Module.finrank ℂ (grDeg r d) := by
  rw [← S.map_grDeg d]; exact Submodule.finrank_map_le _ _

/-- The restriction `gr_{r,d} → A_{r,d}`. -/
def restr (d : ℤ) : grDeg r d →ₗ[ℂ] jetDeg r d := S.g.restrict (S.degree d)

theorem restr_surjective (d : ℤ) : Function.Surjective (S.restr d) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (S.jetDeg_le_map d hy)
  exact ⟨⟨x, hx⟩, rfl⟩

end JetLeadingSymbol

/-- **The dimension squeeze**: with leading-symbol maps in all degrees and the character
bound, `dim gr_{r,d} = dim A_{r,d}` for all `r, d`. -/
theorem finrank_grDeg_eq (S : ∀ r, JetLeadingSymbol r) (hchi : JetCharacterBound)
    (r : ℕ) (d : ℤ) : Module.finrank ℂ (grDeg r d) = Module.finrank ℂ (jetDeg r d) := by
  obtain ⟨R, hR⟩ := exists_piece_eq_grading d
  rcases lt_or_ge d 0 with hd | hd
  · -- negative weight: everything vanishes
    have h0 : affineFlag.piece r d = ⊥ := by
      rw [eq_bot_iff, ← AVOA.positivity d hd]; exact affineFlag.le_grading r d
    have hg : Module.finrank ℂ (grDeg r d) = 0 := by
      have h := finrank_grDeg_add r d
      rw [h0, finrank_bot ℂ ASpace] at h
      omega
    have := (S r).finrank_jetDeg_le d
    omega
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    set T := max (max R N) r with hT
    have hRT : R ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
    have hNT : N ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
    have hrT : r ≤ T := le_max_right _ _
    have hpT : affineFlag.piece T (N : ℤ) = AVOA.grading (N : ℤ) :=
      le_antisymm (affineFlag.le_grading _ _) (hR ▸ affineFlag.mono _ hRT)
    have hsumG := sum_finrank_grDeg T (N : ℤ)
    rw [hpT] at hsumG
    have hle : ∀ i ∈ Finset.range (T + 1),
        Module.finrank ℂ (jetDeg i (N : ℤ)) ≤ Module.finrank ℂ (grDeg i (N : ℤ)) :=
      fun i _ => (S i).finrank_jetDeg_le _
    have hsub : Finset.range (N + 1) ⊆ Finset.range (T + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have hA : Module.finrank ℂ (AVOA.grading (N : ℤ)) ≤
        ∑ i ∈ Finset.range (T + 1), Module.finrank ℂ (jetDeg i (N : ℤ)) :=
      (hchi N).trans (Finset.sum_le_sum_of_subset hsub)
    have heq : ∑ i ∈ Finset.range (T + 1), Module.finrank ℂ (jetDeg i (N : ℤ)) =
        ∑ i ∈ Finset.range (T + 1), Module.finrank ℂ (grDeg i (N : ℤ)) :=
      le_antisymm (Finset.sum_le_sum hle) (hsumG ▸ hA)
    exact ((Finset.sum_eq_sum_iff_of_le hle).mp heq r (Finset.mem_range.mpr (by omega))).symm

/-- **Kernel zero**: every leading-symbol map is injective, given leading-symbol maps in all
degrees and the character bound. -/
theorem JetLeadingSymbol.injective_of_bound (S : ∀ r, JetLeadingSymbol r)
    (hchi : JetCharacterBound) (r : ℕ) : Function.Injective (S r).g := by
  have hinj' : Function.Injective (S r).g' := by
    refine injective_of_graded (jetWtPiece_iSupIndep r) (iSup_grDeg r) (S r).g'
      (fun e => (S r).g'_mem e) fun e x hx h0 => ?_
    have hfr := finrank_grDeg_eq S hchi r e
    haveI := (S r).jetDeg_finiteDimensional e
    have hres : Function.Injective ((S r).restr e) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mpr
        ((S r).restr_surjective e)
    have : (S r).restr e ⟨x, hx⟩ = 0 :=
      Subtype.ext (Subtype.ext (by change ((S r).g x : JetPoly) = 0; exact h0))
    have := hres (this.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  intro a b h
  exact hinj' (by simp [JetLeadingSymbol.g', h])

/-- **Strictness from a surjective leading-symbol map and the character bound.** -/
def grJetStrict_of_leadingSymbol (S : ∀ r, JetLeadingSymbol r) (hchi : JetCharacterBound)
    (r : ℕ) : GrJetStrict r where
  f := (S r).g
  injective := JetLeadingSymbol.injective_of_bound S hchi r
  intertwine := (S r).intertwine
  degree := (S r).degree

/-! ### Degree zero -/

theorem grJetStrict_zero_f_grVac : grJetStrict_zero.f grVac = oneJet := by
  change (grCyclicVector_zero.w grVac)⁻¹ • (grCyclicVector_zero.w grVac • oneJet) = oneJet
  rw [smul_smul, inv_mul_cancel₀ grVac_w_ne_zero, one_smul]

/-- **The degree-zero leading-symbol map** (proved): the vacuum line maps onto the
constants `A_0 = ℂ`. -/
def jetLeadingSymbol_zero : JetLeadingSymbol 0 where
  g := grJetStrict_zero.f
  surjective := by
    rintro ⟨y, hy⟩
    rw [jetImage, pow_zero, Submodule.mem_one] at hy
    obtain ⟨c, rfl⟩ := hy
    refine ⟨c • grVac, ?_⟩
    rw [map_smul, grJetStrict_zero_f_grVac]
    apply Subtype.ext
    simp [oneJet, MvPolynomial.smul_eq_C_mul]
  intertwine := grJetStrict_zero.intertwine
  degree := grJetStrict_zero.degree

/-- All leading-symbol maps, the degree-zero one being proved. -/
def jetLeadingSymbols (S : ∀ r, JetLeadingSymbol (r + 1)) : ∀ r, JetLeadingSymbol r
  | 0 => jetLeadingSymbol_zero
  | r + 1 => S r

/-- **Strictness for `r ≥ 1`** from the leading-symbol maps for `r ≥ 1` and the character
bound: exactly the `strict` input of `leeYang_gradedUnitary_of_affine_strict`. -/
def grJetStrict_succ_of_leadingSymbol (S : ∀ r, JetLeadingSymbol (r + 1))
    (hchi : JetCharacterBound) (r : ℕ) : GrJetStrict (r + 1) :=
  grJetStrict_of_leadingSymbol (jetLeadingSymbols S) hchi (r + 1)

end

end VOA.SymbolModel
