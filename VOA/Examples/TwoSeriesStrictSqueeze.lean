/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictDescent
import VOA.Examples.JetStrictSqueeze

/-!
# Strictness of the model symbol map by the character squeeze, at every level

The level-one squeeze (`JetStrictSqueeze`), ported to any coset level datum `L` and to the
model `modelImage R t r`:

* `sum_finrank_grDegL` — **telescoping**: `Σ_{r ≤ R} dim gr_{r,d} = dim F_R L_d`;
* `ModelSymbol.map_grDeg` — `g(gr_{r,d}) = modelDeg r d` (inside the model image);
* `ModelCharacterBound L R t` — `dim L_N ≤ Σ_{r ≤ N} dim modelDeg r N` (the input);
* `finrank_grDeg_eq_model` — the squeeze: `dim gr_{r,d} = dim modelDeg r d` for all `r, d`;
* `ModelSymbol.injective_of_bound` — **kernel zero**: given surjective model symbol maps in
  every degree, the independence of the model's conformal pieces, and the character bound,
  every model symbol map is injective.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial
open VOA.SymbolModel (mem_of_mem_iSup_indep injective_of_graded)
open scoped BigOperators

noncomputable section

variable (L : CosetLevels)

/-! ### The corrected filtration at fixed weight, at level `L` -/

theorem aGrading_iSupIndepL : iSupIndep (AVOA L).grading := by
  have h := (Module.End.eigenspaces_iSupIndep
    (mode ((AVOA L).Y (AVOA L).conformalVector) 1)).comp
    (f := fun n : ℤ => (n : ℂ)) (fun a b h => Int.cast_injective h)
  refine h.mono fun n x hx => ?_
  rw [Function.comp_apply, Module.End.mem_eigenspace_iff]
  exact (AVOA L).L0_grading x hx

theorem mem_piece_of_mem_aFilL {q : ℕ} {d : ℤ} {x : ASpace L} (hx : x ∈ (AVOA L).grading d)
    (hq : x ∈ aFil L q) : x ∈ (affineFlag L).piece q d :=
  mem_of_mem_iSup_indep (aGrading_iSupIndepL L) (fun m => (affineFlag L).le_grading q m) hx hq

/-- `F_{r-1} L_d`, with `F_{-1} = 0`. -/
def pieceLTL : ℕ → ℤ → Submodule ℂ (ASpace L)
  | 0, _ => ⊥
  | q + 1, d => (affineFlag L).piece q d

theorem pieceLTL_le (r : ℕ) (d : ℤ) : pieceLTL L r d ≤ (affineFlag L).piece r d := by
  cases r with
  | zero => exact bot_le
  | succ q => exact (affineFlag L).mono d (Nat.le_succ q)

theorem piece_le_aFilL (r : ℕ) (d : ℤ) : (affineFlag L).piece r d ≤ aFil L r :=
  le_iSup (fun m => (affineFlag L).piece r m) d

/-- The class map `F_r L_d → gr_r`. -/
def pieceToGrL (r : ℕ) (d : ℤ) : (affineFlag L).piece r d →ₗ[ℂ] GrA L r :=
  (grKer L r).mkQ ∘ₗ Submodule.inclusion (piece_le_aFilL L r d)

theorem range_pieceToGrL (r : ℕ) (d : ℤ) : LinearMap.range (pieceToGrL L r d) = grDeg L r d := by
  rw [pieceToGrL, LinearMap.range_comp, Submodule.range_inclusion, grDeg]

theorem ker_pieceToGrL (r : ℕ) (d : ℤ) :
    LinearMap.ker (pieceToGrL L r d) =
      (pieceLTL L r d).comap ((affineFlag L).piece r d).subtype := by
  ext x
  rw [LinearMap.mem_ker, pieceToGrL, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  change (x : ASpace L) ∈ aFilLT L r ↔ _
  have hxd : (x : ASpace L) ∈ (AVOA L).grading d := (affineFlag L).le_grading r d x.2
  cases r with
  | zero => rfl
  | succ q =>
    exact ⟨fun h => mem_piece_of_mem_aFilL L hxd h, fun h => piece_le_aFilL L q d h⟩

instance piece_finiteDimensionalL (r : ℕ) (d : ℤ) :
    FiniteDimensional ℂ ((affineFlag L).piece r d) :=
  haveI := (AVOA L).finrank d
  Submodule.finiteDimensional_of_le ((affineFlag L).le_grading r d)

instance pieceLTL_finiteDimensional (r : ℕ) (d : ℤ) : FiniteDimensional ℂ (pieceLTL L r d) :=
  Submodule.finiteDimensional_of_le (pieceLTL_le L r d)

instance grDeg_finiteDimensionalL (r : ℕ) (d : ℤ) : FiniteDimensional ℂ (grDeg L r d) := by
  rw [← range_pieceToGrL]; infer_instance

theorem finrank_grDeg_addL (r : ℕ) (d : ℤ) :
    Module.finrank ℂ (grDeg L r d) + Module.finrank ℂ (pieceLTL L r d) =
      Module.finrank ℂ ((affineFlag L).piece r d) := by
  have h := LinearMap.finrank_range_add_finrank_ker (pieceToGrL L r d)
  rw [range_pieceToGrL, ker_pieceToGrL] at h
  rw [← h, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (pieceLTL_le L r d))]

/-- **Telescoping**: `Σ_{r ≤ R} dim gr_{r,d} = dim F_R L_d`. -/
theorem sum_finrank_grDegL (R : ℕ) (d : ℤ) :
    ∑ r ∈ Finset.range (R + 1), Module.finrank ℂ (grDeg L r d) =
      Module.finrank ℂ ((affineFlag L).piece R d) := by
  induction R with
  | zero =>
    have h := finrank_grDeg_addL L 0 d
    rw [show pieceLTL L 0 d = ⊥ from rfl, finrank_bot ℂ (ASpace L), add_zero] at h
    simpa using h
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, add_comm, ← finrank_grDeg_addL L (R + 1) d]
    rfl

theorem exists_piece_eq_gradingL (d : ℤ) :
    ∃ R : ℕ, (affineFlag L).piece R d = (AVOA L).grading d := by
  haveI := (AVOA L).finrank d
  have hfg : ((AVOA L).grading d).FG := Module.Finite.iff_fg.mp inferInstance
  have hc := (Submodule.fg_iff_compact _).mp hfg
  have hdir : DirectedOn (· ≤ ·) (Set.range fun p : ℕ => (affineFlag L).piece p d) :=
    ((affineFlag L).directed d).directedOn_range
  obtain ⟨_, ⟨R, rfl⟩, hR⟩ :=
    (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).mp hc
      (Set.range fun p : ℕ => (affineFlag L).piece p d) (Set.range_nonempty _) hdir
      (by rw [sSup_range, (affineFlag L).exhaustive d])
  exact ⟨R, le_antisymm ((affineFlag L).le_grading R d) hR⟩

theorem iSup_grDegL (r : ℕ) : ⨆ d, grDeg L r d = ⊤ := by
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

/-! ### The squeeze -/

variable (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)

/-- **The model character bound** (input): `dim L_N ≤ Σ_{r ≤ N} dim modelDeg r N`. -/
def ModelCharacterBound : Prop :=
  ∀ N : ℕ, Module.finrank ℂ ((AVOA L).grading (N : ℤ)) ≤
    ∑ r ∈ Finset.range (N + 1), Module.finrank ℂ (modelDeg R t r (N : ℤ))

namespace ModelSymbol

variable {L R t} {r : ℕ} (S : ModelSymbol L R t r)

/-- The symbol map composed into the model ring. -/
def g' : GrA L r →ₗ[ℂ] MPoly R := (modelImage R t r).subtype ∘ₗ S.g

theorem g'_mem (d : ℤ) : ∀ x ∈ grDeg L r d, S.g' x ∈ modelDeg R t r d :=
  fun x hx => S.degree d x hx

/-- `g(gr_{r,d})` is exactly `modelDeg r d`. -/
theorem map_grDeg (d : ℤ) : (grDeg L r d).map S.g' = modelDeg R t r d := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun x hx => S.g'_mem d x hx) ?_
  rw [modelDeg, Submodule.span_le]
  rintro _ ⟨w, hw, hd, rfl⟩
  refine ⟨_, hd ▸ wordClass_mem_grDeg w hw, ?_⟩
  exact S.word w hw

theorem modelDeg_finiteDimensional (S : ModelSymbol L R t r) (d : ℤ) :
    FiniteDimensional ℂ (modelDeg R t r d) := by
  rw [← S.map_grDeg d]; infer_instance

theorem finrank_modelDeg_le (S : ModelSymbol L R t r) (d : ℤ) :
    Module.finrank ℂ (modelDeg R t r d) ≤ Module.finrank ℂ (grDeg L r d) := by
  rw [← S.map_grDeg d]; exact Submodule.finrank_map_le _ _

/-- The restriction `gr_{r,d} → modelDeg r d`. -/
def restr (d : ℤ) : grDeg L r d →ₗ[ℂ] modelDeg R t r d := S.g'.restrict (S.g'_mem d)

theorem restr_surjective (d : ℤ) : Function.Surjective (S.restr d) := by
  rintro ⟨y, hy⟩
  rw [← S.map_grDeg d] at hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

end ModelSymbol

/-- **The dimension squeeze**: with model symbol maps in all degrees and the character
bound, `dim gr_{r,d} = dim modelDeg r d` for all `r, d`. -/
theorem finrank_grDeg_eq_model (S : ∀ r, ModelSymbol L R t r) (hchi : ModelCharacterBound L R t)
    (r : ℕ) (d : ℤ) : Module.finrank ℂ (grDeg L r d) = Module.finrank ℂ (modelDeg R t r d) := by
  obtain ⟨R₀, hR⟩ := exists_piece_eq_gradingL L d
  rcases lt_or_ge d 0 with hd | hd
  · have h0 : (affineFlag L).piece r d = ⊥ := by
      rw [eq_bot_iff, ← (AVOA L).positivity d hd]; exact (affineFlag L).le_grading r d
    have hg : Module.finrank ℂ (grDeg L r d) = 0 := by
      have h := finrank_grDeg_addL L r d
      rw [h0, finrank_bot ℂ (ASpace L)] at h
      omega
    have := (S r).finrank_modelDeg_le d
    omega
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    set T := max (max R₀ N) r with hT
    have hRT : R₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
    have hNT : N ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
    have hrT : r ≤ T := le_max_right _ _
    have hpT : (affineFlag L).piece T (N : ℤ) = (AVOA L).grading (N : ℤ) :=
      le_antisymm ((affineFlag L).le_grading _ _) (hR ▸ (affineFlag L).mono _ hRT)
    have hsumG := sum_finrank_grDegL L T (N : ℤ)
    rw [hpT] at hsumG
    have hle : ∀ i ∈ Finset.range (T + 1),
        Module.finrank ℂ (modelDeg R t i (N : ℤ)) ≤ Module.finrank ℂ (grDeg L i (N : ℤ)) :=
      fun i _ => (S i).finrank_modelDeg_le _
    have hsub : Finset.range (N + 1) ⊆ Finset.range (T + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have hA : Module.finrank ℂ ((AVOA L).grading (N : ℤ)) ≤
        ∑ i ∈ Finset.range (T + 1), Module.finrank ℂ (modelDeg R t i (N : ℤ)) :=
      (hchi N).trans (Finset.sum_le_sum_of_subset hsub)
    have heq : ∑ i ∈ Finset.range (T + 1), Module.finrank ℂ (modelDeg R t i (N : ℤ)) =
        ∑ i ∈ Finset.range (T + 1), Module.finrank ℂ (grDeg L i (N : ℤ)) :=
      le_antisymm (Finset.sum_le_sum hle) (hsumG ▸ hA)
    exact ((Finset.sum_eq_sum_iff_of_le hle).mp heq r (Finset.mem_range.mpr (by omega))).symm

/-- **Kernel zero**: with model symbol maps in all degrees, independent conformal pieces of
the model, and the character bound, every model symbol map is injective. -/
theorem ModelSymbol.injective_of_bound (S : ∀ r, ModelSymbol L R t r)
    (hind : ∀ r, iSupIndep (modelDeg R t r)) (hchi : ModelCharacterBound L R t) (r : ℕ) :
    Function.Injective (S r).g := by
  have hinj' : Function.Injective (S r).g' := by
    refine injective_of_graded (hind r) (iSup_grDegL L r) (S r).g'
      (fun e => (S r).g'_mem e) fun e x hx h0 => ?_
    have hfr := finrank_grDeg_eq_model L R t S hchi r e
    haveI := (S r).modelDeg_finiteDimensional e
    have hres : Function.Injective ((S r).restr e) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mpr
        ((S r).restr_surjective e)
    have : (S r).restr e ⟨x, hx⟩ = 0 := Subtype.ext h0
    have := hres (this.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  intro a b h
  exact hinj' (by simp [ModelSymbol.g', h])

end

end VOA.TwoSeries.StrictModel
