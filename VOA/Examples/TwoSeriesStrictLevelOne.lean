/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictEndpoint

/-!
# Sanity check: at `n = 1` both inputs of the strict-model route are proved

At `n = 1`, `R_1 = ℂ[T_j]/(T_j) = ℂ` and every `T_j` vanishes, so the model `S_{1,r}` is the
level-one Adamović image `A_r` pushed into `R_1[u_j, v_j]`.

* `twoSeriesModelDetects_one` (in `TwoSeriesStrictEndpoint`) — detection holds at `n = 1`;
* `twoSeriesModelCharacter_one` — the model character bound holds at `n = 1`, from the proved
  level-one jet-ring bound (`jetProductBound_of_identity jetFermionicIdentity`) and an injection
  `A_{r,N} ↪ S_{1,r,N}`;
* `twoSeriesStrictModel_one` — **the strict maps `gr_r L_{-4/3} ↪ S_{1,r}` hold outright**,
  so both inputs of `twoSeriesStrictModel` are satisfiable and the route is not vacuous.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.AdamovicSymbol
open VOA.AffineVOA.CorrectedR (Generator)

noncomputable section

theorem tn_one (j : ℕ) : tn 1 j = 0 := by
  rw [tn, Ideal.Quotient.eq_zero_iff_mem, jetIdealT_one]
  exact Ideal.subset_span ⟨j, rfl⟩

theorem mword_one (w : List (Generator × ℕ)) :
    mword (Rn 1) (tn 1) w = ι (Rn 1) (wordSym w) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [mword_cons, ih, wordSym_cons, map_mul]
    congr 1
    obtain ⟨g, n⟩ := l
    cases g with
    | current a => rfl
    | sugawara =>
      change ι (Rn 1) (letterSym _) + MvPolynomial.C (tn 1 n) = _
      rw [tn_one, map_zero, add_zero]

instance rn_one_nontrivial : Nontrivial (Rn 1) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (εn 1 le_rfl) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem ι_one_injective : Function.Injective (ι (Rn 1)) := by
  intro P Q h
  exact MvPolynomial.map_injective _ (algebraMap ℂ (Rn 1)).injective h

/-- The level-one jet image of weight `N` lands in the model piece. -/
theorem ι_mem_modelDeg_one {r : ℕ} {N : ℤ} {x : jetImage r} (hx : x ∈ jetDeg r N) :
    ι (Rn 1) (x : JetPoly) ∈ modelDeg (Rn 1) (tn 1) r N := by
  let P : ℤ → Submodule ℂ JetPoly := fun e => Submodule.span ℂ
    {Q | ∃ w : List (Generator × ℕ), w.length = r ∧ wordWt w = e ∧ wordSym w = Q}
  have hPJ : ∀ e, P e ≤ jetWtPiece r e := fun e => by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, he, rfl⟩
    have h := wordSym_mem_weighted w
    rw [show wordJetWt w = e - r by rw [← he, wordWt_eq, hw]; ring] at h
    exact h
  have hsup : (x : JetPoly) ∈ ⨆ e, P e := by
    refine (Submodule.span_le.mpr ?_) (jetImage_le_span_wordSym r x.2)
    rintro _ ⟨w, hw, rfl⟩
    exact Submodule.mem_iSup_of_mem (wordWt w) (Submodule.subset_span ⟨w, hw, rfl, rfl⟩)
  have hN : (x : JetPoly) ∈ P N :=
    mem_of_mem_iSup_indep (jetWtPiece_iSupIndep r) hPJ (jetDeg_coe_mem hx) hsup
  have hle : P N ≤ (modelDeg (Rn 1) (tn 1) r N).comap (ι (Rn 1)).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, he, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply, ← mword_one]
    exact Submodule.subset_span ⟨w, hw, he, rfl⟩
  exact hle hN

theorem finrank_jetDeg_le_model (r : ℕ) (N : ℤ) :
    Module.finrank ℂ (jetDeg r N) ≤ Module.finrank ℂ (modelDeg (Rn 1) (tn 1) r N) := by
  haveI := (modelSymbol (twoSeriesModelDetects_one) r).modelDeg_finiteDimensional N
  let f : jetDeg r N →ₗ[ℂ] modelDeg (Rn 1) (tn 1) r N :=
    { toFun := fun x => ⟨ι (Rn 1) ((x : jetImage r) : JetPoly), ι_mem_modelDeg_one x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x y h => ?_
  have h' := ι_one_injective (congrArg Subtype.val h)
  exact Subtype.ext (Subtype.ext h')

/-- **The model character bound at `n = 1`, proved.** -/
theorem twoSeriesModelCharacter_one : TwoSeriesModelCharacter 1 := by
  intro N
  have h := VOA.JetProduct.jetProductBound_of_identity VOA.JetFermionic.jetFermionicIdentity N
  refine h.trans (Finset.sum_le_sum fun r _ => ?_)
  exact_mod_cast finrank_jetDeg_le_model r N

/-- **The strict model maps at `n = 1`, outright**: both inputs are discharged. -/
def twoSeriesStrictModel_one (r : ℕ) : StrictModelMap 1 r :=
  twoSeriesStrictModel le_rfl twoSeriesModelDetects_one twoSeriesModelCharacter_one r

end

end VOA.TwoSeries.StrictModel
