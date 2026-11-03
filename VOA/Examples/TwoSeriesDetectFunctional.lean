/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharEndpoint

/-!
# Detection is equivalent to the existence of evaluation functionals

The detection input `TwoSeriesModelDetects n` says: the leading model symbol of any element of
the maximal ideal of `V^{k_n}(sl₂)`, evaluated at the Drinfeld–Sokolov point `(u, v) = (0, 1)`,
vanishes in `R_n`.  This file proves that it is **equivalent** to a statement that involves no
symbol calculus at all, only linear functionals on the universal vacuum module:

* `EvalFunctional L R t r` — there is a `ℂ`-linear map `Λ : V^{kA}(sl₂) → R` that
  1. kills the maximal ideal,
  2. kills the lower corrected piece `F_{r-1}`,
  3. sends every corrected word `w` of length `r` to the base-point value of its model symbol,
     `evR (mword w)`.

* `modelDetects_of_evalFunctional` — functionals give detection (span induction);
* `evalFunctional_of_modelDetects` — detection gives functionals (the symbol relation is the
  graph of a partial linear map; extend it to the whole space);
* `modelDetects_iff_evalFunctional`, and the boundary specialisation
  `twoSeriesModelDetects_iff_evalFunctional`;
* `twoSeries_gradedUnitary_of_evalFunctional` — the endpoint with `det` replaced by the
  functional family;
* `CoinvEvalFamily` — a **coinvariant** (Drinfeld–Sokolov-shaped) family: `Λ_{r+1} ∘ f_{-1} =
  -Λ_r` and `Λ_{r+1} ∘ f_{-j} = 0` (`j ≥ 2`), i.e. compatible with the constraint `f(z) = -1`;
  `evalFunctional_of_coinv` — for such a family the word condition is needed only on words
  not beginning with an `f`-letter; `twoSeriesModelDetects_of_coinv`,
  `twoSeries_gradedUnitary_of_coinv`.  (Numerical evidence, not a proof: exact linear algebra
  mod `p = 1000003` finds coinvariant families at `n = 2`, `N ≤ 9`, and `n = 3`, `N ≤ 9`; with the
  jets of `T^{n+1}` in place of those of `Tⁿ` the same system is unsolvable.)

Dead end recorded here: functionals of the form `λ ∘ e_1^a` (`a` = number of `f`-letters,
`λ` an arbitrary functional on the charge-zero space) do **not** suffice beyond the `T`-free part;
at `n = 2` they already fail at weight `3`, charge `-2`, `r = 2`, below the maximal ideal.

The point of the reformulation: a functional that factors through the simple quotient kills the
maximal ideal automatically, so any construction of `Λ` *through* `L_{k_n}` (for instance a
Drinfeld–Sokolov-type projection `L_{k_n} → M(2, 2n+1)` followed by the leading-symbol map of
the minimal model) leaves only the two filtration conditions 2 and 3 to check.  At `n = 1`
the functional is the vacuum coefficient after `e_1^r` (`Desc.evalBase_eq_zero_of_mem`).

Everything here is proved outright; no input is added.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.AdamovicSymbol
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

section Generic

variable (L : CosetLevels) (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)

/-- The base-point evaluation as a `ℂ`-linear map. -/
abbrev evRL : MPoly R →ₗ[ℂ] R := ((evR R).toLinearMap).restrictScalars ℂ

/-- **Evaluation functional at filtration index `r`**: a `ℂ`-linear map on the universal vacuum
module killing the maximal ideal and `F_{r-1}`, and sending each length-`r` corrected word to
the base-point value of its model symbol. -/
def EvalFunctional (r : ℕ) : Prop :=
  ∃ Λ : WakModule L.kA →ₗ[ℂ] R,
    (∀ y ∈ ImaxL L, Λ y = 0) ∧
    (∀ y ∈ lowerP L.kA L.aNoncritical r, Λ y = 0) ∧
    ∀ w : List (Generator × ℕ), w.length = r →
      Λ (correctedWordState L.kA L.aNoncritical w) = evR R (mword R t w)

variable {L R t}

/-- On the pair module, a functional with properties 2 and 3 computes the base-point value. -/
theorem evalFunctional_apply_eq {r : ℕ} (Λ : WakModule L.kA →ₗ[ℂ] R)
    (hlow : ∀ y ∈ lowerP L.kA L.aNoncritical r, Λ y = 0)
    (hword : ∀ w : List (Generator × ℕ), w.length = r →
      Λ (correctedWordState L.kA L.aNoncritical w) = evR R (mword R t w))
    {y : WakModule L.kA} {Q : MPoly R} (hyQ : (y, Q) ∈ symModM R t L.kA L.aNoncritical r) :
    Λ y = evR R Q := by
  let Δ : (WakModule L.kA × MPoly R) →ₗ[ℂ] R :=
    Λ.comp (LinearMap.fst ℂ _ _) - (evRL R).comp (LinearMap.snd ℂ _ _)
  have hle : symModM R t L.kA L.aNoncritical r ≤ LinearMap.ker Δ := by
    refine sup_le ?_ ?_
    · rw [symPairsM, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      simp only [Δ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
      rw [hword w hw, sub_self]
    · rintro ⟨z, p⟩ ⟨hz, hp⟩
      change p ∈ (⊥ : Submodule ℂ (MPoly R)) at hp
      rw [Submodule.mem_bot] at hp
      subst hp
      rw [LinearMap.mem_ker]
      simp only [Δ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, map_zero, sub_zero]
      exact hlow z hz
  have h := hle hyQ
  rw [LinearMap.mem_ker] at h
  simp only [Δ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply] at h
  exact sub_eq_zero.mp h

/-- **Functionals give detection** at filtration index `r`. -/
theorem detects_of_evalFunctional {r : ℕ} (h : EvalFunctional L R t r) :
    Detects R t L.kA L.aNoncritical (ImaxL L) r := by
  obtain ⟨Λ, hI, hlow, hword⟩ := h
  intro y Q hyQ hy
  rw [← evalFunctional_apply_eq Λ hlow hword hyQ]
  exact hI y hy

/-- The symbol relation, evaluated at the base point, together with `I × 0`. -/
def evalGraph (r : ℕ) : Submodule ℂ (WakModule L.kA × R) :=
  (symModM R t L.kA L.aNoncritical r).map (LinearMap.prodMap LinearMap.id (evRL R)) ⊔
    (ImaxL L).prod ⊥

theorem evalGraph_single {r : ℕ} (hdet : Detects R t L.kA L.aNoncritical (ImaxL L) r) :
    ∀ x : WakModule L.kA × R, x ∈ evalGraph (L := L) (t := t) r → x.1 = 0 → x.2 = 0 := by
  rintro ⟨y, z⟩ hx (hy0 : y = 0)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  obtain ⟨⟨y1, Q⟩, hyQ, rfl⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  change b.2 ∈ (⊥ : Submodule ℂ R) at hb2
  rw [Submodule.mem_bot] at hb2
  have h1 : y1 + b.1 = y := congrArg Prod.fst hab
  have h2 : evR R Q + b.2 = z := by
    have := congrArg Prod.snd hab
    simpa using this
  rw [hy0] at h1
  have hy1 : y1 ∈ ImaxL L := by
    have : y1 = -b.1 := eq_neg_of_add_eq_zero_left h1
    rw [this]
    exact neg_mem hb1
  change z = 0
  rw [← h2, hb2, add_zero]
  exact hdet y1 Q hyQ hy1

/-- **Detection gives functionals** at filtration index `r`. -/
theorem evalFunctional_of_detects {r : ℕ} (hdet : Detects R t L.kA L.aNoncritical (ImaxL L) r) :
    EvalFunctional L R t r := by
  set G := evalGraph (L := L) (t := t) r with hG
  have hs := evalGraph_single (L := L) (t := t) hdet
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (G.toLinearPMap.toFun)
  have key : ∀ y z, (y, z) ∈ G → Λ y = z := by
    intro y z hyz
    have hdom : y ∈ G.map (LinearMap.fst ℂ _ _) := ⟨(y, z), hyz, rfl⟩
    have hmem := Submodule.mem_graph_toLinearPMap hs ⟨y, hdom⟩
    have h1 : Λ y = G.toLinearPMap ⟨y, hdom⟩ := by
      have := LinearMap.congr_fun hΛ ⟨y, hdom⟩
      simpa using this
    rw [h1]
    have hsub := G.sub_mem hmem hyz
    have := hs _ hsub (by simp)
    simpa [sub_eq_zero] using this
  refine ⟨Λ, ?_, ?_, ?_⟩
  · intro y hy
    exact key y 0 (Submodule.mem_sup_right ⟨hy, Submodule.zero_mem _⟩)
  · intro y hy
    apply key
    refine Submodule.mem_sup_left ⟨(y, 0), lower_mem_symModM R t L.kA L.aNoncritical hy, ?_⟩
    simp
  · intro w hw
    apply key
    refine Submodule.mem_sup_left ⟨(correctedWordState L.kA L.aNoncritical w, mword R t w),
      hw ▸ word_mem_symModM R t L.kA L.aNoncritical w, ?_⟩
    simp

/-- **Detection ⟺ evaluation functionals**, at every level. -/
theorem modelDetects_iff_evalFunctional :
    ModelDetects L R t ↔ ∀ r, EvalFunctional L R t r :=
  ⟨fun h r => evalFunctional_of_detects (h r), fun h r => detects_of_evalFunctional (h r)⟩

/-! ### Coinvariant (Drinfeld–Sokolov-shaped) families

The Drinfeld–Sokolov constraint is `f(z) = χ`: in modes, `f_{-1} = χ` and `f_{-j} = 0` for
`j ≥ 2`; with the normalisation of the model (`f ↦ -v²`) the base point has `χ = -1`.  A family
of evaluation functionals is **coinvariant** if it is compatible with this constraint, the
filtration index dropping by one each time an `f`-letter is absorbed:

  `Λ_{r+1} (f_{-1} y) = - Λ_r y`,   `Λ_{r+1} (f_{-j} y) = 0`  (`j ≥ 2`).

Such a family factors through the Whittaker coinvariants `V / Σ_{j ≥ 1} (f_{-j} - χ δ_{j,1}) V`
(after collecting the filtration indices), which is where the Drinfeld–Sokolov reduction lives.
For a coinvariant family the word condition need only be checked on words that do **not** begin
with an `f`-letter (`evalFunctional_of_coinv`). -/

variable (L R t) in
/-- **A coinvariant family of evaluation functionals.** -/
def CoinvEvalFamily : Prop :=
  ∃ Λ : ℕ → (WakModule L.kA →ₗ[ℂ] R),
    (∀ r, ∀ y ∈ ImaxL L, Λ r y = 0) ∧
    (∀ r, ∀ y ∈ lowerP L.kA L.aNoncritical r, Λ r y = 0) ∧
    (∀ r y, Λ (r + 1) (J L.kA 1 (-1) y) = -Λ r y) ∧
    (∀ r (j : ℕ) y, Λ (r + 1) (J L.kA 1 (-(j : ℤ) - 2) y) = 0) ∧
    (∀ w : List (Generator × ℕ), (∀ m : ℕ, w.head? ≠ some (Generator.current 1, m)) →
      Λ w.length (correctedWordState L.kA L.aNoncritical w) = evR R (mword R t w))

theorem evR_mletter_f (m : ℕ) :
    evR R (mletter R t (Generator.current 1, m)) = if m = 0 then -1 else 0 := by
  change evR R (ι R (letterSym (Generator.current 1, m))) = _
  rw [evR_ι, Desc.evalBase_letterSym]
  by_cases hm : m = 0
  · subst hm; simp
  · have : (Generator.current 1, m) ≠ (Generator.current 1, 0) := by
      intro h; apply hm; exact (Prod.mk.inj h).2
    simp [this, hm]

/-- **A coinvariant family gives the evaluation functionals** at every index. -/
theorem evalFunctional_of_coinv (h : CoinvEvalFamily L R t) : ∀ r, EvalFunctional L R t r := by
  obtain ⟨Λ, hI, hlow, hf1, hfj, hword⟩ := h
  have key : ∀ w : List (Generator × ℕ),
      Λ w.length (correctedWordState L.kA L.aNoncritical w) = evR R (mword R t w) := by
    intro w
    induction w with
    | nil => exact hword [] (by simp)
    | cons l w ih =>
      by_cases hl : ∃ m : ℕ, l = (Generator.current 1, m)
      · obtain ⟨m, rfl⟩ := hl
        rw [correctedWordState_cons', letterOp_current, mword_cons, map_mul, evR_mletter_f,
          List.length_cons]
        rcases m with _ | m
        · simp only [Nat.cast_zero, neg_zero, zero_sub, if_true]
          rw [hf1, ih]; ring
        · rw [show (-((m + 1 : ℕ) : ℤ) - 1) = -(m : ℤ) - 2 by push_cast; ring, hfj]
          simp
      · refine hword _ fun m h => hl ⟨m, ?_⟩
        simpa using h
  intro r
  exact ⟨Λ r, hI r, hlow r, fun w hw => hw ▸ key w⟩

/-- A coinvariant family gives detection. -/
theorem modelDetects_of_coinv (h : CoinvEvalFamily L R t) : ModelDetects L R t :=
  modelDetects_iff_evalFunctional.mpr (evalFunctional_of_coinv h)

end Generic

/-! ### The boundary index -/

/-- The evaluation-functional family at the boundary index `n`. -/
def TwoSeriesEvalFunctionals (n : ℕ) : Prop :=
  ∀ r, EvalFunctional (twoSeriesLevels n) (Rn n) (tn n) r

/-- **`TwoSeriesModelDetects n` ⟺ the evaluation-functional family.** -/
theorem twoSeriesModelDetects_iff_evalFunctional (n : ℕ) :
    TwoSeriesModelDetects n ↔ TwoSeriesEvalFunctionals n :=
  modelDetects_iff_evalFunctional

/-- The coinvariant (Drinfeld–Sokolov-shaped) family at the boundary index `n`. -/
def TwoSeriesCoinvEvalFamily (n : ℕ) : Prop :=
  CoinvEvalFamily (twoSeriesLevels n) (Rn n) (tn n)

/-- A coinvariant family gives `TwoSeriesModelDetects n`. -/
theorem twoSeriesModelDetects_of_coinv {n : ℕ} (h : TwoSeriesCoinvEvalFamily n) :
    TwoSeriesModelDetects n :=
  modelDetects_of_coinv h

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`** with detection replaced by the evaluation
functionals. -/
theorem twoSeries_gradedUnitary_of_evalFunctional (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (Λ : TwoSeriesEvalFunctionals n) (spec : ∀ r, ModelSocleSpectrum n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  VOA.TwoSeries.ModelChar.twoSeries_gradedUnitary_of_strictModel_det n hn hA
    ((twoSeriesModelDetects_iff_evalFunctional n).mpr Λ) spec

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`** from a coinvariant (Drinfeld–Sokolov-shaped)
family. -/
theorem twoSeries_gradedUnitary_of_coinv (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (Λ : TwoSeriesCoinvEvalFamily n) (spec : ∀ r, ModelSocleSpectrum n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  VOA.TwoSeries.ModelChar.twoSeries_gradedUnitary_of_strictModel_det n hn hA
    (twoSeriesModelDetects_of_coinv Λ) spec

end

end VOA.TwoSeries.StrictModel
