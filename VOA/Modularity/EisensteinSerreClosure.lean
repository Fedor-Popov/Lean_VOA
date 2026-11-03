/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.EisensteinRamanujan
import VOA.Modularity.AKMLDE
import VOA.Huang.AndersonMooreCore
import VOA.LatticesAndCodes.ModularForms.LevelOne

/-!
# Serre closure of the Eisenstein coefficient algebra `E46`

`Modularity/EisensteinRamanujan.lean` exposes three named properties of `E46 = ℂ[E₄, E₆]`:
`E46HasWeightedPolynomialReps`, `E46SerreMonomialClosed` and `E46SerreClosed`. This file proves
all three.

* `serreForm F : ModularForm 𝒮ℒ (n + 2)`: the Serre derivative of a level-one modular form
  of weight `n` is a level-one modular form of weight `n + 2`, agreeing with `serreDerivC n` on `ℍ`
  (`serreForm_apply`).
* `e46SerreClosed : E46SerreClosed`.
* `e46HasWeightedPolynomialReps : E46HasWeightedPolynomialReps`. The proof is the one in
  `Notes/Textbook/certificates/L14_Checks.lean`, from the basis theorem `ModularForm.span_eisBasisFun`.
* `e46SerreMonomialClosed : E46SerreMonomialClosed`.
* `IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite'` and `…_of_fin_gen'`: the
  Arakawa–Kawasetsu MLDE theorems of `Modularity/AKMLDE.lean`, with the `hclose : E46SerreClosed`
  hypothesis discharged.

## Method for `serreForm`

On `ℍ`, `F = amEval 0 (qExpansion 1 F)` (`AndersonMoore.modularForm_eq_amEval`). The Serre
derivative acts on such evaluations through the formal operator `serreF`
(`serreDerivC_amEval`), so `g := amEval 0 (serreF n 0 (qExpansion 1 F))` is the Serre derivative
on `ℍ`. It is:
* holomorphic there (`differentiableOn_amEval`);
* `1`-periodic (`amEval_add_one` at `ν = 0`);
* bounded at `i∞` (`isBoundedAtImInfty_amEval_zero`), since `serreF` preserves sub-exponential
  growth.

Its weight-`(n+2)` law at `S` is the Serre-derivative equivariance `serreDerivC_slashC`, applied to
the weight-`n` law of `F`. `AndersonMoore.mkLevelOne` then packages `g` as a modular form. The
Ramanujan identities for `E₄` and `E₆` are **not** needed: closure under `ϑ` comes from
modularity together with `M_* = ℂ[E₄, E₆]` (`levelOne_coe_mem_E46`).
-/

open Complex Filter Topology UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace VOA

open VOA.Huang.AndersonMoore

/-! ## §1  The Serre derivative of a level-one form is a level-one form -/

section SerreForm

variable {n : ℕ} (F : ModularForm 𝒮ℒ (n : ℤ))

/-- The Serre derivative of `F`, as a function on `ℂ`, through the formal `q`-expansion. -/
def serreFun : ℂ → ℂ := amEval 0 (serreF (n : ℤ) 0 (qExpansion 1 F))

theorem serreFun_mem : serreF (n : ℤ) 0 (qExpansion 1 F) ∈ SubexpPS :=
  serreF_mem (qExpansion_mem_subexpPS F)

/-- `F ∘ ofComplex` agrees with its `q`-series near every point of `ℍ`. -/
theorem comp_ofComplex_eventuallyEq {z : ℂ} (hz : z ∈ imGT 0) :
    (fun w => F (ofComplex w)) =ᶠ[𝓝 z] amEval 0 (qExpansion 1 F) := by
  filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
  exact modularForm_eq_amEval F hw

/-- On `ℍ`, `serreFun F` is the Serre derivative of `F`. -/
theorem serreFun_eq {z : ℂ} (hz : z ∈ imGT 0) :
    serreFun F z = serreDerivC (n : ℤ) (fun w => F (ofComplex w)) z := by
  rw [serreDerivC_congr_of_eventuallyEq _ (comp_ofComplex_eventuallyEq F hz),
    serreDerivC_amEval _ (qExpansion_mem_subexpPS F) hz]
  rfl

theorem serreFun_T {z : ℂ} (_hz : z ∈ imGT 0) : serreFun F (z + 1) = serreFun F z := by
  rw [serreFun, amEval_add_one]
  simp

theorem serreFun_S {z : ℂ} (hz : z ∈ imGT 0) :
    serreFun F (-1 / z) = z ^ (n + 2) * serreFun F z := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_imGT hz
  set f : ℂ → ℂ := fun w => F (ofComplex w) with hf
  -- the weight-`n` law of `F` makes `f` slash-invariant near `z`
  have hslash : slashC (n : ℤ) ModularGroup.S f =ᶠ[𝓝 z] f := by
    filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := ne_zero_of_mem_imGT hw
    rw [slashC, mobiusC_S, denomC_S, hf]
    simp only
    rw [slashInv_S_apply F hw, zpow_neg, zpow_natCast]
    field_simp
  have hdiff : DifferentiableAt ℂ f (mobiusC ModularGroup.S z) :=
    (analyticAt_slashInv F (mobiusC_mem_imGT _ hz)).differentiableAt
  have hkey := serreDerivC_slashC (n : ℤ) ModularGroup.S f hz hdiff
  rw [serreDerivC_congr_of_eventuallyEq _ hslash, slashC, mobiusC_S, denomC_S] at hkey
  rw [serreFun_eq F (neg_one_div_mem_imGT hz), serreFun_eq F hz, ← hkey,
    show ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) from by push_cast; ring, zpow_neg, zpow_natCast]
  field_simp
  rfl

/-- **The Serre derivative of a weight-`n` level-one form, as a weight-`(n+2)` form.** -/
def serreForm : ModularForm 𝒮ℒ ((n + 2 : ℕ) : ℤ) :=
  mkLevelOne (serreFun F) (n + 2) (differentiableOn_amEval (serreFun_mem F))
    (fun _ hz => serreFun_S F hz) (fun _ hz => serreFun_T F hz)
    (isBoundedAtImInfty_amEval_zero (serreFun_mem F))

theorem serreForm_apply {z : ℂ} (hz : z ∈ imGT 0) :
    serreForm F (ofComplex z) = serreDerivC (n : ℤ) (fun w => F (ofComplex w)) z := by
  rw [serreForm, mkLevelOne_apply, ofComplex_apply_of_im_pos hz]
  exact serreFun_eq F hz

end SerreForm

/-! ## §2  The three named properties -/

/-- **`E46` is closed under the Serre derivative.** -/
theorem e46SerreClosed : E46SerreClosed := by
  intro k f hf
  obtain ⟨F, hF⟩ := hf
  rcases lt_or_ge k 0 with hneg | hk0
  · -- negative weight: `F = 0`
    have h0 : (F : UpperHalfPlane → ℂ) = 0 := ModularFormClass.levelOne_neg_weight_eq_zero hneg F
    have hf0 : f = 0 := Subtype.ext (by rw [hF, h0]; rfl)
    refine ⟨0, E46Weight.zero _, fun z _ => ?_⟩
    subst hf0
    simp [serreDerivC]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
  let G := serreForm F
  refine ⟨⟨⇑G, levelOne_coe_mem_E46 _ G⟩, ⟨ModularForm.mcast (by push_cast; ring) G, rfl⟩,
    fun z hz => ?_⟩
  show (G : ℍ → ℂ) (ofComplex z) = _
  rw [serreForm_apply F hz]
  congr 1
  funext w
  rw [e46C, hF]

/-- Every weight-`k` element of `E46` has a homogeneous polynomial representative in `E₄`, `E₆`
(the proof of `Notes/Textbook/certificates/L14_Checks.lean`). -/
theorem e46HasWeightedPolynomialReps : E46HasWeightedPolynomialReps := by
  classical
  intro k f hf
  obtain ⟨F, hF⟩ := hf
  rcases lt_or_ge k 0 with hneg | hk0
  · refine ⟨∅, fun _ => 0, ?_, by simp⟩
    have h0 : (F : UpperHalfPlane → ℂ) = 0 := ModularFormClass.levelOne_neg_weight_eq_zero hneg F
    apply Subtype.ext
    rw [hF, h0]
    simp
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
  have hmem : F ∈ Submodule.span ℂ (Set.range (ModularForm.eisBasisFun n)) := by
    rw [ModularForm.span_eisBasisFun]; trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hmem
  have hF' : (F : UpperHalfPlane → ℂ) = ∑ p ∈ c.support,
      c p • (fun z => ModularForm.E₄ z ^ (p : ℕ × ℕ).1 * ModularForm.E₆ z ^ (p : ℕ × ℕ).2) := by
    have h := congrArg (ModularForm.coeLm (n : ℤ)) hc
    rw [Finsupp.sum, map_sum] at h
    simp only [map_smul, ModularForm.coeLm_apply, ModularForm.coe_eisBasisFun] at h
    exact h.symm
  refine ⟨(c.support).map ⟨Subtype.val, Subtype.val_injective⟩,
    fun ab => if h : ab ∈ ModularForm.wtIdx n then c ⟨ab, h⟩ else 0, ?_, ?_⟩
  · apply Subtype.ext
    change (f : UpperHalfPlane → ℂ) = E46.val _
    rw [hF, hF', map_sum, Finset.sum_map]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Function.Embedding.coeFn_mk, dif_pos p.2, map_smul]
    rfl
  · intro ab hab
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hab
    obtain ⟨p, _, rfl⟩ := hab
    have := ModularForm.mem_wtIdx.mp p.2
    exact_mod_cast this

/-- **Serre closure on the `E₄^a E₆^b` monomials.** -/
theorem e46SerreMonomialClosed : E46SerreMonomialClosed := fun a b =>
  e46SerreClosed _ _ (e46Monomial_weight a b)

/-- The reduction `e46SerreClosed_of_weightedPolynomialReps` with both inputs supplied. -/
theorem e46SerreClosed' : E46SerreClosed :=
  e46SerreClosed_of_weightedPolynomialReps e46HasWeightedPolynomialReps e46SerreMonomialClosed

/-! ## §3  The Arakawa–Kawasetsu MLDE theorems without the closure hypothesis -/

section AK

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite` with `E46SerreClosed`
discharged. -/
theorem IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite'
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hgrade : AKWeightGrading W)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    ∃ (s : ℕ) (p : ℕ → E46), 1 ≤ s ∧
      ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F → MonicMLDEOn wt (F a) s p :=
  ha.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite hgrade e46SerreClosed hzero hE

/-- `IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_fin_gen` with `E46SerreClosed`
discharged. -/
theorem IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_fin_gen'
    {W : VertexOperatorAlgebra 𝒱} {a : 𝒱} {wt : ℤ}
    (ha : IsSqPrimary W a (wt : ℂ)) (hgrade : AKWeightGrading W)
    (T : Set (𝒱E 𝒱)) (hTfin : T.Finite)
    (htop : (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      = Submodule.span (↥E46) T ⊔ blockRelSpanE W) :
    ∃ (s : ℕ) (p : ℕ → E46), 1 ≤ s ∧
      ∀ (F : 𝒱 → ℂ → ℂ), IsAnalyticBlock W F → MonicMLDEOn wt (F a) s p :=
  ha.exists_monicMLDEOn_all_analyticBlocks_of_fin_gen hgrade e46SerreClosed T hTfin htop

end AK

end VOA

section AxiomAudit
#print axioms VOA.IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_etingofFinite'
#print axioms VOA.IsSqPrimary.exists_monicMLDEOn_all_analyticBlocks_of_fin_gen'
#print axioms VOA.serreForm
#print axioms VOA.serreForm_apply
#print axioms VOA.e46SerreClosed
#print axioms VOA.e46HasWeightedPolynomialReps
#print axioms VOA.e46SerreMonomialClosed
#print axioms VOA.e46SerreClosed'
end AxiomAudit
