/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuStronglyRational
import VOA.Huang.ZhuFiniteIrr
import VOA.Huang.ZhuSemisimple
import VOA.Modularity.BuhlSpanningData
import VOA.Modularity.TraceNonvanish
import VOA.Core.SimpleImage
import VOA.Classification.COne.Inputs

/-!
# `IModData` from Zhu's theorem

`VOA.Classification.COne.IModData` asks, for every nice VOA `V`, for a
`ModularData.IsModularData` package. Its clauses split by what proves them:

* **classification** (`irred`, `exhaust`, `distinct`, `vac_iso`, `weight_support`, `weight_lowest`,
  `h_vac`): from the canonical family of `Φ V` and Gannon's Lemma 5.3.3, *proved here*; finiteness
  of `Φ V` is *proved* in `Huang/ZhuFiniteIrr.lean` from `C₂` + semisimplicity of `A(V)` (so
  Dong–Li–Mason finiteness is **not** an input);
* **characters** (`char`, `char_vac`): from `C₂`-cofiniteness via the library's subexponential
  growth theorem `onePointSubexp_of_c2`, *proved here*;
* **`S_transform`**, **`S_pinned`**: from the library's pinned Zhu theorem
  `zhuModularity_pinned_of_C2Cofinite` at `γ = S` (`v = 𝟙`, resp. every square-bracket
  homogeneous `v`), *proved here*; in particular the `S`-matrix of the produced data is literally
  Zhu's `ρ(S) = D.repS` (reindexed); semisimplicity of `A(V)` (needed by Zhu's theorem) is
  *proved* from rationality in `Huang/ZhuSemisimple.lean`;
* **`h : ι → ℚ`**: rationality of conformal weights (Dong–Li–Mason 2000, Thm 11.3) — a named input;
* **positivity** (`S00_pos`, `S_vac_vac`, `S_vac_left/right`, `d_ge_one`, `S_bound`): Huang's
  Verlinde/MTC theorem, pseudo-unitarity and Gannon's bound — a named input
  (`HuangSPositivityInput`) about the *actual* Zhu matrix `ρ(S)`.

## Inputs (each a published theorem at its natural generality)

* `ZhuPBWBottomInput` — bottom projection for the regular `A(V)`-module. PBW (DLM 1998
  Thm 4.1); the theorem `VOA.pbw` implies it
  (`zhuPBWBottomInput_of_pbw`).
* `DLMRationalWeightsInput` — conformal weights of a strongly rational VOA are rational.
  DLM 2000 Thm 11.3; Anderson–Moore 1988.
* `HuangSPositivityInput` — `ρ(S)` vacuum entries positive and symmetric, `d ≥ 1`,
  `‖S_ab‖ ≤ S₀₀ d_a d_b`. Huang 2008; ENO 2005; Gannon 2005 (4.2a).

## Main result

* `iModData_of_inputs` : the three inputs imply `IModData`. `#print axioms`: Lean's three only.
* `iModData_of_pbw_inputs` : the same with `ZhuPBWBottomInput` discharged by `VOA.pbw`.
-/

open Complex Finset Module

noncomputable section

namespace VOA.Huang.ZhuModData

open VOA VOA.Classification.COne VOA.VHat VOA.VHat.DLM3 VOA.Huang.ZhuFiniteIrr
  VOA.Huang.ZhuSemisimple

universe u w

/-! ## §1 Small transport lemmas -/

section Transport

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M N : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- A module isomorphism preserves the dimension of every weight space. -/
theorem ModuleEquiv.finrank_weight_eq {A : OrdVModule W M} {B : OrdVModule W N}
    (e : ModuleEquiv W A B) (α : ℂ) :
    finrank ℂ (A.weight α) = finrank ℂ (B.weight α) := by
  have key : ∀ {M N : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
      {A : OrdVModule W M} {B : OrdVModule W N} (e : ModuleEquiv W A B),
      finrank ℂ (A.weight α) ≤ finrank ℂ (B.weight α) := by
    intro M N _ _ _ _ A B e
    haveI := B.finrank α
    let f : A.weight α →ₗ[ℂ] B.weight α :=
      (e.toLinearEquiv.toLinearMap.comp (A.weight α).subtype).codRestrict (B.weight α)
        (fun x => e.maps_weight x.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
    intro x y hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    exact e.toLinearEquiv.injective this
  exact le_antisymm (key e) (key e.symm)

/-- The conformal weight of a module is unique. -/
theorem hasConformalWeight_unique {A : OrdVModule W M} {h₁ h₂ : ℂ}
    (h1 : HasConformalWeight A h₁) (h2 : HasConformalWeight A h₂) : h₁ = h₂ :=
  isLowestWeight_unique A h1.1 h1.2 h2.2 h2.1

/-- Conformal weights transport across module isomorphisms. -/
theorem ModuleEquiv.hasConformalWeight {A : OrdVModule W M} {B : OrdVModule W N}
    (e : ModuleEquiv W A B) {h : ℂ} (hA : HasConformalWeight A h) : HasConformalWeight B h :=
  ⟨e.weight_ne_bot hA.1, fun α hα => hA.2 α (e.symm.weight_ne_bot hα)⟩

/-- The weight spaces of the adjoint module at natural weights are the graded pieces. -/
theorem adjointModule_weight_nat (n : ℕ) :
    (adjointModule W).weight (n : ℂ) = W.grading n := by
  change adjWeight W (n : ℂ) = W.grading n
  have : ((n : ℤ) : ℂ) = (n : ℂ) := by push_cast; rfl
  rw [← this, adjWeight_cast]

end Transport

/-! ## §2 The vacuum graded character as an honest convergent sum -/

section Character

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `onePoint N 𝟙` at `h - c/24 + n` is `dim M_{h+n}`. -/
theorem onePoint_vacuum_coeff (N : OrdVModule W M) (h : ℂ) (n : ℕ) :
    onePoint N W.vacuum (h - W.centralCharge / 24 + n) = (finrank ℂ (N.weight (h + n)) : ℂ) := by
  rw [onePoint_vacuum]
  change (finrank ℂ (N.weight (h - W.centralCharge / 24 + n + W.centralCharge / 24)) : ℂ) = _
  rw [show h - W.centralCharge / 24 + n + W.centralCharge / 24 = h + n by ring]

/-- **The character of a module of conformal weight `h` over a `C₂`-cofinite VOA is an honest
convergent `q`-series on `ℍ`**: `Σₙ dim M_{h+n} e^{2πi(h+n-c/24)τ}` has sum the analytic trace
function `qEvalAt (onePoint N 𝟙) (h - c/24) τ`. -/
theorem hasSum_character (N : OrdVModule W M) {h : ℂ} (hcw : HasConformalWeight N h)
    (hC2 : C2Cofinite W) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (finrank ℂ (N.weight (h + n)) : ℂ) *
        cexp (2 * Real.pi * I * (h + n - W.centralCharge / 24) * τ))
      (qEvalAt (torusOnePoint N W.vacuum) (h - W.centralCharge / 24) τ) := by
  have hsub := onePointSubexp_of_c2 W N hcw (vacuumGradeZero_holds (W := W)) hC2 W.vacuum
  have hsum := qSummableAt_of_subexponential (torusOnePoint N W.vacuum)
    (h - W.centralCharge / 24) hsub τ
  have hhs := (hsum.hasSum).mul_left
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (h - W.centralCharge / 24)))
  rw [qEvalAt]
  refine hhs.congr_fun ?_
  intro n
  change _ = _ * (onePoint N W.vacuum _ * _)
  rw [onePoint_vacuum_coeff, qParam, ← Complex.exp_nat_mul, ← mul_assoc,
    mul_comm _ (finrank ℂ _ : ℂ)]
  rw [mul_assoc (finrank ℂ _ : ℂ), ← Complex.exp_add]
  congr 2
  ring

end Character

/-! ## §3 Pinned Zhu modularity for the canonical family, `Pr`-parametric (no `VOA.pbw`) -/

section Zhu

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Zhu's modularity theorem for the canonical family of a `C₂`-cofinite VOA with finite
`Φ V` and semisimple `A(V)`**, with the PBW datum `Pr` explicit (so no project axiom). -/
theorem zhuModularity_canonical_of_Pr [Fintype (Φ W)] [DecidableEq (Φ W)]
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hC2 : C2Cofinite W) (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    ∃ D : ModularData W (Φ W),
      D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧
      ZhuModularityAnalytic D :=
  zhuModularity_pinned_of_C2Cofinite
    (canonicalIrrModule (W := W))
    (fun c => conformalWeightOf (canonicalIrrModule c))
    hC2 hss Pr canonicalIrrFamily_card canonicalIrrFamily_hasConformalWeight
    (fun _ _ hjk _ => canonicalIrrFamily_bottomSeparated_of_Pr Pr hjk)

end Zhu

/-! ## §4 The named inputs -/

/-- **PBW bottom input** (Dong–Li–Mason 1998, Thm 4.1 / the PBW theorem): the regular
`A(V)`-module has a bottom projection in its level-zero induced module. Equivalent to injectivity of
the bottom map (`nonempty_bottomProjection_iff_bottom_injective`). -/
def ZhuPBWBottomInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    Nonempty (BottomProjection (parabolicRepOfAMod W (regularAMod W)))

/-- The theorem `VOA.pbw` implies the PBW bottom input. -/
theorem zhuPBWBottomInput_of_pbw : ZhuPBWBottomInput.{u} :=
  fun _ _ _ W => ⟨voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))⟩

/-- **Rationality of conformal weights** (Dong–Li–Mason, *Modular-invariance of trace functions
in orbifold theory and generalized Moonshine*, CMP 214 (2000), Thm 11.3; Anderson–Moore 1988):
for a strongly rational VOA every irreducible ordinary module has a rational conformal weight. -/
def DLMRationalWeightsInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M),
      N.IsIrreducible → ∀ h : ℂ, HasConformalWeight N h → ∃ q : ℚ, (q : ℂ) = h

/-- The quantum dimension read off the `S`-matrix, `d_a = S_{a0}/S_{00}` (real part). -/
def qdimOf {ι : Type w} (S : ι → ι → ℂ) (v0 a : ι) : ℝ := (S a v0 / S v0 v0).re

/-- The positivity package of the `S`-matrix at vacuum label `v0`
(GR (2.8) with `ε = +1`, the remark after GR Def. 2.4, and GR (2.35)). -/
structure SPositivity {ι : Type w} (S : ι → ι → ℂ) (v0 : ι) : Prop where
  vac_real : (S v0 v0).im = 0
  vac_pos : 0 < (S v0 v0).re
  symm_vac : ∀ a, S v0 a = S a v0
  qdim_real : ∀ a, (S a v0 / S v0 v0).im = 0
  qdim_ge_one : ∀ a, 1 ≤ qdimOf S v0 a
  bound : ∀ a b, ‖S a b‖ ≤ (S v0 v0).re * qdimOf S v0 a * qdimOf S v0 b

/-- **Huang's positivity input.** For a nice VOA, the `S`-matrix `ρ(S)` of *any* Zhu modular
data on a complete, irredundant family of irreducibles satisfies `SPositivity` at the vacuum label.

*Source.* Zhu/DLM: the trace functions of a complete irredundant family are linearly independent,
so `ρ(S)` is the unique `S`-matrix of `V`. Huang (2008): `Rep V` is modular, `ρ(S)` is symmetric
and equals the categorical `S̃` up to normalisation, with `S_{a0}/S_{00} = dim(a)`. Pseudo-unitarity
(the vacuum is the unique lowest weight) gives positive categorical dimensions equal to the
Frobenius–Perron ones, hence `d_a ≥ 1` (ENO 2005; GR refs [70, 71]) and `S_{00} > 0`. The bound is
Gannon, *Modular data* (2005), (4.2a), quoted as GR (2.35).

*Not vacuous.* `ρ(S)` is pinned by `ZhuModularityAnalytic` together with trace-function
independence; the conclusion constrains the actual matrix. -/
def HuangSPositivityInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        SPositivity D.repS v0

/-! ## §5 The bridge -/

section Bridge

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The adjoint module of a simple VOA, as a bundled irreducible. -/
def adjointIrr (W : VertexOperatorAlgebra 𝒱) (hs : W.IsSimple) : IrrModule W where
  carrier := 𝒱
  isMod := adjointModule W
  irreducible := (isSimple_iff_adjointModule_isIrreducible W).1 hs

/-- The canonical representative of the vacuum class has conformal weight `0`. -/
theorem conformalWeightOf_vacuumClass (W : VertexOperatorAlgebra 𝒱) (hs : W.IsSimple) :
    conformalWeightOf (canonicalIrrModule (adjointIrr W hs).toΦ) = 0 := by
  obtain ⟨f⟩ : IrrModule.Iso W (canonicalIrrModule (adjointIrr W hs).toΦ) (adjointIrr W hs) :=
    Quotient.exact (canonicalIrrModule_toΦ (adjointIrr W hs).toΦ)
  exact hasConformalWeight_unique
    (ModuleEquiv.hasConformalWeight f (hasConformalWeight_conformalWeightOf _))
    (hasConformalWeight_adjoint W hs.vacuum_ne_zero)

/-- **`IModData` from Zhu's theorem plus three named literature inputs.**

Proved here: the classification clauses, character convergence, the vacuum character, and the
`S`-transformation of characters (from the library's Zhu modularity theorem at `γ = S`). -/
theorem iModData_of_inputs
    (hPBW : ZhuPBWBottomInput.{u}) (hRat : DLMRationalWeightsInput.{u})
    (hPos : HuangSPositivityInput.{u, u + 1}) : IModData.{u} := by
  classical
  intro 𝒱 _ _ W hNice
  have hSR : StronglyRational W := hNice.1
  obtain ⟨Pr⟩ := hPBW 𝒱 W
  have hss := isSemisimpleRing_A_of_admissiblyRational Pr hSR.rational
  haveI hfinΦ : Finite (Φ W) := finite_Φ_of_C2Cofinite Pr hSR.c2Cofinite hss
  letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
  obtain ⟨D, hM, hh, hZ⟩ :=
    zhuModularity_canonical_of_Pr (W := W) Pr hSR.c2Cofinite hss
  -- indexing by `Fin n`
  let e : Φ W ≃ Fin (Fintype.card (Φ W)) := Fintype.equivFin (Φ W)
  let X0 : IrrModule W := adjointIrr W hSR.simple
  let c0 : Φ W := X0.toΦ
  -- rational weights
  have hq : ∀ c : Φ W, ∃ q : ℚ, (q : ℂ) = conformalWeightOf (canonicalIrrModule c) := fun c =>
    hRat 𝒱 W hSR _ (canonicalIrrModule c).isMod (canonicalIrrModule c).irreducible _
      (hasConformalWeight_conformalWeightOf _)
  choose q hqc using hq
  have hcw : ∀ c : Φ W, HasConformalWeight (canonicalIrrModule c).isMod (q c) := fun c => by
    rw [hqc]; exact hasConformalWeight_conformalWeightOf _
  -- the character
  let ch : Fin (Fintype.card (Φ W)) → ℂ → ℂ := fun a τ =>
    if hτ : 0 < τ.im then traceFun D.Mfam D.h (e.symm a) W.vacuum ⟨τ, hτ⟩ else 0
  have hch : ∀ a (τ : ℂ) (hτ : 0 < τ.im),
      ch a τ = qEvalAt (torusOnePoint (canonicalIrrModule (e.symm a)).isMod W.vacuum)
        ((q (e.symm a) : ℂ) - W.centralCharge / 24) ⟨τ, hτ⟩ := by
    intro a τ hτ
    simp only [ch, dif_pos hτ, traceFun, hh, hqc]
    rw [hM]
  -- the Huang package
  have hirr := (canonicalIrrFamily_irredundant_complete (W := W))
  have hvac : Nonempty (ModuleEquiv W (D.Mfam c0).isMod (adjointModule W)) := by
    rw [hM]; exact Quotient.exact (canonicalIrrModule_toΦ c0)
  have hP : SPositivity D.repS c0 :=
    hPos 𝒱 W hNice (Φ W) D hZ (by rw [hM]; exact hirr.1) (by rw [hM]; exact hirr.2) c0 hvac
  have hS00ne : D.repS c0 c0 ≠ 0 := by
    intro h0; have := hP.vac_pos; rw [h0] at this; simp at this
  have hS00 : ((D.repS c0 c0).re : ℂ) = D.repS c0 c0 :=
    Complex.ext (by simp) (by simp [hP.vac_real])
  have hSd : ∀ a, ((D.repS c0 c0).re : ℂ) * (qdimOf D.repS c0 a : ℂ) = D.repS a c0 := by
    intro a
    have hd : ((qdimOf D.repS c0 a : ℝ) : ℂ) = D.repS a c0 / D.repS c0 c0 :=
      Complex.ext (by simp [qdimOf]) (by simp [hP.qdim_real a])
    rw [hS00, hd]; field_simp
  refine ⟨{
    ι := Fin (Fintype.card (Φ W))
    vac := e c0
    carrier := fun a => (canonicalIrrModule (e.symm a)).carrier
    module := fun a => (canonicalIrrModule (e.symm a)).isMod
    h := fun a => q (e.symm a)
    ch := ch
    S := fun a b => D.repS (e.symm a) (e.symm b)
    S00 := (D.repS c0 c0).re
    d := fun a => qdimOf D.repS c0 (e.symm a) }, ?_⟩
  -- the `char` clause, used twice
  have hchar : ∀ (a : Fin (Fintype.card (Φ W))) (τ : ℂ), 0 < τ.im →
      HasSum (fun n : ℕ =>
        (finrank ℂ ((canonicalIrrModule (e.symm a)).isMod.weight ((q (e.symm a) : ℂ) + n)) : ℂ) *
          cexp (2 * Real.pi * I * ((q (e.symm a) : ℂ) + n - W.centralCharge / 24) * τ))
        (ch a τ) := by
    intro a τ hτ
    rw [hch a τ hτ]
    exact hasSum_character _ (hcw (e.symm a)) hSR.c2Cofinite ⟨τ, hτ⟩
  have hq0 : (q c0 : ℂ) = 0 := by rw [hqc]; exact conformalWeightOf_vacuumClass W hSR.simple
  refine
    { irred := fun a => (canonicalIrrModule (e.symm a)).irreducible
      exhaust := ?_
      distinct := ?_
      vac_iso := ?_
      weight_support := ?_
      weight_lowest := fun a => (hcw (e.symm a)).1
      h_vac := ?_
      char := hchar
      char_vac := ?_
      S_transform := ?_
      S_pinned := ?_
      S00_pos := hP.vac_pos
      S_vac_vac := ?_
      d_ge_one := fun a => hP.qdim_ge_one (e.symm a)
      S_vac_left := ?_
      S_vac_right := ?_
      S_bound := fun a b => ?_ }
  · -- exhaust
    intro M _ _ N hN
    let X : IrrModule W := ⟨M, N, hN⟩
    refine ⟨e X.toΦ, ?_⟩
    change Nonempty (ModuleEquiv W N (canonicalIrrModule (e.symm (e X.toΦ))).isMod)
    rw [Equiv.symm_apply_apply]
    obtain ⟨f⟩ : IrrModule.Iso W (canonicalIrrModule X.toΦ) X :=
      Quotient.exact (canonicalIrrModule_toΦ X.toΦ)
    exact ⟨f.symm⟩
  · -- distinct
    intro a b ⟨f⟩
    have h1 : (canonicalIrrModule (e.symm a)).toΦ = (canonicalIrrModule (e.symm b)).toΦ :=
      Quotient.sound ⟨f⟩
    simp only [canonicalIrrModule_toΦ] at h1
    exact e.symm.injective h1
  · -- vac_iso
    change Nonempty (ModuleEquiv W (canonicalIrrModule (e.symm (e c0))).isMod (adjointModule W))
    rw [Equiv.symm_apply_apply]
    exact Quotient.exact (canonicalIrrModule_toΦ c0)
  · -- weight_support
    intro a α hα
    exact (hcw (e.symm a)).2 α hα
  · -- h_vac
    change q (e.symm (e c0)) = 0
    rw [Equiv.symm_apply_apply]
    exact_mod_cast hq0
  · -- char_vac
    intro τ hτ
    have h := hchar (e c0) τ hτ
    have hv : e.symm (e c0) = c0 := Equiv.symm_apply_apply _ _
    obtain ⟨f⟩ : Nonempty (ModuleEquiv W (canonicalIrrModule (e.symm (e c0))).isMod
        (adjointModule W)) := by
      rw [hv]; exact Quotient.exact (canonicalIrrModule_toΦ c0)
    refine h.congr_fun (fun n => ?_)
    have hq0' : (q (e.symm (e c0)) : ℂ) = 0 := by rw [hv]; exact hq0
    rw [hq0', zero_add, ModuleEquiv.finrank_weight_eq f, adjointModule_weight_nat]
  · -- S_transform
    intro a τ hτ
    have hτ' : 0 < (-1 / τ).im := by
      have := (ModularGroup.S • (⟨τ, hτ⟩ : UpperHalfPlane)).im_pos
      rw [UpperHalfPlane.modular_S_smul] at this
      rw [div_eq_mul_inv, neg_one_mul, ← inv_neg]
      exact this
    have hSτ : (ModularGroup.S • (⟨τ, hτ⟩ : UpperHalfPlane)) = ⟨-1 / τ, hτ'⟩ := by
      ext; rw [UpperHalfPlane.modular_S_smul]; change (-τ)⁻¹ = -1 / τ; field_simp
    have hlaw := hZ ModularGroup.S 0 W.vacuum (vacuum_mem_sqWeightSpace_zero W) (e.symm a)
      ⟨τ, hτ⟩
    rw [hSτ, pow_zero, one_mul, D.rep_S] at hlaw
    change ch a (-1 / τ) = ∑ b, D.repS (e.symm a) (e.symm b) * ch b τ
    simp only [ch, dif_pos hτ', dif_pos hτ]
    rw [hlaw]
    exact (Equiv.sum_comp e.symm _).symm
  · -- S_pinned: Zhu's law at `γ = S` on every square-bracket homogeneous state
    intro n v hv a τ
    have hlaw := hZ ModularGroup.S n v hv (e.symm a) τ
    have hA : autFactor ModularGroup.S τ = τ := by simp [autFactor, ModularGroup.S]
    rw [hA, D.rep_S] at hlaw
    simp only [traceFun, hh, Matrix.of_apply] at hlaw
    rw [hM] at hlaw
    change qEvalAt (onePoint (canonicalIrrModule (e.symm a)).isMod v)
        ((q (e.symm a) : ℂ) - W.centralCharge / 24) (ModularGroup.S • τ) =
      (τ : ℂ) ^ n * ∑ b, D.repS (e.symm a) (e.symm b) *
        qEvalAt (onePoint (canonicalIrrModule (e.symm b)).isMod v)
          ((q (e.symm b) : ℂ) - W.centralCharge / 24) τ
    simp only [hqc]
    refine hlaw.trans ?_
    congr 1
    exact (Equiv.sum_comp e.symm (fun j => D.repS (e.symm a) j *
      qEvalAt (torusOnePoint (canonicalIrrModule j).isMod v)
        (conformalWeightOf (canonicalIrrModule j) - W.centralCharge / 24) τ)).symm
  · -- S_vac_vac
    change D.repS (e.symm (e c0)) (e.symm (e c0)) = _
    rw [Equiv.symm_apply_apply, hS00]
  · -- S_vac_left
    intro a
    change D.repS (e.symm (e c0)) (e.symm a) = _
    rw [Equiv.symm_apply_apply, hP.symm_vac]
    exact (hSd (e.symm a)).symm
  · -- S_vac_right
    intro a
    change D.repS (e.symm a) (e.symm (e c0)) = _
    rw [Equiv.symm_apply_apply]
    exact (hSd (e.symm a)).symm
  · exact hP.bound (e.symm a) (e.symm b)

/-- `iModData_of_inputs` with the PBW input discharged by the theorem `VOA.pbw`. -/
theorem iModData_of_pbw_inputs (hRat : DLMRationalWeightsInput.{u})
    (hPos : HuangSPositivityInput.{u, u + 1}) : IModData.{u} :=
  iModData_of_inputs zhuPBWBottomInput_of_pbw hRat hPos

end Bridge

end VOA.Huang.ZhuModData
