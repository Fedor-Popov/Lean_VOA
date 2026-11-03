/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorHL6
import VOA.Huang.PzTensorSemisimple
import VOA.Huang.PzTensorCommutator
import VOA.Huang.ModuleC2Main
import VOA.Modularity.LowestWeightExistence

/-!
# The decomposition of `Λ` (`CoefSpanDecomp`)

Let `Λ = coefSpan 𝒴₁ 𝒴₂` with its weak-module structure `wΛ` (the Huang–Lepowsky action `τ`;
`PzTensorSpan.weakModuleS` with the proved commutator and associator inputs).

* `wΛ_compl` — ABD Prop. 5.7 makes `wΛ` admissible, so rationality
  (`StronglyRational.rational`) makes every weak submodule complemented; by `PzTensorSemisimple`
  `Λ` is a semisimple module over its mode algebra.
* `IrrSubOrdinary A` (named, abstract) — irreducible weak submodules of `A` are ordinary; implied by
  ABD Cor. 5.8 (`irrSubOrdinary_of_ABD`) and by ABD Prop. 5.7 + DLM Thm. 8.1(c)
  (`irrSubOrdinary_of_DLM`).  Under it every simple summand is an irreducible lowest-weight module
  (`lwOf`, `lwOf_irr`).
* `BoundedMult A` (named, abstract) — independent families of equivariant maps from an irreducible
  `R` into `M` have bounded size.  `boundedMult_wΛ` — **proved for `Λ`**: independent
  equivariant `ψ_k : R → Λ` give independent intertwining operators `𝒴₄(ψ_k)` of type
  `(R' / P₁ P₂)` (`sum_psi_eq_zero_of_Y4`, via `pair_Y4`), and the fusion rules are finite
  (`finiteDimensional_intertwiningSpace_of_stronglyRational`, proved).
* `finite_of_indep` — with finitely many irreducible modules (`Finite (Φ W)`) and bounded
  multiplicities, every independent family of simple submodules is finite (an infinite one has an
  infinite isomorphism-class fibre, whose embeddings are linearly independent).
* `exists_decomp` — the finite decomposition with equivariant `ψ j`, `χ j`, `Σ ψ j χ j = id`.
* `coefSpanDecomp_of_irrSub`, `coefSpanDecomp_of_citations : StronglyRational W →
  ABDWeakIsAdmissible W → ABDIrreducibleWeakIsOrdinary W → Finite (Φ W) → CoefSpanDecomp W`,
  `coefSpanDecomp_of_DLM` (ABD Prop. 5.7 + DLM Thm. 8.1(b), (c)), and the corresponding
  `associativityInput_of_citations`, `associativityInput_of_DLM`.

The hypotheses beyond `StronglyRational` are library citations, all TRUE for strongly rational
`W`: Abe–Buhl–Dong Prop. 5.7 / Cor. 5.8 (TAMS 356 (2004)), and finiteness of the set of
irreducible modules (Dong–Li–Mason, Math. Ann. 310 (1998) Thm. 8.1(b); `Finite (Φ W)` is implied
by `DLMFinitelyManyIrredAdmissible` via `finite_Φ_of_finite_Φadm`).  The results are therefore
`#print axioms`-clean **conditional on** these citations; they are not unconditional.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorDecomp

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.LogRemovalSemisimple VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.PzTensorSpan VOA.Huang.PzTensorY4 VOA.Huang.PzTensorY3
open VOA.Huang.PzTensorHL6 VOA.Huang.PzTensorSemisimple VOA.Huang.HuangODEContra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Independence: a vanishing sum has vanishing terms -/

theorem eq_zero_of_sum_indep {R N ι : Type*} [Ring R] [AddCommGroup N] [Module R N] [Fintype ι]
    {p : ι → Submodule R N} (hp : iSupIndep p) {w : ι → N}
    (hw : ∀ i, w i ∈ p i) (hs : ∑ i, w i = 0) (j : ι) : w j = 0 := by
  classical
  have h1 : w j = -∑ i ∈ Finset.univ.erase j, w i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have h2 : -∑ i ∈ Finset.univ.erase j, w i ∈ ⨆ (i) (_ : i ≠ j), p i := by
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hi) (hw i))
  rw [← h1] at h2
  exact Submodule.disjoint_def.mp (hp j) (w j) (hw j) h2

/-! ## Simple summands as irreducible lowest-weight modules -/

section Ordinary

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)

/-- **Irreducible stable subspaces are ordinary** (named; the input needed of `M`): every
irreducible weak submodule of `A` carries an ordinary (`ℂ`-graded, finite-dimensional weight
spaces, bounded below) module structure with the same modes.  Implied by Abe–Buhl–Dong Cor. 5.8
(`irrSubOrdinary_of_ABD`, `C₂`-cofinite `V`, any `A`) and by ABD Prop. 5.7 + Dong–Li–Mason
Thm. 8.1(c) (`irrSubOrdinary_of_DLM`, rational `V`). -/
def IrrSubOrdinary : Prop :=
  ∀ (N : Submodule ℂ M) (hN : Stable A N),
    (Nontrivial N ∧ ∀ P : WeakModule.Submodule' (restrict A N hN), P.carrier = ⊥ ∨ P.carrier = ⊤) →
    ∃ O : OrdVModule W N, O.toWeakModule = restrict A N hN

theorem irrSubOrdinary_of_ABD (hOrd : ABDIrreducibleWeakIsOrdinary W) (hC2 : C2Cofinite W) :
    IrrSubOrdinary A :=
  fun _ _ hirr => hOrd hC2 _ hirr

theorem irrSubOrdinary_of_DLM (hR : AdmissiblyRational W) (hABD : ABDWeakIsAdmissible W)
    (hC2 : C2Cofinite W) (hDLM : DLMSimpleAdmissibleOrdinary W) : IrrSubOrdinary A := by
  intro N hN hirr
  obtain ⟨Nadm, hNadm⟩ := hABD hC2 (restrict A N hN)
  have hirr' : Nadm.IsIrreducible := by
    refine ⟨hirr.1, ?_⟩
    rw [hNadm]
    exact hirr.2
  obtain ⟨O, hO⟩ := hDLM hR Nadm hirr'
  exact ⟨O, hO.trans hNadm⟩

end Ordinary

section Summand

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
  (hOrd : IrrSubOrdinary A)
  (N : Submodule (modeAlg A) M) (hN : IsAtom N)

include hOrd hN in
theorem exists_ord_of_atom :
    ∃ O : OrdVModule W (N.restrictScalars ℂ),
      O.toWeakModule = restrict A (N.restrictScalars ℂ) (stable_of_sub A N) :=
  hOrd _ (stable_of_sub A N) (irreducible_restrict_of_atom A N hN)

/-- The ordinary structure on a simple summand (ABD Cor. 5.8). -/
noncomputable def ordOf : OrdVModule W (N.restrictScalars ℂ) :=
  Classical.choose (exists_ord_of_atom A hOrd N hN)

theorem ordOf_spec :
    (ordOf A hOrd N hN).toWeakModule = restrict A (N.restrictScalars ℂ) (stable_of_sub A N) :=
  Classical.choose_spec (exists_ord_of_atom A hOrd N hN)

theorem ordOf_irreducible : (ordOf A hOrd N hN).IsIrreducible := by
  have h := irreducible_restrict_of_atom A N hN
  refine ⟨h.1, ?_⟩
  rw [ordOf_spec]
  exact h.2

theorem ordOf_mode (u : 𝒱) (n : ℤ) (x : N.restrictScalars ℂ) :
    ((mode ((ordOf A hOrd N hN).YM u) n x : N.restrictScalars ℂ) : M) = mode (A.YM u) n x := by
  rw [ordOf_spec]
  rfl

/-- The summand as a bundled irreducible lowest-weight module. -/
noncomputable def lwOf : LWModule W where
  carrier := N.restrictScalars ℂ
  isMod := ordOf A hOrd N hN
  h := Classical.choose
    (OrdVModule.exists_isLowestWeight_of_irreducible _ (ordOf_irreducible A hOrd N hN))
  isLow := (Classical.choose_spec
    (OrdVModule.exists_isLowestWeight_of_irreducible _ (ordOf_irreducible A hOrd N hN))).1
  realized := (Classical.choose_spec
    (OrdVModule.exists_isLowestWeight_of_irreducible _ (ordOf_irreducible A hOrd N hN))).2

theorem lwOf_irr : (lwOf A hOrd N hN).IsIrreducibleLW := ordOf_irreducible A hOrd N hN

/-- The summand as a bundled irreducible module (for `Φ`). -/
noncomputable def irrOf : IrrModule W where
  carrier := N.restrictScalars ℂ
  isMod := ordOf A hOrd N hN
  irreducible := ordOf_irreducible A hOrd N hN

/-- The equivariance of the embedding of a summand `N₀ ≅ N ⊆ M`. -/
theorem psi_equiv {N₀ : Submodule (modeAlg A) M} (h₀ : IsAtom N₀)
    (e : ModuleEquiv W (ordOf A hOrd N₀ h₀) (ordOf A hOrd N hN))
    (u : 𝒱) (k : ℤ) (v : N₀.restrictScalars ℂ) :
    ((N.restrictScalars ℂ).subtype ∘ₗ e.toLinearEquiv.toLinearMap)
        (mode ((ordOf A hOrd N₀ h₀).YM u) k v)
      = mode (A.YM u) k (((N.restrictScalars ℂ).subtype ∘ₗ e.toLinearEquiv.toLinearMap) v) := by
  have h1 := e.map_act u k v
  simp only [WeakModule.act_def] at h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
  rw [h1, ordOf_mode]

end Summand

/-! ## Finiteness and the finite decomposition (abstract) -/

section Abstract

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
  (hOrd : IrrSubOrdinary A)

/-- **Bounded multiplicities** (abstract input): for every irreducible lowest-weight `R`, the
linearly independent families of `V`-equivariant maps `R → M` have bounded size. -/
def BoundedMult : Prop :=
  ∀ R : LWModule W, R.IsIrreducibleLW → ∃ d : ℕ, ∀ (n : ℕ) (ψ : Fin n → R.carrier →ₗ[ℂ] M),
    (∀ k (u : 𝒱) (m : ℤ) (v : R.carrier),
      ψ k (mode (R.isMod.YM u) m v) = mode (A.YM u) m (ψ k v)) →
    LinearIndependent ℂ ψ → n ≤ d

include hOrd in
/-- **Finiteness**: with finitely many irreducible modules and bounded multiplicities,
every independent family of simple submodules is finite. -/
theorem finite_of_indep (hΦ : Finite (Φ W)) (hB : BoundedMult A)
    (s : Set (Submodule (modeAlg A) M)) (hind : sSupIndep s) (hat : ∀ m ∈ s, IsAtom m) :
    s.Finite := by
  classical
  by_contra hinf
  haveI : Infinite s := Set.infinite_coe_iff.mpr hinf
  let cls : s → Φ W := fun m =>
    Quotient.mk (IrrModule.setoid W) (irrOf A hOrd m.1 (hat m.1 m.2))
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber cls
  let emb := Infinite.natEmbedding (cls ⁻¹' {c})
  let m₀ : s := (emb 0).1
  have h₀ : IsAtom m₀.1 := hat m₀.1 m₀.2
  obtain ⟨d, hd⟩ := hB (lwOf A hOrd m₀.1 h₀) (lwOf_irr A hOrd m₀.1 h₀)
  let g : Fin (d + 1) → s := fun k => (emb k.1).1
  have hg : Function.Injective g := fun a b hab =>
    Fin.ext (emb.injective (Subtype.ext hab))
  have hcls : ∀ k, cls (g k) = cls m₀ := fun k => by
    have h1 : cls (g k) = c := (emb k.1).2
    have h2 : cls m₀ = c := (emb 0).2
    rw [h1, h2]
  have hiso : ∀ k, Nonempty (ModuleEquiv W (ordOf A hOrd m₀.1 h₀)
      (ordOf A hOrd (g k).1 (hat _ (g k).2))) := fun k =>
    Quotient.exact (hcls k).symm
  let e : ∀ k, ModuleEquiv W (ordOf A hOrd m₀.1 h₀)
      (ordOf A hOrd (g k).1 (hat _ (g k).2)) := fun k => Classical.choice (hiso k)
  let ψ : Fin (d + 1) → (lwOf A hOrd m₀.1 h₀).carrier →ₗ[ℂ] M := fun k =>
    ((g k).1.restrictScalars ℂ).subtype ∘ₗ (e k).toLinearEquiv.toLinearMap
  have hψ : ∀ k (u : 𝒱) (m : ℤ) (v : (lwOf A hOrd m₀.1 h₀).carrier),
      ψ k (mode ((lwOf A hOrd m₀.1 h₀).isMod.YM u) m v) = mode (A.YM u) m (ψ k v) :=
    fun k u m v => psi_equiv A hOrd (g k).1 (hat _ (g k).2) h₀ (e k) u m v
  have hli : LinearIndependent ℂ ψ := by
    rw [Fintype.linearIndependent_iff]
    intro cf hsum k
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (lwOf A hOrd m₀.1 h₀).realized
    have hs : ∑ j, cf j • ψ j v = 0 := by
      have := congrArg (fun F : (lwOf A hOrd m₀.1 h₀).carrier →ₗ[ℂ] M => F v) hsum
      simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        LinearMap.zero_apply] using this
    have hindg : iSupIndep fun j => (g j).1 := ((sSupIndep_iff s).mp hind).comp hg
    have hz := eq_zero_of_sum_indep hindg (w := fun j => cf j • ψ j v)
      (fun j => ((g j).1.restrictScalars ℂ).smul_mem (cf j) ((e j).toLinearEquiv v).2) hs k
    rcases smul_eq_zero.mp hz with h | h
    · exact h
    · exfalso
      apply hv0
      have h' : ((e k).toLinearEquiv v : (g k).1.restrictScalars ℂ) = 0 := Subtype.ext h
      exact (e k).toLinearEquiv.map_eq_zero_iff.mp h'
  have := hd (d + 1) ψ hψ hli
  omega

include hOrd in
/-- **The finite decomposition of a completely reducible weak module** into irreducible
lowest-weight modules, with equivariant embeddings `ψ j`, projections `χ j`, `Σ ψ j χ j = id`. -/
theorem exists_decomp (hΦ : Finite (Φ W)) (hB : BoundedMult A)
    (hCR : ∀ P : WeakModule.Submodule' A, ∃ Q : WeakModule.Submodule' A,
      IsCompl P.carrier Q.carrier) :
    ∃ (r : ℕ) (R : Fin r → LWModule W) (_ : ∀ j, (R j).IsIrreducibleLW)
      (ψ : ∀ j, (R j).carrier →ₗ[ℂ] M) (χ : ∀ j, M →ₗ[ℂ] (R j).carrier),
      (∀ j (u : 𝒱) (m : ℤ) (v : (R j).carrier),
        ψ j (mode ((R j).isMod.YM u) m v) = mode (A.YM u) m (ψ j v)) ∧
      (∀ j (u : 𝒱) (m : ℤ) (x : M),
        χ j (mode (A.YM u) m x) = mode ((R j).isMod.YM u) m (χ j x)) ∧
      ∀ x : M, ∑ j, ψ j (χ j x) = x := by
  haveI := isSemisimpleModule_of_compl A hCR
  obtain ⟨r, S, π, hat, _, hmem, hcomm, hsum⟩ :=
    exists_finite_decomp A (finite_of_indep A hOrd hΦ hB)
  refine ⟨r, fun j => lwOf A hOrd (S j) (hat j), fun j => lwOf_irr A hOrd (S j) (hat j),
    fun j => ((S j).restrictScalars ℂ).subtype,
    fun j => LinearMap.codRestrict ((S j).restrictScalars ℂ) (π j) (hmem j), ?_, ?_, hsum⟩
  · intro j u m v
    exact ordOf_mode A hOrd (S j) (hat j) u m v
  · intro j u m x
    apply Subtype.ext
    refine (hcomm j u m x).trans ?_
    exact (ordOf_mode A hOrd (S j) (hat j) u m
      (LinearMap.codRestrict ((S j).restrictScalars ℂ) (π j) (hmem j) x)).symm

end Abstract

/-! ## The weak module `Λ` -/

section Lambda

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂

/-- **`Λ` as a weak module** (the Huang–Lepowsky action, all inputs proved). -/
noncomputable def wΛ : WeakModule W (coefSpan Y₁ Y₂) :=
  weakModuleS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (PzTensorCommutator.tauCommutator_holds P₁ P₂)
    (PzTensorHatBridge.tauAssociator_holds hV)

theorem wΛ_mode_coe {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (n : ℤ) (G : coefSpan Y₁ Y₂) :
    ((mode ((wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂).YM u) n G : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
      = tauHom hu n (G : HomPair P₁ P₂ → ℂ) :=
  mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu n G

/-- **Complete reducibility of `Λ`** (ABD + rationality). -/
theorem wΛ_compl (hABD : ABDWeakIsAdmissible W) :
    ∀ P : WeakModule.Submodule' (wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂),
      ∃ Q : WeakModule.Submodule' (wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂), IsCompl P.carrier Q.carrier := by
  obtain ⟨N, hN⟩ := hABD hV.c2Cofinite (wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂)
  have h : ∀ P : WeakModule.Submodule' N.toWeakModule,
      ∃ Q : WeakModule.Submodule' N.toWeakModule, IsCompl P.carrier Q.carrier := hV.rational N
  rw [hN] at h
  exact h

/-- The embedding relation recovered from a relation among the `𝒴₄`'s (`pair_Y4`). -/
theorem sum_psi_eq_zero_of_Y4 {R : LWModule W} {n : ℕ}
    (ψ : Fin n → R.carrier →ₗ[ℂ] coefSpan Y₁ Y₂)
    (hψ : ∀ k (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (m : ℤ) (v : R.carrier),
      ((ψ k (mode (R.isMod.YM u) m v) : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
        = tauHom hu m ((ψ k v : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ))
    (cf : Fin n → ℂ)
    (hc : ∑ k, cf k • Y4 (tauEmb_of_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (ψ k) (hψ k)) = 0)
    (γ : ℂ) (v : R.carrier) (hv : v ∈ R.isMod.weight γ) :
    ∑ k, cf k • ψ k v = 0 := by
  apply Subtype.ext
  funext x
  have hs := congrArg (fun Z : IntertwiningModes P₁.carrier P₂.carrier (RestrictedDual R.isMod) =>
    dualPairing R.isMod v (Z (x.α₁ + x.α₂ - γ - 1) x.w₁ x.w₂)) hc
  simp only [Finset.sum_apply, Pi.smul_apply, LinearMap.coe_sum, LinearMap.smul_apply,
    map_sum, map_smul, smul_eq_mul, Pi.zero_apply, LinearMap.zero_apply, map_zero] at hs
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
  rw [← hs]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pair_Y4 _ _ hv x.h₁ x.h₂, if_pos (by ring)]
  rfl

/-- **Bounded multiplicities in `Λ`** from the finiteness of the fusion rules: independent
equivariant maps `R → Λ` give independent intertwining operators `𝒴₄` of type `(R' / P₁ P₂)`. -/
theorem boundedMult_wΛ : BoundedMult (wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) := by
  intro R iR
  haveI : FiniteDimensional ℂ (intertwiningSpace P₁.isMod P₂.isMod (contraLW R).isMod) :=
    VOA.Huang.ModuleC2.finiteDimensional_intertwiningSpace_of_stronglyRational hV i₁ i₂
      (contraLW_isIrreducibleLW iR)
  refine ⟨Module.finrank ℂ (intertwiningSpace P₁.isMod P₂.isMod (contraLW R).isMod),
    fun n ψ hψ hli => ?_⟩
  have hψ' : ∀ k (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (m : ℤ) (v : R.carrier),
      ((ψ k (mode (R.isMod.YM u) m v) : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
        = tauHom hu m ((ψ k v : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ) := fun k β u hu m v => by
    rw [hψ k u m v]
    exact wΛ_mode_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu m _
  let F : Fin n → intertwiningSpace P₁.isMod P₂.isMod (contraLW R).isMod := fun k =>
    ⟨Y4 (tauEmb_of_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (ψ k) (hψ' k)),
      isIntertwining_Y4 (tauEmb_of_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (ψ k) (hψ' k))⟩
  have hliF : LinearIndependent ℂ F := by
    rw [Fintype.linearIndependent_iff]
    intro cf hc0
    have hc : ∑ k, cf k • Y4 (tauEmb_of_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (ψ k) (hψ' k)) = 0 := by
      have := congrArg Subtype.val hc0
      simpa only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero] using this
    have hzero : ∑ k, cf k • ψ k = 0 := by
      ext1 v
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
      refine Submodule.iSup_induction R.isMod.weight
        (motive := fun v => ∑ k, cf k • ψ k v = 0)
        (PzTensorHatBridge.mem_iSup_weight R v) ?_ ?_ ?_
      · intro γ v hv
        exact sum_psi_eq_zero_of_Y4 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ ψ hψ' cf hc γ v hv
      · simp
      · intro x y hx hy
        simp only [map_add, smul_add, Finset.sum_add_distrib, hx, hy, add_zero]
    exact Fintype.linearIndependent_iff.mp hli cf hzero
  have := hliF.fintype_card_le_finrank
  simpa only [Fintype.card_fin] using this

end Lambda

/-! ## Assembly -/

/-- **`CoefSpanDecomp` from ABD, ordinarity of irreducible weak submodules, and finitely many
irreducibles.**  Everything else (complete reducibility from rationality, the semisimple-module
decomposition, the bound on multiplicities from finite fusion rules) is proved. -/
theorem coefSpanDecomp_of_irrSub (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hOrd : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M), IrrSubOrdinary A)
    (hΦ : Finite (Φ W)) : CoefSpanDecomp W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, R, iR, ψ, χ, hψ, hχ, hsum⟩ :=
    exists_decomp (wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) (hOrd _) hΦ
      (boundedMult_wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) (wΛ_compl hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hABD)
  refine ⟨r, R, iR, ψ, χ, fun j β u hu k v => ?_, fun j G β u hu k hm => ?_, hsum⟩
  · rw [hψ j u k v]
    exact wΛ_mode_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu k _
  · have e : (⟨tauHom hu k (G : HomPair P₁ P₂ → ℂ), hm⟩ : coefSpan Y₁ Y₂)
        = mode ((wΛ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂).YM u) k G :=
      Subtype.ext (wΛ_mode_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu k G).symm
    rw [e, hχ j u k G]

/-- **`CoefSpanDecomp` from the library citations** ABD Prop. 5.7 and Cor. 5.8 and
`Finite (Φ W)`. -/
theorem coefSpanDecomp_of_citations (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hOrd : ABDIrreducibleWeakIsOrdinary W) (hΦ : Finite (Φ W)) : CoefSpanDecomp W :=
  coefSpanDecomp_of_irrSub hV hABD (fun A => irrSubOrdinary_of_ABD A hOrd hV.c2Cofinite) hΦ

/-- **`CoefSpanDecomp` from the Dong–Li–Mason citations** (Thm. 8.1(b), (c)) and ABD
Prop. 5.7. -/
theorem coefSpanDecomp_of_DLM (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hDLMc : DLMSimpleAdmissibleOrdinary W) (hDLMb : DLMFinitelyManyIrredAdmissible W) :
    CoefSpanDecomp W :=
  coefSpanDecomp_of_irrSub hV hABD
    (fun A => irrSubOrdinary_of_DLM A hV.rational hABD hV.c2Cofinite hDLMc)
    (finite_Φ_of_finite_Φadm W (hDLMb hV.rational))

/-- **`AssociativityInput` from the ABD citations and `Finite (Φ W)`** (strongly rational
`V`). -/
theorem associativityInput_of_citations (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hOrd : ABDIrreducibleWeakIsOrdinary W) (hΦ : Finite (Φ W)) : AssociativityInput W :=
  associativityInput_of_decomp hV hABD (coefSpanDecomp_of_citations hV hABD hOrd hΦ)

/-- **`AssociativityInput` from ABD Prop. 5.7 and DLM Thm. 8.1(b), (c)** (strongly rational
`V`). -/
theorem associativityInput_of_DLM (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hDLMc : DLMSimpleAdmissibleOrdinary W) (hDLMb : DLMFinitelyManyIrredAdmissible W) :
    AssociativityInput W :=
  associativityInput_of_decomp hV hABD (coefSpanDecomp_of_DLM hV hABD hDLMc hDLMb)

end VOA.Huang.PzTensorDecomp
