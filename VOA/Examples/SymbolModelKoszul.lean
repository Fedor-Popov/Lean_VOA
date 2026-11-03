/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelGr

/-!
# The leading Koszul step in the weight-shifting form needed by the concrete complex

`LeadModel.leadCohomEquivInvariants` (`LeadingKoszulKahler`) and the builder
`SymbolCyclicModel.ofLeadModel` (`CyclicEvalAssembly`) take the Koszul `H₀` of the two lowest rows
as `e0 : KH0 ≃ N` and `e1 : KH1 ≃ (κ → N)` **with the same `N`**, and the induced
Chevalley–Eilenberg map as a family of *endomorphisms* `ρ k : N → N`.

On the actual relative complex at a fixed conformal weight `n` this shape does not fit (reasoned
observation, not machine-checked): Koszul `H₀` in `c`-count zero is `(gr_r A ⊗ L_1)_n`, while in
`c`-count one it is `⊕_{(a,m)} (gr_r A ⊗ L_1)_{n-m} c^a_{-m}` (the ghost `c^a_{-m}` has weight
`m`), and the induced map `v ↦ (J^a_m v)_{(a,m)}` changes the conformal weight. So the CE map is
not a family of endomorphisms of one space, and `KH1` is not `κ → KH0`.

This file gives the correct general form and the concrete package:

* `jointKer ρ = ⋂_k ker ρ_k` for **heterogeneous** maps `ρ_k : N0 → N1_k`;
* `kerDbarEquivJointKer` — `ker d̄_CE ≃ jointKer ρ` from `e0 : KH0 ≃ N0` and an **injective**
  (not necessarily surjective) `e1 : KH1 → Π_k N1_k` intertwining `d̄_CE` with `ρ`;
* `leadCohomEquivJointKer` — `H⁰(Q⁻)_a ≃ jointKer ρ` for a `LeadModel`;
* `GrLeadKoszulData C n r` — the concrete data an instantiation must supply: a `LeadModel` of
  the leading complex at `(2r, 0)`, Koszul `H₀` in `c`-count zero identified with a space `N0`
  embedded (injectively, in total weight `n`) in `gr_r A ⊗ L_1`, and Koszul `H₀` in `c`-count one
  embedded injectively in `Π_{(a,m)} gr_r A ⊗ L_1`, with the CE map becoming the diagonal action
  `J^a_m ⊗ 1 + 1 ⊗ J^a_m`;
* `GrLeadKoszulData.toGrKoszulEmbedding` — such data gives `GrKoszulEmbedding`;
* `leeYang_gradedUnitary_of_affine_grLeadKoszul` — the endpoint with `koszul` replaced by
  `GrLeadKoszulData` at every weight and degree.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.SymbolModel

open VOA.CyclicEval VOA.InvariantSymbol VOA.GradedUnitaryCohomology VOA.LeadingKoszul
open VOA.LeeYangTransferAssembly VOA.ConcreteHodge Sl2CosetConcrete
open TensorProduct

noncomputable section

section General

universe uB

variable {X Y Z G : ℕ → Type uB}
variable [∀ p, AddCommGroup (X p)] [∀ p, Module ℂ (X p)]
variable [∀ p, AddCommGroup (Y p)] [∀ p, Module ℂ (Y p)]
variable [∀ p, AddCommGroup (Z p)] [∀ p, Module ℂ (Z p)]
variable [∀ p, AddCommGroup (G p)] [∀ p, Module ℂ (G p)]
variable {N0 : Type*} [AddCommGroup N0] [Module ℂ N0]
variable {ι' : Type*} {N1 : ι' → Type*} [∀ k, AddCommGroup (N1 k)] [∀ k, Module ℂ (N1 k)]

/-- The joint kernel of a heterogeneous family `ρ_k : N0 → N1_k`. -/
def jointKer (ρ : ∀ k, N0 →ₗ[ℂ] N1 k) : Submodule ℂ N0 := ⨅ k, LinearMap.ker (ρ k)

theorem mem_jointKer (ρ : ∀ k, N0 →ₗ[ℂ] N1 k) (y : N0) : y ∈ jointKer ρ ↔ ∀ k, ρ k y = 0 := by
  simp [jointKer, Submodule.mem_iInf]

/-- **`ker d̄_CE` is the joint kernel**, for an injective `e1`. -/
def kerDbarEquivJointKer (Bc : LeadingBicomplex ℂ X Y Z G) (e0 : Bc.KH0 ≃ₗ[ℂ] N0)
    (e1 : Bc.KH1 →ₗ[ℂ] (∀ k, N1 k)) (he1 : Function.Injective e1) (ρ : ∀ k, N0 →ₗ[ℂ] N1 k)
    (hρ : ∀ v k, e1 (Bc.dbar v) k = ρ k (e0 v)) :
    LinearMap.ker Bc.dbar ≃ₗ[ℂ] jointKer ρ :=
  e0.ofSubmodules _ _ (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext y
    simp only [Submodule.mem_comap, LinearMap.mem_ker, mem_jointKer]
    constructor
    · intro h k
      have := congrArg (fun w => e1 w k) h
      simp only [hρ, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero,
        Pi.zero_apply] at this
      exact this
    · intro h
      apply he1
      funext k
      rw [map_zero, Pi.zero_apply]
      have := hρ (e0.symm y) k
      rw [LinearEquiv.apply_symm_apply] at this
      rw [LinearEquiv.coe_coe, this, h k])

/-- **The leading Koszul step, weight-shifting form**: `H⁰(Q⁻)_a ≃ jointKer ρ`. -/
def leadCohomEquivJointKer {K : Type*} [AddCommGroup K] [Module ℂ K] {C : KahlerComplex K}
    {Bc : LeadingBicomplex ℂ X Y Z G} {a : ℤ × ℤ} (LM : LeadModel C Bc a)
    (e0 : Bc.KH0 ≃ₗ[ℂ] N0) (e1 : Bc.KH1 →ₗ[ℂ] (∀ k, N1 k)) (he1 : Function.Injective e1)
    (ρ : ∀ k, N0 →ₗ[ℂ] N1 k) (hρ : ∀ v k, e1 (Bc.dbar v) k = ρ k (e0 v)) :
    C.leadCohom a ≃ₗ[ℂ] jointKer ρ :=
  LM.leadCohomEquivH0.trans (Bc.equivKer.trans (kerDbarEquivJointKer Bc e0 e1 he1 ρ hρ))

end General

/-! ### The concrete package on `gr_r A ⊗ L_1` -/

/-- The diagonal action `J^a_m ⊗ 1 + 1 ⊗ J^a_m` on `gr_r A ⊗ L_1`. -/
def grDiag (r : ℕ) (k : Fin 3 × ℕ) : Module.End ℂ (GrA r ⊗[ℂ] BSpace) :=
  (grRho r k).rTensor BSpace + (bMode k).lTensor (GrA r)

theorem isInv_iff_grDiag (r : ℕ) (x : GrA r ⊗[ℂ] BSpace) :
    IsInv (grRho r) bMode x ↔ ∀ k, grDiag r k x = 0 := Iff.rfl

/-- **The concrete leading Koszul data at weight `n`, degree `r`** (OPEN): a `LeadModel` of the
leading complex at `(2r, 0)`; Koszul `H₀` in `c`-count zero identified with `N0`, embedded
injectively in `gr_r A ⊗ L_1` in total weight `n`; Koszul `H₀` in `c`-count one embedded
injectively in `Π_{(a,m)} gr_r A ⊗ L_1`, so that `d̄_CE` becomes the diagonal action. -/
structure GrLeadKoszulData {K : Type*} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)
    (n : ℤ) (r : ℕ) where
  X : ℕ → Type
  Y : ℕ → Type
  Z : ℕ → Type
  G : ℕ → Type
  [xacg : ∀ p, AddCommGroup (X p)]
  [xmod : ∀ p, Module ℂ (X p)]
  [yacg : ∀ p, AddCommGroup (Y p)]
  [ymod : ∀ p, Module ℂ (Y p)]
  [zacg : ∀ p, AddCommGroup (Z p)]
  [zmod : ∀ p, Module ℂ (Z p)]
  [gacg : ∀ p, AddCommGroup (G p)]
  [gmod : ∀ p, Module ℂ (G p)]
  Bc : LeadingBicomplex ℂ X Y Z G
  LM : LeadModel C Bc (2 * (r : ℤ), 0)
  N0 : Type
  [nacg : AddCommGroup N0]
  [nmod : Module ℂ N0]
  e0 : Bc.KH0 ≃ₗ[ℂ] N0
  j : N0 →ₗ[ℂ] GrA r ⊗[ℂ] BSpace
  j_injective : Function.Injective j
  j_weight : ∀ y, j y ∈ tensorWeight (grDeg r) bWeight n
  e1 : Bc.KH1 →ₗ[ℂ] (Fin 3 × ℕ → GrA r ⊗[ℂ] BSpace)
  e1_injective : Function.Injective e1
  intertwine : ∀ v k, e1 (Bc.dbar v) k = grDiag r k (j (e0 v))

attribute [instance] GrLeadKoszulData.xacg GrLeadKoszulData.xmod GrLeadKoszulData.yacg
  GrLeadKoszulData.ymod GrLeadKoszulData.zacg GrLeadKoszulData.zmod GrLeadKoszulData.gacg
  GrLeadKoszulData.gmod GrLeadKoszulData.nacg GrLeadKoszulData.nmod

/-- **Concrete Koszul data gives the Koszul embedding.** -/
def GrLeadKoszulData.toGrKoszulEmbedding {K : Type*} [AddCommGroup K] [Module ℂ K]
    {C : KahlerComplex K} {n : ℤ} {r : ℕ} (D : GrLeadKoszulData C n r) :
    GrKoszulEmbedding C n r where
  ι := D.j ∘ₗ (jointKer fun k => grDiag r k ∘ₗ D.j).subtype ∘ₗ
    (leadCohomEquivJointKer D.LM D.e0 D.e1 D.e1_injective (fun k => grDiag r k ∘ₗ D.j)
      D.intertwine).toLinearMap
  injective := D.j_injective.comp (Subtype.val_injective.comp (LinearEquiv.injective _))
  inv v := by
    have h := (leadCohomEquivJointKer D.LM D.e0 D.e1 D.e1_injective
      (fun k => grDiag r k ∘ₗ D.j) D.intertwine v).2
    rw [mem_jointKer] at h
    exact (isInv_iff_grDiag r _).mpr h
  weight v := D.j_weight _

/-- OPEN (leading Koszul data): the concrete Koszul data for the endpoint geometry. -/
abbrev EndpointGrLeadKoszul (hA : GradedUnitary affineForm affineRealStructure affineFlag) :=
  ∀ n (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ),
    GrLeadKoszulData ((endpointKahler hA).model n hp) n r

/-- **Affine GU ⇒ Lee–Yang GU**, with the Koszul input in its concrete bicomplex form.
`#print axioms`-clean, conditional on `hA` (the hypothesis), `cyc` (input (A) for `r ≥ 1`),
`koszul` (the concrete leading Koszul data), `lower` (classical Rogers–Ramanujan). -/
theorem leeYang_gradedUnitary_of_affine_grLeadKoszul
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (cyc : GrCyclicVectorsPos) (koszul : EndpointGrLeadKoszul hA)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_grSymbols hA cyc
    (fun n hp r => (koszul n hp r).toGrKoszulEmbedding) lower

end

end VOA.SymbolModel
