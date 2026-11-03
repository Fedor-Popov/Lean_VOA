/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.CyclicEvalCore
import VOA.Examples.InvariantSymbolAssembly
import VOA.Examples.LeadingKoszulKahler

/-!
# `LeadingCyclicEvaluation` from a symbol model and Fock coordinates

`InvariantSymbolAssembly.LeadingCyclicEvaluation` asks for an injective linear map
`ev : H⁰(Q⁻)_{(2r,0)}(n) → C[a_1, a_2, …]` of weighted degree `n - r(r+1)` annihilated by the
Cartan ideal. Here it is **constructed** (`leadingCyclicEvaluation_of_models`) from three inputs
with separate mathematical content:

* `SymbolCyclicModel` — for each weight `n` and filtration degree `r`: a symbol module `M`
  (in the note: `gr_r L_{-4/3}(sl₂)`) with its induced mode action and a `CyclicDual`
  vector (input (A) of the coset note: cyclicity of the full physical restricted dual and
  relation (A1)), together with an injective linear embedding of the actual leading cohomology
  into the invariant tensors `(M ⊗ B)^{g[t]}` of total weight `n` (the leading Koszul
  identification, which is only needed as an injection);
* `FockCoordinates` for every `r` — the level-one charge-`r` sectors of `B`;
* the vanishing of the leading cohomology at odd and at negative `2R` (`oddZero`, `negZero`).

`SymbolCyclicModel.ofLeadModel` builds the Koszul embedding from the abstract leading Koszul
step `LeadModel.leadCohomEquivInvariants` (`LeadingKoszulKahler`), given a linear injection of
its coefficient module into `M ⊗ B` carrying the joint kernel into the invariants.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.CyclicEval

open VOA.InvariantSymbol VOA.GradedUnitaryCohomology VOA.LeeYangTransferAssembly
open VOA.ConcreteHodge TensorProduct
open Module (finrank)

noncomputable section
set_option synthInstance.maxHeartbeats 200000

universe v

section Model

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
variable {κ : Type*} (σ : κ → Module.End ℂ B) (hz : κ) (hpos : ℕ → κ)
variable (Bdeg : ℤ → Submodule ℂ B)

/-- **The symbol model at weight `n`, degree `r`.** A symbol module `M` with mode action `ρ`,
conformal grading `Mdeg`, a cyclic dual vector with the highest Cartan relations, and an
injective embedding of the leading cohomology `H⁰(Q⁻)_{(2r,0)}` into the invariant tensors of
`M ⊗ B` of total weight `n`. -/
structure SymbolCyclicModel {K : Type*} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)
    (n : ℤ) (r : ℕ) where
  M : Type
  [acg : AddCommGroup M]
  [mod : Module ℂ M]
  ρ : κ → Module.End ℂ M
  Mdeg : ℤ → Submodule ℂ M
  dual : CyclicDual ρ hz hpos Mdeg r
  ι : C.leadCohom (2 * (r : ℤ), 0) →ₗ[ℂ] M ⊗[ℂ] B
  injective : Function.Injective ι
  inv : ∀ v, IsInv ρ σ (ι v)
  weight : ∀ v, ι v ∈ tensorWeight Mdeg Bdeg n

attribute [instance] SymbolCyclicModel.acg SymbolCyclicModel.mod

variable {σ hz hpos Bdeg}

/-- The cyclic evaluation of the leading cohomology defined by a symbol model and Fock
coordinates. -/
def SymbolCyclicModel.ev {K : Type*} [AddCommGroup K] [Module ℂ K] {C : KahlerComplex K}
    {n : ℤ} {r : ℕ} (S : SymbolCyclicModel σ hz hpos Bdeg C n r)
    (Φ : FockCoordinates σ hz hpos Bdeg r) :
    C.leadCohom (2 * (r : ℤ), 0) →ₗ[ℂ] MvPolynomial ℕ ℂ :=
  Φ.φ ∘ₗ contract S.dual.w ∘ₗ S.ι

theorem SymbolCyclicModel.ev_spec {K : Type*} [AddCommGroup K] [Module ℂ K]
    {C : KahlerComplex K} {n : ℤ} {r : ℕ} (S : SymbolCyclicModel σ hz hpos Bdeg C n r)
    (Φ : FockCoordinates σ hz hpos Bdeg r) :
    Function.Injective (S.ev Φ) ∧
    (∀ v, MvPolynomial.IsWeightedHomogeneous modeWeightZ (S.ev Φ v) (n - r * (r + 1))) ∧
    (∀ v (F : MvPolynomial ℕ ℂ), F ∈ cartanIdeal r → modePairing F (S.ev Φ v) = 0) :=
  cyclicEvaluation S.dual Φ n S.ι S.injective S.inv S.weight

/-- **The Koszul embedding from the abstract leading Koszul step.** A `LeadModel` of the leading
complex at `(2r, 0)`, the identifications `e0`, `e1` of Koszul `H₀` with a coefficient module `N`
intertwining `d̄_CE` with `ρN`, and a linear injection `j : N → M ⊗ B` carrying the joint kernel
of `ρN` into the invariant tensors of weight `n`, give a symbol model. -/
def SymbolCyclicModel.ofLeadModel {K : Type*} [AddCommGroup K] [Module ℂ K]
    {C : KahlerComplex K} {n : ℤ} {r : ℕ}
    {X Y Z G : ℕ → Type v}
    [∀ p, AddCommGroup (X p)] [∀ p, Module ℂ (X p)]
    [∀ p, AddCommGroup (Y p)] [∀ p, Module ℂ (Y p)]
    [∀ p, AddCommGroup (Z p)] [∀ p, Module ℂ (Z p)]
    [∀ p, AddCommGroup (G p)] [∀ p, Module ℂ (G p)]
    {Bc : VOA.LeadingKoszul.LeadingBicomplex ℂ X Y Z G}
    (LM : VOA.LeadingKoszul.LeadModel C Bc (2 * (r : ℤ), 0))
    {N : Type*} [AddCommGroup N] [Module ℂ N] {ι' : Type*}
    (e0 : Bc.KH0 ≃ₗ[ℂ] N) (e1 : Bc.KH1 ≃ₗ[ℂ] (ι' → N)) (ρN : ι' → N →ₗ[ℂ] N)
    (hρ : ∀ v k, e1 (Bc.dbar v) k = ρN k (e0 v))
    (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : κ → Module.End ℂ M)
    (Mdeg : ℤ → Submodule ℂ M) (dual : CyclicDual ρ hz hpos Mdeg r)
    (j : N →ₗ[ℂ] M ⊗[ℂ] B) (hj : Function.Injective j)
    (hjinv : ∀ y ∈ VOA.LeadingKoszul.invariants ρN, IsInv ρ σ (j y))
    (hjwt : ∀ y ∈ VOA.LeadingKoszul.invariants ρN, j y ∈ tensorWeight Mdeg Bdeg n) :
    SymbolCyclicModel σ hz hpos Bdeg C n r where
  M := M
  ρ := ρ
  Mdeg := Mdeg
  dual := dual
  ι := j ∘ₗ (VOA.LeadingKoszul.invariants ρN).subtype ∘ₗ
    (LM.leadCohomEquivInvariants e0 e1 ρN hρ).toLinearMap
  injective := hj.comp (Subtype.val_injective.comp (LinearEquiv.injective _))
  inv := fun v => hjinv _ (LM.leadCohomEquivInvariants e0 e1 ρN hρ v).2
  weight := fun v => hjwt _ (LM.leadCohomEquivInvariants e0 e1 ρN hρ v).2

end Model

/-! ### Assembly into `LeadingCyclicEvaluation` -/

/-- Vanishing bigraded piece gives vanishing leading cohomology. -/
theorem finrank_leadCohom_eq_zero_of_deg {K : Type*} [AddCommGroup K] [Module ℂ K]
    (C : KahlerComplex K) (a : ℤ × ℤ) (h : C.deg a = ⊥) : finrank ℂ (C.leadCohom a) = 0 := by
  have hc : C.leadCycles a = ⊥ := by
    rw [KahlerComplex.leadCycles, h, inf_bot_eq]
  haveI : Subsingleton (C.leadCycles a) := ⟨fun x y => Subtype.ext (by
    have hx : (x : K) ∈ (⊥ : Submodule ℂ K) := hc ▸ x.2
    have hy : (y : K) ∈ (⊥ : Submodule ℂ K) := hc ▸ y.2
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy])⟩
  haveI : Subsingleton (C.leadCohom a) := ⟨fun x y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]⟩
  exact Module.finrank_zero_of_subsingleton

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
variable {κ : Type*} {σ : κ → Module.End ℂ B} {hz : κ} {hpos : ℕ → κ}
variable {Bdeg : ℤ → Submodule ℂ B}

/-- **`LeadingCyclicEvaluation` from symbol models and Fock coordinates.** -/
def leadingCyclicEvaluation_of_models (S : ConcreteKahlerGeometry)
    (oddZero : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (p : ℕ),
      finrank ℂ ((S.model n hp).leadCohom (2 * (p : ℤ) + 1, 0)) = 0)
    (negZero : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (j : ℤ), j < 0 →
      finrank ℂ ((S.model n hp).leadCohom (j, 0)) = 0)
    (model : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (r : ℕ),
      SymbolCyclicModel σ hz hpos Bdeg (S.model n hp) n r)
    (fock : ∀ r : ℕ, FockCoordinates σ hz hpos Bdeg r) :
    LeadingCyclicEvaluation S where
  odd_zero := oddZero
  neg_zero := negZero
  ev n hp r := (model n hp r).ev (fock r)
  injective n hp r := ((model n hp r).ev_spec (fock r)).1
  degree n hp r := ((model n hp r).ev_spec (fock r)).2.1
  cartan n hp r x F hF _ := ((model n hp r).ev_spec (fock r)).2.2 x F hF

end

end VOA.CyclicEval
