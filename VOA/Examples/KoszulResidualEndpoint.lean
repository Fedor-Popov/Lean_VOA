/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualExact

/-!
# The endpoint with Koszul exactness discharged

`KoszulConcrete.EndpointKoszulResidual hA` has two components at every weight `n` and degree `r`:
Koszul exactness `KExact` of the actual `d_K`, and the symbol maps `π₀`, `π₁`. The first is
**proved** (`kExact_endpoint`). This file records the reduction

  `EndpointSymbolResidual hA → EndpointKoszulResidual hA`

and the endpoint theorem with only the symbol maps left (besides `hA`, `strict`, `lower`).
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open scoped TensorProduct

noncomputable section

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- **OPEN (the symbol maps) at weight `n`, degree `r`**: the second component of
`KoszulResidual` — `π₀` on the antighost-free block at `(2r, 0)` into `gr_r A ⊗ L_1` with kernel
exactly the `d_K`-boundaries, `π₁` on the antighost-free block at `(2r + 1, 1)` with kernel
exactly the `d_K`-boundaries, `π₁ ∘ d_CE = grDiag ∘ π₀`, and `π₀` landing in weight `n`. -/
def SymbolResidual (n : ℤ) (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ) :
    Type :=
  Σ' S : (endpointBlocks hA n hp).KoszulSymbolMaps (2 * (r : ℤ), 0) (GrA r ⊗[ℂ] BSpace)
    (grDiag r), ∀ x, S.π0 x ∈ tensorWeight (grDeg r) bWeight n

/-- OPEN: the symbol maps at every weight and degree. -/
abbrev EndpointSymbolResidual : Type :=
  ∀ n (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ), SymbolResidual hA n hp r

/-- **The Koszul residual from the symbol maps alone**: Koszul exactness is proved. -/
def koszulResidual_of_symbols (S : EndpointSymbolResidual hA) : EndpointKoszulResidual hA :=
  fun n hp r => ⟨kExact_endpoint hA hp (2 * (r : ℤ), 0), S n hp r⟩

/-- **Affine GU ⇒ Lee–Yang GU, with Koszul exactness proved.** `#print axioms`-clean,
conditional on `hA` (the hypothesis), `strict` (strictness `gr_r A ↪ A_r`, `r ≥ 1`), `S` (the
two symbol maps on the antighost-free blocks), `lower` (classical Rogers–Ramanujan). -/
theorem leeYang_gradedUnitary_of_affine_symbolResidual
    (strict : ∀ r : ℕ, GrJetStrict (r + 1)) (S : EndpointSymbolResidual hA)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_koszulResidual hA strict (koszulResidual_of_symbols hA S) lower

end

end VOA.KoszulResidual
