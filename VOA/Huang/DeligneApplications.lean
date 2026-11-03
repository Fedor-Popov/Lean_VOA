/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneIntegral
import VOA.Huang.TannakianFusion

/-!
# Integrality of the trivial-twist dimensions, without Deligne's theorem

The integrality half of GR Prop. 2.17 / 2.13 does **not** need the full Deligne theorem: it only
needs Deligne's exterior-power argument, proved in `DeligneIntegral`.

* `trivialTwist_dim_nat` — in a pseudo-unitary ribbon fusion category satisfying Turaev's
  formula at trivial twist (`SymDimAgrees`), if `S̃_ij = d_i d_j` on trivial-twist simples, then
  every trivial-twist simple has `d_i ∈ ℤ_{>0}` (for `Rep V`: `d_a ∈ ℤ_{>0}` whenever `h_a ∈ ℤ`).

Previously this was a consequence of `tannakian_dims_of_factorized`, conditional on
`DeligneTannakian`; here it is unconditional (given the stated categorical data).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C] [BraidedCategory C]
  [HasKernels C] [HasFiniteBiproducts C] [F : FusionCategory C] {R : RibbonStructure C}

/-- **The dimensions of the trivial-twist simples are positive integers** (unconditional:
Deligne's exterior-power argument in the symmetric fusion category `C_{θ=1}`). -/
theorem trivialTwist_dim_nat (U : PseudoUnitaryData R)
    (hS : ∀ i j, R.T i = 1 → R.T j = 1 → R.sTilde i j = (U.d i : ℂ) * (U.d j : ℂ))
    (hsym : R.SymDimAgrees) (i : F.ι) (hi : R.T i = 1) :
    ∃ n : ℕ, 0 < n ∧ U.d i = n := by
  letI := isMonoidal_trivialTwist_of_factorized U hS
  letI := symmetricTrivialTwist_of_factorized U hS
  have h2 : ∀ j : {j : F.ι // R.T j = 1}, symDim (F.simple j.1) = (U.d j.1 : ℂ) := fun j => by
    rw [hsym j.1 j.2, U.qdim_eq]
  have hpos : ∀ j : (ttFusion R).ι, 0 < (symDim ((ttFusion R).simple j)).re := fun j => by
    change 0 < (symDim (ttSimple R j)).re
    rw [symDim_ttSimple, h2 j, Complex.ofReal_re]
    exact U.d_pos j.1
  obtain ⟨n, hn, hd⟩ := symDim_simple_nat (F := ttFusion R) hpos ⟨i, hi⟩
  refine ⟨n, hn, ?_⟩
  have : symDim (ttSimple R ⟨i, hi⟩) = (U.d i : ℂ) := by rw [symDim_ttSimple, h2 ⟨i, hi⟩]
  change symDim (ttSimple R ⟨i, hi⟩) = n at hd
  rw [this] at hd
  exact_mod_cast hd

end VOA.Huang.TensorCat
