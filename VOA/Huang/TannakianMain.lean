/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TannakianFusion
import VOA.Huang.TannakianDim

/-!
# GR Proposition 2.17 with dimensions — assembly of the pure-category part

`tannakian_dims_of_factorized`: in a pseudo-unitary ribbon fusion category satisfying
Turaev's formula at trivial twist, if `S̃_ij = d_i d_j` on trivial-twist simples, then (given
Deligne's theorem) there are a finite group `G` and a braided `ℂ`-linear equivalence
`Φ : C_{θ=1} ≃ Rep(G)` such that, for every simple `X_i` of trivial twist,

* `d_i = dim Φ(X_i)` — the dimensions of `Rep(V)_{h∈ℤ}` are **positive integers**, and
* `dim Hom_G(Fun(G), Φ X_i) = d_i` — `X_i` occurs in the regular algebra with multiplicity `d_i`
  (the coefficient in `ch_W = Σ_a d_a ch_a`).

Conditional only on `DeligneTannakian` and on the stated categorical data; the rest is proved
(`tannakian_of_factorized`, `symDim_eq_of_braided`, `symDim_fdRep`, `finrank_hom_rightFDRep`).
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

/-- **GR Prop. 2.17 with dimensions, conditional on Deligne.** -/
theorem tannakian_dims_of_factorized (hDel : DeligneTannakian.{v, u}) (U : PseudoUnitaryData R)
    (hS : ∀ i j, R.T i = 1 → R.T j = 1 → R.sTilde i j = (U.d i : ℂ) * (U.d j : ℂ))
    (hsym : R.SymDimAgrees) :
    letI := isMonoidal_trivialTwist_of_factorized U hS
    letI := symmetricTrivialTwist_of_factorized U hS
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (Φ : TT R ⥤ FDRep ℂ G),
      Nonempty Φ.Braided ∧ Φ.Linear ℂ ∧ Φ.IsEquivalence ∧
      ∀ (i : F.ι) (hi : R.T i = 1),
        (U.d i : ℂ) = finrank ℂ (Φ.obj (ttSimple R ⟨i, hi⟩)) ∧
        finrank ℂ ((TannakaDuality.FiniteGroup.rightFDRep : FDRep ℂ G) ⟶ Φ.obj (ttSimple R ⟨i, hi⟩)) =
          finrank ℂ (Φ.obj (ttSimple R ⟨i, hi⟩)) := by
  letI := isMonoidal_trivialTwist_of_factorized U hS
  letI := symmetricTrivialTwist_of_factorized U hS
  obtain ⟨G, hG, hGf, Φ, ⟨hbr⟩, hlin, heq⟩ := tannakian_of_factorized hDel U hS hsym
  refine ⟨G, hG, hGf, Φ, ⟨hbr⟩, hlin, heq, fun i hi => ⟨?_, VOA.Huang.Tannakian.finrank_hom_rightFDRep _⟩⟩
  letI := hbr
  have hD := (ttFusion R).finrank_end_unit
  have h1 := symDim_eq_of_braided Φ hD (ttSimple R ⟨i, hi⟩) _ (coev_braid_ev_fdRep _)
  rw [symDim_ttSimple, hsym i hi, U.qdim_eq] at h1
  exact h1

end VOA.Huang.TensorCat
