/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LeadingKoszulRows
import VOA.Examples.LeadingKoszulTranslation
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Sanity checks: the leading Koszul hypotheses are satisfiable and non-degenerate

* `koszulH0_X` : in one variable over `ℚ` with `a = 1`, the Koszul `H₀` of `x + 1` sends the
  class of `x` to `-1` (the variable is eliminated as `-a`).
* `example` bicomplex `B0`: every row is the Koszul complex of `x + 1` on `ℚ[x]`, with zero
  Chevalley–Eilenberg components. All fields of `LeadingBicomplex` are discharged, and the
  total ghost-zero cohomology is one-dimensional (`finrank_H0`), as predicted by the
  collapse theorem (`H⁰ ≅ ker d̄_CE = Koszul H₀ ≅ ℚ`). So the hypotheses are not vacuous and
  the conclusion is not forced to be zero.
-/

namespace VOA.LeadingKoszul.Example

open MvPolynomial Translation

/-- The translated sequence `x + 1` in one variable over `ℚ`. -/
noncomputable abbrev W1 : WeylDatum ℚ (Fin 1) (MvPolynomial (Fin 1) ℚ) :=
  translatedWeyl fun _ => (1 : ℚ)

theorem koszulH0_X :
    translatedKoszulH0Equiv (fun _ : Fin 1 => (1 : ℚ)) (Submodule.Quotient.mk (X 0)) = -1 := by
  rw [translatedKoszulH0Equiv_mk]
  simp

/-- The constant family of rows. -/
abbrev Prow : ℕ → Type := fun _ => MvPolynomial (Fin 1) ℚ

/-- Koszul rows of `x + 1`, zero CE components. -/
noncomputable def B0 :
    LeadingBicomplex ℚ (LeadingBicomplex.KX ℚ (Fin 1) Prow) (LeadingBicomplex.KY ℚ (Fin 1) Prow)
      (LeadingBicomplex.KZ ℚ (Fin 1) Prow) (LeadingBicomplex.KG ℚ (Fin 1) Prow) :=
  LeadingBicomplex.ofKoszulRows ℚ (Fin 1) Prow (fun _ => W1) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (by simp) (by simp) (by simp) (by simp)

theorem B0_dbar : B0.dbar = 0 := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [LeadingBicomplex.dbar_mk]
    rfl

/-- `H⁰ ≅ ℚ` for the example. -/
noncomputable def H0Equiv : B0.H0 ≃ₗ[ℚ] ℚ :=
  B0.equivKer.trans <|
    (LinearEquiv.ofEq _ _ (by rw [B0_dbar, LinearMap.ker_zero])).trans <|
      (LinearEquiv.ofTop _ rfl).trans (W1.rowH0Equiv (translatedAug _))

theorem finrank_H0 : Module.finrank ℚ B0.H0 = 1 := by
  rw [H0Equiv.finrank_eq, Module.finrank_self]

end VOA.LeadingKoszul.Example
