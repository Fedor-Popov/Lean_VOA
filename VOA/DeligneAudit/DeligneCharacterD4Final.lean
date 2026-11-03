/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Schur

/-!
# The D₄ character side: final form

The D₄ character side splits as follows.

* **`D4DemazureEqSchur`** (the paper's D₄ theorem at `t = q`, `z = 1`): the Demazure sum equals the
  Schur index `d4SchurQ` (`½ CT_x Θ(x) M` with the explicit theta measure). Proved here
  (`d4DemazureEqSchur_holds`) from two named inputs:
  - `D4F.D4FiniteIdentity`, the finite polynomial identity (P);
  - `D4K.D4DemazurePositivity`, nonnegativity of the Demazure energies and multiplicities, a
    consequence of the Demazure character formula (the input that reads `C_m` as `ch D(1,mθ)`).
* **`D4ClassS W`** (literature): `d4SchurQ N ≤ dim W_N` for `W = L_{-2}(D₄)`.  Arakawa's class-S theorem
  (arXiv:1811.01577, Thms A.1, A.2, 10.11) identifies the vacuum character of the simple quotient with the
  Schur integral of the product kernel; the product kernel's `x`-constant term equals the explicit-θ
  form used in `d4SchurQ` by the two-variable Jacobi triple product
  (`DeligneCharacterD4Theta.TwoVariableJTP`, proved as `VOA.QSeries.JTP.twoVariableJTP`).
* The earlier target `d4TargetCoeff` (`q^{-7/12}E₄′/(240η¹⁰)`) stays only as a documented alternative;
  identifying it with `d4SchurQ` needs the Arakawa–Kawasetsu MLDE or an elliptic Schur-integral evaluation.
-/

namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra D4K

/-- **D₄: Demazure sum = Schur index** (at `t = q`, `z = 1`). -/
def D4DemazureEqSchur : Prop := ∀ N, (demazureSumCoeff d4DemazureHilb N : ℚ) = d4SchurQ N

theorem d4DemazureEqSchur_holds (hF : D4F.D4FiniteIdentity) (hpos : D4DemazurePositivity) :
    D4DemazureEqSchur :=
  d4_demazure_eq_schur hF hpos

/-- **Class S (literature)**: the Schur index bounds the vacuum character of `W` from below. -/
structure D4ClassS {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V) : Prop where
  le : ∀ N : ℕ, d4SchurQ N ≤ (Module.finrank ℂ (W.grading N) : ℚ)

/-- **The D₄ character side** `D_N ≤ dim W_N`, from the finite identity, Demazure positivity and class S. -/
theorem d4DemazureBound {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (hF : D4F.D4FiniteIdentity) (hpos : D4DemazurePositivity) (hS : D4ClassS W) :
    DemazureBoundFor W d4DemazureHilb :=
  ⟨fun N => by
    have h := (d4DemazureEqSchur_holds hF hpos N).trans_le (hS.le N)
    exact_mod_cast h⟩

/-- Finite guard for `D4DemazurePositivity` at `m ≤ 1`. -/
theorem d4DemazurePositivity_small :
    (∀ m ∈ List.range 2, ∀ t ∈ demazureChar cartanD4 thetaD4 wordD4 m, 0 ≤ t.1.2 + (m : ℤ) * m) ∧
      ∀ m ∈ List.range 2, ∀ N ∈ List.range 6, 0 ≤ hilbInt m N := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.d4DemazurePositivity_small
#print axioms VOA.DeligneAudit.DeligneCharacter.d4DemazureEqSchur_holds
#print axioms VOA.DeligneAudit.DeligneCharacter.d4DemazureBound
end AxiomAudit
