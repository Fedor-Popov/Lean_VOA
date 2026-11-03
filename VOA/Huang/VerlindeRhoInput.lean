import VOA.Huang.VerlindeRhoReduction

/-!
# Explicit remaining inputs for `VerlindeEigen.RhoNegOneInput`

The coordinate reflection and the nonzero vacuum pairing are separate, true
mathematical statements. This module proves their implication to the unchanged
target; it does not assert either residual.

Huang, arXiv:math/0406291, Proposition 2.4, (2.20), and Proposition 5.3.
-/

namespace VOA.Huang.VerlindeRho

open VOA VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.VerlindeEigen
  VOA.Huang.ZhuModData

universe u w

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- In the coordinate `z = exp(t) - 1`, reversal of `t` is the Möbius map
`z ↦ -z/(1+z)`, represented on states by `contraTwist`.
This is a state-space identity, with no module, trace or modular representation. -/
def SquareBracketReflection (W : VertexOperatorAlgebra V) : Prop :=
  ∀ (n : ℕ) (v : V), v ∈ sqWeightSpace W (n : ℂ) →
    contraTwist W v = (-1 : ℂ) ^ n • v

/-- State-space reflection supplies the formal contragredient trace identity. -/
theorem squareBracketTraceParity_of_reflection
    {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
    (hr : SquareBracketReflection W) : SquareBracketTraceParity W := by
  intro M _ _ N n v hv
  rw [onePoint_contragredient_twist, hr n v hv, onePoint_smul]

/-- The coordinate-change identity needed here, restricted to nice VOAs. -/
def SquareBracketReflectionInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V),
    Nice W → SquareBracketReflection W

/-- Only nonvanishing of the contragredient vacuum channel is needed to identify
the labels of a supplied vacuum delta rule. This is weaker than the full FHL
vacuum fusion calculation: neither its exact dimension nor other channels occur. -/
def ContragredientVacuumNonzeroInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        ∀ a b, Nonempty (ModuleEquiv W (contragredientModule (D.Mfam a).isMod)
          (D.Mfam b).isMod) → famFusion D a b v0 ≠ 0

/-- Reduction to formal trace parity and the nonzero vacuum pairing, with PBW explicit. -/
theorem rhoNegOneInput_of_traceParity
    (hPBW : ZhuPBWBottomInput.{u})
    (hpar : ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V),
      Nice W → SquareBracketTraceParity W)
    (hpair : ContragredientVacuumNonzeroInput.{u, w}) : RhoNegOneInput.{u, w} := by
  intro V _ _ W hV ι _ _ D hZ hirr hcomp v0 hv0 σ hσ
  obtain ⟨Pr⟩ := hPBW V W
  exact rep_neg_one_of_contragredient Pr D hV.1.c2Cofinite hZ hirr (hpar V W hV)
    (contragredientLabels_of_vacuum_nonzero D v0 hcomp σ hσ
      (hpair V W hV ι D v0 hv0))

/-- Reduction to the state-space coordinate reflection and the nonzero vacuum pairing.
The conclusion is exactly the existing `RhoNegOneInput`, at all its universes. -/
theorem rhoNegOneInput_of_reflection
    (hPBW : ZhuPBWBottomInput.{u}) (hr : SquareBracketReflectionInput.{u})
    (hpair : ContragredientVacuumNonzeroInput.{u, w}) : RhoNegOneInput.{u, w} :=
  rhoNegOneInput_of_traceParity hPBW
    (fun V _ _ W hV => squareBracketTraceParity_of_reflection (hr V W hV)) hpair

end VOA.Huang.VerlindeRho
