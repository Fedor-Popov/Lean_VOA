import VOA.Huang.NgSchauenburgTwistOrder

/-! # Consequences of the still-open Bantay formula

These theorems are explicitly conditional on `BantayFormula`. In particular
they do not purport to prove that formula by defining the indicator to be its
right-hand side. The indicator remains the trace of the pivotal rotation.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The specifically requested second-indicator theorem, as an unproved
categorical target independent of the higher-degree formula. -/
def BantaySecondFormula (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ V : C, indicator F.toPivotal V 2 = F.globalDimension⁻¹ *
    ∑ i : F.Label, ∑ j : F.Label,
      (F.fusionMultiplicity i j V : ℂ) * F.dimension (F.simple i) *
        F.dimension (F.simple j) * (M.twistScalar i / M.twistScalar j) ^ 2

theorem bantaySecondFormula_of_bantay (F : SphericalFusion C) (M : Modular F)
    (h : BantayFormula F M) : BantaySecondFormula F M :=
  fun V => h V 2 (by decide)

/-- A common twist-annihilating power is a period of every positive-degree
indicator, conditional on the categorical Bantay theorem. -/
theorem indicator_periodic_of_bantay (F : SphericalFusion C) (M : Modular F)
    (h : BantayFormula F M) {N : ℕ}
    (hN : ∀ i : F.Label, M.twistScalar i ^ N = 1)
    (V : C) {n : ℕ} (hn : 0 < n) :
    indicator F.toPivotal V (n + N) = indicator F.toPivotal V n := by
  rw [h V (n + N) (by omega), h V n hn]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_add, div_pow, hN i, hN j, div_self one_ne_zero, mul_one]

/-- Vafa plus Bantay gives a positive common period. This is not yet the
FS-exponent theorem: the value at a multiple must also be identified with
categorical dimension. -/
theorem positive_indicator_period_of_vafa_bantay (F : SphericalFusion C) (M : Modular F)
    (hv : VafaTheorem F M) (hb : BantayFormula F M) :
    0 < M.toRibbon.twistOrder ∧ ∀ (V : C) (n : ℕ), 0 < n →
      indicator F.toPivotal V (n + M.toRibbon.twistOrder) = indicator F.toPivotal V n := by
  refine ⟨M.toRibbon.twistOrder_pos_iff.mpr hv, fun V n hn => ?_⟩
  refine indicator_periodic_of_bantay F M hb ?_ V hn
  intro i
  exact congrFun (pow_orderOf_eq_one (fun j => M.twistScalar j)) i

end VOA.Huang.NgSchauenburg
