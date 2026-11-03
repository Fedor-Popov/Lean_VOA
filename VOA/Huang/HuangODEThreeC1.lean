import VOA.Huang.ModuleC2Main
import VOA.Huang.HuangODEThreeModes

/-! # The five external graded C₁ inputs

Only the external modules are used in the C₁ reduction: the output contributes
its restricted dual, and the three insertions and terminal vector contribute
ordinary C₁ data. The two intermediate modules do not need irreducibility here.
This discharges the graded input, not the five-slot filtration reduction.
-/

namespace VOA.Huang.HuangODEThree
open VOA VOA.Huang.HuangODEProduct VOA.Huang.HuangODEC1
open VOA.Huang.HuangODEDual VOA.Huang.HuangODEContra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Both ordinary and restricted-dual graded inputs follow from the proved
module C₂ theorem. This does not use the PBW theorem `VOA.pbw`. -/
theorem moduleC1Data_of_stronglyRational (hV : StronglyRational W) : ModuleC1Data W :=
  moduleC1Data_of_C2 (BuhlSpanning.moduleC2Input_holds V W hV)
    (moduleDualC1Data_of_contragredientC2
      (contragredientC2Data_of_moduleC2Input BuhlSpanning.moduleC2Input_holds hV))

/-- Concrete external data for products of three intertwining operators. -/
def FiveSlotC1Data (P₀ P₁ P₂ P₃ P₄ : LWModule W) : Prop :=
  ∃ B₀ B₁ B₂ B₃ B₄ : ℕ,
    DualC1Graded P₀.isMod P₀.h B₀ ∧ C1Graded P₁.isMod P₁.h B₁ ∧
    C1Graded P₂.isMod P₂.h B₂ ∧ C1Graded P₃.isMod P₃.h B₃ ∧
    C1Graded P₄.isMod P₄.h B₄

/-- All five graded cofiniteness inputs are proved for irreducible external
modules of a strongly rational VOA. -/
theorem fiveSlotC1Data_holds (hV : StronglyRational W)
    {P₀ P₁ P₂ P₃ P₄ : LWModule W}
    (i₀ : P₀.IsIrreducibleLW) (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) :
    FiveSlotC1Data P₀ P₁ P₂ P₃ P₄ := by
  have hC := moduleC1Data_of_stronglyRational hV
  obtain ⟨B₀, h₀⟩ := (hC P₀ i₀).2
  obtain ⟨B₁, h₁⟩ := (hC P₁ i₁).1
  obtain ⟨B₂, h₂⟩ := (hC P₂ i₂).1
  obtain ⟨B₃, h₃⟩ := (hC P₃ i₃).1
  obtain ⟨B₄, h₄⟩ := (hC P₄ i₄).1
  exact ⟨B₀, B₁, B₂, B₃, B₄, h₀, h₁, h₂, h₃, h₄⟩

end VOA.Huang.HuangODEThree
