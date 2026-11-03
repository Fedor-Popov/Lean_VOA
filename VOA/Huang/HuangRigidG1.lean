import VOA.Huang.GenusOneG1fSeparation

/-!
# (G1) and Huang's Prop. 5.1 (zig-zag nonvanishing)

All four named genus-one inputs of `GenusOneG1d.vacuumChannelTransportInput_of_genusOneInputs`
are discharged by the algebraic G1e/G1f theorems:

* (N1) `VacuumSCovarianceInput` — `vacuumSCovarianceInput_of_bracket` ∘
  `vacuumBracketSharpInput_of_channel` ∘ `channelBracketSharpInput_of_substitution`
  ∘ `intertwinerSubstitutionInput_holds`;
* (N2) `ConjugationInputAll` — `conjugationInputAll_of_skew traceSkewInput_holds
  intertwinerSubstitutionInput_holds`;
* (N3) `ChannelSStabilityInput` — `channelSStabilityInput_of_bracket` of the same bracket input;
* (N4) `ChannelIndependenceInput` — `channelIndependenceInput_of_separation
  traceSeparationInput_holds`.

Hence:
* `vacuumChannelTransportInput_holds : VacuumChannelTransportInput` (G1);
* `zigzagNonzeroInput_holds : ZigzagNonzeroInput` (Huang's Prop. 5.1, categorical form:
  the zig-zag of the nonzero vacuum pairings is nonzero).

No `sorry`, no new axiom; the proofs use the theorem `VOA.pbw`.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HuangRigid

open VOA.Huang.GenusOneG1d VOA.Huang.GenusOneG1e VOA.Huang.GenusOneG1f
  VOA.Huang.VerlindeTransport

universe u w

/-- The coordinate-change input in the bracket form, from the proved substitution identity. -/
theorem channelBracketSharpInput_holds : ChannelBracketSharpInput.{u, w} :=
  channelBracketSharpInput_of_substitution intertwinerSubstitutionInput_holds

/-- (N1) holds. -/
theorem vacuumSCovarianceInput_holds : VacuumSCovarianceInput.{u, w} :=
  vacuumSCovarianceInput_of_bracket (vacuumBracketSharpInput_of_channel channelBracketSharpInput_holds)

/-- (N2) holds. -/
theorem conjugationInputAll_holds : ConjugationInputAll.{u, w} :=
  conjugationInputAll_of_skew traceSkewInput_holds intertwinerSubstitutionInput_holds

/-- (N3) holds. -/
theorem channelSStabilityInput_holds : ChannelSStabilityInput.{u, w} :=
  channelSStabilityInput_of_bracket channelBracketSharpInput_holds

/-- (N4) holds (Huang Prop. 2.11). -/
theorem channelIndependenceInput_holds : ChannelIndependenceInput.{u, w} :=
  channelIndependenceInput_of_separation traceSeparationInput_holds

/-- **(G1), the genus-one vacuum-channel transport.** -/
theorem vacuumChannelTransportInput_holds : VacuumChannelTransportInput.{u, w} :=
  vacuumChannelTransportInput_of_genusOneInputs vacuumSCovarianceInput_holds
    conjugationInputAll_holds channelSStabilityInput_holds channelIndependenceInput_holds

/-- **Huang's Prop. 5.1 (categorical form)**: the zig-zag
`λ⁻¹ ≫ (η ▷ M_b) ≫ α ≫ (M_b ◁ ε) ≫ ρ` of nonzero vacuum pairings is nonzero. -/
theorem zigzagNonzeroInput_holds : ZigzagNonzeroInput.{u, w} :=
  zigzagNonzeroInput_of_genusOne vacuumChannelTransportInput_holds

end VOA.Huang.HuangRigid
