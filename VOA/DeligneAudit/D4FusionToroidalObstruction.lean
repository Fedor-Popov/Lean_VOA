import VOA.DeligneAudit.D4FusionToroidalFilt

/-!
# An obstruction to the proposed graded toroidal action

For the abelian one-colour current algebra and no defining tails, a mode-two letter
is in filtration step one but not step two. Thus the operator proposed to have
`u` degree two does not preserve the high-letter filtration with that shift.
This file makes no dimension or surjectivity claim.
-/

namespace VOA.DeligneAudit.FusionToroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

private def zeroBracket : Fin 1 → Fin 1 → Fin 1 → ℂ := fun _ _ _ => 0

private def emptySpec : RelSpec 1 where
  tails := ∅
  eig := ∅

private abbrev high : Ltr 1 := ((0 : Fin 1), 2)

private def highCoeff : FreeW 1 →ₗ[ℂ] ℂ := Finsupp.lapply [high]

private theorem highCoeff_J :
    Jrel zeroBracket emptySpec ≤ LinearMap.ker highCoeff := by
  rw [Jrel, Submodule.span_le]
  rintro _ ⟨p, ⟨s, x, y, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨q, hq, rfl⟩⟩
  · have hxy : p ++ x :: y :: s ≠ [high] := by
      intro he
      have hh := congrArg List.length he
      simp at hh
      omega
    have hyx : p ++ y :: x :: s ≠ [high] := by
      intro he
      have hh := congrArg List.length he
      simp at hh
      omega
    change highCoeff (commInst zeroBracket p s x y) = 0
    simp [highCoeff, commInst, zeroBracket, sw, Finsupp.lapply_apply,
      hxy, hyx]
  · simp [emptySpec] at ht
  · simp [emptySpec] at hq

private def highCoeffU : UModG zeroBracket emptySpec →ₗ[ℂ] ℂ :=
  (Jrel zeroBracket emptySpec).liftQ highCoeff highCoeff_J

private theorem highCoeffU_TU_two :
    TU zeroBracket emptySpec 1 2 ≤ LinearMap.ker highCoeffU := by
  rintro _ ⟨v, hv, rfl⟩
  change highCoeff v = 0
  exact Tfree_two_le_ker_single 1 high hv

theorem high_single_not_mem_TU_two :
    (Jrel zeroBracket emptySpec).mkQ (sw [high]) ∉
      TU zeroBracket emptySpec 1 2 := by
  intro h
  have hz := highCoeffU_TU_two h
  change highCoeff (sw [high]) = 0 at hz
  simp [highCoeff, sw, Finsupp.lapply_apply] at hz

/-- The required degree-two shift already fails on the universal generator. -/
theorem no_two_step_shift_TU :
    ¬ TU zeroBracket emptySpec 1 0 ≤
      (TU zeroBracket emptySpec 1 2).comap
        ((univRepG zeroBracket emptySpec).op 0 2) := by
  intro h
  have hw : wUG zeroBracket emptySpec ∈ TU zeroBracket emptySpec 1 0 :=
    word_mem_TU zeroBracket emptySpec 1 0 [] (Nat.zero_le _)
  have hx := h hw
  change opU zeroBracket emptySpec high
    (Submodule.Quotient.mk (sw [])) ∈
      TU zeroBracket emptySpec 1 2 at hx
  rw [opU_mk] at hx
  exact high_single_not_mem_TU_two hx

end

end VOA.DeligneAudit.FusionToroidal

section AxiomAudit
#print axioms VOA.DeligneAudit.FusionToroidal.high_single_not_mem_TU_two
#print axioms VOA.DeligneAudit.FusionToroidal.no_two_step_shift_TU
end AxiomAudit
