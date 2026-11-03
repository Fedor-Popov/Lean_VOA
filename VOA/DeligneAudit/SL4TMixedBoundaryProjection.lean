import VOA.DeligneAudit.SL4TMiddleFlagBoundary

/-! Exact boundary projections between consecutive mixed multiplicity rings. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Every old relation vanishes after removing a valid middle site. -/
theorem mixedBNext_old_relations (q : MixedParams) (hq : MixedValid q)
    (s : MixedBState) (hs : MixedValid (mixedBNext q s))
    (f : MixedPoly) (hf : f ∈ mixedRelations q) :
    mixedEvaluation (mixedBNext q s) f = 0 := by
  rcases hf with ⟨i, j, hj, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨j, hj, _, rfl⟩ |
    ⟨j, hj, _, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨j, hj, _, rfl⟩
  · apply mixedElementary_tail _ hs i j
    cases s <;> fin_cases i <;> simp [mixedLengths, mixedBNext] at hj ⊢ <;> omega
  · exact mixedBase_complete_tail _ hs 0 j (by cases s <;> exact hj)
  · apply mixedBase_complete_tail _ hs 1 j
    cases s <;> simp [mixedBaseSize, mixedBaseLength, mixedBNext] at hj ⊢ <;> omega
  · exact mixedBase_complete_tail _ hs 2 j (by cases s <;> exact hj)
  · apply mixedG1prime_tail _ hs j
    cases s <;> simp [mixedP, mixedBNext] at hj ⊢ <;> omega
  · apply mixedG2prime_tail _ hs j
    cases s <;> simp [mixedQ, mixedBNext] at hj ⊢ <;> omega

/-- The generator-preserving projection to the ring with one middle site removed. -/
def mixedBProjection (q : MixedParams) (hq : MixedValid q)
    (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    MixedRing q →ₐ[ℂ] MixedRing (mixedBNext q s) :=
  Ideal.Quotient.liftₐ (mixedIdeal q) (mixedEvaluation (mixedBNext q s)) (by
    have hle : mixedIdeal q ≤ RingHom.ker (mixedEvaluation (mixedBNext q s)).toRingHom := by
      rw [mixedIdeal, if_pos hq, Ideal.span_le]
      exact mixedBNext_old_relations q hq s hs
    exact hle)

/-- The projection preserves every polynomial expression in the elementary generators. -/
theorem mixedBProjection_evaluation (q : MixedParams) (hq : MixedValid q)
    (s : MixedBState) (hs : MixedValid (mixedBNext q s)) (f : MixedPoly) :
    mixedBProjection q hq s hs (mixedEvaluation q f) =
      mixedEvaluation (mixedBNext q s) f := rfl

/-- The boundary projection is onto, since the generators do not change. -/
theorem mixedBProjection_surjective (q : MixedParams) (hq : MixedValid q)
    (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    Function.Surjective (mixedBProjection q hq s hs) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (mixedIdeal (mixedBNext q s)) x
  exact ⟨mixedEvaluation q f, rfl⟩

/-- Both boundary generators disappear under the projection. -/
theorem mixedBProjection_boundary (q : MixedParams) (hq : MixedValid q)
    (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    mixedEvaluation (mixedBNext q s) (mixedBPair q s).1 = 0 ∧
      mixedEvaluation (mixedBNext q s) (mixedBPair q s).2 = 0 := by
  have hv := hq
  have hn := hs
  simp only [MixedValid, mixedP, mixedQ] at hv
  cases s
  · constructor
    · apply mixedBase_complete_tail _ hs 1
      simp [mixedBaseSize, mixedBaseLength, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega
    · apply mixedG1prime_tail _ hs
      simp [mixedP, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega
  · constructor
    · apply mixedBase_complete_tail _ hs 1
      simp [mixedBaseSize, mixedBaseLength, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega
    · apply mixedElementary_tail _ hs 3
      simp [mixedLengths, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega
  · constructor
    · apply mixedElementary_tail _ hs 1
      simp [mixedLengths, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega
    · apply mixedElementary_tail _ hs 4
      simp [mixedLengths, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega
  · constructor
    · apply mixedElementary_tail _ hs 1
      simp [mixedLengths, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega
    · apply mixedG2prime_tail _ hs
      simp [mixedQ, mixedBNext]
      simp [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      omega

/-- The state ideal is exactly the kernel of the reduced-ring projection. -/
theorem mixedBProjection_kernel (q : MixedParams) (hq : MixedValid q) (hB : 1 ≤ q.B)
    (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    RingHom.ker (mixedBProjection q hq s hs).toRingHom = mixedBStateIdeal q s := by
  apply le_antisymm
  · intro x hx
    have he : mixedBStateSurjection q hq hB s hs (mixedBProjection q hq s hs x) =
        Ideal.Quotient.mk (mixedBStateIdeal q s) x := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (mixedIdeal q) x
      rfl
    change mixedBProjection q hq s hs x = 0 at hx
    rw [hx, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  · apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact (mixedBProjection_boundary q hq s hs).1
    · rcases hx with rfl
      exact (mixedBProjection_boundary q hq s hs).2

/-- At zero outer labels the projection has precisely the principal flag-top kernel. -/
theorem middleFlagProjection_kernel (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 1 ≤ q.B) (s : MixedBState)
    (hs : MixedValid (mixedBNext q s)) :
    RingHom.ker (mixedBProjection q hq s hs).toRingHom =
      Ideal.span {middleFlagTop q s} := by
  rw [mixedBProjection_kernel q hq hB s hs, middleFlag_stateIdeal q hq hA]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedBNext_old_relations
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_evaluation
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_surjective
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_boundary
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_kernel
#print axioms VOA.DeligneAudit.SL4T.middleFlagProjection_kernel
