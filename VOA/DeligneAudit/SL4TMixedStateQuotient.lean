import VOA.DeligneAudit.SL4TMixed

/-!
# Surjections onto the quotients at a mixed site

All five alphabets live in the same polynomial ring. A containment of relation
sets therefore gives an algebra surjection from the reduced ring onto the state
quotient. The direction of this map is the one required for spanning bounds.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Evaluation of the five alphabets in their presented mixed ring. -/
def mixedEvaluation (q : MixedParams) : MixedPoly →ₐ[ℂ] MixedRing q :=
  Ideal.Quotient.mkₐ ℂ (mixedIdeal q)

/-- Evaluation in a further ideal quotient of the mixed ring. -/
def mixedStateEvaluation (q : MixedParams) (K : Ideal (MixedRing q)) :
    MixedPoly →ₐ[ℂ] MixedRing q ⧸ K :=
  (Ideal.Quotient.mkₐ ℂ K).comp (mixedEvaluation q)

/-- The two successive quotient maps are jointly surjective. -/
theorem mixedStateEvaluation_surjective (q : MixedParams) (K : Ideal (MixedRing q)) :
    Function.Surjective (mixedStateEvaluation q K) :=
  (Ideal.Quotient.mkₐ_surjective ℂ K).comp
    (Ideal.Quotient.mkₐ_surjective ℂ (mixedIdeal q))

/-- Old defining relations vanish in every further state quotient. -/
theorem mixedStateEvaluation_relation (q : MixedParams) (hq : MixedValid q)
    (K : Ideal (MixedRing q)) (f : MixedPoly) (hf : f ∈ mixedRelations q) :
    mixedStateEvaluation q K f = 0 := by
  change Ideal.Quotient.mk K (Ideal.Quotient.mk (mixedIdeal q) f) = 0
  rw [mixedRelation_zero q hq f hf, map_zero]

/-- A valid reduced presentation maps onto a state quotient when its relations vanish. -/
def mixedStateSurjection (q q' : MixedParams) (hq' : MixedValid q')
    (K : Ideal (MixedRing q))
    (hrel : ∀ f ∈ mixedRelations q', mixedStateEvaluation q K f = 0) :
    MixedRing q' →ₐ[ℂ] MixedRing q ⧸ K :=
  Ideal.Quotient.liftₐ (mixedIdeal q') (mixedStateEvaluation q K) (by
    intro f hf
    have hle : mixedIdeal q' ≤ RingHom.ker (mixedStateEvaluation q K).toRingHom := by
      rw [mixedIdeal, if_pos hq', Ideal.span_le]
      exact hrel
    exact hle hf)

/-- The reduced-ring map preserves every polynomial in the elementary generators. -/
theorem mixedStateSurjection_evaluation (q q' : MixedParams) (hq' : MixedValid q')
    (K : Ideal (MixedRing q))
    (hrel : ∀ f ∈ mixedRelations q', mixedStateEvaluation q K f = 0)
    (f : MixedPoly) :
    mixedStateSurjection q q' hq' K hrel (mixedEvaluation q' f) =
      mixedStateEvaluation q K f := rfl

/-- No injectivity or exact dimension statement is needed for this quotient map. -/
theorem mixedStateSurjection_surjective (q q' : MixedParams) (hq' : MixedValid q')
    (K : Ideal (MixedRing q))
    (hrel : ∀ f ∈ mixedRelations q', mixedStateEvaluation q K f = 0) :
    Function.Surjective (mixedStateSurjection q q' hq' K hrel) := by
  intro x
  obtain ⟨f, rfl⟩ := mixedStateEvaluation_surjective q K x
  exact ⟨mixedEvaluation q' f, rfl⟩

/-- Each of the two boundary generators vanishes in its state quotient. -/
theorem mixedBStateEvaluation_boundary (q : MixedParams) (s : MixedBState) :
    mixedStateEvaluation q (mixedBStateIdeal q s) (mixedBPair q s).1 = 0 ∧
      mixedStateEvaluation q (mixedBStateIdeal q s) (mixedBPair q s).2 = 0 := by
  constructor <;> apply Ideal.Quotient.eq_zero_iff_mem.mpr <;>
    apply Ideal.subset_span <;> simp [mixedEvaluation, Ideal.Quotient.mkₐ_eq_mk]

/-- Every relation of the reduced b-site tuple is old or is a boundary generator. -/
theorem mixedBState_relation_containment (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    mixedRelations (mixedBNext q s) ⊆
      mixedRelations q ∪ {(mixedBPair q s).1, (mixedBPair q s).2} := by
  intro f hf
  rcases hf with ⟨i, j, hj, rfl⟩ | ⟨j, hj, hu, rfl⟩ | ⟨j, hj, hu, rfl⟩ |
    ⟨j, hj, hu, rfl⟩ | ⟨j, hj, hu, rfl⟩ | ⟨j, hj, hu, rfl⟩
  · by_cases ho : mixedLengths q i < j
    · exact Or.inl (Or.inl ⟨i, j, ho, rfl⟩)
    · have hv := hq
      simp only [MixedValid, mixedP, mixedQ] at hv
      cases s <;> fin_cases i <;>
        simp [mixedLengths, mixedBNext] at hj ho <;>
        first
        | omega
        | (have he : j = q.d2.toNat := by omega
           rw [he]
           exact Or.inr (by simp [mixedBPair]))
        | (have he : j = q.e1.toNat := by omega
           rw [he]
           exact Or.inr (by simp [mixedBPair]))
        | (have he : j = q.e2.toNat := by omega
           rw [he]
           exact Or.inr (by simp [mixedBPair]))
  · apply Or.inl
    exact Or.inr (Or.inl ⟨j, by cases s <;> exact hj, by cases s <;> exact hu, rfl⟩)
  · by_cases ho : (q.B - q.d2).toNat < j
    · apply Or.inl
      exact Or.inr (Or.inr (Or.inl ⟨j, ho, by
        cases s <;> simp [mixedBNext] at hu <;> omega, rfl⟩))
    · have hv := hq
      simp only [MixedValid, mixedP, mixedQ] at hv
      cases s <;> simp [mixedBNext] at hj <;>
        first
        | omega
        | (have he : j = (q.B - q.d2).toNat := by omega
           rw [he]
           exact Or.inr (by simp [mixedBPair]))
  · apply Or.inl
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨j, by cases s <;> exact hj, by cases s <;> exact hu, rfl⟩)))
  · by_cases ho : (mixedP q - q.e1).toNat < j
    · apply Or.inl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, ho, by
        cases s <;> simp [mixedP, mixedBNext] at hu ⊢ <;> omega, rfl⟩))))
    · have hv := hq
      have hn := hs
      simp only [MixedValid, mixedP, mixedQ, mixedBNext] at hv hn
      cases s <;> simp [mixedP, mixedBNext] at hj <;>
        first
        | (simp only [mixedP] at ho; omega)
        | (have he : j = (mixedP q - q.e1).toNat := by simp [mixedP] at *; omega
           rw [he]
           exact Or.inr (by simp [mixedBPair]))
  · by_cases ho : (mixedQ q - q.e2).toNat < j
    · apply Or.inl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, ho, by
        cases s <;> simp [mixedQ, mixedBNext] at hu ⊢ <;> omega, rfl⟩))))
    · have hv := hq
      have hn := hs
      simp only [MixedValid, mixedP, mixedQ, mixedBNext] at hv hn
      cases s <;> simp [mixedQ, mixedBNext] at hj <;>
        first
        | (simp only [mixedQ] at ho; omega)
        | (have he : j = (mixedQ q - q.e2).toNat := by simp [mixedQ] at *; omega
           rw [he]
           exact Or.inr (by simp [mixedBPair]))

/-- The new finite windows vanish in each valid b-state quotient. -/
theorem mixedBStateEvaluation_relations (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) (s : MixedBState) (hs : MixedValid (mixedBNext q s))
    (f : MixedPoly) (hf : f ∈ mixedRelations (mixedBNext q s)) :
    mixedStateEvaluation q (mixedBStateIdeal q s) f = 0 := by
  rcases mixedBState_relation_containment q hq hB s hs hf with ho | hb
  · exact mixedStateEvaluation_relation q hq _ f ho
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact (mixedBStateEvaluation_boundary q s).1
    · exact (mixedBStateEvaluation_boundary q s).2

/-- The reduced ring surjects onto the b-state quotient, preserving all generators. -/
def mixedBStateSurjection (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    MixedRing (mixedBNext q s) →ₐ[ℂ] MixedRing q ⧸ mixedBStateIdeal q s :=
  mixedStateSurjection q (mixedBNext q s) hs (mixedBStateIdeal q s)
    (mixedBStateEvaluation_relations q hq hB s hs)

theorem mixedBStateSurjection_surjective (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    Function.Surjective (mixedBStateSurjection q hq hB s hs) :=
  mixedStateSurjection_surjective q (mixedBNext q s) hs (mixedBStateIdeal q s)
    (mixedBStateEvaluation_relations q hq hB s hs)

theorem mixedBStateSurjection_evaluation (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) (s : MixedBState) (hs : MixedValid (mixedBNext q s))
    (f : MixedPoly) :
    mixedBStateSurjection q hq hB s hs (mixedEvaluation (mixedBNext q s) f) =
      mixedStateEvaluation q (mixedBStateIdeal q s) f := rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedStateEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.mixedStateEvaluation_relation
#print axioms VOA.DeligneAudit.SL4T.mixedStateSurjection_evaluation
#print axioms VOA.DeligneAudit.SL4T.mixedStateSurjection_surjective
#print axioms VOA.DeligneAudit.SL4T.mixedBStateEvaluation_boundary
#print axioms VOA.DeligneAudit.SL4T.mixedBState_relation_containment
#print axioms VOA.DeligneAudit.SL4T.mixedBStateEvaluation_relations
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_surjective
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_evaluation
