import VOA.DeligneAudit.SL4TMixedSeries

/-! # The nine a-site state quotients after the b-sites have been removed -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The location of the removed root at the first node. -/
inductive MixedFirstChoice
  | outside | complement | chosen
  deriving DecidableEq

/-- The location of the removed root at the third node. -/
inductive MixedThirdChoice
  | original | chosen | complement
  deriving DecidableEq

/-- An a-site has independent choices at its first and third nodes. -/
abbrev MixedAState := MixedFirstChoice × MixedThirdChoice

/-- The remaining parameters after removing one a-site. -/
def mixedANext (q : MixedParams) (s : MixedAState) : MixedParams :=
  { q with
    A := q.A - 1
    d1 := q.d1 - (if s.1 = .outside then 0 else 1)
    d3 := q.d3 - (if s.2 = .original then 1 else 0)
    e1 := q.e1 - (if s.1 = .chosen then 1 else 0)
    e2 := q.e2 - (if s.2 = .chosen then 1 else 0) }

/-- The number of zero roots removed from the characteristic alphabet. -/
def mixedAZeroRoots (s : MixedAState) : ℕ :=
  (if s.1 = .chosen then 1 else 0) + (if s.2 = .complement then 1 else 0)

/-- The two boundary polynomials attached to an a-site state. -/
def mixedAPair (q : MixedParams) (s : MixedAState) : MixedPoly × MixedPoly :=
  (match s.1 with
    | .outside => mixedH 0 (q.A - q.d1).toNat
    | .complement => mixedG1prime (mixedP q - q.e1).toNat
    | .chosen => mixedE 3 q.e1.toNat,
   match s.2 with
    | .original => mixedE 2 q.d3.toNat
    | .chosen => mixedE 4 q.e2.toNat
    | .complement => mixedG2prime (mixedQ q - q.e2).toNat)

/-- The a-state boundary ideal in the original mixed ring. -/
def mixedAStateIdeal (q : MixedParams) (s : MixedAState) : Ideal (MixedRing q) :=
  Ideal.span {mixedEvaluation q (mixedAPair q s).1,
    mixedEvaluation q (mixedAPair q s).2}

/-- The a-state boundary conditions at which the reduced tuple becomes invalid. -/
def mixedABoundary (q : MixedParams) (s : MixedAState) : Prop :=
  (match s.1 with
    | .outside => q.d1 = q.A
    | .complement => q.e1 = mixedP q
    | .chosen => q.e1 = 0) ∨
  (match s.2 with
    | .original => q.d3 = 0
    | .chosen => q.e2 = 0
    | .complement => q.e2 = mixedQ q)

/-- Invalidity of the reduced parameters is exactly a boundary condition. -/
theorem mixedANext_invalid_iff (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState) :
    ¬ MixedValid (mixedANext q s) ↔ mixedABoundary q s := by
  rcases s with ⟨l, r⟩
  cases l <;> cases r <;>
    simp [MixedValid, mixedP, mixedQ, mixedANext, mixedABoundary] at * <;> omega

/-- The characteristic weight drops by precisely the number of removed zero roots. -/
theorem mixedANext_weight (q : MixedParams) (s : MixedAState) :
    mixedWeight q = mixedWeight (mixedANext q s) + (mixedAZeroRoots s : ℤ) := by
  rcases s with ⟨l, r⟩
  cases l <;> cases r <;>
    simp [mixedWeight, mixedQ, mixedANext, mixedAZeroRoots] <;> omega

/-- The two boundary generators vanish in the a-state quotient. -/
theorem mixedAStateEvaluation_boundary (q : MixedParams) (s : MixedAState) :
    mixedStateEvaluation q (mixedAStateIdeal q s) (mixedAPair q s).1 = 0 ∧
      mixedStateEvaluation q (mixedAStateIdeal q s) (mixedAPair q s).2 = 0 := by
  constructor <;> apply Ideal.Quotient.eq_zero_iff_mem.mpr <;>
    apply Ideal.subset_span <;> simp

/-- Either first-node boundary inside `x1` kills its top elementary generator. -/
theorem mixedAStateEvaluation_first_top (q : MixedParams) (hq : MixedValid q)
    (hB : q.B = 0) (s : MixedAState) (hl : s.1 ≠ .outside) :
    mixedStateEvaluation q (mixedAStateIdeal q s) (mixedE 0 q.d1.toNat) = 0 := by
  have h := congrArg (Ideal.Quotient.mk (mixedAStateIdeal q s))
    (mixedFirst_top_without_b_sites q hq hB)
  simp only [map_mul] at h
  change mixedStateEvaluation q _ (mixedE 3 q.e1.toNat) *
    mixedStateEvaluation q _ (mixedG1prime (mixedP q - q.e1).toNat) =
      mixedStateEvaluation q _ (mixedE 0 q.d1.toNat) at h
  have hb := (mixedAStateEvaluation_boundary q s).1
  rw [← h]
  rcases s with ⟨l, r⟩
  cases l with
  | outside => exact False.elim (hl rfl)
  | complement => change _ * mixedStateEvaluation q _ (mixedAPair q (.complement, r)).1 = 0
                  rw [hb, mul_zero]
  | chosen => change mixedStateEvaluation q _ (mixedAPair q (.chosen, r)).1 * _ = 0
              rw [hb, zero_mul]

/-- Either third-node boundary inside the complement kills its top complete function. -/
theorem mixedAStateEvaluation_third_top (q : MixedParams) (hq : MixedValid q)
    (hB : q.B = 0) (s : MixedAState) (hr : s.2 ≠ .original) :
    mixedStateEvaluation q (mixedAStateIdeal q s) (mixedH 2 (q.A - q.d3).toNat) = 0 := by
  have h := congrArg (Ideal.Quotient.mk (mixedAStateIdeal q s))
    (mixedSecond_top_without_b_sites q hq hB)
  simp only [map_mul, map_pow, map_neg, map_one] at h
  change mixedStateEvaluation q _ (mixedE 4 q.e2.toNat) *
    mixedStateEvaluation q _ (mixedG2prime (mixedQ q - q.e2).toNat) =
      (-1) ^ (q.A - q.d3).toNat *
        mixedStateEvaluation q _ (mixedH 2 (q.A - q.d3).toNat) at h
  apply (IsUnit.mul_right_eq_zero (isUnit_neg_one.pow (q.A - q.d3).toNat)).mp
  rw [← h]
  have hb := (mixedAStateEvaluation_boundary q s).2
  rcases s with ⟨l, r⟩
  cases r with
  | original => exact False.elim (hr rfl)
  | chosen => change mixedStateEvaluation q _ (mixedAPair q (l, .chosen)).2 * _ = 0
              rw [hb, zero_mul]
  | complement => change _ * mixedStateEvaluation q _ (mixedAPair q (l, .complement)).2 = 0
                  rw [hb, mul_zero]

set_option maxHeartbeats 1200000 in
/-- All reduced a-state relations vanish in the corresponding boundary quotient. -/
theorem mixedAStateEvaluation_relations (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState)
    (hs : MixedValid (mixedANext q s)) (f : MixedPoly)
    (hf : f ∈ mixedRelations (mixedANext q s)) :
    mixedStateEvaluation q (mixedAStateIdeal q s) f = 0 := by
  have hb := mixedAStateEvaluation_boundary q s
  have he := mixedAStateEvaluation_first_top q hq hB s
  have hh := mixedAStateEvaluation_third_top q hq hB s
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  rcases s with ⟨l, r⟩
  rcases hf with ⟨i, j, hj, rfl⟩ | ⟨j, hj, hu, rfl⟩ | ⟨j, hj, hu, rfl⟩ |
    ⟨j, hj, hu, rfl⟩ | ⟨j, hj, hu, rfl⟩ | ⟨j, hj, hu, rfl⟩
  · by_cases ho : mixedLengths q i < j
    · exact mixedStateEvaluation_relation q hq _ _ (Or.inl ⟨i, j, ho, rfl⟩)
    · cases l <;> cases r <;> fin_cases i <;>
        simp [mixedLengths, mixedANext] at hj ho <;>
        first
        | omega
        | (have h : j = q.d1.toNat := by omega
           subst j
           exact he (by decide))
        | (have h : j = q.d3.toNat := by omega
           subst j
           simpa [mixedAPair] using hb.2)
        | (have h : j = q.e1.toNat := by omega
           subst j
           simpa [mixedAPair] using hb.1)
        | (have h : j = q.e2.toNat := by omega
           subst j
           simpa [mixedAPair] using hb.2)
  · by_cases ho : (q.A - q.d1).toNat < j
    · apply mixedStateEvaluation_relation q hq
      exact Or.inr (Or.inl ⟨j, ho, by simp [mixedANext] at hu; omega, rfl⟩)
    · cases l <;> cases r <;> simp [mixedANext] at hj <;>
        first
        | omega
        | (have h : j = (q.A - q.d1).toNat := by omega
           subst j
           simpa [mixedAPair] using hb.1)
  · apply mixedStateEvaluation_relation q hq
    exact Or.inr (Or.inr (Or.inl ⟨j, hj, hu, rfl⟩))
  · by_cases ho : (q.A - q.d3).toNat < j
    · apply mixedStateEvaluation_relation q hq
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨j, ho, by simp [mixedANext] at hu; omega, rfl⟩)))
    · cases l <;> cases r <;> simp [mixedANext] at hj <;>
        first
        | omega
        | (have h : j = (q.A - q.d3).toNat := by omega
           subst j
           exact hh (by decide))
  · by_cases ho : (mixedP q - q.e1).toNat < j
    · apply mixedStateEvaluation_relation q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, ho, by
        cases l <;> cases r <;> simp [mixedP, mixedANext] at hu ⊢ <;> omega, rfl⟩))))
    · have hn := hs
      cases l <;> cases r <;>
        simp [MixedValid, mixedP, mixedQ, mixedANext] at hn hj <;>
        first
        | (simp only [mixedP] at ho; omega)
        | (have h : j = (mixedP q - q.e1).toNat := by simp [mixedP] at *; omega
           subst j
           simpa [mixedAPair] using hb.1)
  · by_cases ho : (mixedQ q - q.e2).toNat < j
    · apply mixedStateEvaluation_relation q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, ho, by
        cases l <;> cases r <;> simp [mixedQ, mixedANext] at hu ⊢ <;> omega, rfl⟩))))
    · have hn := hs
      cases l <;> cases r <;>
        simp [MixedValid, mixedP, mixedQ, mixedANext] at hn hj <;>
        first
        | (simp only [mixedQ] at ho; omega)
        | (have h : j = (mixedQ q - q.e2).toNat := by simp [mixedQ] at *; omega
           subst j
           simpa [mixedAPair] using hb.2)

/-- The reduced ring maps onto each valid a-state quotient. -/
def mixedAStateSurjection (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState)
    (hs : MixedValid (mixedANext q s)) :
    MixedRing (mixedANext q s) →ₐ[ℂ] MixedRing q ⧸ mixedAStateIdeal q s :=
  mixedStateSurjection q (mixedANext q s) hs (mixedAStateIdeal q s)
    (mixedAStateEvaluation_relations q hq hA hB s hs)

theorem mixedAStateSurjection_surjective (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState)
    (hs : MixedValid (mixedANext q s)) :
    Function.Surjective (mixedAStateSurjection q hq hA hB s hs) :=
  mixedStateSurjection_surjective q (mixedANext q s) hs (mixedAStateIdeal q s)
    (mixedAStateEvaluation_relations q hq hA hB s hs)

theorem mixedAStateSurjection_evaluation (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState)
    (hs : MixedValid (mixedANext q s)) (f : MixedPoly) :
    mixedAStateSurjection q hq hA hB s hs (mixedEvaluation (mixedANext q s) f) =
      mixedStateEvaluation q (mixedAStateIdeal q s) f := rfl

/-- An invalid a-state forces one of its boundary generators to be the unit. -/
theorem mixedAPair_one_of_invalid (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState)
    (hs : ¬ MixedValid (mixedANext q s)) :
    (mixedAPair q s).1 = 1 ∨ (mixedAPair q s).2 = 1 := by
  have hb := (mixedANext_invalid_iff q hq hA hB s).mp hs
  obtain ⟨he, hh, _, _, hg, hg'⟩ := mixed_series_zero
  rcases s with ⟨l, r⟩
  cases l <;> cases r <;>
    simp only [mixedABoundary] at hb <;>
    rcases hb with hb | hb <;> simp [mixedAPair, hb, he, hh, hg, hg']

/-- Invalid reduced a-states have zero quotient rings. -/
theorem mixedAState_invalid (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState)
    (hs : ¬ MixedValid (mixedANext q s)) :
    Subsingleton (MixedRing q ⧸ mixedAStateIdeal q s) := by
  apply Ideal.Quotient.subsingleton_iff.mpr
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  rcases mixedAPair_one_of_invalid q hq hA hB s hs with h | h <;> simp [h]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedANext_invalid_iff
#print axioms VOA.DeligneAudit.SL4T.mixedANext_weight
#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_boundary

#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_first_top
#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_third_top

#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_relations
#print axioms VOA.DeligneAudit.SL4T.mixedAStateSurjection_surjective
#print axioms VOA.DeligneAudit.SL4T.mixedAStateSurjection_evaluation

#print axioms VOA.DeligneAudit.SL4T.mixedAPair_one_of_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedAState_invalid
