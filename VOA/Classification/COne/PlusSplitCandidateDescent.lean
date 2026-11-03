import VOA.Classification.COne.PlusSplitSpanningValues

/-! The explicit candidate functional on free coordinates, and its descent
criterion. The kernel inclusion is an open obligation, not a consequence of
spanning. Once it holds, normalization and generator values are automatic. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuFiniteTests
open PlusUnitary PlusZhuNormalForms PlusCharacterTable

variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance descentRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance descentAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) :=
  instAlgebraA _

/-- Send free coordinates to the actual Zhu spanning family. -/
def coordinateMap : (Index m → ℂ) →ₗ[ℂ] VOA.A (V2mPlus m hm) :=
  Fintype.linearCombination ℂ (spanningClass m hm)

/-- Four explicit linear functionals on the free coordinate space. -/
def freeCandidate (i : Fin 4) : (Index m → ℂ) →ₗ[ℂ] ℂ :=
  Fintype.linearCombination ℂ (candidateValues m i)

theorem coordinateMap_surjective (hm2 : 2 ≤ m) :
    Function.Surjective (coordinateMap m hm) :=
  (span_range_eq_top_iff_surjective_fintypeLinearCombination ℂ _).mp
    (spanningClass_span m hm hm2)

/-- OPEN: all dependencies of the spanning family annihilate the proposed
values. This makes no assertion that the family is a basis. -/
def CandidateDescent (i : Fin 4) : Prop :=
  LinearMap.ker (coordinateMap m hm) ≤ LinearMap.ker (freeCandidate m i)

/-- A conditional construction on the genuine quotient, using the proved
surjectivity and the explicitly required kernel inclusion. -/
def candidateFunctional (hm2 : 2 ≤ m) (i : Fin 4) (hd : CandidateDescent m hm i) :
    VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ :=
  ((LinearMap.ker (coordinateMap m hm)).liftQ (freeCandidate m i) hd).comp
    ((coordinateMap m hm).quotKerEquivOfSurjective
      (coordinateMap_surjective m hm hm2)).symm.toLinearMap

theorem candidateFunctional_coordinateMap (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (c : Index m → ℂ) :
    candidateFunctional m hm hm2 i hd (coordinateMap m hm c) = freeCandidate m i c := by
  simp [candidateFunctional, LinearMap.quotKerEquivOfSurjective_symm_apply]

theorem candidateFunctional_spanningClass (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (j : Index m) :
    candidateFunctional m hm hm2 i hd (spanningClass m hm j) = candidateValues m i j := by
  have h := candidateFunctional_coordinateMap m hm hm2 i hd (Pi.single j 1)
  simpa [coordinateMap, freeCandidate] using h

/-- Exact existence criterion for a linear functional with the proposed values. -/
theorem candidateDescent_iff (hm2 : 2 ≤ m) (i : Fin 4) :
    CandidateDescent m hm i ↔
      ∃ f : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ,
        ∀ j : Index m, f (spanningClass m hm j) = candidateValues m i j := by
  constructor
  · intro hd
    exact ⟨candidateFunctional m hm hm2 i hd, candidateFunctional_spanningClass m hm hm2 i hd⟩
  · rintro ⟨f, hf⟩ c hc
    have he : f (coordinateMap m hm c) = freeCandidate m i c := by
      simp [coordinateMap, freeCandidate, Fintype.linearCombination_apply, map_sum, hf]
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← he, hc, map_zero]

theorem candidateFunctional_one (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) : candidateFunctional m hm hm2 i hd 1 = 1 :=
  candidateFunctional_spanningClass m hm hm2 i hd (.inl (.inl ⟨0, by omega⟩))

theorem candidateFunctional_generators (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (a : Fin 3) :
    candidateFunctional m hm hm2 i hd (generator m hm a) = twistedRow m i a := by
  have hv := candidateFunctional_spanningClass m hm hm2 i hd
  fin_cases a
  · have h := hv (.inl (.inl ⟨1, by omega⟩))
    have he : spanningClass m hm (.inl (.inl ⟨1, by omega⟩)) = generator m hm 0 := by
      change VOA.mk (V2mPlus m hm) ((V2mPlus m hm).smul
        (V2mPlus m hm).conformalVector (-1) (V2mPlus m hm).vacuum) = _
      exact congrArg (VOA.mk (V2mPlus m hm))
        ((V2mPlus m hm).creation (V2mPlus m hm).conformalVector).1
    simpa [he, candidateValues, iterateValue] using h
  · simpa [spanningClass, spanningState, omegaIter, candidateValues, iterateValue] using
      hv (.inl (.inr 0))
  · have h := hv (.inr 0)
    change candidateFunctional m hm hm2 i hd (VOA.mk (V2mPlus m hm) (y0 m hm)) =
      _ * (twistedRow m i 2 / 2) at h
    simp only [iterateValue, one_mul] at h
    change candidateFunctional m hm hm2 i hd (VOA.mk (V2mPlus m hm) (EP m hm)) = _
    rw [EP_eq_y0, map_smul, map_smul, h]
    change 2 * (twistedRow m i 2 / 2) = twistedRow m i 2
    ring

/-- With descent supplied, precisely the generator multiplication tests remain. -/
def characterOfCandidateTests (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i)
    (ht : ∀ (a : Fin 3) (j : Index m),
      candidateFunctional m hm hm2 i hd (generator m hm a * spanningClass m hm j) =
        twistedRow m i a * candidateValues m i j) :
    VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ :=
  characterOfFiniteTests (generator m hm) (V2mPlus_zhu_adjoin_generators m hm hm2)
    (spanningClass m hm) (spanningClass_span m hm hm2)
    (candidateFunctional m hm hm2 i hd) (candidateFunctional_one m hm hm2 i hd)
    (by intro a j; rw [ht, candidateFunctional_generators, candidateFunctional_spanningClass])

theorem characterOfCandidateTests_hasValues (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i)
    (ht : ∀ (a : Fin 3) (j : Index m),
      candidateFunctional m hm hm2 i hd (generator m hm a * spanningClass m hm j) =
        twistedRow m i a * candidateValues m i j) :
    HasValues m hm (twistedLabel m i) (characterOfCandidateTests m hm hm2 i hd ht) :=
  ⟨candidateFunctional_generators m hm hm2 i hd 0,
    candidateFunctional_generators m hm hm2 i hd 1,
    candidateFunctional_generators m hm hm2 i hd 2⟩

/-- An interior conformal test follows from the two adjacent forced values. -/
theorem linear_omegaIter_test (f : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ)
    {v : ↥(PlusC2.VP m hm)} {d : ℤ} (hv : v ∈ (V2mPlus m hm).grading d)
    (h c : ℂ) (n : ℕ)
    (hn : f (VOA.mk (V2mPlus m hm) (omegaIter m hm v n)) = iterateValue h d n * c)
    (hs : f (VOA.mk (V2mPlus m hm) (omegaIter m hm v (n + 1))) =
      iterateValue h d (n + 1) * c) :
    f (generator m hm 0 * VOA.mk (V2mPlus m hm) (omegaIter m hm v n)) =
      h * f (VOA.mk (V2mPlus m hm) (omegaIter m hm v n)) := by
  rw [omega_mul_mk m hm (omegaIter_mem_grading m hm hv n), map_sub, map_smul]
  change f (VOA.mk (V2mPlus m hm) (omegaIter m hm v (n+1))) - _ = _
  rw [hn, hs]
  simp only [iterateValue, smul_eq_mul]
  push_cast
  ring

/-- All m non-boundary pure-omega tests, conditional only on descent. -/
theorem candidateFunctional_omega_vacuum (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (j : Fin m) :
    candidateFunctional m hm hm2 i hd
      (generator m hm 0 * spanningClass m hm (.inl (.inl ⟨j.val, by omega⟩))) =
      twistedRow m i 0 * candidateValues m i (.inl (.inl ⟨j.val, by omega⟩)) := by
  have hn := candidateFunctional_spanningClass m hm hm2 i hd
    (.inl (.inl ⟨j.val, by omega⟩))
  have hs := candidateFunctional_spanningClass m hm hm2 i hd
    (.inl (.inl ⟨j.val+1, by omega⟩))
  have h := linear_omegaIter_test m hm (candidateFunctional m hm hm2 i hd)
    (V2mPlus m hm).vacuum_mem_grading_zero (twistedRow m i 0) 1 j.val
    (by simpa [spanningClass, spanningState, candidateValues] using hn)
    (by simpa [spanningClass, spanningState, candidateValues] using hs)
  change _ = twistedRow m i 0 * candidateValues m i (.inl (.inl ⟨j.val, by omega⟩))
  exact h.trans (congrArg (fun c => twistedRow m i 0 * c) hn)

/-- The two non-boundary W-column conformal tests. -/
theorem candidateFunctional_omega_W (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (j : Fin 2) :
    candidateFunctional m hm hm2 i hd
      (generator m hm 0 * spanningClass m hm (.inl (.inr ⟨j.val, by omega⟩))) =
      twistedRow m i 0 * candidateValues m i (.inl (.inr ⟨j.val, by omega⟩)) := by
  have hn := candidateFunctional_spanningClass m hm hm2 i hd
    (.inl (.inr ⟨j.val, by omega⟩))
  have hs := candidateFunctional_spanningClass m hm hm2 i hd
    (.inl (.inr ⟨j.val+1, by omega⟩))
  have h := linear_omegaIter_test m hm (candidateFunctional m hm hm2 i hd)
    (WP_mem_grading m hm) (twistedRow m i 0) (twistedRow m i 1) j.val hn hs
  exact h.trans (congrArg (fun c => twistedRow m i 0 * c) hn)

/-- The two non-boundary E-column conformal tests. -/
theorem candidateFunctional_omega_E (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (j : Fin 2) :
    candidateFunctional m hm hm2 i hd
      (generator m hm 0 * spanningClass m hm (.inr ⟨j.val, by omega⟩)) =
      twistedRow m i 0 * candidateValues m i (.inr ⟨j.val, by omega⟩) := by
  have hn := candidateFunctional_spanningClass m hm hm2 i hd (.inr ⟨j.val, by omega⟩)
  have hs := candidateFunctional_spanningClass m hm hm2 i hd (.inr ⟨j.val+1, by omega⟩)
  have hv : y0 m hm ∈ (V2mPlus m hm).grading m := by
    have he : y0 m hm = (1/2 : ℂ) • EP m hm := by
      rw [EP_eq_y0, smul_smul]
      norm_num
    rw [he]
    exact Submodule.smul_mem _ _ (EP_mem_grading m hm)
  have h := linear_omegaIter_test m hm (candidateFunctional m hm hm2 i hd)
    hv (twistedRow m i 0) (twistedRow m i 2 / 2) j.val
    (by simpa using hn) (by simpa using hs)
  exact h.trans (congrArg (fun c => twistedRow m i 0 * c) hn)

end VOA.Classification.COne.PlusZhuFiniteTests
