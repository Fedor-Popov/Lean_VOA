import VOA.Classification.COne.PlusSplitCandidateDescent

/-! Reduction of the multiplication checks to the conformal tests and E².
All constructions still require descent of the proposed spanning values. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuFiniteTests
open PlusUnitary PlusZhuNormalForms PlusCharacterTable
variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance testsRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance testsAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

theorem linear_omega_power (f : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ) (h : ℂ)
    (hf : ∀ x, f (generator m hm 0 * x) = h * f x) (n : ℕ)
    (x : VOA.A (V2mPlus m hm)) : f (generator m hm 0 ^ n * x) = h ^ n * f x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, hf, ih, pow_succ', mul_assoc]

theorem linear_mul_omegaIter (f : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ) (h : ℂ)
    (hf : ∀ x, f (generator m hm 0 * x) = h * f x)
    (a : VOA.A (V2mPlus m hm)) {d : ℤ} {v : ↥(PlusC2.VP m hm)}
    (hv : v ∈ (V2mPlus m hm).grading d) (n : ℕ) :
    f (a * VOA.mk (V2mPlus m hm) (omegaIter m hm v n)) =
      iterateValue h d n * f (a * VOA.mk (V2mPlus m hm) v) := by
  induction n with
  | zero => simp [omegaIter, iterateValue]
  | succ n ih =>
    have he := (eq_sub_iff_add_eq.mp
      (omega_mul_mk m hm (omegaIter_mem_grading m hm hv n))).symm
    change VOA.mk (V2mPlus m hm) (omegaIter m hm v (n + 1)) = _ at he
    rw [he, mul_add, mul_smul_comm, map_add, map_smul, ← mul_assoc,
      (omega_commute m hm a).eq.symm, mul_assoc, hf, ih]
    simp only [iterateValue, smul_eq_mul]
    push_cast
    ring

theorem linear_W_squared (i : Fin 4)
    (f : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ) (h1 : f 1 = 1)
    (hv : ∀ a : Fin 3, f (generator m hm a) = twistedRow m i a)
    (hf : ∀ x, f (generator m hm 0 * x) = twistedRow m i 0 * f x) :
    f (generator m hm 1 * generator m hm 1) = twistedRow m i 1 * twistedRow m i 1 := by
  have hp (n : ℕ) : f (generator m hm 0 ^ n) = twistedRow m i 0 ^ n := by
    simpa [h1] using linear_omega_power m hm f _ hf n 1
  rw [← pow_two, W_squared]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hp, hv, hf,
    linear_omega_power m hm f _ hf]
  simpa [pow_two, hv] using (twistedRow_W_squared m i).symm

theorem linear_W_E (hm2 : 2 ≤ m) (i : Fin 4)
    (f : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ)
    (hv : ∀ a : Fin 3, f (generator m hm a) = twistedRow m i a)
    (hf : ∀ x, f (generator m hm 0 * x) = twistedRow m i 0 * f x) :
    f (generator m hm 1 * generator m hm 2) = twistedRow m i 1 * twistedRow m i 2 := by
  have h := congrArg f (W_E_relation m hm hm2)
  simp only [map_smul, map_add, map_sub, smul_eq_mul,
    linear_omega_power m hm f _ hf, hf, hv] at h
  apply mul_left_cancel₀ (mixed_denominator_ne_zero m hm2)
  linear_combination h - (twistedRow_mixed m i) * twistedRow m i 2

/-- All generator multiplication tests follow from the conformal tests and
one E-square value. W² and W E are supplied by actual quotient identities. -/
theorem candidate_all_tests (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i)
    (ho : ∀ j : Index m,
      candidateFunctional m hm hm2 i hd (generator m hm 0 * spanningClass m hm j) =
        twistedRow m i 0 * candidateValues m i j)
    (he : candidateFunctional m hm hm2 i hd (generator m hm 2 * generator m hm 2) =
      twistedRow m i 2 * twistedRow m i 2) :
    ∀ (a : Fin 3) (j : Index m),
      candidateFunctional m hm hm2 i hd (generator m hm a * spanningClass m hm j) =
        twistedRow m i a * candidateValues m i j := by
  let f := candidateFunctional m hm hm2 i hd
  have hv : ∀ a : Fin 3, f (generator m hm a) = twistedRow m i a :=
    candidateFunctional_generators m hm hm2 i hd
  have hf1 := candidateFunctional_one m hm hm2 i hd
  have hf : ∀ x, f (generator m hm 0 * x) = twistedRow m i 0 * f x := by
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range (spanningClass m hm)) := by
      rw [spanningClass_span m hm hm2]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact (ho j).trans (congrArg (fun c => twistedRow m i 0 * c)
        (candidateFunctional_spanningClass m hm hm2 i hd j).symm)
    | zero => simp
    | add x y _ _ hx hy => simp [mul_add, hx, hy]
    | smul c x _ hx => simp [hx, mul_left_comm]
  have hww := linear_W_squared m hm i f hf1 hv hf
  have hwe := linear_W_E m hm hm2 i f hv hf
  have hunit : VOA.mk (V2mPlus m hm) (V2mPlus m hm).vacuum =
      (1 : VOA.A (V2mPlus m hm)) := rfl
  have hy : VOA.mk (V2mPlus m hm) (y0 m hm) = (1/2 : ℂ) • generator m hm 2 := by
    have hstate : y0 m hm = (1/2 : ℂ) • EP m hm := by
      rw [EP_eq_y0, smul_smul]
      norm_num
    rw [hstate, map_smul]
    rfl
  have hyv : y0 m hm ∈ (V2mPlus m hm).grading m := by
    have hstate : y0 m hm = (1/2 : ℂ) • EP m hm := by
      rw [EP_eq_y0, smul_smul]
      norm_num
    rw [hstate]
    exact Submodule.smul_mem _ _ (EP_mem_grading m hm)
  intro a j
  fin_cases a
  · exact ho j
  · rcases j with (j | j) | j
    · have h := linear_mul_omegaIter m hm f _ hf (generator m hm 1)
        (V2mPlus m hm).vacuum_mem_grading_zero j.val
      change f (_ * _) = _
      simpa [spanningClass, spanningState, candidateValues, hunit, hv, mul_comm] using h
    · have h := linear_mul_omegaIter m hm f _ hf (generator m hm 1)
        (WP_mem_grading m hm) j.val
      change f (_ * _) = iterateValue _ 4 _ * f (generator m hm 1 * generator m hm 1) at h
      simpa [spanningClass, spanningState, candidateValues, hww, mul_left_comm] using h
    · have h := linear_mul_omegaIter m hm f _ hf (generator m hm 1) hyv j.val
      rw [hy, mul_smul_comm, map_smul, hwe] at h
      convert h using 1
      simp only [candidateValues, Int.cast_natCast, smul_eq_mul]
      change twistedRow m i 1 * (iterateValue (twistedRow m i 0) m j.val *
        (twistedRow m i 2 / 2)) = _
      ring
  · rcases j with (j | j) | j
    · have h := linear_mul_omegaIter m hm f _ hf (generator m hm 2)
        (V2mPlus m hm).vacuum_mem_grading_zero j.val
      simpa [spanningClass, spanningState, candidateValues, hunit, hv, mul_comm] using h
    · have h := linear_mul_omegaIter m hm f _ hf (generator m hm 2)
        (WP_mem_grading m hm) j.val
      change f (_ * _) = iterateValue _ 4 _ * f (generator m hm 2 * generator m hm 1) at h
      rw [(W_commute_E m hm hm2).eq.symm, hwe] at h
      simpa [spanningClass, spanningState, candidateValues, mul_comm, mul_left_comm,
        mul_assoc] using h
    · have h := linear_mul_omegaIter m hm f _ hf (generator m hm 2) hyv j.val
      rw [hy, mul_smul_comm, map_smul, he] at h
      convert h using 1
      simp only [candidateValues, Int.cast_natCast, smul_eq_mul]
      change twistedRow m i 2 * (iterateValue (twistedRow m i 0) m j.val *
        (twistedRow m i 2 / 2)) = _
      ring

/-- The last index in each of the three conformal columns. -/
def boundaryIndex : Fin 3 → Index m :=
  ![.inl (.inl ⟨m, by omega⟩), .inl (.inr 2), .inr 2]

/-- After descent, only three conformal boundary tests and one E-square test
remain. This is an open numerical target on the genuine quotient. -/
def FourScalarTests (hm2 : 2 ≤ m) (i : Fin 4) (hd : CandidateDescent m hm i) : Prop :=
  (∀ a : Fin 3,
    candidateFunctional m hm hm2 i hd
      (generator m hm 0 * spanningClass m hm (boundaryIndex m a)) =
        twistedRow m i 0 * candidateValues m i (boundaryIndex m a)) ∧
  candidateFunctional m hm hm2 i hd (generator m hm 2 * generator m hm 2) =
    twistedRow m i 2 * twistedRow m i 2

theorem candidate_all_tests_of_four (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (ht : FourScalarTests m hm hm2 i hd) :
    ∀ (a : Fin 3) (j : Index m),
      candidateFunctional m hm hm2 i hd (generator m hm a * spanningClass m hm j) =
        twistedRow m i a * candidateValues m i j := by
  apply candidate_all_tests m hm hm2 i hd _ ht.2
  intro j
  rcases j with (j | j) | j
  · by_cases hj : j.val < m
    · exact candidateFunctional_omega_vacuum m hm hm2 i hd ⟨j.val, hj⟩
    · have he : j = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) :=
        Fin.ext (by change j.val = m; have := j.isLt; omega)
      rw [he]
      exact ht.1 0
  · by_cases hj : j.val < 2
    · exact candidateFunctional_omega_W m hm hm2 i hd ⟨j.val, hj⟩
    · have he : j = 2 := Fin.ext (by have := j.isLt; change j.val = 2; omega)
      subst j
      exact ht.1 1
  · by_cases hj : j.val < 2
    · exact candidateFunctional_omega_E m hm hm2 i hd ⟨j.val, hj⟩
    · have he : j = 2 := Fin.ext (by have := j.isLt; change j.val = 2; omega)
      subst j
      exact ht.1 2

/-- A character of the actual algebra, conditional on descent and exactly
four scalar tests. Neither premise is supplied by this definition. -/
def characterOfFourTests (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (ht : FourScalarTests m hm hm2 i hd) :
    VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ :=
  characterOfCandidateTests m hm hm2 i hd (candidate_all_tests_of_four m hm hm2 i hd ht)

theorem characterOfFourTests_hasValues (hm2 : 2 ≤ m) (i : Fin 4)
    (hd : CandidateDescent m hm i) (ht : FourScalarTests m hm hm2 i hd) :
    HasValues m hm (twistedLabel m i) (characterOfFourTests m hm hm2 i hd ht) :=
  characterOfCandidateTests_hasValues m hm hm2 i hd
    (candidate_all_tests_of_four m hm hm2 i hd ht)

/-- Exact equivalence: descent plus the four tests loses no character data. -/
theorem fourScalarTests_iff_character (hm2 : 2 ≤ m) (i : Fin 4) :
    (∃ hd : CandidateDescent m hm i, FourScalarTests m hm hm2 i hd) ↔
      ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm (twistedLabel m i) χ := by
  constructor
  · rintro ⟨hd, ht⟩
    exact ⟨characterOfFourTests m hm hm2 i hd ht,
      characterOfFourTests_hasValues m hm hm2 i hd ht⟩
  · rintro ⟨χ, hχ⟩
    have hv := character_spanningClass m hm χ i hχ
    have hd := (candidateDescent_iff m hm hm2 i).mpr ⟨χ.toLinearMap, hv⟩
    have heq : candidateFunctional m hm hm2 i hd = χ.toLinearMap := by
      apply linearMap_eq_of_spanning_values m hm hm2
      intro j
      exact (candidateFunctional_spanningClass m hm hm2 i hd j).trans (hv j).symm
    refine ⟨hd, ?_, ?_⟩
    · intro a
      rw [heq]
      change χ (_ * _) = _
      rw [map_mul, hv]
      exact congrArg (fun c => c * candidateValues m i (boundaryIndex m a)) hχ.1
    · rw [heq]
      change χ (_ * _) = _
      rw [map_mul]
      have he : χ (generator m hm 2) = twistedRow m i 2 := hχ.2.2
      rw [he]

end VOA.Classification.COne.PlusZhuFiniteTests
