import VOA.DeligneAudit.D4CharBoxConvolution
import VOA.DeligneAudit.D4LeviKSCorrectedCountSum

/-! Degreewise counting of the corrected D4 key multiplicities and Levi characters. -/

namespace VOA.DeligneAudit.D4Char

open D4Levi

noncomputable section

/-- The GL4 character assigned to the four nonnegative multiplicities. -/
def leviClassHilb (t : Fin 4 → ℕ) : ℕ → ℕ :=
  gl4Hilb (2 * t 0 + (t 1 + t 2)) (t 0 + (t 1 + t 2)) (t 0) 0

/-- The key seed degree is added to the degree of its Levi descendants. -/
def gradedKeyContribution (n : ℕ) (k : RadicalKey) (N : ℕ) : ℕ :=
  if k.degree ≤ N then
    ksCorrectedBoxCount n k * leviClassHilb (ksKeyClass n k) (N - k.degree)
  else 0

theorem gradedKeyContribution_unsupported (n : ℕ) (k : RadicalKey) (N : ℕ)
    (h : ¬ ksCorrectedSupported n k) : gradedKeyContribution n k N = 0 := by
  simp [gradedKeyContribution, ksCorrectedBoxCount_zero_of_not_supported n k h]

theorem gradedKeyContribution_supported (n : ℕ) (k : RadicalKey) (N : ℕ)
    (h : ksCorrectedSupported n k) :
    gradedKeyContribution n k N =
      if k.degree ≤ N then
        qmultiCoeff (ksKeyClass n k) k.degree *
          leviClassHilb (ksKeyClass n k) (N - k.degree) else 0 := by
  have ht := ksCorrectedKeyClass_mem n k h
  have hn := (Finset.mem_piAntidiag.mp ht).1
  have hc := ksCorrectedClass_boxCount n k (ksKeyClass n k) h rfl
  have hq := ksGradedBoxCount_eq_qmulti (ksKeyClass n k) k.degree
  rw [hn] at hq
  rw [hq] at hc
  simp only [gradedKeyContribution, hc]

/-- Each class has at most one key in a given seed degree. -/
theorem gradedKeyContribution_fiber_le (n N : ℕ) (t : Fin 4 → ℕ)
    (I : Finset RadicalKey)
    (hI : ∀ k ∈ I, ksCorrectedSupported n k ∧ ksKeyClass n k = t) :
    (∑ k ∈ I, gradedKeyContribution n k N) ≤
      A2.conv (qmultiCoeff t) (leviClassHilb t) N := by
  classical
  let J := I.filter fun k => k.degree ≤ N
  have hJ : ∀ k ∈ J, ksCorrectedSupported n k ∧ ksKeyClass n k = t := by
    intro k hk
    exact hI k (Finset.mem_filter.mp hk).1
  have hj : Set.InjOn RadicalKey.degree (J : Set RadicalKey) := by
    intro k hk l hl hd
    rw [ksCorrectedClass_shape n k t (hJ k hk).1 (hJ k hk).2,
      ksCorrectedClass_shape n l t (hJ l hl).1 (hJ l hl).2, hd]
  have he : (∑ k ∈ I, gradedKeyContribution n k N) =
      ∑ k ∈ J, qmultiCoeff t k.degree * leviClassHilb t (N - k.degree) := by
    simp only [J, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    rw [gradedKeyContribution_supported n k N (hI k hk).1, (hI k hk).2]
  rw [he, ← Finset.sum_image (f := fun d =>
    qmultiCoeff t d * leviClassHilb t (N - d)) hj]
  apply Finset.sum_le_sum_of_subset
  intro d hd
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)

/-- The corrected finite key box satisfies the sharp counting inequality in every degree. -/
theorem gradedKeyContribution_sum_le (n N : ℕ) :
    (∑ k ∈ globalKeyBox n, gradedKeyContribution n k N) ≤ d4LeviHilb n N := by
  classical
  let S := (globalKeyBox n).filter (ksCorrectedSupported n)
  let T := Finset.piAntidiag (Finset.univ : Finset (Fin 4)) n
  have he : (∑ k ∈ globalKeyBox n, gradedKeyContribution n k N) =
      ∑ k ∈ S, gradedKeyContribution n k N := by
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : ksCorrectedSupported n k
    · simp [hk]
    · simp [hk, gradedKeyContribution_unsupported n k N hk]
  have hm : ∀ k ∈ S, ksKeyClass n k ∈ T := by
    intro k hk
    exact ksCorrectedKeyClass_mem n k (Finset.mem_filter.mp hk).2
  rw [he, ← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_le_sum
  intro t ht
  apply gradedKeyContribution_fiber_le
  intro k hk
  obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
  exact ⟨(Finset.mem_filter.mp hk).2, he⟩

theorem gradedKeyContribution_enum_sum_le (n N : ℕ) :
    (∑ i : Fin (globalKeyBox n).card,
      gradedKeyContribution n (keyEnum n i) N) ≤ d4LeviHilb n N := by
  classical
  have he : Finset.univ.image (keyEnum n) = globalKeyBox n := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ keyEnum_mem n i,
      fun hk => keyEnum_cover n k hk⟩
  rw [← Finset.sum_image (s := Finset.univ)
    (f := fun k => gradedKeyContribution n k N) (keyEnum_injective n).injOn, he]
  exact gradedKeyContribution_sum_le n N

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gradedKeyContribution_unsupported
#print axioms VOA.DeligneAudit.D4Char.gradedKeyContribution_supported
#print axioms VOA.DeligneAudit.D4Char.gradedKeyContribution_fiber_le
#print axioms VOA.DeligneAudit.D4Char.gradedKeyContribution_sum_le
#print axioms VOA.DeligneAudit.D4Char.gradedKeyContribution_enum_sum_le
