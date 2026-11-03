import VOA.DeligneAudit.D4LeviKSBoxCountFiber

/-! Sum the graded D4 boxes over the actual finite radical key box. -/

namespace VOA.DeligneAudit.D4Levi

private def classWeight (t : Fin 4 → ℕ) : ℕ :=
  16 ^ t 0 * 6 ^ (t 1 + t 2)

private noncomputable def supportedClassKeys (m : ℕ) (t : Fin 4 → ℕ) :
    Finset RadicalKey := by
  classical
  exact (globalKeyBox m).filter
    (fun k => ksSupported m k ∧ ksKeyClass m k = t)

theorem ksBoxCount_fiber_le (m : ℕ) (t : Fin 4 → ℕ)
    (ht : t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m) :
    (∑ k ∈ supportedClassKeys m t,
      keyOrbitLength m k * ksBoxCount m k) ≤
      Nat.multinomial Finset.univ t *
        ∏ j : Fin 4, ksClassWeight j ^ t j := by
  classical
  let I := supportedClassKeys m t
  have hshape : ∀ k ∈ I,
      k = pairFinalKey (t 0) (t 2) (t 3) k.degree := by
    intro k hk
    have hk' := (Finset.mem_filter.mp
      (show k ∈ (globalKeyBox m).filter
        (fun k => ksSupported m k ∧ ksKeyClass m k = t) from hk)).2
    exact ksClass_shape m k t hk'.1 hk'.2
  have hdegree := ksGradedBoxCount_sum_le m (t 0) (t 2) (t 3) I hshape
  calc
    (∑ k ∈ I, keyOrbitLength m k * ksBoxCount m k) =
        ∑ k ∈ I, classWeight t *
          ksGradedBoxCount m (t 0) (t 2) (t 3) k.degree := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := (Finset.mem_filter.mp
        (show k ∈ (globalKeyBox m).filter
          (fun k => ksSupported m k ∧ ksKeyClass m k = t) from hk)).2
      have hs := hk'.1
      have hc := hk'.2
      rw [ksClass_orbit m k t hs hc, ksClass_boxCount m k t hs hc]
      rfl
    _ = classWeight t *
          ∑ k ∈ I, ksGradedBoxCount m (t 0) (t 2) (t 3) k.degree := by
      rw [Finset.mul_sum]
    _ ≤ classWeight t * (ksBoxTriples m (t 0) (t 2) (t 3)).card :=
      Nat.mul_le_mul_left _ hdegree
    _ = Nat.multinomial Finset.univ t *
          ∏ j : Fin 4, ksClassWeight j ^ t j := by
      rw [ksBoxTriples_card_class m t ht, ksClassWeight_product]
      simp only [classWeight]
      ring

theorem ksBoxCount_global_sum (m : ℕ) :
    (∑ k ∈ globalKeyBox m, keyOrbitLength m k * ksBoxCount m k) ≤ 29 ^ m := by
  classical
  let S := (globalKeyBox m).filter (ksSupported m)
  let T := Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m
  have hzero :
      (∑ k ∈ globalKeyBox m, keyOrbitLength m k * ksBoxCount m k) =
        ∑ k ∈ S, keyOrbitLength m k * ksBoxCount m k := by
    rw [show S = (globalKeyBox m).filter (ksSupported m) by rfl,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hs : ksSupported m k
    · simp [hs]
    · simp [hs, ksBoxCount_zero_of_not_supported m k hs]
  have hmaps : ∀ k ∈ S, ksKeyClass m k ∈ T := by
    intro k hk
    exact ksKeyClass_mem m k (Finset.mem_filter.mp hk).2
  have hfiber :
      (∑ k ∈ S, keyOrbitLength m k * ksBoxCount m k) =
        ∑ t ∈ T, ∑ k ∈ S.filter (fun k => ksKeyClass m k = t),
          keyOrbitLength m k * ksBoxCount m k := by
    exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  rw [hzero, hfiber]
  calc
    (∑ t ∈ T, ∑ k ∈ S.filter (fun k => ksKeyClass m k = t),
        keyOrbitLength m k * ksBoxCount m k) ≤
      ∑ t ∈ T, Nat.multinomial Finset.univ t *
        ∏ j : Fin 4, ksClassWeight j ^ t j := by
      apply Finset.sum_le_sum
      intro t ht
      simpa [S, Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
        ksBoxCount_fiber_le m t ht
    _ = 29 ^ m := ksWeightedMultinomial m

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_fiber_le
#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_global_sum
