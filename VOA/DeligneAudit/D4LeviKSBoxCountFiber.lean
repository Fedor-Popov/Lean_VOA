import VOA.DeligneAudit.D4LeviKSBoxCountClass

/-! One fibre of supported keys has at most its four-class multinomial weight. -/

namespace VOA.DeligneAudit.D4Levi

private theorem class_sum (m : ℕ) (t : Fin 4 → ℕ)
    (ht : t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m) :
    t 0 + t 1 + t 2 + t 3 = m := by
  have h := (Finset.mem_piAntidiag.mp ht).1
  simpa only [Fin.sum_univ_four] using h

private theorem class_vector (t : Fin 4 → ℕ) :
    t = ![t 0, t 1, t 2, t 3] := by
  funext j
  fin_cases j <;> rfl

theorem ksBoxTriples_card_class (m : ℕ) (t : Fin 4 → ℕ)
    (ht : t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m) :
    (ksBoxTriples m (t 0) (t 2) (t 3)).card =
      Nat.multinomial Finset.univ t := by
  have hm := class_sum m t ht
  rw [← hm, ksBoxTriples_card_of_composition]
  congr 1
  exact (class_vector t).symm

theorem ksClassWeight_product (t : Fin 4 → ℕ) :
    (∏ j : Fin 4, ksClassWeight j ^ t j) =
      16 ^ t 0 * 6 ^ (t 1 + t 2) := by
  simp only [Fin.prod_univ_four, ksClassWeight, one_pow, mul_one]
  rw [pow_add]
  ring

theorem ksClass_shape (m : ℕ) (k : RadicalKey) (t : Fin 4 → ℕ)
    (hs : ksSupported m k) (hc : ksKeyClass m k = t) :
    k = pairFinalKey (t 0) (t 2) (t 3) k.degree := by
  have h0 : k.x - k.y = t 0 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 0) hc
  have h2 : k.y = t 2 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 2) hc
  have h3 : k.z = t 3 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 3) hc
  rw [← h0, ← h2, ← h3]
  exact ksSupported_shape m k hs

theorem ksClass_orbit (m : ℕ) (k : RadicalKey) (t : Fin 4 → ℕ)
    (hs : ksSupported m k) (hc : ksKeyClass m k = t) :
    keyOrbitLength m k = 16 ^ t 0 * 6 ^ (t 1 + t 2) := by
  have ht : t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m := by
    rw [← hc]
    exact ksKeyClass_mem m k hs
  have hm := class_sum m t ht
  rw [ksClass_shape m k t hs hc, ← hm]
  exact keyOrbitLength_pairFinalKey (t 0) (t 1) (t 2) (t 3) k.degree

theorem ksClass_boxCount (m : ℕ) (k : RadicalKey) (t : Fin 4 → ℕ)
    (hs : ksSupported m k) (hc : ksKeyClass m k = t) :
    ksBoxCount m k = ksGradedBoxCount m (t 0) (t 2) (t 3) k.degree := by
  rw [ksSupported_boxCount m k hs]
  have h0 : k.x - k.y = t 0 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 0) hc
  have h2 : k.y = t 2 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 2) hc
  have h3 : k.z = t 3 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 3) hc
  rw [h0, h2, h3]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBoxTriples_card_class
#print axioms VOA.DeligneAudit.D4Levi.ksClassWeight_product
#print axioms VOA.DeligneAudit.D4Levi.ksClass_shape
#print axioms VOA.DeligneAudit.D4Levi.ksClass_orbit
#print axioms VOA.DeligneAudit.D4Levi.ksClass_boxCount
