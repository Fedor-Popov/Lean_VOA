import VOA.DeligneAudit.D4LeviKSBoxCountEnum

/-! Corrected box support: every non-overfull symmetric XYZ shape is retained. -/

namespace VOA.DeligneAudit.D4Levi

/-- Correct support, without the erroneous comparison of `a` and `b₊`. -/
def ksCorrectedSupported (m : ℕ) (k : RadicalKey) : Prop :=
  k.e = 0 ∧ k.u = 0 ∧ k.up = 0 ∧ k.y ≤ k.x ∧ k.x + k.z ≤ m

/-- The actual graded rectangle count at a symmetric XYZ key. -/
noncomputable def ksCorrectedBoxCount (m : ℕ) (k : RadicalKey) : ℕ := by
  classical
  exact if ksCorrectedSupported m k then
    ksGradedBoxCount m (k.x - k.y) k.y k.z k.degree else 0

theorem ksCorrectedBoxCount_pairFinalKey (m a b c d : ℕ)
    (h : a + b + c ≤ m) :
    ksCorrectedBoxCount m (pairFinalKey a b c d) = ksGradedBoxCount m a b c d := by
  simp [ksCorrectedBoxCount, ksCorrectedSupported, pairFinalKey, h,
    show b ≤ a + b by omega]

theorem ksCorrectedBoxCount_zero_of_not_supported (m : ℕ) (k : RadicalKey)
    (h : ¬ ksCorrectedSupported m k) : ksCorrectedBoxCount m k = 0 := by
  exact if_neg h

theorem ksCorrectedSupported_shape (m : ℕ) (k : RadicalKey)
    (h : ksCorrectedSupported m k) :
    k = pairFinalKey (k.x - k.y) k.y k.z k.degree := by
  rcases h with ⟨he, hu, hup, hy, _⟩
  cases k with
  | mk e x u up y z degree =>
    change e = 0 at he
    change u = 0 at hu
    change up = 0 at hup
    change y ≤ x at hy
    simp [pairFinalKey, he, hu, hup, Nat.sub_add_cancel hy]

theorem ksCorrectedKeyClass_mem (m : ℕ) (k : RadicalKey)
    (h : ksCorrectedSupported m k) :
    ksKeyClass m k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m := by
  rw [Finset.mem_piAntidiag]
  constructor
  · simp [ksKeyClass, Fin.sum_univ_four]
    have hy := h.2.2.2.1
    have hm := h.2.2.2.2
    omega
  · intro i _
    exact Finset.mem_univ i

theorem ksCorrectedSupported_boxCount (m : ℕ) (k : RadicalKey)
    (h : ksCorrectedSupported m k) :
    ksCorrectedBoxCount m k = ksGradedBoxCount m (k.x - k.y) k.y k.z k.degree := by
  exact if_pos h

theorem ksCorrectedClass_shape (m : ℕ) (k : RadicalKey) (t : Fin 4 → ℕ)
    (hs : ksCorrectedSupported m k) (hc : ksKeyClass m k = t) :
    k = pairFinalKey (t 0) (t 2) (t 3) k.degree := by
  have h0 : k.x - k.y = t 0 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 0) hc
  have h2 : k.y = t 2 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 2) hc
  have h3 : k.z = t 3 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 3) hc
  rw [← h0, ← h2, ← h3]
  exact ksCorrectedSupported_shape m k hs

theorem ksCorrectedClass_orbit (m : ℕ) (k : RadicalKey) (t : Fin 4 → ℕ)
    (hs : ksCorrectedSupported m k) (hc : ksKeyClass m k = t) :
    keyOrbitLength m k = 16 ^ t 0 * 6 ^ (t 1 + t 2) := by
  have ht : t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m := by
    rw [← hc]
    exact ksCorrectedKeyClass_mem m k hs
  have hm : t 0 + t 1 + t 2 + t 3 = m := by
    simpa only [Fin.sum_univ_four] using (Finset.mem_piAntidiag.mp ht).1
  rw [ksCorrectedClass_shape m k t hs hc, ← hm]
  exact keyOrbitLength_pairFinalKey (t 0) (t 1) (t 2) (t 3) k.degree

theorem ksCorrectedClass_boxCount (m : ℕ) (k : RadicalKey) (t : Fin 4 → ℕ)
    (hs : ksCorrectedSupported m k) (hc : ksKeyClass m k = t) :
    ksCorrectedBoxCount m k = ksGradedBoxCount m (t 0) (t 2) (t 3) k.degree := by
  rw [ksCorrectedSupported_boxCount m k hs]
  have h0 : k.x - k.y = t 0 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 0) hc
  have h2 : k.y = t 2 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 2) hc
  have h3 : k.z = t 3 := by
    simpa [ksKeyClass] using congrArg (fun f : Fin 4 → ℕ => f 3) hc
  rw [h0, h2, h3]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedBoxCount_pairFinalKey
#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedBoxCount_zero_of_not_supported
#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedSupported_shape
#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedKeyClass_mem
#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedSupported_boxCount
#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedClass_shape
#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedClass_orbit
#print axioms VOA.DeligneAudit.D4Levi.ksCorrectedClass_boxCount
