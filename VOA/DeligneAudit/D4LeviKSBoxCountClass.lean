import VOA.DeligneAudit.D4LeviKSBoxDegreeAggregate

/-! Recover the four multinomial classes from a supported radical key. -/

namespace VOA.DeligneAudit.D4Levi

def ksSupported (m : ℕ) (k : RadicalKey) : Prop :=
  k.e = 0 ∧ k.u = 0 ∧ k.up = 0 ∧ k.y ≤ k.x ∧
    k.x + k.z ≤ m ∧ k.x - k.y ≤ m - k.x - k.z

def ksKeyClass (m : ℕ) (k : RadicalKey) : Fin 4 → ℕ :=
  ![k.x - k.y, m - k.x - k.z, k.y, k.z]

theorem ksBoxCount_zero_of_not_supported (m : ℕ) (k : RadicalKey)
    (h : ¬ ksSupported m k) : ksBoxCount m k = 0 := by
  exact if_neg h

theorem ksSupported_shape (m : ℕ) (k : RadicalKey)
    (h : ksSupported m k) :
    k = pairFinalKey (k.x - k.y) k.y k.z k.degree := by
  rcases h with ⟨he, hu, hup, hy, _, _⟩
  cases k with
  | mk e x u up y z degree =>
    change e = 0 at he
    change u = 0 at hu
    change up = 0 at hup
    change y ≤ x at hy
    simp [pairFinalKey, he, hu, hup, Nat.sub_add_cancel hy]

theorem ksKeyClass_mem (m : ℕ) (k : RadicalKey)
    (h : ksSupported m k) :
    ksKeyClass m k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m := by
  rw [Finset.mem_piAntidiag]
  constructor
  · simp [ksKeyClass, Fin.sum_univ_four]
    have hy := h.2.2.2.1
    have hm := h.2.2.2.2.1
    omega
  · intro i _
    exact Finset.mem_univ i

theorem ksSupported_boxCount (m : ℕ) (k : RadicalKey)
    (h : ksSupported m k) :
    ksBoxCount m k = ksGradedBoxCount m (k.x - k.y) k.y k.z k.degree := by
  exact if_pos h

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_zero_of_not_supported
#print axioms VOA.DeligneAudit.D4Levi.ksSupported_shape
#print axioms VOA.DeligneAudit.D4Levi.ksKeyClass_mem
#print axioms VOA.DeligneAudit.D4Levi.ksSupported_boxCount
