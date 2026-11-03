import VOA.DeligneAudit.D4LeviKSPairRecolourSwap

/-! Count the X positions remaining after `k` paired recolourings. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

theorem pairRemainingPaired_card (b k : ℕ) :
    (Finset.univ.filter fun y : Fin b => k ≤ y.val).card = b - k := by
  classical
  have h : (Finset.univ.filter fun y : Fin b => k ≤ y.val).card =
      (Finset.Ico k b).card := by
    apply Finset.card_bij (fun y _ => y.val)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact Finset.mem_Ico.mpr ⟨hy, y.isLt⟩
    · intro y₁ _ y₂ _ heq
      exact Fin.ext heq
    · intro n hn
      have hn' := Finset.mem_Ico.mp hn
      exact ⟨⟨n, hn'.2⟩, by simpa using hn'.1, rfl⟩
  simpa only [Nat.card_Ico] using h

theorem pairRemainingX_card (a b c k : ℕ) :
    (Finset.univ.filter fun t : PairSource a b c =>
      pairRecolourShape a b c k t = 1).card = a + (b - k) := by
  classical
  calc
    _ = ∑ t : PairSource a b c,
        if pairRecolourShape a b c k t = 1 then 1 else 0 := by
          exact (Finset.sum_boole
            (fun t : PairSource a b c => pairRecolourShape a b c k t = 1)
            Finset.univ).symm
    _ = (∑ y : Fin b, if k ≤ y.val then 1 else 0) + a := by
          simp [Fintype.sum_sum_type, pairRecolourShape,
            not_lt, Finset.sum_const_zero]
    _ = a + (b - k) := by
          simpa only [Finset.sum_boole, pairRemainingPaired_card,
            Nat.add_comm, Nat.cast_id]

theorem pairRemainingX_length (a b c k : ℕ) :
    (Finset.univ.toList.filter fun t : PairSource a b c =>
      pairRecolourShape a b c k t = 1).length = a + (b - k) := by
  classical
  have hn : (Finset.univ.toList.filter fun t : PairSource a b c =>
      pairRecolourShape a b c k t = 1).Nodup :=
    (Finset.nodup_toList _).filter _
  have heq : (Finset.univ.toList.filter fun t : PairSource a b c =>
      pairRecolourShape a b c k t = 1).toFinset =
      Finset.univ.filter fun t => pairRecolourShape a b c k t = 1 := by
    ext t
    simp
  calc
    _ = (Finset.univ.toList.filter fun t : PairSource a b c =>
        pairRecolourShape a b c k t = 1).toFinset.card :=
          (List.toFinset_card_of_nodup hn).symm
    _ = a + (b - k) := by
          rw [heq]
          exact pairRemainingX_card a b c k

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The positional factor in the symmetric conversion is the number of
    X slots left after `k` conversions. -/
theorem pairRecolour_adjoint_symmetric_count
    (ρ : CurrentModule D4sector.f V) (a b c k r : ℕ) (hk : k < b)
    (P : MvPolynomial (PairSource a b c) ℂ)
    (hsym : ∀ t : PairSource a b c,
      pairRecolourShape a b c k t = 1 →
        rename (Equiv.swap (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t) P = P) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairRecolourOperator ρ a b c k P) =
      -((a + (b - k)) •
        pairRecolourOperator ρ a b c (k + 1)
          (X (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) ^ r * P)) := by
  rw [pairRecolour_adjoint_symmetric_op ρ a b c k r hk P hsym]
  rw [pairRemainingX_length]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairRemainingPaired_card
#print axioms VOA.DeligneAudit.D4Levi.pairRemainingX_card
#print axioms VOA.DeligneAudit.D4Levi.pairRemainingX_length
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_symmetric_count
