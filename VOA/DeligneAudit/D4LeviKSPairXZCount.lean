import VOA.DeligneAudit.D4LeviKSPairXZSymmetricStep

/-! Count the X slots in the Y-free recolouring. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

theorem pairXZRemainingX_card (a b c k : ℕ) :
    (Finset.univ.filter fun t : PairXZ a b c =>
      pairXZRecolourShape a b c k t = 1).card = a + (b - k) := by
  classical
  calc
    _ = ∑ t : PairXZ a b c,
        if pairXZRecolourShape a b c k t = 1 then 1 else 0 := by
          exact (Finset.sum_boole
            (fun t : PairXZ a b c => pairXZRecolourShape a b c k t = 1)
            Finset.univ).symm
    _ = (∑ y : Fin b, if k ≤ y.val then 1 else 0) + a := by
          simp [Fintype.sum_sum_type, pairXZRecolourShape,
            pairRecolourShape, pairXZSource, not_lt,
            Finset.sum_const_zero]
    _ = a + (b - k) := by
          simpa only [Finset.sum_boole, pairRemainingPaired_card,
            Nat.add_comm, Nat.cast_id]

theorem pairXZRemainingX_length (a b c k : ℕ) :
    (Finset.univ.toList.filter fun t : PairXZ a b c =>
      pairXZRecolourShape a b c k t = 1).length = a + (b - k) := by
  classical
  have hn : (Finset.univ.toList.filter fun t : PairXZ a b c =>
      pairXZRecolourShape a b c k t = 1).Nodup :=
    (Finset.nodup_toList _).filter _
  have heq : (Finset.univ.toList.filter fun t : PairXZ a b c =>
      pairXZRecolourShape a b c k t = 1).toFinset =
      Finset.univ.filter fun t => pairXZRecolourShape a b c k t = 1 := by
    ext t
    simp
  calc
    _ = (Finset.univ.toList.filter fun t : PairXZ a b c =>
        pairXZRecolourShape a b c k t = 1).toFinset.card :=
          (List.toFinset_card_of_nodup hn).symm
    _ = a + (b - k) := by
          rw [heq]
          exact pairXZRemainingX_card a b c k

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairXZRecolour_adjoint_symmetric_count
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (hk : k < b)
    (Q : MvPolynomial (PairXZ a b c) ℂ)
    (hsym : ∀ t : PairXZ a b c,
      pairXZRecolourShape a b c k t = 1 →
        rename (Equiv.swap
          (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t) Q = Q) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairXZRecolourOperator ρ a b c k Q) w =
      -((a + (b - k)) •
        xyzEvaluation ρ w
          (Function.update (pairXZRecolourShape a b c k)
            (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) 3)
          (X (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) ^ r * Q)) := by
  rw [pairXZRecolour_adjoint_symmetric ρ w a b c k r hk Q hsym]
  rw [pairXZRemainingX_length]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZRemainingX_card
#print axioms VOA.DeligneAudit.D4Levi.pairXZRemainingX_length
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolour_adjoint_symmetric_count
