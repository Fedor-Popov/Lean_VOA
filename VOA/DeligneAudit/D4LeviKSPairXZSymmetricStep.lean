import VOA.DeligneAudit.D4LeviKSPairXZRecolour

/-! One symmetric recolouring step on the Y-free coefficient alphabet. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairXZRecolour_adjoint_shift_sum
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairXZRecolourOperator ρ a b c k Q) w =
      -((Finset.univ.toList.filter fun t : PairXZ a b c =>
          pairXZRecolourShape a b c k t = 1).map
        fun t => xyzEvaluation ρ w
          (Function.update (pairXZRecolourShape a b c k) t 3)
          (X t ^ r * Q)).sum := by
  rw [pairXZRecolour_adjoint_positions]
  rw [pairPositionalEvaluation_eq_sum]

/-- X symmetry makes all still-X conversion terms equal, with a factor
    equal to the number of still-X positions. -/
theorem pairXZRecolour_adjoint_symmetric
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (hk : k < b)
    (Q : MvPolynomial (PairXZ a b c) ℂ)
    (hsym : ∀ t : PairXZ a b c,
      pairXZRecolourShape a b c k t = 1 →
        rename (Equiv.swap
          (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t) Q = Q) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairXZRecolourOperator ρ a b c k Q) w =
      -((Finset.univ.toList.filter fun t : PairXZ a b c =>
          pairXZRecolourShape a b c k t = 1).length •
        xyzEvaluation ρ w
          (Function.update (pairXZRecolourShape a b c k)
            (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) 3)
          (X (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) ^ r * Q)) := by
  let s : PairXZ a b c := Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))
  let shape := pairXZRecolourShape a b c k
  have hs : shape s = 1 := by
    exact pairRecolourShape_unpaired_at a b c k ⟨k, hk⟩ (le_refl k)
  let C := xyzEvaluation ρ w (Function.update shape s 3) (X s ^ r * Q)
  have hsum (L : List (PairXZ a b c))
      (hL : ∀ t ∈ L, shape t = 1) :
      (L.map fun t => xyzEvaluation ρ w (Function.update shape t 3)
        (X t ^ r * Q)).sum = L.length • C := by
    induction L with
    | nil => simp
    | cons t ts ih =>
        have ht : shape t = 1 := hL t (List.mem_cons_self)
        have hts : ∀ u ∈ ts, shape u = 1 := by
          intro u hu
          exact hL u (List.mem_cons_of_mem t hu)
        have hterm : xyzEvaluation ρ w (Function.update shape t 3)
            (X t ^ r * Q) = C := by
          exact pairConvertedTerm_eq_of_swap ρ w shape s t
            (hs.trans ht.symm) r Q (hsym t ht)
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          hterm, ih hts]
        simp [succ_nsmul, add_comm]
  rw [pairXZRecolour_adjoint_shift_sum]
  congr 1
  apply hsum
  intro t ht
  exact of_decide_eq_true (List.mem_filter.mp ht).2

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolour_adjoint_shift_sum
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolour_adjoint_symmetric
