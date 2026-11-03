import VOA.DeligneAudit.D4LeviKSPairXZInvariant
import VOA.DeligneAudit.D4LeviKSPairRecolourIter

/-! Iterate recolouring on a Y-free PAIR coefficient. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable def pairXZEarlierFactor (a b c k : ℕ) (γ : Fin b → ℕ) :
    MvPolynomial (PairXZ a b c) ℂ :=
  ∏ y ∈ (Finset.univ.filter fun y : Fin b => y.val < k),
    X (Sum.inl (Sum.inl y)) ^ γ y

theorem pairXZEarlierFactor_swap (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) (t : PairXZ a b c)
    (ht : pairXZRecolourShape a b c k t = 1) :
    rename (Equiv.swap (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t)
      (pairXZEarlierFactor a b c k γ) =
        pairXZEarlierFactor a b c k γ := by
  classical
  simp only [pairXZEarlierFactor, map_prod, map_pow, rename_X]
  apply Finset.prod_congr rfl
  intro y hy
  have hylt : y.val < k := (Finset.mem_filter.mp hy).2
  have hys : (Sum.inl (Sum.inl y) : PairXZ a b c) ≠
      Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b)) := by
    intro heq
    have hv : y.val = k := congrArg (fun u : PairXZ a b c =>
      match u with
      | Sum.inl (Sum.inl z) => z.val
      | _ => 0) heq
    omega
  have hyt : (Sum.inl (Sum.inl y) : PairXZ a b c) ≠ t := by
    intro heq
    subst t
    simp [pairXZRecolourShape, pairRecolourShape, pairXZSource, hylt] at ht
  simp [Equiv.swap_apply_of_ne_of_ne hys hyt]

theorem pairXZShifted_swap (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ)
    (hQ : ∀ s t : Fin b ⊕ Fin a,
      rename (Equiv.swap (Sum.inl s) (Sum.inl t)) Q = Q)
    (t : PairXZ a b c) (ht : pairXZRecolourShape a b c k t = 1) :
    rename (Equiv.swap (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t)
      (pairXZEarlierFactor a b c k γ * Q) =
        pairXZEarlierFactor a b c k γ * Q := by
  rw [map_mul, pairXZEarlierFactor_swap a b c k hk γ t ht]
  rcases t with x | z
  · exact congrArg _ (hQ (Sum.inl ⟨k, hk⟩) x)
  · simp [pairXZRecolourShape, pairRecolourShape, pairXZSource] at ht

theorem pairXZEarlierFactor_succ (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) :
    pairXZEarlierFactor a b c (k + 1) γ =
      X (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) ^ γ ⟨k, hk⟩ *
        pairXZEarlierFactor a b c k γ := by
  classical
  have heq : (Finset.univ.filter fun y : Fin b => y.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter fun y : Fin b => y.val < k) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hy
      by_cases h : y.val = k
      · left
        exact Fin.ext h
      · right
        omega
    · rintro (h | h)
      · subst y
        simp
      · omega
  have hn : (⟨k, hk⟩ : Fin b) ∉
      (Finset.univ.filter fun y : Fin b => y.val < k) := by simp
  simp only [pairXZEarlierFactor, heq]
  rw [Finset.prod_insert hn]

theorem pairXZRecolourShape_succ (a b c k : ℕ) (hk : k < b) :
    pairXZRecolourShape a b c (k + 1) =
      Function.update (pairXZRecolourShape a b c k)
        (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) 3 := by
  funext t
  have h := pairRecolourShape_step a b c k hk (pairXZSource a b c t)
  rcases t with (y | x) | z <;>
    simpa [pairXZRecolourShape, pairXZSource, Function.update] using h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairXZRecolour_adjoint_shifted
    (ρ : CurrentModule D4sector.f V) (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ)
    (hQ : ∀ s t : Fin b ⊕ Fin a,
      rename (Equiv.swap (Sum.inl s) (Sum.inl t)) Q = Q) :
    pairAdjoint (ρ.op (17 : Fin 28)) [γ ⟨k, hk⟩]
        (pairXZRecolourOperator ρ a b c k
          (pairXZEarlierFactor a b c k γ * Q)) =
      -((a + (b - k)) •
        pairXZRecolourOperator ρ a b c (k + 1)
          (pairXZEarlierFactor a b c (k + 1) γ * Q)) := by
  ext w
  rw [pairXZRecolour_adjoint_symmetric_count ρ w a b c k (γ ⟨k, hk⟩) hk
    (pairXZEarlierFactor a b c k γ * Q)
    (pairXZShifted_swap a b c k hk γ Q hQ)]
  simp only [LinearMap.neg_apply, LinearMap.smul_apply]
  rw [pairXZEarlierFactor_succ a b c k hk γ]
  simp only [pairXZRecolourOperator_apply, mul_assoc]
  rw [pairXZRecolourShape_succ a b c k hk]

theorem pairXZRecolour_adjoint_iterated
    (ρ : CurrentModule D4sector.f V) (a b c : ℕ)
    (γ : ℕ → ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ)
    (hQ : ∀ s t : Fin b ⊕ Fin a,
      rename (Equiv.swap (Sum.inl s) (Sum.inl t)) Q = Q)
    (k : ℕ) (hk : k ≤ b) :
    pairAdjoint (ρ.op (17 : Fin 28)) ((List.range k).map γ)
        (pairXZRecolourOperator ρ a b c 0 Q) =
      pairIterCoefficient a b k •
        pairXZRecolourOperator ρ a b c k
          (pairXZEarlierFactor a b c k (fun y => γ y.val) * Q) := by
  induction k with
  | zero => simp [pairAdjoint, pairIterCoefficient, pairXZEarlierFactor]
  | succ k ih =>
      have hk' : k < b := by omega
      rw [List.range_succ, List.map_append, pairAdjoint_append]
      simp only [List.map_singleton]
      rw [ih (Nat.le_of_lt hk')]
      rw [pairAdjoint_smul]
      rw [pairXZRecolour_adjoint_shifted ρ a b c k hk'
        (fun y : Fin b => γ y.val) Q hQ]
      rw [smul_neg, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      rw [pairIterCoefficient, ← neg_smul]
      congr 1
      rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hk')]
      ring

theorem pairXZRecolour_adjoint_full
    (ρ : CurrentModule D4sector.f V) (a b c : ℕ)
    (γ : ℕ → ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ)
    (hQ : ∀ s t : Fin b ⊕ Fin a,
      rename (Equiv.swap (Sum.inl s) (Sum.inl t)) Q = Q) :
    pairAdjoint (ρ.op (17 : Fin 28)) ((List.range b).map γ)
        (pairXZRecolourOperator ρ a b c 0 Q) =
      ((-1 : ℂ) ^ b * (Nat.descFactorial (a + b) b : ℂ)) •
        pairXZRecolourOperator ρ a b c b
          (pairXZEarlierFactor a b c b (fun y => γ y.val) * Q) := by
  rw [pairXZRecolour_adjoint_iterated ρ a b c γ Q hQ b le_rfl]
  rw [pairIterCoefficient_descFactorial a b b le_rfl]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZEarlierFactor_swap
#print axioms VOA.DeligneAudit.D4Levi.pairXZShifted_swap
#print axioms VOA.DeligneAudit.D4Levi.pairXZEarlierFactor_succ
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolourShape_succ
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolour_adjoint_shifted
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolour_adjoint_iterated
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolour_adjoint_full
