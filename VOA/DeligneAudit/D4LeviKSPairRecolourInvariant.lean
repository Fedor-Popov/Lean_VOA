import VOA.DeligneAudit.D4LeviKSPairRecolourCount
import VOA.DeligneAudit.D4LeviKSPairSymmetricMap

/-! Symmetry of the X alphabet in the PAIR source algebra. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

theorem pairSourceXPsum_rename_x (a b c r : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    rename (Equiv.Perm.sumCongr e (Equiv.refl (Fin b ⊕ Fin c)))
      (pairSourceXPsum a b c r) = pairSourceXPsum a b c r := by
  classical
  simp only [pairSourceXPsum, map_sum, map_pow, rename_X]
  change (∑ x : Fin b ⊕ Fin a, X (Sum.inl (e x)) ^ r) =
    ∑ x : Fin b ⊕ Fin a, X (Sum.inl x) ^ r
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem sourceYPsum_rename_x (a b c r : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    rename (Equiv.Perm.sumCongr e (Equiv.refl (Fin b ⊕ Fin c)))
      (sourceYPsum a b c r) = sourceYPsum a b c r := by
  simp [sourceYPsum]

theorem pairSourceZPsum_rename_x (a b c r : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    rename (Equiv.Perm.sumCongr e (Equiv.refl (Fin b ⊕ Fin c)))
      (pairSourceZPsum a b c r) = pairSourceZPsum a b c r := by
  simp [pairSourceZPsum]

theorem pairSourceSymmetric_rename_x (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a))
    (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) :
    rename (Equiv.Perm.sumCongr e (Equiv.refl (Fin b ⊕ Fin c))) P = P := by
  induction hP using Algebra.adjoin_induction with
  | mem P hP =>
      rcases hP with ⟨⟨j, r⟩, rfl⟩
      fin_cases j
      · simpa [pairSourcePower] using pairSourceXPsum_rename_x a b c r e
      · simpa [pairSourcePower] using sourceYPsum_rename_x a b c r e
      · simpa [pairSourcePower] using pairSourceZPsum_rename_x a b c r e
  | algebraMap z => simp
  | add P Q _ _ hP hQ => simp [hP, hQ]
  | mul P Q _ _ hP hQ => simp [hP, hQ]

theorem pairSourceSymmetric_swap_x (a b c : ℕ)
    (s t : Fin b ⊕ Fin a)
    (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) :
    rename (Equiv.swap (Sum.inl s) (Sum.inl t)) P = P := by
  rw [← Equiv.Perm.sumCongr_swap_refl]
  exact pairSourceSymmetric_rename_x a b c (Equiv.swap s t) P hP

/-- Shifts already assigned to the first `k` paired positions. -/
noncomputable def pairEarlierXFactor (a b c k : ℕ) (γ : Fin b → ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  ∏ y ∈ (Finset.univ.filter fun y : Fin b => y.val < k),
    X (Sum.inl (Sum.inl y)) ^ γ y

theorem pairEarlierXFactor_swap (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) (t : PairSource a b c)
    (ht : pairRecolourShape a b c k t = 1) :
    rename (Equiv.swap (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t)
      (pairEarlierXFactor a b c k γ) =
        pairEarlierXFactor a b c k γ := by
  classical
  simp only [pairEarlierXFactor, map_prod, map_pow, rename_X]
  apply Finset.prod_congr rfl
  intro y hy
  have hylt : y.val < k := (Finset.mem_filter.mp hy).2
  have hys : (Sum.inl (Sum.inl y) : PairSource a b c) ≠
      Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b)) := by
    intro heq
    have hv : y.val = k := congrArg (fun u : PairSource a b c =>
      match u with
      | Sum.inl (Sum.inl z) => z.val
      | _ => 0) heq
    omega
  have hyt : (Sum.inl (Sum.inl y) : PairSource a b c) ≠ t := by
    intro heq
    subst t
    simp [pairRecolourShape, hylt] at ht
  simp [Equiv.swap_apply_of_ne_of_ne hys hyt]

theorem pairSourceSymmetric_shifted_swap (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c)
    (t : PairSource a b c)
    (ht : pairRecolourShape a b c k t = 1) :
    rename (Equiv.swap (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) t)
        (pairEarlierXFactor a b c k γ * P) =
      pairEarlierXFactor a b c k γ * P := by
  rw [map_mul, pairEarlierXFactor_swap a b c k hk γ t ht]
  rcases t with x | yz
  · rw [pairSourceSymmetric_swap_x a b c (Sum.inl ⟨k, hk⟩) x P hP]
  · rcases yz with y | z
    · simp [pairRecolourShape] at ht
    · simp [pairRecolourShape] at ht

theorem pairEarlierXFactor_succ (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) :
    pairEarlierXFactor a b c (k + 1) γ =
      X (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin b))) ^ γ ⟨k, hk⟩ *
        pairEarlierXFactor a b c k γ := by
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
  simp only [pairEarlierXFactor, heq]
  rw [Finset.prod_insert hn]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Recolouring after the earlier shifts has the exact falling-factorial
    coefficient needed for the induction. -/
theorem pairRecolour_adjoint_shifted
    (ρ : CurrentModule D4sector.f V) (a b c k : ℕ) (hk : k < b)
    (γ : Fin b → ℕ) (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) :
    pairAdjoint (ρ.op (17 : Fin 28)) [γ ⟨k, hk⟩]
        (pairRecolourOperator ρ a b c k
          (pairEarlierXFactor a b c k γ * P)) =
      -((a + (b - k)) •
        pairRecolourOperator ρ a b c (k + 1)
          (pairEarlierXFactor a b c (k + 1) γ * P)) := by
  rw [pairRecolour_adjoint_symmetric_count ρ a b c k (γ ⟨k, hk⟩) hk
    (pairEarlierXFactor a b c k γ * P)
    (pairSourceSymmetric_shifted_swap a b c k hk γ P hP)]
  rw [pairEarlierXFactor_succ a b c k hk γ]
  simp only [mul_assoc]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSourceXPsum_rename_x
#print axioms VOA.DeligneAudit.D4Levi.sourceYPsum_rename_x
#print axioms VOA.DeligneAudit.D4Levi.pairSourceZPsum_rename_x
#print axioms VOA.DeligneAudit.D4Levi.pairSourceSymmetric_rename_x
#print axioms VOA.DeligneAudit.D4Levi.pairSourceSymmetric_swap_x
#print axioms VOA.DeligneAudit.D4Levi.pairEarlierXFactor_swap
#print axioms VOA.DeligneAudit.D4Levi.pairSourceSymmetric_shifted_swap
#print axioms VOA.DeligneAudit.D4Levi.pairEarlierXFactor_succ
#print axioms VOA.DeligneAudit.D4Levi.pairRecolour_adjoint_shifted
