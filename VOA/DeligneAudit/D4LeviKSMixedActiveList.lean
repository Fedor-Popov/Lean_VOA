import VOA.DeligneAudit.D4LeviKSMixedSeedEvaluation

/-! Relabel the active mixed alphabets by the corresponding colour lists. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def rxActiveIndex (a b c : ℕ) :
    Fin (c + (a + b)) ≃ Fin c ⊕ (Fin b ⊕ Fin a) :=
  (finSumFinEquiv (m := c) (n := a + b)).symm |>.trans
    (Equiv.sumCongr (Equiv.refl (Fin c))
      ((finCongr (Nat.add_comm a b)).trans
        (finSumFinEquiv (m := b) (n := a)).symm))

def ryActiveIndex (b c : ℕ) : Fin (c + b) ≃ Fin c ⊕ Fin b :=
  (finSumFinEquiv (m := c) (n := b)).symm

private theorem rxActiveIndex_left (a b c : ℕ) (i : Fin c) :
    rxActiveIndex a b c (Fin.castAdd (a + b) i) = Sum.inl i := by
  simp [rxActiveIndex]

private theorem rxActiveIndex_right (a b c : ℕ) (i : Fin (a + b)) :
    (rxActiveIndex a b c (Fin.natAdd c i)).isRight := by
  simp [rxActiveIndex]

private theorem ryActiveIndex_left (b c : ℕ) (i : Fin c) :
    ryActiveIndex b c (Fin.castAdd b i) = Sum.inl i := by
  simp [ryActiveIndex]

private theorem ryActiveIndex_right (b c : ℕ) (i : Fin b) :
    ryActiveIndex b c (Fin.natAdd c i) = Sum.inr i := by
  simp [ryActiveIndex]

theorem rxActiveIndex_shape (a b c : ℕ) :
    (fun t : Fin c ⊕ (Fin b ⊕ Fin a) =>
      match t with
      | Sum.inl _ => (5 : Fin 6)
      | Sum.inr _ => 1) ∘ rxActiveIndex a b c =
        (fun i : Fin (c + (a + b)) =>
          (List.replicate c (5 : Fin 6) ++
            List.replicate (a + b) (1 : Fin 6))[i.val]'(by
              simpa using i.isLt)) := by
  funext i
  let p := (finSumFinEquiv (m := c) (n := a + b)).symm i
  rcases hp : p with z | x
  · have hi : i = Fin.castAdd (a + b) z := by
      exact (Equiv.symm_apply_eq _).mp hp
    subst i
    simp [rxActiveIndex_left]
  · have hi : i = Fin.natAdd c x := by
      exact (Equiv.symm_apply_eq _).mp hp
    subst i
    simp [rxActiveIndex_right, rxActiveIndex]

theorem ryActiveIndex_shape (b c : ℕ) :
    (fun t : Fin c ⊕ Fin b =>
      match t with
      | Sum.inl _ => (5 : Fin 6)
      | Sum.inr _ => 4) ∘ ryActiveIndex b c =
        (fun i : Fin (c + b) =>
          (List.replicate c (5 : Fin 6) ++
            List.replicate b (4 : Fin 6))[i.val]'(by
              simpa using i.isLt)) := by
  funext i
  let p := (finSumFinEquiv (m := c) (n := b)).symm i
  rcases hp : p with z | y
  · have hi : i = Fin.castAdd b z := by
      exact (Equiv.symm_apply_eq _).mp hp
    subst i
    simp [ryActiveIndex_left]
  · have hi : i = Fin.natAdd c y := by
      exact (Equiv.symm_apply_eq _).mp hp
    subst i
    simp [ryActiveIndex_right]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rxActiveIndex_shape
#print axioms VOA.DeligneAudit.D4Levi.ryActiveIndex_shape
