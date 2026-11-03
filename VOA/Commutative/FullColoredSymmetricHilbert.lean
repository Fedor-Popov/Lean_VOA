/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.ColoredSymmetricHilbert

namespace VOA.ColoredSymmetricHilbert
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [Field K] {τ κ α β γ : Type u}

def fullColorFamily (color : τ → κ) : κ ⊕ (Unit ⊕ (Unit ⊕ Unit)) → Type u
  | Sum.inl c => {i // color i = c}
  | Sum.inr (Sum.inl _) => α
  | Sum.inr (Sum.inr (Sum.inl _)) => β
  | Sum.inr (Sum.inr (Sum.inr _)) => γ

def fullFiberEquiv (color : τ → κ) :
    (Σ c, fullColorFamily (α := α) (β := β) (γ := γ) color c) ≃ τ ⊕ (α ⊕ (β ⊕ γ)) where
  toFun
    | ⟨Sum.inl _, i⟩ => Sum.inl i.val
    | ⟨Sum.inr (Sum.inl _), i⟩ => Sum.inr (Sum.inl i)
    | ⟨Sum.inr (Sum.inr (Sum.inl _)), i⟩ => Sum.inr (Sum.inr (Sum.inl i))
    | ⟨Sum.inr (Sum.inr (Sum.inr _)), i⟩ => Sum.inr (Sum.inr (Sum.inr i))
  invFun
    | Sum.inl i => ⟨Sum.inl (color i), ⟨i, rfl⟩⟩
    | Sum.inr (Sum.inl i) => ⟨Sum.inr (Sum.inl ()), i⟩
    | Sum.inr (Sum.inr (Sum.inl i)) => ⟨Sum.inr (Sum.inr (Sum.inl ())), i⟩
    | Sum.inr (Sum.inr (Sum.inr i)) => ⟨Sum.inr (Sum.inr (Sum.inr ())), i⟩
  left_inv x := by
    rcases x with ⟨c, i⟩
    rcases c with c | c
    · rcases i with ⟨i, hi⟩; subst c; rfl
    · rcases c with c | c
      · cases c; rfl
      · rcases c with c | c <;> cases c <;> rfl
  right_inv x := by rcases x with i | i; rfl; rcases i with i | i; rfl; rcases i <;> rfl

def fullColorPermutationEquiv (color : τ → κ) :
    (∀ c, Equiv.Perm (fullColorFamily (α := α) (β := β) (γ := γ) color c)) ≃
      ColorPermutation color × (Equiv.Perm α × (Equiv.Perm β × Equiv.Perm γ)) where
  toFun h := (colorPermutationEquiv color (fun c => h (Sum.inl c)),
    h (Sum.inr (Sum.inl ())), h (Sum.inr (Sum.inr (Sum.inl ()))),
    h (Sum.inr (Sum.inr (Sum.inr ()))))
  invFun h
    | Sum.inl c => fiberPermutation color h.1 c
    | Sum.inr (Sum.inl _) => h.2.1
    | Sum.inr (Sum.inr (Sum.inl _)) => h.2.2.1
    | Sum.inr (Sum.inr (Sum.inr _)) => h.2.2.2
  left_inv h := by
    funext c
    rcases c with c | c
    · exact congrFun ((colorPermutationEquiv color).symm_apply_apply (fun c => h (Sum.inl c))) c
    · rcases c with c | c
      · cases c; rfl
      · rcases c with c | c <;> cases c <;> rfl
  right_inv h := by
    apply Prod.ext
    · exact (colorPermutationEquiv color).apply_symm_apply h.1
    · rfl

def fullColorAction (color : τ → κ)
    (h : ColorPermutation color × (Equiv.Perm α × (Equiv.Perm β × Equiv.Perm γ))) :
    Equiv.Perm (τ ⊕ (α ⊕ (β ⊕ γ))) :=
  Equiv.sumCongr h.1.val (Equiv.sumCongr h.2.1 (Equiv.sumCongr h.2.2.1 h.2.2.2))

theorem fullColorPiece_finrank_eq_coeff [Fintype τ] [Fintype κ]
    [Fintype α] [Fintype β] [Fintype γ] (color : τ → κ) (d : ℕ) :
    (Module.finrank K (actionPiece (K := K)
      (fullColorAction (α := α) (β := β) (γ := γ) color) d) : ℚ) =
      PowerSeries.coeff d ((∏ c, (QSeries.reciprocalQFactorial
        (Nat.card {i // color i = c}) : PowerSeries ℚ)) *
        QSeries.reciprocalQFactorial (Fintype.card α) *
        QSeries.reciprocalQFactorial (Fintype.card β) *
        QSeries.reciprocalQFactorial (Fintype.card γ)) := by
  classical
  letI : ∀ c, Fintype (fullColorFamily (α := α) (β := β) (γ := γ) color c) := fun c => by
    rcases c with c | c
    · exact inferInstanceAs (Fintype {i // color i = c})
    · rcases c with c | c
      · exact inferInstanceAs (Fintype α)
      · rcases c with c | c
        · exact inferInstanceAs (Fintype β)
        · exact inferInstanceAs (Fintype γ)
  have he := (actionPieceEquiv (K := K) (fun h => Equiv.sigmaCongrRight h)
    (fullColorAction (α := α) (β := β) (γ := γ) color) (fullFiberEquiv color) (fullColorPermutationEquiv color) (by
      intro h i
      rcases i with ⟨c, i⟩
      rcases c with c | c
      · rcases i with ⟨i, hi⟩; subst c; rfl
      · rcases c with c | c
        · cases c; rfl
        · rcases c with c | c <;> cases c <;> rfl) d).finrank_eq
  rw [← he, sigmaPiece_finrank_eq_coeff]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique]
  simp only [← Nat.card_eq_fintype_card]
  simp [fullColorFamily, mul_assoc]

end
end VOA.ColoredSymmetricHilbert
