/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonSelectedDiagonals
import VOA.Commutative.GordonPairedEvaluation
import VOA.Commutative.GordonResidualFiltration

/-! # Genuine auxiliary relations in the paired Gordon geometry -/

namespace VOA.GordonPairedRelations

open scoped BigOperators
open MvPolynomial VOA.GordonFunctionalCoefficients VOA.GordonRestrictedDual
open VOA.GordonSelectedDiagonals VOA.GordonPairedEvaluation VOA.GordonFiltration
open VOA.GordonBlockEquiv VOA.GordonResidualFiltration

noncomputable section

variable {K ρ α β γ τ : Type*} [Field K]

abbrev Residual (α β γ : Type*) := α ⊕ (β ⊕ γ)

def residualColor : Residual α β γ → Fin 3 :=
  Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 2) (fun _ ↦ 1))

def sourceColor : Source ρ α β γ → Fin 3 :=
  Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 2) (fun _ ↦ 1))

def residualSource : Residual α β γ → Source ρ α β γ
  | .inl x => .inl (.inr x)
  | .inr (.inl y) => .inr (.inl (.inr y))
  | .inr (.inr z) => .inr (.inr z)

/-- Evaluate all paired tau blocks, retaining the independent residual particles. -/
def clusterIndex (f : ρ → τ) : Source ρ α β γ → Target τ α β γ :=
  Sum.map f id ∘ pairIndex

def clusterEval (f : ρ → τ) :
    MvPolynomial (Source ρ α β γ) K →ₐ[K] MvPolynomial (Target τ α β γ) K :=
  rename (clusterIndex f)

theorem clusterEval_eq (f : ρ → τ) (F : MvPolynomial (Source ρ α β γ) K) :
    clusterEval f F = residualEval f (pairEval F) := by
  simp [clusterEval, residualEval, pairEval, clusterIndex, rename_rename]

/-- Select one residual particle and `m` paired e/f particles. -/
def residualSelection {m : ℕ} (h : Fin m ↪ ρ) (d : Residual α β γ) :
    RelationSlots m ↪ Source ρ α β γ where
  toFun := Sum.elim (fun _ ↦ residualSource d)
    (Sum.elim (fun j ↦ Sum.inl (Sum.inl (h j)))
      (fun j ↦ Sum.inr (Sum.inl (Sum.inl (h j)))))
  inj' := by
    rintro (x | (x | x)) (y | (y | y)) heq <;>
      rcases d with d | (d | d) <;>
      simp_all [residualSource, h.injective.eq_iff]

theorem residualSelection_color {m : ℕ} (h : Fin m ↪ ρ) (d : Residual α β γ)
    (j : RelationSlots m) :
    sourceColor (residualSelection h d j) = relationColor m (residualColor d) j := by
  rcases j with j | (j | j) <;> rcases d with d | (d | d) <;> rfl

variable [Fintype ρ] [Fintype α] [Fintype β] [Fintype γ] [Fintype τ]
variable [DecidableEq ρ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq τ]

/-- The source functional model forces a linear block-residual factor for every
block containing at least `m` paired particles and every residual species. -/
theorem block_residual_dvd (m D : ℕ) (f : ρ → τ) (u : τ)
    (hu : m ≤ blockSize f u) (d : Residual α β γ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ))) :
    (X (Sum.inl u) - X (Sum.inr d) : MvPolynomial (Target τ α β γ) K) ∣ clusterEval f F := by
  let hf : Fin m ↪ {x : ρ // f x = u} :=
    (Function.Embedding.nonempty_of_card_le (by
      simpa [Fintype.card_fin, ← blockSize_eq_card_fiber] using hu)).some
  let h : Fin m ↪ ρ := hf.trans (Function.Embedding.subtype _)
  have hh (j : Fin m) : f (h j) = u := (hf j).property
  apply block_residual_factor m D sourceColor F hF (clusterIndex f)
    (Sum.inl u) (Sum.inr d) (by simp) (residualColor d) (residualSelection h d)
    (residualSelection_color h d)
  · rcases d with d | (d | d) <;> rfl
  · rintro (j | j) <;> simp [clusterIndex, pairIndex, residualSelection, hh]

/-- Select an e-relation entirely inside `m+1` distinct paired variables. -/
def largeSelection {m : ℕ} (h : Fin (m + 1) ↪ ρ) :
    RelationSlots m ↪ Source ρ α β γ where
  toFun := Sum.elim (fun _ ↦ Sum.inl (Sum.inl (h 0)))
    (Sum.elim (fun j ↦ Sum.inl (Sum.inl (h j.succ)))
      (fun j ↦ Sum.inr (Sum.inl (Sum.inl (h j.succ)))))
  inj' := by
    rintro (x | (x | x)) (y | (y | y)) heq <;>
      simp_all [h.injective.eq_iff]
    exact (Fin.succ_ne_zero _) heq.symm

/-- Every block larger than `m` vanishes identically in the actual functional model. -/
theorem large_block_eval_eq_zero (m D : ℕ) (f : ρ → τ) (u : τ)
    (hu : m < blockSize f u) (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ))) :
    clusterEval f F = 0 := by
  let hf : Fin (m + 1) ↪ {x : ρ // f x = u} :=
    (Function.Embedding.nonempty_of_card_le (by
      simpa [Fintype.card_fin, ← blockSize_eq_card_fiber] using hu)).some
  let h : Fin (m + 1) ↪ ρ := hf.trans (Function.Embedding.subtype _)
  have hh (j : Fin (m + 1)) : f (h j) = u := (hf j).property
  have hz := functionalModel_selected_vanish (A := MvPolynomial (Target τ α β γ) K)
    m D sourceColor F hF 0 (largeSelection h) (by rintro (j | (j | j)) <;> rfl)
    (fun j ↦ X (clusterIndex f j)) (X (Sum.inl u)) ?_
  · have heq : clusterEval (K := K) (α := α) (β := β) (γ := γ) f =
        aeval (fun j ↦ X (clusterIndex f j)) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [clusterEval]
    rw [heq]
    exact hz
  · rintro (j | (j | j)) <;> simp [largeSelection, clusterIndex, pairIndex, hh]

/-- Permute the paired e/f labels simultaneously. -/
def pairSourcePerm (e : Equiv.Perm ρ) : Equiv.Perm (Source ρ α β γ) :=
  Equiv.sumCongr (Equiv.sumCongr e (Equiv.refl α))
    (Equiv.sumCongr (Equiv.sumCongr e (Equiv.refl β)) (Equiv.refl γ))

/-- Paired evaluation of the genuine functional model is symmetric in all tau variables. -/
theorem functionalModel_pair_symmetry (m D : ℕ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (e : Equiv.Perm ρ) :
    rename (Equiv.sumCongr e (Equiv.refl (Residual α β γ))) (pairEval F) = pairEval F := by
  have hinv : rename (pairSourcePerm e) F = F := by
    obtain ⟨L, rfl⟩ := hF
    apply particleMap_rename
    rintro ((j | j) | ((j | j) | j)) <;> rfl
  have hindex : Equiv.sumCongr e (Equiv.refl (Residual α β γ)) ∘ pairIndex =
      pairIndex ∘ pairSourcePerm (α := α) (β := β) (γ := γ) e := by
    funext j
    rcases j with (j | j) | ((j | j) | j) <;> rfl
  simp only [pairEval, rename_rename]
  rw [hindex, ← rename_rename, hinv]

/-- Residual e/f permutations are inherited from the actual quotient-dual symmetry. -/
theorem functionalModel_residual_symmetry (m D : ℕ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (e : Equiv.Perm α) (f : Equiv.Perm β) :
    rename (sourcePerm e f) F = F := by
  obtain ⟨L, rfl⟩ := hF
  apply particleMap_rename
  rintro ((j | j) | ((j | j) | j)) <;> rfl

/-- The actual functional model in a genuine next-pair kernel has the complete
residual cross-species divisor after paired evaluation. -/
theorem functionalModel_residualDivisor_dvd (m D : ℕ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (x₀ : α) (y₀ : β) (hnext : nextPairEval x₀ y₀ F = 0) :
    residualDivisor (K := K) (ρ := ρ) (γ := γ) ∣ pairEval F :=
  residualDivisor_dvd x₀ y₀ F (functionalModel_residual_symmetry m D F hF) hnext

end
end VOA.GordonPairedRelations
