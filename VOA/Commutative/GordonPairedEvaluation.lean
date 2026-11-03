/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonDivisor

/-! # Paired evaluation kernels and residual cross-species factors

Paired e/f variables are identified at labeled tau variables. Identifying one further
residual e/f pair is the next paired evaluation. Its actual kernel, together with
separate permutation symmetry, forces all residual e-f collision factors.
-/

namespace VOA.GordonPairedEvaluation

open scoped BigOperators
open MvPolynomial VOA.GordonCommonFactors VOA.GordonDivisor

noncomputable section

variable {K ρ α β γ : Type*} [Field K]

abbrev Source (ρ α β γ : Type*) := (ρ ⊕ α) ⊕ ((ρ ⊕ β) ⊕ γ)
abbrev Target (ρ α β γ : Type*) := ρ ⊕ (α ⊕ (β ⊕ γ))

/-- Identify each designated e/f pair at its common tau label. -/
def pairIndex : Source ρ α β γ → Target ρ α β γ
  | .inl (.inl t) => .inl t
  | .inl (.inr x) => .inr (.inl x)
  | .inr (.inl (.inl t)) => .inl t
  | .inr (.inl (.inr y)) => .inr (.inr (.inl y))
  | .inr (.inr z) => .inr (.inr (.inr z))

def pairEval : MvPolynomial (Source ρ α β γ) K →ₐ[K] MvPolynomial (Target ρ α β γ) K :=
  rename pairIndex

def eLabel (x : α) : Target ρ α β γ := .inr (.inl x)
def fLabel (y : β) : Target ρ α β γ := .inr (.inr (.inl y))

def sourcePerm (e : Equiv.Perm α) (f : Equiv.Perm β) : Equiv.Perm (Source ρ α β γ) :=
  Equiv.sumCongr (Equiv.sumCongr (Equiv.refl ρ) e)
    (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl ρ) f) (Equiv.refl γ))

def targetPerm (e : Equiv.Perm α) (f : Equiv.Perm β) : Equiv.Perm (Target ρ α β γ) :=
  Equiv.sumCongr (Equiv.refl ρ)
    (Equiv.sumCongr e (Equiv.sumCongr f (Equiv.refl γ)))

theorem pairIndex_sourcePerm (e : Equiv.Perm α) (f : Equiv.Perm β)
    (i : Source ρ α β γ) :
    pairIndex (sourcePerm e f i) = targetPerm e f (pairIndex i) := by
  rcases i with (t | x) | ((t | y) | z) <;> rfl

theorem pairEval_rename (e : Equiv.Perm α) (f : Equiv.Perm β)
    (F : MvPolynomial (Source ρ α β γ) K) :
    pairEval (rename (sourcePerm e f) F) = rename (targetPerm e f) (pairEval F) := by
  simp only [pairEval, rename_rename]
  have hi : pairIndex ∘ sourcePerm (ρ := ρ) (γ := γ) e f =
      targetPerm e f ∘ pairIndex := funext (pairIndex_sourcePerm e f)
  rw [hi]

variable [DecidableEq ρ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The next paired evaluation, literally identifying a residual e/f pair. -/
def nextPairEval (x : α) (y : β) :
    MvPolynomial (Source ρ α β γ) K →ₐ[K]
      MvPolynomial {i : Target ρ α β γ // i ≠ eLabel x} K :=
  (collisionMap (eLabel x) (fLabel y) (by simp [eLabel, fLabel])).comp pairEval

/-- Restrict the next evaluation kernel to the given particle subspace. -/
def nextKernel (U : Submodule K (MvPolynomial (Source ρ α β γ) K)) (x : α) (y : β) :=
  U ⊓ (nextPairEval (K := K) (ρ := ρ) (γ := γ) x y).toLinearMap.ker

/-- One genuine next-pair kernel forces every residual e-f linear factor,
by separately permuting the remaining e and f particles. -/
theorem residual_factor_dvd (x₀ x : α) (y₀ y : β)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hsym : ∀ e f, rename (sourcePerm e f) F = F)
    (hnext : nextPairEval x₀ y₀ F = 0) :
    (X (eLabel x) - X (fLabel y) : MvPolynomial (Target ρ α β γ) K) ∣ pairEval F := by
  have hbase : collisionFactor (K := K) (eLabel x₀) (fLabel y₀) ∣ pairEval F := by
    apply (collisionFactor_dvd_iff _ _ (by simp [eLabel, fLabel]) _).mpr
    exact hnext
  let e := Equiv.swap x₀ x
  let f := Equiv.swap y₀ y
  have h := map_dvd (rename (targetPerm (ρ := ρ) (γ := γ) e f)).toRingHom hbase
  have hinv : rename (targetPerm e f) (pairEval F) = pairEval F := by
    rw [← pairEval_rename, hsym]
  change rename (targetPerm e f) (collisionFactor (K := K) (eLabel x₀) (fLabel y₀)) ∣
    rename (targetPerm e f) (pairEval F) at h
  rw [hinv] at h
  simpa [collisionFactor, eLabel, fLabel, targetPerm, e, f] using h

variable [Fintype α] [Fintype β]

/-- Product of all residual cross-species collision factors. -/
def residualDivisor : MvPolynomial (Target ρ α β γ) K :=
  ∏ xy : α × β, (X (eLabel xy.1) - X (fLabel xy.2))

/-- The whole residual divisor follows from one actual next-pair kernel and
separate symmetry; distinct factors are prime and nonassociated. -/
theorem residualDivisor_dvd (x₀ : α) (y₀ : β)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hsym : ∀ e f, rename (sourcePerm e f) F = F)
    (hnext : nextPairEval x₀ y₀ F = 0) :
    residualDivisor (K := K) (ρ := ρ) (γ := γ) ∣ pairEval F := by
  have h := prod_pow_dvd_of_pairwise_prime_varying (Finset.univ : Finset (α × β))
    (fun xy ↦ collisionFactor (K := K) (eLabel (ρ := ρ) (γ := γ) xy.1) (fLabel xy.2))
    (fun _ ↦ 1) (pairEval F) ?_ ?_ ?_
  · simpa [residualDivisor, collisionFactor] using h
  · intro xy _
    exact collisionFactor_prime _ _ (by simp [eLabel, fLabel])
  · intro xy _ zw _ hne
    apply collisionFactor_not_dvd_of_unordered_pairs_ne
    · simp [eLabel, fLabel]
    · simp [eLabel, fLabel]
    · intro h
      apply hne
      apply Prod.ext
      · simpa [eLabel, fLabel] using h.1.symm
      · simpa [eLabel, fLabel] using h.2.symm
    · simp [eLabel, fLabel]
  · intro xy _
    simpa [collisionFactor] using residual_factor_dvd x₀ xy.1 y₀ xy.2 F hsym hnext

end
end VOA.GordonPairedEvaluation
