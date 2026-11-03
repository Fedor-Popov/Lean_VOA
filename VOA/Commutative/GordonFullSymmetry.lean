/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonFullDivisor
import VOA.Commutative.GordonSymmetry

/-! # Separate symmetry of the full Gordon divisor -/

namespace VOA.GordonFullSymmetry

open scoped BigOperators
open MvPolynomial VOA.GordonFiltration VOA.GordonCommonFactors VOA.GordonDivisor
open VOA.GordonPairedEvaluation VOA.GordonPairedRelations VOA.GordonFullDivisor
open VOA.GordonSymmetry VOA.GordonRestrictedDual VOA.GordonResidualFiltration
open VOA.GordonBlockEquiv

noncomputable section

variable {K ρ τ α β γ : Type*} [Field K]
variable [Fintype ρ] [Fintype τ] [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq ρ] [LinearOrder τ] [LinearOrder α] [LinearOrder β] [LinearOrder γ]

def residualPerm (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    Equiv.Perm (Residual α β γ) := Equiv.sumCongr a (Equiv.sumCongr b c)

def fullPerm (e : Equiv.Perm τ) (a : Equiv.Perm α) (b : Equiv.Perm β)
    (c : Equiv.Perm γ) : Equiv.Perm (Target τ α β γ) :=
  Equiv.sumCongr e (residualPerm a b c)

def maximalEquiv (m : ℕ) (f : ρ → τ) (e : Equiv.Perm τ)
    (he : ∀ j, blockSize f (e j) = blockSize f j) :
    Equiv.Perm {j : τ // blockSize f j = m} :=
  Equiv.subtypeEquiv e (fun j ↦ by rw [he])

def maximalResidualDivisor (m : ℕ) (f : ρ → τ) : MvPolynomial (Target τ α β γ) K :=
  ∏ ud : {u : τ // blockSize f u = m} × Residual α β γ,
    (X (Sum.inl ud.1.val) - X (Sum.inr ud.2))

theorem fullDivisor_expansion (m : ℕ) (f : ρ → τ) :
    fullDivisor (K := K) (α := α) (β := β) (γ := γ) m f =
      rename Sum.inl (clusterDivisor f) *
        (maximalResidualDivisor m f * residualDivisor (K := K) (ρ := τ) (γ := γ)) := by
  simp [fullDivisor, Fintype.prod_sum_type, edgePair, edgeExponent,
    clusterDivisor, maximalResidualDivisor, residualDivisor, collisionFactor,
    eLabel, fLabel, map_prod]

theorem rename_maximalResidualDivisor (m : ℕ) (f : ρ → τ) (e : Equiv.Perm τ)
    (he : ∀ j, blockSize f (e j) = blockSize f j)
    (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    rename (fullPerm e a b c) (maximalResidualDivisor (K := K) m f) =
      maximalResidualDivisor m f := by
  rw [maximalResidualDivisor, map_prod]
  apply Fintype.prod_equiv (Equiv.prodCongr (maximalEquiv m f e he) (residualPerm a b c))
  intro ud
  simp [fullPerm, maximalEquiv]

theorem rename_residualDivisor (e : Equiv.Perm τ)
    (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    rename (fullPerm e a b c) (residualDivisor (K := K) (ρ := τ) (γ := γ)) =
      residualDivisor := by
  rw [residualDivisor, map_prod]
  apply Fintype.prod_equiv (Equiv.prodCongr a b)
  intro xy
  simp [fullPerm, residualPerm, eLabel, fLabel]

/-- Every equal-size cluster permutation and independent residual-species permutation
fixes the full Gordon divisor exactly, including its orientation signs. -/
theorem rename_fullDivisor (m : ℕ) (f : ρ → τ) (e : Equiv.Perm τ)
    (he : ∀ j, blockSize f (e j) = blockSize f j)
    (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    rename (fullPerm e a b c) (fullDivisor (K := K) m f) = fullDivisor m f := by
  rw [fullDivisor_expansion, map_mul, map_mul, rename_maximalResidualDivisor m f e he,
    rename_residualDivisor]
  congr 1
  have hcomp : fullPerm e a b c ∘ Sum.inl = Sum.inl ∘ e := rfl
  rw [rename_rename, hcomp, ← rename_rename, rename_clusterDivisor f e he]

def residualSourcePerm (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    Equiv.Perm (Source ρ α β γ) :=
  Equiv.sumCongr (Equiv.sumCongr (Equiv.refl ρ) a)
    (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl ρ) b) c)

/-- Residual species symmetry is inherited by the actual evaluated functional model. -/
theorem rename_residual_clusterEval (m D : ℕ) (f : ρ → τ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    rename (fullPerm (Equiv.refl τ) a b c) (clusterEval f F) = clusterEval f F := by
  have hinv : rename (residualSourcePerm (ρ := ρ) a b c) F = F := by
    obtain ⟨L, rfl⟩ := hF
    apply particleMap_rename
    rintro ((j | j) | ((j | j) | j)) <;> rfl
  have hi : fullPerm (Equiv.refl τ) a b c ∘ clusterIndex f =
      clusterIndex f ∘ residualSourcePerm (ρ := ρ) a b c := by
    funext j
    rcases j with (j | j) | ((j | j) | j) <;> rfl
  simp only [clusterEval, rename_rename]
  rw [hi, ← rename_rename, hinv]

/-- Equal-size cluster symmetry survives while residuals remain independent. -/
theorem rename_cluster_clusterEval (m D : ℕ) (f : ρ → τ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (e : Equiv.Perm τ) (he : ∀ j, blockSize f (e j) = blockSize f j) :
    rename (fullPerm e (Equiv.refl α) (Equiv.refl β) (Equiv.refl γ)) (clusterEval f F) =
      clusterEval f F := by
  rw [clusterEval_eq]
  have hp : (fullPerm e (Equiv.refl α) (Equiv.refl β) (Equiv.refl γ) :
      Target τ α β γ → Target τ α β γ) = Sum.map e id := by
    funext j
    rcases j with j | (j | (j | j)) <;> rfl
  rw [hp]
  change residualEval e (residualEval f (pairEval F)) = residualEval f (pairEval F)
  apply (sumRingEquiv K τ (Residual α β γ)).injective
  change sumToIter K τ (Residual α β γ) _ = sumToIter K τ (Residual α β γ) _
  simp only [sumToIter_residualEval]
  change rename e (rename f (sumToIter K ρ (Residual α β γ) (pairEval F))) = _
  rw [rename_rename]
  apply blockEval_eq_of_blockSize_eq _ _ _
    (sumToIter_isSymmetric _ (functionalModel_pair_symmetry m D F hF))
  intro j
  have hh := blockSize_equiv_comp f e (e.symm j)
  simp only [Equiv.apply_symm_apply] at hh
  exact hh.trans (by simpa using (he (e.symm j)).symm)

/-- All separate symmetries of the actual evaluated model. -/
theorem rename_full_clusterEval (m D : ℕ) (f : ρ → τ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (e : Equiv.Perm τ) (he : ∀ j, blockSize f (e j) = blockSize f j)
    (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    rename (fullPerm e a b c) (clusterEval f F) = clusterEval f F := by
  have hp : (fullPerm e a b c : Target τ α β γ → Target τ α β γ) =
      fullPerm e (Equiv.refl α) (Equiv.refl β) (Equiv.refl γ) ∘
        fullPerm (Equiv.refl τ) a b c := by
    funext j
    rcases j with j | (j | (j | j)) <;> rfl
  rw [hp, ← rename_rename, rename_residual_clusterEval m D f F hF,
    rename_cluster_clusterEval m D f F hF e he]

/-- Dividing the actual evaluation by the full nonzero divisor preserves all separate symmetries. -/
theorem quotient_separate_symmetry (m D : ℕ) (f : ρ → τ)
    (F : MvPolynomial (Source ρ α β γ) K)
    (hF : F ∈ functionalModel m D (sourceColor (ρ := ρ) (α := α) (β := β) (γ := γ)))
    (q : MvPolynomial (Target τ α β γ) K) (hq : clusterEval f F = fullDivisor m f * q)
    (e : Equiv.Perm τ) (he : ∀ j, blockSize f (e j) = blockSize f j)
    (a : Equiv.Perm α) (b : Equiv.Perm β) (c : Equiv.Perm γ) :
    rename (fullPerm e a b c) q = q := by
  apply mul_left_cancel₀ (fullDivisor_ne_zero (K := K) (α := α) (β := β) (γ := γ) m f)
  calc
    fullDivisor m f * rename (fullPerm e a b c) q =
        rename (fullPerm e a b c) (fullDivisor m f * q) := by
          rw [map_mul, rename_fullDivisor m f e he]
    _ = clusterEval f F := by rw [← hq, rename_full_clusterEval m D f F hF e he]
    _ = fullDivisor m f * q := hq

end
end VOA.GordonFullSymmetry
