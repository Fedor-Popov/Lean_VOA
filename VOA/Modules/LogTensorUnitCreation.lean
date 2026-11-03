/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorUnit
import VOA.Modules.LogTensorSkewEquiv

/-! # Actual logarithmic vacuum creation coefficients

The genuine module operator has only its constant vacuum coefficient. Applying
actual logarithmic skew symmetry gives the full right-vacuum creation series,
with no positive logarithmic coefficients, for every branch of the skew map.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor
open scoped BigOperators
open VOA.LogSkew
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The actual module logarithmic operator at the vacuum, at every complex mode
and every logarithmic degree. -/
theorem logModuleIntertwiner_vacuum_modes (A : WeakModule W M)
    (n : ℂ) (k : ℕ) (x : M) :
    (logModuleIntertwiner A).1 n k W.vacuum x =
      if n = -1 ∧ k = 0 then x else 0 := by
  classical
  by_cases hn : n = -1
  · subst n
    cases k with
    | zero => simp only [and_self, if_true, logModuleIntertwiner_vacuum,
        LinearMap.id_apply]
    | succ k =>
      rw [vacuum_positive_log_zero (logModuleIntertwiner A).2 k,
        LinearMap.zero_apply]
      simp
  · rw [vacuum_mode_zero_of_ne (logModuleIntertwiner A).2 hn k,
      LinearMap.zero_apply]
    simp [hn]

private theorem module_vacuum_positive_log (A : WeakModule W M)
    (n : ℂ) (k : ℕ) (hk : 0 < k) (x : M) :
    (logModuleIntertwiner A).1 n k W.vacuum x = 0 := by
  rw [logModuleIntertwiner_vacuum_modes]
  simp [Nat.ne_of_gt hk]

private theorem skew_module_vacuum_positive_log (A : WeakModule W M)
    (r : ℤ) (n : ℂ) (k : ℕ) (hk : 0 < k) (x : M) :
    skewK A (omegaPhase r) (logModuleIntertwiner A).1 n k x W.vacuum = 0 := by
  rw [(logModuleIntertwiner A).2.skewK_apply, sSum,
    finsum_eq_zero_of_forall_eq_zero, smul_zero]
  intro j
  simp only [sTerm, comp_apply, module_vacuum_positive_log A _ k hk x,
    map_zero, smul_zero]

/-- No positive logarithmic degree appears in the genuine skewed module vacuum
insertion, including the branch-dependent logarithmic shift. -/
theorem omega_module_vacuum_positive_log_zero (A : WeakModule W M)
    (r : ℤ) (n : ℂ) (k : ℕ) (hk : 0 < k) (x : M) :
    omega A r (logModuleIntertwiner A).1 n k x W.vacuum = 0 := by
  rw [omega, logShift_eq_sum
    ((logModuleIntertwiner A).2.isLogIntertwining_skewK
      (omegaPhase_succ r) (omegaPhase_ne_zero r)).logFin 1
    (fun j hj => skew_module_vacuum_positive_log A r n j (by omega) x)]
  simp only [Finset.sum_range_one]
  rw [shc_eq_zero hk, zero_smul]

private theorem omega_module_vacuum_log_zero (A : WeakModule W M)
    (r : ℤ) (n : ℂ) (x : M) :
    omega A r (logModuleIntertwiner A).1 n 0 x W.vacuum =
      skewK A (omegaPhase r) (logModuleIntertwiner A).1 n 0 x W.vacuum := by
  rw [omega, logShift_eq_sum
    ((logModuleIntertwiner A).2.isLogIntertwining_skewK
      (omegaPhase_succ r) (omegaPhase_ne_zero r)).logFin 1
    (fun j hj => skew_module_vacuum_positive_log A r n j (by omega) x)]
  simp [shc]

/-- The actual skewed module vacuum mode vanishes off the creation indices. -/
theorem omega_module_vacuum_zero_of_no_index (A : WeakModule W M)
    (r : ℤ) (n : ℂ) (hn : ∀ j : ℕ, n ≠ -1 - (j : ℂ)) (x : M) :
    omega A r (logModuleIntertwiner A).1 n 0 x W.vacuum = 0 := by
  rw [omega_module_vacuum_log_zero, (logModuleIntertwiner A).2.skewK_apply,
    sSum, finsum_eq_zero_of_forall_eq_zero, smul_zero]
  intro j
  have hnj : n + (j : ℂ) ≠ -1 := by
    intro h
    exact hn j (by linear_combination h)
  simp only [sTerm, comp_apply, logModuleIntertwiner_vacuum_modes,
    hnj, false_and, if_false, map_zero, smul_zero]

private theorem omegaPhase_creation (r : ℤ) (j : ℕ) :
    omegaPhase r (-1 - (j : ℂ)) * sc j = (j.factorial : ℂ)⁻¹ := by
  have h := phase_nat (omegaPhase_succ r) (-1 - (j : ℂ)) j
  rw [show -1 - (j : ℂ) + (j : ℂ) = -1 by ring] at h
  have hm : omegaPhase r (-1) = 1 := by simp [omegaPhase]
  rw [hm] at h
  rw [sc]
  calc
    omegaPhase r (-1 - (j : ℂ)) * ((j.factorial : ℂ)⁻¹ * (-1) ^ j) =
        (j.factorial : ℂ)⁻¹ * ((-1) ^ j * omegaPhase r (-1 - (j : ℂ))) := by ring
    _ = (j.factorial : ℂ)⁻¹ := by rw [← h, mul_one]

/-- The full genuine right-vacuum creation formula, derived by logarithmic skew
symmetry rather than an ordinary intertwiner specialization. -/
theorem omega_module_vacuum_creation (A : WeakModule W M)
    (r : ℤ) (j : ℕ) (x : M) :
    omega A r (logModuleIntertwiner A).1 (-1 - (j : ℂ)) 0 x W.vacuum =
      (j.factorial : ℂ)⁻¹ • (Lm1 A ^ j) x := by
  classical
  rw [omega_module_vacuum_log_zero,
    (logModuleIntertwiner A).2.skewK_eq_sum (omegaPhase r)
      (-1 - (j : ℂ)) 0 x W.vacuum (j+1)]
  · rw [Finset.sum_eq_single j]
    · rw [show -1 - (j : ℂ) + (j : ℂ) = -1 by ring,
        logModuleIntertwiner_vacuum, LinearMap.id_apply,
        smul_smul, omegaPhase_creation]
    · intro i hi hij
      have hni : -1 - (j : ℂ) + (i : ℂ) ≠ -1 := by
        intro h
        have he : (i : ℂ) = (j : ℂ) := by linear_combination h
        exact hij (Nat.cast_injective he)
      rw [logModuleIntertwiner_vacuum_modes, if_neg (by simp [hni]),
        map_zero, smul_zero]
    · intro hj
      exact (hj (Finset.mem_range.mpr (Nat.lt_succ_self j))).elim
  · intro i hi
    have hni : -1 - (j : ℂ) + (i : ℂ) ≠ -1 := by
      intro h
      have he : (i : ℂ) = (j : ℂ) := by linear_combination h
      have hij : i = j := Nat.cast_injective he
      omega
    rw [logModuleIntertwiner_vacuum_modes, if_neg (by simp [hni])]

end VOA.LogTensor
