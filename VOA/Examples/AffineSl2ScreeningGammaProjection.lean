/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningCartan

/-!
# Removing gamma variables from the actual lowering result

The positive Cartan equations and the actual raising/lowering commutator
show that F_1 of the screening state is gamma-independent. Evaluation at
zero gamma variables therefore preserves it. This removes gamma tails
without presupposing their finite reindexing or lowering annihilation.
-/
namespace VOA.Wak.Screening
open MvPolynomial
open scoped BigOperators
noncomputable section

/-- Set every gamma oscillator to zero, preserving beta and boson variables. -/
def gammaErase : WakFock →ₐ[ℂ] WakFock :=
  aeval (fun v : Fin 3 × ℕ => if v.1=1 then 0 else X v)

/-- The projection on an oscillator generator. -/
theorem gammaErase_X (v : Fin 3 × ℕ) :
    gammaErase (X v)=if v.1=1 then 0 else X v := by simp [gammaErase]

/-- A nonzero coefficient of a gamma-independent polynomial has zero
occupation at every gamma variable. Characteristic zero is used here. -/
theorem gammaFree_occupation (P : WakFock) (hP : P∈gammaFree)
    (d : Fin 3 × ℕ →₀ ℕ) (hd : coeff d P≠0) (j : ℕ) : d (1,j)=0 := by
  have hz : coeff d (X (1,j)*pderiv (1,j) P)=0 := by rw [hP j,mul_zero,coeff_zero]
  rw [coeff_X_mul_pderiv] at hz
  exact Nat.cast_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hd)

/-- Evaluation at zero gamma variables fixes every gamma-independent
polynomial exactly, rather than merely its constant coefficient. -/
theorem gammaErase_fixed (P : WakFock) (hP : P∈gammaFree) : gammaErase P=P := by
  change eval₂ MvPolynomial.C (fun v : Fin 3 × ℕ => if v.1=1 then 0 else X v) P=P
  apply Eq.trans (eval₂_congr MvPolynomial.C _ X ?_) (eval₂_eta P)
  intro v d hv hd
  have hne : v.1≠1 := by
    intro h
    obtain ⟨a,j⟩ := v
    dsimp only at h
    subst a
    exact (Finsupp.mem_support_iff.mp hv) (gammaFree_occupation P hP d hd j)
  rw [if_neg hne]

/-- Actual oscillator partials preserve gamma independence. -/
theorem gammaFree_partial (P : WakFock) (hP : P∈gammaFree) (v : Fin 3 × ℕ) :
    pderiv v P∈gammaFree := by
  intro j
  rw [pderiv_comm',hP j,map_zero]

/-- Every indexed beta partial, including the zero extension, preserves
gamma independence. -/
theorem gammaFree_bD (P : WakFock) (hP : P∈gammaFree) (i : ℤ) : bD i P∈gammaFree := by
  by_cases hi : (1 : ℤ) ≤ i
  · rw [bD_of_pos hi,dV_apply]; exact gammaFree_partial P hP _
  · rw [bD_of_nonpos (by omega),LinearMap.zero_apply]; exact gammaFree.zero_mem

/-- The projection fixes every beta creation variable with its zero extension. -/
theorem gammaErase_bV (i : ℤ) : gammaErase (bV i)=bV i := by
  unfold bV
  split_ifs <;> simp [gammaErase_X]

/-- The projection fixes every boson creation variable with its zero extension. -/
theorem gammaErase_aV (i : ℤ) : gammaErase (aV i)=aV i := by
  unfold aV
  split_ifs <;> simp [gammaErase_X]

/-- Every gamma creation variable, including its zero extension, projects to zero. -/
theorem gammaErase_cV (i : ℤ) : gammaErase (cV i)=0 := by
  unfold cV
  split_ifs <;> simp [gammaErase_X]

/-- The actual lowering result has zero gamma partials: the commutator
reduces each to a positive Cartan mode of the screening state. This does
not assume that the lowering result itself is zero. -/
theorem state_lowering_gammaFree (r q M : ℕ) (hq : 0<q) (k lam : ℂ)
    (hMk : (M : ℂ)*(k+2)=1) : Charged.F k lam 1 (state r q M)∈gammaFree := by
  intro j
  have hc := congrArg (fun T : Module.End ℂ WakFock => T (state r q M))
    (Charged.ef k lam (j : ℤ) 1)
  dsimp only at hc
  rw [if_neg (by omega),add_zero,Ring.lie_def,
    LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
    state_raising r q M (j : ℤ) (by omega),map_zero,sub_zero] at hc
  have hh := state_positive_cartan r q M (j+1) hq (by omega) k lam hMk
  have hi : ((j+1 : ℕ) : ℤ)=(j : ℤ)+1 := by push_cast; rfl
  rw [hi] at hh
  rw [hh,Ecur,Bet_of_nonneg (by omega),cD_of_nonneg (by omega),dV_apply] at hc
  simpa using hc

/-- Gamma evaluation preserves the actual lowering result of the screening
state under the proved reciprocal-level condition. -/
theorem gammaErase_state_lowering (r q M : ℕ) (hq : 0<q) (k lam : ℂ)
    (hMk : (M : ℂ)*(k+2)=1) :
    gammaErase (Charged.F k lam 1 (state r q M))=Charged.F k lam 1 (state r q M) :=
  gammaErase_fixed _ (state_lowering_gammaFree r q M hq k lam hMk)

end
end VOA.Wak.Screening
