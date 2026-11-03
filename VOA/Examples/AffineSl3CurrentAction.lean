/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3NegativeSerre
import VOA.Examples.AffineSl3BracketTable

/-!
# Current action for arbitrary trace-zero matrices

The eight actual currents are assembled using the proved matrix
coordinates. Their bracket is the actual matrix commutator plus the
trace cocycle, with no Lie-representation hypothesis.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- The actual current operators in the fixed Chevalley-basis order. -/
def currentBasis (k : ℂ) (i : Fin 8) (n : ℤ) : Module.End ℂ Fock :=
  ![E1 n,E2 n,E12 n,F1 k n,F2 k n,F12 k n,H1 k n,H2 k n] i

/-- The full current bracket on the eight basis elements, using the
structure constants and trace form of the actual matrix Lie algebra. -/
theorem currentBasis_bracket (k : ℂ) (a b : Fin 8) (m n : ℤ) :
    ⁅currentBasis k a m,currentBasis k b n⁆ =
      (∑ c, structureConstant a b c • currentBasis k c (m+n))+
      (if m+n=0 then ((m : ℂ)*k*form (generator a) (generator b)) •
        (1 : Module.End ℂ Fock) else 0) := by
  simp only [structureConstant_eq_table,form_generator_eq_table]
  fin_cases a <;> fin_cases b
  all_goals
    simp only [bracketTable,formTable,currentBasis,Fin.sum_univ_succ]
    norm_num only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Matrix.head_cons,
      Matrix.tail_cons,Fin.reduceFinMk,zero_smul,one_smul,neg_smul,zero_add,add_zero,
      mul_zero,mul_one,Fin.sum_univ_zero]
  all_goals
    first
    | rw [E1_E1]
    | rw [E2_E2]
    | rw [E12_E12]
    | rw [E1_E2]
    | rw [E1_E12]
    | rw [E2_E12]
    | rw [H1_H1]
    | rw [H2_H2]
    | rw [H1_H2]
    | rw [H1_E1]
    | rw [H1_E2]
    | rw [H1_E12]
    | rw [H1_F1]
    | rw [H1_F2]
    | rw [H1_F12]
    | rw [H2_E1]
    | rw [H2_E2]
    | rw [H2_E12]
    | rw [H2_F1]
    | rw [H2_F2]
    | rw [H2_F12]
    | rw [E1_F1]
    | rw [E1_F2]
    | rw [E1_F12]
    | rw [E2_F1]
    | rw [E2_F2]
    | rw [E2_F12]
    | rw [E12_F1]
    | rw [E12_F2]
    | rw [E12_F12]
    | rw [F1_self]
    | rw [F2_self]
    | rw [F12_self]
    | rw [F2_F1]
    | rw [F1_F12]
    | rw [F2_F12]
    | (rw [← lie_skew]; first
        | rw [E1_E1]
        | rw [E2_E2]
        | rw [E12_E12]
        | rw [E1_E2]
        | rw [E1_E12]
        | rw [E2_E12]
        | rw [H1_H1]
        | rw [H2_H2]
        | rw [H1_H2]
        | rw [H1_E1]
        | rw [H1_E2]
        | rw [H1_E12]
        | rw [H1_F1]
        | rw [H1_F2]
        | rw [H1_F12]
        | rw [H2_E1]
        | rw [H2_E2]
        | rw [H2_E12]
        | rw [H2_F1]
        | rw [H2_F2]
        | rw [H2_F12]
        | rw [E1_F1]
        | rw [E1_F2]
        | rw [E1_F12]
        | rw [E2_F1]
        | rw [E2_F2]
        | rw [E2_F12]
        | rw [E12_F1]
        | rw [E12_F2]
        | rw [E12_F12]
        | rw [F1_self]
        | rw [F2_self]
        | rw [F12_self]
        | rw [F2_F1]
        | rw [F1_F12]
        | rw [F2_F12]
)
  all_goals
    by_cases hz : m+n=0
    · have hc : (n : ℂ)= -(m : ℂ) := by exact_mod_cast (show n= -m by omega)
      simp only [add_comm n m,hz,ite_true,hc] <;> module
    · simp only [add_comm n m,hz,ite_false] <;> module

/-- Linear current operator for an arbitrary actual trace-zero matrix. -/
def currentAction (k : ℂ) (n : ℤ) : Sl3 →ₗ[ℂ] Module.End ℂ Fock where
  toFun x := ∑ i, coordinatesLinear x i • currentBasis k i n
  map_add' x y := by simp [map_add,add_smul,Finset.sum_add_distrib]
  map_smul' z x := by simp [map_smul,smul_smul,Finset.smul_sum]

/-- The linear assembly recovers each of the eight proved current operators. -/
theorem currentAction_generator (k : ℂ) (n : ℤ) (i : Fin 8) :
    currentAction k n (generator i)=currentBasis k i n := by
  change (∑ j, coordinates (generator i) j • currentBasis k j n)=_
  rw [coordinates_generator]
  simp [Pi.single_apply]

/-- Every basis current annihilates the vacuum at nonnegative indices. -/
theorem currentBasis_vacuum (k : ℂ) (i : Fin 8) {n : ℤ} (hn : 0 ≤ n) :
    currentBasis k i n 1=0 := by
  fin_cases i <;> simp [currentBasis,E1_vacuum hn,E2_vacuum hn,E12_vacuum hn,
    F1_vacuum k hn,F2_vacuum k hn,F12_vacuum k hn,H1_vacuum k hn,H2_vacuum k hn]

/-- Vacuum annihilation extends linearly to every trace-zero matrix. -/
theorem currentAction_vacuum (k : ℂ) (x : Sl3) {n : ℤ} (hn : 0 ≤ n) :
    currentAction k n x 1=0 := by
  simp [currentAction,LinearMap.sum_apply,currentBasis_vacuum k _ hn]

end
end VOA.AffineSl3.FreeField
