/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningLowering

/-!
# Genuine nonzero affine screening singular states

The finite screening polynomial is killed by every positive affine current
and by the horizontal raising operator. Its energy, Cartan weight and
nonvanishing are actual statements in the charged Wakimoto representation.
These results do not yet identify a universal Verma Gram determinant root.
-/
namespace VOA.Wak.Screening
open Module (End)
noncomputable section

/-- Every positive lowering mode kills the screening vector. The first
mode is the finite IBP theorem; higher modes follow from actual Cartan
commutators and already proved positive Cartan annihilation. -/
theorem state_positive_lowering (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) (n : ℤ) (hn : 0<n) :
    Charged.F k ((q : ℂ)*(k+2)-(r : ℂ)-1) n (state r q M)=0 := by
  by_cases h : n=1
  · subst n
    exact state_lowering r q M hr hq k hMk
  have hk : k+2≠0 := by intro hz; simp [hz] at hMk
  have hH : Charged.H k ((q : ℂ)*(k+2)-(r : ℂ)-1) (n-1) (state r q M)=0 := by
    have hh := state_positive_cartan r q M (n-1).toNat hq (by omega)
      k ((q : ℂ)*(k+2)-(r : ℂ)-1) hMk
    simpa only [Int.toNat_of_nonneg (by omega : 0≤n-1)] using hh
  have hc := congrArg (fun T : End ℂ WakFock => T (state r q M))
    (Charged.hf k ((q : ℂ)*(k+2)-(r : ℂ)-1) hk (n-1) 1)
  dsimp only at hc
  rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
    state_lowering r q M hr hq k hMk,hH,map_zero,map_zero,sub_self,
    LinearMap.smul_apply,sub_add_cancel] at hc
  exact (smul_eq_zero.mp hc.symm).resolve_left (by norm_num)

/-- Every positive actual affine current annihilates the nonzero screening
polynomial; all three colours use the same charged representation. -/
theorem state_positive_current (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) (a : Fin 3) (n : ℤ) (hn : 0<n) :
    Charged.J k ((q : ℂ)*(k+2)-(r : ℂ)-1) a n (state r q M)=0 := by
  fin_cases a <;> dsimp only
  · change Ecur n (state r q M)=0
    exact state_raising r q M n (by omega)
  · change Charged.F k ((q : ℂ)*(k+2)-(r : ℂ)-1) n (state r q M)=0
    exact state_positive_lowering r q M hr hq k hMk n hn
  · change Charged.H k ((q : ℂ)*(k+2)-(r : ℂ)-1) n (state r q M)=0
    have h := state_positive_cartan r q M n.toNat hq (by omega)
      k ((q : ℂ)*(k+2)-(r : ℂ)-1) hMk
    simpa only [Int.toNat_of_nonneg (by omega : 0≤n)] using h

/-- The integer-screening construction supplies an ACTUAL nonzero joint
weight vector satisfying all affine highest-weight equations. This is an
unconditional construction at reciprocal-positive-integer shifted level. -/
theorem exists_nonzero_screening_highest (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) :
    ∃ v : WakFock, v≠0 ∧ Dwt v=(r*q : ℂ) • v ∧
      Charged.H k ((q : ℂ)*(k+2)-(r : ℂ)-1) 0 v=
        ((q : ℂ)*(k+2)+(r : ℂ)-1) • v ∧
      Ecur 0 v=0 ∧
      ∀ (a : Fin 3) (n : ℤ),0<n →
        Charged.J k ((q : ℂ)*(k+2)-(r : ℂ)-1) a n v=0 := by
  refine ⟨state r q M,state_ne_zero r q M hr hq,state_energy r q M hq,?_,
    state_raising r q M 0 (by omega),state_positive_current r q M hr hq k hMk⟩
  rw [state_cartan]
  congr 1
  ring

end
end VOA.Wak.Screening
