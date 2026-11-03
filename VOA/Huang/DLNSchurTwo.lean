import VOA.Huang.DLNSchurSix

/-! # Schur triviality at level two and the first two-power inflation case -/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

private abbrev SLTwo := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

private def s : SLTwo := ⟨!![0, 1; 1, 0], by decide⟩
private def t : SLTwo := ⟨!![0, 1; 1, 1], by decide⟩

/-- `SL₂(ℤ/2)` satisfies the homology-free Schur condition, unconditionally. -/
theorem schurTrivial_SL_two :
    SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  apply schurTrivial_of_six_normal_forms s t
  · decide
  · exact orderOf_eq_prime (by decide : t ^ 3 = 1) (by decide : t ≠ 1)
  · decide
  · decide
  · have h : ∀ q : SLTwo, ∃ i : Fin 2, ∃ j : Fin 3, q = t ^ j.val * s ^ i.val := by
      decide +kernel
    intro q
    obtain ⟨i, j, hij⟩ := h q
    exact ⟨i.val, j.val, hij⟩

/-- Every reduction to level two has trivial inflation. -/
theorem inflationTrivial_reduction_to_two (L : ℕ) (h : 2 ∣ L) :
    InflationTrivial (reductionMod L 2 h) :=
  inflationTrivial_of_schurTrivial_target _ schurTrivial_SL_two

/-- The `a = 1` case of `TwoPowerInflation`. -/
theorem twoPowerInflation_one : InflationTrivial
    (reductionMod (2 ^ (1 + 1)) (2 ^ 1) (pow_dvd_pow 2 (Nat.le_succ 1))) := by
  exact inflationTrivial_reduction_to_two _ _

/-- The remaining two-primary statement, with the base case removed.
This is the `a ≥ 2` range of the original Beyl residual. -/
def TwoPowerInflationFromTwo : Prop :=
  ∀ a : ℕ, 2 ≤ a → InflationTrivial
    (reductionMod (2 ^ (a + 1)) (2 ^ a) (pow_dvd_pow 2 (Nat.le_succ a)))

/-- The original two-primary residual is equivalent to its range `a ≥ 2`. -/
theorem twoPowerInflation_iff_fromTwo : TwoPowerInflation ↔ TwoPowerInflationFromTwo := by
  constructor
  · intro h a ha
    exact h a (by omega)
  · intro h a ha
    by_cases h1 : a = 1
    · subst a
      exact twoPowerInflation_one
    · exact h a (by omega)

/-- Assembly with the verified level-two case discharged. -/
theorem matrixDLNLifting_of_remaining (hodd : OddPrimePowerSchur)
    (htwo : TwoPowerInflationFromTwo) : VOA.Huang.DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_local hodd (twoPowerInflation_iff_fromTwo.mpr htwo)

end VOA.Huang.DLNSchur
