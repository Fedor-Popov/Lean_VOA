import VOA.Classification.COne.Statement
import VOA.Modularity.LowestWeightExistence

/-!
# Lowest-weight and arithmetic endpoints for exceptional positivity

This extracts the first step of `PlusUnitary.pseudoUnitary_of_tops`.
No rationality, modular data, or quantum dimension is needed at this endpoint.
-/

namespace VOA.Classification.COne.OrbPos
open VOA

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  (W : VertexOperatorAlgebra V)

/-- Only realized lowest weights are tested. `IsLowestWeight` alone does not
assert that its proposed bottom weight occurs. -/
def PositiveLowestWeights : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M),
    N.IsIrreducible → IsEmpty (ModuleEquiv W N (adjointModule W)) →
    ∀ h : ℂ, IsLowestWeight N h → N.weight h ≠ ⊥ → 0 < h.re

theorem pseudoUnitary_iff_positiveLowestWeights :
    PseudoUnitary W ↔ PositiveLowestWeights W := by
  constructor
  · intro hp M _ _ N hi hn h _ hh
    exact hp M N hi hn h hh
  · intro hp M _ _ N hi hn α hα
    obtain ⟨h, hl, hh⟩ := N.exists_isLowestWeight_of_irreducible hi
    have hpos := hp M N hi hn h hl hh
    obtain ⟨n, rfl⟩ := hl α hα
    simp only [Complex.add_re, Complex.natCast_re]
    exact add_pos_of_pos_of_nonneg hpos n.cast_nonneg

/-- The numerical shape of a weight in a rank-one cyclic fixed-point lattice
module. This definition makes no assertion of orbifold-sector completeness. -/
noncomputable def CyclicWeight (n : ℕ) (j : ℤ) (r : ℕ) : ℂ :=
  (((j : ℝ) / (2 * n)) ^ 2 + r : ℝ)

@[simp] theorem cyclicWeight_re (n : ℕ) (j : ℤ) (r : ℕ) :
    (CyclicWeight n j r).re = ((j : ℝ) / (2 * n)) ^ 2 + r := rfl

theorem cyclicWeight_nonneg (n : ℕ) (j : ℤ) (r : ℕ) :
    0 ≤ (CyclicWeight n j r).re := by
  simp only [cyclicWeight_re]
  positivity

theorem cyclicWeight_eq_zero_iff {n : ℕ} (hn : 0 < n) (j : ℤ) (r : ℕ) :
    CyclicWeight n j r = 0 ↔ j = 0 ∧ r = 0 := by
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by positivity
  constructor
  · intro h
    have he := congrArg Complex.re h
    simp only [cyclicWeight_re, Complex.zero_re] at he
    have hs : 0 ≤ ((j : ℝ) / (2 * n)) ^ 2 := sq_nonneg _
    have hr : (0 : ℝ) ≤ r := r.cast_nonneg
    have hz : ((j : ℝ) / (2 * n)) ^ 2 = 0 := by linarith
    have hj : (j : ℝ) = 0 := (div_eq_zero_iff).mp (sq_eq_zero_iff.mp hz) |>.resolve_right hn0
    have hr0 : (r : ℝ) = 0 := by linarith
    exact ⟨by exact_mod_cast hj, by exact_mod_cast hr0⟩
  · rintro ⟨rfl, rfl⟩
    simp [CyclicWeight]

/-- A quantitative gap; in particular `b = 5` gives the exceptional bound `1/100`.
This is arithmetic, conditional on the stated cyclic weight formula. -/
theorem cyclicWeight_gap {n b : ℕ} (hn : 0 < n) (hnb : n ≤ b)
    (j : ℤ) (r : ℕ) (hne : CyclicWeight n j r ≠ 0) :
    1 / (4 * (b : ℝ) ^ 2) ≤ (CyclicWeight n j r).re := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le hn hnb)
  have hnbR : (n : ℝ) ≤ b := by exact_mod_cast hnb
  have hden : 0 < 4 * (n : ℝ) ^ 2 := by positivity
  have hdenb : 0 < 4 * (b : ℝ) ^ 2 := by positivity
  have hle : 4 * (n : ℝ) ^ 2 ≤ 4 * (b : ℝ) ^ 2 := by nlinarith
  have hrec : 1 / (4 * (b : ℝ) ^ 2) ≤ 1 / (4 * (n : ℝ) ^ 2) :=
    one_div_le_one_div_of_le hden hle
  rw [cyclicWeight_re]
  by_cases hj : j = 0
  · have hr : r ≠ 0 := fun hr => hne ((cyclicWeight_eq_zero_iff hn j r).2 ⟨hj, hr⟩)
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hrec1 : 1 / (4 * (n : ℝ) ^ 2) ≤ 1 := (div_le_one hden).2 (by nlinarith)
    exact hrec.trans (by nlinarith [sq_nonneg ((j : ℝ) / (2 * n))])
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
      have hi : 1 ≤ j ^ 2 := by have := sq_pos_of_ne_zero hj; omega
      exact_mod_cast hi
    have hform : ((j : ℝ) / (2 * n)) ^ 2 = (j : ℝ) ^ 2 / (4 * (n : ℝ) ^ 2) := by ring
    rw [hform]
    exact hrec.trans ((div_le_div_of_nonneg_right hj1 hden.le).trans
      (le_add_of_nonneg_right r.cast_nonneg))

end VOA.Classification.COne.OrbPos
