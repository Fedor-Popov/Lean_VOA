import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! The nested cube chain is the unique monomial of largest color weight.
The variables are indexed by bit masks0..7, and the three coordinate
marginals are ordered. This is an all-degree arithmetic statement. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube

abbrev Counts := Fin 8 → ℕ

def length (n : Counts) : ℕ :=
  n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7

def first (n : Counts) : ℕ := n 1 + n 3 + n 5 + n 7

def second (n : Counts) : ℕ := n 2 + n 3 + n 6 + n 7

def third (n : Counts) : ℕ := n 4 + n 5 + n 6 + n 7

/-- The weight of a cube variable is the square of its number of coordinates. -/
def energy (n : Counts) : ℕ :=
  n 1 + n 2 + 4 * n 3 + n 4 + 4 * n 5 + 4 * n 6 + 9 * n 7

/-- The chain empty,1,12,123, with ordered marginals a>=b>=c. -/
def chain (r a b c : ℕ) : Counts :=
  ![r - a,a - b,0,b - c,0,0,0,c]

/-- The deficit consists exactly of the four colors outside this chain. -/
theorem energy_deficit (n : Counts) :
    energy n + 2 * n 2 + 4 * n 4 + 2 * n 5 + 4 * n 6 =
      first n + 3 * second n + 5 * third n := by
  simp only [energy,first,second,third]
  omega

theorem energy_le (n : Counts) :
    energy n ≤ first n + 3 * second n + 5 * third n := by
  have h := energy_deficit n
  omega

/-- Maximal color weight forces the exact nested-chain exponent vector. -/
theorem eq_chain_of_energy_eq (n : Counts) (r a b c : ℕ)
    (hr : length n = r) (ha : first n = a) (hb : second n = b)
    (hc : third n = c) (he : energy n = a + 3 * b + 5 * c) :
    n = chain r a b c := by
  have hd := energy_deficit n
  simp only [ha,hb,hc] at hd
  have hz2 : n 2 = 0 := by omega
  have hz4 : n 4 = 0 := by omega
  have hz5 : n 5 = 0 := by omega
  have hz6 : n 6 = 0 := by omega
  simp only [length,first,second,third,hz2,hz4,hz5,hz6] at hr ha hb hc
  funext i
  fin_cases i <;> simp [chain] <;> omega

/-- Every other monomial with these marginals has strictly smaller weight. -/
theorem energy_lt_of_ne_chain (n : Counts) (r a b c : ℕ)
    (hr : length n = r) (ha : first n = a) (hb : second n = b)
    (hc : third n = c) (hne : n ≠ chain r a b c) :
    energy n < a + 3 * b + 5 * c := by
  have hl := energy_le n
  rw [ha,hb,hc] at hl
  have he : energy n ≠ a + 3 * b + 5 * c := fun h =>
    hne (eq_chain_of_energy_eq n r a b c hr ha hb hc h)
  omega

theorem chain_data (r a b c : ℕ) (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    length (chain r a b c) = r ∧ first (chain r a b c) = a ∧
      second (chain r a b c) = b ∧ third (chain r a b c) = c ∧
      energy (chain r a b c) = a + 3 * b + 5 * c := by
  simp [length,first,second,third,energy,chain]
  omega

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.eq_chain_of_energy_eq
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.energy_lt_of_ne_chain
