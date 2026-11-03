import Mathlib

/-! Ordered positional subsets for noncommutative Wick products. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {R : Type*} [Ring R]

/-- The two choices for every letter, retaining multiplicities of repeated letters. -/
def choices {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | x :: xs =>
      ((choices xs).map fun p => (x :: p.1, p.2)) ++
        ((choices xs).map fun p => (p.1, x :: p.2))

/-- A summand with the uncontracted letters before the contracted letters. -/
def wickTerm {ι : Type*} (F : R) (a b : ι → R) (k : ℕ)
    (p : List ι × List ι) : R :=
  (-1 : R) ^ p.2.length * (k.descFactorial p.2.length : R) *
    (F ^ (k - p.2.length) * (p.1.map a).prod * (p.2.map b).prod)

/-- The finite Wick expansion, with one summand per positional subset. -/
def wickSum {ι : Type*} (F : R) (a b : ι → R) (k : ℕ) (xs : List ι) : R :=
  ((choices xs).map (wickTerm F a b k)).sum

end
end VOA.DeligneAudit.LeviConversion
