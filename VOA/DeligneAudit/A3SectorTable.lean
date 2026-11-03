import VOA.DeligneAudit.A2SectorWeyl

/-!
The 15-colour matrix-unit table for `sl₄`.  Colours 0--5 are the positive
roots E₀₁, E₀₂, E₀₃, E₁₂, E₁₃, E₂₃; colours 6--11 are their transposes;
colours 12--14 are E₀₀-E₁₁, E₁₁-E₂₂, E₂₂-E₃₃.
-/

namespace VOA.DeligneAudit.A3Sector

/-- Row of an off-diagonal matrix unit. -/
def row (c : Fin 15) : Fin 4 :=
  if c.val < 3 then 0 else if c.val < 5 then 1 else if c.val = 5 then 2 else
  if c.val = 6 then 1 else if c.val = 7 then 2 else if c.val = 8 then 3 else
  if c.val = 9 then 2 else if c.val = 10 then 3 else 3

/-- Column of an off-diagonal matrix unit. -/
def col (c : Fin 15) : Fin 4 :=
  if c.val = 0 then 1 else if c.val = 1 then 2 else if c.val = 2 then 3 else
  if c.val = 3 then 2 else if c.val < 6 then 3 else if c.val < 9 then 0 else
  if c.val < 11 then 1 else 2

/-- The integer matrix of a Chevalley basis element. -/
def basis (c : Fin 15) (i j : Fin 4) : ℤ :=
  if c.val < 12 then (if i = row c ∧ j = col c then 1 else 0) else
  if c.val = 12 then (if i = 0 ∧ j = 0 then 1 else
    if i = 1 ∧ j = 1 then -1 else 0) else
  if c.val = 13 then (if i = 1 ∧ j = 1 then 1 else
    if i = 2 ∧ j = 2 then -1 else 0) else
  (if i = 2 ∧ j = 2 then 1 else if i = 3 ∧ j = 3 then -1 else 0)

/-- Matrix commutator, with integral entries. -/
def commEntry (a b : Fin 15) (i j : Fin 4) : ℤ :=
  ∑ k : Fin 4, (basis a i k * basis b k j - basis b i k * basis a k j)

/-- Coordinates of the commutator in the traceless basis. -/
def bracketInt (a b c : Fin 15) : ℤ :=
  if c.val < 12 then commEntry a b (row c) (col c) else
  if c.val = 12 then commEntry a b 0 0 else
  if c.val = 13 then commEntry a b 0 0 + commEntry a b 1 1 else
  commEntry a b 0 0 + commEntry a b 1 1 + commEntry a b 2 2

/-- Structure constants over `ℂ` for the current-algebra interface. -/
def bracketTable (a b c : Fin 15) : ℂ := bracketInt a b c

/-- The node-1 radical letters E₁₀, E₂₀, E₃₀. -/
def F : Fin 3 → Fin 15
  | 0 => 6
  | 1 => 7
  | 2 => 8

/-- Simple negative root vectors at the two Levi nodes. -/
def leviF : Fin 2 → Fin 15
  | 0 => 9
  | 1 => 11

theorem radical_abelian (i j : Fin 3) (c : Fin 15) :
    bracketTable (F i) (F j) c = 0 := by
  have h : bracketInt (F i) (F j) c = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases c <;> decide
  simp [bracketTable, h]

theorem levi_step_one (c : Fin 15) :
    bracketTable (leviF 0) (F 0) c = if c = F 1 then 1 else 0 := by
  have h : bracketInt (leviF 0) (F 0) c = if c = F 1 then 1 else 0 := by
    fin_cases c <;> decide
  simp [bracketTable, h]

theorem levi_step_two (c : Fin 15) :
    bracketTable (leviF 1) (F 1) c = if c = F 2 then 1 else 0 := by
  have h : bracketInt (leviF 1) (F 1) c = if c = F 2 then 1 else 0 := by
    fin_cases c <;> decide
  simp [bracketTable, h]

theorem levi_other_zero (i : Fin 2) (j : Fin 3) (h : j.val ≠ i.val) (c : Fin 15) :
    bracketTable (leviF i) (F j) c = 0 := by
  have h' : bracketInt (leviF i) (F j) c = 0 := by
    fin_cases i <;> fin_cases j <;> simp at h <;> fin_cases c <;> decide
  simp [bracketTable, h']

#print axioms radical_abelian
#print axioms levi_step_one
#print axioms levi_step_two
#print axioms levi_other_zero

end VOA.DeligneAudit.A3Sector
