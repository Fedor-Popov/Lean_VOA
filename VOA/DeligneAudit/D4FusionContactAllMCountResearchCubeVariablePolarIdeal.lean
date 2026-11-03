import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishingPower

/-! Literal lower ideals for consecutive source powers. These results give
the coefficient cutoff needed by variable-power identities; they do not
assert such identities or a quotient dimension bound. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Admissible whole polar coefficients at the two unchanged source powers. -/
def consecutivePolarSeeds (m n : ℕ) : Set (MvPolynomial (Vars m) ℂ) :=
  {p | ∃ r a b c s, (r = n ∨ r = n + 1) ∧ m < r + s ∧
    p = PowerSeries.coeff s (currentMap m (orbit ℂ r a b c))}

def consecutivePolarIdeal (m n : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) :=
  Ideal.span (consecutivePolarSeeds m n)

theorem consecutivePolar_coeff_mem (m n r a b c s : ℕ)
    (hr : r = n ∨ r = n + 1) (hs : m < r + s) :
    PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) ∈
      consecutivePolarIdeal m n :=
  Ideal.subset_span ⟨r,a,b,c,s,hr,hs,rfl⟩

theorem consecutivePolarIdeal_two (m : ℕ) :
    consecutivePolarIdeal m 2 = quadraticCubicPolarIdeal m := rfl

/-- Explicit original zero-mode source words place the lower ideal in the
bounded source ideal, without any source-completeness premise. -/
theorem consecutivePolarIdeal_le_powerBounded (m n : ℕ) (hn : 1 ≤ n) :
    consecutivePolarIdeal m n ≤ LeviRules.powerBoundedIdeal m (n + 1) := by
  apply Ideal.span_le.mpr
  rintro p ⟨r,a,b,c,s,hr,hs,rfl⟩
  exact current_orbit_coeff_mem_powerBounded m (n + 1) r a b c s
    (by omega) (by omega) hs

/-- The original nonzero current-degree-zero witness separates these
literal lower ideals from the full original candidate ideal. -/
theorem consecutivePolarIdeal_lt_candidate (m n : ℕ)
    (hn : 1 ≤ n) (hm : n + 1 ≤ m) :
    consecutivePolarIdeal m n < AllM.candidateIdeal m :=
  lt_of_le_of_lt (consecutivePolarIdeal_le_powerBounded m n hn)
    (LeviRules.powerBoundedIdeal_lt_candidate m (n + 1) (by omega) hm)

theorem consecutive_jet_product_coeff_mem_polarIdeal
    (m n a b N x1 y1 z1 x2 y2 z2 : ℕ)
    (h : 2 * m < 2 * n + 1 + N + a + b) :
    PowerSeries.coeff N
      (jetDerivative a (currentMap m (orbit ℂ n x1 y1 z1)) *
        jetDerivative b (currentMap m (orbit ℂ (n + 1) x2 y2 z2))) ∈
          consecutivePolarIdeal m n := by
  apply coeff_jet_product_mem (consecutivePolarIdeal m n) _ _ n (n + 1) m a b N
    (fun k hk => consecutivePolar_coeff_mem m n n x1 y1 z1 k (Or.inl rfl) hk)
    (fun k hk => consecutivePolar_coeff_mem m n (n + 1) x2 y2 z2 k (Or.inr rfl) hk)
  omega

/-- Natural subtraction applies to the entire source-power correction. -/
def variablePowerBudget (m n : ℕ) : ℕ := (2 * m + 1) - 2 * n

theorem variablePowerBudget_jet_cutoff (m n j : ℕ) :
    2 * m < 2 * n + 1 + (variablePowerBudget m n - j) + j := by
  dsimp [variablePowerBudget]
  omega

theorem consecutive_jet_product_budget_mem_polarIdeal
    (m n a b j x1 y1 z1 x2 y2 z2 : ℕ) (hab : a + b = j) :
    PowerSeries.coeff (variablePowerBudget m n - j)
      (jetDerivative a (currentMap m (orbit ℂ n x1 y1 z1)) *
        jetDerivative b (currentMap m (orbit ℂ (n + 1) x2 y2 z2))) ∈
          consecutivePolarIdeal m n := by
  apply consecutive_jet_product_coeff_mem_polarIdeal
  have h := variablePowerBudget_jet_cutoff m n j
  omega

/-- The externally shifted coefficient is the quantity transferred to a
filtered finite moment. Orders above the budget give zero, not a clamped
raw-jet coefficient. -/
theorem consecutive_jet_product_moment_mem_polarIdeal
    (m n a b j x1 y1 z1 x2 y2 z2 : ℕ) (hab : a + b = j) :
    PowerSeries.coeff (variablePowerBudget m n)
      (PowerSeries.X ^ j *
        (jetDerivative a (currentMap m (orbit ℂ n x1 y1 z1)) *
          jetDerivative b (currentMap m (orbit ℂ (n + 1) x2 y2 z2)))) ∈
          consecutivePolarIdeal m n := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hj
  · exact consecutive_jet_product_budget_mem_polarIdeal m n a b j
      x1 y1 z1 x2 y2 z2 hab
  · exact (consecutivePolarIdeal m n).zero_mem

end
#print axioms consecutivePolarIdeal_two
#print axioms consecutivePolarIdeal_le_powerBounded
#print axioms consecutivePolarIdeal_lt_candidate
#print axioms consecutive_jet_product_coeff_mem_polarIdeal
#print axioms variablePowerBudget_jet_cutoff
#print axioms consecutive_jet_product_budget_mem_polarIdeal
#print axioms consecutive_jet_product_moment_mem_polarIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
