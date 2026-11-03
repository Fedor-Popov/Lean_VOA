import VOA.DeligneAudit.D4LeviKSRzHsymmEvaluation

/-! The general Rz raw seed as a fixed-shape sum of monomials. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

def rzRawModes (a b k l : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) (e : Fin k → ℕ) :
    PairSource a b (k + l) → ℕ
  | Sum.inl x => α x
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr z) => Fin.addCases e β z

theorem rzRawSourceGenerator_eq_sum_monomials
    (a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) :
    rzRawSourceGenerator a b k l s α β =
      ∑ e : {e : Fin k → ℕ // ∑ i, e i = s},
        ∏ t : PairSource a b (k + l),
          X t ^ rzRawModes a b k l α β e.1 t := by
  classical
  simp only [rzRawSourceGenerator, rzXSeed, rzZSeed,
    rz_hsymm_eq_sum_vectors, map_mul, map_sum, map_prod,
    map_pow, rename_X, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  simp [rzRawModes, Fintype.prod_sum_type, Fin.prod_univ_add,
    Fin.addCases, mul_assoc]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzRawSourceGenerator_eq_sum_monomials
