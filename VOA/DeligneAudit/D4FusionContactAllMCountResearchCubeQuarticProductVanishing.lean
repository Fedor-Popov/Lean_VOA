import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishingBase
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrent

/-! Derivative-product relations in the literal quadratic/cubic polar ideal.
That smaller ideal is proved to lie in the original candidate ideal. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Only admissible WHOLE coefficients of original normalized cube polars. -/
def quadraticCubicPolarSeeds (m : ℕ) : Set (MvPolynomial (Vars m) ℂ) :=
  {p | ∃ r a b c s, (r = 2 ∨ r = 3) ∧ m < r + s ∧
    p = PowerSeries.coeff s (currentMap m (orbit ℂ r a b c))}

def quadraticCubicPolarIdeal (m : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) :=
  Ideal.span (quadraticCubicPolarSeeds m)

theorem quadraticCubicPolar_coeff_mem (m r a b c s : ℕ)
    (hr : r = 2 ∨ r = 3) (hs : m < r + s) :
    PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) ∈ quadraticCubicPolarIdeal m :=
  Ideal.subset_span ⟨r,a,b,c,s,hr,hs,rfl⟩

theorem quadraticCubicPolarIdeal_le_candidate (m : ℕ) :
    quadraticCubicPolarIdeal m ≤ AllM.candidateIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨r,a,b,c,s,hr,hs,rfl⟩
  exact current_orbit_coeff_mem m r a b c s (by omega) hs

/-- Every quadratic/cubic jet convolution past the summed source cutoff
already belongs to the SMALL literal polar ideal, not merely the full ideal. -/
theorem quadratic_cubic_jet_product_coeff_mem_polarIdeal
    (m a b N x1 y1 z1 x2 y2 z2 : ℕ) (h : 2 * m < 5 + N + a + b) :
    PowerSeries.coeff N
      (jetDerivative a (currentMap m (orbit ℂ 2 x1 y1 z1)) * 
        jetDerivative b (currentMap m (orbit ℂ 3 x2 y2 z2))) ∈
          quadraticCubicPolarIdeal m := by
  exact coeff_jet_product_mem (quadraticCubicPolarIdeal m) _ _ 2 3 m a b N
    (fun k hk => quadraticCubicPolar_coeff_mem m 2 x1 y1 z1 k (Or.inl rfl) hk)
    (fun k hk => quadraticCubicPolar_coeff_mem m 3 x2 y2 z2 k (Or.inr rfl) hk) h

/-- The same whole-source convolution is an original actual D4 relation. -/
theorem quadratic_cubic_jet_product_coeff_mem
    (m a b N x1 y1 z1 x2 y2 z2 : ℕ) (h : 2 * m < 5 + N + a + b) :
    PowerSeries.coeff N
      (jetDerivative a (currentMap m (orbit ℂ 2 x1 y1 z1)) * 
        jetDerivative b (currentMap m (orbit ℂ 3 x2 y2 z2))) ∈
          AllM.candidateIdeal m :=
  quadraticCubicPolarIdeal_le_candidate m
    (quadratic_cubic_jet_product_coeff_mem_polarIdeal m a b N x1 y1 z1 x2 y2 z2 h)

end
#print axioms quadraticCubicPolarIdeal_le_candidate
#print axioms quadratic_cubic_jet_product_coeff_mem_polarIdeal
#print axioms quadratic_cubic_jet_product_coeff_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
