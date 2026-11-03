import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrent

/-! Whole quartic sources singled out by the bounded quintic experiments.
Only source membership is asserted; no reduced head or rank is assumed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def quarticBlockAxes : Fin 8 → Fin 3 → ℕ := ![
  ![2,2,2],![1,2,2],![2,1,2],![1,1,2],
  ![2,2,1],![1,2,1],![2,1,1],![1,1,1]]

def quarticBlockSource (m : ℕ) (i : Fin 8) (k : Fin m) : MvPolynomial (Vars m) ℂ :=
  actualMode m k.val i * PowerSeries.coeff (2*m-3-k.val)
    (currentMap m (orbit ℂ 4 (quarticBlockAxes i 0) (quarticBlockAxes i 1) (quarticBlockAxes i 2)))

/-- All8m static rows are in the original sound candidate ideal. -/
theorem quarticBlockSource_mem (m : ℕ) (i : Fin 8) (k : Fin m) :
    quarticBlockSource m i k ∈ AllM.candidateIdeal m := by
  apply (AllM.candidateIdeal m).mul_mem_left
  exact current_orbit_coeff_mem m 4 _ _ _ _ (by decide) (by have hk := k.isLt; omega)

def quarticWitness (m : ℕ) : MvPolynomial (Vars m) ℂ :=
  actualMode m (m-1) 0 * PowerSeries.coeff (m-2) (currentMap m (orbit ℂ 4 2 2 2))

theorem quarticWitness_mem (m : ℕ) : quarticWitness m ∈ AllM.candidateIdeal m := by
  apply (AllM.candidateIdeal m).mul_mem_left
  exact current_orbit_coeff_mem m 4 2 2 2 (m-2) (by decide) (by omega)

end
#print axioms quarticBlockSource_mem
#print axioms quarticWitness_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
