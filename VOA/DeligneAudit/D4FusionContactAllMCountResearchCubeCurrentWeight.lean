import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrent

/-! Whole current coefficients preserve the explicit additive color weight.
This transfers the strict abstract cube remainder to the actual polynomial
ring; no image-space or flatness premise substitutes for this check. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

variable {σ : Type*}

def seriesWeighted (w : σ → ℕ) (n : ℕ) (f : PowerSeries (MvPolynomial σ ℂ)) : Prop :=
  ∀ s, (PowerSeries.coeff s f).IsWeightedHomogeneous w n

theorem seriesWeighted_algebraMap (w : σ → ℕ) (z : ℂ) :
    seriesWeighted w 0 (algebraMap ℂ (PowerSeries (MvPolynomial σ ℂ)) z) := by
  intro s
  rw [PowerSeries.algebraMap_apply,PowerSeries.coeff_C]
  split_ifs
  · exact MvPolynomial.isWeightedHomogeneous_C w z
  · exact MvPolynomial.isWeightedHomogeneous_zero ℂ w 0

theorem seriesWeighted_one (w : σ → ℕ) : seriesWeighted w 0 1 := by
  simpa only [map_one] using seriesWeighted_algebraMap w (1:ℂ)

theorem seriesWeighted_mul {w : σ → ℕ} {n k : ℕ}
    {f g : PowerSeries (MvPolynomial σ ℂ)}
    (hf : seriesWeighted w n f) (hg : seriesWeighted w k g) :
    seriesWeighted w (n+k) (f*g) := by
  intro s
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro x _
  exact (hf x.1).mul (hg x.2)

theorem seriesWeighted_pow {w : σ → ℕ} {n : ℕ}
    {f : PowerSeries (MvPolynomial σ ℂ)} (hf : seriesWeighted w n f) (k : ℕ) :
    seriesWeighted w (k*n) (f^k) := by
  induction k with
  | zero => simpa only [pow_zero,Nat.zero_mul] using seriesWeighted_one w
  | succ k ih =>
      simpa only [pow_succ,Nat.succ_mul] using seriesWeighted_mul ih hf

theorem seriesWeighted_prod {ι : Type*} (w : σ → ℕ) (s : Finset ι)
    (f : ι → PowerSeries (MvPolynomial σ ℂ)) (n : ι → ℕ)
    (h : ∀ i ∈ s, seriesWeighted w (n i) (f i)) :
    seriesWeighted w (∑ i ∈ s, n i) (∏ i ∈ s, f i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty,Finset.prod_empty] using seriesWeighted_one w
  | @insert i s hi ih =>
      intro h
      rw [Finset.sum_insert hi,Finset.prod_insert hi]
      exact seriesWeighted_mul (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def sourceEnergy : Fin 8 → ℕ := ![0,1,1,4,1,4,4,9]
def contactEnergy : Fin 9 → ℕ := ![0,1,1,1,4,4,4,9,0]
def currentColorWeight (m : ℕ) : Vars m → ℕ := fun x => contactEnergy x.1

theorem cubeColor_energy : ∀ i : Fin 8, contactEnergy (cubeColor i) = sourceEnergy i := by
  decide +kernel

theorem sourceEnergy_weight (d : Fin 8 →₀ ℕ) :
    Finsupp.weight sourceEnergy d = energy d := by
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_eight,
    sourceEnergy,energy,mul_comm,add_assoc]

theorem actualMode_weighted (m s : ℕ) (i : Fin 8) :
    (actualMode m s i).IsWeightedHomogeneous (currentColorWeight m) (sourceEnergy i) := by
  unfold actualMode
  by_cases hs : s < m
  · rw [modeX,dif_pos hs]
    have hh := MvPolynomial.isWeightedHomogeneous_X ℂ (currentColorWeight m)
      (cubeColor i,⟨s,hs⟩)
    change (MvPolynomial.X (cubeColor i,⟨s,hs⟩) : MvPolynomial (Vars m) ℂ).IsWeightedHomogeneous
      (currentColorWeight m) (contactEnergy (cubeColor i)) at hh
    rw [cubeColor_energy] at hh
    intro d hd
    rw [MvPolynomial.coeff_smul] at hd
    exact hh (right_ne_zero_of_mul hd)
  · rw [modeX,dif_neg hs,smul_zero]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ (currentColorWeight m) (sourceEnergy i)

theorem actualCurrent_weighted (m : ℕ) (i : Fin 8) :
    seriesWeighted (currentColorWeight m) (sourceEnergy i) (actualCurrent m i) := by
  intro s
  rw [actualCurrent_coeff]
  exact actualMode_weighted m s i

/-- The whole coefficient of each source monomial has the SAME explicit color weight. -/
theorem currentMap_monomial_weighted (m : ℕ) (d : Fin 8 →₀ ℕ) (z : ℂ) :
    seriesWeighted (currentColorWeight m) (energy d)
      (currentMap m (MvPolynomial.monomial d z)) := by
  rw [currentMap,MvPolynomial.aeval_monomial]
  have hp : seriesWeighted (currentColorWeight m)
      (d.sum fun i n => n * sourceEnergy i)
      (d.prod fun i n => actualCurrent m i ^ n) := by
    exact seriesWeighted_prod (currentColorWeight m) d.support
      (fun i => actualCurrent m i ^ d i) (fun i => d i * sourceEnergy i)
      (fun i _ => seriesWeighted_pow (actualCurrent_weighted m i) (d i))
  have he := sourceEnergy_weight d
  simp only [Finsupp.weight_apply,nsmul_eq_mul,Nat.cast_id] at he
  rw [he] at hp
  simpa only [zero_add] using
    seriesWeighted_mul (seriesWeighted_algebraMap (currentColorWeight m) z) hp

def currentColorLow (m L : ℕ) : Submodule ℂ (MvPolynomial (Vars m) ℂ) :=
  Finsupp.supported ℂ ℂ {d | Finsupp.weight (currentColorWeight m) d < L}

/-- Strict weight is proved in the actual target monomials, not just in a named image. -/
theorem current_coefficient_low (m s L : ℕ) (p : P8 ℂ) (hp : p ∈ colorLow ℂ L) :
    PowerSeries.coeff s (currentMap m p) ∈ currentColorLow m L := by
  change (↑p.support : Set (Fin 8 →₀ ℕ)) ⊆ {d | energy d < L} at hp
  rw [MvPolynomial.as_sum p,map_sum,map_sum]
  apply Submodule.sum_mem
  intro d hd
  change (↑(PowerSeries.coeff s (currentMap m
    (MvPolynomial.monomial d (MvPolynomial.coeff d p)))).support : Set (Vars m →₀ ℕ)) ⊆ _
  intro e he
  have hw := currentMap_monomial_weighted m d (MvPolynomial.coeff d p) s
    (MvPolynomial.mem_support_iff.mp he)
  change Finsupp.weight (currentColorWeight m) e < L
  rw [hw]
  exact hp hd

end
#print axioms currentMap_monomial_weighted
#print axioms current_coefficient_low
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
