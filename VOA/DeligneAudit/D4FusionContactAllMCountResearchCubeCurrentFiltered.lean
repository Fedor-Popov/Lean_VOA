import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrentWeight

/-! Actual whole-current chain straightening, with an explicit strict color
filtration. No dimension, normal-completeness or image-space premise occurs. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Whole normalized chain product; the mode coefficient is taken afterwards. -/
def chainCurrentProduct (m r a b c : ℕ) : PowerSeries (MvPolynomial (Vars m) ℂ) :=
  actualCurrent m 0^(r-a) * actualCurrent m 1^(a-b) *
    actualCurrent m 3^(b-c) * actualCurrent m 7^c

theorem currentMap_chainTerm (m r a b c : ℕ) :
    currentMap m (chainTerm ℂ r a b c) =
      (towerCoeff r a b c : ℂ) • chainCurrentProduct m r a b c := by
  simp only [chainTerm,map_mul,map_pow,map_natCast,currentMap_X,chainCurrentProduct,
    Algebra.smul_def,map_natCast]
  simp only [mul_assoc]

/-- The leading whole coefficient lies in the actual source ideal modulo
explicitly lower additive color weight. -/
theorem chainTerm_coefficient_mem (m r a b c s : ℕ)
    (hr : 1 ≤ r) (hs : m < r + s) (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    PowerSeries.coeff s (currentMap m (chainTerm ℂ r a b c)) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) := by
  have hsource : PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) :=
    Submodule.mem_sup_left (current_orbit_coeff_mem m r a b c s hr hs)
  have hlow := current_coefficient_low m s (a+3*b+5*c)
    (orbit ℂ r a b c - chainTerm ℂ r a b c)
    (orbit_sub_chainTerm_mem ℂ r a b c ha hb hc)
  rw [map_sub,map_sub] at hlow
  have herror : PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) -
      PowerSeries.coeff s (currentMap m (chainTerm ℂ r a b c)) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) :=
    Submodule.mem_sup_right hlow
  simpa only [sub_sub_cancel] using Submodule.sub_mem _ hsource herror

theorem chain_coefficient_mem (m r a b c s : ℕ)
    (hr : 1 ≤ r) (hs : m < r + s) (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    PowerSeries.coeff s (chainCurrentProduct m r a b c) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) := by
  have h := chainTerm_coefficient_mem m r a b c s hr hs ha hb hc
  rw [currentMap_chainTerm,PowerSeries.coeff_smul] at h
  have hn : (towerCoeff r a b c : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (towerCoeff_pos r a b c ha hb hc))
  exact (Submodule.smul_mem_iff _ hn).mp h

/-- The original contact colors 0,1,4,7; no sign-normalized variable remains. -/
def rawChainCurrentProduct (m r a b c : ℕ) : PowerSeries (MvPolynomial (Vars m) ℂ) :=
  AllM.current m 0^(r-a) * AllM.current m 1^(a-b) *
    AllM.current m 4^(b-c) * AllM.current m 7^c

theorem chainCurrentProduct_eq_raw (m r a b c : ℕ) (hc : c ≤ b) :
    chainCurrentProduct m r a b c = (-1:ℂ)^b • rawChainCurrentProduct m r a b c := by
  have h0 : actualCurrent m 0 = AllM.current m 0 := by simp [actualCurrent,cubeSign,cubeColor]
  have h1 : actualCurrent m 1 = AllM.current m 1 := by simp [actualCurrent,cubeSign,cubeColor]
  have h3 : actualCurrent m 3 = (-1:ℂ) • AllM.current m 4 := by
    simp [actualCurrent,cubeSign,cubeColor]
  have h7 : actualCurrent m 7 = (-1:ℂ) • AllM.current m 7 := by
    simp [actualCurrent,cubeSign,cubeColor]
  simp only [chainCurrentProduct,rawChainCurrentProduct,h0,h1,h3,h7,
    smul_pow,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [← pow_add,Nat.add_sub_of_le hc]

theorem raw_chain_coefficient_mem (m r a b c s : ℕ)
    (hr : 1 ≤ r) (hs : m < r + s) (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    PowerSeries.coeff s (rawChainCurrentProduct m r a b c) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) := by
  have h := chain_coefficient_mem m r a b c s hr hs ha hb hc
  rw [chainCurrentProduct_eq_raw m r a b c hc,PowerSeries.coeff_smul] at h
  exact (Submodule.smul_mem_iff _ (pow_ne_zero b (neg_ne_zero.mpr one_ne_zero))).mp h

end
#print axioms chainTerm_coefficient_mem
#print axioms chain_coefficient_mem
#print axioms raw_chain_coefficient_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
