import VOA.DeligneAudit.D4LevelReductionCoreRootCurrents

/-! The union-alphabet characteristic relation for the highest negative root of the core. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

open VOA.DeligneAudit.SectorWeyl

/-- The signed Grassmannian coefficients are the Newton series after any specialization. -/
theorem coreGrassmannian_newtonSeries {R : Type} [CommRing R] [Algebra ℂ R]
    (d T : ℕ) (f : SL4T.GrassRing d T →ₐ[ℂ] R) :
    SL4T.newtonCoefficientSeries (SL4T.powerSumOfCoeff d
      (fun n => (-1) ^ n * f (SL4T.eClass d T n))) =
        ((SL4T.grassSeries d T).map f.toRingHom : PowerSeries R) := by
  ext n : 1
  simp only [SL4T.newtonCoefficientSeries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe, Polynomial.coeff_map]
  rw [SL4T.newtonCoeff_powerSumOfCoeff d _ (by simp [SL4T.eClass])]
  have ht : ∀ j, d < j → (-1 : SL4T.GrassRing d T) ^ j * SL4T.eClass d T j = 0 := by
    intro j hj
    rw [SL4T.eClass_eq_zero d T j hj, mul_zero]
  rw [SL4T.grassSeries, SL4T.coefficientPoly_coeff_of_tail _ d ht]
  simp

/-- Adding the two Cartan alphabets gives the coefficients of their product series. -/
theorem coreUnion_newtonCoeff (a b c n : ℕ) :
    SL4T.newtonCoeff
      (fun s => coreComplementPowerSum a b c s + coreAdjointPowerSum a b c s) n =
        (SL4T.S_series (a + b + c) (a + b) a).coeff n := by
  have he := SL4T.newtonCoefficientSeries_add
    (coreComplementPowerSum a b c) (coreAdjointPowerSum a b c)
  have hl : SL4T.newtonCoefficientSeries (coreComplementPowerSum a b c) =
      ((SL4T.grassSeries (a + b) (a + b + c - (a + b))).map
        (SL4T.biLeft (a + b) (a + b + c - (a + b)) a
          (a + b + c - a)).toRingHom : PowerSeries (CoreBaseRing a b c)) :=
    coreGrassmannian_newtonSeries _ _ _
  have hr : SL4T.newtonCoefficientSeries (coreAdjointPowerSum a b c) =
      ((SL4T.grassSeries a (a + b + c - a)).map
        (SL4T.biRight (a + b) (a + b + c - (a + b)) a
          (a + b + c - a)).toRingHom : PowerSeries (CoreBaseRing a b c)) :=
    coreGrassmannian_newtonSeries _ _ _
  rw [hl, hr, ← Polynomial.coe_mul] at he
  simpa only [SL4T.newtonCoefficientSeries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe, SL4T.S_series] using congrArg (PowerSeries.coeff n) he

/-- The highest-root Newton polynomial is the product of the two characteristic factors. -/
theorem coreUnion_descendingPolynomial (a b c : ℕ) :
    SL4T.descendingPoly
      (SL4T.newtonCoeff
        (fun s => coreComplementPowerSum a b c s + coreAdjointPowerSum a b c s))
      (a + b + a) =
        SL4T.leftP (a + b + c) (a + b) a * SL4T.rightP (a + b + c) (a + b) a := by
  rw [funext (coreUnion_newtonCoeff a b c)]
  rw [← funext (SL4T.S_newtonCoeff (a + b + c) (a + b) a)]
  exact SL4T.S_descending_newton (a + b + c) (a + b) a

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
variable (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreRelations Q a b c π)

include h

/-- The highest-root Cartan weight is the total size of the union alphabet with multiplicity. -/
theorem coreHighestCartan_weight (φ : CoreBaseRing a b c) :
    coreHighestCartan Q 0 (π φ) = ((a + b + a : ℕ) : ℂ) • π φ := by
  have hzero := h.weight 0 φ
  have hone := h.weight 1 φ
  have htwo := h.weight 2 φ
  simp only [A3Sector.simpleH, A3Sector.weightABC] at hzero hone htwo
  simp only [coreHighestCartan, LinearMap.add_apply, hzero, hone, htwo, Nat.cast_add]
  module

/-- Positive highest-root Cartan currents act by the sum of the two power-sum alphabets. -/
theorem coreHighestCartan_powerSum (s : ℕ) (hs : 1 ≤ s) (φ : CoreBaseRing a b c) :
    coreHighestCartan Q s (π φ) =
      π ((coreComplementPowerSum a b c s + coreAdjointPowerSum a b c s) * φ) := by
  have hzero := h.cartan 0 s hs φ
  have hone := h.cartan 1 s hs φ
  have htwo := h.cartan 2 s hs φ
  simp only [A3Sector.simpleH, coreCartanSymbol] at hzero hone htwo
  norm_num [Fin.ext_iff] at hzero hone htwo
  simp only [coreHighestCartan, LinearMap.add_apply, hzero, hone, htwo,
    sub_mul, add_mul, map_sub, map_add]
  abel

/-- Garland annihilates all multiples of the union characteristic on the bottom image. -/
theorem coreHighest_characteristic [FiniteDimensional ℂ V] :
    SL4T.PiCharacteristic (Q.op 8) π
      (SL4T.leftP (a + b + c) (a + b) a * SL4T.rightP (a + b + c) (a + b) a) := by
  rw [← coreUnion_descendingPolynomial a b c]
  apply SL4T.piCharacteristic_of_highest (coreHighest_currentRelations Q) π
    (fun s => coreComplementPowerSum a b c s + coreAdjointPowerSum a b c s)
    (fun s φ => h.parabolic 2 (by decide) (by decide) s φ)
    (coreHighestCartan_powerSum a b c Q π h) (a + b + a)
  · intro φ
    exact coreHighest_lowering_nilpotent (coreHighest_currentRelations Q) (π φ)
      (a + b + a) (h.parabolic 2 (by decide) (by decide) 0 φ)
      (coreHighestCartan_weight a b c Q π h φ)
  · intro j hj
    rw [coreUnion_newtonCoeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((SL4T.S_series_degree (a + b + c) (a + b) a).trans_lt hj)

/-- The highest negative root sends each cell vector below its union cutoff. -/
theorem coreCellGenerator_highest_truncation [FiniteDimensional ℂ V]
    (hhigh : ∀ e r, a + b + c ≤ r → Q.op e r = 0)
    (F : CoreCellFlag a b c) (i : ℕ) (hi : i < (coreCellCatalog a b c).length)
    (s : ℕ) (hs : coreCellCutoff a b c i ≤ s) :
    Q.op 8 s (π (F.generator i)) ∈ coreCellFiltration a b c Q π F i := by
  apply SL4T.piCurrentMap_cell (Q.op 8) π (F.ideal i)
    (coreCellFiltration a b c Q π F i)
    (SL4T.leftP (a + b + c) (a + b) a * SL4T.rightP (a + b + c) (a + b) a)
    (a + b + c)
    (fun φ hφ => coreIdealSpan_contains a b c Q π _ hφ)
    (fun r => coreCellFiltration_stable a b c Q π F i 8 r)
    (coreHighest_characteristic a b c Q π h)
    (fun r hr φ => by rw [hhigh 8 r hr]; rfl) (F.characteristic i hi) s hs

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannian_newtonSeries
#print axioms VOA.DeligneAudit.D4LevelReduction.coreUnion_newtonCoeff
#print axioms VOA.DeligneAudit.D4LevelReduction.coreUnion_descendingPolynomial
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighestCartan_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighestCartan_powerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_characteristic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_highest_truncation
