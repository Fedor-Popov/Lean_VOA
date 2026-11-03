import VOA.Classification.COne.OrbIcoVSpecializeCompare

/-! The actual fixed coefficient functionals satisfy Xu's identities, closing B4. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbIcoT OrbIcoS OrbC2c
  InverseDS.VirasoroVerma HeisenbergN VOA.VirasoroScreening
  InverseDS.LeeYangFockVirasoro MvPolynomial
open scoped Classical

theorem vacuumCoefficient_from_Ward (R : ℕ) (hR : R<100)
    (a : FiniteFockPBW false R) (v : FiniteFockColumns false R → ℂ)
    (hv0 : finiteBlockProbe false R a ⟨0,by omega⟩ v=1)
    (hrows : finiteWardRowMap false R a 1 v=0) (r : ℕ) (hr : 2*r≤R) :
    vacuumCoefficient r = vacuumCoefficient 0 *
      ((2:ℂ)^r * finiteBlockProbe false R a ⟨2*r,by omega⟩ v) := by
  have hp := congrArg vacuumProbe
    (finiteActualSequence_matches_vacuum R hR a v hv0 hrows (2*r) hr)
  rw [vacuumState,vacuumProbe_vacuumProjection,map_smul] at hp
  have hvp : vacuumProbe (finiteActualSequence false R a v (2*r)) =
      finiteBlockProbe false R a ⟨2*r,by omega⟩ v := by
    simpa only [Bool.false_eq_true,if_false,mul_one] using
      finiteActualSequence_probe false R a v (2*r) hr
  rw [hvp] at hp
  have he : vacuumCoefficient r =
      (2:ℂ)^r * vacuumProbe (productState (2*r) (by omega)).val := by
    simp only [vacuumCoefficient,productState,Nat.cast_mul,Nat.cast_ofNat]
  rw [he,hp]
  simp only [smul_eq_mul]
  ring

theorem sixthCoefficient_from_Ward (R : ℕ) (hR : R<64)
    (a : FiniteFockPBW true R) (v : FiniteFockColumns true R → ℂ)
    (hv0 : finiteBlockProbe true R a ⟨0,by omega⟩ v=1)
    (hrows : finiteWardRowMap true R a 1 v=0) (r : ℕ) (hr : 2*r≤R) :
    sixthCoefficient (18+r) = icoSixthCoupling *
      ((2:ℂ)^r * finiteBlockProbe true R a ⟨2*r,by omega⟩ v) := by
  have hp := congrArg sixthProbe
    (finiteActualSequence_matches_sixth R hR a v hv0 hrows (2*r) hr)
  rw [sixthState,sixthProbe_sixthProjection,map_smul] at hp
  have hvp : sixthProbe (finiteActualSequence true R a v (2*r)) =
      finiteBlockProbe true R a ⟨2*r,by omega⟩ v * neutralProbe Xico := by
    simpa only [if_true] using finiteActualSequence_probe true R a v (2*r) hr
  rw [hvp] at hp
  have he : sixthCoefficient (18+r) =
      ((2:ℂ)^r * sixthProbe (productState (36+2*r) (by omega)).val)/neutralProbe Xico := by
    have hi : (71-2*((18+r:ℕ):ℤ)) = 71-((36+2*r:ℕ):ℤ) := by push_cast; ring
    simp only [sixthCoefficient,show 18+r-18=r by omega,hi,productState]
  rw [he,hp]
  simp only [smul_eq_mul]
  field_simp [neutralProbe_Xico_ne_zero]

/-- The first genuine vacuum-channel coefficient equals its nonzero ground coupling
multiplied by Xu's certified normalized value. -/
theorem vacuumCoefficient37_exact : vacuumCoefficient 37=vacuumCoefficient 0*(xuU37:ℂ) := by
  obtain ⟨a,v,hv0,hrows,h37,h38⟩ := exists_specialized_vacuum_Xu
  have h := vacuumCoefficient_from_Ward 76 (by omega) a v hv0 hrows 37 (by omega)
  rwa [h37] at h

theorem vacuumCoefficient38_exact : vacuumCoefficient 38=vacuumCoefficient 0*(xuU38:ℂ) := by
  obtain ⟨a,v,hv0,hrows,h37,h38⟩ := exists_specialized_vacuum_Xu
  have h := vacuumCoefficient_from_Ward 76 (by omega) a v hv0 hrows 38 (by omega)
  rwa [h38] at h

/-- The first genuine sixth-channel coefficient equals the actual nonzero sixth
coupling multiplied by Xu's certified normalized value. -/
theorem sixthCoefficient37_exact : sixthCoefficient 37=icoSixthCoupling*(xuV19:ℂ) := by
  obtain ⟨a,v,hv0,hrows,h19,h20⟩ := exists_specialized_self_Xu
  have h := sixthCoefficient_from_Ward 40 (by omega) a v hv0 hrows 19 (by omega)
  rwa [h19] at h

theorem sixthCoefficient38_exact : sixthCoefficient 38=icoSixthCoupling*(xuV20:ℂ) := by
  obtain ⟨a,v,hv0,hrows,h19,h20⟩ := exists_specialized_self_Xu
  have h := sixthCoefficient_from_Ward 40 (by omega) a v hv0 hrows 20 (by omega)
  rwa [h20] at h

/-- All parts of the fixed actual-coefficient numerical gate hold outright. -/
theorem actualCoefficientCompatibility_holds : ActualCoefficientCompatibility := by
  constructor
  · rw [vacuumCoefficient37_exact,sixthCoefficient37_exact]
    exact mul_ne_zero
      (mul_ne_zero vacuumCoefficient_zero_ne_zero xuU37_ne_zero)
      (mul_ne_zero icoSixthCoupling_ne_zero xuV19_ne_zero)
  · constructor
    · rw [vacuumCoefficient37_exact,vacuumCoefficient38_exact]
      ring
    · rw [sixthCoefficient37_exact,sixthCoefficient38_exact]
      ring

/-- The unchanged original icosahedral symbol-relation target is proved. -/
theorem icoSymbolRelations_holds : IcoSymbolRelations :=
  icoSymbolRelations_of_actual_coefficients actualCoefficientCompatibility_holds

end VOA.Classification.COne.OrbIcoV
