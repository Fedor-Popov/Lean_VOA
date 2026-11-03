import VOA.DeligneAudit.D4LevelReductionConvertedEvaluation

/-! Descent of the complete converted ideal to the universal level piece. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SL4T
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)
variable (a b c : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))

/-- A coefficient representative evaluates in the level filtration before coinvariants. -/
def coreBottomLevelLift : BiSymPoly →ₗ[ℂ]
    levelFiltration ρ w (a + b + c) b (2 * a + b) :=
  ((xyzEvaluation ρ w (bottomModeShape a c)).comp
    (coreBottomModePolynomial a c).toLinearMap).codRestrict _ fun P =>
      (bottomCartanLift ρ w a b c h
        (bottomSymmetricToCartan ρ w a b c h
          (bottomElementaryModes a c (leftComplementAlphabet P)))).property

/-- Raising preserves the level containing the bottom coefficient representatives. -/
def coreRaisingLevelLift (j : ℕ) : MvPolynomial (Fin j) BiSymPoly →ₗ[ℂ]
    levelFiltration ρ w (a + b + c) b (2 * a + b) :=
  positionModeEvaluation
    (fun _ s => (levelLeviCurrent ρ w (a + b + c) b (2 * a + b)).op 3 s)
    (List.finRange j) (coreBottomLevelLift ρ w a b c h)

/-- The lift has exactly the ambient polynomial raising evaluation. -/
theorem coreRaisingLevelLift_coe (j : ℕ) (P : MvPolynomial (Fin j) BiSymPoly) :
    (coreRaisingLevelLift ρ w a b c h j P : V) =
      coreRaisingSourceEvaluation ρ w a c j P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
      simp only [coreRaisingLevelLift, coreRaisingSourceEvaluation,
        middlePositionEvaluation_word]
      exact levelLeviCurrent_word_coe ρ w _ _ _ _ _
  | add P Q hP hQ => simp only [map_add, Submodule.coe_add, hP, hQ]

/-- Evaluation of coefficient representatives commutes with the level quotient. -/
theorem coreRaisingEvaluation_representative (j : ℕ)
    (P : MvPolynomial (Fin j) BiSymPoly) :
    coreRaisingEvaluation (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
      a b c (coreGrassmannianEvaluation ρ w a b c h) j
        (MvPolynomial.map (Ideal.Quotient.mk _) P) =
      levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)
        (coreRaisingLevelLift ρ w a b c h j P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
      rw [MvPolynomial.map_monomial, coreRaisingEvaluation, coreRaisingLevelLift,
        middlePositionEvaluation_word, middlePositionEvaluation_word,
        coreGrassmannianEvaluation_mk]
      exact levelCoinvariantMap_word ρ w _ _ _ _ _
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- Exact vanishing in the source implies vanishing of the evaluated core representative. -/
theorem coreRaisingEvaluation_zero_of_source (j : ℕ)
    (P : MvPolynomial (Fin j) BiSymPoly)
    (hP : coreRaisingSourceEvaluation ρ w a c j P = 0) :
    coreRaisingEvaluation (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
      a b c (coreGrassmannianEvaluation ρ w a b c h) j
        (MvPolynomial.map (Ideal.Quotient.mk _) P) = 0 := by
  rw [coreRaisingEvaluation_representative]
  have hz : coreRaisingLevelLift ρ w a b c h j P = 0 := by
    apply Subtype.ext
    exact (coreRaisingLevelLift_coe ρ w a b c h j P).trans hP
  rw [hz, map_zero]

/-- The complete-function representative maps to the prescribed core relation. -/
theorem coreRaisingCompleteRepresentative_map (j n : ℕ) :
    MvPolynomial.map (Ideal.Quotient.mk _) (coreRaisingCompleteRepresentative j n) =
      coreRaisingComplete a b c j n := by
  simp only [coreRaisingCompleteRepresentative, coreRaisingComplete,
    map_sum, map_mul, MvPolynomial.map_C, map_hsymm]
  rfl

/-- The full converted relation holds for every core coefficient and raising-mode multiplier. -/
theorem coreGrassmannianEvaluation_complete_mul_zero (j n : ℕ) (hn : c < j + n)
    (P : MvPolynomial (Fin j) (CoreBaseRing a b c)) :
    coreRaisingEvaluation (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
      a b c (coreGrassmannianEvaluation ρ w a b c h) j
        (P * coreRaisingComplete a b c j n) = 0 := by
  obtain ⟨Q, hQ⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective P
  rw [← hQ, ← coreRaisingCompleteRepresentative_map, ← map_mul]
  apply coreRaisingEvaluation_zero_of_source
  exact coreRaisingSourceEvaluation_complete_mul_zero ρ w (a + b + c) a c j n h hn Q

/-- The entire converted ideal vanishes in every saturated level coinvariant. -/
theorem coreGrassmannianEvaluation_converted :
    CoreConvertedRelations (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
      a b c (coreGrassmannianEvaluation ρ w a b c h) := by
  intro j P hP
  change coreRaisingEvaluation _ a b c (coreGrassmannianEvaluation ρ w a b c h) j P = 0
  have hall : ∀ Q ∈ coreRaisingIdeal a b c j,
      ∀ R, coreRaisingEvaluation
        (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
        a b c (coreGrassmannianEvaluation ρ w a b c h) j (R * Q) = 0 := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
        obtain ⟨n, hn, rfl⟩ := hQ
        intro R
        exact coreGrassmannianEvaluation_complete_mul_zero ρ w a b c h j n hn R
    | zero => intro R; rw [mul_zero, map_zero]
    | add Q S hQ hS ihQ ihS =>
        intro R
        rw [mul_add, map_add, ihQ, ihS, add_zero]
    | smul z Q hQ ih =>
        intro R
        simpa only [smul_eq_mul, mul_assoc] using ih (R * z)
  simpa only [one_mul] using hall P hP 1

/-- The universal evaluation satisfies every converted relation at every raising length. -/
theorem universalCoreEvaluation_converted (a b c : ℕ) :
    CoreConvertedRelations (universalCoreCurrent a b c) a b c
      (universalCoreEvaluation a b c) :=
  coreGrassmannianEvaluation_converted _ _ a b c
    (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0))

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingLevelLift_coe
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingEvaluation_representative
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingEvaluation_zero_of_source
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingCompleteRepresentative_map
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_complete_mul_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_converted
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_converted
