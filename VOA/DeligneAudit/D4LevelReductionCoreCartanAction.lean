import VOA.DeligneAudit.D4LevelReductionCoreEvaluation

/-! Cartan equivariance of the honest two-Grassmannian evaluation on every bottom level. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SL4T
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- The power-sum polynomial in abstract elementary generators. -/
def elementaryPowerSum (d s : ℕ) : SymPoly :=
  powerSumOfCoeff d (fun n => (-1) ^ n * elementary n) s

/-- Positive Cartan symbols in the actual central and adjoint elementary alphabets. -/
def bottomCartanSymbol (a c : ℕ) (i : Fin 3) (s : ℕ) : BiSymPoly :=
  if i = 1 then -alphabetIn true (elementaryPowerSum a s) -
    alphabetIn false (elementaryPowerSum c s)
  else alphabetIn true (elementaryPowerSum a s)

theorem bottomElementaryModes_centralPowerSum (a c s : ℕ) (hs : 0 < s) :
    (bottomElementaryModes a c (alphabetIn false (elementaryPowerSum c s)) :
      MvPolynomial (BottomModeSlot a c) ℂ) = colourPsum (bottomModeShape a c) 5 s := by
  rw [bottomElementaryModes_central, elementaryPowerSum, powerSumOfCoeff_map,
    powerSumOfCoeff_map]
  simp only [map_mul, map_pow, map_neg, map_one, elementarySpecialization_elementary]
  rw [powerSumOfCoeff_psum_map (Fin c) (rename Sum.inl) c s hs,
    bottomModeShape_centralPowerSum]

theorem bottomElementaryModes_adjointPowerSum (a c s : ℕ) (hs : 0 < s) :
    (bottomElementaryModes a c (alphabetIn true (elementaryPowerSum a s)) :
      MvPolynomial (BottomModeSlot a c) ℂ) = colourPsum (bottomModeShape a c) 1 s := by
  rw [bottomElementaryModes_adjoint, elementaryPowerSum, powerSumOfCoeff_map,
    powerSumOfCoeff_map]
  simp only [map_mul, map_pow, map_neg, map_one, elementarySpecialization_elementary]
  rw [powerSumOfCoeff_psum_map (Fin a) (rename Sum.inr) a s hs,
    bottomModeShape_adjointPowerSum]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Multiplication by a colour power sum evaluates as the sum of the corresponding mode shifts. -/
theorem bottomMode_powerSum_evaluation {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (d : σ →₀ ℕ) (j : Fin 6) (r : ℕ) :
    xyzEvaluation ρ w shape (colourPsum shape j r * modeMonomial σ d) =
      colourPowerShift ρ w j r (shapedModes shape Finset.univ.toList d) := by
  classical
  rw [← symmetricShiftAction_apply, symmetricShiftAction_colourPsum, map_list_sum,
    colourPowerShift_shapedModes ρ w shape Finset.univ.toList (Finset.nodup_toList _) d j r]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases hij : shape i = j
  · simp [hij, xyzEvaluation, modeWordEvaluation_monomial]
  · simp [hij]

variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Positive Cartan currents act by the two positional mode power sums before quotienting. -/
theorem bottomMode_cartan_evaluation (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (i : Fin 3) (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial (BottomModeSlot a c) ℂ) :
    (leviCurrent ρ).op (A3Sector.simpleH i) s (xyzEvaluation ρ w (bottomModeShape a c) P) =
      xyzEvaluation ρ w (bottomModeShape a c)
        ((bottomElementaryModes a c (bottomCartanSymbol a c i s) :
          MvPolynomial (BottomModeSlot a c) ℂ) * P) := by
  have hsymbol : (bottomElementaryModes a c (bottomCartanSymbol a c i s) :
      MvPolynomial (BottomModeSlot a c) ℂ) =
        if i = 1 then -colourPsum (bottomModeShape a c) 1 s -
          colourPsum (bottomModeShape a c) 5 s else colourPsum (bottomModeShape a c) 1 s := by
    unfold bottomCartanSymbol
    split_ifs <;> simp only [map_sub, map_neg, Subalgebra.coe_sub, Subalgebra.coe_neg,
      bottomElementaryModes_centralPowerSum a c s hs,
      bottomElementaryModes_adjointPowerSum a c s hs]
  rw [hsymbol]
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      have he : (monomial d z : MvPolynomial (BottomModeSlot a c) ℂ) =
          z • modeMonomial (BottomModeSlot a c) d := by simp [modeMonomial, smul_monomial]
      rw [he, mul_smul_comm, map_smul, map_smul, map_smul]
      congr 1
      have hc : ∀ q ∈ shapedModes (bottomModeShape a c) Finset.univ.toList d,
          q.1 = 1 ∨ q.1 = 5 := by
        rintro q hq
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
        cases t <;> simp [bottomModeShape]
      have hh := bottomWord_cartanPowerSums ρ w m h i s hs
        (shapedModes (bottomModeShape a c) Finset.univ.toList d) hc
      change (leviCurrent ρ).op (A3Sector.simpleH i) s
        (xyzEvaluation ρ w (bottomModeShape a c) (modeMonomial (BottomModeSlot a c) d)) = _
      rw [show xyzEvaluation ρ w (bottomModeShape a c) (modeMonomial (BottomModeSlot a c) d) =
          radicalWord ρ w (shapedModes (bottomModeShape a c) Finset.univ.toList d) from
        modeWordEvaluation_monomial _ _ d, hh]
      split_ifs <;> simp only [sub_mul, neg_mul, map_sub, map_neg,
        bottomMode_powerSum_evaluation]
  | add P Q hP hQ => simp only [map_add, mul_add, hP, hQ]

/-- The complement convention converts the core Cartan symbols to actual bottom Cartan symbols. -/
theorem coreGrassmannianToBottom_cartanSymbol (a b c : ℕ) (i : Fin 3) (s : ℕ)
    (hs : 0 < s) :
    coreGrassmannianToBottom a b c (coreCartanSymbol a b c i s) =
      Ideal.Quotient.mk _ (bottomCartanSymbol a c i s) := by
  have hx : coreGrassmannianToBottom a b c (coreAdjointPowerSum a b c s) =
      Ideal.Quotient.mk _ (alphabetIn true (elementaryPowerSum a s)) := by
    rw [coreAdjointPowerSum, powerSumOfCoeff_map]
    simp only [map_mul, map_pow, map_neg, map_one, coreGrassmannianToBottom_rightElementary]
    simp only [elementaryPowerSum, powerSumOfCoeff_map, map_mul, map_pow, map_neg, map_one]
    simpa only [map_mul, map_pow, map_neg, map_one] using
      (powerSumOfCoeff_map (Ideal.Quotient.mkₐ ℂ (biGrassIdeal c (a + b) a (b + c)))
        a (fun n => (-1) ^ n * alphabetIn true (elementary n)) s).symm
  have hz := coreGrassmannianToBottom_complementPowerSum a b c s hs
  have hg : coreGrassmannianToBottom a b c (coreComplementPowerSum a b c s) =
      -Ideal.Quotient.mk _ (alphabetIn false (elementaryPowerSum c s)) := by
    rw [hz]
    simp only [elementaryPowerSum, powerSumOfCoeff_map, map_mul, map_pow, map_neg, map_one]
    congr 1
    simpa only [map_mul, map_pow, map_neg, map_one] using
      (powerSumOfCoeff_map (Ideal.Quotient.mkₐ ℂ (biGrassIdeal c (a + b) a (b + c)))
        c (fun n => (-1) ^ n * alphabetIn false (elementary n)) s).symm
  unfold coreCartanSymbol bottomCartanSymbol
  split_ifs
  · rw [map_sub, hg, hx, map_sub, map_neg]
    abel
  · exact hx

/-- Cartan equivariance descends from the symmetric mode evaluator to the Grassmannian source. -/
theorem bottomGrassmannianEvaluation_cartan (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (i : Fin 3) (s : ℕ) (hs : 0 < s) (P : BiGrass c (a + b) a (b + c)) :
    (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b)).op (A3Sector.simpleH i) s
      (bottomGrassmannianEvaluation ρ w a b c h P) =
        bottomGrassmannianEvaluation ρ w a b c h
          (Ideal.Quotient.mk _ (bottomCartanSymbol a c i s) * P) := by
  induction P using Quotient.inductionOn' with
  | h P =>
      change (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b)).op
        (A3Sector.simpleH i) s
        (bottomGrassmannianEvaluation ρ w a b c h (Ideal.Quotient.mk _ P)) =
          bottomGrassmannianEvaluation ρ w a b c h
            (Ideal.Quotient.mk _ (bottomCartanSymbol a c i s) * Ideal.Quotient.mk _ P)
      rw [← map_mul, bottomGrassmannianEvaluation_mk, bottomGrassmannianEvaluation_mk]
      change levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)
        ((levelLeviCurrent ρ w (a + b + c) b (2 * a + b)).op (A3Sector.simpleH i) s
          (bottomCartanLift ρ w a b c h
            (bottomSymmetricToCartan ρ w a b c h (bottomElementaryModes a c P)))) =
        levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)
          (bottomCartanLift ρ w a b c h
            (bottomSymmetricToCartan ρ w a b c h
              (bottomElementaryModes a c (bottomCartanSymbol a c i s * P))))
      congr 1
      apply Subtype.ext
      simpa only [map_mul, Subalgebra.coe_mul] using bottomMode_cartan_evaluation
        ρ w (a + b + c) a c h i s hs (bottomElementaryModes a c P)

/-- The honest Grassmannian evaluation has exactly the Cartan action specified by the core. -/
theorem coreGrassmannianEvaluation_cartan (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0)) :
    CoreCartanAction (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b)) a b c
      (coreGrassmannianEvaluation ρ w a b c h) := by
  intro i s hs P
  change (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b)).op (A3Sector.simpleH i) s
    (bottomGrassmannianEvaluation ρ w a b c h (coreGrassmannianToBottom a b c P)) =
      bottomGrassmannianEvaluation ρ w a b c h
        (coreGrassmannianToBottom a b c (coreCartanSymbol a b c i s * P))
  rw [map_mul, coreGrassmannianToBottom_cartanSymbol a b c i s hs]
  exact bottomGrassmannianEvaluation_cartan ρ w a b c h i s hs _

/-- All universal bottom levels satisfy the positive Cartan part of the core presentation. -/
theorem universalCoreEvaluation_cartan (a b c : ℕ) :
    CoreCartanAction (universalCoreCurrent a b c) a b c (universalCoreEvaluation a b c) :=
  coreGrassmannianEvaluation_cartan _ _ a b c _

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.bottomElementaryModes_centralPowerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomElementaryModes_adjointPowerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomMode_powerSum_evaluation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomMode_cartan_evaluation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_cartanSymbol
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomGrassmannianEvaluation_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_cartan
