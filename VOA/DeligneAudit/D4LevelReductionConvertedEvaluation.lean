import VOA.DeligneAudit.D4LevelReductionConvertedAlphabet

/-! Exact evaluation of converted mode polynomials before taking the level quotient. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SL4T
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Modes of the middle simple raising current commute. -/
theorem middleRaisingCurrent_commute (Q : CurrentModule A3Sector.bracketTable V) (r s : ℕ) :
    Commute (Q.op 3 r) (Q.op 3 s) := by
  have hz (k : Fin 15) : A3Sector.bracketTable 3 3 k = 0 := by
    simp [A3Sector.bracketTable, A3Sector.bracketInt, A3Sector.commEntry]
  apply LinearMap.ext
  intro v
  exact sub_eq_zero.mp (by simpa [hz] using Q.comm 3 3 r s v)

variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The semisimple middle raising current is the ambient D4 operator with positive sign. -/
theorem leviMiddleRaising_operator (s : ℕ) :
    (leviCurrent ρ).op 3 s = ρ.op (leviColour (A3Sector.simpleE 1)) s := by
  simp [leviCurrent, leviSign, A3Sector.simpleE]

/-- The order reversal used by positional conversion does not change the raising word. -/
theorem middleRaisingProduct_reverse (rs : List ℕ) :
    middleRaisingProduct ρ rs.reverse = middleRaisingProduct ρ rs := by
  unfold middleRaisingProduct
  rw [List.map_reverse]
  apply (List.reverse_perm _).prod_eq'
  rw [List.pairwise_reverse, List.pairwise_map]
  apply List.pairwise_of_forall
  intro r s
  rw [← leviMiddleRaising_operator, ← leviMiddleRaising_operator]
  exact middleRaisingCurrent_commute _ s r

/-- The positional operator product is the corresponding ambient middle raising word. -/
theorem middlePositionProduct_ambient (j : ℕ) (u : Fin j →₀ ℕ) :
    positionModeProduct (fun _ s => (leviCurrent ρ).op 3 s) (List.finRange j) u =
      middleRaisingProduct ρ (List.ofFn fun i => u i) := by
  simp only [positionModeProduct, middleRaisingProduct, List.ofFn_eq_map,
    List.map_map, Function.comp_def, leviMiddleRaising_operator]

/-- Evaluate core coefficient representatives and raising modes in the saturated source. -/
def coreRaisingSourceEvaluation (a c j : ℕ) : MvPolynomial (Fin j) BiSymPoly →ₗ[ℂ] V :=
  positionModeEvaluation (fun _ s => (leviCurrent ρ).op 3 s) (List.finRange j)
    ((xyzEvaluation ρ w (bottomModeShape a c)).comp
      (coreBottomModePolynomial a c).toLinearMap)

/-- Polynomial raising evaluation is the sum of the exact slot substitutions. -/
theorem coreRaisingSourceEvaluation_choices (m a c j : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (P : MvPolynomial (Fin j) BiSymPoly) :
    coreRaisingSourceEvaluation ρ w a c j P =
      ((centralRaisingChoices (bottomModeShape a c) j).map fun q =>
        xyzEvaluation ρ w q.2 (coreRaisingSubstitution a c j q.1 P)).sum := by
  induction P using MvPolynomial.induction_on' with
  | monomial u z =>
      rw [coreRaisingSourceEvaluation, positionModeEvaluation_monomial,
        middlePositionProduct_ambient]
      change middleRaisingProduct ρ (List.ofFn fun i => u i)
        (xyzEvaluation ρ w (bottomModeShape a c) (coreBottomModePolynomial a c z)) = _
      rw [← middleRaisingProduct_reverse, middleRaisingProduct_choices ρ w m j h
        (bottomModeShape a c) (bottomModeShape_colours a c)]
      congr 1
      apply List.map_congr_left
      intro q hq
      congr 1
      change _ = eval₂Hom (coreBottomModePolynomial a c).toRingHom (fun i => X (q.1 i))
        (monomial u z)
      rw [eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      exact mul_comm _ _
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, List.sum_map_add]

/-- Every polynomial multiple of a converted generator vanishes in the saturated source. -/
theorem coreRaisingSourceEvaluation_complete_mul_zero (m a c j n : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (hn : c < j + n)
    (P : MvPolynomial (Fin j) BiSymPoly) :
    coreRaisingSourceEvaluation ρ w a c j (P * coreRaisingCompleteRepresentative j n) = 0 := by
  rw [coreRaisingSourceEvaluation_choices ρ w m a c j h]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  rw [coreRaisingSubstitution_complete_mul_zero a c j n q hq hn, map_zero]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingCurrent_commute
#print axioms VOA.DeligneAudit.D4LevelReduction.leviMiddleRaising_operator
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingProduct_reverse
#print axioms VOA.DeligneAudit.D4LevelReduction.middlePositionProduct_ambient
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSourceEvaluation_choices
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSourceEvaluation_complete_mul_zero
