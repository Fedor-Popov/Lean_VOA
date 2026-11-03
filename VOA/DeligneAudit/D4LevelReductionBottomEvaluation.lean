import VOA.DeligneAudit.D4LevelReductionComplementAlphabet
import VOA.DeligneAudit.D4LeviKSMixedZeroSlots
import VOA.DeligneAudit.D4LeviKSMixedHsymmCurrent
import VOA.DeligneAudit.SL4TCompletePolynomialSpecialization

/-! Symmetric mode evaluation on the two radical alphabets of a bottom vector. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.LeviConversion

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- Central slots precede adjoint slots in the bottom mode polynomial. -/
abbrev BottomModeSlot (a c : ℕ) := Fin c ⊕ Fin a

/-- The two radical colours of the bottom multiplicity space. -/
def bottomModeShape (a c : ℕ) : BottomModeSlot a c → Fin 6 := Sum.elim (fun _ => 5) (fun _ => 1)

theorem bottomModeShape_colours (a c : ℕ) (i : BottomModeSlot a c) :
    bottomModeShape a c i = 1 ∨ bottomModeShape a c i = 4 ∨ bottomModeShape a c i = 5 := by
  cases i <;> simp [bottomModeShape]

/-- The central power sum is the power sum on the first summand of mode slots. -/
theorem bottomModeShape_centralPowerSum (a c s : ℕ) :
    colourPsum (bottomModeShape a c) 5 s =
      rename Sum.inl (psum (Fin c) ℂ s) := by
  classical
  simp only [colourPsum, Finset.sum_map_toList, psum, map_sum, map_pow, rename_X]
  simp [Fintype.sum_sum_type, bottomModeShape]

/-- The adjoint power sum is the power sum on the second summand of mode slots. -/
theorem bottomModeShape_adjointPowerSum (a c s : ℕ) :
    colourPsum (bottomModeShape a c) 1 s =
      rename Sum.inr (psum (Fin a) ℂ s) := by
  classical
  simp only [colourPsum, Finset.sum_map_toList, psum, map_sum, map_pow, rename_X]
  simp [Fintype.sum_sum_type, bottomModeShape]

/-- Symmetric central polynomials belong to the selective Cartan power-sum algebra. -/
theorem bottomCentral_symmetric_mem (a c : ℕ) (P : MvPolynomial (Fin c) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin c) ℂ) :
    rename Sum.inl P ∈ xyzPowerSumAlgebra (bottomModeShape a c) := by
  apply symmetric_image_mem_of_power_sums (Fin c) _ (rename Sum.inl) _ _ P hP
  intro r
  cases r with
  | zero => simp [psum_zero]
  | succ r =>
      rw [← bottomModeShape_centralPowerSum]
      exact Algebra.subset_adjoin ⟨5, r + 1, by simp, by omega, rfl⟩

/-- Symmetric adjoint polynomials belong to the selective Cartan power-sum algebra. -/
theorem bottomAdjoint_symmetric_mem (a c : ℕ) (P : MvPolynomial (Fin a) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin a) ℂ) :
    rename Sum.inr P ∈ xyzPowerSumAlgebra (bottomModeShape a c) := by
  apply symmetric_image_mem_of_power_sums (Fin a) _ (rename Sum.inr) _ _ P hP
  intro r
  cases r with
  | zero => simp [psum_zero]
  | succ r =>
      rw [← bottomModeShape_adjointPowerSum]
      exact Algebra.subset_adjoin ⟨1, r + 1, by simp, by omega, rfl⟩

/-- Abstract elementary generators specialize to the two actual mode alphabets. -/
def bottomElementaryModes (a c : ℕ) :
    SL4T.BiSymPoly →ₐ[ℂ] xyzPowerSumAlgebra (bottomModeShape a c) :=
  aeval fun q => if q.1 then
    ⟨rename Sum.inr (esymm (Fin a) ℂ (q.2 + 1)),
      bottomAdjoint_symmetric_mem a c _ (esymm_isSymmetric _ _ _)⟩ else
    ⟨rename Sum.inl (esymm (Fin c) ℂ (q.2 + 1)),
      bottomCentral_symmetric_mem a c _ (esymm_isSymmetric _ _ _)⟩

theorem bottomElementaryModes_central (a c : ℕ) (P : SL4T.SymPoly) :
    (bottomElementaryModes a c (SL4T.alphabetIn false P) :
      MvPolynomial (BottomModeSlot a c) ℂ) =
        rename Sum.inl (SL4T.elementarySpecialization c P) := by
  have he : (xyzPowerSumAlgebra (bottomModeShape a c)).val.comp
      ((bottomElementaryModes a c).comp (SL4T.alphabetIn false)) =
        (rename Sum.inl).comp (SL4T.elementarySpecialization c) := by
    ext i : 1
    simp [bottomElementaryModes, SL4T.alphabetIn, SL4T.elementarySpecialization]
  exact AlgHom.congr_fun he P

theorem bottomElementaryModes_adjoint (a c : ℕ) (P : SL4T.SymPoly) :
    (bottomElementaryModes a c (SL4T.alphabetIn true P) :
      MvPolynomial (BottomModeSlot a c) ℂ) =
        rename Sum.inr (SL4T.elementarySpecialization a P) := by
  have he : (xyzPowerSumAlgebra (bottomModeShape a c)).val.comp
      ((bottomElementaryModes a c).comp (SL4T.alphabetIn true)) =
        (rename Sum.inr).comp (SL4T.elementarySpecialization a) := by
    ext i : 1
    simp [bottomElementaryModes, SL4T.alphabetIn, SL4T.elementarySpecialization]
  exact AlgHom.congr_fun he P

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- A single-colour complete symmetric polynomial evaluates to its current power coefficient. -/
theorem constantShape_complete_evaluation (j : Fin 6) (n s : ℕ) :
    xyzEvaluation ρ w (fun _ : Fin n => j) (hsymm (Fin n) ℂ s) =
      PowerSeries.coeff s (fCurrent (fun r => ρ.op (radicalColour j) r) ^ n) w := by
  rw [xyz_hsymm_evaluation_current]
  simp

/-- Complete central functions evaluate to current coefficients with adjoint spectators. -/
theorem bottomCentral_complete_evaluation (a c s : ℕ) :
    xyzEvaluation ρ w (bottomModeShape a c) (rename Sum.inl (hsymm (Fin c) ℂ s)) =
      ((xOp ρ 0) ^ a * PowerSeries.coeff s (fCurrent (zOp ρ) ^ c)) w := by
  rw [xyzEvaluation_sum_zero_slots]
  have he : bottomModeShape a c ∘ Sum.inl = fun _ : Fin c => (5 : Fin 6) := rfl
  rw [he, constantShape_complete_evaluation]
  simp [bottomModeShape, xOp, zOp, radicalColour, Module.End.mul_apply]
  rfl

/-- Complete adjoint functions evaluate to current coefficients with central spectators. -/
theorem bottomAdjoint_complete_evaluation (a c s : ℕ) :
    xyzEvaluation ρ w (bottomModeShape a c) (rename Sum.inr (hsymm (Fin a) ℂ s)) =
      ((zOp ρ 0) ^ c * PowerSeries.coeff s (fCurrent (xOp ρ) ^ a)) w := by
  have he : (rename (Equiv.sumComm (Fin a) (Fin c))).comp (rename Sum.inl) =
      (rename Sum.inr : MvPolynomial (Fin a) ℂ →ₐ[ℂ]
        MvPolynomial (BottomModeSlot a c) ℂ) := by
    ext i : 1
    simp
  rw [← AlgHom.congr_fun he, AlgHom.comp_apply, xyzEvaluation_rename_bijection,
    xyzEvaluation_sum_zero_slots]
  have hs : (bottomModeShape a c ∘ Equiv.sumComm (Fin a) (Fin c)) ∘ Sum.inl =
      fun _ : Fin a => (1 : Fin 6) := rfl
  rw [hs, constantShape_complete_evaluation]
  simp [bottomModeShape, xOp, zOp, radicalColour, Module.End.mul_apply]
  rfl

/-- The constant mode polynomial evaluates to the distinguished bottom vector. -/
theorem bottomMode_evaluation_one (a c : ℕ) :
    xyzEvaluation ρ w (bottomModeShape a c) 1 = bottomVector ρ w a c := by
  have he := bottomCentral_complete_evaluation ρ w a c 0
  simpa [hsymm_zero, fCurrent, bottomVector, bottomRadicalWord, radicalWord_eq_prod,
    List.map_append, List.map_replicate, List.prod_append, List.prod_replicate,
    xOp, zOp, radicalColour] using he

/-- The bottom Cartan span is preserved by every reductive Cartan mode. -/
theorem bottomCartanSpan_rawCartan (a c : ℕ) (i : Fin 4) (r : ℕ) :
    bottomCartanSpan ρ w a c ≤
      (bottomCartanSpan ρ w a c).comap (ρ.op (reductiveCartanColour i) r) := by
  rw [bottomCartanSpan, Submodule.span_le]
  rintro v ⟨l, rfl⟩
  exact Submodule.subset_span ⟨(i, r) :: l, rfl⟩

/-- The Cartan combinations realizing symmetric shifts preserve the bottom Cartan orbit. -/
theorem bottomCartanSpan_selective (a c : ℕ) (j : Fin 3) (r : ℕ) {v : V}
    (hv : v ∈ bottomCartanSpan ρ w a c) :
    selectiveCartan ρ j r v ∈ bottomCartanSpan ρ w a c := by
  have hblend (u v' t : ℂ) : cartanBlend ρ u v' t r v ∈ bottomCartanSpan ρ w a c := by
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.smul_mem _ u (bottomCartanSpan_rawCartan ρ w a c 2 r hv))
        (Submodule.smul_mem _ v' (bottomCartanSpan_rawCartan ρ w a c 1 r hv)))
      (Submodule.smul_mem _ t (bottomCartanSpan_rawCartan ρ w a c 0 r hv))
  fin_cases j <;> exact hblend _ _ _

/-- Every symmetric bottom mode polynomial lies in the Cartan orbit of the zero-mode vector. -/
theorem bottomSymmetric_evaluation_mem_cartan (m a c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (P : xyzPowerSumAlgebra (bottomModeShape a c)) :
    xyzEvaluation ρ w (bottomModeShape a c) P ∈ bottomCartanSpan ρ w a c := by
  let N := (bottomCartanSpan ρ w a c).comap (xyzEvaluation ρ w (bottomModeShape a c))
  have hsub : xyzPowerSumAlgebra (bottomModeShape a c) ≤
      preservingShiftAlgebra _ (symmetricShiftAction (BottomModeSlot a c)) N := by
    apply Algebra.adjoin_le
    rintro Q ⟨j, r, hj, hr, rfl⟩ U hU
    have hh := bottomCartanSpan_selective ρ w a c
      (if j = 1 then 0 else if j = 4 then 1 else 2) r hU
    rw [xyzEvaluation_psum_intertwine ρ w m h (bottomModeShape a c)
      (bottomModeShape_colours a c) j hj r hr U] at hh
    have hn : (if j = 5 then (1 : ℂ) else 2) ≠ 0 := by split_ifs <;> norm_num
    change xyzEvaluation ρ w (bottomModeShape a c)
      (symmetricShiftAction (BottomModeSlot a c) (colourPsum (bottomModeShape a c) j r) U)
        ∈ bottomCartanSpan ρ w a c
    exact (Submodule.smul_mem_iff (bottomCartanSpan ρ w a c) hn).mp hh
  have hone : (1 : MvPolynomial (BottomModeSlot a c) ℂ) ∈ N := by
    change xyzEvaluation ρ w (bottomModeShape a c) 1 ∈ bottomCartanSpan ρ w a c
    rw [bottomMode_evaluation_one]
    exact Submodule.subset_span ⟨[], rfl⟩
  simpa only [symmetricShiftAction_apply, mul_one] using hsub P.property 1 hone

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.bottomModeShape_centralPowerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomModeShape_adjointPowerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_symmetric_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomAdjoint_symmetric_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomElementaryModes_central
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomElementaryModes_adjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.constantShape_complete_evaluation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_complete_evaluation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomAdjoint_complete_evaluation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomMode_evaluation_one
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_rawCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_selective
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomSymmetric_evaluation_mem_cartan
