import VOA.DeligneAudit.D4LevelReductionCommonRootFlag

/-! The one-letter middle raising evaluator kills both common-root characteristics. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

open Polynomial
open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
variable (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreRelations Q a b c π)

include h

/-- The outer negative-root evaluator satisfies the adjoint characteristic relation. -/
theorem coreOuter_characteristic [FiniteDimensional ℂ V] :
    SL4T.PiCharacteristic (Q.op 6) π (SL4T.rightP (a + b + c) (a + b) a) := by
  have hn (n : ℕ) : SL4T.newtonCoeff (coreAdjointPowerSum a b c) n =
      (-1) ^ n * SL4T.rightE (a + b + c) (a + b) a n :=
    SL4T.newtonCoeff_powerSumOfCoeff a _ (by simp [SL4T.rightE_zero_index]) n
  rw [SL4T.rightP_as_descending, ← funext hn]
  apply SL4T.piCharacteristic_of_highest (coreOuter_currentRelations Q) π
    (coreAdjointPowerSum a b c) (fun s φ => h.parabolic 0 (by decide) (by decide) s φ)
  · intro s hs φ
    simpa [coreCartanSymbol, A3Sector.simpleH] using h.cartan 0 s hs φ
  · intro φ
    apply coreHighest_lowering_nilpotent (coreOuter_currentRelations Q) (π φ) a
      (h.parabolic 0 (by decide) (by decide) 0 φ)
    exact h.weight 0 φ
  · intro n hn'
    rw [hn, SL4T.rightE_eq_zero _ _ _ _ hn', mul_zero]

omit h in
private theorem coreRaising_outerBracket :
    ∀ k : Fin 15, A3Sector.bracketTable 1 6 k = if k = 3 then -1 else 0 := by
  have ht : ∀ k : Fin 15, A3Sector.bracketInt 1 6 k = if k = 3 then -1 else 0 := by
    decide +kernel
  unfold A3Sector.bracketTable
  exact_mod_cast ht

/-- A positive composite-root commutator converts outer lowering into middle raising. -/
theorem coreRaising_from_outer (s : ℕ) (φ : CoreBaseRing a b c) :
    Q.op 1 0 (Q.op 6 s (π φ)) = -Q.op 3 s (π φ) := by
  have hc := Q.comm 1 6 0 s (π φ)
  simp only [coreRaising_outerBracket, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Nat.zero_add, h.parabolic 1 (by decide) (by decide),
    map_zero, sub_zero, neg_one_smul] at hc
  exact hc

/-- The same conversion holds for the entire polynomial evaluator. -/
theorem coreRaising_polynomial_from_outer (P : (CoreBaseRing a b c)[X]) :
    Q.op 1 0 (SL4T.piCurrentMap (Q.op 6) π P) =
      -SL4T.piCurrentMap (Q.op 3) π P := by
  induction P using Polynomial.induction_on' with
  | monomial s φ =>
      simp only [SL4T.piCurrentMap_monomial]
      exact coreRaising_from_outer a b c Q π h s φ
  | add P T hP hT => simp only [map_add, hP, hT, neg_add]

/-- The middle raising evaluator kills all multiples of the adjoint characteristic. -/
theorem coreRaising_adjoint_characteristic [FiniteDimensional ℂ V] :
    SL4T.PiCharacteristic (Q.op 3) π (SL4T.rightP (a + b + c) (a + b) a) := by
  intro φ s
  have he := coreRaising_polynomial_from_outer a b c Q π h
    (Polynomial.C φ * X ^ s * SL4T.rightP (a + b + c) (a + b) a)
  rw [coreOuter_characteristic a b c Q π h φ s, map_zero, eq_neg_iff_add_eq_zero] at he
  simpa using he

omit h

/-- One-variable positional evaluation is the ordinary current polynomial evaluation. -/
theorem coreRaising_single_evaluation (P : MvPolynomial (Fin 1) (CoreBaseRing a b c)) :
    coreRaisingEvaluation Q a b c π 1 P =
      SL4T.piCurrentMap (Q.op 3) π
        (MvPolynomial.uniqueAlgEquiv (CoreBaseRing a b c) (Fin 1) P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u φ =>
      rw [coreRaisingEvaluation, SL4T.positionModeEvaluation_monomial,
        MvPolynomial.uniqueAlgEquiv_monomial, SL4T.piCurrentMap_monomial]
      simp [SL4T.positionModeProduct, List.finRange_succ, List.finRange_zero]
  | add P T hP hT => simp only [map_add, hP, hT]

/-- Complete symmetric polynomials in a single variable are its powers. -/
theorem coreComplete_single_variable {R : Type*} [CommRing R] (n : ℕ) :
    MvPolynomial.hsymm (Fin 1) R n = MvPolynomial.X 0 ^ n := by
  classical
  rw [MvPolynomial.hsymm, Fintype.sum_unique,
    Sym.eq_replicate_of_subsingleton (0 : Fin 1) (default : Sym (Fin 1) n)]
  simp [Sym.replicate]

/-- The first converted complete relation is the complementary characteristic polynomial. -/
theorem coreRaising_complete_characteristic :
    MvPolynomial.uniqueAlgEquiv (CoreBaseRing a b c) (Fin 1)
      (coreRaisingComplete a b c 1 c) = SL4T.leftPbar (a + b + c) (a + b) a := by
  rw [coreRaisingComplete, SL4T.leftPbar_eq_sum]
  have hc : a + b + c - (a + b) = c := by omega
  simp only [hc, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_mul, coreComplete_single_variable, map_pow]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

include h

/-- Converted relations kill every multiple of the complementary characteristic. -/
theorem coreRaising_complement_characteristic :
    SL4T.PiCharacteristic (Q.op 3) π (SL4T.leftPbar (a + b + c) (a + b) a) := by
  intro φ s
  let e := MvPolynomial.uniqueAlgEquiv (CoreBaseRing a b c) (Fin 1)
  have hmem : coreRaisingComplete a b c 1 c ∈ coreRaisingIdeal a b c 1 :=
    Ideal.subset_span ⟨c, by omega, rfl⟩
  have hz := h.converted 1 ((coreRaisingIdeal a b c 1).mul_mem_left
    (e.symm (Polynomial.C φ * X ^ s)) hmem)
  rw [LinearMap.mem_ker, coreRaising_single_evaluation, map_mul,
    AlgEquiv.apply_symm_apply] at hz
  change SL4T.piCurrentMap (Q.op 3) π
    ((Polynomial.C φ * X ^ s) * e (coreRaisingComplete a b c 1 c)) = 0 at hz
  rwa [coreRaising_complete_characteristic] at hz

/-- The one-letter function model kills the full ideal of the two common-root polynomials. -/
theorem coreRaising_commonRootIdeal [FiniteDimensional ℂ V]
    (P : (CoreBaseRing a b c)[X])
    (hP : P ∈ grassmannianCommonRootIdeal (a + b + c) (a + b) a) :
    SL4T.piCurrentMap (Q.op 3) π P = 0 := by
  obtain ⟨U, hU, T, hT, rfl⟩ := Submodule.mem_sup.mp hP
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hU
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hT
  rw [map_add, mul_comm (SL4T.rightP _ _ _), mul_comm (SL4T.leftPbar _ _ _),
    SL4T.PiCharacteristic.mul _ _ (coreRaising_adjoint_characteristic a b c Q π h),
    SL4T.PiCharacteristic.mul _ _ (coreRaising_complement_characteristic a b c Q π h),
    add_zero]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreOuter_characteristic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_from_outer
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_polynomial_from_outer
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_adjoint_characteristic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_single_evaluation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreComplete_single_variable
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_complete_characteristic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_complement_characteristic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaising_commonRootIdeal
