import VOA.Huang.GenusTwoPointSepEnergyWitt
import VOA.Moonshine.VnatAxiomsVir

/-!
# Energy conjugation reduced to one universal scalar identity

The commutator calculation, local finiteness, and evaluation of the actual
exponentials are discharged here. The remaining identity is entirely scalar:
it compares the exponential of the Witt adjoint action with Zhu's coefficients.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The universal scalar coefficient identity required by energy conjugation.
No module, state, or trace predicate occurs in this statement. -/
def LogarithmicEnergyCoefficients : Prop :=
  ∀ n : ℕ, energyExpCoeff (iterativeLog (logarithmicCoordinate 1)) n =
    sqBracketCoeffZ 2 1 ((n + 1 : ℕ) : ℤ)

/-- Nonnegative Virasoro modes act pointwise finitely on the state space. -/
theorem stateEnergy_support_finite (W : VertexOperatorAlgebra V) (x : V) :
    (Function.support (fun n : ℕ => W.L (n : ℤ) x)).Finite := by
  obtain ⟨K, hK⟩ := W.regularity W.conformalVector x
  refine (Set.finite_Iio K.toNat).subset fun n hn => ?_
  simp only [Function.mem_support, Set.mem_Iio] at *
  by_contra h
  exact hn (by rw [VertexOperatorAlgebra.L_def, hK _ (by omega)])

/-- The central term vanishes on the nonnegative Virasoro subalgebra,
including the boundary i = j = 0. -/
theorem stateEnergy_comm (W : VertexOperatorAlgebra V) (i j : ℕ) (x : V) :
    W.L (i : ℤ) (W.L (j : ℤ) x) - W.L (j : ℤ) (W.L (i : ℤ) x) =
      ((i : ℂ) - j) • W.L ((i + j : ℕ) : ℤ) x := by
  have h := L_virasoro_apply W (i : ℤ) (j : ℤ) x
  by_cases hij : (i : ℤ) + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i; subst j
    simp
  · simpa only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      Nat.cast_add, Int.cast_natCast, if_neg hij, add_zero] using h

/-- The abstract Witt action is exactly the implemented negative generator. -/
theorem stateEnergy_generator (a : ℕ → ℂ) :
    energyWittAction (fun n : ℕ => W.L (n : ℤ)) (stateEnergy_support_finite W)
      (energyGenerator a) = -coordGen W a := by
  ext x
  rw [energyWittAction_apply, finsum_nat_succ _
    ((stateEnergy_support_finite W x).subset (fun n hn hz => hn (by
      simp only [hz, smul_zero])))]
  simp only [energyGenerator, zero_smul, zero_add, Nat.cast_add, Nat.cast_one,
    neg_smul, finsum_neg_distrib, LinearMap.neg_apply, coordGen_apply]

/-- Exact state energy conjugation by the actual normalized exponential. -/
theorem normalizedState_energy_expansion (x : V) :
    normalizedStateChange W (W.L 0 ((normalizedStateChange W).symm x)) =
      ∑ᶠ n : ℕ, energyExpCoeff (iterativeLog (logarithmicCoordinate 1)) n •
        W.L (n : ℤ) x := by
  let a := iterativeLog (logarithmicCoordinate 1)
  have he := stateEnergy_generator (W := W) a
  have hd : IsLocNilp (energyWittAction (fun n : ℕ => W.L (n : ℤ))
      (stateEnergy_support_finite W) (energyGenerator a)) := by
    rw [he]
    exact (coordGen_isLocNilp W a).neg
  have h := energy_conjugation_eq _ (stateEnergy_support_finite W)
    (stateEnergy_comm W) a hd x
  have hinv : (normalizedStateChange W).symm x = expFun (coordGen_isLocNilp W a) x := by
    apply (normalizedStateChange W).injective
    rw [LinearEquiv.apply_symm_apply, normalizedStateChange_exp]
    exact (expFun_neg_cancel' (coordGen_isLocNilp W a) x).symm
  rw [normalizedStateChange_exp, hinv]
  simpa only [he, neg_neg, energyWittAction_apply] using h

/-- The state zero-mode law consumes only the scalar coefficient identity. -/
theorem normalizedStateZeroConjugation_of_energyCoefficients
    (h : LogarithmicEnergyCoefficients) : NormalizedStateZeroConjugation W := by
  intro x
  have he := normalizedState_energy_expansion (W := W) (normalizedStateChange W x)
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [Lsq_zero_eq_nat_finsum]
  exact (he.trans (finsum_congr (fun n => by rw [h n]))).symm

/-- Nonnegative Virasoro modes act pointwise finitely on every lowest-weight module. -/
theorem moduleEnergy_support_finite (P : LWModule W) (x : P.carrier) :
    (Function.support (fun n : ℕ => SquareModule.roundL P.isMod (n : ℤ) x)).Finite := by
  obtain ⟨K, hK⟩ := P.isMod.truncation W.conformalVector x
  refine (Set.finite_Iio K.toNat).subset fun n hn => ?_
  simp only [Function.mem_support, Set.mem_Iio] at *
  by_contra h
  exact hn (hK _ (by omega))

/-- The same Witt relation on a module; the full module Virasoro theorem
supplies the central term before its nonnegative-index specialization. -/
theorem moduleEnergy_comm (P : LWModule W) (i j : ℕ) (x : P.carrier) :
    SquareModule.roundL P.isMod i (SquareModule.roundL P.isMod j x) -
      SquareModule.roundL P.isMod j (SquareModule.roundL P.isMod i x) =
      ((i : ℂ) - j) • SquareModule.roundL P.isMod ((i + j : ℕ) : ℤ) x := by
  have h := congrArg (fun f : Module.End ℂ P.carrier => f x)
    (Moonshine.VnatAxioms.module_virasoro P.isMod.toWeakModule (i : ℤ) (j : ℤ))
  by_cases hij : (i : ℤ) + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i; subst j
    simp
  · simpa only [SquareModule.roundL, Ring.lie_def, LinearMap.sub_apply,
      Module.End.mul_apply, Nat.cast_add, Int.cast_natCast, if_neg hij, add_zero,
      LinearMap.smul_apply] using h

theorem moduleEnergy_generator (P : LWModule W) (a : ℕ → ℂ) :
    energyWittAction (fun n : ℕ => SquareModule.roundL P.isMod n)
      (moduleEnergy_support_finite P) (energyGenerator a) = -moduleCoordGen P a := by
  ext x
  rw [energyWittAction_apply, finsum_nat_succ _
    ((moduleEnergy_support_finite P x).subset (fun n hn hz => hn (by
      simp only [hz, smul_zero])))]
  simp only [energyGenerator, zero_smul, zero_add, Nat.cast_add, Nat.cast_one,
    neg_smul, finsum_neg_distrib, LinearMap.neg_apply, SquareModule.roundL,
    moduleCoordGen, add_assoc, show (1 + 1 : ℤ) = 2 from rfl]
  rfl

/-- Exact module energy conjugation, with all operator obligations discharged. -/
theorem normalizedModule_energy_expansion (P : LWModule W) (x : P.carrier) :
    normalizedCoordinateChange P (mode (P.isMod.YM W.conformalVector) 1
      ((normalizedCoordinateChange P).symm x)) =
      ∑ᶠ n : ℕ, energyExpCoeff (iterativeLog (logarithmicCoordinate 1)) n •
        SquareModule.roundL P.isMod n x := by
  let a := iterativeLog (logarithmicCoordinate 1)
  have he := moduleEnergy_generator P a
  have hd : IsLocNilp (energyWittAction (fun n : ℕ => SquareModule.roundL P.isMod n)
      (moduleEnergy_support_finite P) (energyGenerator a)) := by
    rw [he]
    exact (moduleCoordGen_isLocNilp P a).neg
  have h := energy_conjugation_eq _ (moduleEnergy_support_finite P)
    (moduleEnergy_comm P) a hd x
  change expFun (moduleCoordGen_isLocNilp P a).neg
    (mode (P.isMod.YM W.conformalVector) 1
      (expFun (moduleCoordGen_isLocNilp P a).neg.neg x)) = _
  simp only [he, neg_neg, energyWittAction_apply] at h
  simp only [neg_neg]
  exact h

/-- The module zero-mode law consumes the very same universal scalar identity. -/
theorem normalizedModuleZeroConjugation_of_energyCoefficients (P : LWModule W)
    (h : LogarithmicEnergyCoefficients) : NormalizedModuleZeroConjugation P := by
  intro x
  have he := normalizedModule_energy_expansion P (normalizedCoordinateChange P x)
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [SquareModule.Lsq_zero_eq_nat_finsum]
  exact (he.trans (finsum_congr (fun n => by rw [h n]))).symm

/-- The all-mode target, reduced to a module-independent scalar calculation. -/
theorem normalizedSquareConjugation_of_energyCoefficients (P : LWModule W)
    (h : LogarithmicEnergyCoefficients) : NormalizedSquareConjugation P :=
  normalizedSquareConjugation_of_zero P
    (normalizedStateZeroConjugation_of_energyCoefficients h)
    (normalizedModuleZeroConjugation_of_energyCoefficients P h)

end VOA.Huang.GenusTwoPoint.Separate
