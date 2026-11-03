import VOA.DeligneAudit.D4LeviKSPairHeight
import VOA.DeligneAudit.D4LeviKSPowerSums

/-! Symmetric mode shifts on a fixed number of labelled letters. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable (σ : Type*)

/-- A mode assignment for exactly the letters indexed by `σ`. -/
noncomputable def modeMonomial (a : σ →₀ ℕ) : MvPolynomial σ ℂ :=
  monomial a 1

/-- A polynomial acts on mode words by multiplication. -/
noncomputable def symmetricShiftAction :
    MvPolynomial σ ℂ →ₐ[ℂ] Module.End ℂ (MvPolynomial σ ℂ) :=
  Algebra.lmul ℂ (MvPolynomial σ ℂ)

theorem symmetricShiftAction_apply (P Q : MvPolynomial σ ℂ) :
    symmetricShiftAction σ P Q = P * Q := rfl

/-- Shift operators multiply by composition in the same order. -/
theorem symmetricShiftAction_mul (P Q W : MvPolynomial σ ℂ) :
    symmetricShiftAction σ (P * Q) W =
      symmetricShiftAction σ P (symmetricShiftAction σ Q W) := by
  simp [symmetricShiftAction_apply]

/-- A power sum shifts one of the labelled letters by `r` modes. -/
theorem symmetricShiftAction_psum [Fintype σ] (r : ℕ) (a : σ →₀ ℕ) :
    symmetricShiftAction σ (psum σ ℂ r) (modeMonomial σ a) =
      ∑ i : σ, modeMonomial σ (Finsupp.single i r + a) := by
  simp [symmetricShiftAction_apply, modeMonomial, psum,
    X_pow_eq_monomial, monomial_mul]

/-- Closure under all power-sum shifts implies closure under every symmetric
    shift polynomial in this fixed-length word model. -/
theorem symmetricShiftAction_preserves
    [Fintype σ]
    (N : Submodule ℂ (MvPolynomial σ ℂ))
    (hpower : ∀ r : ℕ, ∀ W ∈ N,
      symmetricShiftAction σ (psum σ ℂ r) W ∈ N)
    (P : MvPolynomial σ ℂ) (hP : P ∈ symmetricSubalgebra σ ℂ)
    (W : MvPolynomial σ ℂ) (hW : W ∈ N) :
    symmetricShiftAction σ P W ∈ N := by
  exact symmetric_shift_preserves σ (MvPolynomial σ ℂ)
    (AlgHom.id ℂ (MvPolynomial σ ℂ))
    (symmetricShiftAction σ) N (by simpa using hpower) P hP W hW

/-- Evaluate a mode polynomial by assigning a vector to each mode word. -/
noncomputable def modeWordEvaluation
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : (σ →₀ ℕ) → V) : MvPolynomial σ ℂ →ₗ[ℂ] V :=
  Finsupp.lsum ℂ fun a =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ V).symm (f a)

theorem modeWordEvaluation_monomial
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : (σ →₀ ℕ) → V) (a : σ →₀ ℕ) :
    modeWordEvaluation σ f (modeMonomial σ a) = f a := by
  change (Finsupp.lsum ℂ fun b =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ V).symm (f b))
      (Finsupp.single a 1) = f a
  rw [Finsupp.lsum_single]
  simp

/-- A linear word evaluator transfers symmetric-shift closure from the
    polynomial word model to any target submodule. -/
theorem symmetricShiftAction_evaluation_mem
    [Fintype σ]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : (σ →₀ ℕ) → V) (N : Submodule ℂ V)
    (hpower : ∀ r : ℕ, ∀ W : MvPolynomial σ ℂ,
      modeWordEvaluation σ f W ∈ N →
        modeWordEvaluation σ f
          (symmetricShiftAction σ (psum σ ℂ r) W) ∈ N)
    (P : MvPolynomial σ ℂ) (hP : P ∈ symmetricSubalgebra σ ℂ)
    (W : MvPolynomial σ ℂ)
    (hW : modeWordEvaluation σ f W ∈ N) :
    modeWordEvaluation σ f (symmetricShiftAction σ P W) ∈ N := by
  let M := N.comap (modeWordEvaluation σ f)
  have hm : ∀ r : ℕ, ∀ U ∈ M,
      symmetricShiftAction σ (psum σ ℂ r) U ∈ M := by
    intro r U hU
    exact hpower r U hU
  exact symmetricShiftAction_preserves σ M hm P hP W hW

/-- An ordered fixed-colour radical word with `n` labelled modes. -/
def fixedColourModes (n : ℕ) (j : Fin 6) (a : Fin n →₀ ℕ) :
    List (Fin 6 × ℕ) :=
  (List.finRange n).map fun i => (j, a i)

/-- The linear evaluation of a mode polynomial as D4 radical words. -/
noncomputable def fixedColourEvaluation
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (n : ℕ) (j : Fin 6) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] V :=
  modeWordEvaluation (Fin n) fun a => radicalWord ρ w (fixedColourModes n j a)

theorem fixedColourEvaluation_monomial
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (n : ℕ) (j : Fin 6) (a : Fin n →₀ ℕ) :
    fixedColourEvaluation ρ w n j (modeMonomial (Fin n) a) =
      radicalWord ρ w (fixedColourModes n j a) := by
  exact modeWordEvaluation_monomial (Fin n) _ a

/-- The power sum on fixed-colour D4 words is the sum of single-letter
    shifts at the positions indexed by `Fin n`. -/
theorem fixedColourEvaluation_psum
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (n : ℕ) (j : Fin 6) (r : ℕ) (a : Fin n →₀ ℕ) :
    fixedColourEvaluation ρ w n j
        (symmetricShiftAction (Fin n) (psum (Fin n) ℂ r)
          (modeMonomial (Fin n) a)) =
      ∑ i : Fin n,
        radicalWord ρ w (fixedColourModes n j (Finsupp.single i r + a)) := by
  rw [symmetricShiftAction_psum]
  simp only [map_sum, fixedColourEvaluation_monomial]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.symmetricShiftAction_apply
#print axioms VOA.DeligneAudit.D4Levi.symmetricShiftAction_mul
#print axioms VOA.DeligneAudit.D4Levi.symmetricShiftAction_psum
#print axioms VOA.DeligneAudit.D4Levi.symmetricShiftAction_preserves
#print axioms VOA.DeligneAudit.D4Levi.modeWordEvaluation_monomial
#print axioms VOA.DeligneAudit.D4Levi.symmetricShiftAction_evaluation_mem
#print axioms VOA.DeligneAudit.D4Levi.fixedColourEvaluation_monomial
#print axioms VOA.DeligneAudit.D4Levi.fixedColourEvaluation_psum
