import VOA.DeligneAudit.D4FusionContactAllMCountResearchRefinedEnergy
import VOA.DeligneAudit.D4FusionContactAllMCountResearchSeries

/-! # Whole current coefficients of checked constant-color quadratics

Both modes of the checked two-mode polynomial are sent to the full
color current. Constant Levi derivations commute with this evaluation
and with whole coefficient extraction. No monomial seed is substituted.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate

noncomputable section

def colorCurrentAlg (m : ℕ) : MvPolynomial (Vars 2) ℂ →ₐ[ℂ]
    PowerSeries (MvPolynomial (Vars m) ℂ) :=
  MvPolynomial.aeval fun x => Polynomial.AllM.current m x.1

@[simp] theorem colorCurrentAlg_X (m : ℕ) (x : Vars 2) :
    colorCurrentAlg m (MvPolynomial.X x) = Polynomial.AllM.current m x.1 :=
  MvPolynomial.aeval_X _ _

theorem constant_modeX (m : ℕ) (g : Fin 10) (i : Fin 9) (r : ℕ) :
    g0Deriv m g 0 (modeX m i r) =
      ∑ j : Fin 9, contactF (zeroIndex g) (radIndex i) (radIndex j) • modeX m j r := by
  by_cases hr : r < m
  · simp [modeX,hr,g0Deriv,g0Image]
  · simp only [modeX,dif_neg hr,map_zero,smul_zero,Finset.sum_const_zero]

theorem colorCurrentAlg_deriv_X (m : ℕ) (g : Fin 10) (x : Vars 2) :
    colorCurrentAlg m (g0Deriv 2 g 0 (MvPolynomial.X x)) =
      seriesDerivation (g0Deriv m g 0) (colorCurrentAlg m (MvPolynomial.X x)) := by
  apply PowerSeries.ext
  intro r
  simp only [g0Deriv_X_constant,map_sum,map_smul,colorCurrentAlg_X,
    seriesDerivation_coeff,Polynomial.AllM.current,PowerSeries.coeff_smul,
    PowerSeries.coeff_mk,constant_modeX]

theorem colorCurrentAlg_deriv (m : ℕ) (g : Fin 10) (p : MvPolynomial (Vars 2) ℂ) :
    colorCurrentAlg m (g0Deriv 2 g 0 p) =
      seriesDerivation (g0Deriv m g 0) (colorCurrentAlg m p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.derivation_C,map_zero]
      simpa only [colorCurrentAlg,MvPolynomial.aeval_C] using
        ((seriesDerivation (g0Deriv m g 0)).map_algebraMap c).symm
  | add p q ihp ihq => simp only [map_add,ihp,ihq]
  | mul_X p x ih =>
      rw [(g0Deriv 2 g 0).leibniz,
        map_mul (colorCurrentAlg m) p (MvPolynomial.X x),
        (seriesDerivation (g0Deriv m g 0)).leibniz]
      simp only [smul_eq_mul,map_add,map_mul,ih,colorCurrentAlg_deriv_X]

/-- The coefficient is kept whole under the actual constant current derivation. -/
theorem constant_deriv_coefficient (m : ℕ) (g : Fin 10) (s : ℕ)
    (p : MvPolynomial (Vars 2) ℂ) :
    g0Deriv m g 0 (PowerSeries.coeff s (colorCurrentAlg m p)) =
      PowerSeries.coeff s (colorCurrentAlg m (g0Deriv 2 g 0 p)) := by
  rw [colorCurrentAlg_deriv,seriesDerivation_coeff]

theorem colorCurrentAlg_twoSeed (m : ℕ) :
    colorCurrentAlg m twoSeed = Polynomial.AllM.current m 0 ^ 2 := by
  simp only [twoSeed,map_mul,colorCurrentAlg_X,pow_two]

theorem twoEvalMap_levi_step (i : Fin 3) (e : IntegerExpr)
    (p : MvPolynomial (Vars 2) ℂ) :
    twoEvalMap (.deriv (leviIndex i) e.toWheel) p =
      g0Deriv 2 (leviCurrent i) 0 (twoEvalMap e.toWheel p) := by
  fin_cases i <;>
    simp [twoEvalMap,leviIndex,leviCurrent,derivationIndex,Polynomial.candidateDeriv]

variable {m : ℕ} (b : BoundaryPair m)

/-- The actual constant-Levi orbit of the whole grouped seed is the
whole coefficient of the already checked two-mode color polynomial. -/
theorem leviOrbit_grouped_coefficient (l : List (Fin 3)) :
    evalMap b (leviOrbit l .base).toWheel (groupedSeed b) =
      (1/2:ℂ) • PowerSeries.coeff (b.lower.val+b.top.val)
        (colorCurrentAlg m (twoEvalMap (leviOrbit l .base).toWheel twoSeed)) := by
  induction l with
  | nil =>
      change groupedSeed b = (1/2:ℂ) • PowerSeries.coeff _ (colorCurrentAlg m twoSeed)
      rw [colorCurrentAlg_twoSeed,groupedSeed_whole]
  | cons i l ih =>
      change evalMap b (.deriv (leviIndex i) (leviOrbit l .base).toWheel) (groupedSeed b) = _
      rw [evalMap_levi_step,ih,Derivation.map_smul,constant_deriv_coefficient]
      congr 2
      exact congrArg (fun p => colorCurrentAlg m p) (twoEvalMap_levi_step i _ twoSeed).symm

end

#print axioms colorCurrentAlg_deriv
#print axioms leviOrbit_grouped_coefficient

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
