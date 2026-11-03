import VOA.DeligneAudit.D4LevelCoreModuleAudit
import VOA.DeligneAudit.SL4TNewtonSeries

/-! Complementation of the Grassmannian alphabet used by the bottom Cartan orbit. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SL4T

/-- The elementary coefficients of the complementary alphabet are signed complete functions. -/
def complementAlphabet : SymPoly →ₐ[ℂ] SymPoly :=
  MvPolynomial.aeval fun i => (-1) ^ (i + 1) * complete (i + 1)

theorem complementAlphabet_elementary (n : ℕ) :
    complementAlphabet (elementary n) = (-1) ^ n * complete n := by
  cases n <;> simp [complementAlphabet]

/-- Complementation exchanges the complete coefficients with signed elementary coefficients. -/
theorem complementAlphabet_complete (n : ℕ) :
    complementAlphabet (complete n) = (-1) ^ n * elementary n := by
  let E : PowerSeries SymPoly := PowerSeries.mk (fun k => (-1) ^ k * elementary k)
  let H : PowerSeries SymPoly := PowerSeries.mk complete
  let K : PowerSeries SymPoly := PowerSeries.mk (fun k => complementAlphabet (complete k))
  have hEH : E * H = 1 := specializedElementary_complete_inverse (AlgHom.id ℂ SymPoly)
  have hHK : H * K = 1 := by
    have h := specializedElementary_complete_inverse complementAlphabet
    have he : PowerSeries.mk (fun k => (-1) ^ k * complementAlphabet (elementary k)) = H := by
      ext k : 1
      simp only [PowerSeries.coeff_mk, H, complementAlphabet_elementary]
      rw [← mul_assoc, ← mul_pow]
      simp
    rwa [he] at h
  have hKE : K = E := by
    calc
      K = (E * H) * K := by rw [hEH, one_mul]
      _ = E := by rw [mul_assoc, hHK, mul_one]
  simpa only [K, E, PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff n) hKE

/-- Applying alphabet complementation twice recovers every symmetric polynomial. -/
theorem complementAlphabet_involutive : Function.Involutive complementAlphabet := by
  have he : complementAlphabet.comp complementAlphabet = AlgHom.id ℂ SymPoly := by
    ext i : 1
    change complementAlphabet (complementAlphabet (elementary (i + 1))) = elementary (i + 1)
    rw [complementAlphabet_elementary, map_mul, map_pow, map_neg, map_one,
      complementAlphabet_complete, ← mul_assoc, ← mul_pow]
    simp
  intro P
  exact AlgHom.congr_fun he P

/-- The two rectangle tails are exchanged by alphabet complementation. -/
theorem complementAlphabet_grassIdeal (d T : ℕ) :
    grassIdeal d T ≤ (grassIdeal T d).comap complementAlphabet := by
  apply sup_le
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro n hn
    change complementAlphabet (elementary n) ∈ grassIdeal T d
    rw [complementAlphabet_elementary]
    exact Ideal.mul_mem_left _ _
      ((show tailIdeal complete d ≤ grassIdeal T d from le_sup_right)
        (mem_tailIdeal complete hn))
  · apply (tailIdeal_le_iff _ _ _).mpr
    intro n hn
    change complementAlphabet (complete n) ∈ grassIdeal T d
    rw [complementAlphabet_complete]
    exact Ideal.mul_mem_left _ _
      ((show tailIdeal elementary T ≤ grassIdeal T d from le_sup_left)
        (mem_tailIdeal elementary hn))

/-- Complementation descends to the two transposed Grassmannian rectangles. -/
def grassmannianComplement (d T : ℕ) : GrassRing d T →ₐ[ℂ] GrassRing T d :=
  Ideal.quotientMapₐ _ complementAlphabet (complementAlphabet_grassIdeal d T)

theorem grassmannianComplement_elementary (d T n : ℕ) :
    grassmannianComplement d T (eClass d T n) = (-1) ^ n * hClass T d n := by
  change Ideal.Quotient.mk _ (complementAlphabet (elementary n)) = _
  rw [complementAlphabet_elementary, map_mul, map_pow, map_neg, map_one]
  rfl

theorem grassmannianComplement_complete (d T n : ℕ) :
    grassmannianComplement d T (hClass d T n) = (-1) ^ n * eClass T d n := by
  change Ideal.Quotient.mk _ (complementAlphabet (complete n)) = _
  rw [complementAlphabet_complete, map_mul, map_pow, map_neg, map_one]
  rfl

/-- The complementary Grassmannian maps are mutually inverse for arbitrary rectangles. -/
theorem grassmannianComplement_inverse (d T : ℕ) (P : GrassRing d T) :
    grassmannianComplement T d (grassmannianComplement d T P) = P := by
  induction P using Quotient.inductionOn' with
  | h P =>
      change Ideal.Quotient.mk _ (complementAlphabet (complementAlphabet P)) = _
      rw [complementAlphabet_involutive]
      rfl

/-- Positive power sums of a complete-function complement are the negative original power sums. -/
theorem completeAlphabet_powerSum {R : Type*} [CommRing R] [Algebra ℂ R]
    (φ : SymPoly →ₐ[ℂ] R) (d e s : ℕ) (hs : 0 < s) :
    powerSumOfCoeff d (fun n => φ (complete n)) s =
      -powerSumOfCoeff e (fun n => (-1) ^ n * φ (elementary n)) s := by
  let p := powerSumOfCoeff e (fun n => (-1) ^ n * φ (elementary n))
  have he : newtonCoefficientSeries (fun r => -p r) =
      PowerSeries.mk (fun n => φ (complete n)) := by
    apply newtonCoefficientSeries_neg_of_inverse
    rw [newtonCoefficientSeries_elementary]
    exact specializedElementary_complete_inverse φ
  have hc : newtonCoeff (fun r => -p r) = fun n => φ (complete n) := by
    funext n
    simpa only [newtonCoefficientSeries, PowerSeries.coeff_mk] using
      congrArg (PowerSeries.coeff n) he
  rw [← hc]
  exact powerSumOfCoeff_newtonCoeff d (fun r => -p r) s hs

/-- The complement map realizes the required negative sign on every positive power sum. -/
theorem grassmannianComplement_powerSum (d T s : ℕ) (hs : 0 < s) :
    grassmannianComplement d T
        (powerSumOfCoeff d (fun n => (-1) ^ n * eClass d T n) s) =
      -powerSumOfCoeff T (fun n => (-1) ^ n * eClass T d n) s := by
  rw [powerSumOfCoeff_map]
  have he : (fun n => grassmannianComplement d T ((-1) ^ n * eClass d T n)) =
      fun n => hClass T d n := by
    funext n
    rw [map_mul, map_pow, map_neg, map_one, grassmannianComplement_elementary,
      ← mul_assoc, ← mul_pow]
    simp
  rw [he]
  exact completeAlphabet_powerSum (Ideal.Quotient.mkₐ ℂ (grassIdeal T d)) d T s hs

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.complementAlphabet_elementary
#print axioms VOA.DeligneAudit.D4LevelReduction.complementAlphabet_complete
#print axioms VOA.DeligneAudit.D4LevelReduction.complementAlphabet_involutive
#print axioms VOA.DeligneAudit.D4LevelReduction.complementAlphabet_grassIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.grassmannianComplement_elementary
#print axioms VOA.DeligneAudit.D4LevelReduction.grassmannianComplement_complete
#print axioms VOA.DeligneAudit.D4LevelReduction.grassmannianComplement_inverse
#print axioms VOA.DeligneAudit.D4LevelReduction.completeAlphabet_powerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.grassmannianComplement_powerSum
