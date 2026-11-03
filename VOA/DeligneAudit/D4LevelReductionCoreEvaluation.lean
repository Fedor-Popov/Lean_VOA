import VOA.DeligneAudit.D4LevelReductionBottomGrassmannian

/-! The core Grassmannian source evaluates in the universal bottom Cartan orbit. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SL4T
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

/-- Complement the first alphabet while retaining the second alphabet. -/
def leftComplementAlphabet : BiSymPoly →ₐ[ℂ] BiSymPoly :=
  MvPolynomial.aeval fun q => if q.1 then MvPolynomial.X q else
    alphabetIn false (complementAlphabet (elementary (q.2 + 1)))

theorem leftComplementAlphabet_left (P : SymPoly) :
    leftComplementAlphabet (alphabetIn false P) = alphabetIn false (complementAlphabet P) := by
  have he : leftComplementAlphabet.comp (alphabetIn false) =
      (alphabetIn false).comp complementAlphabet := by
    ext i : 1
    simp [leftComplementAlphabet, alphabetIn]
  exact AlgHom.congr_fun he P

theorem leftComplementAlphabet_right (P : SymPoly) :
    leftComplementAlphabet (alphabetIn true P) = alphabetIn true P := by
  have he : leftComplementAlphabet.comp (alphabetIn true) = alphabetIn true := by
    ext i : 1
    simp [leftComplementAlphabet, alphabetIn]
  exact AlgHom.congr_fun he P

/-- The first rectangle transposes and the second rectangle is unchanged. -/
theorem leftComplementAlphabet_biGrassIdeal (d T e U : ℕ) :
    biGrassIdeal d T e U ≤ (biGrassIdeal T d e U).comap leftComplementAlphabet := by
  apply sup_le
  · apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change leftComplementAlphabet (alphabetIn false P) ∈ biGrassIdeal T d e U
    rw [leftComplementAlphabet_left]
    exact (show (grassIdeal T d).map (alphabetIn false) ≤ biGrassIdeal T d e U from
      le_sup_left) (Ideal.mem_map_of_mem _ (complementAlphabet_grassIdeal d T hP))
  · apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change leftComplementAlphabet (alphabetIn true P) ∈ biGrassIdeal T d e U
    rw [leftComplementAlphabet_right]
    exact (show (grassIdeal e U).map (alphabetIn true) ≤ biGrassIdeal T d e U from
      le_sup_right) (Ideal.mem_map_of_mem _ hP)

/-- The honest core alphabets map to the actual central and adjoint mode alphabets. -/
def coreGrassmannianToBottom (a b c : ℕ) :
    CoreBaseRing a b c →ₐ[ℂ] BiGrass c (a + b) a (b + c) :=
  Ideal.quotientMapₐ _ leftComplementAlphabet (by
    have hs : a + b + c - (a + b) = c := by omega
    have ht : a + b + c - a = b + c := by omega
    change biGrassIdeal (a + b) (a + b + c - (a + b)) a (a + b + c - a) ≤ _
    rw [hs, ht]
    exact leftComplementAlphabet_biGrassIdeal (a + b) c a (b + c))

theorem coreGrassmannianToBottom_mk (a b c : ℕ) (P : BiSymPoly) :
    coreGrassmannianToBottom a b c (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (leftComplementAlphabet P) := rfl

/-- The core elementary complement evaluates as a signed complete central mode function. -/
theorem coreGrassmannianToBottom_leftElementary (a b c n : ℕ) :
    coreGrassmannianToBottom a b c (leftE (a + b + c) (a + b) a n) =
      (-1) ^ n * Ideal.Quotient.mk _ (alphabetIn false (complete n)) := by
  change Ideal.Quotient.mk _ (leftComplementAlphabet (alphabetIn false (elementary n))) = _
  rw [leftComplementAlphabet_left, complementAlphabet_elementary]
  simp only [map_mul, map_pow, map_neg, map_one]

/-- The core complete complement evaluates as a signed elementary central mode function. -/
theorem coreGrassmannianToBottom_leftComplete (a b c n : ℕ) :
    coreGrassmannianToBottom a b c (leftH (a + b + c) (a + b) a n) =
      (-1) ^ n * Ideal.Quotient.mk _ (alphabetIn false (elementary n)) := by
  change Ideal.Quotient.mk _ (leftComplementAlphabet (alphabetIn false (complete n))) = _
  rw [leftComplementAlphabet_left, complementAlphabet_complete]
  simp only [map_mul, map_pow, map_neg, map_one]

/-- The adjoint elementary alphabet is retained by the core-to-bottom map. -/
theorem coreGrassmannianToBottom_rightElementary (a b c n : ℕ) :
    coreGrassmannianToBottom a b c (rightE (a + b + c) (a + b) a n) =
      Ideal.Quotient.mk _ (alphabetIn true (elementary n)) := by
  change Ideal.Quotient.mk _ (leftComplementAlphabet (alphabetIn true (elementary n))) = _
  rw [leftComplementAlphabet_right]

/-- Complement power sums become negative central power sums at every positive mode. -/
theorem coreGrassmannianToBottom_complementPowerSum (a b c s : ℕ) (hs : 0 < s) :
    coreGrassmannianToBottom a b c (coreComplementPowerSum a b c s) =
      -powerSumOfCoeff c (fun n => (-1) ^ n *
        Ideal.Quotient.mk (biGrassIdeal c (a + b) a (b + c))
          (alphabetIn false (elementary n))) s := by
  rw [coreComplementPowerSum, powerSumOfCoeff_map]
  have he : (fun n => coreGrassmannianToBottom a b c
      ((-1) ^ n * leftE (a + b + c) (a + b) a n)) = fun n =>
        Ideal.Quotient.mk (biGrassIdeal c (a + b) a (b + c))
          (alphabetIn false (complete n)) := by
    funext n
    rw [map_mul, map_pow, map_neg, map_one, coreGrassmannianToBottom_leftElementary,
      ← mul_assoc, ← mul_pow]
    simp
  rw [he]
  exact completeAlphabet_powerSum
    ((Ideal.Quotient.mkₐ ℂ _).comp (alphabetIn false)) (a + b) c s hs

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)
variable (a b c : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))

/-- Evaluation of the honest core ring at the bottom vector of any saturated level piece. -/
def coreGrassmannianEvaluation : CoreBaseRing a b c →ₗ[ℂ]
    TruncatedLevelPiece ρ w (a + b + c) b (2 * a + b) :=
  (bottomGrassmannianEvaluation ρ w a b c h).comp
    (coreGrassmannianToBottom a b c).toLinearMap

theorem coreGrassmannianEvaluation_mk (P : BiSymPoly) :
    coreGrassmannianEvaluation ρ w a b c h (Ideal.Quotient.mk _ P) =
      bottomSymmetricToLevel ρ w a b c h
        (bottomElementaryModes a c (leftComplementAlphabet P)) := rfl

/-- The core-ring image is contained in the actual bottom Cartan image. -/
theorem coreGrassmannianEvaluation_range :
    LinearMap.range (coreGrassmannianEvaluation ρ w a b c h) ≤
      LinearMap.range (bottomCartanToLevel ρ w a b c h) := by
  rintro v ⟨P, rfl⟩
  exact bottomGrassmannianEvaluation_range ρ w a b c h
    (LinearMap.mem_range_self (bottomGrassmannianEvaluation ρ w a b c h)
      (coreGrassmannianToBottom a b c P))

/-- The core-ring evaluation on the universal level module for every nonnegative triple. -/
def universalCoreEvaluation (a b c : ℕ) : CoreBaseRing a b c →ₗ[ℂ] UniversalCorePiece a b c :=
  coreGrassmannianEvaluation (demazureCurrent (a + b + c)) (demazureGenerator (a + b + c))
    a b c (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0))

/-- The unit of the honest Grassmannian pair evaluates to the prescribed bottom vector. -/
theorem universalCoreEvaluation_one (a b c : ℕ) :
    universalCoreEvaluation a b c 1 = universalCoreBottom a b c := by
  rw [show (1 : CoreBaseRing a b c) = Ideal.Quotient.mk _ 1 from rfl]
  unfold universalCoreEvaluation
  rw [coreGrassmannianEvaluation_mk, map_one, map_one]
  apply congrArg (universalBottomCartanMap a b c)
  apply Subtype.ext
  exact bottomMode_evaluation_one _ _ a c

theorem universalCoreEvaluation_range (a b c : ℕ) :
    LinearMap.range (universalCoreEvaluation a b c) ≤
      LinearMap.range (universalBottomCartanMap a b c) :=
  coreGrassmannianEvaluation_range _ _ a b c _

/-- Every vector evaluated from the honest pair satisfies the positive parabolic relations. -/
theorem universalCoreEvaluation_parabolic (a b c : ℕ) (e : Fin 15)
    (he : e.val < 6) (hne : e ≠ 3) (r : ℕ) (P : CoreBaseRing a b c) :
    (universalCoreCurrent a b c).op e r (universalCoreEvaluation a b c P) = 0 := by
  obtain ⟨v, hv⟩ := universalCoreEvaluation_range a b c
    (LinearMap.mem_range_self (universalCoreEvaluation a b c) P)
  rw [← hv]
  exact universalBottomCartan_parabolic_annihilation a b c v e he hne r

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.leftComplementAlphabet_left
#print axioms VOA.DeligneAudit.D4LevelReduction.leftComplementAlphabet_right
#print axioms VOA.DeligneAudit.D4LevelReduction.leftComplementAlphabet_biGrassIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_mk
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_leftElementary
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_leftComplete
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_rightElementary
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_complementPowerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_mk
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_range
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_one
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_range
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_parabolic
