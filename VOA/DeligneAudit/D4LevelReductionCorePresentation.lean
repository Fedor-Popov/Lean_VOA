import VOA.DeligneAudit.D4LevelReductionBottomCartan
import VOA.DeligneAudit.SL4TDoubledSiteRankAudit

/-!
The precise core-module bound and its interface with the universal level piece.
The presentation of the universal piece by the two Grassmannian alphabets is an
explicit residual proposition. The final implication in this module is conditional
on that presentation and on the core rank bound; neither input is asserted here.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

noncomputable section

/-- The two independent Grassmannian alphabets for a bottom level. -/
abbrev CoreBaseRing (a b c : ℕ) := SL4T.S (a + b + c) (a + b) a

/-- The power sums of the complement alphabet. -/
def coreComplementPowerSum (a b c s : ℕ) : CoreBaseRing a b c :=
  SL4T.powerSumOfCoeff (a + b) (fun j => (-1) ^ j * SL4T.leftE (a + b + c) (a + b) a j) s

/-- The power sums of the adjoint-letter alphabet. -/
def coreAdjointPowerSum (a b c s : ℕ) : CoreBaseRing a b c :=
  SL4T.powerSumOfCoeff a (fun j => (-1) ^ j * SL4T.rightE (a + b + c) (a + b) a j) s

/-- The three semisimple Cartan symbols in the two-alphabet ring. -/
def coreCartanSymbol (a b c : ℕ) (i : Fin 3) (s : ℕ) : CoreBaseRing a b c :=
  if i = 1 then coreComplementPowerSum a b c s - coreAdjointPowerSum a b c s
    else coreAdjointPowerSum a b c s

/-- A complete function in the union of the complement and raising-mode alphabets. -/
def coreRaisingComplete (a b c j n : ℕ) : MvPolynomial (Fin j) (CoreBaseRing a b c) :=
  ∑ i ∈ Finset.range (n + 1),
    MvPolynomial.C (SL4T.leftH (a + b + c) (a + b) a i) *
      MvPolynomial.hsymm (Fin j) (CoreBaseRing a b c) (n - i)

/-- The converted complete-function ideal, including the constant relation when overfull. -/
def coreRaisingIdeal (a b c j : ℕ) : Ideal (MvPolynomial (Fin j) (CoreBaseRing a b c)) :=
  Ideal.span {P | ∃ n, c < j + n ∧ P = coreRaisingComplete a b c j n}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- An ordered middle-root raising word evaluates the mode exponents of a polynomial. -/
def coreRaisingEvaluation (Q : CurrentModule A3Sector.bracketTable V)
    (a b c : ℕ) (π : CoreBaseRing a b c →ₗ[ℂ] V) (j : ℕ) :
    MvPolynomial (Fin j) (CoreBaseRing a b c) →ₗ[ℂ] V :=
  SL4T.positionModeEvaluation (fun _ s => Q.op 3 s) (List.finRange j) π

/-- The positive Cartan currents act through the two Grassmannian power-sum alphabets. -/
def CoreCartanAction (Q : CurrentModule A3Sector.bracketTable V)
    (a b c : ℕ) (π : CoreBaseRing a b c →ₗ[ℂ] V) : Prop :=
  ∀ i s, 0 < s → ∀ φ, Q.op (A3Sector.simpleH i) s (π φ) =
    π (coreCartanSymbol a b c i s * φ)

/-- Every middle-root raising evaluator kills the full converted complete-function ideal. -/
def CoreConvertedRelations (Q : CurrentModule A3Sector.bracketTable V)
    (a b c : ℕ) (π : CoreBaseRing a b c →ₗ[ℂ] V) : Prop :=
  ∀ j, (coreRaisingIdeal a b c j).restrictScalars ℂ ≤
    LinearMap.ker (coreRaisingEvaluation Q a b c π j)

/-- The parabolic, Cartan, and converted relations defining the truncated core problem. -/
structure CoreRelations (Q : CurrentModule A3Sector.bracketTable V)
    (a b c : ℕ) (π : CoreBaseRing a b c →ₗ[ℂ] V) : Prop where
  parabolic : ∀ e : Fin 15, e.val < 6 → e ≠ 3 → ∀ r φ, Q.op e r (π φ) = 0
  weight : ∀ i φ, Q.op (A3Sector.simpleH i) 0 (π φ) =
    (A3Sector.weightABC a b a i : ℂ) • π φ
  cartan : CoreCartanAction Q a b c π
  converted : CoreConvertedRelations Q a b c π

/-- The remaining finite-dimensional core estimate with all currents truncated at the site count. -/
def TruncatedCoreRankBound (a b c : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V),
    CoreRelations Q a b c π → cycSubG Q (π 1) = ⊤ →
    (∀ e r, a + b + c ≤ r → Q.op e r = 0) →
    Module.finrank ℂ V ≤ levelTarget (a + b + c) b (2 * a + b)

/-- Overfull raising words impose the constant polynomial relation. -/
theorem coreRaisingIdeal_eq_top_of_overfull (a b c j : ℕ) (hj : c < j) :
    coreRaisingIdeal a b c j = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  refine ⟨0, by omega, ?_⟩
  simp [coreRaisingComplete, SL4T.leftH, SL4T.hClass]

/-- The converted ideal condition kills every raising word longer than the central count. -/
theorem coreRaisingEvaluation_zero_of_overfull
    (Q : CurrentModule A3Sector.bracketTable V) (a b c : ℕ)
    (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreConvertedRelations Q a b c π)
    (j : ℕ) (hj : c < j) : coreRaisingEvaluation Q a b c π j = 0 := by
  apply LinearMap.ext
  intro P
  apply h j
  rw [coreRaisingIdeal_eq_top_of_overfull a b c j hj]
  trivial

variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The actual level coinvariant has zero high Levi currents as operators. -/
theorem levelCoinvariantCurrent_high (m : ℕ) (κ p : ℤ) (e : Fin 15) (r : ℕ)
    (hr : m ≤ r) : (levelCoinvariantCurrent ρ w m κ p).op e r = 0 := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change (leviSign e : ℂ) • ρ.op (leviColour e) r (v : V) ∈
        levelCoinvariantRelations ρ w m κ p
      apply Submodule.smul_mem
      apply Submodule.mem_sup_right
      exact currentTail_contains ρ _ _ m (leviColour_isLevi e) hr v.property

/-- The linear map from the bottom Cartan orbit to its level coinvariant. -/
def bottomCartanToLevel (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0)) :
    bottomCartanSpan ρ w a c →ₗ[ℂ] TruncatedLevelPiece ρ w (a + b + c) b (2 * a + b) :=
  (levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)).comp
    (Submodule.inclusion ((bottomCartanSpan_le_multiplicity ρ w a b c h).trans
      (levelMultiplicitySpan_le_filtration ρ w (a + b + c) h b (2 * a + b))))

/-- Cartan zero modes have the bottom weight after passage to the level coinvariant. -/
theorem bottomCartanToLevel_weight (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    (i : Fin 3) (v : bottomCartanSpan ρ w a c) :
    (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b)).op (A3Sector.simpleH i) 0
      (bottomCartanToLevel ρ w a b c h v) =
        (A3Sector.weightABC a b a i : ℂ) • bottomCartanToLevel ρ w a b c h v := by
  change levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)
    ((levelLeviCurrent ρ w (a + b + c) b (2 * a + b)).op (A3Sector.simpleH i) 0
      (bottomCartanLift ρ w a b c h v)) =
        (A3Sector.weightABC a b a i : ℂ) •
          levelCoinvariantMap ρ w (a + b + c) b (2 * a + b)
            (bottomCartanLift ρ w a b c h v)
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  exact bottomCartanSpan_weight ρ w a b c h i v.property

/-- The actual universal level module for a triple of nonnegative bottom labels. -/
abbrev UniversalCorePiece (a b c : ℕ) :=
  UniversalLevelPiece (a + b + c) b (2 * a + b)

abbrev universalCoreCurrent (a b c : ℕ) :=
  levelCoinvariantCurrent (demazureCurrent (a + b + c))
    (demazureGenerator (a + b + c)) (a + b + c) b (2 * a + b)

abbrev universalBottomCartanMap (a b c : ℕ) :=
  bottomCartanToLevel (demazureCurrent (a + b + c)) (demazureGenerator (a + b + c))
    a b c (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0))

/-- The universal level piece is finite for all triples, including the zero-site case. -/
theorem universalCorePiece_finite (a b c : ℕ) : FiniteDimensional ℂ (UniversalCorePiece a b c) := by
  haveI := demazureModule_finite (a + b + c)
  infer_instance

/-- The zero-mode bottom vector in the universal level coinvariant. -/
def universalCoreBottom (a b c : ℕ) : UniversalCorePiece a b c :=
  universalBottomCartanMap a b c
    ⟨bottomVector _ _ a c, Submodule.subset_span ⟨[], rfl⟩⟩

/-- The still-required two-alphabet presentation of the universal bottom and its Levi orbit. -/
def UniversalCorePresentation (a b c : ℕ) : Prop :=
  ∃ π : CoreBaseRing a b c →ₗ[ℂ] UniversalCorePiece a b c,
    π 1 = universalCoreBottom a b c ∧
    LinearMap.range π ≤ LinearMap.range (universalBottomCartanMap a b c) ∧
    CoreCartanAction (universalCoreCurrent a b c) a b c π ∧
    CoreConvertedRelations (universalCoreCurrent a b c) a b c π ∧
    cycSubG (universalCoreCurrent a b c) (π 1) = ⊤

/-- The proved parabolic and zero-mode relations complete any such two-alphabet presentation. -/
theorem universalCoreRelations_of_bottomImage (a b c : ℕ)
    (π : CoreBaseRing a b c →ₗ[ℂ] UniversalCorePiece a b c)
    (himage : LinearMap.range π ≤ LinearMap.range (universalBottomCartanMap a b c))
    (hcartan : CoreCartanAction (universalCoreCurrent a b c) a b c π)
    (hconverted : CoreConvertedRelations (universalCoreCurrent a b c) a b c π) :
    CoreRelations (universalCoreCurrent a b c) a b c π := by
  refine ⟨?_, ?_, hcartan, hconverted⟩
  · intro e he hne r φ
    obtain ⟨v, hv⟩ := himage (LinearMap.mem_range_self π φ)
    rw [← hv]
    exact universalBottomCartan_parabolic_annihilation a b c v e he hne r
  · intro i φ
    obtain ⟨v, hv⟩ := himage (LinearMap.mem_range_self π φ)
    rw [← hv]
    exact bottomCartanToLevel_weight _ _ a b c
      (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0)) i v

/-- A core estimate gives the level bound once the explicit universal presentation is supplied. -/
theorem levelTruncationBound_of_corePresentation (a b c : ℕ)
    (hbound : TruncatedCoreRankBound a b c) (hpresentation : UniversalCorePresentation a b c) :
    LevelTruncationBound (a + b + c) b (2 * a + b) := by
  obtain ⟨π, _, himage, hcartan, hconverted, hcyclic⟩ := hpresentation
  haveI := universalCorePiece_finite a b c
  exact hbound (UniversalCorePiece a b c) (universalCoreCurrent a b c) π
    (universalCoreRelations_of_bottomImage a b c π himage hcartan hconverted) hcyclic
    (fun e r hr => levelCoinvariantCurrent_high _ _ _ _ _ e r hr)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingIdeal_eq_top_of_overfull
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingEvaluation_zero_of_overfull
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantCurrent_high
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanToLevel_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCorePiece_finite
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreRelations_of_bottomImage
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_corePresentation
