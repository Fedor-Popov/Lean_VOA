import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTransfer
import VOA.DeligneAudit.DeligneCharacterDemazureCountTypes
import VOA.DeligneAudit.D4FusionRealizationSmallCharacter

/-! The D4 input U5 reduced to PER-CURRENT-DEGREE commutative algebra.
`modelDegree m b` is the image in `AllM.Model m` of the polynomials of current
weight b (weight of a mode variable = its mode index). Every local-Weyl module
of multiplicity m >= 1 has `finrank (cycDeg R w b) <= finrank (modelDegree m b)`.
Hence per-degree model bounds by the coefficients of `d4FusionFZ m` give
`FusionModuleBoundG D4sector d4FusionFZ` (the total clause comes from the proved
count 28^m) and D4 classical freeness, with NO Demazure-realization input.
`ModelDegreeBound m` itself is open (not proved here); multiplicity one is bypassed by the proved
m = 1 module bounds, so only m >= 2 is needed (`..._two` versions). -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
noncomputable section

/-- Generic per-degree transfer: a finite quotient mapping each of its degree
pieces onto the degree-d symbols of the universal PBW module bounds every
arbitrary source degree piece. -/
theorem source_cycDeg_le_of_degree_cover (spec : RelSpec 28) {m : ℕ}
    (hU : HighestRel (univRepG contactF spec) (wUG contactF spec) m)
    {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q]
    (L : Q →ₗ[ℂ] universalPBWGr spec) (hsurj : Function.Surjective L)
    (P : ℕ → Submodule ℂ Q)
    (hP : ∀ d, GrDeg (univRepG contactF spec) (wUG contactF spec) d ≤ (P d).map L)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {R : CurrentModule contactF V} {w : V} (h : Sat contactF R w spec) (d : ℕ) :
    Module.finrank ℂ (cycDeg R w d) ≤ Module.finrank ℂ (P d) := by
  haveI : FiniteDimensional ℂ (universalPBWGr spec) := Module.Finite.of_surjective L hsurj
  haveI : FiniteDimensional ℂ (UModG contactF spec) := (universal_source_bound spec hU).1
  have h1 := finrank_cycDeg_le_univG h d
  have h2 := finrank_univ_cycDeg_le_GrDeg spec hU d
  have h3 := Submodule.finrank_mono (hP d)
  have h4 := Submodule.finrank_map_le L (P d)
  exact (h1.trans h2).trans (h3.trans h4)

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

namespace VOA.DeligneAudit.D4FusionContact
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneCharacter
open Polynomial
noncomputable section

/-- The current weight of a mode variable is its mode index. -/
def modeCurrentWeight (m : ℕ) : Vars m → ℕ := fun x => x.2.val

/-- The current-degree-b piece of the commutative model. -/
def modelDegree (m b : ℕ) : Submodule ℂ (AllM.Model m) :=
  (MvPolynomial.weightedHomogeneousSubmodule ℂ (modeCurrentWeight m) b).map
    ((AllM.modelIdeal m).restrictScalars ℂ).mkQ

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V}

/-- Every degree-d word symbol is the evaluation of a current-weight-d polynomial. -/
theorem exists_weighted_polyEval {m : ℕ} (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    ∀ l : List CurrentLetter, ∃ p : MvPolynomial (Vars m) ℂ,
      p ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ (modeCurrentWeight m) (letterDeg l) ∧
        polyEval R w (modeLetter m) p = grWord R w l := by
  intro l
  induction l with
  | nil =>
      refine ⟨1, ?_, polyEval_one R w (modeLetter m)⟩
      rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      exact MvPolynomial.isWeightedHomogeneous_one ℂ _
  | cons x l ih =>
      obtain ⟨p, hp, hpe⟩ := ih
      by_cases hx : x.2 < m
      · refine ⟨MvPolynomial.X (x.1, ⟨x.2, hx⟩) * p, ?_, ?_⟩
        · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hp ⊢
          rw [letterDeg_cons]
          exact (MvPolynomial.isWeightedHomogeneous_X ℂ (modeCurrentWeight m)
            (x.1, ⟨x.2, hx⟩)).mul hp
        · have hj : modeLetter m (x.1, ⟨x.2, hx⟩) = (x.1, x.2) := rfl
          rw [polyEval_X_mul, hj, hpe, grOp_grWord]
      · refine ⟨0, Submodule.zero_mem _, ?_⟩
        rw [map_zero, ← grOp_grWord, grOp_zero_of_source_zero R w x.1 x.2
          (localWeyl_high_kills hm h (radIndex x.1) x.2 (by omega))]
        rfl

/-- The model's degree-d piece covers the degree-d word symbols. -/
theorem GrDeg_le_modelDegree_map {m : ℕ} (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m)
    (d : ℕ) : GrDeg R w d ≤ (modelDegree m d).map (AllM.modelMap hm h) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨p, hp, hpe⟩ := exists_weighted_polyEval hm h l
  rw [hl] at hp
  exact ⟨((AllM.modelIdeal m).restrictScalars ℂ).mkQ p, ⟨p, hp, rfl⟩, hpe⟩

/-- MAIN (per-degree transfer): every local-Weyl module of multiplicity m >= 1
has each current-degree rank bounded by the model's degree piece. -/
theorem localWeyl_cycDeg_le_modelDegree {m : ℕ} (hm : 1 ≤ m)
    (h : LocalWeylRelG D4sector R w m) (b : ℕ) :
    Module.finrank ℂ (cycDeg R w b) ≤ Module.finrank ℂ (modelDegree m b) := by
  have hU := univ_localWeylRelG D4sector m
  exact source_cycDeg_le_of_degree_cover (lwSpec D4sector m) (highestRel_of_localWeyl hU)
    (AllM.modelMap hm hU) (AllM.modelMap_surjective hm hU) (modelDegree m)
    (GrDeg_le_modelDegree_map hm hU) ((localWeylRelG_iff D4sector R w m).mp h) b

/-- The residual commutative statement, degree by degree. -/
def ModelDegreeBound (m : ℕ) : Prop :=
  ∀ b, (Module.finrank ℂ (modelDegree m b) : ℚ) ≤ PowerSeries.coeff b (D4Wp.d4FusionFZ m)

theorem d4_hilbInt_zero (N : ℕ) : D4K.hilbInt 0 N = if N = 0 then 1 else 0 := by
  by_cases h : N = 0
  · subst N; rfl
  have h' : (0 : ℤ) ≠ (N : ℤ) := by omega
  simp [D4K.hilbInt, demazureChar, h, h']

theorem d4FusionFZ_zero_coeff (b : ℕ) :
    PowerSeries.coeff b (D4Wp.d4FusionFZ 0) = if b = 0 then 1 else 0 := by
  rw [D4Wp.d4FusionFZ, DeligneCarrier.fusionOf_eq]
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, D4Wp.hilbSeriesZ,
    PowerSeries.coeff_mk, d4_hilbInt_zero]
  split_ifs <;> simp

/-- Per-degree bounds at multiplicity zero, from the proved trivial bounds. -/
theorem localWeyl_zero_le_coeff (h : LocalWeylRelG D4sector R w 0) (b : ℕ) :
    (Module.finrank ℂ (cycDeg R w b) : ℚ) ≤ PowerSeries.coeff b (D4Wp.d4FusionFZ 0) := by
  rw [d4FusionFZ_zero_coeff]
  by_cases hb : b = 0
  · subst hb
    rw [if_pos rfl]
    exact_mod_cast (localWeyl_zero_degree_bound h).2
  · rw [if_neg hb, localWeyl_zero_cycDeg_eq_bot h b (by omega)]
    simp

/-- The total clause follows from per-degree bounds and the proved count 28^m. -/
theorem total_of_degree_le {m : ℕ}
    (hle : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule D4sector.f V)
      (w : V), LocalWeylRelG D4sector ρ w m → ∀ b,
        (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ PowerSeries.coeff b (D4Wp.d4FusionFZ m))
    (h : LocalWeylRelG D4sector R w m) (B : ℕ) :
    ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg R w b) ≤ D4sector.n ^ m := by
  obtain ⟨B0, hz, hs⟩ := DeligneCarrier.d4FusionFZ_count m
  have hnn : ∀ b, 0 ≤ PowerSeries.coeff b (D4Wp.d4FusionFZ m) := fun b =>
    (Nat.cast_nonneg _).trans (hle _ _ _ (univ_localWeylRelG D4sector m) b)
  have h1 : (∑ b ∈ Finset.range B, (Module.finrank ℂ (cycDeg R w b) : ℚ)) ≤
      ∑ b ∈ Finset.range B, PowerSeries.coeff b (D4Wp.d4FusionFZ m) :=
    Finset.sum_le_sum (fun b _ => hle V R w h b)
  have h2 : (∑ b ∈ Finset.range B, PowerSeries.coeff b (D4Wp.d4FusionFZ m)) ≤
      ∑ b ∈ Finset.range (max B B0), PowerSeries.coeff b (D4Wp.d4FusionFZ m) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (le_max_left B B0)) (fun b _ _ => hnn b)
  have h3 : (∑ b ∈ Finset.range B0, PowerSeries.coeff b (D4Wp.d4FusionFZ m)) =
      ∑ b ∈ Finset.range (max B B0), PowerSeries.coeff b (D4Wp.d4FusionFZ m) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right B B0))
    intro b _ hb
    exact hz b (by simpa using hb)
  have h4 : (∑ b ∈ Finset.range B, (Module.finrank ℂ (cycDeg R w b) : ℚ)) ≤
      ((28 : ℕ) : ℚ) ^ m := by
    rw [← hs, h3]
    exact h1.trans h2
  change _ ≤ 28 ^ m
  exact_mod_cast h4

/-- MAIN: per-degree model bounds for m >= 1 give U5 for D4 in the unclamped form. -/
theorem fusionModuleBoundZ_of_modelDegreeBound (hQ : ∀ m, 1 ≤ m → ModelDegreeBound m) :
    FusionModuleBoundG D4sector D4Wp.d4FusionFZ := by
  have hle : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule D4sector.f V) (w : V), LocalWeylRelG D4sector ρ w m → ∀ b,
        (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ PowerSeries.coeff b (D4Wp.d4FusionFZ m) := by
    intro m V _ _ ρ w h b
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact localWeyl_zero_le_coeff h b
    · exact (Nat.cast_le.mpr (localWeyl_cycDeg_le_modelDegree hm h b)).trans (hQ m hm b)
  exact ⟨hle, fun m V _ _ ρ w h B => total_of_degree_le (hle m) h B⟩

/-- D4 classical freeness from the per-degree model bounds; no Demazure realization. -/
theorem D4_classicallyFree_of_modelDegreeBound (hQ : ∀ m, 1 ≤ m → ModelDegreeBound m) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  D4Lie.classicallyFree_of_fusionBoundZ (fusionModuleBoundZ_of_modelDegreeBound hQ)

theorem d4_hilbInt_one (N : ℕ) :
    D4K.hilbInt 1 N = if N = 0 then 28 else if N = 1 then 1 else 0 := by
  unfold D4K.hilbInt
  rw [cartanD4, VOA.DeligneAudit.DeligneCharacter.thetaD4, wordD4, D4Small.charOne_eq]
  simpa using D4Small.charOne_coeff N

theorem d4FusionFZ_one_eq :
    D4Wp.d4FusionFZ 1 = D4Wp.hilbSeriesZ 1 - PowerSeries.X * D4Wp.d4FusionFZ 0 := by
  have hq : VOA.DeligneGaussian.qbinom (PowerSeries.X : PowerSeries ℚ) 1 1 = 1 := by
    simp [VOA.DeligneGaussian.qbinom]
  change DeligneCarrier.fusionOf D4Wp.hilbSeriesZ 1 =
    D4Wp.hilbSeriesZ 1 - PowerSeries.X * DeligneCarrier.fusionOf D4Wp.hilbSeriesZ 0
  rw [DeligneCarrier.fusionOf_eq D4Wp.hilbSeriesZ 1, Finset.sum_range_one]
  simp [hq]

/-- The unclamped multiplicity-one fusion series is exactly 28 in degree zero. -/
theorem d4FusionFZ_one_coeff (b : ℕ) :
    PowerSeries.coeff b (D4Wp.d4FusionFZ 1) = if b = 0 then 28 else 0 := by
  rw [d4FusionFZ_one_eq, map_sub, D4Wp.hilbSeriesZ, PowerSeries.coeff_mk, d4_hilbInt_one]
  rcases b with _ | _ | b
  · simp
  · simp [PowerSeries.coeff_succ_X_mul, d4FusionFZ_zero_coeff]
  · simp [PowerSeries.coeff_succ_X_mul, d4FusionFZ_zero_coeff]

/-- Per-degree bounds at multiplicity one, from the proved m = 1 module bounds. -/
theorem localWeyl_one_le_coeff (h : LocalWeylRelG D4sector R w 1) (b : ℕ) :
    (Module.finrank ℂ (cycDeg R w b) : ℚ) ≤ PowerSeries.coeff b (D4Wp.d4FusionFZ 1) := by
  rw [d4FusionFZ_one_coeff]
  by_cases hb : b = 0
  · subst hb
    rw [if_pos rfl]
    exact_mod_cast (localWeyl_one_zero_bound h).2
  · rw [if_neg hb, localWeyl_one_cycDeg_eq_bot h b (by omega)]
    simp

/-- MAIN (sharpened): per-degree model bounds for m >= 2 alone give U5 for D4. -/
theorem fusionModuleBoundZ_of_modelDegreeBound_two (hQ : ∀ m, 2 ≤ m → ModelDegreeBound m) :
    FusionModuleBoundG D4sector D4Wp.d4FusionFZ := by
  have hle : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule D4sector.f V) (w : V), LocalWeylRelG D4sector ρ w m → ∀ b,
        (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ PowerSeries.coeff b (D4Wp.d4FusionFZ m) := by
    intro m V _ _ ρ w h b
    match m, h with
    | 0, h => exact localWeyl_zero_le_coeff h b
    | 1, h => exact localWeyl_one_le_coeff h b
    | m + 2, h =>
        exact (Nat.cast_le.mpr (localWeyl_cycDeg_le_modelDegree (by omega) h b)).trans
          (hQ (m + 2) (by omega) b)
  exact ⟨hle, fun m V _ _ ρ w h B => total_of_degree_le (hle m) h B⟩

theorem D4_classicallyFree_of_modelDegreeBound_two (hQ : ∀ m, 2 ≤ m → ModelDegreeBound m) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  D4Lie.classicallyFree_of_fusionBoundZ (fusionModuleBoundZ_of_modelDegreeBound_two hQ)

end
#print axioms localWeyl_cycDeg_le_modelDegree
#print axioms d4FusionFZ_zero_coeff
#print axioms fusionModuleBoundZ_of_modelDegreeBound
#print axioms D4_classicallyFree_of_modelDegreeBound
#print axioms d4FusionFZ_one_coeff
#print axioms fusionModuleBoundZ_of_modelDegreeBound_two
#print axioms D4_classicallyFree_of_modelDegreeBound_two
end VOA.DeligneAudit.D4FusionContact
