import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoIdeal
import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCount06
import VOA.DeligneAudit.D4FusionRealizationCharacterTwo

/-! `ModelDegreeBound 2`, from the existing m=2 certificates. The 784 checked
normal words span `AllM.Model 2` (their ideal is smaller); the all-m model
ideal is current-homogeneous, so each degree piece is spanned by the normal
words of that current degree; these number 300, 378, 106 (zero beyond), by
the degree-refined stem cascade; and `d4FusionFZ 2 = 300 + 378 q + 106 q^2`
from the kernel-checked n = 2 Demazure character. Hence D4 classical freeness
rests only on `ModelDegreeBound m` for m >= 3. -/
namespace VOA.DeligneAudit.D4FusionContact
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneCharacter
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open Polynomial
noncomputable section

/-- The image of a normal word in the all-m model at m = 2. -/
def normalImage (w : List (Fin 18)) : AllM.Model 2 :=
  ((AllM.modelIdeal 2).restrictScalars ℂ).mkQ (polyWord (w.map varIndex))

theorem normal_deg_cast (w : List (Fin 18)) :
    (((w.map varIndex).map fun x => (x.2.val : ℤ)).sum) = (wordCurrentDeg w : ℤ) := by
  induction w with
  | nil => simp [wordCurrentDeg]
  | cons v w ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, ih]
      simp [wordCurrentDeg, varIndex]

theorem normal_graded (w : List (Fin 18)) :
    (polyWord (w.map varIndex)).IsWeightedHomogeneous (cw 2) (wordCurrentDeg w : ℤ) := by
  have h := polyWord_graded 2 (w.map varIndex)
  rwa [normal_deg_cast] at h

/-- The 784 normal words span the all-m model at m = 2. -/
theorem model_two_span :
    (⊤ : Submodule ℂ (AllM.Model 2)) ≤
      Submodule.span ℂ (normalImage '' {w | w ∈ normalEnumeration}) := by
  have hle : m2ModelIdeal.restrictScalars ℂ ≤ (AllM.modelIdeal 2).restrictScalars ℂ :=
    fun _ hp => m2ModelIdeal_le_allM hp
  let φ : M2Model →ₗ[ℂ] AllM.Model 2 :=
    (m2ModelIdeal.restrictScalars ℂ).mapQ ((AllM.modelIdeal 2).restrictScalars ℂ)
      LinearMap.id hle
  intro x _
  obtain ⟨p, rfl⟩ := ((AllM.modelIdeal 2).restrictScalars ℂ).mkQ_surjective x
  have hp : (m2ModelIdeal.restrictScalars ℂ).mkQ p ∈ Submodule.span ℂ (Set.range
      fun i : Fin normalEnumeration.length => (m2ModelIdeal.restrictScalars ℂ).mkQ
        (polyWord ((normalEnumeration.get i).map varIndex))) := by
    rw [m2_normalEnumeration_span]
    exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := φ) hp
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_mono ?_) hmap
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨normalEnumeration.get i, List.get_mem _ _, rfl⟩

/-- The current-weight-b projection of the model (the model ideal is homogeneous). -/
def degProj (b : ℤ) : AllM.Model 2 →ₗ[ℂ] AllM.Model 2 :=
  ((AllM.modelIdeal 2).restrictScalars ℂ).mapQ ((AllM.modelIdeal 2).restrictScalars ℂ)
    (MvPolynomial.weightedHomogeneousComponent (cw 2) b)
    (fun _ hp => modelIdeal_component_mem 2 hp b)

theorem degProj_normalImage (b : ℕ) (w : List (Fin 18)) :
    degProj (b : ℤ) (normalImage w) = if wordCurrentDeg w = b then normalImage w else 0 := by
  have hw := normal_graded w
  change ((AllM.modelIdeal 2).restrictScalars ℂ).mkQ
    (MvPolynomial.weightedHomogeneousComponent (cw 2) (b : ℤ) (polyWord (w.map varIndex))) = _
  by_cases h : wordCurrentDeg w = b
  · rw [if_pos h, ← h, hw.weightedHomogeneousComponent_same]
    rfl
  · rw [if_neg h, hw.weightedHomogeneousComponent_ne (b : ℤ)
      (fun hb => h (by exact_mod_cast hb.symm)), map_zero]

theorem isWeightedHomogeneous_cw {m : ℕ} {p : MvPolynomial (Vars m) ℂ} {b : ℕ}
    (hp : p.IsWeightedHomogeneous (modeCurrentWeight m) b) :
    p.IsWeightedHomogeneous (cw m) (b : ℤ) := by
  intro e he
  rw [← hp he]
  simp [Finsupp.weight_apply, Finsupp.sum, AllMCountResearch.LeviRules.modeWeight,
    modeCurrentWeight]

/-- Each current-degree piece of the model is spanned by the normal words of that degree. -/
theorem modelDegree_two_le (b : ℕ) :
    modelDegree 2 b ≤
      Submodule.span ℂ
        (normalImage '' {w | w ∈ normalEnumeration ∧ wordCurrentDeg w = b}) := by
  rintro _ ⟨p, hp, rfl⟩
  have hz : ((AllM.modelIdeal 2).restrictScalars ℂ).mkQ p =
      degProj (b : ℤ) (((AllM.modelIdeal 2).restrictScalars ℂ).mkQ p) := by
    change _ = ((AllM.modelIdeal 2).restrictScalars ℂ).mkQ
      (MvPolynomial.weightedHomogeneousComponent (cw 2) (b : ℤ) p)
    rw [(isWeightedHomogeneous_cw hp).weightedHomogeneousComponent_same]
  rw [hz]
  have hx := model_two_span
    (Submodule.mem_top (x := ((AllM.modelIdeal 2).restrictScalars ℂ).mkQ p))
  have hmap := Submodule.mem_map_of_mem (f := degProj (b : ℤ)) hx
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, degProj_normalImage]
  split_ifs with h
  · exact Submodule.subset_span ⟨w, ⟨hw, h⟩, rfl⟩
  · exact Submodule.zero_mem _

theorem finrank_modelDegree_two_le (b : ℕ) :
    Module.finrank ℂ (modelDegree 2 b) ≤ degCount normalEnumeration b := by
  classical
  let L := normalEnumeration.filter fun w => decide (wordCurrentDeg w = b)
  have hsub : normalImage '' {w | w ∈ normalEnumeration ∧ wordCurrentDeg w = b} ⊆
      ↑((L.map normalImage).toFinset) := by
    rintro _ ⟨w, ⟨hw, hd⟩, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨w, List.mem_filter.mpr ⟨hw, by simpa using hd⟩, rfl⟩
  calc Module.finrank ℂ (modelDegree 2 b)
      ≤ Module.finrank ℂ (Submodule.span ℂ (↑((L.map normalImage).toFinset) :
          Set (AllM.Model 2))) :=
        Submodule.finrank_mono ((modelDegree_two_le b).trans (Submodule.span_mono hsub))
    _ ≤ ((L.map normalImage).toFinset).card := finrank_span_finset_le_card _
    _ ≤ (L.map normalImage).length := List.toFinset_card_le _
    _ = degCount normalEnumeration b := by
        rw [List.length_map, degCount, List.countP_eq_length_filter]

/-- The exact current-degree profile of the m=2 normal words. -/
def twoCount (b : ℕ) : ℕ :=
  if b = 0 then 300 else if b = 1 then 378 else if b = 2 then 106 else 0

theorem degCount_normal (b : ℕ) : degCount normalEnumeration b = twoCount b := by
  change degCount (enumerateFrom leaders 4 0 []) b = _
  by_cases hb : b < 5
  · have h : degCount (enumerateFrom leaders 4 0 []) b = Count.stem459Deg ⟨b, hb⟩ :=
      Count.stem459_dcount ⟨b, hb⟩
    rw [h]
    rcases b with _ | _ | _ | _ | _ | b
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  · have ht : twoCount b = 0 := by
      simp only [twoCount]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [ht]
    unfold degCount
    rw [List.countP_eq_zero]
    intro w hw
    have h1 := length_le_of_mem_enumerateFrom leaders 4 0 [] w hw
    have h2 := wordCurrentDeg_le_length w
    simp only [List.length_nil] at h1
    simp only [decide_eq_true_eq]
    omega

private theorem d4_hilbInt_integerCoeff (m N : ℕ) :
    D4K.hilbInt m N = D4CharacterTwo.integerCoeff
      (demazureChar cartanD4 VOA.DeligneAudit.DeligneCharacter.thetaD4 wordD4 m)
        ((m : ℤ) * m) N := by
  unfold D4K.hilbInt D4CharacterTwo.integerCoeff
  rfl

theorem d4_hilbInt_two (N : ℕ) : D4K.hilbInt 2 N = D4CharacterTwo.profile N := by
  have hc : D4CharacterTwo.integerCoeff
      (demazureChar cartanD4 VOA.DeligneAudit.DeligneCharacter.thetaD4 wordD4 2) 4 N =
        D4CharacterTwo.profile N := D4CharacterTwo.charTwo_coeff N
  rw [d4_hilbInt_integerCoeff 2 N]
  change D4CharacterTwo.integerCoeff
    (demazureChar cartanD4 VOA.DeligneAudit.DeligneCharacter.thetaD4 wordD4 2) 4 N = _
  rw [hc]

theorem d4FusionFZ_two_eq : D4Wp.d4FusionFZ 2 = D4Wp.hilbSeriesZ 2 -
    (PowerSeries.X ^ 2 * (PowerSeries.X + 1) * D4Wp.d4FusionFZ 1 +
      PowerSeries.X ^ 4 * D4Wp.d4FusionFZ 0) := by
  have hq1 : VOA.DeligneGaussian.qbinom (PowerSeries.X : PowerSeries ℚ) 2 1 =
      PowerSeries.X + 1 := by
    simp [VOA.DeligneGaussian.qbinom]
  have hq2 : VOA.DeligneGaussian.qbinom (PowerSeries.X : PowerSeries ℚ) 2 2 = 1 := by
    simp [VOA.DeligneGaussian.qbinom]
  change DeligneCarrier.fusionOf D4Wp.hilbSeriesZ 2 = D4Wp.hilbSeriesZ 2 -
    (PowerSeries.X ^ 2 * (PowerSeries.X + 1) * DeligneCarrier.fusionOf D4Wp.hilbSeriesZ 1 +
      PowerSeries.X ^ 4 * DeligneCarrier.fusionOf D4Wp.hilbSeriesZ 0)
  rw [DeligneCarrier.fusionOf_eq D4Wp.hilbSeriesZ 2, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [hq1, hq2]

/-- The unclamped multiplicity-two fusion series is 300 + 378 q + 106 q^2. -/
theorem d4FusionFZ_two_coeff (b : ℕ) :
    PowerSeries.coeff b (D4Wp.d4FusionFZ 2) = (twoCount b : ℚ) := by
  have h1 : D4Wp.d4FusionFZ 1 = PowerSeries.C (28 : ℚ) := by
    ext n
    rw [d4FusionFZ_one_coeff, PowerSeries.coeff_C]
  have h0 : D4Wp.d4FusionFZ 0 = 1 := by
    ext n
    rw [d4FusionFZ_zero_coeff, PowerSeries.coeff_one]
  have hpoly : (PowerSeries.X ^ 2 * (PowerSeries.X + 1) * PowerSeries.C (28 : ℚ) +
      PowerSeries.X ^ 4 * 1 : PowerSeries ℚ) =
      PowerSeries.C 28 * PowerSeries.X ^ 3 + PowerSeries.C 28 * PowerSeries.X ^ 2 +
        PowerSeries.X ^ 4 := by
    ring
  rw [d4FusionFZ_two_eq, h1, h0, hpoly, map_sub, map_add, map_add,
    PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow,
    D4Wp.hilbSeriesZ, PowerSeries.coeff_mk, d4_hilbInt_two]
  rcases b with _ | _ | _ | _ | _ | b
  · norm_num [twoCount, D4CharacterTwo.profile]
  · norm_num [twoCount, D4CharacterTwo.profile]
  · norm_num [twoCount, D4CharacterTwo.profile]
  · norm_num [twoCount, D4CharacterTwo.profile]
  · norm_num [twoCount, D4CharacterTwo.profile]
  · simp only [twoCount, D4CharacterTwo.profile]
    split_ifs <;> first | omega | norm_num

/-- MAIN: the per-degree model bound at multiplicity two holds. -/
theorem modelDegreeBound_two : ModelDegreeBound 2 := by
  intro b
  rw [d4FusionFZ_two_coeff]
  exact_mod_cast (finrank_modelDegree_two_le b).trans_eq (degCount_normal b)

theorem fusionModuleBoundZ_of_modelDegreeBound_three
    (hQ : ∀ m, 3 ≤ m → ModelDegreeBound m) :
    FusionModuleBoundG D4sector D4Wp.d4FusionFZ :=
  fusionModuleBoundZ_of_modelDegreeBound_two fun m hm => by
    rcases Nat.eq_or_lt_of_le hm with rfl | h
    · exact modelDegreeBound_two
    · exact hQ m h

/-- D4 classical freeness from the per-degree model bounds for m >= 3 alone. -/
theorem D4_classicallyFree_of_modelDegreeBound_three
    (hQ : ∀ m, 3 ≤ m → ModelDegreeBound m) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  D4Lie.classicallyFree_of_fusionBoundZ (fusionModuleBoundZ_of_modelDegreeBound_three hQ)

end
#print axioms model_two_span
#print axioms finrank_modelDegree_two_le
#print axioms degCount_normal
#print axioms d4FusionFZ_two_coeff
#print axioms modelDegreeBound_two
#print axioms fusionModuleBoundZ_of_modelDegreeBound_three
#print axioms D4_classicallyFree_of_modelDegreeBound_three
end VOA.DeligneAudit.D4FusionContact
