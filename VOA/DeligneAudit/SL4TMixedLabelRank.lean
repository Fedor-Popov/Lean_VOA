import VOA.DeligneAudit.SL4TRadicalCountFiltration
import VOA.DeligneAudit.SL4TMixedBlockTotal

/-! The truncated sl₄ dimension bound for every pair of symmetric outer and middle labels. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.UnivG
attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- The two supported second counts at a first-count triple. -/
def mixedSecondSupportedCounts (a b : ℕ) (d : Fin 3 → ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range ((a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩).toNat + 1)) ×ˢ
    (Finset.range ((a3KeyLabelInt b a 1 ⟨d 0, d 1, d 2, 0⟩).toNat + 1))

/-- A nested pair of Levi count indices determines a mixed parameter block. -/
def mixedCountIndexParams (a b : ℕ) (x : Σ _ : (Fin 3 → ℕ), ℕ × ℕ) : MixedParams :=
  mixedLabelBlockParams a b x.1 x.2.1 x.2.2

theorem mixedCountIndexParams_injective (a b : ℕ) :
    Function.Injective (mixedCountIndexParams a b) := by
  rintro ⟨d, e₁, e₂⟩ ⟨d', f₁, f₂⟩ he
  have h₀ : (d 0 : ℤ) = d' 0 := congrArg MixedParams.d1 he
  have h₁ : (d 1 : ℤ) = d' 1 := congrArg MixedParams.d2 he
  have h₂ : (d 2 : ℤ) = d' 2 := congrArg MixedParams.d3 he
  have hd : d = d' := by
    funext i
    fin_cases i <;> simp <;> omega
  have he₁ : (e₁ : ℤ) = f₁ := congrArg MixedParams.e1 he
  have he₂ : (e₂ : ℤ) = f₂ := congrArg MixedParams.e2 he
  have hf₁ : e₁ = f₁ := by omega
  have hf₂ : e₂ = f₂ := by omega
  subst d'
  subst f₁
  subst f₂
  rfl

/-- Every supported pair of Levi indices determines a valid mixed block. -/
theorem mixedCountIndexParams_mem_valid (a b : ℕ)
    (x : Σ _ : (Fin 3 → ℕ), ℕ × ℕ)
    (hx : x ∈ (radicalSupportedCounts a b a).sigma (mixedSecondSupportedCounts a b)) :
    mixedCountIndexParams a b x ∈ mixedValidBlocks a b := by
  obtain ⟨hd, he⟩ := Finset.mem_sigma.mp hx
  have hd' := (mem_radicalSupportedCounts _ _ _ _).mp hd
  have hm : ∀ j, 0 ≤ a3KeyLabelInt b a j ⟨x.1 0, x.1 1, x.1 2, 0⟩ := by
    intro j
    fin_cases j <;> simp [a3KeyLabelInt] <;> omega
  simp only [mixedSecondSupportedCounts, Finset.mem_product, Finset.mem_range] at he
  apply (mem_mixedValidBlocks _ _ _).mpr
  refine ⟨mixedLabelBlockParams_valid a b x.1 hd' x.2.1 x.2.2 ?_ ?_, rfl, rfl⟩
  · rw [← Int.toNat_of_nonneg (hm 0)]
    exact_mod_cast Nat.le_of_lt_succ he.1
  · rw [← Int.toNat_of_nonneg (hm 1)]
    exact_mod_cast Nat.le_of_lt_succ he.2

/-- The nested Levi block sum is bounded by the complete mixed site count. -/
theorem mixedNestedBlockBound_sum_le (a b : ℕ) :
    (∑ d ∈ radicalSupportedCounts a b a,
      ∑ e ∈ mixedSecondSupportedCounts a b d,
        mixedBlockBound (mixedLabelBlockParams a b d e.1 e.2)) ≤ 15 ^ a * 6 ^ b := by
  classical
  rw [← mixedBlockBound_sum_all_valid]
  let t := (radicalSupportedCounts a b a).sigma (mixedSecondSupportedCounts a b)
  have hs : (∑ x ∈ t, mixedBlockBound (mixedCountIndexParams a b x)) =
      ∑ q ∈ t.image (mixedCountIndexParams a b), mixedBlockBound q := by
    rw [Finset.sum_image (mixedCountIndexParams_injective a b).injOn]
  have he : (∑ d ∈ radicalSupportedCounts a b a,
      ∑ e ∈ mixedSecondSupportedCounts a b d,
        mixedBlockBound (mixedLabelBlockParams a b d e.1 e.2)) =
      ∑ x ∈ t, mixedBlockBound (mixedCountIndexParams a b x) := by
    rw [Finset.sum_sigma]
    rfl
  rw [he, hs]
  apply Finset.sum_le_sum_of_subset
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact mixedCountIndexParams_mem_valid a b x hx

variable {V : Type} [AddCommGroup V] [Module ℂ V]

set_option synthInstance.maxHeartbeats 100000 in
-- The two quotient stages contain nested Grassmannian coefficient algebras.
/-- The two actual Levi filtrations give the mixed truncated bound on a cyclic module. -/
theorem mixedLabelTruncatedCyclic_rank_le [FiniteDimensional ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (a b : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b a))
    (ht : ∀ i s v, a + b ≤ s → ρ.op i s v = 0) :
    Module.finrank ℂ (cycSubG ρ w) ≤ 15 ^ a * 6 ^ b := by
  apply le_trans (radicalCountFiltration_rank_le ρ w a b a h
    (fun d => ∑ e ∈ mixedSecondSupportedCounts a b d,
      mixedBlockBound (mixedLabelBlockParams a b d e.1 e.2)) ?_)
    (mixedNestedBlockBound_sum_le a b)
  intro d hd
  rw [radicalCountClosure_map_eq_secondCounts ρ w a b a h d]
  exact mixedSecondLeviFiltration_rank_le ρ w a b h ht d
    ((mem_radicalSupportedCounts a b a d).mp hd)

/-- Every universally presented mixed-label truncated sl₄ module has the mixed site bound. -/
theorem truncatedWeyl_sl4_mixed_rank_le (a b : ℕ) :
    FiniteDimensional ℂ (MixedLabelModule a b) ∧
      Module.finrank ℂ (MixedLabelModule a b) ≤ 15 ^ a * 6 ^ b := by
  let R := truncatedWeylSpec (weightABC a b a) (a + b)
  let ρ := univRepG bracketTable R
  let w := wUG bracketTable R
  have hw := (truncatedWeylSpec_sat_iff ρ w _ _).mp (univG_sat bracketTable R)
  haveI : FiniteDimensional ℂ (MixedLabelModule a b) :=
    (mixedLabelModule_finite_and_local_bound a b).1
  have ht : ∀ i s v, a + b ≤ s → ρ.op i s v = 0 := by
    intro i s v hs
    exact current_truncation_on_cyclic ρ w (a + b) hw.2 v
      (by rw [presentedCurrent_cyclic]; trivial) i s hs
  have hb := mixedLabelTruncatedCyclic_rank_le ρ w a b hw.1 ht
  rw [presentedCurrent_cyclic, finrank_top] at hb
  exact ⟨inferInstance, hb⟩

/-- The universal mixed-label truncated rank assertion holds for every pair of labels. -/
theorem mixedLabelTruncatedRank : MixedLabelTruncatedRank := truncatedWeyl_sl4_mixed_rank_le

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedCountIndexParams_injective
#print axioms VOA.DeligneAudit.SL4T.mixedCountIndexParams_mem_valid
#print axioms VOA.DeligneAudit.SL4T.mixedNestedBlockBound_sum_le
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedCyclic_rank_le
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_mixed_rank_le
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedRank
