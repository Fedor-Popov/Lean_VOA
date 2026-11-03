import VOA.DeligneAudit.SL4TMixedQuotientSubspaceFlag

/-! Multi-doubled coefficient flags bound the actual last-root Levi orbits. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

variable {V : Type} [AddCommGroup V] [Module ℂ V]

set_option synthInstance.maxHeartbeats 100000 in
-- Both actual Levi quotients involve nested Grassmannian coefficient algebras.
/-- An all-tail coefficient flag bounds each actual middle-weight last-root orbit. -/
theorem multiDoubledSiteSecondLeviOrbit_bound_of_flag
    (ρ : CurrentModule bracketTable V) (w : V) (B k : ℕ) (hN : 0 < B - k)
    (h : LocalWeylRel ρ w (weightABC 0 B 0))
    (ht : ∀ i s v, B - k ≤ s → ρ.op i s v = 0)
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 0 B d e₁ e₂))
    (hflag : MultiDoubledSiteCoefficientFlag B k (mixedLabelBlockParams 0 B d e₁ e₂)) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w 0 B 0 h d
    FiniteDimensional ℂ (secondLeviOrbit Q β e₁ e₂) ∧
      Module.finrank ℂ (secondLeviOrbit Q β e₁ e₂) ≤
        multiDoubledSiteBlockBound B k (mixedLabelBlockParams 0 B d e₁ e₂) := by
  let Q := radicalCountQuotCurrent ρ w d
  let β := radicalGrassmannianAmbientEvaluation ρ w 0 B 0 h d
  let N := higherSecondLeviCountClosure Q β e₁ e₂
  let q := mixedLabelBlockParams 0 B d e₁ e₂
  let π := (secondLeviMultiplicity Q β e₁ e₂).subtype.comp
    (mixedSecondLeviEvaluation ρ w 0 B h d e₁ e₂ hv)
  let q₀ := (a3KeyLabelInt B 0 1 ⟨d 0, d 1, d 2, 0⟩).toNat
  have hm := mixedLabelBlockParams_dominant 0 B d e₁ e₂ hv 1
  have hw : mixedWeight q = (q₀ : ℤ) + e₁ - e₂ := by
    dsimp only [q₀]
    rw [Int.toNat_of_nonneg hm]
    simp [q, mixedWeight, mixedQ, mixedLabelBlockParams, a3KeyLabelInt]
    ring
  have hwpos : 0 ≤ mixedWeight q := by
    have : MixedValid q := hv
    simp only [MixedValid] at this
    unfold mixedWeight
    omega
  have he : ∀ s φ, Q.op 1 s (β φ) = 0 :=
    fun s φ => radicalGrassmannianAmbientEvaluation_raising ρ w 0 B 0 h d 1 s φ
  have hh : ∀ φ, Q.op 7 0 (β φ) = (q₀ : ℂ) • β φ :=
    radicalGrassmannianAmbientEvaluation_weight ρ w 0 B 0 h d 1 hm
  have hf : ∀ φ, (Q.op 4 0 ^ (q₀ + 1)) (β φ) = 0 :=
    radicalGrassmannianAmbientEvaluation_lowering ρ w 0 B 0 h d 1 hm
  have hI : (middleFlagAllTailIdeal q (B - k)).restrictScalars ℂ ≤ LinearMap.ker π := by
    intro x hx
    have hz := middleFlagAllTailIdeal_le_kernel ρ w 0 B h (B - k) ht d e₁ e₂ hv
      hN hx
    change (mixedSecondLeviEvaluation ρ w 0 B h d e₁ e₂ hv x).val = 0
    rw [LinearMap.mem_ker.mp hz]
    rfl
  obtain ⟨flag⟩ := hflag
  have hb := mixedQuotientRingImage_bound_of_subspaceFlag q hv
    (secondLeviQuotient_currentRelations Q β e₁ e₂) π
    (middleFlagAllTailIdeal q (B - k)) hI (B - k)
    (multiDoubledSiteBlockBound B k q) flag
    (fun s φ => secondLeviMultiplicity_raising Q β he e₁ e₂ s
      (mixedSecondLeviEvaluation ρ w 0 B h d e₁ e₂ hv φ))
    (fun φ => by
      have hz := secondLeviMultiplicity_weight Q β q₀ hh e₁ e₂
        (mixedSecondLeviEvaluation ρ w 0 B h d e₁ e₂ hv φ)
      rw [← hw] at hz
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hwpos]
      exact hz)
    (fun s hs φ => mixedSecondLeviEvaluation_cartan ρ w 0 B h d e₁ e₂ hv s hs φ)
    (fun φ => by
      have hz := (secondLeviMultiplicity_lowering_sharp Q β q₀ he hh hf e₁ e₂
        (mixedSecondLeviEvaluation ρ w 0 B h d e₁ e₂ hv φ)).2
      rw [← hw] at hz
      exact hz hwpos)
    (fun s hs φ => by
      obtain ⟨x, hx⟩ := N.mkQ_surjective (π φ)
      rw [← hx]
      change N.mkQ (Q.op 4 s x) = 0
      rw [radicalCountQuot_truncated ρ w (B - k) ht d 4 s hs x, map_zero])
  have hr : Set.range π = (secondLeviMultiplicity Q β e₁ e₂ : Set _) := by
    ext x
    constructor
    · rintro ⟨φ, rfl⟩
      exact (mixedSecondLeviEvaluation ρ w 0 B h d e₁ e₂ hv φ).property
    · intro hx
      obtain ⟨φ, hφ⟩ := mixedSecondLeviEvaluation_surjective ρ w 0 B h d e₁ e₂ hv ⟨x, hx⟩
      exact ⟨φ, congrArg Subtype.val hφ⟩
  rw [hr] at hb
  exact hb

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteSecondLeviOrbit_bound_of_flag
