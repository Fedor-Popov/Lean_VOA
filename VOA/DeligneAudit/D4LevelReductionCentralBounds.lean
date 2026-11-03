import VOA.DeligneAudit.D4LevelReductionCentralFiltration

/-! The all-m zero-adjoint boundary bound, including every integer vector-node grade. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- The boundary configuration consists of positive exterior-square sites and central sites. -/
def centralBoundaryMultiplicity (b c : ℕ) : SiteMultiplicity := ![0, b, 0, c]

theorem centralBoundaryMultiplicity_mem (b c : ℕ) :
    centralBoundaryMultiplicity b c ∈ siteMultiplicities (b + c) := by
  simp [siteMultiplicities, Finset.mem_piAntidiag, centralBoundaryMultiplicity,
    Fin.sum_univ_succ]

/-- There is one site configuration at the zero-adjoint boundary. -/
theorem multiplicity_eq_centralBoundary (b c : ℕ) (t : SiteMultiplicity)
    (ht : t ∈ siteMultiplicities (b + c)) (hg : multiplicityGrade t = b)
    (hp : multiplicityLevel t = b) : t = centralBoundaryMultiplicity b c := by
  have hs := siteMultiplicity_sum (b + c) t ht
  simp only [multiplicityGrade, multiplicityLevel] at hg hp
  have ht₀ : t 0 = 0 := by omega
  have ht₁ : t 1 = b := by omega
  have ht₂ : t 2 = 0 := by omega
  have ht₃ : t 3 = c := by omega
  funext i
  fin_cases i <;> simp [centralBoundaryMultiplicity, ht₀, ht₁, ht₂, ht₃]

/-- The central boundary target is its Grassmannian multiplicity times the local Weyl rank. -/
theorem levelTarget_central_boundary (b c : ℕ) :
    levelTarget (b + c) b b = (b + c).choose c * 6 ^ b := by
  classical
  have hmem : centralBoundaryMultiplicity b c ∈
      (siteMultiplicities (b + c)).filter
        (fun t => multiplicityGrade t = b ∧ multiplicityLevel t = b) := by
    refine Finset.mem_filter.mpr ⟨centralBoundaryMultiplicity_mem b c, ?_, ?_⟩
    · simp [multiplicityGrade, centralBoundaryMultiplicity]
    · simp [multiplicityLevel, centralBoundaryMultiplicity]
  rw [levelTarget, Finset.sum_eq_single_of_mem _ hmem]
  · rw [configurationDimension_factorial (b + c) _ (centralBoundaryMultiplicity_mem b c)]
    simp only [centralBoundaryMultiplicity, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Nat.factorial_zero, pow_zero,
      one_mul, zero_add, add_zero]
    rw [Nat.choose_eq_factorial_div_factorial (by omega : c ≤ b + c)]
    simp [Nat.add_sub_cancel_right, Nat.mul_comm]
  · intro t ht hne
    obtain ⟨ht, hg, hp⟩ := Finset.mem_filter.mp ht
    exact (hne (multiplicity_eq_centralBoundary b c t ht hg hp)).elim

/-- The universal parent is finite-dimensional even at multiplicity zero. -/
theorem demazureModule_finite (m : ℕ) : FiniteDimensional ℂ (DemazureModule m) := by
  have h := d4_all_weight_rank (demazureCurrent m) (demazureGenerator m) m
    (univG_sat D4sector.f (ravFam D4sector m 0))
  rw [d4_univ_cyclic] at h
  haveI : FiniteDimensional ℂ (⊤ : Submodule ℂ (DemazureModule m)) := h.1
  exact FiniteDimensional.of_surjective (⊤ : Submodule ℂ (DemazureModule m)).subtype
    (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

/-- Every supported zero-adjoint boundary satisfies the required truncation bound. -/
theorem levelTruncationBound_central_boundary (b c : ℕ) :
    LevelTruncationBound (b + c) b b := by
  haveI := demazureModule_finite (b + c)
  let ρ := demazureCurrent (b + c)
  let w := demazureGenerator (b + c)
  let E := levelFiltration ρ w (b + c) b b
  let T := levelFiltration ρ w (b + c) b ((b : ℤ) + 1)
  have hb := centralBoundary_rank_le ρ w b c
    (univG_sat D4sector.f (ravFam D4sector (b + c) 0))
  change Module.finrank ℂ (E ⧸ T.comap E.subtype) ≤ _ at hb
  rw [ksKey_quot_finrank_eq_image] at hb
  rw [LevelTruncationBound, levelTarget_central_boundary]
  change Module.finrank ℂ
    (E ⧸ (T ⊔ currentTail ρ E {a | IsLevi a} (b + c)).comap E.subtype) ≤ _
  rw [ksKey_quot_finrank_eq_image]
  exact (SL4T.quotientImage_finrank_antitone E T _ le_sup_left).trans hb

/-- Overfull central words generate no boundary quotient. -/
theorem centralBoundary_eq_next_of_overfull {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V) (m c : ℕ) (hc : m < c)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c) =
      levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c + 1) := by
  rw [centralBoundary_eq_orbits_sup_next ρ w m c h]
  apply sup_eq_right.mpr
  apply iSup_le
  intro d
  exact keyOrbit_le_levelFiltration_of_layer ρ w m _ _ _
    (centralKey_le_next_of_overfull ρ w m c d hc h)

/-- The zero-adjoint level bound holds at every multiplicity and every integer grade. -/
theorem levelTruncationBound_of_zero_adjoint (m : ℕ) (κ : ℤ) :
    LevelTruncationBound m κ κ := by
  by_cases hupper : (m : ℤ) < κ
  · exact levelTruncationBound_of_empty m κ κ (Or.inr (Or.inr (Or.inr (by omega))))
  by_cases hnonneg : 0 ≤ κ
  · let b := κ.toNat
    let c := m - b
    have hb : (b : ℤ) = κ := Int.toNat_of_nonneg hnonneg
    have hbc : b + c = m := by dsimp [c]; omega
    have hh := levelTruncationBound_central_boundary b c
    rwa [hbc, hb] at hh
  · let c := ((m : ℤ) - κ).toNat
    have hc : (c : ℤ) = (m : ℤ) - κ := Int.toNat_of_nonneg (by omega)
    have heq := centralBoundary_eq_next_of_overfull (demazureCurrent m)
      (demazureGenerator m) m c (by omega)
      (univG_sat D4sector.f (ravFam D4sector m 0))
    have hg : (m : ℤ) - c = κ := by omega
    rw [hg] at heq
    change Module.finrank ℂ (UniversalLevelPiece m κ κ) ≤ _
    rw [truncatedLevel_finrank_zero_of_eq_next _ _ m κ κ heq]
    exact Nat.zero_le _

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.centralBoundaryMultiplicity_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.multiplicity_eq_centralBoundary
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_central_boundary
#print axioms VOA.DeligneAudit.D4LevelReduction.demazureModule_finite
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_central_boundary
#print axioms VOA.DeligneAudit.D4LevelReduction.centralBoundary_eq_next_of_overfull
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_zero_adjoint
