import VOA.DeligneAudit.SL4TConfigurationRootDivisor

/-! Remainder-minor containment and the exact point deformation of every full-flag stratum. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Each selected coordinate is homogeneous of integer degree one. -/
theorem fullFlagSubalphabet_integerHomogeneous {B : ℕ} (Y : Finset (Fin B)) :
    ∀ x ∈ fullFlagSubalphabet Y,
      x.IsWeightedHomogeneous (fun _ => (1 : ℤ)) 1 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact MvPolynomial.isWeightedHomogeneous_X (R := ℂ)
    (fun _ : Fin B => (1 : ℤ)) i

/-- Every all-row remainder minor is a leading relation of the configuration stratum. -/
theorem remainderRowMinor_mem_configurationInitialIdeal (B k j : ℕ)
    (Y : Finset (Fin B)) (ζ : Fin (B - k) → ℂ) (rows cols : Fin j → ℕ) :
    remainderRowMinor (fullFlagSubalphabet Y) (B - k) j rows cols ∈
      pointInitialIdeal (fullFlagStratumPoint B k j Y ζ) := by
  let d := remainderMinorDegree (B - k) j rows cols
  have hhom := remainderRowMinor_homogeneous (fun _ => (1 : ℤ))
    (fullFlagSubalphabet Y) (fullFlagSubalphabet_integerHomogeneous Y)
    (B - k) j rows cols
  by_cases hd : d < 0
  · rw [integerHomogeneous_eq_zero _ d hhom hd]
    exact Ideal.zero_mem _
  · have he : d = (d.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    let q := alphabetCharacteristic (List.ofFn ζ)
    have hq : q.coeff (B - k) = 1 := by
      have hm := alphabetCharacteristic_monic (List.ofFn ζ)
      have hn : q.natDegree = B - k := by
        dsimp only [q]
        rw [alphabetCharacteristic_natDegree, List.length_ofFn]
      rw [← hn]
      exact hm.coeff_natDegree
    obtain ⟨hdegree, htop⟩ := deformedRemainderMinor_top (fullFlagSubalphabet Y)
      (fullFlagSubalphabet_integerHomogeneous Y) (B - k) j q hq rows cols d.toNat he
    rw [← htop]
    apply pointInitialIdeal_of_vanishing _ _ _ _ hdegree
    funext f
    exact deformedRemainderMinor_configuration_zero B k j Y ζ rows cols f

/-- The entire all-row determinantal ideal lies in the configuration initial ideal. -/
theorem remainderAllIdeal_le_configurationInitialIdeal (B k j : ℕ)
    (Y : Finset (Fin B)) (ζ : Fin (B - k) → ℂ) :
    remainderAllIdeal (fullFlagSubalphabet Y) (B - k) j ≤
      pointInitialIdeal (fullFlagStratumPoint B k j Y ζ) := by
  apply Ideal.span_le.mpr
  rintro p ⟨rows, cols, rfl⟩
  exact remainderRowMinor_mem_configurationInitialIdeal B k j Y ζ rows cols

/-- In particular, the top-row stratum ideal lies in the configuration initial ideal. -/
theorem remainderTopIdeal_le_configurationInitialIdeal (B k j : ℕ)
    (Y : Finset (Fin B)) (ζ : Fin (B - k) → ℂ) :
    remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j ≤
      pointInitialIdeal (fullFlagStratumPoint B k j Y ζ) :=
  (remainderTopIdeal_le_allIdeal _ _ _).trans
    (remainderAllIdeal_le_configurationInitialIdeal B k j Y ζ)

/-- The upper-bound squeeze identifies the full-flag stratum with its point initial algebra. -/
theorem fullFlagStratumIdeal_eq_pointInitialIdeal (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B) (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) :
    fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j =
        pointInitialIdeal (fullFlagStratumPoint B k j Y ζ) := by
  apply fullFlagStratumIdeal_eq_pointInitialIdeal_of_le B k j Y hk ζ hζ
  exact sup_le (fullFlagTruncationIdeal_le_pointInitialIdeal B k j Y ζ)
    (remainderTopIdeal_le_configurationInitialIdeal B k j Y ζ)

/-- The all-row presentation has the same point initial algebra, including boundary strata. -/
theorem fullFlagAllStratumIdeal_eq_pointInitialIdeal (B k j : ℕ)
    (Y : Finset (Fin B)) (hk : 2 * k ≤ B)
    (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) :
    fullFlagTruncationIdeal B (B - k) ⊔
      remainderAllIdeal (fullFlagSubalphabet Y) (B - k) j =
        pointInitialIdeal (fullFlagStratumPoint B k j Y ζ) := by
  apply le_antisymm
  · exact sup_le (fullFlagTruncationIdeal_le_pointInitialIdeal B k j Y ζ)
      (remainderAllIdeal_le_configurationInitialIdeal B k j Y ζ)
  · rw [← fullFlagStratumIdeal_eq_pointInitialIdeal B k j Y hk ζ hζ]
    exact sup_le_sup_left (remainderTopIdeal_le_allIdeal _ _ _) _

/-- Every full-flag stratum has exactly the number of its labeled configurations. -/
theorem fullFlagStratum_finrank_eq_configurations (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B) :
    Module.finrank ℂ (FullFlagStratumRing B (B - k) j Y) =
      Nat.card (FullFlagStratumConfiguration B k j Y) := by
  let ζ : Fin (B - k) → ℂ := fun a => (a.val : ℂ)
  have hζ : Function.Injective ζ := by
    intro a b h
    apply Fin.ext
    dsimp [ζ] at h
    exact_mod_cast h
  let e := (Ideal.quotientEquivAlgOfEq ℂ
    (fullFlagStratumIdeal_eq_pointInitialIdeal B k j Y hk ζ hζ)).toLinearEquiv
  rw [e.finrank_eq]
  exact (fullFlagStratumPoint_initial_finrank B k j Y ζ hζ).2

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagSubalphabet_integerHomogeneous
#print axioms VOA.DeligneAudit.SL4T.remainderRowMinor_mem_configurationInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.remainderAllIdeal_le_configurationInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_le_configurationInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_eq_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.fullFlagAllStratumIdeal_eq_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_eq_configurations
