import VOA.Examples.LatticeGenOppExpand

/-! # Vacuum coefficient of a boson dressing on a Schur state

`EE(α)_{-p} S_p(β) = κ(⟨α,β⟩, p) · 1`, where `κ(P, ·)` are the coefficients of `(1 - x)^P`.
This is the Fock-space input for evaluating the `E`-telescope on charged lattice tops.
It is read off from the master OPE expansion `hExpand1_gen`, valid for either sign of `⟨α,β⟩`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LatGen
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatExp (kZ kZ_neg kZ_nonneg)

variable (L : IntegralLattice)

/-- On the Fock vacuum, the four-fold product `TvVec` reduces to its creation halves. -/
theorem TvVec_vacuum_eq (α β : L.carrier) (C D : ℤ) :
    TvVec L α β C D (vacuumN (rank L)) =
      EminusVecField L α C (EminusVecField L β D (vacuumN (rank L))) := by
  rw [TvVec, finsum_eq_single _ (C, D)]
  · simp only [sub_self, EplusVecField_vacuum, if_true]
  · intro pq hpq
    by_cases hq : pq.2 = D
    · have hp : pq.1 ≠ C := fun h => hpq (Prod.ext h hq)
      rw [hq, sub_self, EplusVecField_vacuum, if_pos rfl, EplusVecField_vacuum,
        if_neg (by omega)]
      simp
    · rw [EplusVecField_vacuum, if_neg (by omega)]
      simp

/-- `EE(α)_{-p} S_p(β) = κ(⟨α,β⟩, p) · 1`. -/
theorem EEVec_neg_vSchur (hPos : L.PosDef) (α β : L.carrier) (p : ℕ) :
    EEVec L α (-(p : ℤ)) (vSchur L β p) =
      kZ ((L.form α β : ℤ) : ℂ) (p : ℤ) • vacuumN (rank L) := by
  have h0 : vSchur L β p = EEVec L β (p : ℤ) (vacuumN (rank L)) := by
    rw [EEVec_vacuum, if_pos (by positivity)]
    simp
  rw [h0, hExpand1_gen L hPos, finsum_eq_single _ (p : ℤ)]
  · rw [TvVec_vacuum_eq, neg_add_cancel, sub_self, EminusVecField_vacuum, if_pos le_rfl]
    simp [EminusVecField_apply, EminusVec, vSchur_zero, vacuumN]
  · intro k hk
    rw [TvVec_vacuum_eq]
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [EminusVecField_neg L α (by omega), LinearMap.zero_apply, smul_zero]
    · rw [EminusVecField_vacuum, if_neg (by omega), map_zero, smul_zero]

end VOA.LatGen
