import VOA.DeligneAudit.SL4TConfigurationColourOrbits

/-! The exact equivariant point comparison for the truncated full flag without a stratum ideal. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The truncated full flag is the leading-relation algebra of all paired configurations. -/
theorem fullFlagTruncationIdeal_eq_pointInitialIdeal (B k : ℕ) (hk : 2 * k ≤ B)
    (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) :
    fullFlagTruncationIdeal B (B - k) =
      pointInitialIdeal (fullFlagStratumPoint B k (k + 1) Finset.univ ζ) := by
  letI := Fintype.ofFinite (FullFlagStratumConfiguration B k (k + 1) Finset.univ)
  letI := fullFlag_finite B (B - k)
  apply pointInitialIdeal_eq_of_rank_bound _
    (fullFlagStratumPoint_injective B k (k + 1) Finset.univ ζ hζ) _
    (fullFlagTruncationIdeal_le_pointInitialIdeal B k (k + 1) Finset.univ ζ)
  rw [← Nat.card_eq_fintype_card, Nat.card_congr
    (fullFlagStratumConfiguration_allEquiv B k (k + 1) Finset.univ (by omega))]
  exact fullFlag_finrank_le_configurations B k hk

/-- The dimension of the truncated full flag equals the number of its paired configurations. -/
theorem fullFlag_finrank_eq_configurations (B k : ℕ) (hk : 2 * k ≤ B) :
    Module.finrank ℂ (FullFlagRing B (B - k)) = Nat.card (FullFlagConfiguration B k) := by
  let ζ : Fin (B - k) → ℂ := fun a => (a.val : ℂ)
  have hζ : Function.Injective ζ := by
    intro a b h
    apply Fin.ext
    dsimp [ζ] at h
    exact_mod_cast h
  let e := (Ideal.quotientEquivAlgOfEq ℂ
    (fullFlagTruncationIdeal_eq_pointInitialIdeal B k hk ζ hζ)).toLinearEquiv
  rw [e.finrank_eq, (fullFlagStratumPoint_initial_finrank B k (k + 1) Finset.univ ζ hζ).2]
  exact Nat.card_congr
    (fullFlagStratumConfiguration_allEquiv B k (k + 1) Finset.univ (by omega))

/-- Position permutations preserve all elementary and common root-power relations. -/
theorem fullFlagTruncationIdeal_stable (B N : ℕ) (e : Equiv.Perm (Fin B)) :
    (fullFlagTruncationIdeal B N).restrictScalars ℂ ≤
      ((fullFlagTruncationIdeal B N).restrictScalars ℂ).comap
        (MvPolynomial.rename e).toLinearMap := by
  change fullFlagTruncationIdeal B N ≤
    (fullFlagTruncationIdeal B N).comap (MvPolynomial.rename e).toRingHom
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro p ⟨n, hn, rfl⟩
    change MvPolynomial.rename e (MvPolynomial.esymm (Fin B) ℂ n) ∈
      fullFlagTruncationIdeal B N
    rw [MvPolynomial.rename_esymm]
    exact (show fullFlagSymmetricIdeal B ≤ fullFlagTruncationIdeal B N from le_sup_left)
      (Ideal.subset_span ⟨n, hn, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change MvPolynomial.rename e ((MvPolynomial.X i : MvPolynomial (Fin B) ℂ) ^ N) ∈
      fullFlagTruncationIdeal B N
    rw [map_pow, MvPolynomial.rename_X]
    exact (show Ideal.span _ ≤ fullFlagTruncationIdeal B N from le_sup_right)
      (Ideal.subset_span ⟨e i, rfl⟩)

variable {G : Type*} [Group G]

/-- The position representation on the concrete truncated full-flag quotient. -/
def fullFlagPositionRepresentation (B N : ℕ) (η : G →* Equiv.Perm (Fin B)) :
    Representation ℂ G (FullFlagRing B N) :=
  (polynomialPositionRepresentation η).quotient
    ((fullFlagTruncationIdeal B N).restrictScalars ℂ)
    (fun g => fullFlagTruncationIdeal_stable B N (η g))

/-- All position permutations preserve the complete set of positions. -/
theorem positionPermutation_preserves_univ (B : ℕ) (e : Equiv.Perm (Fin B)) :
    Finset.univ.map e.toEmbedding = Finset.univ := by
  ext i
  simp

/-- The full-flag point comparison intertwines the concrete quotient actions. -/
theorem fullFlagPointComparison_equivariant (B k : ℕ) (hk : 2 * k ≤ B)
    (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ)
    (η : G →* Equiv.Perm (Fin B)) :
    letI := fullFlagStratumPositionAction B k (k + 1) Finset.univ η
      (fun g => positionPermutation_preserves_univ B (η g))
    let e := (Ideal.quotientEquivAlgOfEq ℂ
      (fullFlagTruncationIdeal_eq_pointInitialIdeal B k hk ζ hζ)).toLinearEquiv
    ∀ g v, e (fullFlagPositionRepresentation B (B - k) η g v) =
      pointInitialRepresentation (fullFlagStratumPoint B k (k + 1) Finset.univ ζ) η
        (fullFlagStratumPoint_equivariant B k (k + 1) Finset.univ ζ η
          (fun g => positionPermutation_preserves_univ B (η g))) g (e v) := by
  letI := fullFlagStratumPositionAction B k (k + 1) Finset.univ η
    (fun g => positionPermutation_preserves_univ B (η g))
  dsimp only
  intro g v
  induction v using Submodule.Quotient.induction_on with
  | _ p => rfl

/-- Invariants in the concrete truncated full flag are counted by configuration orbits. -/
theorem fullFlag_invariant_finrank [Fintype G] (B k : ℕ) (hk : 2 * k ≤ B)
    (η : G →* Equiv.Perm (Fin B)) :
    letI := fullFlagStratumPositionAction B k (k + 1) Finset.univ η
      (fun g => positionPermutation_preserves_univ B (η g))
    Module.finrank ℂ (fullFlagPositionRepresentation B (B - k) η).invariants =
      Nat.card (MulAction.orbitRel.Quotient G
        (FullFlagStratumConfiguration B k (k + 1) Finset.univ)) := by
  letI := fullFlagStratumPositionAction B k (k + 1) Finset.univ η
    (fun g => positionPermutation_preserves_univ B (η g))
  let ζ : Fin (B - k) → ℂ := fun a => (a.val : ℂ)
  have hζ : Function.Injective ζ := by
    intro a b h
    apply Fin.ext
    dsimp [ζ] at h
    exact_mod_cast h
  let e := (Ideal.quotientEquivAlgOfEq ℂ
    (fullFlagTruncationIdeal_eq_pointInitialIdeal B k hk ζ hζ)).toLinearEquiv
  let τ := pointInitialRepresentation (fullFlagStratumPoint B k (k + 1) Finset.univ ζ) η
    (fullFlagStratumPoint_equivariant B k (k + 1) Finset.univ ζ η
      (fun g => positionPermutation_preserves_univ B (η g)))
  let ef := representationFixedEquiv (fullFlagPositionRepresentation B (B - k) η) τ e
    (fullFlagPointComparison_equivariant B k hk ζ hζ η)
  rw [ef.finrank_eq]
  exact fullFlagStratumPoint_initial_fixed_finrank B k (k + 1) Finset.univ ζ hζ η
    (fun g => positionPermutation_preserves_univ B (η g))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagTruncationIdeal_eq_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_eq_configurations
#print axioms VOA.DeligneAudit.SL4T.fullFlagTruncationIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.positionPermutation_preserves_univ
#print axioms VOA.DeligneAudit.SL4T.fullFlagPointComparison_equivariant
#print axioms VOA.DeligneAudit.SL4T.fullFlag_invariant_finrank
