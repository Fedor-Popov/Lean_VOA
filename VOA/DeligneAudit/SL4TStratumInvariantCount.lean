import VOA.DeligneAudit.SL4TStratumInitialIdeal
import VOA.DeligneAudit.SL4TFullFlagInvariantCount

/-! Exact invariant dimensions for the concrete determinantal full-flag strata. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {G : Type*} [Group G]

/-- Every position group preserving the selected set preserves the full stratum ideal. -/
theorem fullFlagStratumIdeal_stable (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) (g : G) :
    (fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j).restrictScalars ℂ ≤
        ((fullFlagTruncationIdeal B (B - k) ⊔
          remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j).restrictScalars ℂ).comap
            (polynomialPositionRepresentation η g) := by
  letI := fullFlagStratumPositionAction B k j Y η hY
  let ζ : Fin (B - k) → ℂ := fun a => (a.val : ℂ)
  have hζ : Function.Injective ζ := by
    intro a b h
    apply Fin.ext
    dsimp [ζ] at h
    exact_mod_cast h
  rw [fullFlagStratumIdeal_eq_pointInitialIdeal B k j Y hk ζ hζ]
  exact pointInitialIdeal_stable (fullFlagStratumPoint B k j Y ζ) η
    (fullFlagStratumPoint_equivariant B k j Y ζ η hY) g

/-- Position permutations act on the actual polynomial quotient defining a stratum. -/
def fullFlagStratumPositionRepresentation (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    Representation ℂ G (FullFlagStratumRing B (B - k) j Y) :=
  (polynomialPositionRepresentation η).quotient
    ((fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j).restrictScalars ℂ)
    (fullFlagStratumIdeal_stable B k j Y hk η hY)

/-- The exact point comparison intertwines the actual stratum quotient representations. -/
theorem fullFlagStratumPointComparison_equivariant (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B) (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ)
    (η : G →* Equiv.Perm (Fin B)) (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    letI := fullFlagStratumPositionAction B k j Y η hY
    let e := (Ideal.quotientEquivAlgOfEq ℂ
      (fullFlagStratumIdeal_eq_pointInitialIdeal B k j Y hk ζ hζ)).toLinearEquiv
    ∀ g v, e (fullFlagStratumPositionRepresentation B k j Y hk η hY g v) =
      pointInitialRepresentation (fullFlagStratumPoint B k j Y ζ) η
        (fullFlagStratumPoint_equivariant B k j Y ζ η hY) g (e v) := by
  letI := fullFlagStratumPositionAction B k j Y η hY
  dsimp only
  intro g v
  induction v using Submodule.Quotient.induction_on with
  | _ p => rfl

/-- Invariants of the concrete full-flag stratum are counted exactly by configuration orbits. -/
theorem fullFlagStratum_invariant_finrank [Fintype G] (B k j : ℕ)
    (Y : Finset (Fin B)) (hk : 2 * k ≤ B) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    letI := fullFlagStratumPositionAction B k j Y η hY
    Module.finrank ℂ
      (fullFlagStratumPositionRepresentation B k j Y hk η hY).invariants =
        Nat.card (MulAction.orbitRel.Quotient G (FullFlagStratumConfiguration B k j Y)) := by
  letI := fullFlagStratumPositionAction B k j Y η hY
  let ζ : Fin (B - k) → ℂ := fun a => (a.val : ℂ)
  have hζ : Function.Injective ζ := by
    intro a b h
    apply Fin.ext
    dsimp [ζ] at h
    exact_mod_cast h
  let e := (Ideal.quotientEquivAlgOfEq ℂ
    (fullFlagStratumIdeal_eq_pointInitialIdeal B k j Y hk ζ hζ)).toLinearEquiv
  let τ := pointInitialRepresentation (fullFlagStratumPoint B k j Y ζ) η
    (fullFlagStratumPoint_equivariant B k j Y ζ η hY)
  let ef := representationFixedEquiv
    (fullFlagStratumPositionRepresentation B k j Y hk η hY) τ e
    (fullFlagStratumPointComparison_equivariant B k j Y hk ζ hζ η hY)
  rw [ef.finrank_eq]
  exact fullFlagStratumPoint_initial_fixed_finrank B k j Y ζ hζ η hY

/-- Young-invariant stratum dimensions equal the number of attained site colour multisets. -/
theorem colourStratum_invariant_finrank {C : Type*} [DecidableEq C]
    (B k j : ℕ) (hk : 2 * k ≤ B) (colour : Fin B → C) (selected : Finset C) :
    Module.finrank ℂ
      (fullFlagStratumPositionRepresentation B k j (selectedColourPositions colour selected)
        hk (positionColourSubgroup colour).subtype
        (positionColourSubgroup_preserves_selected colour selected)).invariants =
      Nat.card (Set.range (fun f : FullFlagStratumConfiguration B k j
        (selectedColourPositions colour selected) =>
          configurationColourMultiplicity colour f.val)) := by
  letI := colourStratumPositionAction B k j colour selected
  letI := Fintype.ofFinite (positionColourSubgroup colour)
  exact (fullFlagStratum_invariant_finrank B k j _ hk
    (positionColourSubgroup colour).subtype
    (positionColourSubgroup_preserves_selected colour selected)).trans
      (Nat.card_congr (colourStratumOrbitEquiv B k j colour selected))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPositionRepresentation
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPointComparison_equivariant
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_invariant_finrank
#print axioms VOA.DeligneAudit.SL4T.colourStratum_invariant_finrank
