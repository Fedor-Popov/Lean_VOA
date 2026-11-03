import VOA.DeligneAudit.SL4TPointInvariantComparison

/-! Equivariant point configurations for truncated full-flag strata and the dimension squeeze. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Realize a labeled stratum configuration as a complex point using distinct site values. -/
def fullFlagStratumPoint (B k j : ℕ) (Y : Finset (Fin B))
    (ζ : Fin (B - k) → ℂ) (f : FullFlagStratumConfiguration B k j Y) : Fin B → ℂ :=
  fun i => ζ (f.val.val i)

/-- Distinct site values give distinct points for distinct labeled configurations. -/
theorem fullFlagStratumPoint_injective (B k j : ℕ) (Y : Finset (Fin B))
    (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) :
    Function.Injective (fullFlagStratumPoint B k j Y ζ) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact hζ (congrFun h i)

/-- The leading-relation quotient of the actual stratum point set has the configuration count. -/
theorem fullFlagStratumPoint_initial_finrank (B k j : ℕ) (Y : Finset (Fin B))
    (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) :
    FiniteDimensional ℂ (MvPolynomial (Fin B) ℂ ⧸
      pointInitialIdeal (fullFlagStratumPoint B k j Y ζ)) ∧
    Module.finrank ℂ (MvPolynomial (Fin B) ℂ ⧸
      pointInitialIdeal (fullFlagStratumPoint B k j Y ζ)) =
        Nat.card (FullFlagStratumConfiguration B k j Y) := by
  letI := Fintype.ofFinite (FullFlagStratumConfiguration B k j Y)
  simpa only [Nat.card_eq_fintype_card] using
    pointInitialQuotient_finrank _ (fullFlagStratumPoint_injective B k j Y ζ hζ)

variable {G : Type*} [Group G]

/-- Position permutations preserving the selected subset act on its configuration stratum. -/
abbrev fullFlagStratumPositionAction (B k j : ℕ) (Y : Finset (Fin B))
    (η : G →* Equiv.Perm (Fin B)) (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    MulAction G (FullFlagStratumConfiguration B k j Y) where
  smul g f := ⟨fullFlagConfiguration_relabel B k (η g) f.val, by
    have he := fullFlagDoublesIn_relabel B k Y (η g) f.val
    rw [hY g] at he
    rw [he]
    exact f.property⟩
  one_smul f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change f.val.val ((η 1).symm i) = f.val.val i
    rw [map_one]
    rfl
  mul_smul g h f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change f.val.val ((η (g * h)).symm i) =
      f.val.val ((η h).symm ((η g).symm i))
    rw [map_mul]
    rfl

/-- The stratum-point embedding intertwines its position action with coordinate permutations. -/
theorem fullFlagStratumPoint_equivariant (B k j : ℕ) (Y : Finset (Fin B))
    (ζ : Fin (B - k) → ℂ) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    letI := fullFlagStratumPositionAction B k j Y η hY
    ∀ (g : G) f i, fullFlagStratumPoint B k j Y ζ (g⁻¹ • f) i =
      fullFlagStratumPoint B k j Y ζ f (η g i) := by
  letI := fullFlagStratumPositionAction B k j Y η hY
  intro g f i
  change ζ (f.val.val ((η g⁻¹).symm i)) = ζ (f.val.val (η g i))
  rw [map_inv]
  rfl

/-- The invariant leading-relation algebra of a stratum has one dimension per position orbit. -/
theorem fullFlagStratumPoint_initial_fixed_finrank [Fintype G]
    (B k j : ℕ) (Y : Finset (Fin B)) (ζ : Fin (B - k) → ℂ)
    (hζ : Function.Injective ζ) (η : G →* Equiv.Perm (Fin B))
    (hY : ∀ g, Y.map (η g).toEmbedding = Y) :
    letI := fullFlagStratumPositionAction B k j Y η hY
    Module.finrank ℂ
      (pointInitialRepresentation (fullFlagStratumPoint B k j Y ζ) η
        (fullFlagStratumPoint_equivariant B k j Y ζ η hY)).invariants =
      Nat.card (MulAction.orbitRel.Quotient G (FullFlagStratumConfiguration B k j Y)) := by
  letI := fullFlagStratumPositionAction B k j Y η hY
  letI := Fintype.ofFinite (FullFlagStratumConfiguration B k j Y)
  exact pointInitialQuotient_fixed_finrank _
    (fullFlagStratumPoint_injective B k j Y ζ hζ) η
    (fullFlagStratumPoint_equivariant B k j Y ζ η hY)

/-- The Young subgroup preserving every colour class of the positions. -/
def positionColourSubgroup {C : Type*} {B : ℕ} (colour : Fin B → C) :
    Subgroup (Equiv.Perm (Fin B)) where
  carrier := {e | ∀ i, colour (e i) = colour i}
  one_mem' := fun _ => rfl
  mul_mem' := by intro e f he hf i; exact (he (f i)).trans (hf i)
  inv_mem' := by
    intro e he i
    have h := he (e⁻¹ i)
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

/-- A union of colour classes is preserved by the Young subgroup. -/
theorem positionColourSubgroup_preserves_selected {C : Type*} [DecidableEq C]
    {B : ℕ} (colour : Fin B → C) (selected : Finset C)
    (g : positionColourSubgroup colour) :
    (Finset.univ.filter fun i => colour i ∈ selected).map g.val.toEmbedding =
      Finset.univ.filter fun i => colour i ∈ selected := by
  classical
  ext i
  simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
  have h := g.property (g.val.symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [← h]

/-- A scalar upper bound matching a point count forces equality with the leading relation ideal. -/
theorem pointInitialIdeal_eq_of_rank_bound {ι σ : Type*} [Fintype ι]
    (x : ι → σ → ℂ) (hx : Function.Injective x) (I : Ideal (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ (MvPolynomial σ ℂ ⧸ I)]
    (hI : I ≤ pointInitialIdeal x)
    (hbound : Module.finrank ℂ (MvPolynomial σ ℂ ⧸ I) ≤ Fintype.card ι) :
    I = pointInitialIdeal x := by
  obtain ⟨hfinite, hdim⟩ := pointInitialQuotient_finrank x hx
  letI := hfinite
  let f := Ideal.Quotient.factorₐ ℂ hI
  have hs : Function.Surjective f := Ideal.Quotient.factor_surjective hI
  have he : Module.finrank ℂ (MvPolynomial σ ℂ ⧸ I) =
      Module.finrank ℂ (MvPolynomial σ ℂ ⧸ pointInitialIdeal x) := by
    apply le_antisymm (hbound.trans_eq hdim.symm)
    exact LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hs
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) he).mpr hs
  apply le_antisymm hI
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hi
  change Ideal.Quotient.mk (pointInitialIdeal x) p = f 0
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

/-- The full-flag scalar bound reduces the dimension squeeze to ideal containment. -/
theorem fullFlagStratumIdeal_eq_pointInitialIdeal_of_le (B k j : ℕ)
    (Y : Finset (Fin B)) (hk : 2 * k ≤ B) (ζ : Fin (B - k) → ℂ)
    (hζ : Function.Injective ζ)
    (hI : fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j ≤
        pointInitialIdeal (fullFlagStratumPoint B k j Y ζ)) :
    fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet Y) (B - k) j =
        pointInitialIdeal (fullFlagStratumPoint B k j Y ζ) := by
  letI := Fintype.ofFinite (FullFlagStratumConfiguration B k j Y)
  letI := fullFlagStratum_finite B (B - k) j Y
  apply pointInitialIdeal_eq_of_rank_bound _
    (fullFlagStratumPoint_injective B k j Y ζ hζ) _ hI
  simpa only [Nat.card_eq_fintype_card] using fullFlagStratum_finrank_le B k j Y hk

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPoint_injective
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPoint_initial_finrank
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPoint_equivariant
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPoint_initial_fixed_finrank
#print axioms VOA.DeligneAudit.SL4T.positionColourSubgroup_preserves_selected
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_eq_of_rank_bound
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumIdeal_eq_pointInitialIdeal_of_le
