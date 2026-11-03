import VOA.DeligneAudit.SL4TConfigurationInitialRelations

/-! Young-subgroup orbits of stratum configurations are their site colour multisets. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {C : Type*} [DecidableEq C]

/-- The number of positions of each colour assigned to each labeled site. -/
def configurationColourMultiplicity {B k : ℕ} (colour : Fin B → C)
    (f : FullFlagConfiguration B k) (a : Fin (B - k)) (c : C) : ℕ :=
  (Finset.univ.filter fun i => f.val i = a ∧ colour i = c).card

/-- Equality of site colour multiplicities is exactly equivalence under a colour-preserving
permutation of the positions. -/
theorem configurationColourMultiplicity_eq_iff {B k : ℕ} (colour : Fin B → C)
    (f g : FullFlagConfiguration B k) :
    configurationColourMultiplicity colour f = configurationColourMultiplicity colour g ↔
      ∃ e : positionColourSubgroup colour, ∀ i, g.val (e.val i) = f.val i := by
  classical
  constructor
  · intro h
    have hc (a : Fin (B - k) × C) :
        Fintype.card {i : Fin B // (f.val i, colour i) = a} =
          Fintype.card {i : Fin B // (g.val i, colour i) = a} := by
      rcases a with ⟨a, c⟩
      have ha := congrFun (congrFun h a) c
      simpa only [configurationColourMultiplicity, Fintype.card_subtype,
        Prod.mk.injEq, Prod.eta] using ha
    let ef := fun a => Classical.choice (Fintype.card_eq.mp (hc a))
    let e : Equiv.Perm (Fin B) := Equiv.ofFiberEquiv ef
    have he (i : Fin B) : (g.val (e i), colour (e i)) = (f.val i, colour i) :=
      Equiv.ofFiberEquiv_map ef i
    exact ⟨⟨e, fun i => congrArg Prod.snd (he i)⟩, fun i => congrArg Prod.fst (he i)⟩
  · rintro ⟨e, he⟩
    funext a c
    apply Finset.card_equiv e.val
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
    rw [e.property i]

/-- The union of the selected colour classes, as a set of flag positions. -/
def selectedColourPositions {B : ℕ} (colour : Fin B → C) (selected : Finset C) :
    Finset (Fin B) := Finset.univ.filter fun i => colour i ∈ selected

/-- The Young subgroup acts on a stratum selected by a union of its colour classes. -/
abbrev colourStratumPositionAction (B k j : ℕ) (colour : Fin B → C) (selected : Finset C) :
    MulAction (positionColourSubgroup colour)
      (FullFlagStratumConfiguration B k j (selectedColourPositions colour selected)) :=
  fullFlagStratumPositionAction B k j (selectedColourPositions colour selected)
    (positionColourSubgroup colour).subtype
    (positionColourSubgroup_preserves_selected colour selected)

/-- Two stratum configurations are in the same Young-subgroup orbit exactly when their
multiset of colours at every site agrees. -/
theorem colourStratum_orbit_iff (B k j : ℕ) (colour : Fin B → C) (selected : Finset C)
    (f g : FullFlagStratumConfiguration B k j (selectedColourPositions colour selected)) :
    letI := colourStratumPositionAction B k j colour selected
    MulAction.orbitRel (positionColourSubgroup colour) _ f g ↔
      configurationColourMultiplicity colour f.val =
        configurationColourMultiplicity colour g.val := by
  letI := colourStratumPositionAction B k j colour selected
  constructor
  · rintro ⟨e, he⟩
    apply (configurationColourMultiplicity_eq_iff colour f.val g.val).mpr
    refine ⟨e⁻¹, fun i => ?_⟩
    have h := congrArg (fun a => a.val.val i) he
    exact h
  · intro h
    obtain ⟨e, he⟩ := (configurationColourMultiplicity_eq_iff colour f.val g.val).mp h
    refine ⟨e⁻¹, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact he i

/-- Young-subgroup orbits are in bijection with the attained site colour multisets. -/
def colourStratumOrbitEquiv (B k j : ℕ) (colour : Fin B → C) (selected : Finset C) :
    letI := colourStratumPositionAction B k j colour selected
    MulAction.orbitRel.Quotient (positionColourSubgroup colour)
        (FullFlagStratumConfiguration B k j (selectedColourPositions colour selected)) ≃
      Set.range (fun f : FullFlagStratumConfiguration B k j
        (selectedColourPositions colour selected) =>
          configurationColourMultiplicity colour f.val) := by
  letI := colourStratumPositionAction B k j colour selected
  exact (Quotient.congrRight (fun f g =>
    colourStratum_orbit_iff B k j colour selected f g)).trans
      (Setoid.quotientKerEquivRange _)

/-- The point initial algebra for a Young subgroup counts the attained site colour multisets. -/
theorem colourStratumPoint_initial_fixed_finrank (B k j : ℕ) (colour : Fin B → C)
    (selected : Finset C) (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) :
    letI := colourStratumPositionAction B k j colour selected
    let Y := selectedColourPositions colour selected
    let η := (positionColourSubgroup colour).subtype
    Module.finrank ℂ
      (pointInitialRepresentation (fullFlagStratumPoint B k j Y ζ) η
        (fullFlagStratumPoint_equivariant B k j Y ζ η
          (positionColourSubgroup_preserves_selected colour selected))).invariants =
      Nat.card (Set.range (fun f : FullFlagStratumConfiguration B k j Y =>
        configurationColourMultiplicity colour f.val)) := by
  letI := colourStratumPositionAction B k j colour selected
  letI := Fintype.ofFinite (positionColourSubgroup colour)
  exact (fullFlagStratumPoint_initial_fixed_finrank B k j _ ζ hζ
    (positionColourSubgroup colour).subtype
    (positionColourSubgroup_preserves_selected colour selected)).trans
      (Nat.card_congr (colourStratumOrbitEquiv B k j colour selected))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.configurationColourMultiplicity_eq_iff
#print axioms VOA.DeligneAudit.SL4T.colourStratum_orbit_iff
#print axioms VOA.DeligneAudit.SL4T.colourStratumPoint_initial_fixed_finrank
