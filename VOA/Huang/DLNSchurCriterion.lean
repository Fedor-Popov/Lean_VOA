import VOA.Huang.DLNBeylLocal

/-! # Central-extension criteria for the homology-free Schur condition -/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

/-- The derived subgroup meets the kernel trivially in every central extension. -/
def CentralDerivedInjective (Q : Type) [Group Q] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* Q), Function.Surjective π →
    π.ker ≤ Subgroup.center E → ∀ x ∈ commutator E, π x = 1 → x = 1

/-- The central-extension criterion is exactly the existing Schur contract. -/
theorem schurTrivial_iff_centralDerivedInjective (Q : Type) [Group Q] :
    SchurTrivial Q ↔ CentralDerivedInjective Q := by
  constructor
  · intro h E _ π hs hc x hx hπx
    exact h E π hs hc E (MonoidHom.id E) π (by ext; rfl) x hx hπx
  · intro h E _ π hs hc F _ α β hcompat x hx hβx
    apply h E π hs hc (α x)
    · have hmap : (commutator F).map α ≤ commutator E := by
        rw [map_commutator_eq, commutator_def]
        exact Subgroup.commutator_mono le_top le_top
      exact hmap ⟨x, hx, rfl⟩
    · simpa [hβx] using congrArg (fun f : F →* Q => f x) hcompat

/-- Any map into a Schur-trivial group has trivial inflation. -/
theorem inflationTrivial_of_schurTrivial_target {A B : Type} [Group A] [Group B]
    (r : B →* A) (h : SchurTrivial A) : InflationTrivial r := by
  intro E _ π hs hc F _ α β hcompat x hx hβx
  exact h E π hs hc F α (r.comp β) (by simpa using hcompat) x hx
    (by simp [hβx])

end VOA.Huang.DLNSchur
