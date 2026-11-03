import VOA.DeligneAudit.LeviTypeA3Closure
import VOA.DeligneAudit.LeviTypeA2CertGradedCertificate

/-! Restrict a fifteen-colour current module to the standard `sl₃` Levi. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

/-- The eight Levi currents satisfy the `sl₃[t]` commutator relation. -/
theorem a3Levi_comm (x y : Fin 8) (r s : ℕ) (v : V) :
    ρ.op (a3LeviColour x) r (ρ.op (a3LeviColour y) s v) -
      ρ.op (a3LeviColour y) s (ρ.op (a3LeviColour x) r v) =
        ∑ z : Fin 8, VOA.AffineSl3.bracketTable x y z •
          ρ.op (a3LeviColour z) (r + s) v := by
  rw [ρ.comm]
  let F : Fin 15 → V := fun z =>
    bracketTable (a3LeviColour x) (a3LeviColour y) z • ρ.op z (r + s) v
  have hsub : ∑ z ∈ Finset.univ.image a3LeviColour, F z = ∑ z, F z := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz
    have hnot : z ∉ Set.range a3LeviColour := by
      simpa using hz
    simp [F, a3Levi_bracket_outside x y z hnot]
  rw [← hsub]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z _
    simp [F, a3Levi_bracket_compat]
  · intro z _ z' _ heq
    exact a3LeviColour_injective heq

/-- The standard eight-colour Levi current module on the original carrier. -/
def a3LeviCurrent : CurrentModule VOA.AffineSl3.bracketTable V where
  op x r := ρ.op (a3LeviColour x) r
  comm := a3Levi_comm ρ

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3Levi_comm
#print axioms VOA.DeligneAudit.A3Sector.a3LeviCurrent
