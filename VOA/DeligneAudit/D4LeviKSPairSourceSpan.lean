import VOA.DeligneAudit.D4LeviKSSymmetricShiftAlgebra

/-! Higher-orbit containment for the partial sources of iterated PAIR. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- All radical words at partial PAIR keys before the last f₃ mode has
    transferred. The `nx` and `ny` counts record X-to-U' and U-to-Y steps. -/
def pairPartialSourceSpan (a b c d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ nx ny : ℕ, ∃ l : List (Fin 6 × ℕ),
    nx ≤ a + b ∧ nx + ny < b ∧
      wordKey l = pairPartialKey a b c d nx ny ∧
        u = radicalWord ρ w l}

/-- Every partial source is strictly above the final symmetric key. -/
theorem pairPartialSourceSpan_le_higher (a b c d : ℕ) :
    pairPartialSourceSpan ρ w a b c d ≤
      higherOrbit ρ w m (pairFinalKey a b c d) := by
  rw [pairPartialSourceSpan, Submodule.span_le]
  rintro u ⟨nx, ny, l, hnx, hstep, hkey, rfl⟩
  have hless := pairPartialKey_higher m a b c d nx ny hnx hstep
  rw [← hkey] at hless
  exact keyOrbit_le_higher ρ w m (pairFinalKey a b c d)
    (wordKey l) hless
      (keyLayer_le_orbit ρ w (wordKey l) (radicalWord_mem_key ρ w l))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairPartialSourceSpan_le_higher
