import VOA.Classification.COne.OrbPosLowest
import VOA.Moonshine.LatticeTwistedGeneralModule
import VOA.Moonshine.LatticeTwistedGeneralRestriction
import VOA.Moonshine.LatticeTwistedGeneralTops

/-!
# Positive weights of the existing order-two FLM sectors

The rank must be positive. No completeness claim, conjugacy transport, or
construction for twists of order three, four, or five is made here.
-/

namespace VOA.Classification.COne.OrbPos
open VOA VOA.Moonshine VOA.Moonshine.LatticeTwisted
open VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwistedGeneral
open VOA.IntegralLattice

/-- A nonzero weight space of the actual FLM oscillator/charge carrier occurs
at an oscillator level, hence has the explicit lower bound `rank/16`. -/
theorem flm_weight_lower_bound (r : ℕ) (T : Type*) [AddCommGroup T] [Module ℂ T]
    {α : ℂ} (hα : weightLT r T α ≠ ⊥) : (r : ℝ) / 16 ≤ α.re := by
  have hex : ∃ d : ℕ, ((levelT r d : ℚ) : ℂ) = α := by
    by_contra h
    push Not at h
    exact hα (weightLT_eq_bot r T h)
  obtain ⟨d, rfl⟩ := hex
  rw [Complex.ratCast_re, levelT]
  push_cast
  have hd : (0 : ℝ) ≤ d := d.cast_nonneg
  linarith

theorem latticeTwistedModule_weights_positive (L : IntegralLattice.{0})
    (he : L.Even) (C : TwistedCharge L) (hp : L.PosDef)
    [FiniteDimensional ℂ C.carrier] (hr : 0 < rank L) {α : ℂ}
    (hα : (latticeTwistedModule L he C hp).weight α ≠ ⊥) : 0 < α.re := by
  have hb := flm_weight_lower_bound (rank L) (Space L he C) hα
  have hrR : (0 : ℝ) < rank L := by exact_mod_cast hr
  exact lt_of_lt_of_le (by positivity) hb

/-- The same positivity holds after the existing restriction to the fixed VOA. -/
theorem fixedOrdModule_weights_positive (L : IntegralLattice.{0})
    (he : L.Even) (C : TwistedCharge L) (hp : L.PosDef)
    [FiniteDimensional ℂ C.carrier] (hr : 0 < rank L) {α : ℂ}
    (hα : (fixedOrdModule (latticeTwistedModule L he C hp)).weight α ≠ ⊥) :
    0 < α.re :=
  latticeTwistedModule_weights_positive L he C hp hr hα

/-- An explicit bound on both FLM parity pieces, including the odd shift. -/
theorem parityModule_weight_lower_bound (L : IntegralLattice.{0})
    (he : L.Even) (C : TwistedCharge L) (hp : L.PosDef)
    [FiniteDimensional ℂ C.carrier] (odd : Bool) {α : ℂ}
    (hα : (parityModule L he C hp odd).weight α ≠ ⊥) :
    (rank L : ℝ) / 16 + (odd.toNat : ℝ) / 2 ≤ α.re := by
  obtain ⟨d, rfl, hd⟩ := parityModule_weight_support L he C hp odd α hα
  have hle : odd.toNat ≤ d := by
    cases odd
    · simp
    · simp only [Bool.toNat_true] at *
      obtain ⟨k, hk⟩ := hd
      omega
  rw [Complex.ratCast_re, levelT]
  push_cast
  have : (odd.toNat : ℝ) ≤ d := by exact_mod_cast hle
  linarith

/-- Positivity passes to any injectively and weight-preservingly embedded
sector. This does not assume that all irreducibles have such embeddings. -/
theorem positive_weights_of_injective
    {V M T : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    {W : VertexOperatorAlgebra V} (N : OrdVModule W M)
    (w : ℂ → Submodule ℂ T) (f : M →ₗ[ℂ] T) (hf : Function.Injective f)
    (hweight : ∀ α x, x ∈ N.weight α → f x ∈ w α)
    (hpos : ∀ α, w α ≠ ⊥ → 0 < α.re) :
    ∀ α, N.weight α ≠ ⊥ → 0 < α.re := by
  intro α hα
  apply hpos α
  intro hz
  apply hα
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hfx := hweight α x hx
  rw [hz, Submodule.mem_bot] at hfx
  exact hf (hfx.trans (map_zero f).symm)

end VOA.Classification.COne.OrbPos
