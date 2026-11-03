import VOA.Huang.DLNLiftingCharacters
import Mathlib.GroupTheory.Commutator.Basic

/-!
# A precise group-theoretic boundary for DLN lifting

The missing arithmetic statement is `RelativeCommutatorCongruence`:
`Γ(12N) ≤ [SL₂(ℤ), Γ(N)]` for positive `N`. It is left as an explicit
proposition, not an axiom or an asserted theorem. The implication to the exact
`DLNBridge.MatrixDLNLifting` target is proved below.

Projective congruence makes the image of `Γ(N)` central, so its commutators
with the full modular group vanish. This reduction works in dimension zero
as well, with no scalar cancellation or nonemptiness assumption.
-/

namespace VOA.Huang.DLNLifting

open VOA.Huang.DLN VOA.Huang.DLNBridge CongruenceSubgroup
open scoped commutatorElement

/-- The arithmetic relative-commutator containment needed for DLN lifting.
This is a separate, currently unproved group-theoretic contract. -/
def RelativeCommutatorCongruence : Prop :=
  ∀ N : ℕ, 0 < N → Gamma (12 * N) ≤ ⁅(⊤ : Subgroup SL2Z), Gamma N⁆

/-- Scalar images of the principal congruence subgroup commute with all images. -/
theorem projective_commute {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hp : MatrixProjectiveCongruence ρ N)
    (g h : SL2Z) (hh : h ∈ Gamma N) : Commute (ρ g) (ρ h) := by
  obtain ⟨c, hc⟩ := hp h hh
  change ρ g * ρ h = ρ h * ρ g
  simp only [hc, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

/-- Projective congruence kills the full relative commutator subgroup. -/
theorem relativeCommutator_le_ker {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hp : MatrixProjectiveCongruence ρ N) :
    ⁅(⊤ : Subgroup SL2Z), Gamma N⁆ ≤ ρ.toHomUnits.ker := by
  apply Subgroup.commutator_le.mpr
  intro g _ h hh
  change ρ.toHomUnits ⁅g, h⁆ = 1
  rw [map_commutatorElement]
  apply Commute.commutator_eq
  change ρ.toHomUnits g * ρ.toHomUnits h = ρ.toHomUnits h * ρ.toHomUnits g
  apply Units.ext
  exact projective_commute ρ hp g h hh

/-- The pure group-theoretic contract implies exactly the requested matrix lifting theorem. -/
theorem matrixDLNLifting_of_relativeCommutator
    (hgroup : RelativeCommutatorCongruence) : MatrixDLNLifting := by
  intro κ _ _ ρ N hN hp γ hγ
  have h := relativeCommutator_le_ker ρ hp (hgroup N hN hγ)
  exact congrArg (fun a : (Matrix κ κ ℂ)ˣ => (a : Matrix κ κ ℂ)) h

section ScalarCharacter

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

omit [Fintype κ] in
/-- A scalar matrix has a unique scalar in positive dimension. -/
theorem scalar_injective : Function.Injective (fun c : ℂ => c • (1 : Matrix κ κ ℂ)) := by
  intro c d h
  let i : κ := Classical.arbitrary κ
  have hi := congrArg (fun M : Matrix κ κ ℂ => M i i) h
  simpa using hi

/-- The scalar coefficient on the principal congruence subgroup as a complex-valued hom. -/
noncomputable def scalarCharacterComplex (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ}
    (hp : MatrixProjectiveCongruence ρ N) : Gamma N →* ℂ where
  toFun γ := ρ γ (Classical.arbitrary κ) (Classical.arbitrary κ)
  map_one' := by simp
  map_mul' x y := by
    obtain ⟨c, hc⟩ := hp x x.property
    obtain ⟨d, hd⟩ := hp y y.property
    simp [Subgroup.coe_mul, map_mul, hc, hd, mul_comm]

/-- On a nonempty index set the scalar coefficients automatically lie in `ℂˣ`. -/
noncomputable def scalarCharacter (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ}
    (hp : MatrixProjectiveCongruence ρ N) : Gamma N →* ℂˣ :=
  (scalarCharacterComplex ρ hp).toHomUnits

/-- The unit-valued scalar character recovers the original representation on `Γ(N)`. -/
theorem scalarCharacter_spec (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ}
    (hp : MatrixProjectiveCongruence ρ N) (γ : Gamma N) :
    ρ γ = (scalarCharacter ρ hp γ : ℂ) • (1 : Matrix κ κ ℂ) := by
  obtain ⟨c, hc⟩ := hp γ γ.property
  simp [scalarCharacter, scalarCharacterComplex, hc]

/-- Conjugation by a modular-group element preserves the principal congruence subgroup. -/
def gammaConjugate {N : ℕ} (g : SL2Z) (γ : Gamma N) : Gamma N :=
  ⟨g * γ * g⁻¹, (Gamma_normal N).conj_mem γ γ.property g⟩

/-- The scalar character is invariant under conjugation by the full modular group. -/
theorem scalarCharacter_conjugate (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ}
    (hp : MatrixProjectiveCongruence ρ N) (g : SL2Z) (γ : Gamma N) :
    scalarCharacter ρ hp (gammaConjugate g γ) = scalarCharacter ρ hp γ := by
  apply Units.ext
  apply scalar_injective (κ := κ)
  dsimp only
  rw [← scalarCharacter_spec, ← scalarCharacter_spec]
  change ρ (g * γ * g⁻¹) = ρ γ
  rw [map_mul, map_mul, (projective_commute ρ hp g γ γ.property).eq, mul_assoc,
    ← map_mul, mul_inv_cancel, map_one, mul_one]

/-- The determinant bound on the canonical scalar character. -/
theorem scalarCharacter_pow_card_mul_twelve (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ}
    (hp : MatrixProjectiveCongruence ρ N) (γ : Gamma N) :
    scalarCharacter ρ hp γ ^ (Fintype.card κ * 12) = 1 := by
  apply Units.ext
  exact scalar_pow_card_mul_twelve ρ γ (scalarCharacter_spec ρ hp γ)

end ScalarCharacter

end VOA.Huang.DLNLifting
