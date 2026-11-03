import VOA.Classification.COne.OrbPos5Locality
import VOA.Classification.COne.OrbPos4Untwist

/-!
# Assembly of the concrete shifted lattice fields

All fields and all structure axioms other than twisted Jacobi are constructed
and proved. `ShiftedProductFormula` names the ONE remaining coefficient
identity for these explicit fields. The module constructor below is
CONDITIONAL on that identity. It is not an unconditional existence theorem
for non-dual shifts, nor a classification of arbitrary twisted modules.
-/

namespace VOA.Classification.COne.OrbPos5
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 LatMod TwistedReduction

/-- The remaining twisted iterate identity for the explicitly constructed
fields. Unlike an existence residual this has no unspecified operators,
grading, transport map, or module structure. -/
def ShiftedProductFormula {n : ℕ} (hn : 0 < n) (a j : ℤ) : Prop :=
  ∀ (r : ℕ) (u : Space), u ∈ (shiftAut n a).twistedEigenspace n r →
    ∀ (v : Space) (e : ℤ), 0 ≤ e → e < n → ∀ (ℓ s : ℤ) (x : Space),
      mode (Fld.prod ℓ
        (rescFld hn (shiftedY_truncation hn a j u) (-(r : ℤ)))
        (rescFld hn (shiftedY_truncation hn a j v) e)).1 s x =
      ∑ᶠ d : ℕ, cbinom ((-(r : ℤ) : ℂ) / n) d •
        shiftedY n a j ((V2m 1 le_rfl).smul u (ℓ+d) v)
          ((n : ℤ)*(s-d)-(r : ℤ)+e) x

/-- The proven locality stage reduces Jacobi to the explicit iterate identity. -/
theorem shiftedJacobi_of_productFormula {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (hpf : ShiftedProductFormula hn a j) :
    TwistedJacobi (shiftAut n a) n (shiftedY n a j) := by
  apply twistedJacobi_of_local_pf (shiftAut n a) (shiftedY n a j) hn
    (shiftedY_truncation hn a j) (fun r => -(r : ℤ)) (fun r => by simp)
    (fun r u _ v e _ _ => shiftedY_local hn a j (-(r : ℤ)) e u v)
  simpa only [ShiftedProductFormula, sub_eq_add_neg, Int.cast_neg] using hpf

/-- CONDITIONAL constructor: the concrete fields become a genuine
`TwistedModule` once their remaining product identity is proved. -/
noncomputable def latticeShiftedTwistedModule {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (hpf : ShiftedProductFormula hn a j) : TwistedModule (shiftAut n a) n Space where
  YM := shiftedY n a j
  vacuum_YM := shiftedY_vacuum hn a j
  truncation := shiftedY_truncation hn a j
  support := shiftedY_support hn a j
  jacobi := shiftedJacobi_of_productFormula hn a j hpf
  weight := energyGrade n a j
  isInternal := energyGrade_isInternal n a j
  L0_weight := (shiftedY_ordinaryGrading hn a j).2.2.1
  finrank := energyGrade_finiteDimensional hn a j
  boundedBelow := ⟨0, fun _ h => energyGrade_nonneg n a j h⟩

theorem latticeShiftedTwistedModule_irreducible {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (hpf : ShiftedProductFormula hn a j) :
    TwistedIrreducible (latticeShiftedTwistedModule hn a j hpf) := by
  refine ⟨(latticeModule_isIrreducible 1 le_rfl j).1, ?_⟩
  exact shiftedY_irreducible hn a j

/-- Existence of the energy realization for the constructed family, still
conditional on the displayed product formula. No completeness is claimed. -/
theorem latticeShiftedTwistedModule_energyRealization {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (hpf : ShiftedProductFormula hn a j) :
    LatticeEnergyRealization (latticeShiftedTwistedModule hn a j hpf) a := by
  refine ⟨j, LinearEquiv.refl ℂ Space, ?_⟩
  intro x
  exact congrArg (fun F : Module.End ℂ Space => F x) (shiftedY_conformal hn a j)

/-- An unconditional check on the full Jacobi identity at zero shift.
This is a base case only; it does not settle a non-dual shift. -/
theorem shiftedJacobi_zero (j : ℤ) :
    TwistedJacobi (shiftAut 1 0) 1 (shiftedY 1 0 j) := by
  have hg : shiftAut 1 0 = 1 := by
    have hu : torusUnit 1 0 = 1 := by
      apply Units.ext
      simp [torusUnit, phase]
    rw [shiftAut, hu, map_one]
    rfl
  rw [hg, shiftedY_zero_one]
  exact twistedJacobi_of_twistedModule (latticeModule 1 le_rfl j).toTwisted

end VOA.Classification.COne.OrbPos5
