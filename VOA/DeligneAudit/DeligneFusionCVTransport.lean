import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.NoncommRing

/-!
# A square transport identity for the A₂ CV calculations

This file proves only an elementary endomorphism lemma.  If `Z = X * Y - Y * X` commutes
with `X`, and `Y²` kills `u`, `X u`, and `X² u`, then `Z²` kills `u`.  The proof applies
the double commutator identity `ad X (ad X (Y²)) = 2 Z²` to `u`.

These hypotheses must still be established in each intended CV module.  This file does not
construct a CV kernel map or prove a fusion dimension bound.  No commutation hypothesis
between `Y` and `Z` is needed for this square identity.
-/

namespace VOA.DeligneAudit.CVTransport

section Ring

variable {R : Type*} [Ring R]

/-- A double commutator with `Y²`, when `ad X Y = Z` and `ad X Z = 0`. -/
theorem double_commutator_square (X Y Z : R)
    (hXY : X * Y - Y * X = Z) (hXZ : X * Z = Z * X) :
    X * (X * (Y * Y) - (Y * Y) * X) - (X * (Y * Y) - (Y * Y) * X) * X =
      Z * Z + Z * Z := by
  have hY2 : X * (Y * Y) - (Y * Y) * X = Z * Y + Y * Z := by
    rw [← hXY]
    noncomm_ring
  rw [hY2]
  calc
    X * (Z * Y + Y * Z) - (Z * Y + Y * Z) * X =
        (X * Z - Z * X) * Y + Z * (X * Y - Y * X) +
          (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by noncomm_ring
    _ = Z * Z + Z * Z := by rw [hXY, hXZ]; simp

end Ring

section Endomorphism

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Transport square annihilation across a central commutator.

The assumptions are explicit annihilation statements on three successive `X`-descendants.
They are not inferred from a current-module presentation here. -/
theorem square_kill_of_commutator [CharZero K] (X Y Z : Module.End K V)
    (hXY : X * Y - Y * X = Z) (hXZ : X * Z = Z * X) (u : V)
    (h0 : (Y ^ 2) u = 0) (h1 : (Y ^ 2) (X u) = 0)
    (h2 : (Y ^ 2) ((X ^ 2) u) = 0) : (Z ^ 2) u = 0 := by
  have h := congrArg (fun T : Module.End K V => T u)
    (double_commutator_square X Y Z hXY hXZ)
  have h0' : Y (Y u) = 0 := by simpa only [pow_two, Module.End.mul_apply] using h0
  have h1' : Y (Y (X u)) = 0 := by simpa only [pow_two, Module.End.mul_apply] using h1
  have h2' : Y (Y (X (X u))) = 0 := by simpa only [pow_two, Module.End.mul_apply] using h2
  have hz : (Z ^ 2) u + (Z ^ 2) u = 0 := by
    simpa only [pow_two, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      h0', h1', h2', map_zero, sub_zero, zero_sub, neg_zero] using h.symm
  have htwo : (2 : K) • ((Z ^ 2) u) = 0 := by simpa only [two_smul] using hz
  have htwo_ne : (2 : K) ≠ 0 := Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0)
  have hh := congrArg (fun v : V => (2 : K)⁻¹ • v) htwo
  simpa only [smul_smul, inv_mul_cancel₀ htwo_ne, one_smul,
    smul_zero] using hh

end Endomorphism

end VOA.DeligneAudit.CVTransport

section AxiomAudit
#print axioms VOA.DeligneAudit.CVTransport.double_commutator_square
#print axioms VOA.DeligneAudit.CVTransport.square_kill_of_commutator
end AxiomAudit
