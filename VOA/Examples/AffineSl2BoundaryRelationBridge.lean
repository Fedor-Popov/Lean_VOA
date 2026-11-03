/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BoundaryHarmonicSymbol
import VOA.Examples.AffineSl2AdmissiblePrimitive

/-!
# The weak boundary relation bridge

Maximal-ideal generation is unnecessary for the relation surjection. Every
boundary candidate already lies in the actual maximal ideal. The sole remaining
uniform relation input is nonvanishing of its universal C₂ symbol. The explicit
first two candidates give unconditional relation surjections.
-/
namespace VOA.AffineSl2BoundarySingularFamily
open AffineVOA AffineVOA.Inst AffineVOA.Strong
open VertexOperatorAlgebra AffineSl2BoundaryC2 QuasiLisseSl2 Sl2Pres Sl2Symbol
open Sl2Sing85 Sl2Symbol85
noncomputable section

/-- Every actual positive-weight boundary primitive belongs to the maximal ideal,
without a maximal-generation hypothesis. -/
theorem Candidate.mem_maxGradedIdeal {k : ℂ} {n : ℕ} (C : Candidate k n) :
    C.vector ∈ QuotVOA.maxGradedIdeal (affineSl2VOA_closed k C.noncritical) := by
  exact SimpleQuot.mem_maxGradedIdeal_of_stronglySingular
    (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k C.noncritical)
    (affineSl2_qp k C.noncritical)
    (isStronglySingular_of_SingP k C.noncritical C.positiveSingular C.nonzero
      (by exact_mod_cast denominator_pos n) C.homogeneous)

/-- The actual simple quotient current-symbol map. -/
def simpleSymbol {k : ℂ} {n : ℕ} (C : Candidate k n) :
    SymSl2 →ₐ[ℂ] A₂ (QuotVOA.maxQuotientVOA (affineSl2VOA_closed k C.noncritical)) :=
  quotientSymbol k C.noncritical _ (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _)

theorem simpleSymbol_surjective {k : ℂ} {n : ℕ} (C : Candidate k n) :
    Function.Surjective (simpleSymbol C) := quotientSymbol_surjective _ _ _ _ _

/-- A single computed highest symbol gives all three actual quotient relations. -/
theorem Candidate.boundaryIdeal_le_kernel_of_highestSymbol {k : ℂ} {n : ℕ}
    (C : Candidate k n) (c : ℂ) (hc : c ≠ 0)
    (hsymbol : mk₂ (affineSl2VOA_closed k C.noncritical) C.vector =
      c • symbolAlg k C.noncritical (eSym * casSym ^ n)) :
    boundaryIdeal n ≤ RingHom.ker (simpleSymbol C) := by
  exact boundaryIdeal_le_ker_quotientSymbol_of_highestSymbol k C.noncritical n _
    (QuotVOA.maxGradedIdeal_isIdeal _) (QuotVOA.maxGradedIdeal_isGradedIdeal _)
    C.vector C.mem_maxGradedIdeal c hc hsymbol

/-- Harmonic classification reduces the uniform relation gate to literal C₂
nonvanishing, with all other inputs proved for the actual candidate. -/
theorem Candidate.boundaryIdeal_le_kernel_of_symbol_ne_zero {k : ℂ} {n : ℕ}
    (C : Candidate k n)
    (hne : mk₂ (affineSl2VOA_closed k C.noncritical) C.vector ≠ 0) :
    boundaryIdeal n ≤ RingHom.ker (simpleSymbol C) := by
  obtain ⟨c, hc, hs⟩ := C.exists_highestSymbol_of_symbol_ne_zero hne
  exact C.boundaryIdeal_le_kernel_of_highestSymbol c hc hs

/-- The first boundary algebra genuinely maps onto the actual simple C₂ algebra. -/
theorem boundaryIdeal43_le_kernel :
    boundaryIdeal 1 ≤ RingHom.ker (simpleSymbol candidate43) := by
  apply candidate43.boundaryIdeal_le_kernel_of_highestSymbol 9 (by norm_num)
  change mk₂ (affineSl2VOA_closed (-4 / 3 : ℂ) admLevel_noncritical)
    Sl2Sing.sl2Singular = 9 • symbolAlg _ _ (eSym * casSym ^ 1)
  rw [map_mul, map_pow, pow_one, symbolAlg_eSym, symbolAlg_casSym]
  exact mk₂_sl2Singular_casimir

/-- The second boundary algebra has the same unconditional relation containment. -/
theorem boundaryIdeal85_le_kernel :
    boundaryIdeal 2 ≤ RingHom.ker (simpleSymbol candidate85) := by
  apply candidate85.boundaryIdeal_le_kernel_of_highestSymbol 625 (by norm_num)
  change mk₂ (affineSl2VOA_closed (-8 / 5 : ℂ) level85_noncritical)
    Sl2Sing85.sl2Singular85 = 625 • symbolAlg _ _ (eSym * casSym ^ 2)
  rw [map_mul, map_pow, symbolAlg_eSym, symbolAlg_casSym]
  exact mk₂_sl2Singular85_casimir_sq

/-- Factor the actual simple current-symbol map through the boundary presentation. -/
def boundaryC2Map {k : ℂ} {n : ℕ} (C : Candidate k n)
    (hrel : boundaryIdeal n ≤ RingHom.ker (simpleSymbol C)) :
    (SymSl2 ⧸ boundaryIdeal n) →ₐ[ℂ]
      A₂ (QuotVOA.maxQuotientVOA (affineSl2VOA_closed k C.noncritical)) :=
  Ideal.Quotient.liftₐ _ (simpleSymbol C) (fun p hp => hrel hp)

theorem boundaryC2Map_surjective {k : ℂ} {n : ℕ} (C : Candidate k n)
    (hrel : boundaryIdeal n ≤ RingHom.ker (simpleSymbol C)) :
    Function.Surjective (boundaryC2Map C hrel) := by
  intro y
  obtain ⟨p, hp⟩ := simpleSymbol_surjective C y
  exact ⟨Ideal.Quotient.mk _ p, hp⟩

end
end VOA.AffineSl2BoundarySingularFamily
