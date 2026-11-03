/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2UniversalC2PBW
import VOA.Examples.WakimotoFree

/-!
# Affine `sl₂` PBW reduced to Wakimoto polynomial triangularity

`AffineSl2UniversalC2PBW` proves that the ordered negative-current states span the universal
affine vacuum module and that their linear independence is equivalent to the named `PBWBasis`
package.  This file connects that independence statement to the already
formalized Wakimoto free-field representation.

The evaluation `Wak.valW` kills the vacuum left ideal, so it descends to a linear map

`vacuumToWak : V^k(sl₂) → MvPolynomial (Fin 3 × ℕ) ℂ`.

It intertwines every Chevalley current mode with `Wak.Jw`.  Therefore it is enough to prove that
the images of the ordered creation states are linearly independent as explicit polynomials.
That final assertion is a concrete triangularity theorem in a polynomial ring; it does not
mention a quotient, a universal enveloping algebra, or a spanning condition.

## Status

The descent map and both reduction theorems are proved without new axioms.  The independence
`LinearIndependent ℂ (wakimotoOrderedCreationState k)` is proved downstream as
`AffineSl2WakimotoLiLeading.wakimotoOrderedCreationState_linearIndependent`, giving
`AffineSl2WakimotoLiLeading.affineSl2PBWBasis` for `k + 2 ≠ 0`.  (Mathlib has no PBW theorem
for universal enveloping algebras, and `PBWPrinciple.inducedBottom` does not imply this
independence, hence the leading-monomial route through the Wakimoto polynomials.)
-/

namespace VOA
namespace AffineSl2PBWWakimotoReduction

open VOA.AffineLie
open VOA.AffineVOA
open VOA.AffineSl2UniversalC2PBW

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The Wakimoto vacuum evaluation descended from `U(sl₂^)` to the universal affine vacuum
module.  The scalar restriction is only the standard adapter between the left-ideal quotient and
its underlying complex-vector-space quotient. -/
def vacuumToWak : WakModule k →ₗ[ℂ] Wak.WakFock :=
  (((vacuumIdeal kappaForm kappaForm_isInvariant k).restrictScalars ℂ).liftQ
      (Wak.valW k hk) (fun _ hw ↦ LinearMap.mem_ker.mpr (Wak.valW_vacuumIdeal k hk _ hw))).comp
    (Submodule.Quotient.restrictScalarsEquiv ℂ
      (vacuumIdeal kappaForm kappaForm_isInvariant k)).symm.toLinearMap

@[simp] theorem vacuumToWak_mk (w : Wak.UW) :
    vacuumToWak k hk (Submodule.Quotient.mk w) = Wak.valW k hk w := rfl

/-- The descended map sends the affine vacuum to the polynomial vacuum. -/
@[simp] theorem vacuumToWak_vacuum : vacuumToWak k hk (vacuumA k) = 1 := by
  rw [Wak.vacuumA_mk, vacuumToWak_mk, Wak.valW_one]

/-- The descended map intertwines each Chevalley current generator with its Wakimoto current. -/
theorem vacuumToWak_J (a : Fin 3) (m : ℤ) (v : WakModule k) :
    vacuumToWak k hk (J k a m v) = Wak.Jw k a m (vacuumToWak k hk v) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
    (vacuumIdeal kappaForm kappaForm_isInvariant k) v
  rw [Wak.J_mk, vacuumToWak_mk, vacuumToWak_mk, Wak.valW_gen]

/-- The colour-and-depth list underlying an ordered PBW exponent. -/
def orderedPBWColorWord (mu : ((Fin 3 ×ₗ ℕ) →₀ ℕ)) : List (Fin 3 × ℕ) :=
  (mu.support.sort (fun a b ↦ a ≤ b)).flatMap fun q ↦
    List.replicate (mu q) ((ofLex q).1, (ofLex q).2)

/-- The ordered creation state is the basis-coloured current word attached to its exponent. -/
theorem orderedCreationState_eq_wordStateA (mu : ((Fin 3 ×ₗ ℕ) →₀ ℕ)) :
    orderedCreationState k mu = wordStateA k (orderedPBWColorWord mu) := by
  rw [orderedCreationState, pbwWord]
  simpa [orderedPBWColorWord, List.map_flatMap, Pi.basisFun_apply, basis] using
    negWord_map_basis_eq_wordStateA k (orderedPBWColorWord mu)

/-- Evaluation of a basis-coloured negative-current word by the explicit Wakimoto currents. -/
def wakimotoWordState : List (Fin 3 × ℕ) → Wak.WakFock
  | [] => 1
  | (a, n) :: l => Wak.Jw k a (-((n : ℤ)) - 1) (wakimotoWordState l)

/-- The descended Wakimoto map evaluates every current word by the recursive polynomial model. -/
theorem vacuumToWak_wordStateA : ∀ l : List (Fin 3 × ℕ),
    vacuumToWak k hk (wordStateA k l) = wakimotoWordState k l
  | [] => by rw [wordStateA_nil, vacuumToWak_vacuum]; rfl
  | (a, n) :: l => by
      rw [wordStateA_cons, vacuumToWak_J, vacuumToWak_wordStateA l]
      rfl

/-- The image of an ordered affine creation state in the explicit Wakimoto polynomial Fock
space.  Its linear independence is
`AffineSl2WakimotoLiLeading.wakimotoOrderedCreationState_linearIndependent`. -/
def wakimotoOrderedCreationState : ((Fin 3 ×ₗ ℕ) →₀ ℕ) → Wak.WakFock :=
  fun mu ↦ wakimotoWordState k (orderedPBWColorWord mu)

/-- The concrete recursive polynomial family is exactly the image of the ordered creation
states under `vacuumToWak`. -/
theorem wakimotoOrderedCreationState_eq (mu : ((Fin 3 ×ₗ ℕ) →₀ ℕ)) :
    wakimotoOrderedCreationState k mu = vacuumToWak k hk (orderedCreationState k mu) := by
  rw [orderedCreationState_eq_wordStateA, vacuumToWak_wordStateA]
  rfl

/-- Linear independence of the explicit Wakimoto images implies ordinary affine PBW.  Spanning
does not appear as a hypothesis because it is already proved by current straightening. -/
theorem pbwBasis_of_wakimotoOrderedCreationState_linearIndependent
    (hk : k + 2 ≠ 0)
    (hli : LinearIndependent ℂ (wakimotoOrderedCreationState k)) :
    PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k := by
  rw [pbwBasis_iff_orderedCreationState_linearIndependent k]
  apply LinearIndependent.of_comp (vacuumToWak k hk)
  rw [show (⇑(vacuumToWak k hk) ∘ orderedCreationState k) =
      wakimotoOrderedCreationState k by
    funext mu
    exact (wakimotoOrderedCreationState_eq k hk mu).symm]
  exact hli

/-- The same concrete Wakimoto triangularity input proves injectivity of the universal `C₂`
symbol map. -/
theorem symbolAlg_injective_of_wakimotoOrderedCreationState_linearIndependent
    (hli : LinearIndependent ℂ (wakimotoOrderedCreationState k)) :
    Function.Injective (Sl2Pres.symbolAlg k hk) :=
  symbolAlg_injective_of_PBWBasis k hk
    (pbwBasis_of_wakimotoOrderedCreationState_linearIndependent k hk hli)

end
end AffineSl2PBWWakimotoReduction
end VOA

section AxiomAudit
#print axioms VOA.AffineSl2PBWWakimotoReduction.vacuumToWak_J
#print axioms VOA.AffineSl2PBWWakimotoReduction.vacuumToWak_wordStateA
#print axioms VOA.AffineSl2PBWWakimotoReduction.pbwBasis_of_wakimotoOrderedCreationState_linearIndependent
#print axioms VOA.AffineSl2PBWWakimotoReduction.symbolAlg_injective_of_wakimotoOrderedCreationState_linearIndependent
end AxiomAudit
