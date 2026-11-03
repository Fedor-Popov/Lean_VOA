/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.LatticeOrthoFrame
import VOA.Examples.HeisenbergNFock

/-!
# The charge oscillators `α(m)` of the general lattice VOA and their Heisenberg bracket

The genuinely-new rank-`n` ingredient of the general lattice VOA: the oscillator attached
to a lattice charge `α ∈ L`.  The ambient rank-`r` Fock oscillators `HeisenbergN.oscN (rank L) 1`
are **orthonormal** (`[aᵃₘ, aᵇₙ] = m δ^{ab} δ_{m+n,0}`), so we assemble `α(m)` from them using the
real orthonormal frame coordinates `orthCoord α` (`Foundations.LatticeOrthoFrame`):

  `chargeOsc α m = α(m) := ∑ₐ (orthCoordα ₐ : ℂ) · aₐ(m)`.

The payoff (`chargeOsc_comm`) is the **metric-carrying Heisenberg relation**

  `[α(m), β(n)] = ⟨α,β⟩ · m · δ_{m+n,0} · id`,

which reduces via `oscN_comm` (the `δ^{ab}` collapses the double sum) to the frame identity
`orthCoord_inner : ∑ₐ orthCoordα ₐ orthCoordβ ₐ = ⟨α,β⟩`.  This is the relation that will drive
every locality sign of the charge-`α` vertex operators, with the odd-pairing sign supplied by
`latticeCocycle_comm` (`ε(α,β)ε(β,α) = (−1)^{⟨α,β⟩}`).

## References
* FLM Ch. 8; Gannon §5.2.2, (3.2.12a).
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-! ## Reconciling the two rank indices `rank L` and `latRank L` -/

/-- The two lattice ranks agree: `rank L = Module.finrank ℤ L = Fintype.card (ChooseBasisIndex) =
latRank L`. -/
theorem rank_eq_latRank : rank L = latRank L :=
  Module.finrank_eq_card_chooseBasisIndex ℤ L.carrier

/-- The canonical identification `Fin (rank L) ≃ Fin (latRank L)` used to index the frame
coordinates by the ambient Fock directions. -/
noncomputable def rankEquiv : Fin (rank L) ≃ Fin (latRank L) := finCongr (rank_eq_latRank L)

/-! ## The charge oscillators -/

/-- The **charge-`α` oscillator** `α(m) = ∑ₐ (orthCoordα ₐ) · aₐ(m)` on the rank-`L` Fock space,
built from the orthonormal frame coordinates and the ambient unit (`k = 1`) oscillators. -/
noncomputable def chargeOsc (α : L.carrier) (m : ℤ) :
    Module.End ℂ (HeisenbergN.FockN (rank L)) :=
  ∑ a : Fin (rank L), (orthCoord L α (rankEquiv L a) : ℂ) • HeisenbergN.oscN (rank L) 1 a m

/-- **Annihilation modes kill the vacuum**: `α(m) Ω = 0` for `m ≥ 0` (each `aₐ(m)` does, by
`oscN_vacuum`).  The creation-vs-annihilation split of the charge field will build on this. -/
theorem chargeOsc_vacuum (α : L.carrier) (m : ℤ) (hm : 0 ≤ m) :
    chargeOsc L α m (HeisenbergN.vacuumN (rank L)) = 0 := by
  simp only [chargeOsc, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    HeisenbergN.oscN_vacuum (rank L) 1 _ m hm, smul_zero, Finset.sum_const_zero]

/-- The euclidean inner product of the frame coordinates, reindexed by the ambient directions,
is the lattice pairing (cast to `ℂ`): `∑ₐ orthCoordα(eₐ) orthCoordβ(eₐ) = ⟨α,β⟩`. -/
theorem sum_orthCoord_rankEquiv (hPos : L.PosDef) (α β : L.carrier) :
    ∑ a : Fin (rank L),
        (orthCoord L α (rankEquiv L a) : ℂ) * (orthCoord L β (rankEquiv L a) : ℂ)
      = ((L.form α β : ℤ) : ℂ) := by
  simp only [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum,
    Equiv.sum_comp (rankEquiv L) (fun c => orthCoord L α c * orthCoord L β c),
    orthCoord_inner L hPos α β]
  push_cast
  ring

/-- **The metric-carrying Heisenberg bracket of the charge oscillators**:
`[α(m), β(n)] = ⟨α,β⟩ · m · δ_{m+n,0} · id`.  The lattice form enters through the frame
(`orthCoord_inner`); the `δ^{ab}` of `oscN_comm` collapses the double sum. -/
theorem chargeOsc_comm (hPos : L.PosDef) (α β : L.carrier) (m n : ℤ) :
    chargeOsc L α m * chargeOsc L β n - chargeOsc L β n * chargeOsc L α m
      = (if m + n = 0 then ((L.form α β : ℤ) : ℂ) * (m : ℂ) else 0) • LinearMap.id := by
  -- Step 1a: expand `α(m)·β(n)` into a double sum of scaled oscillator products.
  have e1 : chargeOsc L α m * chargeOsc L β n
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          ((orthCoord L α (rankEquiv L a) : ℂ) * (orthCoord L β (rankEquiv L b) : ℂ)) •
            (HeisenbergN.oscN (rank L) 1 a m * HeisenbergN.oscN (rank L) 1 b n) := by
    simp only [chargeOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  -- Step 1b: expand `β(n)·α(m)`, reindexed so both sums share the `(a,b)` order.
  have e2 : chargeOsc L β n * chargeOsc L α m
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          ((orthCoord L α (rankEquiv L a) : ℂ) * (orthCoord L β (rankEquiv L b) : ℂ)) •
            (HeisenbergN.oscN (rank L) 1 b n * HeisenbergN.oscN (rank L) 1 a m) := by
    simp only [chargeOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [mul_comm (orthCoord L β (rankEquiv L b) : ℂ) (orthCoord L α (rankEquiv L a) : ℂ)]
  -- Step 1c: assemble the commutator as a double sum of scaled oscillator brackets.
  have hexpand : chargeOsc L α m * chargeOsc L β n - chargeOsc L β n * chargeOsc L α m
      = ∑ a : Fin (rank L), ∑ b : Fin (rank L),
          ((orthCoord L α (rankEquiv L a) : ℂ) * (orthCoord L β (rankEquiv L b) : ℂ)) •
            (HeisenbergN.oscN (rank L) 1 a m * HeisenbergN.oscN (rank L) 1 b n
              - HeisenbergN.oscN (rank L) 1 b n * HeisenbergN.oscN (rank L) 1 a m) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_sub]
  -- Step 2: evaluate each oscillator bracket via `oscN_comm` (level `k = 1`, so `m·1 = m`).
  have hbr : ∀ a b : Fin (rank L),
      HeisenbergN.oscN (rank L) 1 a m * HeisenbergN.oscN (rank L) 1 b n
          - HeisenbergN.oscN (rank L) 1 b n * HeisenbergN.oscN (rank L) 1 a m
        = (if a = b ∧ m + n = 0 then (m : ℂ) else 0) • LinearMap.id := by
    intro a b
    rw [HeisenbergN.oscN_comm (rank L) 1 a b m n, mul_one]
  rw [hexpand]
  simp only [hbr, smul_smul]
  by_cases hP : m + n = 0
  · -- `m + n = 0`: collapse the inner sum at `b = a`, then use the frame inner product.
    rw [if_pos hP]
    simp only [← Finset.sum_smul]
    congr 1
    have hb : ∀ a : Fin (rank L),
        (∑ b : Fin (rank L),
          ((orthCoord L α (rankEquiv L a) : ℂ) * (orthCoord L β (rankEquiv L b) : ℂ))
            * (if a = b ∧ m + n = 0 then (m : ℂ) else 0))
          = ((orthCoord L α (rankEquiv L a) : ℂ) * (orthCoord L β (rankEquiv L a) : ℂ))
              * (m : ℂ) := by
      intro a
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb])
          (fun h => absurd (Finset.mem_univ a) h)]
      simp [hP]
    simp only [hb]
    rw [← Finset.sum_mul, sum_orthCoord_rankEquiv L hPos α β]
  · -- `m + n ≠ 0`: every summand vanishes.
    rw [if_neg hP, zero_smul]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    simp [hP]

end VOA.LatGen
