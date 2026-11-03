/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenEEMaster

/-!
# Same-sign mutual locality `Local Y(e^α) Y(e^β)` for `⟨α,β⟩ ≥ 0`

The vertex-operator-level assembly: the two orders of `Y(e^α,z₁)Y(e^β,z₂)` on a basis state differ
by the boson reordering sign `(-1)^{⟨α,β⟩}` (`shift_comm_P`) times the cocycle asymmetry
`(-1)^{⟨α,β⟩}` (`latticeCocycle_swap_sign`), whose product is `+1` — so the bracket vanishes and the
operators are mutually local (bound `0`, exact commutation).  This is the FLM cocycle mechanism the
`A₁` diagonal never exhibits.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-- Reduce `Local F G` (for the lattice module) to vanishing of the bracket on every basis state
`latStateGen p γ`.  Cross-charge lift of A₁'s `local_of_bracket_on_state`. -/
theorem local_of_bracket_on_state {F G : FormalDist (End ℂ (LatModuleGen L))}
    (h : ∀ (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)),
      bracketDist F G j k (latStateGen L p γ) = 0) : Local F G := by
  refine local_of_bracketDist_eq_zero ?_
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change bracketDist F G j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single γ a =>
          rw [(Finsupp.smul_single_one γ a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show (Finsupp.single γ (1 : ℂ) : L.carrier →₀ ℂ) = eGen L γ from rfl]
          rw [show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl, h, smul_zero]

/-- **The same-sign bracket vanishes on every basis state** (`⟨α,β⟩ ≥ 0`, bound `0`).  The two
operator orders' boson parts differ by `(-1)^{⟨α,β⟩}` (`shift_comm_P`) and their cocycle prefactors
by `(-1)^{⟨α,β⟩}` (`latticeCocycle_swap_sign`); the two signs cancel and the bracket vanishes. -/
theorem Yeαvec_sameSign_bracket_on_state (hEven : L.Even) (hPos : L.PosDef) (α β : L.carrier)
    (hsign : 0 ≤ L.form α β) (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)) :
    bracketDist (Yeαvec L α) (Yeαvec L β) j k (latStateGen L p γ) = 0 := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ, (P : ℤ) = L.form α β := ⟨(L.form α β).toNat, by omega⟩
  simp only [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Yeαvec_tmul, map_smul]
  -- boson-part equality via `shift_comm_P`, cocycle-part equality via `swap_sign`; the two signs cancel
  have hEE : EEVec L α (j - L.form α (β + γ)) (EEVec L β (k - L.form β γ) p)
      = (-1 : ℂ) ^ P • EEVec L β (k - L.form β (α + γ)) (EEVec L α (j - L.form α γ) p) := by
    rw [show j - L.form α (β + γ) = (j - L.form α γ) - P from by
          rw [map_add, hP]; ring,
      shift_comm_P L hPos α β P hP (j - L.form α γ) (k - L.form β γ) p,
      show k - L.form β γ - P = k - L.form β (α + γ) from by
        rw [map_add, hP, form_symm L β α]; ring]
  have hpp : (-1 : ℂ) ^ P * (-1 : ℂ) ^ P = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hsw : latticeCocycle L α β = (-1 : ℂ) ^ P * latticeCocycle L β α := by
    rw [latticeCocycle_swap_sign L hEven α β, ← hP, zpow_natCast]
  rw [hEE, latStateGen_smul_boson, show α + (β + γ) = β + (α + γ) from by abel,
    latticeCocycle_add_right L α β γ, latticeCocycle_add_right L β α γ, hsw]
  simp only [smul_smul]
  rw [← sub_smul,
    show latticeCocycle L β γ * ((-1 : ℂ) ^ P * latticeCocycle L β α * latticeCocycle L α γ
            * (-1 : ℂ) ^ P)
        - latticeCocycle L α γ * (latticeCocycle L β α * latticeCocycle L β γ) = 0 from by
      linear_combination
        (latticeCocycle L β γ * latticeCocycle L β α * latticeCocycle L α γ) * hpp,
    zero_smul]

/-- **Same-sign mutual locality** `Local Y(e^α) Y(e^β)` for `⟨α,β⟩ ≥ 0`. -/
theorem Yeαvec_sameSign_local (hEven : L.Even) (hPos : L.PosDef) (α β : L.carrier)
    (hsign : 0 ≤ L.form α β) : Local (Yeαvec L α) (Yeαvec L β) :=
  local_of_bracket_on_state L
    (fun j k γ p => Yeαvec_sameSign_bracket_on_state L hEven hPos α β hsign j k γ p)

end VOA.LatGen
