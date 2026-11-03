/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenOppCollapse
import VOA.Examples.LatticeGenSameSignLocal

/-!
# Opposite-sign mutual locality `Local Y(e^α) Y(e^β)` for `⟨α,β⟩ < 0`

The two operator orders of `Y(e^α,z₁)Y(e^β,z₂)` on a basis state reduce (`reduce_mixed`) to the two
`EEVec`-orderings, each carrying its FLM cocycle prefactor.  Multiplying by the `(z₁-z₂)^{Pn}`
finite difference (`Pn = -⟨α,β⟩ > 0`) and expanding binomially, the first ordering collapses
(`collapseL`) to `TvVec α β u v p`, the second (`collapseR2_gen`) to `(-1)^{Pn}·TvVec α β u v p`.
The two cocycle prefactors differ by exactly `ε(β,α) = (-1)^{Pn} ε(α,β)`, so the difference
vanishes — mutual locality with bound `Pn`.  Combined with the same-sign case (`⟨α,β⟩ ≥ 0`), this
gives full `Local Y(e^α) Y(e^β)` for **all** `α, β`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatExp (kZ wt shear3g mulBySubPow_binom)

variable (L : IntegralLattice)

/-- `latStateGen` is subtractive in the boson slot. -/
theorem latStateGen_sub_boson (p q : FockN (rank L)) (α : L.carrier) :
    latStateGen L (p - q) α = latStateGen L p α - latStateGen L q α := by
  simp only [latStateGen, TensorProduct.sub_tmul]

/-- **The opposite-sign mixed reduction**: `[Y(e^α)_j, Y(e^β)_k]` on `p ⊗ e^γ` is the difference of
the two `EEVec`-orderings, each with its cocycle prefactor, in the common sector `α+β+γ`.  The
vector-charge, cocycle-carrying lift of A₁'s `reduce_mixed`. -/
theorem reduce_mixed (α β : L.carrier) (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)) :
    bracketDist (Yeαvec L α) (Yeαvec L β) j k (latStateGen L p γ)
      = ((latticeCocycle L β γ * latticeCocycle L α (β + γ)) •
            EEVec L α ((j - L.form α γ) - L.form α β) (EEVec L β (k - L.form β γ) p)
          - (latticeCocycle L α γ * latticeCocycle L β (α + γ)) •
            EEVec L β ((k - L.form β γ) - L.form α β) (EEVec L α (j - L.form α γ) p))
        ⊗ₜ[ℂ] eGen L (α + β + γ) := by
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Yeαvec_tmul, map_smul, Yeαvec_tmul, Yeαvec_tmul, map_smul, Yeαvec_tmul, smul_smul, smul_smul,
    show α + (β + γ) = α + β + γ from by abel, show β + (α + γ) = α + β + γ from by abel,
    show j - L.form α (β + γ) = (j - L.form α γ) - L.form α β from by rw [map_add]; ring,
    show k - L.form β (α + γ) = (k - L.form β γ) - L.form α β from by
      rw [map_add, form_symm L β α]; ring,
    latStateGen, latStateGen, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    ← TensorProduct.sub_tmul]

/-- **The opposite-sign bracket's `(z₁-z₂)^Pn` finite difference vanishes on every basis state**
(`Pn = -⟨α,β⟩`).  Via `mulBySubPow_binom` the `Pn`-fold difference splits into the two `EEVec`
orderings; `collapseL` sends the first to `TvVec u v p`, `collapseR2_gen` sends the second to
`(-1)^Pn·TvVec u v p`, and the two cocycle prefactors cancel by `ε(β,α)=(-1)^Pn ε(α,β)`. -/
theorem Yeαvec_oppSign_bracket_binom_on_state (hEven : L.Even) (hPos : L.PosDef)
    (α β : L.carrier) (hsign : L.form α β ≤ -1) (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)) :
    mulBySubPow ((-(L.form α β)).toNat) (bracketDist (Yeαvec L α) (Yeαvec L β)) j k
        (latStateGen L p γ) = 0 := by
  set Pn : ℕ := (-(L.form α β)).toNat with hPndef
  have hPnZ : (Pn : ℤ) = -(L.form α β) := by
    rw [hPndef, Int.toNat_of_nonneg (by omega)]
  have hPnC : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ) := by
    rw [show (L.form α β : ℤ) = -(Pn : ℤ) from by omega]; push_cast; ring
  -- the cocycle cancellation scalar identity `C1 - C2·(-1)^Pn = 0`
  have hcoc : (latticeCocycle L β γ * latticeCocycle L α (β + γ))
      - (latticeCocycle L α γ * latticeCocycle L β (α + γ)) * (-1 : ℂ) ^ Pn = 0 := by
    rw [latticeCocycle_add_right L α β γ, latticeCocycle_add_right L β α γ]
    have hsw : latticeCocycle L α β = (-1 : ℂ) ^ Pn * latticeCocycle L β α := by
      rw [latticeCocycle_swap_sign L hEven α β, show L.form α β = -(Pn : ℤ) from by omega,
        zpow_neg, zpow_natCast, inv_eq_of_mul_eq_one_right
          (by rw [← pow_add, ← two_mul, pow_mul]; norm_num)]
    rw [hsw]; ring
  -- binomial expansion of the finite difference, evaluated at the basis state
  rw [show mulBySubPow Pn (bracketDist (Yeαvec L α) (Yeαvec L β)) j k
        = ∑ i ∈ Finset.range (Pn + 1),
            wt Pn i • bracketDist (Yeαvec L α) (Yeαvec L β) (j - ((Pn : ℤ) - i)) (k - i) from
      mulBySubPow_binom Pn (bracketDist (Yeαvec L α) (Yeαvec L β)) j k]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [LinearMap.smul_apply]
  -- reduce each `i`-term to the two `EEVec` orderings via `reduce_mixed`
  have hbody : ∀ i ∈ Finset.range (Pn + 1),
      wt Pn i • bracketDist (Yeαvec L α) (Yeαvec L β) (j - ((Pn : ℤ) - i)) (k - i)
          (latStateGen L p γ)
        = wt Pn i •
            (((latticeCocycle L β γ * latticeCocycle L α (β + γ)) •
                EEVec L α ((j - L.form α γ) + (i : ℤ))
                  (EEVec L β ((k - L.form β γ) - (i : ℤ)) p)
              - (latticeCocycle L α γ * latticeCocycle L β (α + γ)) •
                EEVec L β (((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ))
                  (EEVec L α (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) p))
             ⊗ₜ[ℂ] eGen L (α + β + γ)) := by
    intro i _
    rw [reduce_mixed L α β (j - ((Pn : ℤ) - i)) (k - i) γ p,
      show (j - ((Pn : ℤ) - i)) - L.form α γ = ((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ) from by omega,
      show (k - i) - L.form β γ = (k - L.form β γ) - (i : ℤ) from by omega,
      show ((k - L.form β γ) - (i : ℤ)) - L.form α β = ((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ) from by
        omega,
      show (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) - L.form α β
          = (j - L.form α γ) + (i : ℤ) from by omega]
  rw [Finset.sum_congr rfl hbody]
  -- pull the two cocycle scalars out of the two sums (over the common antidiagonal)
  rw [show (∑ i ∈ Finset.range (Pn + 1), wt Pn i •
          (((latticeCocycle L β γ * latticeCocycle L α (β + γ)) •
              EEVec L α ((j - L.form α γ) + (i : ℤ)) (EEVec L β ((k - L.form β γ) - (i : ℤ)) p)
            - (latticeCocycle L α γ * latticeCocycle L β (α + γ)) •
              EEVec L β (((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ))
                (EEVec L α (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) p))
           ⊗ₜ[ℂ] eGen L (α + β + γ)))
        = (((latticeCocycle L β γ * latticeCocycle L α (β + γ)) •
              ∑ i ∈ Finset.range (Pn + 1), wt Pn i •
                EEVec L α ((j - L.form α γ) + (i : ℤ)) (EEVec L β ((k - L.form β γ) - (i : ℤ)) p))
            - ((latticeCocycle L α γ * latticeCocycle L β (α + γ)) •
              ∑ i ∈ Finset.range (Pn + 1), wt Pn i •
                EEVec L β (((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ))
                  (EEVec L α (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) p)))
          ⊗ₜ[ℂ] eGen L (α + β + γ) from by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_sub,
        smul_comm (wt Pn i) (latticeCocycle L β γ * latticeCocycle L α (β + γ)),
        smul_comm (wt Pn i) (latticeCocycle L α γ * latticeCocycle L β (α + γ))]]
  -- collapse each ordering; both land on `TvVec u v p` (the second with a `(-1)^Pn`)
  rw [collapseL L hPos Pn α β hPnC (j - L.form α γ) (k - L.form β γ) p,
    collapseR2_gen L hPos Pn α β hPnC ((j - L.form α γ) - (Pn : ℤ)) ((k - L.form β γ) + (Pn : ℤ)) p,
    show ((j - L.form α γ) - (Pn : ℤ)) + (Pn : ℤ) = j - L.form α γ from by ring,
    show ((k - L.form β γ) + (Pn : ℤ)) - (Pn : ℤ) = k - L.form β γ from by ring]
  -- cocycle cancellation
  rw [smul_smul, ← sub_smul, hcoc, zero_smul, TensorProduct.zero_tmul]

/-- **The opposite-sign bracket's `(z₁-z₂)^Pn` annihilator vanishes** as a two-variable
distribution (`Pn = -⟨α,β⟩`).  Lifts the on-state version to all of `V_L` by `TensorProduct`/
`Finsupp` induction. -/
theorem Yeαvec_oppSign_bracket_binom (hEven : L.Even) (hPos : L.PosDef) (α β : L.carrier)
    (hsign : L.form α β ≤ -1) :
    mulBySubPow ((-(L.form α β)).toNat) (bracketDist (Yeαvec L α) (Yeαvec L β)) = 0 := by
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change mulBySubPow ((-(L.form α β)).toNat) (bracketDist (Yeαvec L α) (Yeαvec L β)) j k y = 0
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
          rw [show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl,
            Yeαvec_oppSign_bracket_binom_on_state L hEven hPos α β hsign j k γ p, smul_zero]

/-- **Opposite-sign mutual locality** `Local Y(e^α) Y(e^β)` for `⟨α,β⟩ < 0` (bound `Pn = -⟨α,β⟩`). -/
theorem Yeαvec_oppSign_local (hEven : L.Even) (hPos : L.PosDef) (α β : L.carrier)
    (hsign : L.form α β ≤ -1) : Local (Yeαvec L α) (Yeαvec L β) :=
  ⟨(-(L.form α β)).toNat, Yeαvec_oppSign_bracket_binom L hEven hPos α β hsign⟩

/-- **The FULL charge-pair mutual locality** of the lattice vertex operators:
`Local Y(e^α) Y(e^β)` for **all** `α, β : L.carrier`.  `rcases` on the sign of `⟨α,β⟩`: same-sign
(`⟨α,β⟩ ≥ 0`) via `Yeαvec_sameSign_local`, opposite-sign (`⟨α,β⟩ < 0`) via `Yeαvec_oppSign_local`.
`sorry`/`pbw`-free. -/
theorem Yeαvec_local (hEven : L.Even) (hPos : L.PosDef) (α β : L.carrier) :
    Local (Yeαvec L α) (Yeαvec L β) := by
  by_cases h : 0 ≤ L.form α β
  · exact Yeαvec_sameSign_local L hEven hPos α β h
  · exact Yeαvec_oppSign_local L hEven hPos α β (by omega)

end VOA.LatGen
