/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.CyclicEvalEndpoint
import VOA.Examples.TwoSeriesKoszulEndpoint

/-!
# Level-generic port of `CyclicEvalParity` and `endpoint_negZero`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval VOA.SympFerm VOA.Ghost
open Sl2SemiInfinite Sl2CosetConcrete VOA.LeeYangTransferAssembly VOA.GradedUnitaryCohomology
open VOA.VertexOperatorAlgebra VOA.InvariantSymbol
open Module (finrank)
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `CyclicEvalParity` -/


set_option synthInstance.maxHeartbeats 200000

/-! ### One pair -/

/-! ### Koszul operators are involutions -/

/-! ### Three pairs -/

/-! ### Matter pieces: even `2R`, ghost number zero -/

theorem matterDeg_evenZero : EvenZero (matterDeg L) :=
  tensorDeg_evenZero (tensorDeg_evenZero (layerDeg_evenZero _ _) (trivialDeg_evenZero _))
    (layerDeg_evenZero _ _)

/-! ### Relative states at odd `2R` and ghost number zero -/

theorem antighostZero_eq_lTensor (a : Fin 3) :
    antighostZero (matterSVA L) a = (ConcreteHodge.gMode a 0 0).lTensor (MatterSpace L) := by
  apply TensorProduct.ext'; intro x y
  rw [antighostZero_tmul a ((matter_mem_parity_zero L) x), koszul_zero_right, one_smul,
    LinearMap.lTensor_tmul]
  rfl

theorem lTensor_parity_fix {x : (BRSTSpace L)}
    (hx : x ∈ relativeCarrier (matterAction L).toAffineSl2Action) (a : Fin 3)
    (P : Module.End ℂ Sl2GhostSpace)
    (hP : P = LinearMap.id - (2 : ℂ) • (ConcreteHodge.gMode a 1 (-1) * ConcreteHodge.gMode a 0 0)) :
    P.lTensor (MatterSpace L) x = x := by
  have h0 : (ConcreteHodge.gMode a 0 0).lTensor (MatterSpace L) x = 0 := by
    rw [← antighostZero_eq_lTensor]
    exact ((mem_relativeCarrier _ x).mp hx).2 a
  rw [hP, LinearMap.lTensor_sub, LinearMap.lTensor_smul, LinearMap.lTensor_mul,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, h0, map_zero, smul_zero,
    sub_zero, LinearMap.lTensor_id, LinearMap.id_apply]

/-- Relative states are fixed by the product of the three `c₀`-parities. -/
theorem ghostParity_relative {x : (BRSTSpace L)}
    (hx : x ∈ relativeCarrier (matterAction L).toAffineSl2Action) :
    ghostParity.lTensor (MatterSpace L) x = x := by
  rw [ghostParity_eq, LinearMap.lTensor_mul, LinearMap.lTensor_mul, Module.End.mul_apply,
    Module.End.mul_apply, (lTensor_parity_fix L) hx 2 _ parity_two_eq,
    (lTensor_parity_fix L) hx 1 _ parity_one_eq, (lTensor_parity_fix L) hx 0 _ parity_zero_eq]

/-- On a BRST piece of odd `2R` at ghost number zero, the parity is `-1`. -/
theorem ghostParity_odd (j : ℤ) (hj : ¬ Even j) (w : ℂ) (x : (BRSTSpace L))
    (hx : x ∈ tensorDeg (matterDeg L) ghostDeg ((j, 0), w)) :
    ghostParity.lTensor (MatterSpace L) x = -x := by
  refine tensorDeg_induction (matterDeg L) ghostDeg ((j, 0), w)
    (fun z => ghostParity.lTensor (MatterSpace L) z = -z) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, neg_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_neg]) ?_ x hx
  intro b m hm y hy
  by_cases hb : Even b.1.1 ∧ b.1.2 = 0
  · rw [LinearMap.lTensor_tmul, ghostParity_ghostDeg _ y hy, TensorProduct.tmul_smul,
      ← TensorProduct.tmul_neg, ← neg_one_smul ℂ y, TensorProduct.tmul_smul]
    congr 1
    unfold idxSign psign
    rw [if_neg]
    simp only [Prod.fst_sub, Prod.snd_sub]
    intro he
    apply hj
    have := he.add hb.1
    rw [hb.2] at this
    simpa using this
  · rw [(matterDeg_evenZero L) b hb, Submodule.mem_bot] at hm
    rw [hm, TensorProduct.zero_tmul, map_zero, neg_zero]

/-- **The interpreted piece of the relative complex at `(2p+1, 0)` is zero**, for every
standard ghost grading. -/
theorem relDeg_odd_eq_bot {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (n : ℤ) (p : ℕ) : (relDeg L) Gh n (2 * (p : ℤ) + 1, 0) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : (BRSTSpace L)) ∈ tensorDeg (matterDeg L) ghostDeg ((2 * (p : ℤ) + 1, 0), (n : ℂ)) := by
    have := hx
    change (x : (BRSTSpace L)) ∈ (brstDeg L) Gh _ at this
    rwa [brstDeg, hs] at this
  have h1 := (ghostParity_relative L) (inf_le_left (a := relativeCarrier _) x.2)
  have h2 := (ghostParity_odd L) (2 * (p : ℤ) + 1) (by
    rw [Int.not_even_iff_odd]; exact ⟨p, rfl⟩) _ _ hx'
  rw [h1] at h2
  have h4 : (x : (BRSTSpace L)) = 0 := by
    have h3 : (2 : ℂ) • (x : (BRSTSpace L)) = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; simp
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  exact (Submodule.mem_bot _).mpr (Subtype.ext h4)

set_option synthInstance.maxHeartbeats 200000

/-- **The endpoint has no leading cohomology at odd `2R`** (the `odd_zero` field of
`LeadingCyclicEvaluation`), proved. -/
theorem endpoint_oddZero (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    ∀ n (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (p : ℕ),
      finrank ℂ ((((endpointKahler L) hA).model n hp).leadCohom (2 * (p : ℤ) + 1, 0)) = 0 := by
  intro n hp p
  exact finrank_leadCohom_eq_zero_of_deg (((endpointKahler L) hA).model n hp) _
    ((relDeg_odd_eq_bot L) bgGh bgGh_isStd n p)


/-! ## Port of `CyclicEvalEndpoint` -/


set_option synthInstance.maxHeartbeats 200000

/-- **No leading cohomology at negative `2R`** (proved). -/
theorem endpoint_negZero (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    ∀ n (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (j : ℤ), j < 0 →
      finrank ℂ ((((endpointKahler L) hA).model n hp).leadCohom (j, 0)) = 0 := by
  intro n hp j hj
  apply finrank_leadCohom_eq_zero_of_deg
  change ((brstDeg L) bgGh (((j, 0) : ℤ × ℤ), (n : ℂ))).comap ((relativeWeight L) n).subtype = ⊥
  rw [(brstDeg_nonnegR_std L) bgGh_isStd ((j, 0), (n : ℂ)) hj, Submodule.comap_bot,
    Submodule.ker_subtype]


end

end VOA.TwoSeries
