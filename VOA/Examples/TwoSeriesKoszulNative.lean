/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualGhost
import VOA.Examples.TwoSeriesKoszulMatter

/-!
# Level-generic port of `KoszulResidualNative`, `KoszulResidualGhost`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete Sl2SemiInfinite
open AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.LeeYangTransferAssembly VOA.SympFerm
open VOA.Ghost
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualNative` -/


/-! ### The antighost modes -/

/-! ### The native operators on the BRST space -/

section Native

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

/-- **The native Koszul differential** `Σ_{q ∈ s} u_q ⊗ c_{q}`. -/
def dN (s : Finset LexLetter) : Module.End ℂ (BRSTSpace L) :=
  ∑ q ∈ s, TensorProduct.map ((mLead L) hA q) (gAn q)

/-- **The contracting homotopy** `Σ_{q ∈ s} D_q ⊗ b_{q}`. -/
def hN (s : Finset LexLetter) : Module.End ℂ (BRSTSpace L) :=
  ∑ q ∈ s, TensorProduct.map ((mDer L) q) (gCr q)

/-- **The Koszul Laplacian** `L_s ⊗ 1 + 1 ⊗ Nb s`. -/
def ΔN (s : Finset LexLetter) : Module.End ℂ (BRSTSpace L) :=
  TensorProduct.map ((mL L) hA s) LinearMap.id + TensorProduct.map LinearMap.id (Nb s)

theorem mDer_mLead_apply (q q' : LexLetter) (x : (MatterSpace L)) :
    (mDer L) q ((mLead L) hA q' x) = (mLead L) hA q' ((mDer L) q x) + if q = q' then x else 0 := by
  have h := LinearMap.congr_fun ((mDer_mLead L) hA q q') x
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply] at h
  rw [h]
  split_ifs <;> rfl

theorem mLead_comm_apply (q q' : LexLetter) (x : (MatterSpace L)) :
    (mLead L) hA q ((mLead L) hA q' x) = (mLead L) hA q' ((mLead L) hA q x) := by
  have h := LinearMap.congr_fun ((mLead_comm L) hA q q') x
  simpa using h

theorem mDer_comm_apply (q q' : LexLetter) (x : (MatterSpace L)) :
    (mDer L) q ((mDer L) q' x) = (mDer L) q' ((mDer L) q x) := by
  have h := LinearMap.congr_fun ((mDer_comm L) q q') x
  simpa using h

theorem mL_apply (s : Finset LexLetter) (x : (MatterSpace L)) :
    (mL L) hA s x = ∑ q ∈ s, (mLead L) hA q ((mDer L) q x) := by
  simp [mL, LinearMap.coe_sum]

/-- The termwise identity behind `(dN L) (hN L) + (hN L) (dN L) = (ΔN L)`. -/
theorem term_identity (q q' : LexLetter) (x : (MatterSpace L)) (y : Sl2GhostSpace) :
    (mLead L) hA q ((mDer L) q' x) ⊗ₜ[ℂ] gAn q (gCr q' y) + (mDer L) q' ((mLead L) hA q x) ⊗ₜ[ℂ] gCr q' (gAn q y) =
      if q = q' then (mLead L) hA q ((mDer L) q x) ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] gCr q (gAn q y) else 0 := by
  rw [gAn_gCr_apply, mDer_mLead_apply]
  by_cases h : q = q'
  · subst h
    simp only [if_true]
    rw [TensorProduct.tmul_sub, TensorProduct.add_tmul]
    abel
  · simp only [if_neg h, if_neg (Ne.symm h), add_zero]
    rw [zero_sub, TensorProduct.tmul_neg]
    abel

/-- **`(dN L) (hN L) + (hN L) (dN L) = (ΔN L)`.** -/
theorem dN_hN_add (s : Finset LexLetter) (v : (BRSTSpace L)) :
    (dN L) hA s ((hN L) s v) + (hN L) s ((dN L) hA s v) = (ΔN L) hA s v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add]; rw [← hv, ← hw]; abel
  | tmul x y =>
      simp only [dN, hN, ΔN, LinearMap.coe_sum, Finset.sum_apply, map_sum,
        TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply]
      conv_lhs => arg 1; rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, term_identity, Finset.sum_ite_eq]
      rw [mL_apply, Nb_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q hq => by rw [if_pos hq]

/-- `L_s u_q = u_q L_s + u_q` for `q ∈ s`. -/
theorem mL_mLead (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (x : (MatterSpace L)) :
    (mL L) hA s ((mLead L) hA q x) = (mLead L) hA q ((mL L) hA s x) + (mLead L) hA q x := by
  rw [mL_apply, mL_apply, map_sum]
  simp only [mDer_mLead_apply, map_add, (mLead_comm_apply L) hA _ q]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single q (fun b _ hb => by rw [if_neg hb, map_zero])
    (fun h => absurd hq h), if_pos rfl]

/-- `D_q L_s = L_s D_q + D_q`. -/
theorem mDer_mL (s : Finset LexLetter) (q : LexLetter) (x : (MatterSpace L)) :
    (mDer L) q ((mL L) hA s x) = (mL L) hA s ((mDer L) q x) + if q ∈ s then (mDer L) q x else 0 := by
  rw [mL_apply, mL_apply, map_sum]
  simp only [mDer_mLead_apply, (mDer_comm_apply L) q]
  rw [Finset.sum_add_distrib]
  congr 1
  split_ifs with hq
  · rw [Finset.sum_eq_single q (fun b _ hb => by rw [if_neg (Ne.symm hb)])
      (fun h => absurd hq h), if_pos rfl]
  · exact Finset.sum_eq_zero fun b hb => by rw [if_neg (fun e => hq (by rw [e]; exact hb))]

/-- **`(ΔN L) (dN L) = (dN L) (ΔN L)`.** -/
theorem ΔN_dN (s : Finset LexLetter) (v : (BRSTSpace L)) :
    (ΔN L) hA s ((dN L) hA s v) = (dN L) hA s ((ΔN L) hA s v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul x y =>
      simp only [dN, ΔN, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
        LinearMap.add_apply, LinearMap.id_apply, map_add]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [(mL_mLead L) hA s hq, Nb_gAn s hq, TensorProduct.add_tmul, TensorProduct.tmul_sub]
      abel

/-- The derivation `D_q ⊗ 1` on the BRST space. -/
def mDerB (q : LexLetter) : Module.End ℂ (BRSTSpace L) := TensorProduct.map ((mDer L) q) LinearMap.id

/-- **`(D_q ⊗ 1) (ΔN L) = ((ΔN L) + 1)(D_q ⊗ 1)`** for `q ∈ s`. -/
theorem mDerB_ΔN (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (v : (BRSTSpace L)) :
    (mDerB L) q ((ΔN L) hA s v) = (ΔN L) hA s ((mDerB L) q v) + (mDerB L) q v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]; abel
  | tmul x y =>
      simp only [mDerB, ΔN, TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply,
        map_add]
      rw [mDer_mL, if_pos hq, TensorProduct.add_tmul]
      abel

theorem hN_eq_sum (s : Finset LexLetter) (v : (BRSTSpace L)) :
    (hN L) s v = ∑ q ∈ s, TensorProduct.map LinearMap.id (gCr q) ((mDerB L) q v) := by
  simp only [hN, mDerB, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]

theorem hN_eq_zero_of (s : Finset LexLetter) {v : (BRSTSpace L)} (h : ∀ q ∈ s, (mDerB L) q v = 0) :
    (hN L) s v = 0 := by
  rw [hN_eq_sum]
  exact Finset.sum_eq_zero fun q hq => by rw [h q hq, map_zero]

end Native


/-! ## Port of `KoszulResidualGhost` -/


/-! ### No negative `c₀` counts -/

theorem blockB_eq_bot_of_c0 {j : KF × ℤ} (hj : ¬ 0 ≤ j.1.2) : (blockB L) j = ⊥ :=
  tensorDeg_eq_bot_of (fun j : KF × ℤ => 0 ≤ j.1.2) (fun a b ha hb => by
      simp only [Prod.fst_add, Prod.snd_add]; omega) _ _
    (fun i h => by
      unfold matterBK matterF
      split_ifs with h1 h2
      · exact absurd (show (fun j : KF × ℤ => 0 ≤ j.1.2) i by simp [h2]) h
      · rfl
      · rfl)
    (fun i h => by
      unfold KoszulConcrete.ghostB
      split_ifs
      · exact ghostDegF_eq_bot_of_c0 h
      · rfl) hj

/-! ### The letters of index `< N` -/

/-! ### `Nb` on creation operators and words -/

/-! ### `Nb` on the fine ghost pieces -/


end

end VOA.TwoSeries
