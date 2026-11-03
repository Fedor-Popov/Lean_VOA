/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualMatter
import VOA.Examples.TwoSeriesKoszulU

/-!
# Level-generic port of `KoszulResidualMatter`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete AffineSl2GeneralRigidity
open AffineSl2BelowCritical AffineVOA AffineVOA.Inst VOA.LeeYangTransferAssembly MvPolynomial
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualMatter` -/


/-! ### Components of a composition -/

/-! ### Letters, shifts and modes -/

/-! ### The `A` factor -/

section AFactor

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

include hA in
theorem aDeg_isInternal : DirectSum.IsInternal (aDeg L) :=
  layerDeg_isInternal (affineForm L) (affineRealStructure L) (affineFlag L) hA (affineGramRefl L)

/-- **The leading part of a creation mode on `A`**: the `R`-raising component of
`J^a_{-j-1}` for the interpreted layers. -/
def aLead (q : LexLetter) : Module.End ℂ (ASpace L) :=
  compOp ((aDeg_isInternal L) hA) ((aMode L) (ofLex q).1 (nq q)) (· + eq q)

/-- The `(e + e')`-component of a single mode vanishes: modes raise `R` by at most one. -/
theorem iproj_mode_eq_zero_A (c : Fin 3) (n : ℤ) (q q' : LexLetter) {i : (ℤ × ℤ) × ℂ}
    {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    iproj ((aDeg_isInternal L) hA) (i + eq q' + eq q) ((aMode L) c n x) = 0 := by
  refine iproj_eq_zero_of_mem_iSup ((aDeg_isInternal L) hA) (fun j => ∃ δ, modePred n δ ∧ j = i + δ)
    ?_ ?_
  · have h := (aMode_shifts L) hA c n i x hx
    have hle : shiftTarget (aDeg L) (modePred n) i ≤
        ⨆ (j : (ℤ × ℤ) × ℂ) (_ : ∃ δ, modePred n δ ∧ j = i + δ), (aDeg L) j :=
      iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (i + δ) (le_iSup_of_le ⟨δ, hδ, rfl⟩ le_rfl)
    exact hle h
  · rintro ⟨δ, hδ, he⟩
    obtain ⟨d, hd, hd1⟩ := modePred_le_one hδ
    have h1 := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) he
    simp only [Prod.fst_add, hd] at h1
    omega

/-- **The leading creation operators on `A` commute.** -/
theorem aLead_comm (q q' : LexLetter) :
    (aLead L) hA q ∘ₗ (aLead L) hA q' = (aLead L) hA q' ∘ₗ (aLead L) hA q := by
  apply linearMap_ext_internal ((aDeg_isInternal L) hA)
  intro i x hx
  simp only [LinearMap.coe_comp, Function.comp_apply, aLead]
  rw [compOp_comp_of_mem _ _ _ _ _ _ _ ((aMode_shifts L) hA _ _) ((aMode_shifts L) hA _ _)
      (huniq_nq q q') hx,
    compOp_comp_of_mem _ _ _ _ _ _ _ ((aMode_shifts L) hA _ _) ((aMode_shifts L) hA _ _)
      (huniq_nq q' q) hx]
  rw [show i + eq q + eq q' = i + eq q' + eq q by abel, ← sub_eq_zero, ← map_sub]
  have hc := LinearMap.congr_fun ((aAction L).current_comm (ofLex q).1 (ofLex q').1 (nq q) (nq q')) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at hc
  change (aMode L) (ofLex q).1 (nq q) ((aMode L) (ofLex q').1 (nq q') x) -
    (aMode L) (ofLex q').1 (nq q') ((aMode L) (ofLex q).1 (nq q) x) = _ at hc
  rw [hc, if_neg (by have := nq_neg q; have := nq_neg q'; omega), LinearMap.zero_apply, add_zero,
    map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul]
  change _ • iproj ((aDeg_isInternal L) hA) _ ((aMode L) c (nq q + nq q') x) = 0
  rw [(iproj_mode_eq_zero_A L) hA c _ q q' hx, smul_zero]

theorem aLead_of_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    (aLead L) hA q x = iproj ((aDeg_isInternal L) hA) (i + eq q) ((aMode L) (ofLex q).1 (nq q) x) :=
  compOp_of_mem _ _ _ hx

theorem aLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    (aLead L) hA q x ∈ (aDeg L) (i + eq q) :=
  compOp_mem _ _ (· + eq q) hx

end AFactor

/-! ### The `U` factor -/

/-- The leading part of a creation mode on `U`. -/
def uLead (q : LexLetter) : Module.End ℂ (USpace L) :=
  compOp (uDeg_isInternal L) ((uMode L) (ofLex q).1 (nq q)) (· + eq q)

/-- **On `U`, the leading creation operator is multiplication by the variable.** -/
theorem PhiU_uLead (q : LexLetter) (x : (USpace L)) : (PhiU L) ((uLead L) q x) = X q * (PhiU L) x := by
  have key : (PhiU L).toLinearMap ∘ₗ (uLead L) q = LinearMap.mulLeft ℂ (X q) ∘ₗ (PhiU L).toLinearMap := by
    apply linearMap_ext_internal (uDeg_isInternal L)
    intro i y hy
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.mulLeft_apply]
    by_cases hi : ∃ t m, layerIndex t m = i
    · obtain ⟨t, m, rfl⟩ := hi
      rw [uLead, compOp_of_mem _ _ _ hy, layerIndex_add_eq]
      exact (PhiU_uP_creation L) q hy
    · push Not at hi
      rw [(uDeg_eq_bot_of L) hi, Submodule.mem_bot] at hy
      simp [hy]
  exact LinearMap.congr_fun key x

theorem uLead_comm (q q' : LexLetter) : (uLead L) q ∘ₗ (uLead L) q' = (uLead L) q' ∘ₗ (uLead L) q := by
  refine LinearMap.ext fun x => ?_
  apply (PhiU L).injective
  simp only [LinearMap.coe_comp, Function.comp_apply, PhiU_uLead]
  ring

/-- The partner derivation `∂_q` on `U`. -/
def uDer (q : LexLetter) : Module.End ℂ (USpace L) :=
  (PhiU L).symm.toLinearMap ∘ₗ (pderiv q : Derivation ℂ (MvPolynomial LexLetter ℂ)
    (MvPolynomial LexLetter ℂ)).toLinearMap ∘ₗ (PhiU L).toLinearMap

theorem PhiU_uDer (q : LexLetter) (x : (USpace L)) : (PhiU L) ((uDer L) q x) = pderiv q ((PhiU L) x) := by
  simp [uDer]

theorem uDer_comm (q q' : LexLetter) : (uDer L) q ∘ₗ (uDer L) q' = (uDer L) q' ∘ₗ (uDer L) q := by
  refine LinearMap.ext fun x => ?_
  apply (PhiU L).injective
  simp only [LinearMap.coe_comp, Function.comp_apply, PhiU_uDer]
  exact VOA.KoszulResidual.pderiv_pderiv_comm q q' _

theorem uDer_uLead (q q' : LexLetter) (x : (USpace L)) :
    (uDer L) q ((uLead L) q' x) = (uLead L) q' ((uDer L) q x) + if q = q' then x else 0 := by
  apply (PhiU L).injective
  rw [map_add, PhiU_uDer, PhiU_uLead, PhiU_uLead, PhiU_uDer, pderiv_X_mul']
  split_ifs <;> simp

/-- The partial-degree projection on `U`. -/
def uProj (s : Finset LexLetter) (d : ℕ) : Module.End ℂ (USpace L) :=
  (PhiU L).symm.toLinearMap ∘ₗ sProj s d ∘ₗ (PhiU L).toLinearMap

theorem PhiU_uProj (s : Finset LexLetter) (d : ℕ) (x : (USpace L)) :
    (PhiU L) ((uProj L) s d x) = sProj s d ((PhiU L) x) := by
  simp [uProj]

/-- The partial Euler operator on `U`. -/
theorem uProj_euler (s : Finset LexLetter) (d : ℕ) (x : (USpace L)) :
    (uProj L) s d (∑ q ∈ s, (uLead L) q ((uDer L) q x)) = (d : ℂ) • (uProj L) s d x := by
  apply (PhiU L).injective
  rw [PhiU_uProj, map_smul, PhiU_uProj, map_sum]
  simp only [PhiU_uLead, PhiU_uDer]
  have h := sProj_sEuler s d ((PhiU L) x)
  simp only [sEuler, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, Derivation.coeFn_coe, LinearMap.mulLeft_apply] at h
  exact h

theorem uProj_uDer (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (d : ℕ) (x : (USpace L)) :
    (uProj L) s d ((uDer L) q x) = (uDer L) q ((uProj L) s (d + 1) x) := by
  apply (PhiU L).injective
  rw [PhiU_uProj, PhiU_uDer, PhiU_uDer, PhiU_uProj, sProj_pderiv s hq]

theorem exists_uProj_eq_zero (s : Finset LexLetter) (x : (USpace L)) :
    ∃ D : ℕ, ∀ d, D < d → (uProj L) s d x = 0 := by
  obtain ⟨D, hD⟩ := exists_sProj_eq_zero s ((PhiU L) x)
  exact ⟨D, fun d hd => (PhiU L).injective (by rw [PhiU_uProj, hD d hd, map_zero])⟩

theorem sum_uProj (s : Finset LexLetter) (x : (USpace L)) {D : ℕ}
    (hD : ∀ d, D < d → (uProj L) s d x = 0) : ∑ d ∈ Finset.range (D + 1), (uProj L) s d x = x := by
  apply (PhiU L).injective
  rw [map_sum]
  simp only [PhiU_uProj]
  ext μ
  rw [coeff_sum]
  simp only [coeff_sProj]
  rw [Finset.sum_ite_eq]
  split_ifs with hμ
  · rfl
  · rw [Finset.mem_range] at hμ
    have h0 := hD (sdeg s μ) (by omega)
    have := congrArg (fun y => coeff μ ((PhiU L) y)) h0
    simp only [PhiU_uProj, coeff_sProj, if_pos rfl, map_zero, coeff_zero] at this
    exact this.symm

/-! ### Sums of operators -/

/-! ### The matter operators -/

section MatterOps

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

/-- The leading creation operator `u_q` on the matter space. -/
def mLead (q : LexLetter) : Module.End ℂ (MatterSpace L) :=
  TensorProduct.map (TensorProduct.map ((aLead L) hA q) LinearMap.id) LinearMap.id +
    TensorProduct.map LinearMap.id ((uLead L) q)

/-- The partner derivation `D_q` on the matter space. -/
def mDer (q : LexLetter) : Module.End ℂ (MatterSpace L) := TensorProduct.map LinearMap.id ((uDer L) q)

theorem mLead_comm (q q' : LexLetter) : (mLead L) hA q ∘ₗ (mLead L) hA q' = (mLead L) hA q' ∘ₗ (mLead L) hA q := by
  simp only [mLead, LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, (aLead_comm L) hA q q', (uLead_comm L) q q']
  abel

theorem mDer_comm (q q' : LexLetter) : (mDer L) q ∘ₗ (mDer L) q' = (mDer L) q' ∘ₗ (mDer L) q := by
  simp only [mDer, ← TensorProduct.map_comp, LinearMap.id_comp, (uDer_comm L) q q']

theorem uDer_comp_uLead (q q' : LexLetter) :
    (uDer L) q ∘ₗ (uLead L) q' = (uLead L) q' ∘ₗ (uDer L) q + if q = q' then LinearMap.id else 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, uDer_uLead, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> rfl

/-- **The Weyl relation** `D_q u_{q'} = u_{q'} D_q + δ_{q q'}`. -/
theorem mDer_mLead (q q' : LexLetter) :
    (mDer L) q ∘ₗ (mLead L) hA q' = (mLead L) hA q' ∘ₗ (mDer L) q + if q = q' then LinearMap.id else 0 := by
  simp only [mDer, mLead, LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, uDer_comp_uLead]
  split_ifs
  · rw [TensorProduct.map_add_right, TensorProduct.map_id]; abel
  · rw [add_zero, add_zero]

/-- `L_s = Σ_{q ∈ s} u_q D_q`. -/
def mL (s : Finset LexLetter) : Module.End ℂ (MatterSpace L) := ∑ q ∈ s, (mLead L) hA q ∘ₗ (mDer L) q

/-- The partial-degree projection on the matter space (acting on `U`). -/
def mProj (s : Finset LexLetter) (d : ℕ) : Module.End ℂ (MatterSpace L) :=
  TensorProduct.map LinearMap.id ((uProj L) s d)

theorem uProj_comp_euler (s : Finset LexLetter) (d : ℕ) :
    (uProj L) s d ∘ₗ (∑ q ∈ s, (uLead L) q ∘ₗ (uDer L) q) = (d : ℂ) • (uProj L) s d := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [LinearMap.comp_apply]
  exact (uProj_euler L) s d x

theorem uProj_comp_uDer (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (d : ℕ) :
    (uProj L) s d ∘ₗ (uDer L) q = (uDer L) q ∘ₗ (uProj L) s (d + 1) :=
  LinearMap.ext fun x => (uProj_uDer L) s hq d x

/-- The `A`-part of `L_s`. -/
def mLA (s : Finset LexLetter) : Module.End ℂ (MatterSpace L) :=
  ∑ q ∈ s, TensorProduct.map (TensorProduct.map ((aLead L) hA q) LinearMap.id) ((uDer L) q)

theorem mL_eq (s : Finset LexLetter) :
    (mL L) hA s = (mLA L) hA s + TensorProduct.map LinearMap.id (∑ q ∈ s, (uLead L) q ∘ₗ (uDer L) q) := by
  simp only [mL, mLA, mLead, mDer, LinearMap.add_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, Finset.sum_add_distrib, map_id_sum]

theorem mProj_mL (s : Finset LexLetter) (d : ℕ) :
    (mProj L) s d ∘ₗ (mL L) hA s = (d : ℂ) • (mProj L) s d + (mLA L) hA s ∘ₗ (mProj L) s (d + 1) := by
  rw [mL_eq, LinearMap.comp_add, mProj, ← TensorProduct.map_comp, LinearMap.id_comp,
    uProj_comp_euler, TensorProduct.map_smul_right, add_comm]
  congr 1
  rw [mLA, comp_sum', sum_comp']
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mProj, ← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
    LinearMap.comp_id, (uProj_comp_uDer L) s hq]

theorem exists_mProj_bound (s : Finset LexLetter) (v : (MatterSpace L)) :
    ∃ D : ℕ, ∀ D', D ≤ D' → (∀ d, D' < d → (mProj L) s d v = 0) ∧
      ∑ d ∈ Finset.range (D' + 1), (mProj L) s d v = v := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, fun _ _ => ⟨fun _ _ => map_zero _, by simp⟩⟩
  | tmul x y =>
      obtain ⟨D, hD⟩ := (exists_uProj_eq_zero L) s y
      refine ⟨D, fun D' hD' => ⟨fun d hd => ?_, ?_⟩⟩
      · rw [mProj, TensorProduct.map_tmul, hD d (by omega), TensorProduct.tmul_zero]
      · simp only [mProj, TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_sum]
        rw [(sum_uProj L) s y (fun d hd => hD d (by omega))]
  | add v w hv hw =>
      obtain ⟨D1, h1⟩ := hv
      obtain ⟨D2, h2⟩ := hw
      refine ⟨max D1 D2, fun D' hD' => ⟨fun d hd => ?_, ?_⟩⟩
      · rw [map_add, (h1 D' (le_of_max_le_left hD')).1 d hd,
          (h2 D' (le_of_max_le_right hD')).1 d hd, add_zero]
      · simp only [map_add, Finset.sum_add_distrib]
        rw [(h1 D' (le_of_max_le_left hD')).2, (h2 D' (le_of_max_le_right hD')).2]

/-- **`L_s + c` is injective on the whole matter space, for every `c ≥ 1`.** -/
theorem mL_add_injective (s : Finset LexLetter) {c : ℕ} (hc : 1 ≤ c) {v : (MatterSpace L)}
    (hv : (mL L) hA s v + (c : ℂ) • v = 0) : v = 0 := by
  obtain ⟨D, hD⟩ := (exists_mProj_bound L) s v
  have hstep : ∀ d, (mProj L) s (d + 1) v = 0 → (mProj L) s d v = 0 := by
    intro d hd
    have h := congrArg ((mProj L) s d) hv
    rw [map_add, map_smul, map_zero] at h
    have h2 := LinearMap.congr_fun ((mProj_mL L) hA s d) v
    rw [LinearMap.comp_apply] at h2
    rw [h2, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hd, map_zero,
      add_zero, ← add_smul] at h
    have hne : ((d : ℂ) + (c : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) + c := by positivity
      intro h0
      have h0' := congrArg Complex.re h0
      simp at h0'
      linarith
    exact eq_zero_of_smul_eq_zero hne h
  have hall : ∀ k d, D + 1 ≤ d + k → (mProj L) s d v = 0 := by
    intro k
    induction k with
    | zero => intro d hd; exact (hD D le_rfl).1 d (by omega)
    | succ k ih =>
        intro d hd
        by_cases h : D + 1 ≤ d + k
        · exact ih d h
        · exact hstep d (ih (d + 1) (by omega))
  rw [← (hD D le_rfl).2]
  exact Finset.sum_eq_zero fun d _ => hall (D + 1) d (by omega)

end MatterOps


end

end VOA.TwoSeries
