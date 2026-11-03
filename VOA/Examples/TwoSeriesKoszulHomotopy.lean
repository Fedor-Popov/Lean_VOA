/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualHomotopy
import VOA.Examples.TwoSeriesKoszulIdent

/-!
# Level-generic port of `KoszulResidualHomotopy`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete Sl2SemiInfinite
open AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.LeeYangTransferAssembly VOA.SympFerm
open VOA.Ghost MvPolynomial AffineVOA
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualHomotopy` -/


/-! ### The partner derivation lowers `R` -/

theorem PhiU_support_of_mem {t : ℕ} {m : ℤ} {x : (USpace L)} (hx : x ∈ (uDeg L) (layerIndex t m)) :
    ∀ μ ∈ ((PhiU L) x).support, μ.degree = t ∧ (enOf μ : ℤ) = m := by
  intro μ hμ
  rw [(PhiU_of_mem L) hx, mem_support_iff, coeff_homogeneousComponent] at hμ
  split_ifs at hμ with ht
  · refine ⟨ht, ?_⟩
    by_contra hne
    exact hμ (coeff_eq_zero_of_mem_grading _ L.uNoncritical ((uDeg_le_grading L) t m hx) hne)
  · exact absurd rfl hμ

/-- The partner derivation lowers the layer index by `eq q`. -/
theorem uDer_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ x ∈ (uDeg L) i, (uDer L) q x ∈ (uDeg L) (i - eq q) := by
  intro x hx
  by_cases hi : ∃ t m, layerIndex t m = i
  · obtain ⟨t, m, rfl⟩ := hi
    have hsupp := (PhiU_support_of_mem L) hx
    have hx' : (uDer L) q x = ∑ μ ∈ ((PhiU L) x).support,
        (PhiU L).symm (pderiv q (monomial μ (coeff μ ((PhiU L) x)))) := by
      rw [uDer, LinearMap.comp_apply, LinearMap.comp_apply]
      conv_lhs => rw [show ((PhiU L).toLinearMap x) = (PhiU L) x from rfl, ((PhiU L) x).as_sum]
      simp only [map_sum, Derivation.coeFn_coe, LinearEquiv.coe_coe]
    rw [hx']
    refine Submodule.sum_mem _ fun μ hμ => ?_
    rw [pderiv_monomial']
    by_cases hq : μ q = 0
    · rw [hq, Nat.cast_zero, mul_zero, monomial_zero, map_zero]; exact Submodule.zero_mem _
    · obtain ⟨hdeg, hen⟩ := hsupp μ hμ
      have h := (PhiU_symm_monomial_mem L) (μ - Finsupp.single q 1) (coeff μ ((PhiU L) x) * (μ q : ℂ))
      have e : layerIndex (μ - Finsupp.single q 1).degree (enOf (μ - Finsupp.single q 1)) =
          layerIndex t m - eq q := by
        have h1 := degree_sub_single hq
        have h2 := enOf_sub_single hq
        simp only [layerIndex, eq, Prod.mk_sub_mk]
        congr 1
        · congr 1; omega
        · rw [h2, hen]; push_cast; ring
      rwa [e] at h
  · push Not at hi
    rw [(uDeg_eq_bot_of L) hi, Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

theorem mDer_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ (matterDeg L) i, (mDer L) q m ∈ (matterDeg L) (i - eq q) := by
  intro m hm
  have h := tensorDeg_map_shift (tensorDeg (aDeg L) bDeg) (uDeg L) LinearMap.id ((uDer L) q) 0 (-eq q)
    (fun i z hz => by rwa [add_zero]) (fun i y hy => by rw [← sub_eq_add_neg]; exact (uDer_mem L) q i y hy)
    i m hm
  rwa [zero_add, ← sub_eq_add_neg] at h

theorem mDer_mem_matterB (q : LexLetter) (i : KF × ℤ) :
    ∀ x ∈ (matterBK L) i, (mDer L) q x ∈ (matterBK L) (i + ((-(eq q), 0), 0)) := by
  intro x hx
  unfold matterBK matterF at hx ⊢
  split_ifs at hx ⊢ with h1 h2 h3 h4 h3 h4
  · have := (mDer_mem L) q _ x hx
    simpa [sub_eq_add_neg] using this
  all_goals first
    | (rw [Submodule.mem_bot] at hx; rw [hx, map_zero]; exact Submodule.zero_mem _)
    | (simp only [Prod.snd_add, Prod.fst_add, add_zero] at *; contradiction)

/-- **`(hN L)` shifts the joint grading by `δH = -δT`.** -/
theorem hN_mem_blockB (s : Finset LexLetter) (j : KF × ℤ) :
    ∀ z ∈ (blockB L) j, (hN L) s z ∈ (blockB L) (j + δH) := by
  intro z hz
  rw [hN, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun q _ => ?_
  have h := tensorDeg_map_shift (matterBK L) KoszulConcrete.ghostB ((mDer L) q) (gCr q)
    ((-(eq q), 0), 0) (modeIdxF ((ofLex q).2, 0), 1) ((mDer_mem_matterB L) q)
    (gCr_mem_ghostB q) j z hz
  have e : (((-(eq q), 0), 0) : KF × ℤ) + (modeIdxF ((ofLex q).2, 0), 1) = δH := by
    rw [Prod.mk_add_mk, neg_eq_add_modeIdxF]; rfl
  rwa [e] at h

theorem mDerB_mem_blockB (q : LexLetter) (j : KF × ℤ) :
    ∀ z ∈ (blockB L) j, (mDerB L) q z ∈ (blockB L) (j + ((-(eq q), 0), 0)) := by
  intro z hz
  have h := tensorDeg_map_shift (matterBK L) KoszulConcrete.ghostB ((mDer L) q)
    LinearMap.id ((-(eq q), 0), 0) 0 ((mDer_mem_matterB L) q) (fun i y hy => by rwa [add_zero]) j z hz
  rwa [add_zero] at h

/-! ### The antighost number on joint pieces -/

/-- **`1 ⊗ Nb (sN N)` acts as the antighost number** on a joint piece of weight `n₀ ≤ N`. -/
theorem NbB_blockB (N : ℕ) {j : KF × ℤ} {n0 : ℤ} (hn0 : j.1.1.2 = (n0 : ℂ)) (hN : n0 ≤ N) :
    ∀ v ∈ (blockB L) j,
      TensorProduct.map LinearMap.id (Nb (sN N)) v = (j.2 : ℂ) • v := by
  refine tensorDeg_induction (matterBK L) KoszulConcrete.ghostB j _ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, smul_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_comm]) ?_
  intro b x hx y hy
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  by_cases hx0 : x = 0
  · subst hx0; simp
  obtain ⟨wm, hwm⟩ := (matterB_nat L) hx hx0
  have hb2 : b.2 = 0 := by
    unfold matterBK at hx
    split_ifs at hx with h
    · exact h
    · exact absurd ((Submodule.mem_bot ℂ).mp hx) hx0
  unfold KoszulConcrete.ghostB at hy
  split_ifs at hy with hg
  · have hq : (j - b).2 = j.2 := by simp [hb2]
    rw [Nb_ghostDegF N (q := j.2) (by rw [hg, hq]) ?_ y hy, TensorProduct.tmul_smul]
    intro w hw
    simp only [Prod.fst_sub, Prod.snd_sub, hn0, ← hwm] at hw
    have : (w : ℤ) = n0 - wm := by exact_mod_cast hw
    omega
  · rw [Submodule.mem_bot] at hy; rw [hy]; simp

/-! ### Equivariance -/

theorem uMode_zero_uDer (c : Fin 3) (q : LexLetter) (x : (USpace L)) :
    (uMode L) c 0 ((uDer L) q x) = (uDer L) q ((uMode L) c 0 x) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 • (uDer L) (toLex (b, (ofLex q).2)) x := by
  apply (PhiU L).injective
  rw [PhiU_uMode_zero, PhiU_uDer, map_sub, PhiU_uDer, PhiU_uMode_zero, map_sum]
  simp only [map_smul, PhiU_uDer]
  exact symDer_pderiv_comm c q _

theorem mMode_zero_mDer (c : Fin 3) (q : LexLetter) (m : (MatterSpace L)) :
    (mMode L) c 0 ((mDer L) q m) = (mDer L) q ((mMode L) c 0 m) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 • (mDer L) (toLex (b, (ofLex q).2)) m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib, smul_add]; abel
  | tmul x u =>
      have hM : (mMode L) c 0 = TensorProduct.map (TensorProduct.map ((aMode L) c 0) LinearMap.id)
          LinearMap.id + TensorProduct.map (TensorProduct.map LinearMap.id (bMode c 0))
          LinearMap.id + TensorProduct.map LinearMap.id ((uMode L) c 0) := (matterMode_eq L) c 0
      simp only [hM, mDer, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        uMode_zero_uDer, TensorProduct.tmul_sub, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
        map_add]
      abel

theorem totalZero_tmul' (c : Fin 3) (x : (MatterSpace L)) (y : Sl2GhostSpace) :
    totalCurrentZero (matterAction L).toAffineSl2Action c (x ⊗ₜ[ℂ] y) =
      (mMode L) c 0 x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] Jz c y :=
  totalCurrentZero_tmul _ c x y

theorem perq_identity (c : Fin 3) (q : LexLetter) (m : (MatterSpace L)) (g : Sl2GhostSpace) :
    ((mMode L) c 0 ((mDer L) q m) ⊗ₜ[ℂ] gCr q g + (mDer L) q m ⊗ₜ[ℂ] Jz c (gCr q g)) -
      ((mDer L) q ((mMode L) c 0 m) ⊗ₜ[ℂ] gCr q g + (mDer L) q m ⊗ₜ[ℂ] gCr q (Jz c g)) =
    ∑ i : Fin 3, fabc c (ofLex q).1 i • ((mDer L) q m ⊗ₜ[ℂ] gCr (toLex (i, (ofLex q).2)) g) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 • ((mDer L) (toLex (b, (ofLex q).2)) m ⊗ₜ[ℂ] gCr q g) := by
  rw [mMode_zero_mDer, Jz_Cr_b, TensorProduct.sub_tmul, TensorProduct.tmul_add,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  have e : ∀ i : Fin 3, (ConcreteHodge.Cr i ((ofLex q).2, 0)) g = gCr (toLex (i, (ofLex q).2)) g :=
    fun i => rfl
  simp only [e]
  abel

theorem sum_perq_eq_zero (N : ℕ) (c : Fin 3) (m : (MatterSpace L)) (g : Sl2GhostSpace) :
    ∑ q ∈ sN N, (∑ i : Fin 3, fabc c (ofLex q).1 i •
        ((mDer L) q m ⊗ₜ[ℂ] gCr (toLex (i, (ofLex q).2)) g) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 •
        ((mDer L) (toLex (b, (ofLex q).2)) m ⊗ₜ[ℂ] gCr q g)) = 0 := by
  rw [sum_sN]
  simp only [ofLex_toLex, Finset.sum_sub_distrib]
  rw [sub_eq_zero, sum3_comm (Finset.range N) (fun a jj b => fabc c b a •
    ((mDer L) (toLex (b, jj)) m ⊗ₜ[ℂ] gCr (toLex (a, jj)) g))]

/-- **`(hN L) (sN N)` commutes with the total current zero modes.** -/
theorem totalZero_hN (N : ℕ) (c : Fin 3) (v : (BRSTSpace L)) :
    totalCurrentZero (matterAction L).toAffineSl2Action c ((hN L) (sN N) v) =
      (hN L) (sN N) (totalCurrentZero (matterAction L).toAffineSl2Action c v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m g =>
      have hL : totalCurrentZero (matterAction L).toAffineSl2Action c ((hN L) (sN N) (m ⊗ₜ[ℂ] g)) =
          ∑ q ∈ sN N, ((mMode L) c 0 ((mDer L) q m) ⊗ₜ[ℂ] gCr q g + (mDer L) q m ⊗ₜ[ℂ] Jz c (gCr q g)) := by
        simp only [hN, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
          totalZero_tmul']
      have hR : (hN L) (sN N) (totalCurrentZero (matterAction L).toAffineSl2Action c (m ⊗ₜ[ℂ] g)) =
          ∑ q ∈ sN N, ((mDer L) q ((mMode L) c 0 m) ⊗ₜ[ℂ] gCr q g + (mDer L) q m ⊗ₜ[ℂ] gCr q (Jz c g)) := by
        simp only [hN, LinearMap.coe_sum, Finset.sum_apply, totalZero_tmul', map_add,
          TensorProduct.map_tmul, Finset.sum_add_distrib]
      rw [hL, hR, ← sub_eq_zero, ← Finset.sum_sub_distrib]
      simp only [perq_identity]
      exact (sum_perq_eq_zero L) N c m g


end

end VOA.TwoSeries
