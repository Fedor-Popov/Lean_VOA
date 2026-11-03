/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualIdent
import Mathlib.RingTheory.Derivation.Lie

/-!
# The contracting homotopy on the actual joint pieces, and its `sl₂`-equivariance

* `uDer_mem`, `mDer_mem` — the partner derivation `D_q` lowers `R` by one and the weight by
  `j + 1`; `hN_mem_blockB` — `hN` shifts the joint grading by `-δT`.
* `NbB_blockB` — on a joint piece of antighost number `q` and weight `n₀ ≤ N`, `1 ⊗ Nb (sN N)`
  acts as `q`.
* `symDer_pderiv_comm` / `uMode_zero_uDer` — the zero modes act on the partner derivations
  by the coadjoint action.
* `totalZero_hN` — `hN (sN N)` commutes with the total current zero modes;
  `antighostZero_hN` — it anticommutes with the antighost zero modes. Hence `hN` preserves
  relative states.

Everything is proved outright from `hA`.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SympFerm VOA.Ghost MvPolynomial
open AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### The partner derivation lowers `R` -/

theorem PhiU_symm_mem_of_support {d : ℕ} {m : ℤ} {p : MvPolynomial LexLetter ℂ}
    (hp : ∀ μ ∈ p.support, μ.degree = d ∧ (enOf μ : ℤ) = m) :
    PhiU.symm p ∈ uDeg (layerIndex d m) := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have h := PhiU_symm_monomial_mem μ (coeff μ p)
  rwa [(hp μ hμ).1, (hp μ hμ).2] at h

theorem PhiU_support_of_mem {t : ℕ} {m : ℤ} {x : USpace} (hx : x ∈ uDeg (layerIndex t m)) :
    ∀ μ ∈ (PhiU x).support, μ.degree = t ∧ (enOf μ : ℤ) = m := by
  intro μ hμ
  rw [PhiU_of_mem hx, mem_support_iff, coeff_homogeneousComponent] at hμ
  split_ifs at hμ with ht
  · refine ⟨ht, ?_⟩
    by_contra hne
    exact hμ (coeff_eq_zero_of_mem_grading _ uNoncritical (uDeg_le_grading t m hx) hne)
  · exact absurd rfl hμ

theorem enOf_sub_single {μ : CurrentIndex} {q : LexLetter} (hq : μ q ≠ 0) :
    (enOf (μ - Finsupp.single q 1) : ℤ) = enOf μ - letterWt q := by
  have hsplit : μ = (μ - Finsupp.single q 1) + Finsupp.single q 1 := by
    ext r
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  conv_rhs => rw [hsplit]
  simp only [enOf, map_add, Finsupp.weight_single, smul_eq_mul, one_mul]
  push_cast; ring

theorem degree_sub_single {μ : CurrentIndex} {q : LexLetter} (hq : μ q ≠ 0) :
    (μ - Finsupp.single q 1).degree + 1 = μ.degree := by
  have hsplit : μ = (μ - Finsupp.single q 1) + Finsupp.single q 1 := by
    ext r
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  conv_rhs => rw [hsplit]
  rw [map_add, Finsupp.degree_single]

/-- The partner derivation lowers the layer index by `eq q`. -/
theorem uDer_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ x ∈ uDeg i, uDer q x ∈ uDeg (i - eq q) := by
  intro x hx
  by_cases hi : ∃ t m, layerIndex t m = i
  · obtain ⟨t, m, rfl⟩ := hi
    have hsupp := PhiU_support_of_mem hx
    have hx' : uDer q x = ∑ μ ∈ (PhiU x).support,
        PhiU.symm (pderiv q (monomial μ (coeff μ (PhiU x)))) := by
      rw [uDer, LinearMap.comp_apply, LinearMap.comp_apply]
      conv_lhs => rw [show (PhiU.toLinearMap x) = PhiU x from rfl, (PhiU x).as_sum]
      simp only [map_sum, Derivation.coeFn_coe, LinearEquiv.coe_coe]
    rw [hx']
    refine Submodule.sum_mem _ fun μ hμ => ?_
    rw [pderiv_monomial']
    by_cases hq : μ q = 0
    · rw [hq, Nat.cast_zero, mul_zero, monomial_zero, map_zero]; exact Submodule.zero_mem _
    · obtain ⟨hdeg, hen⟩ := hsupp μ hμ
      have h := PhiU_symm_monomial_mem (μ - Finsupp.single q 1) (coeff μ (PhiU x) * (μ q : ℂ))
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
    rw [uDeg_eq_bot_of hi, Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

theorem mDer_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ matterDeg i, mDer q m ∈ matterDeg (i - eq q) := by
  intro m hm
  have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg LinearMap.id (uDer q) 0 (-eq q)
    (fun i z hz => by rwa [add_zero]) (fun i y hy => by rw [← sub_eq_add_neg]; exact uDer_mem q i y hy)
    i m hm
  rwa [zero_add, ← sub_eq_add_neg] at h

theorem mDer_mem_matterB (q : LexLetter) (i : KF × ℤ) :
    ∀ x ∈ KoszulConcrete.matterB i, mDer q x ∈ KoszulConcrete.matterB (i + ((-(eq q), 0), 0)) := by
  intro x hx
  unfold KoszulConcrete.matterB matterF at hx ⊢
  split_ifs at hx ⊢ with h1 h2 h3 h4 h3 h4
  · have := mDer_mem q _ x hx
    simpa [sub_eq_add_neg] using this
  all_goals first
    | (rw [Submodule.mem_bot] at hx; rw [hx, map_zero]; exact Submodule.zero_mem _)
    | (simp only [Prod.snd_add, Prod.fst_add, add_zero] at *; contradiction)

theorem ghShiftF_zero_nonneg (jj : ℕ) : ghShiftF 0 (jj : ℤ) = modeIdxF (jj, 0) := by
  unfold ghShiftF
  rw [if_pos (by omega)]
  rfl

theorem gCr_mem_ghostB (q : LexLetter) (i : KF × ℤ) :
    ∀ y ∈ KoszulConcrete.ghostB i, gCr q y ∈
      KoszulConcrete.ghostB (i + (modeIdxF ((ofLex q).2, 0), 1)) := by
  intro y hy
  unfold KoszulConcrete.ghostB at hy ⊢
  split_ifs at hy with h
  · have hb : b2 (i + (modeIdxF ((ofLex q).2, 0), 1)).1 =
        2 * (i + (modeIdxF ((ofLex q).2, 0), 1)).2 := by
      simp only [Prod.fst_add, Prod.snd_add, map_add, h, b2_modeIdxF_b]; ring
    rw [if_pos hb]
    have h2 := ghostModeF_mem (ofLex q).1 0 (-((ofLex q).2 : ℤ) - 1) hy
    rw [show -(-((ofLex q).2 : ℤ) - 1) - 1 = (((ofLex q).2 : ℕ) : ℤ) by ring,
      ghShiftF_zero_nonneg] at h2
    exact h2
  · rw [Submodule.mem_bot] at hy; rw [hy, map_zero]; exact Submodule.zero_mem _

/-- The joint shift of the homotopy. -/
abbrev δH : KF × ℤ := ((((-1, -1), 0), 0), 1)

theorem neg_eq_add_modeIdxF (q : LexLetter) :
    (((-(eq q)), (0 : ℤ)) : KF) + modeIdxF ((ofLex q).2, 0) = (((-1, -1), 0), 0) := by
  simp only [eq, modeIdxF, modeIdx, modeR, ghCharge, ghModeWt, ghWt, letterWt]
  simp

/-- **`hN` shifts the joint grading by `δH = -δT`.** -/
theorem hN_mem_blockB (s : Finset LexLetter) (j : KF × ℤ) :
    ∀ z ∈ KoszulConcrete.blockB j, hN s z ∈ KoszulConcrete.blockB (j + δH) := by
  intro z hz
  rw [hN, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun q _ => ?_
  have h := tensorDeg_map_shift KoszulConcrete.matterB KoszulConcrete.ghostB (mDer q) (gCr q)
    ((-(eq q), 0), 0) (modeIdxF ((ofLex q).2, 0), 1) (mDer_mem_matterB q)
    (gCr_mem_ghostB q) j z hz
  have e : (((-(eq q), 0), 0) : KF × ℤ) + (modeIdxF ((ofLex q).2, 0), 1) = δH := by
    rw [Prod.mk_add_mk, neg_eq_add_modeIdxF]; rfl
  rwa [e] at h

theorem mDerB_mem_blockB (q : LexLetter) (j : KF × ℤ) :
    ∀ z ∈ KoszulConcrete.blockB j, mDerB q z ∈ KoszulConcrete.blockB (j + ((-(eq q), 0), 0)) := by
  intro z hz
  have h := tensorDeg_map_shift KoszulConcrete.matterB KoszulConcrete.ghostB (mDer q)
    LinearMap.id ((-(eq q), 0), 0) 0 (mDer_mem_matterB q) (fun i y hy => by rwa [add_zero]) j z hz
  rwa [add_zero] at h

/-! ### The antighost number on joint pieces -/

/-- **`1 ⊗ Nb (sN N)` acts as the antighost number** on a joint piece of weight `n₀ ≤ N`. -/
theorem NbB_blockB (N : ℕ) {j : KF × ℤ} {n0 : ℤ} (hn0 : j.1.1.2 = (n0 : ℂ)) (hN : n0 ≤ N) :
    ∀ v ∈ KoszulConcrete.blockB j,
      TensorProduct.map LinearMap.id (Nb (sN N)) v = (j.2 : ℂ) • v := by
  refine tensorDeg_induction KoszulConcrete.matterB KoszulConcrete.ghostB j _ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, smul_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_comm]) ?_
  intro b x hx y hy
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  by_cases hx0 : x = 0
  · subst hx0; simp
  obtain ⟨wm, hwm⟩ := matterB_nat hx hx0
  have hb2 : b.2 = 0 := by
    unfold KoszulConcrete.matterB at hx
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

theorem derivation_sum_apply {ι : Type*} (s : Finset ι)
    (D : ι → Derivation ℂ (MvPolynomial LexLetter ℂ) (MvPolynomial LexLetter ℂ))
    (x : MvPolynomial LexLetter ℂ) : (∑ b ∈ s, D b) x = ∑ b ∈ s, D b x := by
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℂ) (A := MvPolynomial LexLetter ℂ)
    (M := MvPolynomial LexLetter ℂ)) D s
  exact (congrFun this x).trans (Finset.sum_apply _ _ _)

/-- **The zero-mode derivation acts on `∂_q` by the coadjoint action.** -/
theorem symDer_pderiv_comm (c : Fin 3) (q : LexLetter) (p : MvPolynomial LexLetter ℂ) :
    symDer c 0 (pderiv q p) = pderiv q (symDer c 0 p) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 • pderiv (toLex (b, (ofLex q).2)) p := by
  have key : ⁅symDer c 0, (pderiv q : Derivation ℂ (MvPolynomial LexLetter ℂ)
      (MvPolynomial LexLetter ℂ))⁆ =
      -∑ b : Fin 3, fabc c b (ofLex q).1 • (pderiv (toLex (b, (ofLex q).2)) :
        Derivation ℂ (MvPolynomial LexLetter ℂ) (MvPolynomial LexLetter ℂ)) := by
    apply derivation_ext
    intro q'
    rw [Derivation.commutator_apply, Derivation.neg_apply, derivation_sum_apply]
    simp only [Derivation.smul_apply]
    rw [symDer_X, if_pos (Nat.zero_le _), map_sum]
    simp only [Derivation.map_smul]
    have h0 : (symDer c 0) ((pderiv q) (X q' : MvPolynomial LexLetter ℂ)) = 0 := by
      by_cases h : q' = q
      · subst h; rw [pderiv_X_self]; exact Derivation.map_one_eq_zero _
      · rw [pderiv_X_of_ne h, map_zero]
    rw [h0, zero_sub, neg_inj]
    by_cases hj : (ofLex q').2 = (ofLex q).2
    · rw [Finset.sum_eq_single (ofLex q).1, Finset.sum_eq_single (ofLex q').1]
      · have e1 : shiftLetter (ofLex q).1 q' 0 = q := by
          apply ofLex.injective; simp [shiftLetter, hj]
        have e2 : toLex ((ofLex q').1, (ofLex q).2) = q' := by
          apply ofLex.injective; rw [ofLex_toLex, ← hj]
        rw [e1, e2, pderiv_X_self, pderiv_X_self]
      · intro b _ hb
        rw [pderiv_X_of_ne, smul_zero]
        intro h; apply hb
        have := congrArg (fun x => (ofLex x).1) h
        simpa using this.symm
      · simp
      · intro b _ hb
        rw [pderiv_X_of_ne, smul_zero]
        intro h; apply hb
        have := congrArg (fun x => (ofLex x).1) h
        simpa [shiftLetter] using this
      · simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro b _
        rw [pderiv_X_of_ne, smul_zero]
        intro h; apply hj
        have := congrArg (fun x => (ofLex x).2) h
        simpa using this
      · intro b _
        rw [pderiv_X_of_ne, smul_zero]
        intro h; apply hj
        have := congrArg (fun x => (ofLex x).2) h
        simpa [shiftLetter] using this
  have := congrArg (fun D => D p) key
  simp only [Derivation.commutator_apply, Derivation.neg_apply, derivation_sum_apply,
    Derivation.smul_apply] at this
  rw [sub_eq_iff_eq_add] at this
  rw [this]
  abel

theorem uMode_zero_uDer (c : Fin 3) (q : LexLetter) (x : USpace) :
    uMode c 0 (uDer q x) = uDer q (uMode c 0 x) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 • uDer (toLex (b, (ofLex q).2)) x := by
  apply PhiU.injective
  rw [PhiU_uMode_zero, PhiU_uDer, map_sub, PhiU_uDer, PhiU_uMode_zero, map_sum]
  simp only [map_smul, PhiU_uDer]
  exact symDer_pderiv_comm c q _

theorem mMode_zero_mDer (c : Fin 3) (q : LexLetter) (m : MatterSpace) :
    mMode c 0 (mDer q m) = mDer q (mMode c 0 m) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 • mDer (toLex (b, (ofLex q).2)) m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib, smul_add]; abel
  | tmul x u =>
      have hM : mMode c 0 = TensorProduct.map (TensorProduct.map (aMode c 0) LinearMap.id)
          LinearMap.id + TensorProduct.map (TensorProduct.map LinearMap.id (bMode c 0))
          LinearMap.id + TensorProduct.map LinearMap.id (uMode c 0) := matterMode_eq c 0
      simp only [hM, mDer, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        uMode_zero_uDer, TensorProduct.tmul_sub, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
        map_add]
      abel

theorem totalZero_tmul' (c : Fin 3) (x : MatterSpace) (y : Sl2GhostSpace) :
    totalCurrentZero leeYangMatterAction.toAffineSl2Action c (x ⊗ₜ[ℂ] y) =
      mMode c 0 x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] Jz c y :=
  totalCurrentZero_tmul _ c x y

theorem perq_identity (c : Fin 3) (q : LexLetter) (m : MatterSpace) (g : Sl2GhostSpace) :
    (mMode c 0 (mDer q m) ⊗ₜ[ℂ] gCr q g + mDer q m ⊗ₜ[ℂ] Jz c (gCr q g)) -
      (mDer q (mMode c 0 m) ⊗ₜ[ℂ] gCr q g + mDer q m ⊗ₜ[ℂ] gCr q (Jz c g)) =
    ∑ i : Fin 3, fabc c (ofLex q).1 i • (mDer q m ⊗ₜ[ℂ] gCr (toLex (i, (ofLex q).2)) g) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 • (mDer (toLex (b, (ofLex q).2)) m ⊗ₜ[ℂ] gCr q g) := by
  rw [mMode_zero_mDer, Jz_Cr_b, TensorProduct.sub_tmul, TensorProduct.tmul_add,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  have e : ∀ i : Fin 3, (ConcreteHodge.Cr i ((ofLex q).2, 0)) g = gCr (toLex (i, (ofLex q).2)) g :=
    fun i => rfl
  simp only [e]
  abel

theorem sum3_comm {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (G : Fin 3 → ℕ → Fin 3 → M) :
    ∑ a : Fin 3, ∑ jj ∈ s, ∑ b : Fin 3, G a jj b = ∑ b : Fin 3, ∑ jj ∈ s, ∑ a : Fin 3, G a jj b := by
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext jj; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem sum_perq_eq_zero (N : ℕ) (c : Fin 3) (m : MatterSpace) (g : Sl2GhostSpace) :
    ∑ q ∈ sN N, (∑ i : Fin 3, fabc c (ofLex q).1 i •
        (mDer q m ⊗ₜ[ℂ] gCr (toLex (i, (ofLex q).2)) g) -
      ∑ b : Fin 3, fabc c b (ofLex q).1 •
        (mDer (toLex (b, (ofLex q).2)) m ⊗ₜ[ℂ] gCr q g)) = 0 := by
  rw [sum_sN]
  simp only [ofLex_toLex, Finset.sum_sub_distrib]
  rw [sub_eq_zero, sum3_comm (Finset.range N) (fun a jj b => fabc c b a •
    (mDer (toLex (b, jj)) m ⊗ₜ[ℂ] gCr (toLex (a, jj)) g))]

/-- **`hN (sN N)` commutes with the total current zero modes.** -/
theorem totalZero_hN (N : ℕ) (c : Fin 3) (v : BRSTSpace) :
    totalCurrentZero leeYangMatterAction.toAffineSl2Action c (hN (sN N) v) =
      hN (sN N) (totalCurrentZero leeYangMatterAction.toAffineSl2Action c v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m g =>
      have hL : totalCurrentZero leeYangMatterAction.toAffineSl2Action c (hN (sN N) (m ⊗ₜ[ℂ] g)) =
          ∑ q ∈ sN N, (mMode c 0 (mDer q m) ⊗ₜ[ℂ] gCr q g + mDer q m ⊗ₜ[ℂ] Jz c (gCr q g)) := by
        simp only [hN, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
          totalZero_tmul']
      have hR : hN (sN N) (totalCurrentZero leeYangMatterAction.toAffineSl2Action c (m ⊗ₜ[ℂ] g)) =
          ∑ q ∈ sN N, (mDer q (mMode c 0 m) ⊗ₜ[ℂ] gCr q g + mDer q m ⊗ₜ[ℂ] gCr q (Jz c g)) := by
        simp only [hN, LinearMap.coe_sum, Finset.sum_apply, totalZero_tmul', map_add,
          TensorProduct.map_tmul, Finset.sum_add_distrib]
      rw [hL, hR, ← sub_eq_zero, ← Finset.sum_sub_distrib]
      simp only [perq_identity]
      exact sum_perq_eq_zero N c m g

end

end VOA.KoszulResidual
