/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTopSigma

/-!
# (R-top) on `V₃⁺`: the block-monomial map `φ_τ` and what is proved about it

`φ_τ : V_Λ⁺ → TP` sends `x_n = e^n + e^{−n}` (`n ∈ S₁`) to `h_{w_{blk n}}(−½) ⊗ τ(n)`, for an
assignment `τ : S₁ → T` (`phiV3`, `phiV3_frameX0P`).  The block shape is the one the diagonal
letters force (their joint eigenspaces are the blocks on both sides — analysis, not stated as a
theorem); it matches a numerically found intertwiner.  The
`T`-part `τ` is left free.

## Main results
* `mvec`, `nvec` — one explicit odd norm-4 vector `(1²⁴) − 4e_j` per block (`blk_nvec`).
* `cw_complete` — completeness of the frame: `Σ_j (w_j)_a (w_j)_b = 8 δ_ab`.
* `phiV3_mem_frame`, `phiV3_mem_weight`, `phiV3_hits` — the clauses `maps_frame`, `maps_weight`,
  `hits_cyclic` of `TopSigmaV3` (the last when every block meets a common `t₀ ≠ 0`).
* `phiV3_ZM_diag` — the zero-mode identity for the 24 diagonal frame letters `w_j(−1)²𝟙`,
  for **every** `τ` (`σ` fixes them, `sig_dV_fw`, and both sides act by `9`/`1` on blocks).
* `qV_eq_sum_dV` — the abstract-coordinate quadratics are combinations of the frame ones.
* `topSigmaV3_of_offdiag` — `TopSigmaV3 s φ_τ` from `ZhuGenerated G2`, the zero-mode identities
  for the off-diagonal frame letters `w_j(−1)w_k(−1)𝟙` (`j ≠ k`) and for the lattice letters
  `e^γ + e^{−γ}` (`γ ∈ S₀`).
* `topSigmaV3_partial` — unconditional: `∃ φ` with `maps_frame`, `maps_weight`, `hits_cyclic`
  and the diagonal zero-mode identities.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
**`TopSigmaV3` itself is NOT proved.**  `topSigmaV3_partial` uses a constant `τ` and certifies
only the listed clauses; the off-diagonal and lattice identities constrain `τ` (by Schur, at most
one `τ` up to scalar can satisfy all of them), and a constant `τ`
is not expected to.  Open, as named hypotheses of `topSigmaV3_of_offdiag`: (i) `ZhuGenerated G2`;
(ii) the off-diagonal frame Heisenberg letters (276 pairs `j < k`); (iii) the lattice letters
`e^γ + e^{−γ}`, `γ ∈ S₀` (octad type and `(±4,±4,0²²)` type).  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.IntegralLattice
open VOA.LatGen HeisenbergN MvPolynomial
open Module (End)
open Submodule
open scoped TensorProduct

/-! ## §1  One odd norm-4 vector per block -/

/-- `b_j = 2e₀ + 2e_j ∈ A`. -/
theorem bvec_mem (j : Fin 24) :
    (2 : ℤ) • (Pi.single 0 1 + Pi.single j 1 : Fin 24 → ℤ) ∈ Leech.subA := by
  refine ⟨two_smul_mem_preimageOfCode Code.golay _, ⟨1, ?_⟩⟩
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, if_true]
  norm_num

/-- `m_j = u − 4e₀ − 4e_j = (1²⁴) − 4e_j`: an odd Leech vector of norm 4 with its `−3` at `j`. -/
noncomputable def mvec (j : Fin 24) : leech.carrier :=
  uβ - inclΛ ((⟨_, bvec_mem j⟩ : ↥Leech.subA))

theorem lv_mvec (j i : Fin 24) : lv (mvec j) i = if i = j then -3 else 1 := by
  change Leech.uVec i - (2 : ℤ) • ((2 : ℤ) • (Pi.single 0 1 + Pi.single j 1 : Fin 24 → ℤ)) i = _
  simp only [Leech.uVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = j <;> by_cases h0 : i = 0 <;> simp [hi, h0] <;> subst_vars <;> simp_all

theorem mvec_form (j : Fin 24) : leech.form (mvec j) (mvec j) = 4 := by
  rw [leech_form_lv]
  have h : lv (mvec j) ⬝ᵥ lv (mvec j) = 32 := by
    rw [dotProduct]
    simp only [lv_mvec]
    have : ∀ i : Fin 24, (if i = j then (-3 : ℤ) else 1) * (if i = j then -3 else 1) = 1 + if i = j then 8 else 0 := by
      intro i; split_ifs <;> norm_num
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp
  rw [h]; rfl

theorem mvec_not_mem (j : Fin 24) : mvec j ∉ lambda0 := by
  rw [mem_lambda0]
  change ((lv (mvec j) 0 : ℤ) : ZMod 2) ≠ 0
  rw [lv_mvec]
  split_ifs <;> decide

theorem blk_mvec (j : Fin 24) : blk (mvec j) = j := by
  have h := lv_sq (mvec_not_mem j) (mvec_form j) j
  rw [lv_mvec, if_pos rfl] at h
  by_contra hne
  rw [if_neg (Ne.symm hne)] at h
  norm_num at h

open Classical in
/-- The representative of `±m_j` in the half `S₁`. -/
noncomputable def nvec (j : Fin 24) : leech.carrier :=
  if mvec j ∈ halfFour leech leech_posDef then mvec j else -mvec j

theorem nvec_mem (j : Fin 24) : nvec j ∈ halfFourChi 1 := by
  classical
  have hn4 : mvec j ∈ normFour leech leech_posDef := (mem_normFour leech leech_posDef).mpr (mvec_form j)
  have hch : frameChar (mvec j) = 1 := by
    have := mvec_not_mem j
    rw [mem_lambda0] at this
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (frameChar (mvec j)) with h | h
    · exact absurd h this
    · exact h
  unfold nvec
  split_ifs with h
  · exact Finset.mem_filter.mpr ⟨h, hch⟩
  · refine Finset.mem_filter.mpr ⟨?_, by rw [map_neg, hch]; rfl⟩
    rw [normFour_eq_union] at hn4
    rcases Finset.mem_union.mp hn4 with h' | h'
    · exact absurd h' h
    · obtain ⟨β, hβ, hβe⟩ := Finset.mem_image.mp h'
      rw [← hβe, neg_neg]; exact hβ

theorem blk_nvec (j : Fin 24) : blk (nvec j) = j := by
  unfold nvec; split_ifs
  · exact blk_mvec j
  · rw [blk_neg, blk_mvec]

/-! ## §2  Completeness of the frame coordinates -/

theorem cw_orth (j k : Fin 24) : ∑ a, cw j a * cw k a = if j = k then (8 : ℂ) else 0 := by
  rw [show (∑ a, cw j a * cw k a) = ((leech.form (fw j) (fw k) : ℤ) : ℂ) from
    sum_chargeCoord leech leech_posDef (fw j) (fw k), form_fw_fw]
  split_ifs <;> norm_num

/-- `Σ_j (w_j)_a (w_j)_b = 8 δ_ab`. -/
theorem cw_complete (a b : Fin (rank leech)) : ∑ j, cw j a * cw j b = if a = b then (8 : ℂ) else 0 := by
  let e : Fin (rank leech) ≃ Fin 24 := finCongr leech_rank
  let M : Matrix (Fin 24) (Fin 24) ℂ := fun j i => cw j (e.symm i)
  have hMM : ((1 / 8 : ℂ) • M) * M.transpose = 1 := by
    ext j k
    rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply]
    simp only [M, Matrix.transpose_apply]
    rw [show (∑ i, cw j (e.symm i) * cw k (e.symm i)) = ∑ a, cw j a * cw k a from
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl), cw_orth]
    split_ifs <;> norm_num
  have h2 := mul_eq_one_comm.mp hMM
  have h3 := congrFun (congrFun h2 (e a)) (e b)
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] at h3
  simp only [M, Matrix.transpose_apply, Equiv.symm_apply_apply, smul_eq_mul] at h3
  split_ifs with hab
  · rw [if_pos (congrArg e hab)] at h3
    have : ∑ j, cw j a * cw j b = 8 * ((1 / 8) * ∑ j, cw j a * cw j b) := by ring
    rw [this, h3]; norm_num
  · rw [if_neg (fun h => hab (e.injective h))] at h3
    have : ∑ j, cw j a * cw j b = 8 * ((1 / 8) * ∑ j, cw j a * cw j b) := by ring
    rw [this, h3]; norm_num

/-- `e_a = ⅛ Σ_j (w_j)_a w_j` in the orthonormal coordinates. -/
theorem single_eq_sum_cw (a : Fin (rank leech)) :
    (Pi.single a (1 : ℂ) : Fin (rank leech) → ℂ) = ∑ j, (cw j a / 8) • cw j := by
  funext b
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, ← Finset.sum_div, cw_complete,
    Pi.single_apply]
  split_ifs with h1 h2 h2
  · norm_num
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · norm_num

/-! ## §3  The block-monomial map `φ_τ` -/

/-- The constant coefficient of the `e^n`-component, as a functional on `V_Λ⁺`. -/
noncomputable def coefN (n : leech.carrier) : VPlus →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ 0) ∘ₗ coordEα leech n ∘ₗ (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype

open Classical in
theorem neg_not_mem_halfFourChi {m : leech.carrier} (hm : m ∈ halfFourChi 1) : -m ∉ halfFourChi 1 := by
  intro h
  have h1 : m ∈ halfFour leech leech_posDef := (Finset.mem_filter.mp hm).1
  have h2 : -m ∈ halfFour leech leech_posDef := (Finset.mem_filter.mp h).1
  have hd := Finset.disjoint_left.mp (disjoint_halfFour_neg leech leech_posDef) h2
  apply hd
  exact Finset.mem_image.mpr ⟨m, h1, rfl⟩

open Classical in
theorem coefN_frameX0P {n m : leech.carrier} (hn : n ∈ halfFourChi 1) (hm : m ∈ halfFourChi 1) :
    coefN n (frameX0P m) = if n = m then 1 else 0 := by
  change MvPolynomial.coeff 0 (coordEα leech n (frameX0 m)) = _
  rw [frameX0, map_add, coordEα_latChargeGen, coordEα_latChargeGen,
    if_neg (show n ≠ -m from fun h => neg_not_mem_halfFourChi hm (h ▸ hn)), add_zero]
  split_ifs <;> simp [vacuumN]

/-- **The block-monomial top map** `φ_τ (e^n + e^{−n}) = h_{w_{j(n)}}(−½) ⊗ τ(n)` (`n ∈ S₁`,
`j(n) = blk n` the position of the entry `±3`), for an arbitrary assignment `τ : S₁ → T`. -/
noncomputable def phiV3 (τ : leech.carrier → TLeechT) : VPlus →ₗ[ℂ] TP :=
  ∑ n ∈ halfFourChi 1, (coefN n).smulRight (hP (cw (blk n)) (τ n))

theorem phiV3_frameX0P (τ : leech.carrier → TLeechT) {m : leech.carrier} (hm : m ∈ halfFourChi 1) :
    phiV3 τ (frameX0P m) = hP (cw (blk m)) (τ m) := by
  rw [phiV3, LinearMap.sum_apply, Finset.sum_eq_single m]
  · rw [LinearMap.smulRight_apply, coefN_frameX0P hm hm, if_pos rfl, one_smul]
  · intro n hn hnm
    rw [LinearMap.smulRight_apply, coefN_frameX0P hn hm, if_neg hnm, zero_smul]
  · intro h; exact absurd hm h

theorem phiV3_mem_weight (τ : leech.carrier → TLeechT) (x : VPlus) :
    phiV3 τ x ∈ plusModule.weight (2 : ℂ) := by
  rw [phiV3, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (hP_mem_weight _ _)

theorem phiV3_mem_frame {s : ZMod 2} {τ : leech.carrier → TLeechT}
    (hτ : ∀ n ∈ halfFourChi 1, τ n ∈ leechFrameT s) (x : VPlus) : phiV3 τ x ∈ TPframe s := by
  rw [phiV3, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ (hP_mem_frame _ (hτ n hn))

/-- `φ_τ` hits `x0T t₀` as soon as every block contains a vector with `τ = t₀`. -/
theorem phiV3_hits {τ : leech.carrier → TLeechT} {t₀ : TLeechT} (hblk : ∀ j, τ (nvec j) = t₀) :
    ∃ x ∈ OmegaV3, phiV3 τ x = x0T t₀ := by
  set c0 : Fin (rank leech) := Fin.cast leech_rank.symm 0
  refine ⟨∑ j, (cw j c0 / 8) • frameX0P (nvec j),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (frameX0P_mem_OmegaV3 (nvec_mem j)), ?_⟩
  rw [map_sum, x0T_eq_hP, single_eq_sum_cw, hP_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, phiV3_frameX0P τ (nvec_mem j), blk_nvec, hblk, hP_smul_left]

/-- **The diagonal frame letters intertwine**: `φ_τ(o(w_j(−1)²𝟙) x) = o(σ(w_j(−1)²𝟙)) φ_τ(x)`
on `(V₃⁺)₂`, for every `τ`. -/
theorem phiV3_ZM_diag (τ : leech.carrier → TLeechT) (j : Fin 24) :
    ZM (phiV3 τ) OmegaV3 (dV (fw j) (fw j)) := by
  refine ZM_of_basis _ _ fun n hn => ?_
  obtain ⟨h4, h1⟩ := mem_halfFourChi hn
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, h1]; exact one_ne_zero
  rw [actV_dV_fw hn0 h4, map_smul, phiV3_frameX0P τ hn, sig_dV_fw, actT_dV_fw_hP]

/-! ## §4  Frame form of the basis reduction -/

/-- The bilinear map `(x, y) ↦ Σ_{a,b} x_a y_b h_a(−1)h_b(−1)𝟙`. -/
noncomputable def Bq : (Fin (rank leech) → ℂ) →ₗ[ℂ] (Fin (rank leech) → ℂ) →ₗ[ℂ] V0Sub.carrier :=
  LinearMap.mk₂ ℂ (fun x y => ∑ a, ∑ b, (x a * y b) • qV a b)
    (fun x x' y => by simp only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib])
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← smul_smul, Finset.smul_sum])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring_nf)

theorem Bq_apply (x y : Fin (rank leech) → ℂ) : Bq x y = ∑ a, ∑ b, (x a * y b) • qV a b := rfl

theorem Bq_cw (j k : Fin 24) : Bq (cw j) (cw k) = dV (fw j) (fw k) := by
  rw [Bq_apply, dV_eq_sum]; rfl

theorem Bq_single (a b : Fin (rank leech)) : Bq (Pi.single a 1) (Pi.single b 1) = qV a b := by
  rw [Bq_apply, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb; simp [hb]
  · simp
  · intro a' _ ha; simp [Pi.single_apply, ha]
  · simp

/-- `h_a(−1)h_b(−1)𝟙 = (1/64) Σ_{j,k} (w_j)_a (w_k)_b w_j(−1)w_k(−1)𝟙`. -/
theorem qV_eq_sum_dV (a b : Fin (rank leech)) :
    qV a b = ∑ j, ∑ k, ((cw j a / 8) * (cw k b / 8)) • dV (fw j) (fw k) := by
  rw [← Bq_single, single_eq_sum_cw a, single_eq_sum_cw b, LinearMap.map_sum₂]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul₂, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Bq_cw, smul_smul]

theorem qV_mem_span_dV (a b : Fin (rank leech)) :
    qV a b ∈ span ℂ (Set.range fun p : Fin 24 × Fin 24 => dV (fw p.1) (fw p.2)) := by
  rw [qV_eq_sum_dV]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (subset_span ⟨(j, k), rfl⟩)

/-! ## §5  Assembly -/

/-- **`TopSigmaV3` for `φ_τ`, conditional on the off-diagonal and lattice letters.**
Given a `τ` valued in `T_s` hitting a common `t₀ ≠ 0` in every block, Zhu generation by
`G = (V₀⁺)₂`, and the zero-mode identities for the off-diagonal frame letters `w_j(−1)w_k(−1)𝟙`
(`j ≠ k`) and the lattice letters `e^γ + e^{−γ}` (`γ ∈ S₀`), the residual `TopSigmaV3 s φ_τ`
holds (the diagonal letters are proved: `phiV3_ZM_diag`). -/
theorem topSigmaV3_of_offdiag {s : ZMod 2} {τ : leech.carrier → TLeechT}
    (hτ : ∀ n ∈ halfFourChi 1, τ n ∈ leechFrameT s) {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s)
    (h0 : t₀ ≠ 0) (hblk : ∀ j, τ (nvec j) = t₀) (hZhu : ZhuGenerated G2)
    (hoff : ∀ j k : Fin 24, j ≠ k → ZM (phiV3 τ) OmegaV3 (dV (fw j) (fw k)))
    (hlat : ∀ γ ∈ halfFourChi 0, ZM (phiV3 τ) OmegaV3 (lV' γ)) :
    TopSigmaV3 s (phiV3 τ) := by
  have hdV : ∀ j k : Fin 24, ZM (phiV3 τ) OmegaV3 (dV (fw j) (fw k)) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; exact phiV3_ZM_diag τ j
    · exact hoff j k hjk
  refine topSigmaV3_of_zhuGenerated (fun x _ => phiV3_mem_frame hτ x)
    (fun x _ => phiV3_mem_weight τ x) hZhu ?_ ⟨t₀, ht₀, h0, phiV3_hits hblk⟩
  refine hGφ_V3_of_basis _ (fun a b n hn => ?_) (fun γ hγ n hn => hlat γ hγ _ (frameX0P_mem_OmegaV3 hn))
  have hq := ZM_span (phiV3 τ) OmegaV3 (S := Set.range fun p : Fin 24 × Fin 24 => dV (fw p.1) (fw p.2))
    (by rintro _ ⟨p, rfl⟩; exact hdV p.1 p.2) (qV a b) (qV_mem_span_dV a b)
  exact hq _ (frameX0P_mem_OmegaV3 hn)

/-- **The proved part of (R-top) on `V₃⁺`.**  For every `s`, there is a linear `φ` such that
`φ(V₃⁺)₂ ⊆ (T_s⁺)₂`, `φ` hits a cyclic vector `x0T t₀`, and `φ` intertwines the zero modes of the
24 diagonal frame letters `w_j(−1)²𝟙 ∈ G` with those of their `σ`-images (`σ` fixes them). -/
theorem topSigmaV3_partial (s : ZMod 2) :
    ∃ φ : VPlus →ₗ[ℂ] TP, (∀ x ∈ OmegaV3, φ x ∈ TPframe s) ∧
      (∀ x ∈ OmegaV3, φ x ∈ plusModule.weight (2 : ℂ)) ∧
      (∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, φ x = x0T t₀) ∧
      (∀ j : Fin 24, ∀ x ∈ OmegaV3,
        φ (actV (dV (fw j) (fw j)) 1 x) = actT (sig (dV (fw j) (fw j))) 1 (φ x)) := by
  obtain ⟨t₀, ht₀, h0⟩ := exists_ne_zero_leechFrameT s
  refine ⟨phiV3 (fun _ => t₀), fun x _ => phiV3_mem_frame (fun _ _ => ht₀) x,
    fun x _ => phiV3_mem_weight _ x, ⟨t₀, ht₀, h0, phiV3_hits (fun _ => rfl)⟩,
    fun j => phiV3_ZM_diag _ j⟩

end VOA.Moonshine.SigmaTop
