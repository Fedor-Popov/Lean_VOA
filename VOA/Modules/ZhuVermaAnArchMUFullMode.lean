/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullGrading
import VOA.Modules.ZhuRingResidue

/-!
# The `𝒱`-modes `u_p` of DJ's induced module `M(U)` — the field `Y_{M(U)}(u,z)`

Dong–Jiang (`math/0601626`, §4, just before Lemma 4.6) define the `𝒱`-action on
`M(U) = ⊕_n A_{n,m}(V)⊗_{A_m(V)}U` by, for homogeneous `u ∈ V` and `p ∈ ℤ`,

  `u_p : M(U)(n) → M(U)(wt u − p − 1 + n)`,
  `u_p(v ⊗ w) = (u ∗^{wt u − p − 1 + n}_{m,n} v) ⊗ w`   if `wt u − 1 − p + n ≥ 0`, and `0` otherwise,

and set `Y_M(u,z) = ∑_p u_p z^{−p−1}`.  This file builds exactly that, at the repo's base level
`m = 0`, out of the unconditional mode operators `oFullU` (`ZhuVermaAnArchMUFullActionU`, DJ's
`o_{n,m}(u)` on the genuine full ideal):

* `oLevelIncl W U k p n a` — the level-`n` component `M(U)(n) → M(U)` of `a_p` for `a` of weight `k`
  (the DJ case split on `k − p − 1 + n ≥ 0`);
* `muFullMode W U p a : End ℂ (MUFull W U)` — the mode `a_p`, extended over the grade decomposition
  of `a` exactly as `resHom` extends the FZ residue (`ZhuVermaAnBimodule`);
* `muFullYM W U : 𝒱 →ₗ[ℂ] (End ℂ (MUFull W U))⟦z^±⟧` — the state–field correspondence
  `Y_{M(U)}(u,z)`, with `mode (muFullYM W U u) p = muFullMode W U p u`.

and discharges **DJ Lemma 4.6** at `m = 0`:

* `muFullMode_truncation` — 4.6(1), each `Y_{M(U)}(u,z)` is a field (lower truncation);
* `muFullYM_vacuum` — 4.6(2), `Y_{M(U)}(𝟙,z) = id`.  At `m = 0` DJ's binomial computation collapses:
  `𝟙 ∗^{n−p−1}_{0,n} v` picks out the single residue index `i = p+1` with coefficient `C(0, p+1)`,
  which vanishes unless `p = −1`, where it is `1`.

What is NOT here is the module Jacobi (DJ Lemma 4.7 + Corollary after Lemma 4.9, i.e. the commutator
formula together with associativity); `MUFull` is therefore not yet a `WeakModule`.  The
multiplicative core `oFullU_comp` (DJ Lemma 4.1) is already unconditional.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (the definition of `u_p`, Lemma 4.6, Lemma 4.7, Cor. after 4.9,
Thm 4.10); Gannon Def. 5.3.1a–b; `ZhuVermaAnArchMUFullActionU` (`oFullU`, `oFullU_comp`),
`ZhuVermaAnBimodule` (`resHom`, the grade-decomposition extension idiom),
`ZhuRingResidue` (`reduce_homogeneous`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The level-`n` component of the mode `a_p`. -/

/-- **The target level of `a_p` on `M(U)(n)`** for `a` of weight `k`: DJ's `wt a − p − 1 + n`. -/
def muTargetLevel (k p : ℤ) (n : ℕ) : ℤ := k - p - 1 + (n : ℤ)

/-- **The level-`n` component of the mode `a_p`** (`a` homogeneous of weight `k`):
`M(U)(n) → M(U)`, landing in level `k − p − 1 + n` when that is `≥ 0` (via DJ's `o_{n',n}(a)`,
`oFullU`), and `0` otherwise.  This is Dong–Jiang's defining case split for `u_p`. -/
noncomputable def oLevelIncl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (k p : ℤ) (n : ℕ) (a : 𝒱) :
    MUPieceFull W U n →ₗ[ℂ] MUFull W U :=
  if 0 ≤ muTargetLevel k p n then
    (MUFull.incl W U (muTargetLevel k p n).toNat).comp
      (oFullU W U (muTargetLevel k p n).toNat n a)
  else 0

theorem oLevelIncl_of_neg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {n : ℕ}
    (h : muTargetLevel k p n < 0) (a : 𝒱) : oLevelIncl W U k p n a = 0 := by
  simp only [oLevelIncl, if_neg (not_le.mpr h)]

theorem oLevelIncl_of_nonneg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {n : ℕ}
    (h : 0 ≤ muTargetLevel k p n) (a : 𝒱) :
    oLevelIncl W U k p n a
      = (MUFull.incl W U (muTargetLevel k p n).toNat).comp
          (oFullU W U (muTargetLevel k p n).toNat n a) := by
  simp only [oLevelIncl, if_pos h]

/-- The level component with the target level named explicitly (avoids `Int.toNat` in the
dependent position). -/
theorem oLevelIncl_eq_of_target (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {n N : ℕ}
    (h : muTargetLevel k p n = (N : ℤ)) (a : 𝒱) :
    oLevelIncl W U k p n a = (MUFull.incl W U N).comp (oFullU W U N n a) := by
  have hA : (muTargetLevel k p n).toNat = N := by rw [h]; exact Int.toNat_natCast N
  have hnn : 0 ≤ muTargetLevel k p n := by rw [h]; positivity
  subst hA
  exact oLevelIncl_of_nonneg W U hnn a

/-! ## Linearity of `oFullU` and `oLevelIncl` in the acting vector. -/

theorem oFullU_add_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (a b : 𝒱) :
    oFullU W U n m (a + b) = oFullU W U n m a + oFullU W U n m b := by
  apply TensorProduct.ext'
  intro y w
  obtain ⟨g, rfl⟩ := (OnmFull W m 0).mkQ_surjective y
  show oFullU W U n m (a + b) (mkAnmFull W m 0 g ⊗ₜ[ℂ] w) = _
  rw [oFullU_tmul]
  show _ = oFullU W U n m a (mkAnmFull W m 0 g ⊗ₜ[ℂ] w)
      + oFullU W U n m b (mkAnmFull W m 0 g ⊗ₜ[ℂ] w)
  rw [oFullU_tmul, oFullU_tmul, anmGen_add_left, map_add, TensorProduct.add_tmul]

theorem oFullU_smul_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (c : ℂ) (a : 𝒱) :
    oFullU W U n m (c • a) = c • oFullU W U n m a := by
  apply TensorProduct.ext'
  intro y w
  obtain ⟨g, rfl⟩ := (OnmFull W m 0).mkQ_surjective y
  show oFullU W U n m (c • a) (mkAnmFull W m 0 g ⊗ₜ[ℂ] w) = _
  rw [oFullU_tmul]
  show _ = c • oFullU W U n m a (mkAnmFull W m 0 g ⊗ₜ[ℂ] w)
  rw [oFullU_tmul, anmGen_smul_left, map_smul, TensorProduct.smul_tmul']

theorem oLevelIncl_add_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (k p : ℤ) (n : ℕ)
    (a b : 𝒱) :
    oLevelIncl W U k p n (a + b) = oLevelIncl W U k p n a + oLevelIncl W U k p n b := by
  by_cases h : 0 ≤ muTargetLevel k p n
  · rw [oLevelIncl_of_nonneg W U h, oLevelIncl_of_nonneg W U h, oLevelIncl_of_nonneg W U h,
      oFullU_add_acting]
    exact LinearMap.comp_add _ _ _
  · rw [oLevelIncl_of_neg W U (not_le.mp h), oLevelIncl_of_neg W U (not_le.mp h),
      oLevelIncl_of_neg W U (not_le.mp h), add_zero]

theorem oLevelIncl_smul_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (k p : ℤ) (n : ℕ)
    (c : ℂ) (a : 𝒱) :
    oLevelIncl W U k p n (c • a) = c • oLevelIncl W U k p n a := by
  by_cases h : 0 ≤ muTargetLevel k p n
  · rw [oLevelIncl_of_nonneg W U h, oLevelIncl_of_nonneg W U h, oFullU_smul_acting]
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
  · rw [oLevelIncl_of_neg W U (not_le.mp h), oLevelIncl_of_neg W U (not_le.mp h), smul_zero]

/-! ## The mode `a_p` as an endomorphism of `M(U)`, extended over the grading. -/

/-- **The mode `a_p` for `a` homogeneous of weight `k`**, assembled from the level components by
the universal property of the direct sum `M(U) = ⊕_n M(U)(n)`. -/
noncomputable def muFullModeFamily (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (k : ℤ) :
    (W.grading k) →ₗ[ℂ] Module.End ℂ (MUFull W U) where
  toFun ak := DirectSum.toModule ℂ ℕ (MUFull W U) (fun n => oLevelIncl W U k p n (ak : 𝒱))
  map_add' a b := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, DirectSum.toModule_lof,
      Submodule.coe_add, oLevelIncl_add_acting]
  map_smul' c a := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, DirectSum.toModule_lof,
      SetLike.val_smul, oLevelIncl_smul_acting, RingHom.id_apply, LinearMap.smul_apply]

/-- **The mode `a_p` of `Y_{M(U)}`** for arbitrary `a ∈ 𝒱`, extended over the grade decomposition
of `a` (the `resHom` idiom). -/
noncomputable def muFullMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (a : 𝒱) :
    Module.End ℂ (MUFull W U) :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (muFullModeFamily W U p)) (DirectSum.decompose W.grading a)

/-- On a homogeneous `a ∈ 𝒱_k` the mode collapses to the single weight-`k` slice. -/
theorem muFullMode_homogeneous (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) :
    muFullMode W U p a = DirectSum.toModule ℂ ℕ (MUFull W U)
      (fun n => oLevelIncl W U k p n a) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : muFullMode W U p a = muFullModeFamily W U p k ⟨a, ha⟩ := by
    change (DFinsupp.lsum ℂ (muFullModeFamily W U p)) (DirectSum.decompose W.grading a) = _
    rw [DirectSum.decompose_of_mem W.grading ha]
    exact DFinsupp.lsum_single ℂ (muFullModeFamily W U p) k ⟨a, ha⟩
  rw [hcollapse]; rfl

theorem muFullMode_add_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (a b : 𝒱) :
    muFullMode W U p (a + b) = muFullMode W U p a + muFullMode W U p b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_add ((DFinsupp.lsum ℂ (muFullModeFamily W U p)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) a b

theorem muFullMode_smul_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) (c : ℂ) (a : 𝒱) :
    muFullMode W U p (c • a) = c • muFullMode W U p a := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_smul ((DFinsupp.lsum ℂ (muFullModeFamily W U p)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) c a

@[simp] theorem muFullMode_zero_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) :
    muFullMode W U p (0 : 𝒱) = 0 := by
  have := muFullMode_smul_acting W U p (0 : ℂ) (0 : 𝒱)
  simpa using this

/-- Endomorphisms of `M(U)` agreeing on every level piece are equal. -/
theorem muFull_end_ext (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    {f g : Module.End ℂ (MUFull W U)}
    (h : ∀ (n : ℕ) (x : MUPieceFull W U n),
      f (MUFull.incl W U n x) = g (MUFull.incl W U n x)) : f = g :=
  DirectSum.linearMap_ext ℂ (fun n => LinearMap.ext (fun x => h n x))

/-- The mode `a_p` on a homogeneous level-`n` vector: DJ's defining formula. -/
theorem muFullMode_apply_incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (n : ℕ) (x : MUPieceFull W U n) :
    muFullMode W U p a (MUFull.incl W U n x) = oLevelIncl W U k p n a x := by
  rw [muFullMode_homogeneous W U p ha]
  exact DirectSum.toModule_lof ℂ n x

/-! ## DJ Lemma 4.6(1) — each `Y_{M(U)}(u,z)` is a field (lower truncation). -/

/-- The mode `a_p` annihilates the level-`n` piece as soon as `p` exceeds `k + n − 1`
(`k = wt a`): DJ's case `wt a − 1 − p + n < 0`. -/
theorem muFullMode_incl_eq_zero (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {k p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) {n : ℕ} (hp : k + (n : ℤ) ≤ p) (x : MUPieceFull W U n) :
    muFullMode W U p a (MUFull.incl W U n x) = 0 := by
  rw [muFullMode_apply_incl W U p ha n x]
  have hneg : muTargetLevel k p n < 0 := by
    simp only [muTargetLevel]; omega
  rw [oLevelIncl_of_neg W U hneg]
  rfl

/-- **DJ Lemma 4.6(1)** — lower truncation: for every `u ∈ 𝒱` and `x ∈ M(U)` there is `N` with
`u_p x = 0` for all `p ≥ N`.  So each `Y_{M(U)}(u,z)` is a field. -/
theorem muFullMode_truncation (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (u : 𝒱)
    (x : MUFull W U) : ∃ N : ℤ, ∀ p : ℤ, N ≤ p → muFullMode W U p u x = 0 := by
  -- First fix `u` homogeneous and induct on `x`; then reduce `u` to homogeneous.
  refine reduce_homogeneous W (P := fun u => ∃ N : ℤ, ∀ p : ℤ, N ≤ p → muFullMode W U p u x = 0)
    ?_ ?_ ?_ u
  · -- homogeneous `a ∈ 𝒱_k`
    intro k a ha
    have key : ∀ y : MUFull W U, ∃ N : ℤ, ∀ p : ℤ, N ≤ p → muFullMode W U p a y = 0 := by
      intro y
      refine DirectSum.induction_on y ⟨0, fun p _ => map_zero _⟩ ?_ ?_
      · intro n z
        exact ⟨k + (n : ℤ), fun p hp => muFullMode_incl_eq_zero W U ha hp z⟩
      · rintro y₁ y₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨max N₁ N₂, fun p hp => ?_⟩
        rw [map_add, h₁ p (le_trans (le_max_left _ _) hp), h₂ p (le_trans (le_max_right _ _) hp),
          add_zero]
    exact key x
  · exact ⟨0, fun p _ => by rw [muFullMode_zero_acting]; rfl⟩
  · rintro u₁ u₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun p hp => ?_⟩
    rw [muFullMode_add_acting, LinearMap.add_apply, h₁ p (le_trans (le_max_left _ _) hp),
      h₂ p (le_trans (le_max_right _ _) hp), add_zero]

/-! ## DJ Lemma 4.6(2) — `Y_{M(U)}(𝟙, z) = id`.

At the repo's base level `m = 0` Dong–Jiang's binomial computation collapses completely: the vacuum
residue `resHom W 0 P 𝟙 x = C(0, P−1) • x` survives only at `P = 1`, pinning the summation index of
`𝟙 ∗^{n'}_{0,n} x` to `i = n − n'`, where the *outer* binomial is `C(0, n−n')` — zero unless
`n' = n`.  So `𝟙 ∗^{n'}_{0,n} x = 0` for `n' ≠ n` **exactly in `𝒱`** (not merely mod `O`), and
`𝟙 ∗ⁿ_{0,n} x = x` (`anmGen_vacuum_diag`).  Hence `𝟙_p = δ_{p,−1}·id`. -/

/-- `cbz 0 j = 0` for every `j ≠ 0` (the top-`0` generalized binomial). -/
private theorem cbz_zero_top {j : ℤ} (hj : j ≠ 0) : cbz 0 j = 0 := by
  rcases lt_trichotomy j 0 with h | h | h
  · exact cbz_apply_neg 0 h
  · exact absurd h hj
  · exact cbz_lt (le_refl 0) h

/-- `resHom W m P 𝟙 x = C(m, P−1) • x`: the vacuum residue picks the single mode `ℓ = P−1`. -/
private theorem resHom_vacuum' (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (P : ℤ) (x : 𝒱) :
    resHom W (m : ℤ) P W.vacuum x = cbz (m : ℤ) (P - 1) • x := by
  rw [resHom_homogeneous W (m : ℤ) P (vacuum_mem_grading_zero W) x, zero_add]
  have hterm : ∀ ℓ ∈ Finset.range ((m : ℤ).toNat + 1),
      cbz (m : ℤ) (ℓ : ℤ) • W.smul W.vacuum ((ℓ : ℤ) - P) x
        = (if (ℓ : ℤ) - P = -1 then cbz (m : ℤ) (ℓ : ℤ) • x else 0) := by
    intro ℓ _
    rw [show W.smul W.vacuum ((ℓ : ℤ) - P) x
          = PreVertexAlgebra.smul W.toPreVertexAlgebra W.vacuum ((ℓ : ℤ) - P) x from rfl,
        PreVertexAlgebra.smul_vacuum_left]
    split_ifs with h1
    · rfl
    · rw [smul_zero]
  rw [Finset.sum_congr rfl hterm]
  rcases le_or_gt 0 (P - 1) with hPnn | hPneg
  · rcases le_or_gt (P - 1) (m : ℤ) with hPle | hPgt
    · rw [Finset.sum_eq_single (P - 1).toNat]
      · rw [show (((P - 1).toNat : ℤ)) = P - 1 from Int.toNat_of_nonneg hPnn,
            if_pos (by ring)]
      · intro ℓ _ hℓ
        rw [if_neg]
        intro hc
        exact hℓ (by omega)
      · intro hmem
        exact absurd (by simp only [Finset.mem_range]; omega) hmem
    · rw [cbz_lt (by positivity) (by omega), zero_smul]
      refine Finset.sum_eq_zero fun ℓ hℓ => ?_
      simp only [Finset.mem_range] at hℓ
      rw [if_neg (by omega)]
  · rw [cbz_apply_neg (m : ℤ) hPneg, zero_smul]
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    rw [if_neg (by omega)]

/-- **The vacuum annihilates off the diagonal**: `𝟙 ∗^{n'}_{0,n} x = 0` whenever `n' ≠ n`.
(On the diagonal `n' = n` it is the identity, `anmGen_vacuum_diag`.)  This is the `m = 0` collapse of
Dong–Jiang's Lemma 4.6(2) computation. -/
theorem anmGen_vacuum_offdiag (W : VertexOperatorAlgebra 𝒱) {n' n : ℕ} (h : n' ≠ n) (x : 𝒱) :
    anmGen W n' 0 n W.vacuum x = 0 := by
  rw [anmGen]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [resHom_vacuum' W 0 _ x]
  by_cases hz : ((0 : ℕ) : ℤ) + (n' : ℤ) - (n : ℤ) + (i : ℤ) = 0
  · -- the residue survives, but then the outer binomial is `C(0, i)` with `i = n − n' ≠ 0`.
    have hi : (i : ℤ) ≠ 0 := by omega
    rw [show (((0 : ℕ) : ℤ) + (n' : ℤ) - (n : ℤ) + (i : ℤ)) = 0 from hz,
      cbz_zero_top hi, mul_zero, zero_smul]
  · -- the residue itself vanishes.
    have hne : ((0 : ℕ) : ℤ) + (n' : ℤ) - (n : ℤ) + (i : ℤ) + 1 - 1 ≠ 0 := by omega
    rw [show (((0 : ℕ) : ℤ)) = 0 from rfl] at hne ⊢
    rw [cbz_zero_top hne, zero_smul, smul_zero]

/-- The `M(U)` mode operator of the vacuum vanishes off the diagonal. -/
theorem oFullU_vacuum_offdiag (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {n' n : ℕ}
    (h : n' ≠ n) : oFullU W U n' n W.vacuum = 0 := by
  apply TensorProduct.ext'
  intro y w
  obtain ⟨g, rfl⟩ := (OnmFull W n 0).mkQ_surjective y
  show oFullU W U n' n W.vacuum (mkAnmFull W n 0 g ⊗ₜ[ℂ] w) = 0
  rw [oFullU_tmul, anmGen_vacuum_offdiag W h g, map_zero, TensorProduct.zero_tmul]

/-- The `M(U)` mode operator of the vacuum is the identity on the diagonal. -/
theorem oFullU_vacuum_diag (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    oFullU W U n n W.vacuum = LinearMap.id := by
  apply TensorProduct.ext'
  intro y w
  obtain ⟨g, rfl⟩ := (OnmFull W n 0).mkQ_surjective y
  show oFullU W U n n W.vacuum (mkAnmFull W n 0 g ⊗ₜ[ℂ] w) = _
  rw [oFullU_tmul, anmGen_vacuum_diag W n 0 g]
  rfl

/-- **DJ Lemma 4.6(2)** — `𝟙_p = δ_{p,−1}·id` on `M(U)`, i.e. `Y_{M(U)}(𝟙,z) = id`. -/
theorem muFullMode_vacuum (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℤ) :
    muFullMode W U p W.vacuum = if p = -1 then (1 : Module.End ℂ (MUFull W U)) else 0 := by
  rw [muFullMode_homogeneous W U p (vacuum_mem_grading_zero W)]
  refine DirectSum.linearMap_ext ℂ (fun n => ?_)
  refine LinearMap.ext (fun x => ?_)
  rw [LinearMap.comp_apply, DirectSum.toModule_lof]
  by_cases hp : p = -1
  · subst hp
    have hT : muTargetLevel 0 (-1) n = (n : ℤ) := by simp only [muTargetLevel]; ring
    rw [oLevelIncl_eq_of_target W U hT, if_pos rfl, LinearMap.comp_apply,
      oFullU_vacuum_diag W U n]
    rfl
  · rw [if_neg hp]
    by_cases hT : 0 ≤ muTargetLevel 0 p n
    · have hEq : muTargetLevel 0 p n = (((muTargetLevel 0 p n).toNat : ℕ) : ℤ) :=
        (Int.toNat_of_nonneg hT).symm
      have hne : (muTargetLevel 0 p n).toNat ≠ n := by
        simp only [muTargetLevel] at hT ⊢
        omega
      rw [oLevelIncl_eq_of_target W U hEq, LinearMap.comp_apply,
        oFullU_vacuum_offdiag W U hne]
      simp
    · rw [oLevelIncl_of_neg W U (not_le.mp hT)]
      simp

/-! ## The state–field correspondence `Y_{M(U)}(u,z)`. -/

/-- **`Y_{M(U)}(u,z) = ∑_p u_p z^{−p−1}`** — DJ's state–field correspondence on `M(U)`, as a
`ℂ`-linear map into formal `End`-valued distributions. -/
noncomputable def muFullYM (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    𝒱 →ₗ[ℂ] (Module.End ℂ (MUFull W U))⟦z^±⟧ where
  toFun a := fun j => muFullMode W U (-j - 1) a
  map_add' a b := by
    funext j; exact muFullMode_add_acting W U (-j - 1) a b
  map_smul' c a := by
    funext j; exact muFullMode_smul_acting W U (-j - 1) c a

/-- The `p`-th mode of `Y_{M(U)}(a,z)` is exactly `a_p = muFullMode W U p a`. -/
@[simp] theorem mode_muFullYM (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (a : 𝒱) (p : ℤ) :
    mode (muFullYM W U a) p = muFullMode W U p a := by
  show muFullMode W U (-(-p - 1) - 1) a = muFullMode W U p a
  congr 1
  ring

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.muFullMode
  #print axioms VOA.muFullMode_truncation
  #print axioms VOA.muFullYM
-/
