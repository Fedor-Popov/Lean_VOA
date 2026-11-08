/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.AutZeroModesTwisted
import VOA.Moonshine.AutFockEigen

/-!
# No joint `q_ab`-eigenvector of eigenvalue `ββᵀ` in the twisted sector
(Aut(V♮) campaign, step 3, route C, node C4 of `Notes/MONSTER_AUT_PLAN.md`)

On the twisted sector `S[θ] ⊗ T` the zero modes of the quadratic states `q_ab = h_a(−1)h_b(−1)𝟙`
are `o(q_ab) = (N^tw_ab + δ_ab/8) ⊗ 1` (`AutZeroModesTwisted`), with
`N^tw_ab = Σ_k (k+½)(X_{(k,a)}∂_{(k,b)} + X_{(k,b)}∂_{(k,a)}) = quadOp (k+½) K a b`.

* Decompose `t ∈ S[θ] ⊗ T` along a basis `𝒞` of `T`: `t = Σ_i p_i ⊗ 𝒞_i`.  The operators
  `A ⊗ 1` act componentwise (`component_rTensor`), so every Fock component `p_i` of a joint
  eigenvector is a joint eigenvector with the same eigenvalues.
* For a nonzero joint eigenvector `p ∈ S[θ]` the joint-eigenvector lemma
  `HeisenbergN.quadOp_joint_eigen` (weights `μ k = k + ½`, injective, `μ k + μ k' > 0`) forces
  the eigenvalues of `N^tw_ab` to vanish, i.e. the eigenvalues of `o(q_ab)` are exactly `δ_ab/8`
  (`quadNT_joint_eigen`, `rTensor_joint_eigen`).
* An outer product `β_a β_b` is never `δ_ab/8` in rank `≥ 2`: with `a ≠ b`,
  `(β_a β_b)² = β_a² β_b² = 1/64 ≠ 0` contradicts `β_a β_b = 0` (`not_outer_eq_delta`).

Hence no nonzero `t` has eigenvalues `ββᵀ` — including `β = 0`.

## Main results
* ⭐ `quadNT_joint_eigen` — on `FockT r` (rank `≥ 2`): a nonzero joint eigenvector of all
  `N^tw_ab + δ_ab/8` has eigenvalues exactly `δ_ab/8`.
* ⭐ `rTensor_joint_eigen` — the same on `FockT r ⊗ T` for any complex vector space `T`.
* ⭐ `rTensor_outer_eigen_eq_zero` — a joint eigenvector of eigenvalue `β_a β_b` is `0`.
* ⭐ `leech_twisted_outer_eigen_eq_zero` — on `Tw = FockT 24 ⊗ T_Λ`.
* ⭐ `VnatVOA_twisted_outer_eigen_eq_zero` — the `T⁺` block of `V♮`: if
  `(u,0)₍₁₎ (0,t) = β'_a β'_b (0,t)` for all `a, b` and all `u ∈ V_Λ⁺` with
  `u = h_a(−1)h_b(−1)𝟙` (`LatGen.quadState`, the `chargeCoord` frame), then `t = 0`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
(`exists_ne_of_two_le`: `[propext, Quot.sound]`); checked with
`lake build VOA.Moonshine.AutTwistedExclusion` green (9,104 jobs).  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.AutZeroTw

open VOA VOA.Moonshine MvPolynomial TwistedHeisenberg HeisenbergN
open VOA.IntegralLattice VOA.LatGen VOA.Moonshine.LatticeTwisted VOA.Moonshine.Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

/-! ## §1  The Fock lemma for the twisted weights `k + ½` -/

section Fock

variable {r : ℕ}

/-- In rank `≥ 2` every direction has a different one. -/
theorem exists_ne_of_two_le (hr : 2 ≤ r) (b : Fin r) : ∃ a : Fin r, a ≠ b := by
  by_cases hb : b.val = 0
  · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
    have h' := congrArg Fin.val h
    simp only at h'
    omega
  · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
    have h' := congrArg Fin.val h
    simp only at h'
    omega

/-- The twisted weights `μ k = k + ½` have positive pairwise sums. -/
theorem halfWeight_add_ne_zero (k k' : ℕ) : ((k : ℂ) + 1 / 2) + ((k' : ℂ) + 1 / 2) ≠ 0 := by
  have h : ((k : ℂ) + 1 / 2) + ((k' : ℂ) + 1 / 2) = ((k + k' + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [h]
  exact Nat.cast_ne_zero.mpr (by omega)

/-- The twisted weights `μ k = k + ½` are injective. -/
theorem halfWeight_injective (k k' : ℕ) (h : (k : ℂ) + 1 / 2 = (k' : ℂ) + 1 / 2) : k = k' := by
  have h' : (k : ℂ) = k' := by linear_combination h
  exact_mod_cast h'

/-- ⭐ **Joint eigenvectors of the twisted zero modes on `S[θ]`**: in rank `≥ 2`, a nonzero `p`
with `(N^tw_ab + δ_ab/8) p = λ_ab p` for all `a, b` has `λ_ab = δ_ab/8`. -/
theorem quadNT_joint_eigen (hr : 2 ≤ r) (p : FockT r) (lam : Fin r → Fin r → ℂ)
    (h : ∀ a b, (quadNT r a b + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT r))) p
      = lam a b • p)
    (hp : p ≠ 0) : ∀ a b, lam a b = if a = b then (1 / 8 : ℂ) else 0 := by
  obtain ⟨K, hK⟩ := exists_levelBound r p
  have h' : ∀ a b, quadOp (fun k => (k : ℂ) + 1 / 2) K a b p
      = (lam a b - if a = b then (1 / 8 : ℂ) else 0) • p := by
    intro a b
    have e : quadOp (fun k => (k : ℂ) + 1 / 2) K a b p = quadNT r a b p :=
      (quadNT_apply r a b p K hK).symm
    have hab := h a b
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at hab
    rw [e, sub_smul, ← hab, add_sub_cancel_right]
  obtain ⟨hc, -⟩ := quadOp_joint_eigen (fun k => (k : ℂ) + 1 / 2) halfWeight_add_ne_zero
    halfWeight_injective (exists_ne_of_two_le hr) K p hK _ h' hp
  intro a b
  exact sub_eq_zero.mp (hc a b)

/-- ⭐ **An outer product is never `δ_ab/8`** (rank `≥ 2`). -/
theorem not_outer_eq_delta (hr : 2 ≤ r) (β : Fin r → ℂ) :
    ¬ ∀ a b, β a * β b = if a = b then (1 / 8 : ℂ) else 0 := by
  intro hc
  obtain ⟨a, hab⟩ := exists_ne_of_two_le hr ⟨0, by omega⟩
  set b : Fin r := ⟨0, by omega⟩
  have h1 := hc a a
  have h2 := hc b b
  have h3 := hc a b
  rw [if_pos rfl] at h1 h2
  rw [if_neg hab] at h3
  have hsq : (β a * β b) * (β a * β b) = (β a * β a) * (β b * β b) := by ring
  rw [h3, h1, h2] at hsq
  norm_num at hsq

/-- A joint eigenvector of `S[θ]` with eigenvalues `β_a β_b` is `0`. -/
theorem quadNT_outer_eigen_eq_zero (hr : 2 ≤ r) (β : Fin r → ℂ) (p : FockT r)
    (h : ∀ a b, (quadNT r a b + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT r))) p
      = (β a * β b) • p) : p = 0 := by
  by_contra hp
  exact not_outer_eq_delta hr β (quadNT_joint_eigen hr p (fun a b => β a * β b) h hp)

end Fock

/-! ## §2  The tensor factor `T` -/

section Tensor

variable {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm]

/-- `A ⊗ 1` acts componentwise along a basis of the right factor. -/
theorem component_rTensor {κ : Type*} [DecidableEq κ] (𝒞 : Module.Basis κ ℂ Tm)
    (A : End ℂ (FockT r)) (x : FockT r ⊗[ℂ] Tm) (i : κ) :
    TensorProduct.equivFinsuppOfBasisRight 𝒞 (A.rTensor Tm x) i
      = A (TensorProduct.equivFinsuppOfBasisRight 𝒞 x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      rw [LinearMap.rTensor_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
  | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

/-- ⭐ **Joint eigenvectors on `S[θ] ⊗ T`**: in rank `≥ 2`, a nonzero `t` with
`((N^tw_ab + δ_ab/8) ⊗ 1) t = λ_ab t` for all `a, b` has `λ_ab = δ_ab/8`. -/
theorem rTensor_joint_eigen (hr : 2 ≤ r) (t : FockT r ⊗[ℂ] Tm) (lam : Fin r → Fin r → ℂ)
    (h : ∀ a b, (quadNT r a b + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT r))).rTensor Tm t
      = lam a b • t)
    (ht : t ≠ 0) : ∀ a b, lam a b = if a = b then (1 / 8 : ℂ) else 0 := by
  classical
  let 𝒞 := Module.Free.chooseBasis ℂ Tm
  let e := TensorProduct.equivFinsuppOfBasisRight (M := FockT r) 𝒞
  have het : e t ≠ 0 := fun h0 => ht (e.injective (by rw [h0, map_zero]))
  obtain ⟨i, hi⟩ : ∃ i, e t i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact het (Finsupp.ext hall)
  refine quadNT_joint_eigen hr (e t i) lam (fun a b => ?_) hi
  rw [← component_rTensor 𝒞, h a b, map_smul, Finsupp.smul_apply]

/-- ⭐ **No joint eigenvector of eigenvalue `ββᵀ` on `S[θ] ⊗ T`** (rank `≥ 2`). -/
theorem rTensor_outer_eigen_eq_zero (hr : 2 ≤ r) (β : Fin r → ℂ) (t : FockT r ⊗[ℂ] Tm)
    (h : ∀ a b, (quadNT r a b + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT r))).rTensor Tm t
      = (β a * β b) • t) : t = 0 := by
  by_contra ht
  exact not_outer_eq_delta hr β (rTensor_joint_eigen hr t (fun a b => β a * β b) h ht)

end Tensor

/-! ## §3  The Leech twisted sector and the `T⁺` block of `V♮` -/

section Leech

open VOA.Moonshine.SigmaTop VOA.Moonshine.AutMonster

/-- ⭐ **No joint eigenvector of eigenvalue `ββᵀ` on `V_Λ^T = S[θ] ⊗ T_Λ`.** -/
theorem leech_twisted_outer_eigen_eq_zero (β : Fin 24 → ℂ) (t : Tw)
    (h : ∀ a b : Fin 24, (quadNT 24 a b + (if a = b then (1 / 8 : ℂ) else 0) •
        (1 : End ℂ (FockT 24))).rTensor leechT t = (β a * β b) • t) : t = 0 :=
  rTensor_outer_eigen_eq_zero (by norm_num) β t h

/-- ⭐ **Node C4: the `T⁺` block of `V♮` has no joint eigenvector of eigenvalue `β'β'ᵀ`.**
If `(u, 0)₍₁₎ (0, t) = β'_a β'_b · (0, t)` for all directions `a, b` of the `chargeCoord` frame
and all `u ∈ V_Λ⁺` with underlying state `h_a(−1)h_b(−1)𝟙`, then `t = 0`. -/
theorem VnatVOA_twisted_outer_eigen_eq_zero (β' : Fin (rank leech) → ℂ) (t : TP)
    (h : ∀ a b : Fin (rank leech), ∀ u : SkewVP,
      (u : LatModuleGen leech) = LatGen.quadState leech a b →
        VnatVOA.smul ((u, 0) : Vnat) 1 ((0, t) : Vnat) = (β' a * β' b) • ((0, t) : Vnat)) :
    t = 0 := by
  have hT : ∀ c d : Fin 24, (quadNT 24 c d + (if c = d then (1 / 8 : ℂ) else 0) •
      (1 : End ℂ (FockT 24))).rTensor leechT (t : Tw)
        = (β' (Fin.cast leech_rank.symm c) * β' (Fin.cast leech_rank.symm d)) • (t : Tw) := by
    intro c d
    have hu : ((qP (Fin.cast leech_rank.symm c) (Fin.cast leech_rank.symm d) : SkewVP) :
        LatModuleGen leech) = LatGen.quadState leech (Fin.cast leech_rank.symm c)
          (Fin.cast leech_rank.symm d) :=
      (quadState_eq_quadSt leech leech_even leech_posDef _ _).symm
    have h1 := h _ _ _ hu
    obtain ⟨-, h2⟩ := VnatVOA_smul_quad_one_snd _ _ _ hu t
    rw [h1] at h2
    have hcc : ∀ x : Fin 24, cc (Fin.cast leech_rank.symm x) = x := fun x => Fin.ext rfl
    rw [hcc, hcc] at h2
    simp only [Fin.cast_inj, Prod.smul_snd, Submodule.coe_smul] at h2
    exact h2.symm
  have h0 := leech_twisted_outer_eigen_eq_zero
    (fun c => β' (Fin.cast leech_rank.symm c)) (t : Tw) hT
  exact (Submodule.coe_eq_zero).mp h0

end Leech

end VOA.Moonshine.AutZeroTw
