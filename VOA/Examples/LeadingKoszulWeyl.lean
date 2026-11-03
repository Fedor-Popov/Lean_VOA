/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Koszul acyclicity for a sequence with a Weyl partner

This file proves Koszul acyclicity in positive degree by an explicit contracting homotopy.
It is the abstract form of the step “the sequence `U_n^a = x_n^a + a_n^a` is regular” in
the explicit leading contraction of the coset BRST–Koszul transfer argument.

## The datum (`WeylDatum`)

A module `P` over a commutative ring, with finitely many (index type `ι`, linearly ordered)
operators `u i` and `D i` such that

* the `u i` commute among themselves, and so do the `D i`;
* `[D i, u j] = δ_{ij}` (canonical commutation relations);
* for every integer `k ≥ 1`, `L + k` is bijective, where `L = Σ_i u i ∘ D i`.

For the translated polynomial sequence `u i = x_i + a_i`, `D i = ∂/∂x_i` on a polynomial
module, `L = Σ (x_i + a_i) ∂_i` is the Euler operator conjugated by the translation
`x ↦ x + a`; that instance is `LeadingKoszulTranslation`.

## The Koszul complex

Chains are functions `Finset ι → P` (the coefficient of the exterior monomial `b_S`); the
`Koszul degree` (antighost number) of `f S` is `S.card`. The differential is
`(kd f) S = Σ_{i ∉ S} ε(i,S) u i (f (insert i S))`, with `ε(i,S) = (-1)^{#{j ∈ S, j < i}}`,
and the homotopy is `(kh f) S = Σ_{j ∈ S} ε(j, S∖j) D j (f (S∖j))`.

## Results

* `kd_kh_add_kh_kd` : `kd ∘ kh + kh ∘ kd = L + (Koszul degree)` pointwise.
* `kd_kd` : `kd ∘ kd = 0`.
* `exists_kd_eq` (**acyclicity in positive degree**): a `kd`-cycle concentrated in degree
  `l + 1` is the boundary of a chain concentrated in degree `l + 2`.
* `range_L_eq` (**the degree-zero boundaries**): `range L = ⨆ i, range (u i)`; so Koszul
  `H₀ = P / Σ u_i P = coker L`.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.LeadingKoszul

open Finset

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type w} [LinearOrder ι]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- The Koszul sign `ε(i,S) = (-1)^{#{j ∈ S, j < i}}`. -/
def ksign (i : ι) (S : Finset ι) : ℤ := (-1) ^ (S.filter (· < i)).card

theorem ksign_mul_self (i : ι) (S : Finset ι) : ksign i S * ksign i S = 1 := by
  unfold ksign; rw [← mul_pow]; simp

theorem ksign_insert (i a : ι) {T : Finset ι} (ha : a ∉ T) :
    ksign i (insert a T) = (if a < i then -1 else 1) * ksign i T := by
  unfold ksign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), pow_succ]
    ring
  · ring

theorem ksign_empty (i : ι) : ksign i (∅ : Finset ι) = 1 := by simp [ksign]

/-- The sign identity behind the cancellation of cross terms. -/
theorem ksign_cross {i j : ι} {S : Finset ι} (hi : i ∉ S) (hj : j ∈ S) :
    ksign i S * ksign j (insert i (S.erase j)) =
      -(ksign j (S.erase j) * ksign i (S.erase j)) := by
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have hS : S = insert j (S.erase j) := (Finset.insert_erase hj).symm
  have h1 : ksign i S = (if j < i then -1 else 1) * ksign i (S.erase j) := by
    conv_lhs => rw [hS]
    exact ksign_insert i j (Finset.notMem_erase j S)
  have h2 : ksign j (insert i (S.erase j)) = (if i < j then -1 else 1) * ksign j (S.erase j) :=
    ksign_insert j i (fun h => hi (Finset.mem_of_mem_erase h))
  rw [h1, h2]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
  · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring

variable [Fintype ι]

/-- **A sequence with a Weyl partner.** See the module docstring. -/
structure WeylDatum (R : Type u) [CommRing R] (ι : Type w) [Fintype ι] [LinearOrder ι]
    (P : Type v) [AddCommGroup P] [Module R P] where
  /-- The sequence (multiplication by `U_i = x_i + a_i`). -/
  u : ι → P →ₗ[R] P
  /-- The partner derivations (`∂/∂x_i`). -/
  D : ι → P →ₗ[R] P
  u_comm : ∀ i j v, u i (u j v) = u j (u i v)
  D_comm : ∀ i j v, D i (D j v) = D j (D i v)
  /-- `[D i, u j] = δ_{ij}`. -/
  D_u : ∀ i j v, D i (u j v) = u j (D i v) + if i = j then v else 0
  /-- `L + (k + 1)` is bijective for every `k : ℕ`, where `L = Σ_i u i ∘ D i`. -/
  bij : ∀ k : ℕ, Function.Bijective
    (∑ i, (u i).comp (D i) + ((k + 1 : ℕ) : R) • (LinearMap.id : P →ₗ[R] P))

namespace WeylDatum

variable (W : WeylDatum R ι P)

/-- The generalized Euler operator `L = Σ_i u i ∘ D i`. -/
def L : P →ₗ[R] P := ∑ i, (W.u i).comp (W.D i)

theorem L_apply (v : P) : W.L v = ∑ i, W.u i (W.D i v) := by
  simp [L, LinearMap.sum_apply]

/-- `L u_i = u_i (L + 1)`. -/
theorem L_u (i : ι) (v : P) : W.L (W.u i v) = W.u i (W.L v) + W.u i v := by
  rw [W.L_apply, W.L_apply, map_sum]
  simp_rw [W.D_u, map_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => W.u_comm j i _
  · simp [apply_ite]

/-- `D_j L = (L + 1) D_j`. -/
theorem D_L (j : ι) (v : P) : W.D j (W.L v) = W.L (W.D j v) + W.D j v := by
  rw [W.L_apply, W.L_apply, map_sum]
  simp_rw [W.D_u, W.D_comm j]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

/-- `L + (k + 1)`. -/
def Lk (k : ℕ) : P →ₗ[R] P := W.L + ((k + 1 : ℕ) : R) • LinearMap.id

theorem Lk_apply (k : ℕ) (v : P) : W.Lk k v = W.L v + ((k + 1 : ℕ) : R) • v := rfl

theorem Lk_bij (k : ℕ) : Function.Bijective (W.Lk k) := W.bij k

theorem L_add_injective (k : ℕ) {v : P} (h : W.L v + ((k + 1 : ℕ) : R) • v = 0) : v = 0 :=
  (W.Lk_bij k).1 (by rw [Lk_apply, h, map_zero])

/-- **The kernel of `L + k` is killed by every `D j`** (for `k = 0` this is the statement
that `ker L` consists of “constants”). -/
theorem D_eq_zero_of (k : ℕ) {v : P} (h : W.L v + (k : R) • v = 0) (j : ι) : W.D j v = 0 := by
  apply W.L_add_injective k
  have := congrArg (W.D j) h
  rw [map_add, map_smul, W.D_L, map_zero] at this
  rw [← this]; push_cast; module

/-! ### The Koszul complex and its homotopy -/

/-- The Koszul differential `(kd f) S = Σ_{i ∉ S} ε(i,S) u i (f (insert i S))`. -/
def kd : (Finset ι → P) →ₗ[R] (Finset ι → P) where
  toFun f S := ∑ i ∈ Sᶜ, ksign i S • W.u i (f (insert i S))
  map_add' f g := by
    funext S; simp [Finset.sum_add_distrib]
  map_smul' c f := by
    funext S; simp [Finset.smul_sum, smul_comm c]

/-- The contracting homotopy `(kh f) S = Σ_{j ∈ S} ε(j,S∖j) D j (f (S∖j))`. -/
def kh : (Finset ι → P) →ₗ[R] (Finset ι → P) where
  toFun f S := ∑ j ∈ S, ksign j (S.erase j) • W.D j (f (S.erase j))
  map_add' f g := by
    funext S; simp [Finset.sum_add_distrib]
  map_smul' c f := by
    funext S; simp [Finset.smul_sum, smul_comm c]

theorem kd_apply (f : Finset ι → P) (S : Finset ι) :
    W.kd f S = ∑ i ∈ Sᶜ, ksign i S • W.u i (f (insert i S)) := rfl

theorem kh_apply (f : Finset ι → P) (S : Finset ι) :
    W.kh f S = ∑ j ∈ S, ksign j (S.erase j) • W.D j (f (S.erase j)) := rfl

theorem zsmul_zsmul_mul (a b : ℤ) (v : P) : a • b • v = (a * b) • v := (mul_smul a b v).symm

/-- **The homotopy formula** `kd kh + kh kd = L + (Koszul degree)`. -/
theorem kd_kh_add_kh_kd (f : Finset ι → P) (S : Finset ι) :
    W.kd (W.kh f) S + W.kh (W.kd f) S = W.L (f S) + (S.card : R) • f S := by
  -- expand `kd (kh f)`
  have hA : ∀ i ∈ Sᶜ, ksign i S • W.u i (W.kh f (insert i S)) =
      W.u i (W.D i (f S)) + ∑ j ∈ S, (ksign i S * ksign j (insert i (S.erase j))) •
        W.u i (W.D j (f (insert i (S.erase j)))) := by
    intro i hi
    have hiS : i ∉ S := Finset.mem_compl.mp hi
    rw [kh_apply, Finset.sum_insert hiS, Finset.erase_insert hiS, map_add, smul_add,
      map_zsmul, zsmul_zsmul_mul, ksign_mul_self, one_smul, map_sum, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hiS (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij, map_zsmul, zsmul_zsmul_mul]
  -- expand `kh (kd f)`
  have hB : ∀ j ∈ S, ksign j (S.erase j) • W.D j (W.kd f (S.erase j)) =
      W.u j (W.D j (f S)) + f S + ∑ i ∈ Sᶜ, (ksign j (S.erase j) * ksign i (S.erase j)) •
        W.u i (W.D j (f (insert i (S.erase j)))) := by
    intro j hj
    rw [kd_apply, Finset.compl_erase, Finset.sum_insert (by simp [hj]),
      Finset.insert_erase hj, map_add, smul_add, map_zsmul, zsmul_zsmul_mul, ksign_mul_self,
      one_smul, W.D_u, if_pos rfl, map_sum, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiS : i ∉ S := Finset.mem_compl.mp hi
    have hij : j ≠ i := fun h => hiS (h ▸ hj)
    rw [map_zsmul, zsmul_zsmul_mul, W.D_u, if_neg hij, add_zero]
  have e1 : W.kd (W.kh f) S = ∑ i ∈ Sᶜ, (W.u i (W.D i (f S)) + ∑ j ∈ S,
      (ksign i S * ksign j (insert i (S.erase j))) •
        W.u i (W.D j (f (insert i (S.erase j))))) := by
    rw [kd_apply]; exact Finset.sum_congr rfl hA
  have e2 : W.kh (W.kd f) S = ∑ j ∈ S, (W.u j (W.D j (f S)) + f S + ∑ i ∈ Sᶜ,
      (ksign j (S.erase j) * ksign i (S.erase j)) •
        W.u i (W.D j (f (insert i (S.erase j))))) := by
    rw [kh_apply]; exact Finset.sum_congr rfl hB
  have hcross : ∑ i ∈ Sᶜ, ∑ j ∈ S, (ksign i S * ksign j (insert i (S.erase j))) •
        W.u i (W.D j (f (insert i (S.erase j)))) +
      ∑ j ∈ S, ∑ i ∈ Sᶜ, (ksign j (S.erase j) * ksign i (S.erase j)) •
        W.u i (W.D j (f (insert i (S.erase j)))) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [ksign_cross (Finset.mem_compl.mp hi) hj, neg_smul, neg_add_cancel]
  rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    W.L_apply]
  rw [← Finset.sum_compl_add_sum S (fun i => W.u i (W.D i (f S)))]
  have hc : ∑ _j ∈ S, f S = (S.card : R) • f S := by
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  rw [← hc]
  linear_combination (norm := abel_nf) hcross

/-- `kd ∘ kd = 0`. -/
theorem kd_kd (f : Finset ι → P) : W.kd (W.kd f) = 0 := by
  funext S
  rw [kd_apply, Pi.zero_apply]
  simp_rw [kd_apply, map_sum, Finset.smul_sum, map_zsmul, smul_smul]
  -- pair the terms `(i, j)` and `(j, i)` with `i, j ∉ S`
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_compl, Finset.mem_insert, not_or] at hx
    obtain ⟨hi, hji, hj⟩ := hx
    simp only
    rw [W.u_comm j i, Finset.insert_comm]
    have s1 : ksign i S * ksign j (insert i S) = -(ksign j S * ksign i (insert j S)) := by
      rw [ksign_insert j i hi, ksign_insert i j hj]
      rcases lt_or_gt_of_ne hji with h | h
      · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
      · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
    rw [s1, neg_smul, neg_add_cancel]
  · rintro ⟨i, j⟩ hx _ h
    simp only [Finset.mem_sigma, Finset.mem_compl, Finset.mem_insert, not_or] at hx
    simp only [Sigma.mk.injEq] at h
    exact hx.2.1 h.1
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_compl, Finset.mem_insert, not_or] at hx ⊢
    exact ⟨hx.2.2, fun h => hx.2.1 h.symm, hx.1⟩
  · rintro ⟨i, j⟩ _; rfl

/-! ### Acyclicity in positive degree -/

/-- `L + (l + 1)` as a linear equivalence. -/
noncomputable def Lequiv (l : ℕ) : P ≃ₗ[R] P := LinearEquiv.ofBijective (W.Lk l) (W.Lk_bij l)

theorem Lequiv_symm (l : ℕ) (v : P) :
    W.L ((W.Lequiv l).symm v) + ((l + 1 : ℕ) : R) • (W.Lequiv l).symm v = v := by
  have := (W.Lequiv l).apply_symm_apply v
  exact this

/-- **Koszul acyclicity in positive degree.** A `kd`-cycle concentrated in Koszul degree
`l + 1` is the boundary of a chain concentrated in Koszul degree `l + 2`. -/
theorem exists_kd_eq (l : ℕ) (f : Finset ι → P) (hf : ∀ S, S.card ≠ l + 1 → f S = 0)
    (hd : W.kd f = 0) : ∃ g, (∀ S, S.card ≠ l + 2 → g S = 0) ∧ W.kd g = f := by
  let F : Finset ι → P := fun S => (W.Lequiv l).symm (f S)
  have hF : ∀ S, W.L (F S) + ((l + 1 : ℕ) : R) • F S = f S := fun S => W.Lequiv_symm l (f S)
  have hkdF : ∀ T, W.L (W.kd F T) + (l : R) • W.kd F T = 0 := by
    intro T
    have hterm : ∀ i ∈ Tᶜ, W.L (ksign i T • W.u i (F (insert i T))) +
        (l : R) • ksign i T • W.u i (F (insert i T)) = ksign i T • W.u i (f (insert i T)) := by
      intro i _
      rw [← hF, map_zsmul, W.L_u, map_add, map_smul, smul_comm (l : R), ← smul_add]
      congr 1
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [kd_apply, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl hterm, ← kd_apply, hd]
    rfl
  refine ⟨W.kh F, ?_, ?_⟩
  · intro S hS
    rw [kh_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : (S.erase j).card ≠ l + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    simp [F, hf _ this]
  · funext S
    have h := W.kd_kh_add_kh_kd F S
    have h0 : W.kh (W.kd F) S = 0 := by
      rw [kh_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [W.D_eq_zero_of l (hkdF _) j, smul_zero]
    rw [h0, add_zero] at h
    rw [h]
    by_cases hS : S.card = l + 1
    · rw [hS]; exact hF S
    · simp [F, hf S hS]

/-! ### Degree zero -/

/-- **The degree-zero Koszul boundaries are the range of `L`**: `Σ_i u_i P = L P`. -/
theorem range_L_eq : LinearMap.range W.L = ⨆ i, LinearMap.range (W.u i) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [W.L_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i ⟨W.D i v, rfl⟩
  · refine iSup_le fun i => ?_
    rintro _ ⟨w, rfl⟩
    refine ⟨W.u i ((W.Lequiv 0).symm w), ?_⟩
    rw [W.L_u, ← map_add]
    congr 1
    have := W.Lequiv_symm 0 w
    simpa using this

/-- The Koszul boundaries in degree zero, as computed by `kd`. -/
theorem kd_empty (g : Finset ι → P) : W.kd g ∅ = ∑ i, W.u i (g {i}) := by
  rw [kd_apply, Finset.compl_empty]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ksign_empty, one_smul]
  rfl

/-! ### Augmentation: identifying Koszul `H₀` -/

/-- **An augmentation of a Weyl datum**: a map `ε : P → Q` with a section `σ` and a
“homotopy” `G` such that `ε ∘ L = 0`, `ε ∘ σ = id` and `L ∘ G + σ ∘ ε = id`. For translated
polynomials, `ε` is evaluation at `x = -a` (`LeadingKoszulTranslation`). -/
structure Augmentation (Q : Type*) [AddCommGroup Q] [Module R Q] where
  ε : P →ₗ[R] Q
  σ : Q →ₗ[R] P
  G : P →ₗ[R] P
  ε_L : ∀ v, ε (W.L v) = 0
  ε_σ : ∀ q, ε (σ q) = q
  split : ∀ v, W.L (G v) + σ (ε v) = v

variable {W}

theorem Augmentation.range_L_eq_ker {Q : Type*} [AddCommGroup Q] [Module R Q]
    (A : W.Augmentation Q) : LinearMap.range W.L = LinearMap.ker A.ε := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩; exact A.ε_L v
  · intro v hv
    refine ⟨A.G v, ?_⟩
    have := A.split v
    rwa [LinearMap.mem_ker.mp hv, map_zero, add_zero] at this

theorem Augmentation.ε_surjective {Q : Type*} [AddCommGroup Q] [Module R Q]
    (A : W.Augmentation Q) : Function.Surjective A.ε := fun q => ⟨A.σ q, A.ε_σ q⟩

/-- **Koszul `H₀` is `Q`.** The degree-zero Koszul homology `P / Σ_i u_i P` is identified
with `Q` by the augmentation. -/
noncomputable def Augmentation.koszulH0Equiv {Q : Type*} [AddCommGroup Q] [Module R Q]
    (A : W.Augmentation Q) : (P ⧸ ⨆ i, LinearMap.range (W.u i)) ≃ₗ[R] Q :=
  (Submodule.quotEquivOfEq _ _ (by rw [← W.range_L_eq, A.range_L_eq_ker])).trans
    (A.ε.quotKerEquivOfSurjective A.ε_surjective)

theorem Augmentation.koszulH0Equiv_mk {Q : Type*} [AddCommGroup Q] [Module R Q]
    (A : W.Augmentation Q) (v : P) :
    A.koszulH0Equiv (Submodule.Quotient.mk v) = A.ε v := rfl

end WeylDatum

end VOA.LeadingKoszul
