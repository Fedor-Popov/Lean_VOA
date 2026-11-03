/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteDifferential

/-!
# The commutant of an affine sl2 action

The coset consists of states annihilated by every nonnegative current mode.
Translation covariance proves closure under every vertex product. No conformal
vector, simplicity, level restriction, or unitarity hypothesis enters this result.
In particular this is the state-space vertex subalgebra needed for the BRST map.

OPEN: identifying the actual difference of Sugawara vectors as a coset conformal
vector requires the corresponding conformal structures and their current products.
The affine-action input alone does not specify those conformal vectors.
-/

namespace VOA.Sl2Coset

open Module (End)
open Sl2SemiInfinite

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The simultaneous kernel of the nonnegative affine current modes. -/
def cosetSubspace (A : AffineSl2Action V k) : Submodule ℂ M where
  carrier := {x | ∀ (a : Fin 3) (n : ℤ), 0 ≤ n → mode (V.Y (A.current a)) n x = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro a n hn
    rw [map_add, hx a n hn, hy a n hn, add_zero]
  smul_mem' c x hx := by
    intro a n hn
    rw [map_smul, hx a n hn, smul_zero]

@[simp] theorem mem_cosetSubspace (A : AffineSl2Action V k) (x : M) :
    x ∈ cosetSubspace A ↔
      ∀ (a : Fin 3) (n : ℤ), 0 ≤ n → mode (V.Y (A.current a)) n x = 0 :=
  Iff.rfl

/-- The vacuum is a coset state at every level. -/
theorem vacuum_mem_cosetSubspace (A : AffineSl2Action V k) :
    V.vacuum ∈ cosetSubspace A :=
  fun a n hn => (V.creation (A.current a)).2 n hn

/-- Every current mode commutes with the parity involution, because the current
state is even. This does not require translation covariance. -/
theorem current_mode_parityInvol (A : AffineSl2Action V k) (a : Fin 3)
    (n : ℤ) (x : M) :
    mode (V.Y (A.current a)) n ((TensorVA.parGr V).parityInvol x) =
      (TensorVA.parGr V).parityInvol (mode (V.Y (A.current a)) n x) := by
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := (TensorVA.parGr V).exists_parity_decomp x
  have h₀ : mode (V.Y (A.current a)) n x₀ ∈ V.parity 0 := by
    simpa using V.parity_mode (A.current a) (A.current_even a) x₀ hx₀ n
  have h₁ : mode (V.Y (A.current a)) n x₁ ∈ V.parity 1 := by
    simpa using V.parity_mode (A.current a) (A.current_even a) x₁ hx₁ n
  simp only [map_add, (TensorVA.parGr V).parityInvol_even hx₀,
    (TensorVA.parGr V).parityInvol_odd hx₁, map_neg,
    (TensorVA.parGr V).parityInvol_even h₀,
    (TensorVA.parGr V).parityInvol_odd h₁]

/-- The coset is stable under the parity involution. -/
theorem parityInvol_mem_cosetSubspace (A : AffineSl2Action V k) {x : M}
    (hx : x ∈ cosetSubspace A) :
    (TensorVA.parGr V).parityInvol x ∈ cosetSubspace A := by
  intro a n hn
  rw [current_mode_parityInvol, hx a n hn, map_zero]

/-- Splitting a coset state into its even and odd parts stays inside the coset. -/
theorem exists_parity_decomp_coset (A : AffineSl2Action V k) {x : M}
    (hx : x ∈ cosetSubspace A) :
    ∃ x₀ ∈ cosetSubspace A, x₀ ∈ V.parity 0 ∧
      ∃ x₁ ∈ cosetSubspace A, x₁ ∈ V.parity 1 ∧ x₀ + x₁ = x := by
  obtain ⟨x₀, hx₀, x₁, hx₁, heq⟩ := (TensorVA.parGr V).exists_parity_decomp x
  have hparts : ∀ a n, 0 ≤ n →
      mode (V.Y (A.current a)) n x₀ = 0 ∧
        mode (V.Y (A.current a)) n x₁ = 0 := by
    intro a n hn
    have hsum : mode (V.Y (A.current a)) n x₀ +
        mode (V.Y (A.current a)) n x₁ = 0 := by
      rw [← map_add, heq, hx a n hn]
    have h₀ : mode (V.Y (A.current a)) n x₀ ∈ V.parity 0 := by
      simpa using V.parity_mode (A.current a) (A.current_even a) x₀ hx₀ n
    have h₁ : mode (V.Y (A.current a)) n x₁ ∈ V.parity 1 := by
      simpa using V.parity_mode (A.current a) (A.current_even a) x₁ hx₁ n
    have hz : mode (V.Y (A.current a)) n x₀ = 0 := by
      apply Submodule.disjoint_def.mp (TensorVA.parGr V).isCompl01.disjoint _ h₀
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact (V.parity 1).neg_mem h₁
    exact ⟨hz, by simpa only [hz, zero_add] using hsum⟩
  exact ⟨x₀, fun a n hn => (hparts a n hn).1, hx₀,
    x₁, fun a n hn => (hparts a n hn).2, hx₁, heq⟩

/-- A coset field commutes with all integer modes of every affine current. -/
theorem current_mode_coset_mode_commute (A : AffineSl2Action V k)
    (H : TranslationCovariant V) {x : M} (hx : x ∈ cosetSubspace A)
    (a : Fin 3) (m n : ℤ) :
    mode (V.Y (A.current a)) m * mode (V.Y x) n =
      mode (V.Y x) n * mode (V.Y (A.current a)) m := by
  have hom : ∀ {p : ZMod 2} {w : M}, w ∈ cosetSubspace A → w ∈ V.parity p →
      mode (V.Y (A.current a)) m * mode (V.Y w) n =
        mode (V.Y w) n * mode (V.Y (A.current a)) m := by
    intro p w hw hp
    have hc := H.mode_commutator_bound (A.current_even a) hp 0
      (fun j _ => hw a j (Int.natCast_nonneg j)) m n
    simpa only [koszul_zero_left, one_smul, Finset.range_zero,
      Finset.sum_empty, sub_eq_zero] using hc
  obtain ⟨x₀, hx₀, hp₀, x₁, hx₁, hp₁, rfl⟩ := exists_parity_decomp_coset A hx
  simp only [map_add, mode_add, mul_add, add_mul]
  rw [hom hx₀ hp₀, hom hx₁ hp₁]

/-- The commutant is closed under every vertex mode. -/
theorem mode_mem_cosetSubspace (A : AffineSl2Action V k)
    (H : TranslationCovariant V) {x y : M}
    (hx : x ∈ cosetSubspace A) (hy : y ∈ cosetSubspace A) (n : ℤ) :
    mode (V.Y x) n y ∈ cosetSubspace A := by
  intro a m hm
  have hc := congrArg (fun f : End ℂ M => f y)
    (current_mode_coset_mode_commute A H hx a m n)
  simpa only [Module.End.mul_apply, hy a m hm, map_zero] using hc

/-- In particular the intrinsic translation of a coset state stays in the coset. -/
theorem translation_mem_cosetSubspace (A : AffineSl2Action V k)
    (H : TranslationCovariant V) {x : M} (hx : x ∈ cosetSubspace A) :
    V.T x ∈ cosetSubspace A :=
  mode_mem_cosetSubspace A H hx (vacuum_mem_cosetSubspace A) (-2)

/-- The vacuum of the closed coset state space. -/
def cosetVacuum (A : AffineSl2Action V k) : cosetSubspace A :=
  ⟨V.vacuum, vacuum_mem_cosetSubspace A⟩

/-- The actual restricted vertex products of the coset. -/
def cosetMode (A : AffineSl2Action V k) (H : TranslationCovariant V)
    (x : cosetSubspace A) (n : ℤ) : End ℂ (cosetSubspace A) :=
  (mode (V.Y x) n).restrict (fun _ hy => mode_mem_cosetSubspace A H x.property hy n)

@[simp] theorem cosetMode_coe (A : AffineSl2Action V k) (H : TranslationCovariant V)
    (x y : cosetSubspace A) (n : ℤ) :
    ((cosetMode A H x n y : cosetSubspace A) : M) = mode (V.Y x) n y := rfl

end VOA.Sl2Coset
