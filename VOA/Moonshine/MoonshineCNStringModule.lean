/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Abstract string modules

The data of an abstract string module (`Notes/moonshine/MOON_NOGHOST.md`). This module depends only
on Mathlib. Neither a vertex algebra nor a light-cone decomposition is assumed
as part of `StringModule`; the latter is a separate, explicit hypothesis.
The value of `K 0` is immaterial: mixed commutators exclude it.
-/

namespace VOA.Moonshine.ConwayNorton

universe u

/-- A bounded-below, finite-type graded Virasoro module with commuting
longitudinal operators and a weightwise nondegenerate contravariant form. -/
structure StringModule (H : Type u) [AddCommGroup H] [Module ℂ H] where
  wt : ℤ → Submodule ℂ H
  wt_isInternal : DirectSum.IsInternal wt
  wt_finite : ∀ N, FiniteDimensional ℂ (wt N)
  wt_bdd : ∃ N₀, ∀ N < N₀, wt N = ⊥
  c : ℂ
  L : ℤ → Module.End ℂ H
  K : ℤ → Module.End ℂ H
  L_wt : ∀ n N x, x ∈ wt N → L n x ∈ wt (N - n)
  K_wt : ∀ n N x, n ≠ 0 → x ∈ wt N → K n x ∈ wt (N - n)
  L_zero : ∀ N x, x ∈ wt N → L 0 x = (N : ℂ) • x
  L_comm : ∀ m n, L m * L n - L n * L m =
    ((m : ℂ) - n) • L (m + n) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * c) • 1 else 0
  K_comm : ∀ m n, K m * K n = K n * K m
  LK_comm : ∀ m n, n ≠ 0 → m + n ≠ 0 →
    L m * K n - K n * L m = (-(n : ℂ)) • K (m + n)
  B : LinearMap.BilinForm ℂ H
  B_symm : B.IsSymm
  B_orth : ∀ N M x y, N ≠ M → x ∈ wt N → y ∈ wt M → B x y = 0
  B_nondeg : ∀ N x, x ∈ wt N → (∀ y ∈ wt N, B x y = 0) → x = 0
  L_adj : ∀ n x y, B (L n x) y = B x (L (-n) y)
  K_adj : ∀ n x y, B (K n x) y = B x (K (-n) y)

namespace StringModule

variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

/-- The span of all negative Virasoro images. -/
def spurious : Submodule ℂ H := ⨆ n : ℕ, LinearMap.range (M.L (-(n + 1 : ℤ)))

/-- The span of all negative longitudinal images. -/
def kSpurious : Submodule ℂ H := ⨆ n : ℕ, LinearMap.range (M.K (-(n + 1 : ℤ)))

/-- The common kernel of the strictly positive Virasoro modes. -/
def physical : Submodule ℂ H := ⨅ n : ℕ, LinearMap.ker (M.L (n + 1 : ℤ))

/-- The common kernel of the strictly positive longitudinal modes. -/
def kVacuum : Submodule ℂ H := ⨅ n : ℕ, LinearMap.ker (M.K (n + 1 : ℤ))

/-- Vectors annihilated by both families of positive modes. -/
def transverse : Submodule ℂ H := M.physical ⊓ M.kVacuum

/-- The light-cone splitting `H = S ⊕ K`; the concrete sector must establish this
decomposition. -/
def LightConeSplit : Prop := IsCompl M.spurious M.kVacuum

/-- A subspace viewed inside one finite-dimensional weight space. -/
def weightSlice (U : Submodule ℂ H) (N : ℤ) : Submodule ℂ (M.wt N) :=
  U.comap (M.wt N).subtype

/-- Restriction of the form to one weight space. -/
def stringWeightForm (N : ℤ) : LinearMap.BilinForm ℂ (M.wt N) :=
  M.B.restrict (M.wt N)

theorem mem_physical_iff (x : H) :
    x ∈ M.physical ↔ ∀ n : ℕ, M.L (n + 1 : ℤ) x = 0 := by
  simp [physical, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mem_kVacuum_iff (x : H) :
    x ∈ M.kVacuum ↔ ∀ n : ℕ, M.K (n + 1 : ℤ) x = 0 := by
  simp [kVacuum, Submodule.mem_iInf, LinearMap.mem_ker]

theorem negative_L_mem_spurious (n : ℕ) (x : H) :
    M.L (-(n + 1 : ℤ)) x ∈ M.spurious :=
  (le_iSup (fun k : ℕ => LinearMap.range (M.L (-(k + 1 : ℤ)))) n) ⟨x, rfl⟩

theorem negative_K_mem_kSpurious (n : ℕ) (x : H) :
    M.K (-(n + 1 : ℤ)) x ∈ M.kSpurious :=
  (le_iSup (fun k : ℕ => LinearMap.range (M.K (-(k + 1 : ℤ)))) n) ⟨x, rfl⟩

theorem L_comm_apply (m n : ℤ) (x : H) :
    M.L m (M.L n x) - M.L n (M.L m x) =
      ((m : ℂ) - n) • M.L (m + n) x +
        (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * M.c) • x else 0) := by
  have h := LinearMap.congr_fun (M.L_comm m n) x
  split_ifs at h ⊢ <;> simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, Module.End.one_apply,
    ite_apply] using h

theorem K_comm_apply (m n : ℤ) (x : H) :
    M.K m (M.K n x) = M.K n (M.K m x) :=
  LinearMap.congr_fun (M.K_comm m n) x

theorem LK_comm_apply (m n : ℤ) (hn : n ≠ 0) (hmn : m + n ≠ 0) (x : H) :
    M.L m (M.K n x) - M.K n (M.L m x) = (-(n : ℂ)) • M.K (m + n) x :=
  LinearMap.congr_fun (M.LK_comm m n hn hmn) x

theorem stringWeightForm_symm (N : ℤ) : (M.stringWeightForm N).IsSymm := by
  constructor
  intro x y
  exact M.B_symm.eq x y

theorem stringWeightForm_nondegenerate (N : ℤ) :
    (M.stringWeightForm N).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact M.B_nondeg N x x.property fun y hy => hx ⟨y, hy⟩
  · intro x hx
    apply Subtype.ext
    apply M.B_nondeg N x x.property
    intro y hy
    rw [M.B_symm.eq]
    exact hx ⟨y, hy⟩

end StringModule

/-- Optional symmetries of an abstract string module: a group acting by weight-preserving
isometries that commute with the Virasoro and `K` operators. -/
structure StringGroupAction {H : Type u} [AddCommGroup H] [Module ℂ H]
    (M : StringModule H) (G : Type*) [Group G] where
  action : G →* (H ≃ₗ[ℂ] H)
  preserves_wt : ∀ g N x, x ∈ M.wt N → action g x ∈ M.wt N
  commutes_L : ∀ g n x, action g (M.L n x) = M.L n (action g x)
  commutes_K : ∀ g n x, action g (M.K n x) = M.K n (action g x)
  isometry : ∀ g x y, M.B (action g x) (action g y) = M.B x y

end VOA.Moonshine.ConwayNorton
