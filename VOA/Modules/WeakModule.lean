/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.BorcherdsIdentity
import VOA.Core.Borcherds

/-!
# Modules over a VOA — Definition 5.3.1  (Gannon p. 330)

"The raison d'être of VOAs are their modules." A module is a space on which `𝒱` acts,
preserving all the structure.

## Definition 5.3.1 (Gannon, after [199])

Let `𝒱` be a VOA. A **weak `𝒱`-module** `(M, Y_M)` is a vector space `M` with a linear
map `Y_M : 𝒱 → (End M)⟦z^±⟧`, `Y_M(u, z) = ∑_n u₍ₙ₎ z^{-n-1}`, such that:

* `Y_M(1, z) = id_M` (eq. 5.3.1a);
* each `Y_M(u,z)` is a **field** (lower truncation: `u₍ₙ₎x = 0` for `n ≫ 0`);
* the **Jacobi identity** holds (eq. 5.3.1b) — stated here directly in its mode form, the
  module mirror of the proved `𝒱`-level master identity
  `VertexOperatorAlgebra.jacobi` (5.1.7b). For modules the Jacobi identity is *strictly
  stronger* than locality, unlike for `𝒱` itself (Gannon's footnote, after [376]); so we
  posit it directly rather than deriving it from locality.

A weak module is a **(`ℂ`-graded) `𝒱`-module** if additionally `M = ⊕_{α∈ℂ} M_α` with
`M_α = {x : L₀ x = α x}` (eq. 5.3.1c), bounded below (`Re α` bounded below on nonzero
pieces) and each `M_α` finite-dimensional. `α` is the **conformal weight** of `x ∈ M_α`.

`𝒱` itself is the **adjoint module** `adjointModule W`: its `Y_M` is `Y`, and its Jacobi
identity is *exactly* the proved `𝒱`-level identity (`W.jacobi`, definitionally — the module
modes `u₍ₙ₎` are the `𝒱`-products `W.smul u n`). The homomorphism, submodule, irreducible
and completely-reducible notions are defined as expected.

## Implementation

The graded module structure is named **`OrdVModule`** (a `𝒱`-module), *not* `Module`: the
latter would shadow Mathlib's `Module` typeclass and break every `[Module ℂ M]` binder in
the namespace. We keep the action as the bundled field `Y_M : 𝒱 →ₗ[ℂ] (End M)⟦z^±⟧` (rather
than an unbundled family of modes) precisely so the adjoint module reuses `W.jacobi`
definitionally. The complex grading `weight : ℂ → Submodule ℂ M` is built for the adjoint
from the `𝒱`-grading by the injection `ℤ ↪ ℂ` (`adjWeight`), with the off-integer pieces
`⊥`; the internal-direct-sum reindex is `iSupIndep_extend`.

The external direct sum of two modules is represented downstream through
`IsCompletelyReducible` (every submodule is complemented) — the direct-sum decomposition
that Zhu's theorem and rationality actually consume.

## Dependencies
* `VOA.Core.VertexOperatorAlgebra`, `VOA.Core.BorcherdsIdentity`,
  `VOA.Core.Borcherds` (the master Jacobi identity `W.jacobi`).

## Status
`sorry`-free, with no project axioms. The weak module
(5.3.1a–b + field truncation), the `ℂ`-graded `OrdVModule` (5.3.1c, bounded-below,
finite-dimensional), the homomorphism / submodule / irreducible / completely-reducible API,
and the **adjoint module** `adjointModule W : OrdVModule W 𝒱` (both as a weak and as a graded
module, its Jacobi the proved `𝒱`-level identity) are all built and axiom-clean
(`#print axioms adjointModule` = `[propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.3.1; Frenkel–Huang–Lepowsky [199]; Lepowsky–Li Ch. 4–5.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Weak `𝒱`-modules (Definition 5.3.1a–b) -/

/-- A **weak `𝒱`-module** (Gannon Def. 5.3.1, after [199]): a `ℂ`-vector space `M` with a
state–field correspondence `Y_M : 𝒱 → (End M)⟦z^±⟧` such that `Y_M(𝟙,z) = id` (5.3.1a),
each `Y_M(u,z)` is a field (lower truncation), and the **Jacobi identity** (5.3.1b) holds in
the mode form mirroring `VertexOperatorAlgebra.jacobi`. Note the right-hand side feeds the
*`𝒱`-product* `u₍ℓ₊ᵢ₎v = W.smul u (ℓ+i) v` into the module action. -/
structure WeakModule (W : VertexOperatorAlgebra 𝒱) (M : Type v)
    [AddCommGroup M] [Module ℂ M] where
  /-- The module state–field correspondence `Y_M(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}`, linear in `u`. -/
  YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧
  /-- **5.3.1a.** `Y_M(𝟙, z) = id_M`. -/
  vacuum_YM : YM W.vacuum = 1
  /-- Each `Y_M(u,z)` is a **field**: `u₍ₙ₎ x = 0` for `n` large (lower truncation). -/
  truncation : ∀ (u : 𝒱) (x : M), ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YM u) n x = 0
  /-- **5.3.1b — the module Jacobi identity**, in mode form (the module mirror of the
  proved master identity `VertexOperatorAlgebra.jacobi`):
  `∑ᶠ i, (-1)ⁱ C(ℓ,i)·(u₍ℓ₊ₘ₋ᵢ₎ v₍ₙ₊ᵢ₎ x − (-1)^ℓ v₍ℓ₊ₙ₋ᵢ₎ u₍ₘ₊ᵢ₎ x)`
  ` = ∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎ x`. -/
  jacobi : ∀ (u v : 𝒱) (x : M) (ℓ m n : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (YM u) (ℓ + m - i) (mode (YM v) (n + i) x)
          - negOnePow ℓ • mode (YM v) (ℓ + n - i) (mode (YM u) (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • mode (YM (W.smul u (ℓ + i) v)) (m + n - i) x

namespace WeakModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The **module action** `u₍ₙ₎ · x := mode (Y_M u) n x` — Gannon's `u₍ₙ₎ x` on `M`. -/
def act (A : WeakModule W M) (u : 𝒱) (n : ℤ) (x : M) : M := mode (A.YM u) n x

@[simp] theorem act_def (A : WeakModule W M) (u : 𝒱) (n : ℤ) (x : M) :
    A.act u n x = mode (A.YM u) n x := rfl

/-- **5.3.1a** in the `act` API: `𝟙₍ₙ₎ x = δ_{n,-1} x`. -/
@[simp] theorem act_vacuum (A : WeakModule W M) (n : ℤ) (x : M) :
    A.act W.vacuum n x = if n = -1 then x else 0 := by
  rw [act_def, A.vacuum_YM, mode_one]
  split_ifs <;> simp

@[simp] theorem act_add_right (A : WeakModule W M) (u : 𝒱) (n : ℤ) (x y : M) :
    A.act u n (x + y) = A.act u n x + A.act u n y :=
  map_add (mode (A.YM u) n) x y

@[simp] theorem act_smul_right (A : WeakModule W M) (u : 𝒱) (c : ℂ) (n : ℤ) (x : M) :
    A.act u n (c • x) = c • A.act u n x :=
  map_smul (mode (A.YM u) n) c x

@[simp] theorem act_add_left (A : WeakModule W M) (u₁ u₂ : 𝒱) (n : ℤ) (x : M) :
    A.act (u₁ + u₂) n x = A.act u₁ n x + A.act u₂ n x := by
  simp only [act_def, map_add, mode_add, LinearMap.add_apply]

@[simp] theorem act_zero_right (A : WeakModule W M) (u : 𝒱) (n : ℤ) :
    A.act u n (0 : M) = 0 := map_zero (mode (A.YM u) n)

/-! ## Homomorphisms and submodules -/

/-- A **homomorphism of weak modules**: a linear map intertwining every mode action. -/
structure Hom (A : WeakModule W M) {N : Type w} [AddCommGroup N] [Module ℂ N]
    (B : WeakModule W N) where
  /-- The underlying `ℂ`-linear map. -/
  toLinearMap : M →ₗ[ℂ] N
  /-- Intertwining: `φ(u₍ₙ₎ x) = u₍ₙ₎ φ(x)`. -/
  map_act : ∀ (u : 𝒱) (n : ℤ) (x : M), toLinearMap (A.act u n x) = B.act u n (toLinearMap x)

/-- A **weak submodule**: a `ℂ`-subspace closed under every mode `u₍ₙ₎`. -/
structure Submodule' (A : WeakModule W M) where
  /-- The underlying `ℂ`-subspace. -/
  carrier : Submodule ℂ M
  /-- Closure under the action: `x ∈ carrier ⟹ u₍ₙ₎ x ∈ carrier`. -/
  act_mem : ∀ (u : 𝒱) (n : ℤ) {x : M}, x ∈ carrier → A.act u n x ∈ carrier

end WeakModule

/-! ## `ℂ`-graded modules (Definition 5.3.1c) -/

/-- A **(`ℂ`-graded) `𝒱`-module** (Gannon Def. 5.3.1c): a weak module whose space splits as
an internal direct sum `M = ⊕_{α∈ℂ} M_α` of finite-dimensional `L₀`-eigenspaces
(`M_α = {x | L₀ x = α x}`), bounded below (`Re α ≥ B` on the nonzero pieces). Named `OrdVModule`
to avoid shadowing Mathlib's `Module` typeclass (use dot notation `W.OrdVModule M` or
`OrdVModule W M`). -/
structure OrdVModule (W : VertexOperatorAlgebra 𝒱) (M : Type v)
    [AddCommGroup M] [Module ℂ M] extends WeakModule W M where
  /-- The complex grading `M = ⊕_α M_α`, as a family of `ℂ`-subspaces. -/
  weight : ℂ → Submodule ℂ M
  /-- The grading is a genuine internal direct-sum decomposition. -/
  isInternal : DirectSum.IsInternal weight
  /-- **5.3.1c.** `M_α` is the `L₀`-eigenspace of eigenvalue `α`: `L₀ x = α x` on `M_α`. -/
  L0_weight : ∀ (α : ℂ) (x : M), x ∈ weight α → mode (YM W.conformalVector) 1 x = α • x
  /-- Each homogeneous piece `M_α` is finite-dimensional. -/
  finrank : ∀ α, FiniteDimensional ℂ (weight α)
  /-- Bounded below: `Re α` is bounded below on the nonzero pieces. -/
  boundedBelow : ∃ B : ℝ, ∀ α : ℂ, weight α ≠ ⊥ → B ≤ α.re

namespace OrdVModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The **conformal weight** of a homogeneous vector `x ∈ M_α` is `α` (Gannon Def. 5.3.1c). -/
def IsWeightVector (N : OrdVModule W M) (α : ℂ) (x : M) : Prop := x ∈ N.weight α

/-- On `M_α` the grading operator `L₀` acts as the scalar `α` (the conformal weight). -/
theorem L0_eq_weight (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    mode (N.YM W.conformalVector) 1 x = α • x := N.L0_weight α x hx

/-- **Irreducible module** (Gannon §5.3.1): nonzero, with no submodule other than `0` and
`M`. -/
def IsIrreducible (N : OrdVModule W M) : Prop :=
  Nontrivial M ∧ ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤

/-- **Completely reducible module** (Gannon §5.3.1): every submodule is a direct summand
(complemented). This is the external-direct-sum content `M = ⊕ Mᵢ` of irreducibles that
weak rationality and Zhu's theorem use. -/
def IsCompletelyReducible (N : OrdVModule W M) : Prop :=
  ∀ P : WeakModule.Submodule' N.toWeakModule,
    ∃ Q : WeakModule.Submodule' N.toWeakModule, IsCompl P.carrier Q.carrier

end OrdVModule

/-! ## The adjoint module — `𝒱` as its own first module -/

/-- Extension-by-`⊥` preserves `iSupIndep` along any index map (used to reindex the
`𝒱`-grading `ℤ → ℂ` for the adjoint module). -/
theorem iSupIndep_extend {β : Type*} [CompleteLattice β] {ι κ : Type*}
    (t : ι → β) (s : κ → β) (e : ι → κ)
    (hcover : ∀ k, (∀ i, e i ≠ k) → s k = ⊥)
    (hmatch : ∀ i, s (e i) = t i) (ht : iSupIndep t) : iSupIndep s := by
  intro k
  by_cases hk : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [hmatch i]
    refine (ht i).mono_right ?_
    refine iSup_le (fun k' => iSup_le (fun hk' => ?_))
    by_cases hk'e : ∃ i', e i' = k'
    · obtain ⟨i', rfl⟩ := hk'e
      have hii' : i' ≠ i := fun h => hk' (by rw [h])
      rw [hmatch i']
      exact le_iSup_of_le i' (le_iSup_of_le hii' le_rfl)
    · rw [hcover k' (fun i' h => hk'e ⟨i', h⟩)]; exact bot_le
  · rw [hcover k (not_exists.mp hk)]; exact disjoint_bot_left

/-- The complex weight grading of the adjoint module: the `𝒱`-piece `𝒱ₙ` placed at the
complex weight `α = n`, and `⊥` at non-integer `α`. -/
def adjWeight (W : VertexOperatorAlgebra 𝒱) (α : ℂ) : Submodule ℂ 𝒱 :=
  ⨆ (n : ℤ) (_ : (n : ℂ) = α), W.grading n

theorem adjWeight_cast (W : VertexOperatorAlgebra 𝒱) (m : ℤ) :
    adjWeight W (m : ℂ) = W.grading m := by
  unfold adjWeight
  simp only [Int.cast_inj]
  exact iSup_iSup_eq_left

theorem adjWeight_eq_bot (W : VertexOperatorAlgebra 𝒱) {α : ℂ}
    (hne : ∀ m : ℤ, (m : ℂ) ≠ α) : adjWeight W α = ⊥ :=
  iSup_eq_bot.mpr (fun n => iSup_eq_bot.mpr (fun h => absurd h (hne n)))

/-- The **adjoint weak module**: `𝒱` acting on itself, `Y_M = Y`. Its Jacobi identity is
*definitionally* the proved `𝒱`-level master identity `W.jacobi`, and its field truncation is
`𝒱`-regularity (VA5). -/
def adjointWeakModule (W : VertexOperatorAlgebra 𝒱) : WeakModule W 𝒱 where
  YM := W.Y
  vacuum_YM := W.vacuum_Y
  truncation := fun u x => W.regularity u x
  jacobi := W.jacobi

/-- **The adjoint module** `𝒱` (Gannon §5.3.1): `𝒱` as a `ℂ`-graded `𝒱`-module over itself.
The grading is the `𝒱`-grading reindexed `ℤ ↪ ℂ`; the Jacobi identity is the proved
`𝒱`-level identity. This is "the first module". -/
def adjointModule (W : VertexOperatorAlgebra 𝒱) : OrdVModule W 𝒱 where
  toWeakModule := adjointWeakModule W
  weight := adjWeight W
  isInternal := by
    have hW := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W.grading).mp
      W.isInternal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · refine iSupIndep_extend W.grading (adjWeight W) (fun n => (n : ℂ)) ?_ ?_ hW.1
      · intro α hα; exact adjWeight_eq_bot W (fun m hm => hα m hm)
      · intro n; exact adjWeight_cast W n
    · rw [← hW.2]
      apply le_antisymm
      · refine iSup_le (fun α => ?_)
        unfold adjWeight
        exact iSup_le (fun n => iSup_le (fun _ => le_iSup W.grading n))
      · exact iSup_le (fun n => le_iSup_of_le (n : ℂ) (by rw [adjWeight_cast W n]))
  L0_weight := by
    intro α x hx
    by_cases h : ∃ m : ℤ, (m : ℂ) = α
    · obtain ⟨m, rfl⟩ := h
      rw [adjWeight_cast W m] at hx
      have := W.L_zero_grading x hx
      rw [VertexOperatorAlgebra.L_def] at this
      simpa using this
    · rw [adjWeight_eq_bot W (not_exists.mp h), Submodule.mem_bot] at hx
      rw [hx, map_zero, smul_zero]
  finrank := by
    intro α
    by_cases h : ∃ m : ℤ, (m : ℂ) = α
    · obtain ⟨m, rfl⟩ := h
      rw [adjWeight_cast W m]; exact W.finrank m
    · rw [adjWeight_eq_bot W (not_exists.mp h)]; infer_instance
  boundedBelow := by
    refine ⟨0, ?_⟩
    intro α hα
    by_cases h : ∃ m : ℤ, (m : ℂ) = α
    · obtain ⟨m, rfl⟩ := h
      rw [adjWeight_cast W m] at hα
      have hm : 0 ≤ m := by
        by_contra hc
        exact hα (W.positivity m (not_le.mp hc))
      simp only [Complex.intCast_re]
      exact_mod_cast hm
    · exact absurd (adjWeight_eq_bot W (not_exists.mp h)) hα

/-- The adjoint module's action is the `𝒱`-product: `u₍ₙ₎ · x = u₍ₙ₎ x`. -/
@[simp] theorem adjointModule_act (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) (x : 𝒱) :
    (adjointModule W).toWeakModule.act u n x = W.smul u n x := rfl

end VOA
