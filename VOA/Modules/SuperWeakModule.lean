/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperVertexOperatorAlgebra
import VOA.Modules.LogVModule

/-!
# Modules over a super vertex operator algebra

The module layer for the super development.  `Core/Super*.lean` is **algebra-only**:
`SuperVertexAlgebra`, `SuperVertexOperatorAlgebra`, super Dong/Goddard/skew and the three
examples exist, but nothing in them mentions a module.  Yet the theorems the super axis is for
live in modules — pseudo-*super*traces are functionals on endomorphism algebras of super
modules, van Ekeren's twisted-sector theorem needs twisted super modules, and `Γ_θ` characters
are traces over them.

## Design: parity as a second grading, bosonic as the trivial-parity instance

This mirrors the choice already made one level down.  `SuperVertexAlgebra` carries `parity`
alongside `grading`, and the bosonic case embeds by `VertexOperatorAlgebra.toSuper`.  Modules
follow suit: `SuperWeakModule` carries a parity grading on `M`, and a bosonic `WeakModule`
becomes one with trivial parity (`WeakModule.toSuper`).  A *parallel* hierarchy was rejected for
the same reason as there: every downstream construction — pseudo-traces above all — would have to
be written twice.

## The signs

Exactly one axiom changes shape.  The module Jacobi identity (Gannon 5.3.1b) acquires the Koszul
sign on the term where `Y_M(u)` and `Y_M(v)` are exchanged:

`∑ᶠ i, (-1)^i C(ℓ,i)·( u₍ℓ₊ₘ₋ᵢ₎v₍ₙ₊ᵢ₎x − ε(u,v)·(-1)^ℓ·v₍ℓ₊ₙ₋ᵢ₎u₍ₘ₊ᵢ₎x )`
` = ∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`,

with `ε(u,v) = koszul p q` for `u` of parity `p` and `v` of parity `q`.  At trivial parity
`koszul 0 q = 1` and the identity is the bosonic one on the nose — which is what makes
`WeakModule.toSuper` a matter of rewriting by `koszul_zero_left`, with no new mathematics.

Note the parity axiom `parity_mode`: modes add parities, `u₍ₙ₎x` has parity `|u| + |x|`.  As in
the algebra, this is what makes the Koszul signs compose, and hence what makes the identity
close.

## Status

Definitional layer: the structure, the bosonic embedding, and the parity/mode API.  Graded
(`SuperOrdVModule`) and logarithmic (`SuperLogVModule`) super modules are the natural next step
and are *not* here.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A **weak module over a super vertex algebra**: the bosonic axioms, with a parity grading on
the module and the Koszul sign in the Jacobi identity. -/
structure SuperWeakModule (W : SuperVertexAlgebra 𝒱) (M : Type v)
    [AddCommGroup M] [Module ℂ M] where
  /-- The module state–field correspondence `Y_M(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}`, linear in `u`. -/
  YM : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧
  /-- The parity grading `M = M₀̄ ⊕ M₁̄`. -/
  parity : ZMod 2 → Submodule ℂ M
  /-- The parity grading is a genuine internal direct-sum decomposition. -/
  parity_isInternal : DirectSum.IsInternal parity
  /-- **Modes add parities**: `u₍ₙ₎x` has parity `|u| + |x|`.  This is what makes the Koszul
  signs compose, and hence what makes the super-Jacobi identity close. -/
  parity_mode : ∀ {p q : ZMod 2} (u : 𝒱), u ∈ W.parity p → ∀ (x : M), x ∈ parity q →
    ∀ (n : ℤ), mode (YM u) n x ∈ parity (p + q)
  /-- **5.3.1a.** `Y_M(𝟙, z) = id_M`. -/
  vacuum_YM : YM W.vacuum = 1
  /-- Each `Y_M(u,z)` is a **field**: `u₍ₙ₎x = 0` for `n` large. -/
  truncation : ∀ (u : 𝒱) (x : M), ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YM u) n x = 0
  /-- **5.3.1b — the super module Jacobi identity**: the bosonic identity with the Koszul sign
  `ε(u,v)` on the exchanged term. -/
  jacobi : ∀ {p q : ZMod 2} (u : 𝒱), u ∈ W.parity p → ∀ (v : 𝒱), v ∈ W.parity q →
    ∀ (x : M) (ℓ m n : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (YM u) (ℓ + m - i) (mode (YM v) (n + i) x)
          - (koszul p q * negOnePow ℓ) • mode (YM v) (ℓ + n - i) (mode (YM u) (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • mode (YM (W.smul u (ℓ + i) v)) (m + n - i) x

namespace SuperWeakModule

variable {W : SuperVertexAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The **module action** `u₍ₙ₎ · x`. -/
def act (A : SuperWeakModule W M) (u : 𝒱) (n : ℤ) (x : M) : M := mode (A.YM u) n x

@[simp] theorem act_def (A : SuperWeakModule W M) (u : 𝒱) (n : ℤ) (x : M) :
    A.act u n x = mode (A.YM u) n x := rfl

@[simp] theorem act_vacuum (A : SuperWeakModule W M) (n : ℤ) (x : M) :
    A.act W.vacuum n x = if n = -1 then x else 0 := by
  rw [act_def, A.vacuum_YM, mode_one]
  split_ifs <;> simp

@[simp] theorem act_add_right (A : SuperWeakModule W M) (u : 𝒱) (n : ℤ) (x y : M) :
    A.act u n (x + y) = A.act u n x + A.act u n y :=
  map_add (mode (A.YM u) n) x y

@[simp] theorem act_smul_right (A : SuperWeakModule W M) (u : 𝒱) (c : ℂ) (n : ℤ) (x : M) :
    A.act u n (c • x) = c • A.act u n x :=
  map_smul (mode (A.YM u) n) c x

@[simp] theorem act_add_left (A : SuperWeakModule W M) (u₁ u₂ : 𝒱) (n : ℤ) (x : M) :
    A.act (u₁ + u₂) n x = A.act u₁ n x + A.act u₂ n x := by
  simp only [act_def, map_add, mode_add, LinearMap.add_apply]

@[simp] theorem act_zero_right (A : SuperWeakModule W M) (u : 𝒱) (n : ℤ) :
    A.act u n (0 : M) = 0 := map_zero (mode (A.YM u) n)

/-- Modes preserve the parity decomposition, in `act` form. -/
theorem act_parity (A : SuperWeakModule W M) {p q : ZMod 2} {u : 𝒱} (hu : u ∈ W.parity p)
    {x : M} (hx : x ∈ A.parity q) (n : ℤ) : A.act u n x ∈ A.parity (p + q) :=
  A.parity_mode u hu x hx n

end SuperWeakModule

/-! ## The bosonic case is the trivial-parity instance

Reusing `ParityGrading.even` — the all-even grading Fedor already built for the algebra side —
rather than duplicating it here. -/

section Bosonic

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

theorem even_parity_one : (ParityGrading.even M).parity 1 = ⊥ := by
  simp [ParityGrading.even]

theorem mem_even_parity_zero (x : M) : x ∈ (ParityGrading.even M).parity 0 := by
  simp [ParityGrading.even]

/-- **A bosonic weak module is a super weak module with trivial parity.**  The Jacobi identity
transports verbatim: at trivial parity `koszul 0 q = 1`, so the exchanged term loses its sign
and the super identity *is* the bosonic one — no new mathematics, only a rewrite. -/
noncomputable def WeakModule.toSuper (A : WeakModule W M) :
    SuperWeakModule W.toSuper.toSuperVertexAlgebra M where
  YM := A.YM
  parity := (ParityGrading.even M).parity
  parity_isInternal := (ParityGrading.even M).isInternal
  parity_mode := by
    intro p q u hu x hx n
    rcases zmod2_cases q with rfl | rfl
    · rcases zmod2_cases p with rfl | rfl
      · exact mem_even_parity_zero (mode (A.YM u) n x)
      · have hu0 : u = 0 := by
          have : u ∈ (⊥ : Submodule ℂ 𝒱) := by
            simpa [VertexOperatorAlgebra.toSuper, PreVertexAlgebra.toSuper,
              ParityGrading.even] using hu
          simpa using this
        subst hu0
        have hzM : ∀ k : ℤ, ((0 : FormalDist (Module.End ℂ M)) k) = 0 := fun _ => rfl
        simp only [map_zero, mode, hzM, LinearMap.zero_apply]
        exact Submodule.zero_mem _
    · have hx0 : x = 0 := by
        have : x ∈ (⊥ : Submodule ℂ M) := by rw [← even_parity_one]; exact hx
        simpa using this
      subst hx0
      simp only [map_zero]
      exact Submodule.zero_mem _
  vacuum_YM := A.vacuum_YM
  truncation := A.truncation
  jacobi := by
    intro p q u hu v hv x ℓ m n
    rcases zmod2_cases p with rfl | rfl
    · simpa using A.jacobi u v x ℓ m n
    · have hu0 : u = 0 := by
        have : u ∈ (⊥ : Submodule ℂ 𝒱) := by
          simpa [VertexOperatorAlgebra.toSuper, PreVertexAlgebra.toSuper,
            ParityGrading.even] using hu
        simpa using this
      subst hu0
      have hzM : ∀ k : ℤ, ((0 : FormalDist (Module.End ℂ M)) k) = 0 := fun _ => rfl
      have hzV : ∀ k : ℤ, ((0 : FormalDist (Module.End ℂ 𝒱)) k) = 0 := fun _ => rfl
      simp [SuperVertexAlgebra.smul, mode, hzM, hzV]

end Bosonic

end VOA
