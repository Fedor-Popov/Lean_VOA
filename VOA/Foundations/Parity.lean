/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Parity and the Koszul sign  (Axis B of the super generalization)

The `ℤ/2` grading `𝒱 = 𝒱₀̄ ⊕ 𝒱₁̄` of a super vertex algebra, and the sign character it
feeds into locality and skew-symmetry.

This file is deliberately **independent of the weight grading**.  Half-integer moding
(Axis A) and parity (Axis B) are separate generalizations: symplectic bosons `βγ` are
Axis A without Axis B, the `bc` ghost system is Axis B without Axis A.  No spin–statistics
relation between the two is assumed anywhere; where a theorem genuinely needs it, it is
carried as the explicit predicate `SpinStatistics` rather than built into a structure.

## Main definitions

* `parSign` — the sign character `(-1)^p` of `ZMod 2`, valued in `ℂ`.
* `koszul p q` — the Koszul sign `(-1)^{pq}`; this is the `ε` that
  `VOA.bracketDistε` and `VOA.Localε` take as a parameter.
* `ParityGrading` — an internal `ZMod 2` decomposition of the state space.

## Main results

* `parSign_add` — `parSign` is a character: `(-1)^{p+q} = (-1)^p (-1)^q`.
* `koszul_add_left` — `ε` is multiplicative in the parity of the left slot.  This is what
  makes the parity of a bracket `⁅a,b⁆` behave as `|a| + |b|`, and hence what makes the
  **super-Jacobi identity** close.
* `koszul_mul_self` — `ε² = 1`, the hypothesis the super-Jacobi identity rests on.

## References
* Kac, *Vertex Algebras for Beginners*, §1.3 and §4.1 (super setting);
  Frenkel–Lepowsky–Meurman, §1.9.
-/

namespace VOA

/-! ## The sign character of `ZMod 2` -/

/-- Every element of `ZMod 2` is `0` or `1`.  Stated once so the sign lemmas below can
case-split without `fin_cases` artifacts. -/
theorem zmod2_cases (p : ZMod 2) : p = 0 ∨ p = 1 := by revert p; decide

/-- The sign character `(-1)^p` of `ZMod 2`, valued in `ℂ`: `parSign 0 = 1`,
`parSign 1 = -1`. -/
def parSign (p : ZMod 2) : ℂ := if p = 0 then 1 else -1

@[simp] theorem parSign_zero : parSign 0 = 1 := rfl

@[simp] theorem parSign_one : parSign 1 = -1 := rfl

/-- `parSign` is a character of `(ZMod 2, +)`: `(-1)^{p+q} = (-1)^p (-1)^q`. -/
theorem parSign_add (p q : ZMod 2) : parSign (p + q) = parSign p * parSign q := by
  rcases zmod2_cases p with hp | hp <;> rcases zmod2_cases q with hq | hq <;>
    subst hp <;> subst hq <;> simp [parSign, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- The sign character is a square root of unity: `((-1)^p)² = 1`. -/
@[simp] theorem parSign_mul_self (p : ZMod 2) : parSign p * parSign p = 1 := by
  rcases zmod2_cases p with hp | hp <;> subst hp <;> norm_num [parSign]

/-- The sign character never vanishes, so it is invertible in `ℂ`. -/
@[simp] theorem parSign_ne_zero (p : ZMod 2) : parSign p ≠ 0 := by
  rcases zmod2_cases p with hp | hp <;> subst hp <;> norm_num [parSign]

/-- The sign character is its own inverse. -/
@[simp] theorem parSign_inv (p : ZMod 2) : (parSign p)⁻¹ = parSign p := by
  rcases zmod2_cases p with hp | hp <;> subst hp <;> norm_num [parSign]

/-! ## The Koszul sign -/

/-- The **Koszul sign** `ε(p,q) = (-1)^{pq}`: `-1` exactly when both arguments are odd.

This is the scalar that `VOA.bracketDistε` and `VOA.Localε` take as
their parameter `ε`; the ordinary bosonic theory is the case where one argument is even,
so that `koszul = 1`. -/
def koszul (p q : ZMod 2) : ℂ := parSign (p * q)

@[simp] theorem koszul_zero_left (q : ZMod 2) : koszul 0 q = 1 := by simp [koszul]

@[simp] theorem koszul_zero_right (p : ZMod 2) : koszul p 0 = 1 := by simp [koszul]

@[simp] theorem koszul_one_one : koszul 1 1 = -1 := rfl

/-- The Koszul sign is symmetric. -/
theorem koszul_comm (p q : ZMod 2) : koszul p q = koszul q p := by
  simp [koszul, mul_comm]

/-- **`ε² = 1`.**  This is the hypothesis on which the super-Jacobi identity — and hence
Dong's lemma in the super setting — rests; see `VOA.jacobi₃ε`. -/
@[simp] theorem koszul_mul_self (p q : ZMod 2) : koszul p q * koszul p q = 1 :=
  parSign_mul_self _

/-- The Koszul sign is invertible. -/
@[simp] theorem koszul_ne_zero (p q : ZMod 2) : koszul p q ≠ 0 := parSign_ne_zero _

/-- The Koszul sign is its own inverse, so the swap law `bracketDistε_swap` reads
`⁅a,b⁆_ε = -ε ⁅b,a⁆_ε` in the super case. -/
@[simp] theorem koszul_inv (p q : ZMod 2) : (koszul p q)⁻¹ = koszul p q := parSign_inv _

/-- **Multiplicativity in the left slot.**  `ε(p + p', q) = ε(p,q) ε(p',q)`.

This is the key algebraic fact behind the super-Jacobi identity: the bracket `⁅a,b⁆` has
parity `|a| + |b|`, so the sign it acquires against a third element `c` factors as the
product of the signs of `a` and `b` against `c`. -/
theorem koszul_add_left (p p' q : ZMod 2) :
    koszul (p + p') q = koszul p q * koszul p' q := by
  simp only [koszul, add_mul]
  exact parSign_add _ _

/-- **Multiplicativity in the right slot**, by symmetry. -/
theorem koszul_add_right (p q q' : ZMod 2) :
    koszul p (q + q') = koszul p q * koszul p q' := by
  simp only [koszul, mul_add]
  exact parSign_add _ _

/-! ## The parity grading of a state space -/

/-- An internal **`ℤ/2` (parity) grading** `𝒱 = 𝒱₀̄ ⊕ 𝒱₁̄` of a `ℂ`-vector space.

Kept as a separate bundle from the weight grading, so that a structure may carry either,
both, or neither.  `SpinStatistics` is the *predicate* relating the two; it is never a
field, because building it in would silently exclude `βγ` (half weights, even parity) and
the `bc` ghosts (integer weights, odd parity). -/
structure ParityGrading (𝒱 : Type*) [AddCommGroup 𝒱] [Module ℂ 𝒱] where
  /-- The two homogeneous components `𝒱₀̄` (even) and `𝒱₁̄` (odd). -/
  parity : ZMod 2 → Submodule ℂ 𝒱
  /-- The parity grading is a genuine internal direct-sum decomposition. -/
  isInternal : DirectSum.IsInternal parity

namespace ParityGrading

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `u` is **parity-homogeneous of parity `p`** when it lies in the `p`-component. -/
def IsHomog (P : ParityGrading 𝒱) (u : 𝒱) (p : ZMod 2) : Prop := u ∈ P.parity p

/-- The **purely even** parity grading: `𝒱₀̄ = 𝒱`, `𝒱₁̄ = 0`.  This exhibits an ordinary
(non-super) vertex algebra as the trivially-graded case, in which every Koszul sign is `1`
and the super theory collapses to the bosonic one. -/
def even (𝒱 : Type*) [AddCommGroup 𝒱] [Module ℂ 𝒱] : ParityGrading 𝒱 where
  parity p := if p = 0 then ⊤ else ⊥
  isInternal := by
    classical
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨fun p => ?_, le_antisymm le_top (le_iSup_of_le 0 (by simp))⟩
    by_cases hp : p = 0
    · subst hp
      have hbot : (⨆ j, ⨆ (_ : j ≠ (0 : ZMod 2)),
          (if j = 0 then (⊤ : Submodule ℂ 𝒱) else ⊥)) = ⊥ :=
        le_antisymm (iSup₂_le fun j hj => by simp [hj]) bot_le
      rw [hbot]
      exact disjoint_bot_right
    · simp [hp]

/-- The even component of the purely even grading is everything. -/
@[simp] theorem even_parity_zero : (even 𝒱).parity 0 = ⊤ := by simp [even]

/-- The odd component of the purely even grading is trivial. -/
theorem even_parity_of_ne {p : ZMod 2} (hp : p ≠ 0) : (even 𝒱).parity p = ⊥ := by
  simp [even, hp]

/-- In the purely even grading, an odd vector is zero. -/
theorem eq_zero_of_mem_even_of_ne {p : ZMod 2} (hp : p ≠ 0) {u : 𝒱}
    (hu : u ∈ (even 𝒱).parity p) : u = 0 := by
  rw [even_parity_of_ne hp] at hu
  simpa using hu

/-- In the purely even grading every vector is even. -/
@[simp] theorem even_isHomog_zero (u : 𝒱) : (even 𝒱).IsHomog u 0 := by
  simp [IsHomog, even]

/-! ### The fermion-number involution `(-1)^F`

The operator acting as `+1` on the even part and `-1` on the odd part.  It is what lets a
parity-*dependent* sign be written as an honest linear operator, which is exactly what the
super skew-symmetry candidate field needs: the Koszul sign `(-1)^{|u||v|}` depends on the
argument `v`, so it cannot be a scalar, but it *is* `(-1)^F` raised to `|u|`. -/

/-- The even and odd parts are complementary submodules. -/
theorem isCompl01 (P : ParityGrading 𝒱) : IsCompl (P.parity 0) (P.parity 1) :=
  P.isInternal.isCompl (by decide) (by ext p; simpa using zmod2_cases p)

/-- Every vector splits as even `+` odd. -/
theorem exists_parity_decomp (P : ParityGrading 𝒱) (u : 𝒱) :
    ∃ u₀ ∈ P.parity 0, ∃ u₁ ∈ P.parity 1, u₀ + u₁ = u := by
  refine Submodule.mem_sup.1 ?_
  rw [P.isCompl01.sup_eq_top]
  trivial

/-- **The fermion-number involution `(-1)^F`**: `+1` on `𝒱₀̄`, `-1` on `𝒱₁̄`. -/
noncomputable def parityInvol (P : ParityGrading 𝒱) : Module.End ℂ 𝒱 :=
  (2 : ℂ) • ((P.parity 0).projection (P.parity 1) P.isCompl01) - LinearMap.id

@[simp] theorem parityInvol_even (P : ParityGrading 𝒱) {u : 𝒱} (hu : u ∈ P.parity 0) :
    P.parityInvol u = u := by
  have h : (P.parity 0).projection (P.parity 1) P.isCompl01 u = u := by
    simpa using Submodule.projection_apply_left (q := P.parity 1) P.isCompl01 ⟨u, hu⟩
  simp only [parityInvol, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, h]
  rw [two_smul]; abel

@[simp] theorem parityInvol_odd (P : ParityGrading 𝒱) {u : 𝒱} (hu : u ∈ P.parity 1) :
    P.parityInvol u = -u := by
  have h : (P.parity 0).projection (P.parity 1) P.isCompl01 u = 0 := by
    rw [Submodule.projection_apply]
    have h0 : (P.parity 0).projectionOnto (P.parity 1) P.isCompl01 u = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff P.isCompl01).2 hu
    rw [h0]; rfl
  simp only [parityInvol, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, h]
  rw [smul_zero, zero_sub]

/-- On a parity-homogeneous vector, `(-1)^F` is multiplication by the sign character. -/
theorem parityInvol_homog (P : ParityGrading 𝒱) {p : ZMod 2} {u : 𝒱} (hu : u ∈ P.parity p) :
    P.parityInvol u = parSign p • u := by
  rcases zmod2_cases p with hp | hp <;> subst hp
  · rw [P.parityInvol_even hu]; simp
  · rw [P.parityInvol_odd hu]; simp

/-- The operator implementing the Koszul sign `(-1)^{p·|·|}` as a function of the *argument's*
parity: the identity when `p` is even, and `(-1)^F` when `p` is odd. -/
noncomputable def koszulOp (P : ParityGrading 𝒱) (p : ZMod 2) : Module.End ℂ 𝒱 :=
  if p = 0 then LinearMap.id else P.parityInvol

/-- **The defining property of `koszulOp`**: on a homogeneous vector it is the Koszul sign. -/
theorem koszulOp_homog (P : ParityGrading 𝒱) (p : ZMod 2) {q : ZMod 2} {u : 𝒱}
    (hu : u ∈ P.parity q) : P.koszulOp p u = koszul p q • u := by
  rcases zmod2_cases p with hp | hp <;> subst hp
  · simp [koszulOp]
  · simp only [koszulOp, one_ne_zero, if_false]
    rw [P.parityInvol_homog hu, koszul, one_mul]

end ParityGrading

end VOA
