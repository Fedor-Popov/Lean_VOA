/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SuperSymmetricFunctionals
import VOA.Modularity.SuperTrace
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The queer Type-II model and its odd trace

This file supplies the concrete Type-II trace model needed by the super Zhu theory.  For a
finite index type `n`, the queer superalgebra `Q(n)` is represented by pairs of square matrices
`(A,B)`, with product

`(A,B) * (C,D) = (A*C + B*D, A*D + B*C)`.

The even part consists of `(A,0)` and the odd part of `(0,B)`.  The odd trace is the functional
`otr(A,B) = trace(B)`.  It satisfies the homogeneous Koszul cyclicity law and therefore defines
a supersymmetric functional on `Q(n)`.  A faithful block realization sends `(A,B)` to the matrix
with diagonal blocks `A` and off-diagonal blocks `B`.

This is a model calculation only.  In particular, this file does **not** classify finite
dimensional simple associative superalgebras or assert that an arbitrary Type-II component has
already been identified with `Q(n)`.

## Status

Proved without `sorry`, `admit`, `native_decide`, or new axioms.
-/

namespace VOA

open Matrix

universe u

/-- The concrete queer algebra `Q(n)` as a pair of `n`-by-`n` complex matrices. -/
@[ext]
structure Queer (n : Type u) where
  /-- The coefficient of the even block generator. -/
  evenPart : Matrix n n ℂ
  /-- The coefficient of the odd block generator. -/
  oddPart : Matrix n n ℂ

namespace Queer

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The evident equivalence with a product transports only the additive and scalar structures;
the queer multiplication and unit are defined separately below. -/
def equivProd : Queer n ≃ Matrix n n ℂ × Matrix n n ℂ where
  toFun x := (x.evenPart, x.oddPart)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (Queer n) := equivProd.addCommGroup

instance instModule : Module ℂ (Queer n) := equivProd.module ℂ

@[simp] theorem evenPart_zero : (0 : Queer n).evenPart = 0 := rfl

@[simp] theorem oddPart_zero : (0 : Queer n).oddPart = 0 := rfl

@[simp] theorem evenPart_add (x y : Queer n) : (x + y).evenPart = x.evenPart + y.evenPart := rfl

@[simp] theorem oddPart_add (x y : Queer n) : (x + y).oddPart = x.oddPart + y.oddPart := rfl

@[simp] theorem evenPart_neg (x : Queer n) : (-x).evenPart = -x.evenPart := rfl

@[simp] theorem oddPart_neg (x : Queer n) : (-x).oddPart = -x.oddPart := rfl

@[simp] theorem evenPart_smul (c : ℂ) (x : Queer n) : (c • x).evenPart = c • x.evenPart := rfl

@[simp] theorem oddPart_smul (c : ℂ) (x : Queer n) : (c • x).oddPart = c • x.oddPart := rfl

/-- Multiplication in `Q(n)`. -/
instance : Mul (Queer n) where
  mul x y := ⟨x.evenPart * y.evenPart + x.oddPart * y.oddPart,
    x.evenPart * y.oddPart + x.oddPart * y.evenPart⟩

/-- The unit of `Q(n)`. -/
instance : One (Queer n) where
  one := ⟨1, 0⟩

@[simp] theorem evenPart_mul (x y : Queer n) :
    (x * y).evenPart = x.evenPart * y.evenPart + x.oddPart * y.oddPart := rfl

@[simp] theorem oddPart_mul (x y : Queer n) :
    (x * y).oddPart = x.evenPart * y.oddPart + x.oddPart * y.evenPart := rfl

@[simp] theorem evenPart_one : (1 : Queer n).evenPart = 1 := rfl

@[simp] theorem oddPart_one : (1 : Queer n).oddPart = 0 := rfl

/-- The distributive (not yet associativity-carrying) ring structure underlying `Q(n)`. -/
instance instNonAssocRing : NonAssocRing (Queer n) where
  __ := (inferInstance : AddCommGroup (Queer n))
  mul x y := x * y
  one := 1
  one_mul x := by apply Queer.ext <;> simp
  mul_one x := by apply Queer.ext <;> simp
  zero_mul x := by apply Queer.ext <;> simp
  mul_zero x := by apply Queer.ext <;> simp
  left_distrib x y z := by
    apply Queer.ext <;> simp [mul_add] <;> abel
  right_distrib x y z := by
    apply Queer.ext <;> simp [add_mul] <;> abel

/-- The nonnegative part of the queer ring structure. -/
instance instSemiring : Semiring (Queer n) where
  toAddCommMonoid := inferInstance
  mul x y := x * y
  one := 1
  mul_assoc x y z := by
    apply Queer.ext <;> simp only [evenPart_mul, oddPart_mul] <;> noncomm_ring
  one_mul x := by apply Queer.ext <;> simp
  mul_one x := by apply Queer.ext <;> simp
  zero_mul x := by apply Queer.ext <;> simp
  mul_zero x := by apply Queer.ext <;> simp
  left_distrib x y z := by
    apply Queer.ext <;> simp [mul_add]
  right_distrib x y z := by
    apply Queer.ext <;> simp [add_mul]

/-- The pair multiplication makes `Q(n)` an associative unital ring. -/
instance instRing : Ring (Queer n) where
  toSemiring := instSemiring
  __ := (inferInstance : AddCommGroup (Queer n))
  __ := instNonAssocRing

/-- Scalars pass through the queer product in the left input. -/
theorem smul_mul (c : ℂ) (x y : Queer n) : (c • x) * y = c • (x * y) := by
  apply Queer.ext
  · change (c • x.evenPart) * y.evenPart + (c • x.oddPart) * y.oddPart =
      c • (x.evenPart * y.evenPart + x.oddPart * y.oddPart)
    rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, smul_add]
  · change (c • x.evenPart) * y.oddPart + (c • x.oddPart) * y.evenPart =
      c • (x.evenPart * y.oddPart + x.oddPart * y.evenPart)
    rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, smul_add]

/-- Scalars pass through the queer product in the right input. -/
theorem mul_smul (c : ℂ) (x y : Queer n) : x * (c • y) = c • (x * y) := by
  apply Queer.ext
  · change x.evenPart * (c • y.evenPart) + x.oddPart * (c • y.oddPart) =
      c • (x.evenPart * y.evenPart + x.oddPart * y.oddPart)
    rw [Algebra.mul_smul_comm, Algebra.mul_smul_comm, smul_add]
  · change x.evenPart * (c • y.oddPart) + x.oddPart * (c • y.evenPart) =
      c • (x.evenPart * y.oddPart + x.oddPart * y.evenPart)
    rw [Algebra.mul_smul_comm, Algebra.mul_smul_comm, smul_add]

/-- The complex algebra structure on `Q(n)`. -/
noncomputable instance instAlgebra : Algebra ℂ (Queer n) :=
  Algebra.ofModule smul_mul mul_smul

/-- The transported product equivalence, as a complex-linear equivalence. -/
noncomputable def linearEquivProd :
    Queer n ≃ₗ[ℂ] Matrix n n ℂ × Matrix n n ℂ :=
  equivProd.linearEquiv ℂ

/-- For finite `n`, the underlying vector space of `Q(n)` is finite-dimensional. -/
noncomputable instance instFiniteDimensional : FiniteDimensional ℂ (Queer n) :=
  LinearEquiv.finiteDimensional (linearEquivProd (n := n)).symm

/-! ## Internal parity grading -/

/-- The even part of `Q(n)`: pairs `(A,0)`. -/
def evenSubmodule : Submodule ℂ (Queer n) where
  carrier := {x | x.oddPart = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change x.oddPart = 0 at hx
    change y.oddPart = 0 at hy
    change x.oddPart + y.oddPart = 0
    rw [hx, hy, add_zero]
  smul_mem' c x hx := by
    change x.oddPart = 0 at hx
    change c • x.oddPart = 0
    rw [hx, smul_zero]

/-- The odd part of `Q(n)`: pairs `(0,B)`. -/
def oddSubmodule : Submodule ℂ (Queer n) where
  carrier := {x | x.evenPart = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change x.evenPart = 0 at hx
    change y.evenPart = 0 at hy
    change x.evenPart + y.evenPart = 0
    rw [hx, hy, add_zero]
  smul_mem' c x hx := by
    change x.evenPart = 0 at hx
    change c • x.evenPart = 0
    rw [hx, smul_zero]

@[simp] theorem mem_evenSubmodule {x : Queer n} : x ∈ evenSubmodule ↔ x.oddPart = 0 := Iff.rfl

@[simp] theorem mem_oddSubmodule {x : Queer n} : x ∈ oddSubmodule ↔ x.evenPart = 0 := Iff.rfl

/-- The even and odd matrix-pair submodules are complementary. -/
theorem isCompl_even_odd : IsCompl (evenSubmodule : Submodule ℂ (Queer n)) oddSubmodule := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    apply Queer.ext
    · exact hy
    · exact hx
  · rw [codisjoint_iff]
    apply top_unique
    intro x hx
    rw [Submodule.mem_sup]
    refine ⟨⟨x.evenPart, 0⟩, rfl, ⟨0, x.oddPart⟩, rfl, ?_⟩
    exact Queer.ext (by simp) (by simp)

/-- The parity family of the queer algebra. -/
def parity (p : ZMod 2) : Submodule ℂ (Queer n) :=
  if p = 0 then evenSubmodule else oddSubmodule

@[simp] theorem parity_zero : parity (n := n) 0 = evenSubmodule := by simp [parity]

@[simp] theorem parity_one : parity (n := n) 1 = oddSubmodule := by simp [parity]

/-- The pair decomposition is an internal `ZMod 2` grading. -/
theorem parity_isInternal : DirectSum.IsInternal (parity (n := n)) := by
  have huniv : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext p
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using zmod2_cases p
  apply (DirectSum.isInternal_submodule_iff_isCompl (parity (n := n))
    (show (0 : ZMod 2) ≠ 1 by decide) huniv).2
  simpa using isCompl_even_odd (n := n)

/-- The internal parity grading on `Q(n)`. -/
def parityGrading : ParityGrading (Queer n) where
  parity := parity
  isInternal := parity_isInternal

@[simp] theorem parityGrading_parity_zero :
    (parityGrading (n := n)).parity 0 = evenSubmodule := parity_zero

@[simp] theorem parityGrading_parity_one :
    (parityGrading (n := n)).parity 1 = oddSubmodule := parity_one

/-- Multiplication of homogeneous queer elements adds their parities. -/
theorem mul_mem_parity {p q : ZMod 2} {x y : Queer n}
    (hx : x ∈ parity (n := n) p) (hy : y ∈ parity (n := n) q) :
    x * y ∈ parity (n := n) (p + q) := by
  rcases zmod2_cases p with hp | hp <;> rcases zmod2_cases q with hq | hq <;>
    subst hp <;> subst hq
  · simp only [parity_zero, mem_evenSubmodule] at hx hy ⊢
    simp [hx, hy]
  · simp only [parity_zero, parity_one, mem_evenSubmodule, mem_oddSubmodule] at hx hy ⊢
    simp [hx, hy]
  · simp only [parity_zero, parity_one, mem_evenSubmodule, mem_oddSubmodule] at hx hy ⊢
    simp [hx, hy]
  · have hone : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [parity_one, mem_oddSubmodule] at hx hy
    rw [hone, parity_zero]
    simp only [mem_evenSubmodule]
    simp [hx, hy]

/-- `Q(n)` packaged as an associative superalgebra. -/
def associativeSuperalgebra : AssociativeSuperalgebra (Queer n) where
  toParityGrading := parityGrading
  mul_mem := mul_mem_parity

/-! ## The odd trace -/

/-- The queer odd trace `otr(A,B) = trace(B)`. -/
noncomputable def oddTrace : Queer n →ₗ[ℂ] ℂ where
  toFun x := Matrix.trace x.oddPart
  map_add' x y := Matrix.trace_add _ _
  map_smul' c x := Matrix.trace_smul _ _

@[simp] theorem oddTrace_apply (x : Queer n) : oddTrace x = Matrix.trace x.oddPart := rfl

/-- The odd trace obeys the homogeneous Koszul cyclicity law. -/
theorem oddTrace_koszul_cyclic {p q : ZMod 2} {x y : Queer n}
    (hx : x ∈ parity (n := n) p) (hy : y ∈ parity (n := n) q) :
    oddTrace (x * y) = koszul p q * oddTrace (y * x) := by
  rcases zmod2_cases p with hp | hp <;> rcases zmod2_cases q with hq | hq <;>
    subst hp <;> subst hq
  · simp only [parity_zero, mem_evenSubmodule] at hx hy
    simp [oddTrace, hx, hy]
  · simp only [parity_zero, parity_one, mem_evenSubmodule, mem_oddSubmodule] at hx hy
    simpa [oddTrace, hx, hy] using Matrix.trace_mul_comm x.evenPart y.oddPart
  · simp only [parity_zero, parity_one, mem_evenSubmodule, mem_oddSubmodule] at hx hy
    simpa [oddTrace, hx, hy] using Matrix.trace_mul_comm x.oddPart y.evenPart
  · simp only [parity_one, mem_oddSubmodule] at hx hy
    simp [oddTrace, hx, hy]

/-- The odd trace as an element of the supersymmetric-functional space of `Q(n)`. -/
theorem oddTrace_mem_supersymmetricFunctionals :
    oddTrace (n := n) ∈ supersymmetricFunctionals (associativeSuperalgebra (n := n)) := by
  rw [mem_supersymmetricFunctionals]
  intro p q x y hx hy
  exact oddTrace_koszul_cyclic hx hy

/-! ## Faithful block realization -/

/-- The standard block realization `(A,B) ↦ [[A,B],[B,A]]`. -/
def blockRealization : Queer n →ₗ[ℂ] Matrix (n ⊕ n) (n ⊕ n) ℂ where
  toFun x := Matrix.fromBlocks x.evenPart x.oddPart x.oddPart x.evenPart
  map_add' x y := by simp [Matrix.fromBlocks_add]
  map_smul' c x := by simp [Matrix.fromBlocks_smul]

@[simp] theorem blockRealization_apply (x : Queer n) :
    blockRealization x = Matrix.fromBlocks x.evenPart x.oddPart x.oddPart x.evenPart := rfl

/-- The block realization preserves the queer product. -/
theorem blockRealization_mul (x y : Queer n) :
    blockRealization (x * y) = blockRealization x * blockRealization y := by
  simp [blockRealization, Matrix.fromBlocks_multiply, add_comm]

/-- The block realization preserves the unit. -/
theorem blockRealization_one : blockRealization (1 : Queer n) = 1 := by
  simp [blockRealization, Matrix.fromBlocks_one]

/-- The standard block realization is faithful. -/
theorem blockRealization_injective : Function.Injective (blockRealization (n := n)) := by
  intro x y h
  apply Queer.ext
  · have := congrArg Matrix.toBlocks₁₁ h
    simpa [blockRealization] using this
  · have := congrArg Matrix.toBlocks₁₂ h
    simpa [blockRealization] using this

/-! ## Nontriviality and separation from the regular supertrace -/

/-- An odd diagonal matrix unit, used to exhibit the odd trace. -/
def oddMatrixUnit (i : n) : Queer n := ⟨0, Matrix.single i i 1⟩

@[simp] theorem oddMatrixUnit_mem (i : n) :
    oddMatrixUnit i ∈ parity (n := n) 1 := by simp [oddMatrixUnit]

@[simp] theorem oddTrace_oddMatrixUnit (i : n) : oddTrace (oddMatrixUnit i) = 1 := by
  change Matrix.trace (Matrix.single i i 1) = 1
  exact Matrix.trace_single_eq_same (α := ℂ) i 1

/-- The odd trace is nonzero whenever `n` is nonempty. -/
theorem oddTrace_ne_zero [Nonempty n] : oddTrace (n := n) ≠ 0 := by
  intro h
  let i : n := Classical.choice (inferInstance : Nonempty n)
  have hz : oddTrace (oddMatrixUnit i) = 0 := by rw [h]; rfl
  rw [oddTrace_oddMatrixUnit] at hz
  exact one_ne_zero hz

/-- Left multiplication in the regular queer module. -/
def leftMul (x : Queer n) : Module.End ℂ (Queer n) where
  toFun y := x * y
  map_add' y z := left_distrib x y z
  map_smul' c y := mul_smul c x y

@[simp] theorem leftMul_apply (x y : Queer n) : leftMul x y = x * y := rfl

/-- Left multiplication by a parity-`p` element is a parity-`p` endomorphism. -/
theorem leftMul_isParityHomogeneous {p : ZMod 2} {x : Queer n}
    (hx : x ∈ parity (n := n) p) :
    IsParityHomogeneousEnd (parityGrading (n := n)) p (leftMul x) := by
  intro q y hy
  exact mul_mem_parity hx hy

/-- The ordinary supertrace of the regular action vanishes on the odd component. -/
theorem regularSupertrace_eq_zero_of_odd {x : Queer n}
    (hx : x ∈ parity (n := n) 1) :
    supertrace (parityGrading (n := n)) (leftMul x) = 0 :=
  supertrace_eq_zero_of_odd _ (leftMul_isParityHomogeneous hx)

/-- On an odd matrix unit the odd trace is `1`, whereas the ordinary supertrace of its regular
action is `0`.  This is the concrete Type-II distinction used downstream. -/
theorem oddTrace_distinguished_from_regularSupertrace (i : n) :
    oddTrace (oddMatrixUnit i) = 1 ∧
      supertrace (parityGrading (n := n)) (leftMul (oddMatrixUnit i)) = 0 := by
  exact ⟨oddTrace_oddMatrixUnit i, regularSupertrace_eq_zero_of_odd (oddMatrixUnit_mem i)⟩

end Queer

end VOA
