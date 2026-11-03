/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Modularity.SuperTrace
import VOA.Modularity.SuperSymmetricFunctionals
import VOA.Modularity.QueerOddTrace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Standard functionals on a supplied finite super-Wedderburn product

This file proves only the finite-dimensional superalgebra calculation consumed by a future
strong-rationality argument.  A type-M block is a full matrix algebra with a parity-labelled
standard basis and carries its matrix supertrace.  A type-Q block is the concrete queer algebra
from `QueerOddTrace` and carries its odd trace.

`FiniteSuperWedderburnDecomposition` is genuine supplied data: its combined coordinate map is
bijective and each coordinate preserves parity.  Pulling back the standard block functionals
gives a linearly independent family of supersymmetric functionals.  It spans only under the
explicitly oriented bound

`finrank (supersymmetricFunctionals P) <= number of blocks`.

No theorem here produces such a decomposition, classifies simple associative superalgebras, or
deduces super-Wedderburn data from rationality or strong rationality.  No sector, module, or
genus-one trace-realization statement occurs.
-/

namespace VOA

open Module (End finrank)
open scoped BigOperators

set_option autoImplicit false

universe u

/-! ## Coordinate and matrix parity -/

/-- Vectors supported on standard basis coordinates of parity `p`. -/
def coordinateParity {n : Nat} (epsilon : Fin n → ZMod 2) (p : ZMod 2) :
    Submodule Complex (Fin n → Complex) where
  carrier := {x | ∀ i, epsilon i ≠ p → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

@[simp] theorem mem_coordinateParity {n : Nat} {epsilon : Fin n → ZMod 2}
    {p : ZMod 2} {x : Fin n → Complex} :
    x ∈ coordinateParity epsilon p ↔ ∀ i, epsilon i ≠ p → x i = 0 := Iff.rfl

private theorem zmod2_add_self_cancel (a b : ZMod 2) : (a + b) + b = a := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    subst ha <;> subst hb <;> decide

private theorem zmod2_middle_cancel (a b c : ZMod 2) :
    (a + b) + (b + c) = a + c := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    rcases zmod2_cases c with hc | hc <;> subst ha <;> subst hb <;> subst hc <;> decide

/-- The even and odd coordinate subspaces are complementary. -/
theorem coordinateParity_isCompl {n : Nat} (epsilon : Fin n → ZMod 2) :
    IsCompl (coordinateParity epsilon 0) (coordinateParity epsilon 1) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx0 hx1
    funext i
    rcases zmod2_cases (epsilon i) with hi | hi
    · exact hx1 i (by simp [hi])
    · exact hx0 i (by simp [hi])
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    let x0 : Fin n → Complex := fun i => if epsilon i = 0 then x i else 0
    let x1 : Fin n → Complex := fun i => if epsilon i = 1 then x i else 0
    rw [Submodule.mem_sup]
    refine ⟨x0, ?_, x1, ?_, ?_⟩
    · intro i hi
      simp [x0, hi]
    · intro i hi
      simp [x1, hi]
    · funext i
      rcases zmod2_cases (epsilon i) with hi | hi <;> simp [x0, x1, hi]

/-- The internal parity grading of the standard coordinate space. -/
theorem coordinateParity_isInternal {n : Nat} (epsilon : Fin n → ZMod 2) :
    DirectSum.IsInternal (coordinateParity epsilon) := by
  have huniv : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext p
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using zmod2_cases p
  apply (DirectSum.isInternal_submodule_iff_isCompl (coordinateParity epsilon)
    (show (0 : ZMod 2) ≠ 1 by decide) huniv).2
  exact coordinateParity_isCompl epsilon

/-- Standard parity grading associated to a parity-labelled basis. -/
def coordinateParityGrading {n : Nat} (epsilon : Fin n → ZMod 2) :
    ParityGrading (Fin n → Complex) where
  parity := coordinateParity epsilon
  isInternal := coordinateParity_isInternal epsilon

/-- Matrices supported on entries of parity `p`; `E_ij` has parity
`epsilon i + epsilon j`. -/
def matrixSuperParity {n : Nat} (epsilon : Fin n → ZMod 2) (p : ZMod 2) :
    Submodule Complex (Matrix (Fin n) (Fin n) Complex) where
  carrier := {A | ∀ i j, epsilon i + epsilon j ≠ p → A i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i j hij
    simp [hA i j hij, hB i j hij]
  smul_mem' := by
    intro c A hA i j hij
    simp [hA i j hij]

@[simp] theorem mem_matrixSuperParity {n : Nat} {epsilon : Fin n → ZMod 2}
    {p : ZMod 2} {A : Matrix (Fin n) (Fin n) Complex} :
    A ∈ matrixSuperParity epsilon p ↔
      ∀ i j, epsilon i + epsilon j ≠ p → A i j = 0 := Iff.rfl

/-- The even and odd matrix subspaces are complementary. -/
theorem matrixSuperParity_isCompl {n : Nat} (epsilon : Fin n → ZMod 2) :
    IsCompl (matrixSuperParity epsilon 0) (matrixSuperParity epsilon 1) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro A hA0 hA1
    ext i j
    rcases zmod2_cases (epsilon i + epsilon j) with hij | hij
    · exact hA1 i j (by simp [hij])
    · exact hA0 i j (by simp [hij])
  · rw [codisjoint_iff]
    apply top_unique
    intro A _
    let A0 : Matrix (Fin n) (Fin n) Complex := fun i j =>
      if epsilon i + epsilon j = 0 then A i j else 0
    let A1 : Matrix (Fin n) (Fin n) Complex := fun i j =>
      if epsilon i + epsilon j = 1 then A i j else 0
    rw [Submodule.mem_sup]
    refine ⟨A0, ?_, A1, ?_, ?_⟩
    · intro i j hij
      simp [A0, hij]
    · intro i j hij
      simp [A1, hij]
    · ext i j
      rcases zmod2_cases (epsilon i + epsilon j) with hij | hij <;> simp [A0, A1, hij]

theorem matrixSuperParity_isInternal {n : Nat} (epsilon : Fin n → ZMod 2) :
    DirectSum.IsInternal (matrixSuperParity epsilon) := by
  have huniv : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext p
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using zmod2_cases p
  apply (DirectSum.isInternal_submodule_iff_isCompl (matrixSuperParity epsilon)
    (show (0 : ZMod 2) ≠ 1 by decide) huniv).2
  exact matrixSuperParity_isCompl epsilon

/-- Matrix multiplication adds declared entry parities. -/
theorem matrixSuperParity_mul_mem {n : Nat} {epsilon : Fin n → ZMod 2}
    {p q : ZMod 2} {A B : Matrix (Fin n) (Fin n) Complex}
    (hA : A ∈ matrixSuperParity epsilon p) (hB : B ∈ matrixSuperParity epsilon q) :
    A * B ∈ matrixSuperParity epsilon (p + q) := by
  intro i k hik
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : epsilon i + epsilon j = p
  · have hjk : epsilon j + epsilon k ≠ q := by
      intro hjk
      apply hik
      calc
        epsilon i + epsilon k =
            (epsilon i + epsilon j) + (epsilon j + epsilon k) :=
          (zmod2_middle_cancel _ _ _).symm
        _ = p + q := by rw [hij, hjk]
    rw [hB j k hjk, mul_zero]
  · rw [hA i j hij, zero_mul]

/-- The standard type-M matrix superalgebra. -/
def matrixAssociativeSuperalgebra {n : Nat} (epsilon : Fin n → ZMod 2) :
    AssociativeSuperalgebra (Matrix (Fin n) (Fin n) Complex) where
  parity := matrixSuperParity epsilon
  isInternal := matrixSuperParity_isInternal epsilon
  mul_mem := matrixSuperParity_mul_mem

/-- A homogeneous matrix induces an endomorphism of the same parity. -/
theorem matrix_toLin_isParityHomogeneous {n : Nat} {epsilon : Fin n → ZMod 2}
    {p : ZMod 2} {A : Matrix (Fin n) (Fin n) Complex}
    (hA : A ∈ matrixSuperParity epsilon p) :
    IsParityHomogeneousEnd (coordinateParityGrading epsilon) p (Matrix.toLin' A) := by
  intro q x hx i hi
  rw [Matrix.toLin'_apply']
  change ∑ j, A i j * x j = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : epsilon j = q
  · have hij : epsilon i + epsilon j ≠ p := by
      intro hij
      apply hi
      calc
        epsilon i = (epsilon i + epsilon j) + epsilon j :=
          (zmod2_add_self_cancel _ _).symm
        _ = p + q := by rw [hij, hj]
    rw [hA i j hij, zero_mul]
  · rw [hx j hj, mul_zero]

/-! ## Concrete standard block functionals -/

/-- The type-M matrix supertrace through the parity-labelled coordinate module. -/
noncomputable def matrixSupertrace {n : Nat} (epsilon : Fin n → ZMod 2) :
    Matrix (Fin n) (Fin n) Complex →ₗ[Complex] Complex :=
  (supertraceLinear (coordinateParityGrading epsilon)).comp Matrix.toLin'.toLinearMap

/-- The type-M matrix supertrace is supersymmetric. -/
theorem matrixSupertrace_mem_supersymmetricFunctionals {n : Nat}
    (epsilon : Fin n → ZMod 2) :
    matrixSupertrace epsilon ∈
      supersymmetricFunctionals (matrixAssociativeSuperalgebra epsilon) := by
  rw [mem_supersymmetricFunctionals]
  intro p q A B hA hB
  change supertrace (coordinateParityGrading epsilon) (Matrix.toLin' (A * B)) =
    koszul p q * supertrace (coordinateParityGrading epsilon) (Matrix.toLin' (B * A))
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact supertrace_mul_comm (coordinateParityGrading epsilon)
    (matrix_toLin_isParityHomogeneous hA) (matrix_toLin_isParityHomogeneous hB)

/-- A diagonal matrix unit has supertrace equal to its basis-parity sign. -/
theorem matrixSupertrace_single_diag {n : Nat} (epsilon : Fin n → ZMod 2) (i : Fin n) :
    matrixSupertrace epsilon (Matrix.single i i 1) = parSign (epsilon i) := by
  let P := coordinateParityGrading epsilon
  let E : Matrix (Fin n) (Fin n) Complex := Matrix.single i i 1
  have himage : ∀ x : Fin n → Complex,
      Matrix.toLin' E x ∈ coordinateParity epsilon (epsilon i) := by
    intro x j hj
    rw [Matrix.toLin'_apply']
    change Matrix.mulVec E x j = 0
    rw [show E = Matrix.single i i 1 from rfl, Matrix.single_mulVec]
    have hji : j ≠ i := fun hji => hj (hji ▸ rfl)
    simp [hji]
  have htheta : P.parityInvol * Matrix.toLin' E =
      parSign (epsilon i) • Matrix.toLin' E := by
    apply LinearMap.ext
    intro x
    change P.parityInvol (Matrix.toLin' E x) = _
    rw [P.parityInvol_homog (himage x)]
    rfl
  change supertrace P (Matrix.toLin' E) = _
  rw [supertrace, htheta, map_smul, Matrix.trace_toLin'_eq]
  simp [E]

/-! ## Certified M/Q blocks -/

/-- The two concrete simple-block shapes used by the supplied decomposition. -/
inductive SuperWedderburnKind
  | typeM
  | typeQ

/-- A finite block with its nonzero standard supersymmetric functional and an explicit M- or
Q-model certificate.  This is data, not a classification result. -/
structure SuperWedderburnBlock where
  carrier : Type u
  [ring : Ring carrier]
  [algebra : Algebra Complex carrier]
  [finiteDimensional : FiniteDimensional Complex carrier]
  superalgebra : AssociativeSuperalgebra carrier
  standardFunctional : carrier →ₗ[Complex] Complex
  standardFunctional_supersymmetric :
    standardFunctional ∈ supersymmetricFunctionals superalgebra
  standardFunctional_one : ∃ x, standardFunctional x = 1
  kind : SuperWedderburnKind
  typeM_model : kind = .typeM → ∃ (n : Nat) (epsilon : Fin n → ZMod 2)
    (e : carrier ≃ₐ[Complex] Matrix (Fin n) (Fin n) Complex),
      (∀ p x, x ∈ superalgebra.parity p ↔ e x ∈ matrixSuperParity epsilon p) ∧
      (∀ x, standardFunctional x = matrixSupertrace epsilon (e x))
  typeQ_model : kind = .typeQ → ∃ (n : Nat) (e : carrier ≃ₐ[Complex] Queer (Fin n)),
      (∀ p x, x ∈ superalgebra.parity p ↔ e x ∈ Queer.parity p) ∧
      (∀ x, standardFunctional x = Queer.oddTrace (e x))

attribute [instance] SuperWedderburnBlock.ring SuperWedderburnBlock.algebra
  SuperWedderburnBlock.finiteDimensional

namespace SuperWedderburnBlock

/-- A positive-size type-M matrix block. -/
noncomputable def typeM (n : Nat) (epsilon : Fin n → ZMod 2) (hn : 0 < n) :
    SuperWedderburnBlock where
  carrier := Matrix (Fin n) (Fin n) Complex
  superalgebra := matrixAssociativeSuperalgebra epsilon
  standardFunctional := matrixSupertrace epsilon
  standardFunctional_supersymmetric := matrixSupertrace_mem_supersymmetricFunctionals epsilon
  standardFunctional_one := by
    let i : Fin n := ⟨0, hn⟩
    refine ⟨parSign (epsilon i) • Matrix.single i i 1, ?_⟩
    rw [map_smul, matrixSupertrace_single_diag, smul_eq_mul, parSign_mul_self]
  kind := .typeM
  typeM_model := by
    intro
    exact ⟨n, epsilon, AlgEquiv.refl, fun _ _ => Iff.rfl, fun _ => rfl⟩
  typeQ_model := by simp

/-- A positive-size concrete queer block with its odd trace. -/
noncomputable def typeQ (n : Nat) (hn : 0 < n) : SuperWedderburnBlock where
  carrier := Queer (Fin n)
  superalgebra := Queer.associativeSuperalgebra
  standardFunctional := Queer.oddTrace
  standardFunctional_supersymmetric := Queer.oddTrace_mem_supersymmetricFunctionals
  standardFunctional_one := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨Queer.oddMatrixUnit i, Queer.oddTrace_oddMatrixUnit i⟩
  kind := .typeQ
  typeM_model := by simp
  typeQ_model := by
    intro
    exact ⟨n, AlgEquiv.refl, fun _ _ => Iff.rfl, fun _ => rfl⟩

end SuperWedderburnBlock

/-! ## Supplied finite products -/

variable {A : Type u} [Ring A] [Algebra Complex A]

/-- A genuine finite product decomposition supplied as algebraic data.  The coordinate map is
bijective, and each coordinate preserves the displayed parity grading. -/
structure FiniteSuperWedderburnDecomposition (P : AssociativeSuperalgebra A) where
  blockCount : Nat
  block : Fin blockCount → SuperWedderburnBlock.{u}
  coordinate : ∀ i, A →ₐ[Complex] (block i).carrier
  coordinate_parity : ∀ i p a, a ∈ P.parity p →
    coordinate i a ∈ (block i).superalgebra.parity p
  coordinate_bijective : Function.Bijective (fun a i => coordinate i a)

namespace FiniteSuperWedderburnDecomposition

variable {P : AssociativeSuperalgebra A}

/-- The combined coordinate algebra homomorphism. -/
noncomputable def coordinateAlgHom (D : FiniteSuperWedderburnDecomposition P) :
    A →ₐ[Complex] (∀ i, (D.block i).carrier) where
  toFun a i := D.coordinate i a
  map_one' := by funext i; exact map_one (D.coordinate i)
  map_mul' a b := by funext i; exact map_mul (D.coordinate i) a b
  map_zero' := by funext i; exact map_zero (D.coordinate i)
  map_add' a b := by funext i; exact map_add (D.coordinate i) a b
  commutes' c := by funext i; exact (D.coordinate i).commutes c

/-- The supplied bijection as an algebra equivalence to the finite product. -/
noncomputable def algEquiv (D : FiniteSuperWedderburnDecomposition P) :
    A ≃ₐ[Complex] (∀ i, (D.block i).carrier) :=
  AlgEquiv.ofBijective D.coordinateAlgHom D.coordinate_bijective

/-- The source algebra is finite-dimensional because the supplied finite product is. -/
@[reducible] noncomputable def finiteDimensional (D : FiniteSuperWedderburnDecomposition P) :
    FiniteDimensional Complex A :=
  D.algEquiv.symm.toLinearEquiv.finiteDimensional

/-- The product decomposition gives the exact underlying vector-space dimension. -/
theorem finrank_eq_sum_block_finrank (D : FiniteSuperWedderburnDecomposition P) :
    finrank Complex A = ∑ i, finrank Complex (D.block i).carrier := by
  letI : FiniteDimensional Complex A := D.finiteDimensional
  rw [D.algEquiv.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

/-- If the supplied product has no blocks, the source is the zero algebra as a vector space.
This records the empty-product degeneracy explicitly. -/
theorem subsingleton_of_blockCount_eq_zero (D : FiniteSuperWedderburnDecomposition P)
    (hzero : D.blockCount = 0) : Subsingleton A := by
  constructor
  intro a b
  apply D.coordinate_bijective.1
  funext i
  exact Fin.elim0 (hzero ▸ i)

/-- Pullback of the standard M-supertrace or Q-odd-trace on one block. -/
noncomputable def blockFunctional (D : FiniteSuperWedderburnDecomposition P)
    (i : Fin D.blockCount) : A →ₗ[Complex] Complex :=
  (D.block i).standardFunctional.comp (D.coordinate i).toLinearMap

/-- Every pulled-back standard block functional is supersymmetric. -/
theorem blockFunctional_mem_supersymmetricFunctionals
    (D : FiniteSuperWedderburnDecomposition P) (i : Fin D.blockCount) :
    D.blockFunctional i ∈ supersymmetricFunctionals P := by
  rw [mem_supersymmetricFunctionals]
  intro p q a b ha hb
  change (D.block i).standardFunctional (D.coordinate i (a * b)) =
    koszul p q * (D.block i).standardFunctional (D.coordinate i (b * a))
  calc
    _ = (D.block i).standardFunctional (D.coordinate i a * D.coordinate i b) :=
      congrArg (D.block i).standardFunctional ((D.coordinate i).map_mul a b)
    _ = koszul p q *
        (D.block i).standardFunctional (D.coordinate i b * D.coordinate i a) :=
      (D.block i).standardFunctional_supersymmetric p q _ _
        (D.coordinate_parity i p a ha) (D.coordinate_parity i q b hb)
    _ = _ := congrArg
      (fun z => koszul p q * (D.block i).standardFunctional z)
      ((D.coordinate i).map_mul b a).symm

/-- Product coordinate vector supported at `i`, normalized by its standard functional. -/
noncomputable def functionalCoordinate (D : FiniteSuperWedderburnDecomposition P)
    (i : Fin D.blockCount) : ∀ j, (D.block j).carrier :=
  Pi.single i (Classical.choose (D.block i).standardFunctional_one)

/-- Source element separating the `i`-th standard functional from the other blocks. -/
noncomputable def functionalSeparator (D : FiniteSuperWedderburnDecomposition P)
    (i : Fin D.blockCount) : A :=
  Classical.choose (D.coordinate_bijective.2 (D.functionalCoordinate i))

theorem coordinate_functionalSeparator (D : FiniteSuperWedderburnDecomposition P)
    (i j : Fin D.blockCount) :
    D.coordinate j (D.functionalSeparator i) = D.functionalCoordinate i j := by
  have h := Classical.choose_spec (D.coordinate_bijective.2 (D.functionalCoordinate i))
  exact congrFun h j

/-- The standard block functionals have exact Kronecker-delta values on the separators. -/
theorem blockFunctional_functionalSeparator (D : FiniteSuperWedderburnDecomposition P)
    (i j : Fin D.blockCount) :
    D.blockFunctional j (D.functionalSeparator i) = if j = i then 1 else 0 := by
  change (D.block j).standardFunctional (D.coordinate j (D.functionalSeparator i)) = _
  rw [coordinate_functionalSeparator, functionalCoordinate]
  by_cases hji : j = i
  · subst j
    rw [Pi.single_eq_same]
    simpa using Classical.choose_spec (D.block i).standardFunctional_one
  · rw [Pi.single_eq_of_ne hji, map_zero, if_neg hji]

/-- Standard type-M supertraces and type-Q odd traces from distinct blocks are independent. -/
theorem linearIndependent_blockFunctional (D : FiniteSuperWedderburnDecomposition P) :
    LinearIndependent Complex D.blockFunctional := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hval : ∑ j ∈ s, c j * D.blockFunctional j (D.functionalSeparator i) = 0 := by
    simpa using LinearMap.congr_fun hc (D.functionalSeparator i)
  simp only [D.blockFunctional_functionalSeparator] at hval
  rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [if_neg hji, mul_zero])
      (fun hnot => absurd hi hnot), if_pos rfl, mul_one] at hval
  exact hval

/-- The family remains independent inside the supersymmetric-functional submodule. -/
theorem linearIndependent_blockFunctionalSubtype (D : FiniteSuperWedderburnDecomposition P) :
    LinearIndependent Complex (fun i =>
      (⟨D.blockFunctional i, D.blockFunctional_mem_supersymmetricFunctionals i⟩ :
        supersymmetricFunctionals P)) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  apply (linearIndependent_iff'.mp D.linearIndependent_blockFunctional) s c
  · apply LinearMap.ext
    intro a
    have hca := congrArg
      (fun f : supersymmetricFunctionals P => (f : A →ₗ[Complex] Complex) a) hc
    simpa using hca
  · exact hi

/-- The correctly oriented residual dimension input needed for spanning.  Independence proves
the reverse inequality; classification must supply this upper bound. -/
def FunctionalDimensionBound (D : FiniteSuperWedderburnDecomposition P) : Prop :=
  finrank Complex (supersymmetricFunctionals P) ≤ D.blockCount

/-- Under the explicit dimension upper bound, the standard block functionals span. -/
theorem span_blockFunctional_eq_supersymmetricFunctionals
    (D : FiniteSuperWedderburnDecomposition P) (hbound : D.FunctionalDimensionBound) :
    Submodule.span Complex (Set.range fun i =>
      (⟨D.blockFunctional i, D.blockFunctional_mem_supersymmetricFunctionals i⟩ :
        supersymmetricFunctionals P)) = ⊤ := by
  letI : FiniteDimensional Complex A := D.finiteDimensional
  let t : Fin D.blockCount → supersymmetricFunctionals P := fun i =>
    ⟨D.blockFunctional i, D.blockFunctional_mem_supersymmetricFunctionals i⟩
  have hind : LinearIndependent Complex t := D.linearIndependent_blockFunctionalSubtype
  have hrank : finrank Complex (Submodule.span Complex (Set.range t)) = D.blockCount := by
    simpa using finrank_span_eq_card hind
  apply Submodule.eq_top_of_finrank_eq
  rw [hrank]
  exact le_antisymm (by simpa using hind.fintype_card_le_finrank) hbound

/-- Every supersymmetric functional is a finite linear combination of the standard blocks under
the dimension upper bound. -/
theorem exists_eq_sum_blockFunctional
    (D : FiniteSuperWedderburnDecomposition P) (hbound : D.FunctionalDimensionBound)
    (phi : supersymmetricFunctionals P) :
    ∃ c : Fin D.blockCount → Complex,
      (phi : A →ₗ[Complex] Complex) = ∑ i, c i • D.blockFunctional i := by
  have hmem : phi ∈ Submodule.span Complex (Set.range fun i =>
      (⟨D.blockFunctional i, D.blockFunctional_mem_supersymmetricFunctionals i⟩ :
        supersymmetricFunctionals P)) := by
    rw [D.span_blockFunctional_eq_supersymmetricFunctionals hbound]
    trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro a
  have hca := congrArg
    (fun f : supersymmetricFunctionals P => (f : A →ₗ[Complex] Complex) a) hc.symm
  simpa using hca

/-- Under the bound, there is exactly one supersymmetric-functional dimension per block. -/
theorem finrank_supersymmetricFunctionals_eq_blockCount
    (D : FiniteSuperWedderburnDecomposition P) (hbound : D.FunctionalDimensionBound) :
    finrank Complex (supersymmetricFunctionals P) = D.blockCount := by
  letI : FiniteDimensional Complex A := D.finiteDimensional
  exact le_antisymm hbound
    (by simpa using D.linearIndependent_blockFunctionalSubtype.fintype_card_le_finrank)

/-! ## Concrete convention tests -/

/-- Standard parity on a `1|1` coordinate space. -/
def mOneOneParity (i : Fin 2) : ZMod 2 := if i = 0 then 0 else 1

@[simp] theorem mOneOneParity_zero : mOneOneParity 0 = 0 := by simp [mOneOneParity]

@[simp] theorem mOneOneParity_one : mOneOneParity 1 = 1 := by simp [mOneOneParity]

/-- The even basis line in `M(1|1)` has supertrace `+1`. -/
theorem mOneOne_supertrace_even_test :
    matrixSupertrace mOneOneParity (Matrix.single 0 0 1) = 1 := by
  rw [matrixSupertrace_single_diag, mOneOneParity_zero, parSign_zero]

/-- The odd basis line in `M(1|1)` has supertrace `-1`. -/
theorem mOneOne_supertrace_odd_test :
    matrixSupertrace mOneOneParity (Matrix.single 1 1 1) = -1 := by
  rw [matrixSupertrace_single_diag, mOneOneParity_one, parSign_one]

/-- The odd generator of `Q(1)` has odd trace one. -/
theorem qOne_oddTrace_test :
    Queer.oddTrace (Queer.oddMatrixUnit (0 : Fin 1)) = 1 :=
  Queer.oddTrace_oddMatrixUnit 0

end FiniteSuperWedderburnDecomposition

end VOA
