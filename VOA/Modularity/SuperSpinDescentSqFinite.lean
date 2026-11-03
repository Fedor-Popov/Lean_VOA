/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSpinDescentSq
import VOA.Modularity.SuperSectorSystem

/-!
# Finite square-weight spin-sector descent

This file gives the finite cusp-quotient consequence of the square-weight spin
relations.  The induction index is the doubled square weight `n : Nat`, representing `n/2`.
The official half-grading triangularity shows that precisely these square-weight eigenspaces span.

For one fixed outer `BoundaryPair`, the four values of `SpinPair` remain inner simultaneous
state-eigencharacter labels.  The two automorphisms are assumed to be involutions; they are never
identified with parity, and no spin--statistics premise is used.

The ordinary-mode C2 span is not square-graded: square `L[0]` contains positive ordinary
Virasoro modes, so asserting that its square-weight projections remain in ordinary C2 would be
too strong.  Instead this file defines the honest coordinate-changed carrier `superSqO₂`, spanned
by the official global square `[-2]` products.  Square-weight projection stability and exact
fixed-pair spin/square-degree generation are theorems for that carrier.

Ordinary super-C2 cofiniteness still implies finite-dimensional square C2.  The proof projects
ordinary C2 into its genuine doubled ordinary degrees and uses the leading coefficient one of
the complex-weight square mode to replace each ordinary `[-2]` generator by a square `[-2]`
generator plus strictly lower doubled ordinary weight.  Thus the final square-spin cusp quotient
is finite without an extra C2 projection or exact-degree hypothesis.  No original-weight
translation law, spin--statistics premise, trace realization, or modularity claim occurs.
-/

namespace VOA

open scoped BigOperators
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module Complex VType]
variable {W : SuperVertexOperatorAlgebra VType}

namespace SuperNearVOA

/-! ## The honest doubled square-weight spectrum -/

/-- Every nonnegative doubled ordinary-weight filtration step is spanned by square eigenspaces
whose eigenvalues are nonnegative half-integers. -/
theorem halfGradeLE_le_iSup_superSqWeightSpace_nat
    (W : SuperVertexOperatorAlgebra VType) :
    forall n : Nat, halfGradeLE W ((n : Int) - 1) <=
      ⨆ d : Nat, W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2) := by
  intro n
  induction n with
  | zero =>
      rw [show ((0 : Nat) : Int) - 1 = -1 by norm_num,
        halfGradeLE_eq_bot W (by norm_num)]
      exact bot_le
  | succ m ih =>
      rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by push_cast; ring,
        halfGradeLE_split W (m : Int)]
      refine sup_le (fun x hx => ?_) ih
      have hw := superLsq_zero_sub_smul_mem_halfGradeLE W hx
      obtain ⟨y, hymem, hyeq⟩ :=
        superLsq_sub_halfWeight_surj W (m : Int) m
          (W.toSuperNearVOA.superLsq 0 x - ((m : Complex) / 2) • x)
          (by simpa only using hw) (by omega)
      have hymem' : y ∈ halfGradeLE W ((m : Int) - 1) := by
        simpa only using hymem
      have heig : x - y ∈
          W.toSuperNearVOA.superSqWeightSpace ((m : Complex) / 2) := by
        rw [W.toSuperNearVOA.mem_superSqWeightSpace_iff, map_sub, smul_sub]
        have hcast : (((m : Int) : Complex) / 2) = ((m : Complex) / 2) := by norm_num
        rw [hcast] at hyeq
        linear_combination (norm := abel) -hyeq
      rw [show x = (x - y) + y by abel]
      exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem m heig) (ih hymem')

/-- The square-weight spectrum of a half-integrally graded super VOA is supported on
nonnegative half-integers, and those eigenspaces span the state space. -/
theorem iSup_superSqWeightSpace_nat_eq_top
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    (⨆ d : Nat, W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨d, hd⟩ := exists_mem_halfGradeLE W hhalf x
  exact halfGradeLE_le_iSup_superSqWeightSpace_nat W (d + 1).toNat
    (halfGradeLE_mono W (show d <= (((d + 1).toNat : Int)) - 1 by omega) hd)

/-- A negative half-integer is not a square-bracket weight. -/
theorem superSqWeightSpace_eq_bot_of_neg_halfWeight
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (z : Int) (hz : z < 0) :
    W.toSuperNearVOA.superSqWeightSpace ((z : Complex) / 2) = ⊥ := by
  let f : Nat -> Complex := fun d => (d : Complex) / 2
  have hnot : ((z : Complex) / 2) ∉ Set.range f := by
    rintro ⟨d, hd⟩
    have hcast : (z : Complex) = (d : Complex) := by
      dsimp only [f] at hd
      exact (div_left_inj' (by norm_num : (2 : Complex) ≠ 0)).mp hd.symm
    have hzInt : z = (d : Int) := by exact_mod_cast hcast
    omega
  have hind := W.toSuperNearVOA.superSqWeightSpace_iSupIndep.disjoint_biSup hnot
  have htop :
      (⨆ k ∈ Set.range f, W.toSuperNearVOA.superSqWeightSpace k) = ⊤ := by
    apply top_unique
    rw [← iSup_superSqWeightSpace_nat_eq_top W hhalf]
    refine iSup_le fun d => le_iSup_of_le (f d) ?_
    exact le_iSup_of_le (show f d ∈ Set.range f from ⟨d, rfl⟩) le_rfl
  rw [htop, disjoint_top] at hind
  exact hind

/-! ## One outer boundary pair and its inner labels -/

/-- For an outer pair of involutions, the projector ranges are exactly the inner simultaneous
eigenspaces already attached to the `BoundaryPair`. -/
theorem BoundaryPair.spinSectors_eq_spinEigenspace (b : BoundaryPair W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1) :
    SuperAut.spinSectors b.spatial b.temporal = b.spinEigenspace := by
  funext p
  ext x
  rw [SuperAut.mem_spinSectors_iff b.spatial b.temporal hspatial htemporal
    b.commute.eq]
  rfl

/-- Square Virasoro operators preserve an inner eigenspace for the fixed outer boundary pair. -/
theorem BoundaryPair.superLsq_mem_spinEigenspace (b : BoundaryPair W)
    {p : SpinPair} {a : VType} (ha : a ∈ b.spinEigenspace p) (n : Int) :
    W.toSuperNearVOA.superLsq n a ∈ b.spinEigenspace p := by
  rw [BoundaryPair.mem_spinEigenspace] at ha ⊢
  constructor
  · calc
      b.spatial (W.toSuperNearVOA.superLsq n a) =
          W.toSuperNearVOA.superLsq n (b.spatial a) :=
        b.spatial.map_superLsq n a
      _ = W.toSuperNearVOA.superLsq n (SpinPhase.value p.mu • a) := by rw [ha.1]
      _ = SpinPhase.value p.mu • W.toSuperNearVOA.superLsq n a := by rw [map_smul]
  · calc
      b.temporal (W.toSuperNearVOA.superLsq n a) =
          W.toSuperNearVOA.superLsq n (b.temporal a) :=
        b.temporal.map_superLsq n a
      _ = W.toSuperNearVOA.superLsq n (SpinPhase.value p.lambda • a) := by rw [ha.2]
      _ = SpinPhase.value p.lambda • W.toSuperNearVOA.superLsq n a := by rw [map_smul]

/-- Simultaneous inner-spin and doubled square-weight homogeneity for one fixed outer pair. -/
def BoundaryPair.IsSpinSqHalfHomogeneous (b : BoundaryPair W)
    (x : VType) : Prop :=
  exists (p : SpinPair) (d : Nat), x ∈ b.spinEigenspace p ∧
    x ∈ W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2)

/-- Inner-spin and doubled square-weight bihomogeneous vectors span the state space. -/
theorem BoundaryPair.span_isSpinSqHalfHomogeneous_eq_top
    (b : BoundaryPair W) (hhalf : IsHalfIntegerGraded W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1) :
    Submodule.span Complex {x | BoundaryPair.IsSpinSqHalfHomogeneous b x} = ⊤ := by
  rw [eq_top_iff, ← iSup_superSqWeightSpace_nat_eq_top W hhalf]
  refine iSup_le fun d x hx => ?_
  rw [← SuperAut.sum_spinPairProjector b.spatial b.temporal x]
  refine Submodule.sum_mem _ fun p _ => ?_
  apply Submodule.subset_span
  refine ⟨p, d, ?_, b.spatial.spinPairProjector_mem_superSqWeightSpace
    b.temporal p hx⟩
  rw [← BoundaryPair.spinSectors_eq_spinEigenspace b hspatial htemporal]
  exact ⟨x, rfl⟩

/-! ## The square-C2 carrier and its exact grading -/

/-- The coordinate-changed C2 carrier, generated by the official global square `[-2]` products.

This is deliberately distinct from the original-mode `superO2`.  The latter is not preserved by
square-weight projection: square `L[0]` contains positive ordinary Virasoro modes, under which the
ordinary C2 span need not be stable. -/
def superSqO₂ (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) : Submodule Complex VType :=
  Submodule.span Complex {x | exists a c : VType,
    x = superSqModeHalf W hhalf (-2) a c}

/-- A vector homogeneous for the nonnegative doubled square-weight grading. -/
def IsSqHalfHomogeneous (W : SuperVertexOperatorAlgebra VType) (x : VType) : Prop :=
  exists d : Nat, x ∈ W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2)

/-- Nonnegative doubled square-weight homogeneous vectors span the state space. -/
theorem span_isSqHalfHomogeneous_eq_top
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    Submodule.span Complex {x | IsSqHalfHomogeneous W x} = ⊤ := by
  rw [eq_top_iff, ← iSup_superSqWeightSpace_nat_eq_top W hhalf]
  refine iSup_le fun d x hx => ?_
  exact Submodule.subset_span ⟨d, hx⟩

/-- Square-bihomogeneous global `[-2]` generators. -/
def superSqO2SqGen (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) : Set VType :=
  {x | exists (p q : Nat) (a c : VType),
    a ∈ W.toSuperNearVOA.superSqWeightSpace ((p : Complex) / 2) ∧
    c ∈ W.toSuperNearVOA.superSqWeightSpace ((q : Complex) / 2) ∧
    x = superSqModeHalf W hhalf (-2) a c}

/-- The global square-C2 carrier is spanned by square-bihomogeneous generators. -/
theorem superSqO₂_eq_span_sqGen
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    superSqO₂ W hhalf = Submodule.span Complex (superSqO2SqGen W hhalf) := by
  apply le_antisymm
  · rw [superSqO₂, Submodule.span_le]
    rintro _ ⟨a, c, rfl⟩
    have ha : a ∈ Submodule.span Complex {x | IsSqHalfHomogeneous W x} := by
      rw [span_isSqHalfHomogeneous_eq_top W hhalf]
      trivial
    refine Submodule.span_induction
      (p := fun a _ => superSqModeHalf W hhalf (-2) a c ∈
        Submodule.span Complex (superSqO2SqGen W hhalf)) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨p, hap⟩
      have hc : c ∈ Submodule.span Complex {x | IsSqHalfHomogeneous W x} := by
        rw [span_isSqHalfHomogeneous_eq_top W hhalf]
        trivial
      refine Submodule.span_induction
        (p := fun c _ => superSqModeHalf W hhalf (-2) a c ∈
          Submodule.span Complex (superSqO2SqGen W hhalf)) ?_ ?_ ?_ ?_ hc
      · rintro c ⟨q, hcq⟩
        exact Submodule.subset_span ⟨p, q, a, c, hap, hcq, rfl⟩
      · simp
      · intro x y _ _ hx hy
        rw [map_add]
        exact (Submodule.span Complex (superSqO2SqGen W hhalf)).add_mem hx hy
      · intro z x _ hx
        rw [map_smul]
        exact (Submodule.span Complex (superSqO2SqGen W hhalf)).smul_mem z hx
    · simp
    · intro x y _ _ hx hy
      rw [map_add, LinearMap.add_apply]
      exact (Submodule.span Complex (superSqO2SqGen W hhalf)).add_mem hx hy
    · intro z x _ hx
      rw [map_smul, LinearMap.smul_apply]
      exact (Submodule.span Complex (superSqO2SqGen W hhalf)).smul_mem z hx
  · rw [Submodule.span_le]
    rintro _ ⟨p, q, a, c, ha, hc, rfl⟩
    exact Submodule.subset_span ⟨a, c, rfl⟩

/-- A square-bihomogeneous `[-2]` generator has doubled square degree `p+q+2`. -/
theorem superSqO2SqGen_mem_superSqWeightSpace
    (hhalf : IsHalfIntegerGraded W) {p q : Nat} {a c : VType}
    (ha : a ∈ W.toSuperNearVOA.superSqWeightSpace ((p : Complex) / 2))
    (hc : c ∈ W.toSuperNearVOA.superSqWeightSpace ((q : Complex) / 2)) :
    superSqModeHalf W hhalf (-2) a c ∈
      W.toSuperNearVOA.superSqWeightSpace (((p + q + 2 : Nat) : Complex) / 2) := by
  convert superSqModeHalf_mem_superSqWeightSpace W hhalf ha hc (-2) using 1
  push_cast
  ring

/-- Square-weight projection preserves the coordinate-changed square-C2 carrier. -/
theorem superSqC2ProjectionStable
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (d : Nat) {x : VType} (hx : x ∈ superSqO₂ W hhalf) :
    letI := superSqWeightDecomposition W hhalf
    homogProj W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2) x ∈
      superSqO₂ W hhalf := by
  letI := superSqWeightDecomposition W hhalf
  rw [superSqO₂_eq_span_sqGen W hhalf] at hx ⊢
  refine Submodule.span_induction
    (p := fun x _ => homogProj W.toSuperNearVOA.superSqWeightSpace
      ((d : Complex) / 2) x ∈ Submodule.span Complex (superSqO2SqGen W hhalf))
      ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, q, a, c, ha, hc, rfl⟩
    have hwt := superSqO2SqGen_mem_superSqWeightSpace hhalf ha hc
    by_cases hpqd : p + q + 2 = d
    · subst d
      rw [homogProj_of_mem W.toSuperNearVOA.superSqWeightSpace hwt]
      exact Submodule.subset_span ⟨p, q, a, c, ha, hc, rfl⟩
    · have hne : (((p + q + 2 : Nat) : Complex) / 2) ≠ (d : Complex) / 2 := by
        intro h
        have hcasteq : ((p + q + 2 : Nat) : Complex) = (d : Complex) :=
          (div_left_inj' (by norm_num : (2 : Complex) ≠ 0)).mp h
        exact hpqd (by exact_mod_cast hcasteq)
      rw [homogProj_of_mem_ne W.toSuperNearVOA.superSqWeightSpace hne hwt]
      exact (Submodule.span Complex (superSqO2SqGen W hhalf)).zero_mem
  · simp
  · intro a c _ _ ha hc
    rw [map_add]
    exact (Submodule.span Complex (superSqO2SqGen W hhalf)).add_mem ha hc
  · intro z a _ ha
    rw [map_smul]
    exact (Submodule.span Complex (superSqO2SqGen W hhalf)).smul_mem z ha

/-- Inner-sector and square-bihomogeneous global `[-2]` generators. -/
def superSqO2SpinSqGen (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W) : Set VType :=
  {x | exists (label : SpinPair) (p q : Nat) (a c : VType),
    a ∈ b.spinEigenspace label ∧
    a ∈ W.toSuperNearVOA.superSqWeightSpace ((p : Complex) / 2) ∧
    c ∈ W.toSuperNearVOA.superSqWeightSpace ((q : Complex) / 2) ∧
    x = superSqModeHalf W hhalf (-2) a c}

/-- For an involutive fixed outer pair, the square-C2 carrier is spanned by inner-sector and
square-bihomogeneous generators. -/
theorem superSqO₂_eq_span_spinSqGen
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1) :
    superSqO₂ W hhalf =
      Submodule.span Complex (superSqO2SpinSqGen W hhalf b) := by
  apply le_antisymm
  · rw [superSqO₂, Submodule.span_le]
    rintro _ ⟨a, c, rfl⟩
    have ha : a ∈ Submodule.span Complex
        {x | BoundaryPair.IsSpinSqHalfHomogeneous b x} := by
      rw [BoundaryPair.span_isSpinSqHalfHomogeneous_eq_top
        b hhalf hspatial htemporal]
      trivial
    refine Submodule.span_induction
      (p := fun a _ => superSqModeHalf W hhalf (-2) a c ∈
        Submodule.span Complex (superSqO2SpinSqGen W hhalf b)) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨label, p, hsec, hap⟩
      have hc : c ∈ Submodule.span Complex {x | IsSqHalfHomogeneous W x} := by
        rw [span_isSqHalfHomogeneous_eq_top W hhalf]
        trivial
      refine Submodule.span_induction
        (p := fun c _ => superSqModeHalf W hhalf (-2) a c ∈
          Submodule.span Complex (superSqO2SpinSqGen W hhalf b)) ?_ ?_ ?_ ?_ hc
      · rintro c ⟨q, hcq⟩
        exact Submodule.subset_span ⟨label, p, q, a, c, hsec, hap, hcq, rfl⟩
      · simp
      · intro x y _ _ hx hy
        rw [map_add]
        exact (Submodule.span Complex (superSqO2SpinSqGen W hhalf b)).add_mem hx hy
      · intro z x _ hx
        rw [map_smul]
        exact (Submodule.span Complex (superSqO2SpinSqGen W hhalf b)).smul_mem z hx
    · simp
    · intro x y _ _ hx hy
      rw [map_add, LinearMap.add_apply]
      exact (Submodule.span Complex (superSqO2SpinSqGen W hhalf b)).add_mem hx hy
    · intro z x _ hx
      rw [map_smul, LinearMap.smul_apply]
      exact (Submodule.span Complex (superSqO2SpinSqGen W hhalf b)).smul_mem z hx
  · rw [Submodule.span_le]
    rintro _ ⟨label, p, q, a, c, hsec, ha, hc, rfl⟩
    exact Submodule.subset_span ⟨a, c, rfl⟩

/-- Exact doubled square-degree, inner-sector bihomogeneous global `[-2]` generators. -/
def superSqO2SpinSqGenDeg (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W) (n : Nat) : Set VType :=
  {x | exists (label : SpinPair) (p q : Nat) (a c : VType),
    a ∈ b.spinEigenspace label ∧
    a ∈ W.toSuperNearVOA.superSqWeightSpace ((p : Complex) / 2) ∧
    c ∈ W.toSuperNearVOA.superSqWeightSpace ((q : Complex) / 2) ∧
    p + q + 2 = n ∧ x = superSqModeHalf W hhalf (-2) a c}

/-- For an involutive fixed outer pair, an exact square-weight piece of square C2 is spanned by
inner-sector and square-bihomogeneous global `[-2]` generators of that exact doubled degree. -/
theorem superSqC2ExactDegreeSpanning
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (n : Nat) :
    superSqO₂ W hhalf ⊓ W.toSuperNearVOA.superSqWeightSpace ((n : Complex) / 2) <=
      Submodule.span Complex (superSqO2SpinSqGenDeg W hhalf b n) := by
  letI := superSqWeightDecomposition W hhalf
  intro x hx
  obtain ⟨hxO, hxwt⟩ := hx
  rw [superSqO₂_eq_span_spinSqGen hhalf b hspatial htemporal] at hxO
  rw [← homogProj_of_mem W.toSuperNearVOA.superSqWeightSpace hxwt]
  refine Submodule.span_induction
    (p := fun x _ => homogProj W.toSuperNearVOA.superSqWeightSpace
      ((n : Complex) / 2) x ∈
        Submodule.span Complex (superSqO2SpinSqGenDeg W hhalf b n))
      ?_ ?_ ?_ ?_ hxO
  · rintro _ ⟨label, p, q, a, c, hsec, ha, hc, rfl⟩
    have hwt := superSqO2SqGen_mem_superSqWeightSpace hhalf ha hc
    by_cases hpqn : p + q + 2 = n
    · rw [homogProj_of_mem W.toSuperNearVOA.superSqWeightSpace (hpqn ▸ hwt)]
      exact Submodule.subset_span ⟨label, p, q, a, c, hsec, ha, hc, hpqn, rfl⟩
    · have hne : (((p + q + 2 : Nat) : Complex) / 2) ≠ (n : Complex) / 2 := by
        intro h
        have hcasteq : ((p + q + 2 : Nat) : Complex) = (n : Complex) :=
          (div_left_inj' (by norm_num : (2 : Complex) ≠ 0)).mp h
        exact hpqn (by exact_mod_cast hcasteq)
      rw [homogProj_of_mem_ne W.toSuperNearVOA.superSqWeightSpace hne hwt]
      exact (Submodule.span Complex (superSqO2SpinSqGenDeg W hhalf b n)).zero_mem
  · simp
  · intro a c _ _ ha hc
    rw [map_add]
    exact (Submodule.span Complex (superSqO2SpinSqGenDeg W hhalf b n)).add_mem ha hc
  · intro z a _ ha
    rw [map_smul]
    exact (Submodule.span Complex (superSqO2SpinSqGenDeg W hhalf b n)).smul_mem z ha

/-! ## Ordinary-C2 to square-C2 triangular transfer -/

/-- Original doubled-weight homogeneous vectors. -/
def IsHalfHomogeneous (W : SuperVertexOperatorAlgebra VType) (x : VType) : Prop :=
  exists p : Int, x ∈ W.toSuperNearVOA.halfGrading p

/-- Original doubled-weight homogeneous vectors span. -/
theorem span_isHalfHomogeneous_eq_top
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    Submodule.span Complex {x | IsHalfHomogeneous W x} = ⊤ := by
  rw [eq_top_iff, ← iSup_halfGrading_eq_top W hhalf]
  exact iSup_le fun p x hx => Submodule.subset_span ⟨p, hx⟩

/-- Original-mode C2 generators homogeneous for the doubled ordinary grading. -/
def superO2HalfGen (W : SuperVertexOperatorAlgebra VType) : Set VType :=
  {x | exists (p q : Int) (a c : VType),
    a ∈ W.toSuperNearVOA.halfGrading p ∧
    c ∈ W.toSuperNearVOA.halfGrading q ∧
    x = W.toSuperNearVOA.smul a (-2) c}

/-- Half-integrality lets both slots of every original C2 generator be made homogeneous. -/
theorem superO₂_eq_span_halfGen
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    superO₂ W = Submodule.span Complex (superO2HalfGen W) := by
  apply le_antisymm
  · rw [superO₂, Submodule.span_le]
    rintro _ ⟨a, c, rfl⟩
    have ha : a ∈ Submodule.span Complex {x | IsHalfHomogeneous W x} := by
      rw [span_isHalfHomogeneous_eq_top W hhalf]
      trivial
    refine Submodule.span_induction
      (p := fun a _ => W.toSuperNearVOA.smul a (-2) c ∈
        Submodule.span Complex (superO2HalfGen W)) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨p, hap⟩
      have hc : c ∈ Submodule.span Complex {x | IsHalfHomogeneous W x} := by
        rw [span_isHalfHomogeneous_eq_top W hhalf]
        trivial
      refine Submodule.span_induction
        (p := fun c _ => W.toSuperNearVOA.smul a (-2) c ∈
          Submodule.span Complex (superO2HalfGen W)) ?_ ?_ ?_ ?_ hc
      · rintro c ⟨q, hcq⟩
        exact Submodule.subset_span ⟨p, q, a, c, hap, hcq, rfl⟩
      · simp
      · intro x y _ _ hx hy
        rw [SuperVertexAlgebra.smul_add_right]
        exact (Submodule.span Complex (superO2HalfGen W)).add_mem hx hy
      · intro z x _ hx
        rw [SuperVertexAlgebra.smul_smul_right]
        exact (Submodule.span Complex (superO2HalfGen W)).smul_mem z hx
    · simp
    · intro x y _ _ hx hy
      rw [SuperVertexAlgebra.smul_add_left]
      exact (Submodule.span Complex (superO2HalfGen W)).add_mem hx hy
    · intro z x _ hx
      rw [SuperVertexAlgebra.smul_smul_left]
      exact (Submodule.span Complex (superO2HalfGen W)).smul_mem z hx
  · rw [Submodule.span_le]
    rintro _ ⟨p, q, a, c, ha, hc, rfl⟩
    exact Submodule.subset_span ⟨a, c, rfl⟩

/-- An original homogeneous C2 generator has doubled ordinary degree `p+q+2`. -/
theorem superO2HalfGen_mem_halfGrading
    {p q : Int} {a c : VType}
    (ha : a ∈ W.toSuperNearVOA.halfGrading p)
    (hc : c ∈ W.toSuperNearVOA.halfGrading q) :
    W.toSuperNearVOA.smul a (-2) c ∈
      W.toSuperNearVOA.halfGrading (p + q + 2) := by
  change W.toSuperNearVOA.smul a (-2) c ∈
    W.toSuperNearVOA.grading (((p + q + 2 : Int) : Complex) / 2)
  convert W.toSuperNearVOA.smul_mem_grading ha hc (-2) using 1
  push_cast
  ring

/-- Exact doubled ordinary-degree C2 generators. -/
def superO2HalfGenDeg (W : SuperVertexOperatorAlgebra VType) (n : Int) : Set VType :=
  {x | exists (p q : Int) (a c : VType),
    a ∈ W.toSuperNearVOA.halfGrading p ∧
    c ∈ W.toSuperNearVOA.halfGrading q ∧
    p + q + 2 = n ∧ x = W.toSuperNearVOA.smul a (-2) c}

/-- Projection to one original doubled degree preserves original C2. -/
theorem homogProj_halfGrading_mem_superO₂
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (n : Int) {x : VType} (hx : x ∈ superO₂ W) :
    letI := halfGradingDecomposition W hhalf
    homogProj W.toSuperNearVOA.halfGrading n x ∈ superO₂ W := by
  letI := halfGradingDecomposition W hhalf
  rw [superO₂_eq_span_halfGen W hhalf] at hx ⊢
  refine Submodule.span_induction
    (p := fun x _ => homogProj W.toSuperNearVOA.halfGrading n x ∈
      Submodule.span Complex (superO2HalfGen W)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨p, q, a, c, ha, hc, rfl⟩
    have hwt := superO2HalfGen_mem_halfGrading ha hc
    by_cases hpqn : p + q + 2 = n
    · rw [homogProj_of_mem W.toSuperNearVOA.halfGrading (hpqn ▸ hwt)]
      exact Submodule.subset_span ⟨p, q, a, c, ha, hc, rfl⟩
    · rw [homogProj_of_mem_ne W.toSuperNearVOA.halfGrading hpqn hwt]
      exact (Submodule.span Complex (superO2HalfGen W)).zero_mem
  · simp
  · intro a c _ _ ha hc
    rw [map_add]
    exact (Submodule.span Complex (superO2HalfGen W)).add_mem ha hc
  · intro z a _ ha
    rw [map_smul]
    exact (Submodule.span Complex (superO2HalfGen W)).smul_mem z ha

/-- The exact original doubled-degree piece of C2 is spanned by exact homogeneous generators. -/
theorem superO₂_inf_halfGrading_le_span_deg
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) (n : Int) :
    superO₂ W ⊓ W.toSuperNearVOA.halfGrading n <=
      Submodule.span Complex (superO2HalfGenDeg W n) := by
  letI := halfGradingDecomposition W hhalf
  intro x hx
  obtain ⟨hxO, hxwt⟩ := hx
  rw [superO₂_eq_span_halfGen W hhalf] at hxO
  rw [← homogProj_of_mem W.toSuperNearVOA.halfGrading hxwt]
  refine Submodule.span_induction
    (p := fun x _ => homogProj W.toSuperNearVOA.halfGrading n x ∈
      Submodule.span Complex (superO2HalfGenDeg W n)) ?_ ?_ ?_ ?_ hxO
  · rintro _ ⟨p, q, a, c, ha, hc, rfl⟩
    have hwt := superO2HalfGen_mem_halfGrading ha hc
    by_cases hpqn : p + q + 2 = n
    · rw [homogProj_of_mem W.toSuperNearVOA.halfGrading (hpqn ▸ hwt)]
      exact Submodule.subset_span ⟨p, q, a, c, ha, hc, hpqn, rfl⟩
    · rw [homogProj_of_mem_ne W.toSuperNearVOA.halfGrading hpqn hwt]
      exact (Submodule.span Complex (superO2HalfGenDeg W n)).zero_mem
  · simp
  · intro a c _ _ ha hc
    rw [map_add]
    exact (Submodule.span Complex (superO2HalfGenDeg W n)).add_mem ha hc
  · intro z a _ ha
    rw [map_smul]
    exact (Submodule.span Complex (superO2HalfGenDeg W n)).smul_mem z ha

/-- Project a homogeneous `span S + C2` decomposition into an exact original doubled degree. -/
theorem halfGrading_le_span_sup_superO₂_inf
    (hhalf : IsHalfIntegerGraded W) (S : Set VType)
    (hShom : ∀ s ∈ S, IsHalfHomogeneous W s)
    (htop : (⊤ : Submodule Complex VType) =
      Submodule.span Complex S ⊔ superO₂ W) (n : Int) :
    W.toSuperNearVOA.halfGrading n <= Submodule.span Complex S ⊔
      (superO₂ W ⊓ W.toSuperNearVOA.halfGrading n) := by
  letI := halfGradingDecomposition W hhalf
  intro x hx
  have hxtop : x ∈ Submodule.span Complex S ⊔ superO₂ W := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hxtop
  have hpx : homogProj W.toSuperNearVOA.halfGrading n x = x :=
    homogProj_of_mem W.toSuperNearVOA.halfGrading hx
  rw [← hac, map_add] at hpx
  have hpa : homogProj W.toSuperNearVOA.halfGrading n a ∈
      Submodule.span Complex S := by
    refine Submodule.span_induction
      (p := fun a _ => homogProj W.toSuperNearVOA.halfGrading n a ∈
        Submodule.span Complex S) ?_ ?_ ?_ ?_ ha
    · intro s hs
      obtain ⟨p, hsp⟩ := hShom s hs
      by_cases hpn : p = n
      · subst n
        rw [homogProj_of_mem W.toSuperNearVOA.halfGrading hsp]
        exact Submodule.subset_span hs
      · rw [homogProj_of_mem_ne W.toSuperNearVOA.halfGrading hpn hsp]
        exact (Submodule.span Complex S).zero_mem
    · simp
    · intro y z _ _ hy hz
      rw [map_add]
      exact (Submodule.span Complex S).add_mem hy hz
    · intro z y _ hy
      rw [map_smul]
      exact (Submodule.span Complex S).smul_mem z hy
  have hpcO := homogProj_halfGrading_mem_superO₂ W hhalf n hc
  have hpcW := homogProj_mem W.toSuperNearVOA.halfGrading n c
  rw [← hac, ← hpx]
  exact Submodule.add_mem_sup hpa ⟨hpcO, hpcW⟩

/-- The correction after removing the leading ordinary `[-2]` mode from a declared half-weight
square product. -/
noncomputable def superSqHalfDefect
    (W : SuperVertexOperatorAlgebra VType) (a : VType) (p : Int) (c : VType) : VType :=
  ∑ᶠ i : Int,
    (if i = -2 then (0 : Complex) else sqBracketCoeffC ((p : Complex) / 2) (-2) i) •
      W.toSuperNearVOA.smul a i c

theorem superSqHalfDefect_support_finite
    (W : SuperVertexOperatorAlgebra VType) (a : VType) (p : Int) (c : VType) :
    (Function.support fun i : Int =>
      (if i = -2 then (0 : Complex) else sqBracketCoeffC ((p : Complex) / 2) (-2) i) •
        W.toSuperNearVOA.smul a i c).Finite := by
  refine Set.Finite.subset
    (W.toSuperNearVOA.superSqModeC_support_finite a ((p : Complex) / 2) (-2) c)
    (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi ⊢
  intro hc
  apply hi
  by_cases h2 : i = -2
  · rw [if_pos h2, zero_smul]
  · rw [if_neg h2, hc]

/-- On an original doubled-weight homogeneous left state, the global square `[-2]` product is
the ordinary `[-2]` product plus a strictly triangular defect. -/
theorem superSqModeHalf_negTwo_eq_of_mem_halfGrading
    (hhalf : IsHalfIntegerGraded W) {p : Int} {a : VType}
    (ha : a ∈ W.toSuperNearVOA.halfGrading p) (c : VType) :
    superSqModeHalf W hhalf (-2) a c =
      W.toSuperNearVOA.smul a (-2) c + superSqHalfDefect W a p c := by
  rw [superSqModeHalf_of_mem_halfGrading W hhalf ha]
  change W.toSuperNearVOA.superVSqC a ((p : Complex) / 2) (-2) c = _
  rw [W.toSuperNearVOA.superVSqC_apply, superSqHalfDefect]
  have hsplit : forall i : Int,
      sqBracketCoeffC ((p : Complex) / 2) (-2) i • W.toSuperNearVOA.smul a i c =
        (if i = -2 then
          sqBracketCoeffC ((p : Complex) / 2) (-2) i • W.toSuperNearVOA.smul a i c
        else 0) +
        (if i = -2 then (0 : Complex)
          else sqBracketCoeffC ((p : Complex) / 2) (-2) i) •
            W.toSuperNearVOA.smul a i c := by
    intro i
    by_cases h2 : i = -2
    · rw [if_pos h2, if_pos h2, zero_smul, add_zero]
    · rw [if_neg h2, if_neg h2, zero_add]
  rw [finsum_congr hsplit]
  have hsingle : (Function.support fun i : Int =>
      if i = -2 then
        sqBracketCoeffC ((p : Complex) / 2) (-2) i • W.toSuperNearVOA.smul a i c
      else 0).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (-2 : Int)) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hne
    exact hi (if_neg hne)
  rw [finsum_add_distrib hsingle (superSqHalfDefect_support_finite W a p c)]
  congr 1
  rw [finsum_eq_single _ (-2 : Int) (fun i hi => if_neg hi), if_pos rfl,
    sqBracketCoeffC_diag, one_smul]

/-- The square `[-2]` defect has strictly lower doubled ordinary degree. -/
theorem superSqHalfDefect_mem_of_lower
    {p q n : Int} {a c : VType}
    (ha : a ∈ W.toSuperNearVOA.halfGrading p)
    (hc : c ∈ W.toSuperNearVOA.halfGrading q)
    (hpq : p + q + 2 = n) (T : Submodule Complex VType)
    (hT : forall d : Int, d < n -> W.toSuperNearVOA.halfGrading d <= T) :
    superSqHalfDefect W a p c ∈ T := by
  rw [superSqHalfDefect]
  refine finsum_mem_submodule_pd _ _ fun i => ?_
  by_cases h2 : i = -2
  · rw [if_pos h2, zero_smul]
    exact T.zero_mem
  rw [if_neg h2]
  rcases lt_or_ge i (-2 : Int) with hi | hi
  · rw [sqBracketCoeffC_of_lt _ hi, zero_smul]
    exact T.zero_mem
  · refine T.smul_mem _ (hT (p + q - 2 * i - 2) (by omega) ?_)
    change W.toSuperNearVOA.smul a i c ∈
      W.toSuperNearVOA.grading (((p + q - 2 * i - 2 : Int) : Complex) / 2)
    convert W.toSuperNearVOA.smul_mem_grading ha hc i using 1
    push_cast
    ring

/-- The square-C2 span replaces original C2 by doubled ordinary-degree triangular induction. -/
theorem halfGrading_le_span_sup_superSqO₂
    (hhalf : IsHalfIntegerGraded W) (S : Set VType)
    (hShom : ∀ s ∈ S, IsHalfHomogeneous W s)
    (htop : (⊤ : Submodule Complex VType) =
      Submodule.span Complex S ⊔ superO₂ W) (n : Int) :
    W.toSuperNearVOA.halfGrading n <=
      Submodule.span Complex S ⊔ superSqO₂ W hhalf := by
  let T : Submodule Complex VType :=
    Submodule.span Complex S ⊔ superSqO₂ W hhalf
  rcases lt_or_ge n 0 with hn | hn
  · intro x hx
    have hfil : x ∈ halfGradeLE W n :=
      mem_halfGradeLE_of_mem_halfGrading W le_rfl hx
    rw [halfGradeLE_eq_bot W hn, Submodule.mem_bot] at hfil
    rw [hfil]
    exact T.zero_mem
  obtain ⟨N, rfl⟩ : exists N : Nat, n = (N : Int) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | h N ih =>
      have hlower : forall d : Int, d < (N : Int) ->
          W.toSuperNearVOA.halfGrading d <= T := by
        intro d hd
        rcases lt_or_ge d 0 with hd0 | hd0
        · intro x hx
          have hfil : x ∈ halfGradeLE W d :=
            mem_halfGradeLE_of_mem_halfGrading W le_rfl hx
          rw [halfGradeLE_eq_bot W hd0, Submodule.mem_bot] at hfil
          rw [hfil]
          exact T.zero_mem
        · obtain ⟨D, rfl⟩ : exists D : Nat, d = (D : Int) := ⟨d.toNat, by omega⟩
          exact ih D (by exact_mod_cast hd) (by exact_mod_cast hd0)
      refine le_trans
        (halfGrading_le_span_sup_superO₂_inf hhalf S hShom htop (N : Int)) ?_
      refine sup_le le_sup_left ?_
      refine le_trans (superO₂_inf_halfGrading_le_span_deg W hhalf (N : Int)) ?_
      rw [Submodule.span_le]
      rintro _ ⟨p, q, a, c, ha, hc, hpq, rfl⟩
      have hsquare := superSqModeHalf_negTwo_eq_of_mem_halfGrading hhalf ha c
      have hordinary : W.toSuperNearVOA.smul a (-2) c =
          superSqModeHalf W hhalf (-2) a c - superSqHalfDefect W a p c := by
        rw [hsquare, add_sub_cancel_right]
      rw [hordinary]
      exact T.sub_mem
        (Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, rfl⟩))
        (superSqHalfDefect_mem_of_lower ha hc hpq T hlower)

/-- A homogeneous family spanning modulo original C2 also spans modulo square C2. -/
theorem span_sup_superSqO₂_eq_top
    (hhalf : IsHalfIntegerGraded W) (S : Set VType)
    (hShom : ∀ s ∈ S, IsHalfHomogeneous W s)
    (htop : (⊤ : Submodule Complex VType) =
      Submodule.span Complex S ⊔ superO₂ W) :
    (⊤ : Submodule Complex VType) =
      Submodule.span Complex S ⊔ superSqO₂ W hhalf := by
  refine le_antisymm ?_ le_top
  rw [← iSup_halfGrading_eq_top W hhalf]
  exact iSup_le fun n => halfGrading_le_span_sup_superSqO₂ hhalf S hShom htop n

/-! ## Local square `[-2]` descent -/

/-- A square mode strictly above index `-2` has strictly lower doubled square weight. -/
theorem superSqModeHalf_mem_of_lower {P Q n : Nat} {a c : VType}
    (hhalf : IsHalfIntegerGraded W)
    (ha : a ∈ W.toSuperNearVOA.superSqWeightSpace ((P : Complex) / 2))
    (hc : c ∈ W.toSuperNearVOA.superSqWeightSpace ((Q : Complex) / 2))
    (hPQ : P + Q + 2 = n) (m : Int) (hm : -2 < m)
    (T : Submodule Complex VType)
    (hT : forall d : Nat, d < n ->
      W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2) <= T) :
    superSqModeHalf W hhalf m a c ∈ T := by
  let z : Int := (P : Int) + (Q : Int) - 2 * m - 2
  have hmode : superSqModeHalf W hhalf m a c ∈
      W.toSuperNearVOA.superSqWeightSpace ((z : Complex) / 2) := by
    convert superSqModeHalf_mem_superSqWeightSpace W hhalf ha hc m using 1
    dsimp only [z]
    push_cast
    ring
  by_cases hz : z < 0
  · rw [superSqWeightSpace_eq_bot_of_neg_halfWeight W hhalf z hz] at hmode
    have hzero : superSqModeHalf W hhalf m a c = 0 :=
      (Submodule.mem_bot Complex).mp hmode
    rw [hzero]
    exact T.zero_mem
  · push Not at hz
    let d : Nat := z.toNat
    have hdz : (d : Int) = z := Int.toNat_of_nonneg hz
    have hdn : d < n := by
      have hPQ' : (P : Int) + (Q : Int) + 2 = (n : Int) := by exact_mod_cast hPQ
      dsimp only [d]
      omega
    apply hT d hdn
    convert hmode using 1
    rw [← hdz]
    norm_num

/-- The invariant inner sector's `wp` relation solves its square `[-2]` product modulo lower
doubled square weights. -/
theorem superSqModeHalf_negTwo_mem_of_lower_pp
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W)
    {P Q n : Nat} {a c : VType}
    (hsec : a ∈ b.spinEigenspace SpinPair.pp)
    (ha : a ∈ W.toSuperNearVOA.superSqWeightSpace ((P : Complex) / 2))
    (hc : c ∈ W.toSuperNearVOA.superSqWeightSpace ((Q : Complex) / 2))
    (hPQ : P + Q + 2 = n) (T : Submodule Complex VType)
    (hrel : superSpinSqCuspRelSpan W hhalf b.spinEigenspace <= T)
    (hT : forall d : Nat, d < n ->
      W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2) <= T) :
    superSqModeHalf W hhalf (-2) a c ∈ T := by
  classical
  obtain ⟨R, hRnat⟩ := superSqModeHalf_nat_eventually_zero W hhalf a c
  have hR : forall r : Nat, R <= r ->
      superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a c = 0 := by
    intro r hr
    have heq : 2 * ((r : Int) + 2) - 2 = ((2 * r + 2 : Nat) : Int) := by
      push_cast
      ring
    rw [heq]
    exact hRnat (2 * r + 2) (by omega)
  let tail : VType := ∑ r ∈ Finset.range R,
    (((2 * (r + 2) - 1 : Nat) : Complex) *
      spinQCusp SpinPair.pp (2 * (r + 2) - 1)) •
        superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a c
  have hgen : superSqModeHalf W hhalf (-2) a c + tail ∈
      superSpinSqCuspRelSpan W hhalf b.spinEigenspace := by
    apply Submodule.subset_span
    exact Or.inl (Or.inl (Or.inr
      ⟨(P : Complex) / 2, R, a, c, hsec, ha, hR, rfl⟩))
  have htail : tail ∈ T := by
    rw [show tail = ∑ r ∈ Finset.range R,
      (((2 * (r + 2) - 1 : Nat) : Complex) *
        spinQCusp SpinPair.pp (2 * (r + 2) - 1)) •
          superSqModeHalf W hhalf (2 * ((r : Int) + 2) - 2) a c from rfl]
    refine T.sum_mem fun r _ => T.smul_mem _ ?_
    exact superSqModeHalf_mem_of_lower hhalf ha hc hPQ
      (2 * ((r : Int) + 2) - 2) (by omega) T hT
  have hmem := hrel hgen
  rw [show superSqModeHalf W hhalf (-2) a c =
      (superSqModeHalf W hhalf (-2) a c + tail) - tail by abel]
  exact T.sub_mem hmem htail

/-- In a nontrivial inner sector, state-slot square translation and the `P` relation solve the
square `[-2]` product modulo lower doubled square weights. -/
theorem superSqModeHalf_negTwo_mem_of_lower_nontrivial
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W)
    {label : SpinPair} (hlabel : label ≠ SpinPair.pp)
    {P Q n : Nat} {a c : VType} (hsec : a ∈ b.spinEigenspace label)
    (ha : a ∈ W.toSuperNearVOA.superSqWeightSpace ((P : Complex) / 2))
    (hc : c ∈ W.toSuperNearVOA.superSqWeightSpace ((Q : Complex) / 2))
    (hPQ : P + Q + 2 = n) (T : Submodule Complex VType)
    (hrel : superSpinSqCuspRelSpan W hhalf b.spinEigenspace <= T)
    (hT : forall d : Nat, d < n ->
      W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2) <= T) :
    superSqModeHalf W hhalf (-2) a c ∈ T := by
  classical
  let Da : VType := W.toSuperNearVOA.superLsq (-1) a
  have hDsec : Da ∈ b.spinEigenspace label :=
    BoundaryPair.superLsq_mem_spinEigenspace b hsec (-1)
  have hDwt : Da ∈
      W.toSuperNearVOA.superSqWeightSpace (((P + 2 : Nat) : Complex) / 2) := by
    have h := W.toSuperNearVOA.superLsq_neg_one_mem_superSqWeightSpace ha
    convert h using 1
    push_cast
    ring
  obtain ⟨R, hR⟩ := superSqModeHalf_nat_eventually_zero W hhalf Da c
  let tail : VType := ∑ k ∈ Finset.range R,
    spinQCusp label k • superSqModeHalf W hhalf (k : Int) Da c
  have hgen : -superSqModeHalf W hhalf (-1) Da c + tail ∈
      superSpinSqCuspRelSpan W hhalf b.spinEigenspace := by
    apply Submodule.subset_span
    exact Or.inr
      ⟨label, ((P + 2 : Nat) : Complex) / 2, R, Da, c,
        hlabel, hDsec, hDwt, hR, rfl⟩
  have htail : tail ∈ T := by
    rw [show tail = ∑ k ∈ Finset.range R,
      spinQCusp label k • superSqModeHalf W hhalf (k : Int) Da c from rfl]
    refine T.sum_mem fun k _ => ?_
    change spinQCusp label k •
      superSqModeHalf W hhalf (k : Int)
        (W.toSuperNearVOA.superLsq (-1) a) c ∈ T
    rw [superSqModeHalf_superLsq_neg_one W hhalf a (k : Int) c]
    by_cases hk : k = 0
    · subst k
      norm_num
    · exact T.smul_mem _ (T.smul_mem _
        (superSqModeHalf_mem_of_lower hhalf ha hc hPQ ((k : Int) - 1)
          (by omega) T hT))
  have hlead : superSqModeHalf W hhalf (-1) Da c =
      superSqModeHalf W hhalf (-2) a c := by
    change superSqModeHalf W hhalf (-1)
      (W.toSuperNearVOA.superLsq (-1) a) c = _
    rw [superSqModeHalf_superLsq_neg_one W hhalf a (-1) c]
    norm_num
  have hmem : -superSqModeHalf W hhalf (-2) a c + tail ∈ T := by
    rw [← hlead]
    exact hrel hgen
  rw [show superSqModeHalf W hhalf (-2) a c =
      tail - (-superSqModeHalf W hhalf (-2) a c + tail) by abel]
  exact T.sub_mem htail hmem

/-- Uniform local square `[-2]` descent after splitting on the inner `SpinPair` label. -/
theorem superSqModeHalf_negTwo_mem_of_lower
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W)
    {label : SpinPair} {P Q n : Nat} {a c : VType}
    (hsec : a ∈ b.spinEigenspace label)
    (ha : a ∈ W.toSuperNearVOA.superSqWeightSpace ((P : Complex) / 2))
    (hc : c ∈ W.toSuperNearVOA.superSqWeightSpace ((Q : Complex) / 2))
    (hPQ : P + Q + 2 = n) (T : Submodule Complex VType)
    (hrel : superSpinSqCuspRelSpan W hhalf b.spinEigenspace <= T)
    (hT : forall d : Nat, d < n ->
      W.toSuperNearVOA.superSqWeightSpace ((d : Complex) / 2) <= T) :
    superSqModeHalf W hhalf (-2) a c ∈ T := by
  by_cases hp : label = SpinPair.pp
  · subst label
    exact superSqModeHalf_negTwo_mem_of_lower_pp hhalf b hsec ha hc hPQ T hrel hT
  · exact superSqModeHalf_negTwo_mem_of_lower_nontrivial
      hhalf b hp hsec ha hc hPQ T hrel hT

/-! ## Finite simultaneous-homogeneous lifts -/

/-- A finite-dimensional quotient admits finitely many lifts spanning modulo its kernel. -/
theorem exists_finset_span_sup_of_quot_finite_superSq
    (P : Submodule Complex VType) (hfin : FiniteDimensional Complex (VType ⧸ P)) :
    exists T : Finset VType,
      (⊤ : Submodule Complex VType) = Submodule.span Complex (T : Set VType) ⊔ P := by
  classical
  have hfin' : Module.Finite Complex (VType ⧸ P) := hfin
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfin'
  have hsurj : Function.Surjective P.mkQ := Submodule.mkQ_surjective P
  have hlift : forall a : VType ⧸ P, P.mkQ (Function.surjInv hsurj a) = a :=
    fun a => Function.surjInv_eq hsurj a
  refine ⟨S.image (Function.surjInv hsurj), le_antisymm ?_ le_top⟩
  intro x _
  have hle : Submodule.span Complex (S : Set (VType ⧸ P)) <=
      Submodule.map P.mkQ
        (Submodule.span Complex
          ((S.image (Function.surjInv hsurj) : Finset VType) : Set VType)) := by
    rw [Submodule.span_le]
    intro a ha
    exact ⟨Function.surjInv hsurj a, Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp ha))), hlift a⟩
  have hxs : P.mkQ x ∈ Submodule.span Complex (S : Set (VType ⧸ P)) := by
    rw [hS]
    trivial
  obtain ⟨y, hy, hyx⟩ := hle hxs
  have hker : x - y ∈ LinearMap.ker P.mkQ := by
    simp only [LinearMap.mem_ker, map_sub, hyx, sub_self]
  rw [Submodule.ker_mkQ] at hker
  rw [show x = y + (x - y) by abel]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hy) (Submodule.mem_sup_right hker)

/-- Super-C2 cofiniteness supplies finitely many original doubled-weight homogeneous lifts. -/
theorem exists_finset_halfHomogeneous_span_sup_superO₂
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (hC2 : SuperC2Cofinite W) :
    exists T : Finset VType,
      (∀ x ∈ (T : Set VType), IsHalfHomogeneous W x) ∧
      (⊤ : Submodule Complex VType) =
        Submodule.span Complex (T : Set VType) ⊔ superO₂ W := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_span_sup_of_quot_finite_superSq (superO₂ W) hC2
  have hall : forall y : VType, exists F : Finset VType,
      (F : Set VType) ⊆ {x | IsHalfHomogeneous W x} ∧
        y ∈ Submodule.span Complex (F : Set VType) := by
    intro y
    have hy : y ∈ Submodule.span Complex {x | IsHalfHomogeneous W x} := by
      rw [span_isHalfHomogeneous_eq_top W hhalf]
      trivial
    exact Submodule.mem_span_finite_of_mem_span hy
  choose F hFsub hFmem using hall
  let U : Finset VType := T.biUnion F
  have hUhom : ∀ x ∈ (U : Set VType), IsHalfHomogeneous W x := by
    intro x hx
    rw [show U = T.biUnion F from rfl, Finset.mem_coe, Finset.mem_biUnion] at hx
    obtain ⟨y, _, hxy⟩ := hx
    exact hFsub y (Finset.mem_coe.mpr hxy)
  have hTU : (T : Set VType) ⊆
      (Submodule.span Complex (U : Set VType) : Set VType) := by
    intro y hy
    refine Submodule.span_mono ?_ (hFmem y)
    intro z hz
    exact Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨y, Finset.mem_coe.mp hy, Finset.mem_coe.mp hz⟩)
  refine ⟨U, hUhom, le_antisymm ?_ le_top⟩
  rw [hT]
  exact sup_le_sup_right (Submodule.span_le.mpr hTU) _

/-- Ordinary super-C2 cofiniteness implies finite-dimensionality of the global square-C2
quotient, by the doubled ordinary-weight triangular transfer. -/
theorem finiteDimensional_superSqO₂Quotient_of_superC2
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (hC2 : SuperC2Cofinite W) :
    FiniteDimensional Complex (VType ⧸ superSqO₂ W hhalf) := by
  obtain ⟨T, hThom, hT⟩ :=
    exists_finset_halfHomogeneous_span_sup_superO₂ W hhalf hC2
  have hTsq : (⊤ : Submodule Complex VType) =
      Submodule.span Complex (T : Set VType) ⊔ superSqO₂ W hhalf :=
    span_sup_superSqO₂_eq_top hhalf (T : Set VType) hThom hT
  exact (finiteDimensional_and_finrank_quot_le_of_span_sup T hTsq).1

/-- Finite-dimensional square C2 supplies finite lifts homogeneous for both the fixed outer
pair's inner spin labels and the doubled square-weight grading. -/
theorem BoundaryPair.exists_finset_spinSqHomogeneous_span_sup_superSqO2
    (b : BoundaryPair W) (hhalf : IsHalfIntegerGraded W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (hSqC2 : FiniteDimensional Complex (VType ⧸ superSqO₂ W hhalf)) :
    exists T : Finset VType,
      (∀ x ∈ (T : Set VType), BoundaryPair.IsSpinSqHalfHomogeneous b x) ∧
      (⊤ : Submodule Complex VType) =
        Submodule.span Complex (T : Set VType) ⊔ superSqO₂ W hhalf := by
  classical
  obtain ⟨T, hT⟩ :=
    exists_finset_span_sup_of_quot_finite_superSq (superSqO₂ W hhalf) hSqC2
  have hall : forall y : VType, exists F : Finset VType,
      (F : Set VType) ⊆ {x | BoundaryPair.IsSpinSqHalfHomogeneous b x} ∧
        y ∈ Submodule.span Complex (F : Set VType) := by
    intro y
    have hy : y ∈ Submodule.span Complex
        {x | BoundaryPair.IsSpinSqHalfHomogeneous b x} := by
      rw [BoundaryPair.span_isSpinSqHalfHomogeneous_eq_top
        b hhalf hspatial htemporal]
      trivial
    exact Submodule.mem_span_finite_of_mem_span hy
  choose F hFsub hFmem using hall
  let U : Finset VType := T.biUnion F
  have hUhom : ∀ x ∈ (U : Set VType), BoundaryPair.IsSpinSqHalfHomogeneous b x := by
    intro x hx
    rw [show U = T.biUnion F from rfl, Finset.mem_coe, Finset.mem_biUnion] at hx
    obtain ⟨y, _, hxy⟩ := hx
    exact hFsub y (Finset.mem_coe.mpr hxy)
  have hTU : (T : Set VType) ⊆
      (Submodule.span Complex (U : Set VType) : Set VType) := by
    intro y hy
    refine Submodule.span_mono ?_ (hFmem y)
    intro z hz
    exact Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨y, Finset.mem_coe.mp hy, Finset.mem_coe.mp hz⟩)
  refine ⟨U, hUhom, le_antisymm ?_ le_top⟩
  rw [hT]
  exact sup_le_sup_right (Submodule.span_le.mpr hTU) _

/-! ## Projected C2 decomposition and doubled-degree induction -/

/-- Square projection preserves the span of a square-homogeneous family. -/
theorem homogProj_superSqWeightSpace_maps_span_spinSqHomogeneous
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W) (S : Set VType)
    (hShom : ∀ s ∈ S, BoundaryPair.IsSpinSqHalfHomogeneous b s)
    (n : Nat) {x : VType} (hx : x ∈ Submodule.span Complex S) :
    letI := superSqWeightDecomposition W hhalf
    homogProj W.toSuperNearVOA.superSqWeightSpace ((n : Complex) / 2) x ∈
      Submodule.span Complex S := by
  letI := superSqWeightDecomposition W hhalf
  refine Submodule.span_induction
    (p := fun x _ => homogProj W.toSuperNearVOA.superSqWeightSpace
      ((n : Complex) / 2) x ∈ Submodule.span Complex S) ?_ ?_ ?_ ?_ hx
  · intro s hs
    obtain ⟨label, d, -, hwt⟩ := hShom s hs
    by_cases hdn : d = n
    · subst d
      rw [homogProj_of_mem W.toSuperNearVOA.superSqWeightSpace hwt]
      exact Submodule.subset_span hs
    · have hweight : (d : Complex) / 2 ≠ (n : Complex) / 2 := by
        intro h
        have hcast : (d : Complex) = (n : Complex) :=
          (div_left_inj' (by norm_num : (2 : Complex) ≠ 0)).mp h
        exact hdn (by exact_mod_cast hcast)
      rw [homogProj_of_mem_ne W.toSuperNearVOA.superSqWeightSpace hweight hwt]
      exact (Submodule.span Complex S).zero_mem
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact (Submodule.span Complex S).add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact (Submodule.span Complex S).smul_mem c hx

/-- Project a `span S + square-C2` decomposition into one exact doubled square weight. -/
theorem superSqWeightSpace_le_span_sup_superSqO2_inf
    (hhalf : IsHalfIntegerGraded W)
    (b : BoundaryPair W) (S : Set VType)
    (hShom : ∀ s ∈ S, BoundaryPair.IsSpinSqHalfHomogeneous b s)
    (htop : (⊤ : Submodule Complex VType) =
      Submodule.span Complex S ⊔ superSqO₂ W hhalf) (n : Nat) :
    W.toSuperNearVOA.superSqWeightSpace ((n : Complex) / 2) <=
      Submodule.span Complex S ⊔
        (superSqO₂ W hhalf ⊓
          W.toSuperNearVOA.superSqWeightSpace ((n : Complex) / 2)) := by
  letI := superSqWeightDecomposition W hhalf
  intro x hx
  have hxtop : x ∈ Submodule.span Complex S ⊔ superSqO₂ W hhalf :=
    htop ▸ Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hxtop
  have hpx : homogProj W.toSuperNearVOA.superSqWeightSpace
      ((n : Complex) / 2) x = x :=
    homogProj_of_mem W.toSuperNearVOA.superSqWeightSpace hx
  rw [← hac, map_add] at hpx
  have hpa : homogProj W.toSuperNearVOA.superSqWeightSpace
      ((n : Complex) / 2) a ∈ Submodule.span Complex S :=
    homogProj_superSqWeightSpace_maps_span_spinSqHomogeneous hhalf b S hShom n ha
  have hpcO : homogProj W.toSuperNearVOA.superSqWeightSpace
      ((n : Complex) / 2) c ∈ superSqO₂ W hhalf :=
    superSqC2ProjectionStable W hhalf n hc
  have hpcW : homogProj W.toSuperNearVOA.superSqWeightSpace
      ((n : Complex) / 2) c ∈
        W.toSuperNearVOA.superSqWeightSpace ((n : Complex) / 2) :=
    homogProj_mem W.toSuperNearVOA.superSqWeightSpace _ _
  rw [← hac, ← hpx]
  exact Submodule.add_mem_sup hpa ⟨hpcO, hpcW⟩

/-- Strong doubled square-degree descent from a square-C2 lift family to the square-spin cusp
relations. -/
theorem superSqWeightSpace_le_span_sup_superSpinSqCusp
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (S : Set VType) (hShom : ∀ s ∈ S, BoundaryPair.IsSpinSqHalfHomogeneous b s)
    (htop : (⊤ : Submodule Complex VType) =
      Submodule.span Complex S ⊔ superSqO₂ W hhalf) (n : Nat) :
    W.toSuperNearVOA.superSqWeightSpace ((n : Complex) / 2) <=
      Submodule.span Complex S ⊔
        superSpinSqCuspRelSpan W hhalf b.spinEigenspace := by
  classical
  let T : Submodule Complex VType :=
    Submodule.span Complex S ⊔
      superSpinSqCuspRelSpan W hhalf b.spinEigenspace
  induction n using Nat.strong_induction_on with
  | h n ih =>
      refine le_trans
        (superSqWeightSpace_le_span_sup_superSqO2_inf hhalf b S hShom htop n) ?_
      refine sup_le le_sup_left ?_
      refine le_trans
        (superSqC2ExactDegreeSpanning hhalf b hspatial htemporal n) ?_
      rw [Submodule.span_le]
      rintro _ ⟨label, P, Q, a, c, hsec, ha, hc, hPQ, rfl⟩
      exact superSqModeHalf_negTwo_mem_of_lower hhalf b hsec ha hc hPQ T
        le_sup_right (fun d hd => ih d hd)

/-- A finite square-C2 lift family spans modulo the square-spin cusp relations. -/
theorem span_sup_superSpinSqCusp_eq_top
    (hhalf : IsHalfIntegerGraded W) (b : BoundaryPair W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (S : Set VType) (hShom : ∀ s ∈ S, BoundaryPair.IsSpinSqHalfHomogeneous b s)
    (htop : (⊤ : Submodule Complex VType) =
      Submodule.span Complex S ⊔ superSqO₂ W hhalf) :
    (⊤ : Submodule Complex VType) = Submodule.span Complex S ⊔
      superSpinSqCuspRelSpan W hhalf b.spinEigenspace := by
  refine le_antisymm ?_ le_top
  rw [← iSup_superSqWeightSpace_nat_eq_top W hhalf]
  exact iSup_le fun n =>
    superSqWeightSpace_le_span_sup_superSpinSqCusp hhalf b hspatial htemporal
      S hShom htop n

/-- Finite-dimensional square C2 gives a finite simultaneous homogeneous family spanning modulo
the square-spin cusp relations. -/
theorem BoundaryPair.exists_finset_span_sup_superSpinSqCusp_of_superSqC2
    (b : BoundaryPair W) (hhalf : IsHalfIntegerGraded W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (hSqC2 : FiniteDimensional Complex (VType ⧸ superSqO₂ W hhalf)) :
    exists T : Finset VType,
      (∀ x ∈ (T : Set VType), BoundaryPair.IsSpinSqHalfHomogeneous b x) ∧
      (⊤ : Submodule Complex VType) = Submodule.span Complex (T : Set VType) ⊔
        superSpinSqCuspRelSpan W hhalf b.spinEigenspace := by
  obtain ⟨T, hThom, hT⟩ :=
    BoundaryPair.exists_finset_spinSqHomogeneous_span_sup_superSqO2 b
      hhalf hspatial htemporal hSqC2
  exact ⟨T, hThom,
    span_sup_superSpinSqCusp_eq_top hhalf b hspatial htemporal
      (T : Set VType) hThom hT⟩

/-- The honest finite-dimensional square-spin cusp quotient from finite-dimensional square C2. -/
theorem BoundaryPair.finiteDimensional_superSpinSqCuspQuotient_of_superSqC2
    (b : BoundaryPair W) (hhalf : IsHalfIntegerGraded W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (hSqC2 : FiniteDimensional Complex (VType ⧸ superSqO₂ W hhalf)) :
    FiniteDimensional Complex
      (VType ⧸ superSpinSqCuspRelSpan W hhalf b.spinEigenspace) := by
  obtain ⟨T, -, hT⟩ :=
    BoundaryPair.exists_finset_span_sup_superSpinSqCusp_of_superSqC2 b
      hhalf hspatial htemporal hSqC2
  exact (finiteDimensional_and_finrank_quot_le_of_span_sup T hT).1

/-- Super-C2 cofiniteness gives a finite simultaneous homogeneous family spanning modulo the
square-spin cusp relations, with no additional projection-stability premise. -/
theorem BoundaryPair.exists_finset_span_sup_superSpinSqCusp_of_superC2
    (b : BoundaryPair W) (hhalf : IsHalfIntegerGraded W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (hC2 : SuperC2Cofinite W) :
    exists T : Finset VType,
      (∀ x ∈ (T : Set VType), BoundaryPair.IsSpinSqHalfHomogeneous b x) ∧
      (⊤ : Submodule Complex VType) = Submodule.span Complex (T : Set VType) ⊔
        superSpinSqCuspRelSpan W hhalf b.spinEigenspace := by
  exact BoundaryPair.exists_finset_span_sup_superSpinSqCusp_of_superSqC2 b
    hhalf hspatial htemporal
      (finiteDimensional_superSqO₂Quotient_of_superC2 W hhalf hC2)

/-- Super-C2 cofiniteness implies the honest finite-dimensional square-spin cusp quotient for an
involutive fixed outer boundary pair. -/
theorem BoundaryPair.finiteDimensional_superSpinSqCuspQuotient_of_superC2
    (b : BoundaryPair W) (hhalf : IsHalfIntegerGraded W)
    (hspatial : b.spatial ^ 2 = 1) (htemporal : b.temporal ^ 2 = 1)
    (hC2 : SuperC2Cofinite W) :
    FiniteDimensional Complex
      (VType ⧸ superSpinSqCuspRelSpan W hhalf b.spinEigenspace) :=
  BoundaryPair.finiteDimensional_superSpinSqCuspQuotient_of_superSqC2 b
    hhalf hspatial htemporal
      (finiteDimensional_superSqO₂Quotient_of_superC2 W hhalf hC2)

end SuperNearVOA

end VOA
