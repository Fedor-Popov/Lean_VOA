/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.DirectSum.Algebra
import VOA.Filtered.LiMultiplicativity

/-!
# The external Li associated-graded algebra

This file packages the finite fixed-weight Li layers into the external direct sum indexed by
`ℕ × ℕ`.  The product is induced by the `(-1)`-product constructed in
`Filtered.LiMultiplicativity`.

The direct sum has finite support by construction.  Each homogeneous summand is finite
dimensional, and the summand of bidegree `(p,N)` vanishes when `N < p`.  The resulting
external direct sum is a commutative unital algebra.  Translation shifts bidegree by
`(1,1)` and satisfies the Leibniz rule for this multiplication.
-/

namespace VOA

open scoped DirectSum

universe u

section LiGradedAlgebra

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The external direct sum of the fixed-weight Li layers. -/
abbrev liAssociatedGraded (W : VertexOperatorAlgebra V) : Type u :=
  ⨁ d : ℕ × ℕ, liWeightLayer W d.1 d.2

/-- The class of the vacuum in bidegree `(0,0)`. -/
noncomputable def liWeightLayerVacuum (W : VertexOperatorAlgebra V) :
    liWeightLayer W 0 0 :=
  ((liWeightPiece W 1 0).comap (liWeightPiece W 0 0).subtype).mkQ
    ⟨W.vacuum, by
      rw [liWeightPiece, Submodule.mem_inf]
      exact ⟨by rw [liFiltration_zero_eq_top]; exact Submodule.mem_top,
        W.vacuum_mem_grading_zero⟩⟩

private theorem liWeightLayer_mk_heq_of_indices_eq' (W : VertexOperatorAlgebra V)
    {a b c d : ℕ} (hac : a = c) (hbd : b = d) {z : V}
    (hz : z ∈ liWeightPiece W a b) (hz' : z ∈ liWeightPiece W c d) :
    HEq
      (((liWeightPiece W (a + 1) b).comap (liWeightPiece W a b).subtype).mkQ ⟨z, hz⟩)
      (((liWeightPiece W (c + 1) d).comap (liWeightPiece W c d).subtype).mkQ ⟨z, hz'⟩) := by
  subst c
  subst d
  rfl

private theorem liAssociatedGraded_mkQ_reindex (W : VertexOperatorAlgebra V)
    {a b c d : ℕ} (hac : a = c) (hbd : b = d) {z : V}
    (hz : z ∈ liWeightPiece W a b) (hz' : z ∈ liWeightPiece W c d) :
    DirectSum.of (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) (a, b)
        (((liWeightPiece W (a + 1) b).comap
          (liWeightPiece W a b).subtype).mkQ ⟨z, hz⟩) =
      DirectSum.of (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) (c, d)
        (((liWeightPiece W (c + 1) d).comap
          (liWeightPiece W c d).subtype).mkQ ⟨z, hz'⟩) := by
  apply DirectSum.of_eq_of_gradedMonoid_eq
  exact Sigma.ext (Prod.ext hac hbd)
    (liWeightLayer_mk_heq_of_indices_eq' W hac hbd hz hz')

/-- The vacuum is a left unit on each finite fixed-weight layer. -/
theorem liWeightLayerMul_vacuum_left (W : VertexOperatorAlgebra V) (p N : ℕ)
    (xbar : liWeightLayer W p N) :
    HEq (liWeightLayerMul W 0 p 0 N (liWeightLayerVacuum W) xbar) xbar := by
  refine Submodule.Quotient.induction_on _ xbar fun x => ?_
  change HEq
    (liWeightLayerMul W 0 p 0 N (liWeightLayerVacuum W)
      (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x))
    (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
  rw [liWeightLayerVacuum, liWeightLayerMul_mk]
  simp only [PreVertexAlgebra.smul_vacuum_left, if_pos]
  exact liWeightLayer_mk_heq_of_indices_eq' W (Nat.zero_add p) (Nat.zero_add N) _ _

/-- The vacuum is a right unit on each finite fixed-weight layer. -/
theorem liWeightLayerMul_vacuum_right (W : VertexOperatorAlgebra V) (p N : ℕ)
    (xbar : liWeightLayer W p N) :
    liWeightLayerMul W p 0 N 0 xbar (liWeightLayerVacuum W) = xbar := by
  refine Submodule.Quotient.induction_on _ xbar fun x => ?_
  change
    liWeightLayerMul W p 0 N 0
      (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
      (liWeightLayerVacuum W) =
    (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
  rw [liWeightLayerVacuum, liWeightLayerMul_mk]
  simp only [PreVertexAlgebra.smul_vacuum_neg_one, Nat.add_zero]

/-- Homogeneous multiplication on the family of Li layers. -/
noncomputable instance liWeightLayerGMul (W : VertexOperatorAlgebra V) :
    GradedMonoid.GMul (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) where
  mul {i j} x y := by
    rcases i with ⟨p, N⟩
    rcases j with ⟨q, M⟩
    exact liWeightLayerMul W p q N M x y

/-- The homogeneous unit is the vacuum class in bidegree `(0,0)`. -/
noncomputable instance liWeightLayerGOne (W : VertexOperatorAlgebra V) :
    GradedMonoid.GOne (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) where
  one := liWeightLayerVacuum W

/-- The homogeneous Li layers form a graded commutative ring.  Consequently their external
direct sum acquires an ordinary commutative-ring structure from Mathlib's `DirectSum` API. -/
noncomputable instance liWeightLayerGCommRing (W : VertexOperatorAlgebra V) :
    DirectSum.GCommRing (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) where
  one_mul a := by
    rcases a with ⟨⟨p, N⟩, x⟩
    exact Sigma.ext (Prod.ext (Nat.zero_add p) (Nat.zero_add N))
      (liWeightLayerMul_vacuum_left W p N x)
  mul_one a := by
    rcases a with ⟨⟨p, N⟩, x⟩
    exact Sigma.ext (Prod.ext (Nat.add_zero p) (Nat.add_zero N))
      (heq_of_eq (liWeightLayerMul_vacuum_right W p N x))
  mul_assoc a b c := by
    rcases a with ⟨⟨p, N⟩, x⟩
    rcases b with ⟨⟨q, M⟩, y⟩
    rcases c with ⟨⟨r, K⟩, z⟩
    exact Sigma.ext
      (Prod.ext (Nat.add_assoc p q r) (Nat.add_assoc N M K))
      (liWeightLayerMul_assoc W p q r N M K x y z)
  mul_zero {i j} x := by
    rcases i with ⟨p, N⟩
    rcases j with ⟨q, M⟩
    exact (liWeightLayerMul W p q N M x).map_zero
  zero_mul {i j} y := by
    rcases i with ⟨p, N⟩
    rcases j with ⟨q, M⟩
    exact LinearMap.congr_fun (map_zero (liWeightLayerMul W p q N M)) y
  mul_add {i j} x y z := by
    rcases i with ⟨p, N⟩
    rcases j with ⟨q, M⟩
    exact (liWeightLayerMul W p q N M x).map_add y z
  add_mul {i j} x y z := by
    rcases i with ⟨p, N⟩
    rcases j with ⟨q, M⟩
    exact LinearMap.congr_fun (map_add (liWeightLayerMul W p q N M) x y) z
  mul_comm a b := by
    rcases a with ⟨⟨p, N⟩, x⟩
    rcases b with ⟨⟨q, M⟩, y⟩
    exact Sigma.ext (Prod.ext (Nat.add_comm p q) (Nat.add_comm N M))
      (liWeightLayerMul_comm W p q N M x y)
  natCast n := (n : ℂ) • liWeightLayerVacuum W
  natCast_zero := by simp
  natCast_succ n := by
    change ((n + 1 : ℕ) : ℂ) • liWeightLayerVacuum W =
      (n : ℂ) • liWeightLayerVacuum W + liWeightLayerVacuum W
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  intCast z := (z : ℂ) • liWeightLayerVacuum W
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by
    change ((Int.negSucc n : ℤ) : ℂ) • liWeightLayerVacuum W =
      -(((n + 1 : ℕ) : ℂ) • liWeightLayerVacuum W)
    rw [Int.cast_negSucc, neg_smul]

/-- The scalar action on the graded pieces agrees with multiplication by the scalar multiple of
the vacuum.  Thus the external direct sum is naturally a commutative `ℂ`-algebra. -/
noncomputable instance liWeightLayerGAlgebra (W : VertexOperatorAlgebra V) :
    DirectSum.GAlgebra ℂ (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) where
  toFun :=
    { toFun := fun c => c • liWeightLayerVacuum W
      map_zero' := zero_smul _ _
      map_add' := fun c d => add_smul c d _ }
  map_one := one_smul _ _
  map_mul c d := by
    have hvac : liWeightLayerMul W 0 0 0 0 (liWeightLayerVacuum W)
        (d • liWeightLayerVacuum W) = d • liWeightLayerVacuum W :=
      eq_of_heq (liWeightLayerMul_vacuum_left W 0 0 (d • liWeightLayerVacuum W))
    have hmul : liWeightLayerMul W 0 0 0 0 (c • liWeightLayerVacuum W)
        (d • liWeightLayerVacuum W) = (c * d) • liWeightLayerVacuum W := by
      calc
        liWeightLayerMul W 0 0 0 0 (c • liWeightLayerVacuum W)
            (d • liWeightLayerVacuum W) =
          c • liWeightLayerMul W 0 0 0 0 (liWeightLayerVacuum W)
            (d • liWeightLayerVacuum W) :=
              LinearMap.congr_fun (map_smul (liWeightLayerMul W 0 0 0 0) c
                (liWeightLayerVacuum W)) (d • liWeightLayerVacuum W)
        _ = c • (d • liWeightLayerVacuum W) := congrArg (c • ·) hvac
        _ = (c * d) • liWeightLayerVacuum W := smul_smul c d _
    exact Sigma.ext rfl (heq_of_eq hmul.symm)
  commutes c x := by
    rcases x with ⟨⟨p, N⟩, x⟩
    exact Sigma.ext
      (Prod.ext ((Nat.zero_add p).trans (Nat.add_zero p).symm)
        ((Nat.zero_add N).trans (Nat.add_zero N).symm))
      (liWeightLayerMul_comm W 0 p 0 N (c • liWeightLayerVacuum W) x)
  smul_def c x := by
    rcases x with ⟨⟨p, N⟩, x⟩
    have hright : liWeightLayerMul W p 0 N 0 x (c • liWeightLayerVacuum W) = c • x := by
      calc
        liWeightLayerMul W p 0 N 0 x (c • liWeightLayerVacuum W) =
            c • liWeightLayerMul W p 0 N 0 x (liWeightLayerVacuum W) :=
          (liWeightLayerMul W p 0 N 0 x).map_smul c (liWeightLayerVacuum W)
        _ = c • x := congrArg (c • ·) (liWeightLayerMul_vacuum_right W p N x)
    refine Sigma.ext (Prod.ext (Nat.zero_add p).symm (Nat.zero_add N).symm) ?_
    exact ((liWeightLayerMul_comm W 0 p 0 N (c • liWeightLayerVacuum W) x).trans
      (heq_of_eq hright)).symm

/-- Multiplication of two homogeneous inclusions is the descended `(-1)`-product. -/
@[simp] theorem liAssociatedGraded_of_mul_of (W : VertexOperatorAlgebra V)
    (p q N M : ℕ) (x : liWeightLayer W p N) (y : liWeightLayer W q M) :
    (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) x :
        liAssociatedGraded W) *
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (q, M) y =
    DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p + q, N + M)
      (liWeightLayerMul W p q N M x y) := by
  rw [DirectSum.of_mul_of]
  rfl

/-- The unit of the external associated graded is the homogeneous vacuum class. -/
theorem liAssociatedGraded_one (W : VertexOperatorAlgebra V) :
    (1 : liAssociatedGraded W) =
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (0, 0)
        (liWeightLayerVacuum W) :=
  rfl

/-- The algebra map inserts a scalar multiple of the vacuum in bidegree `(0,0)`. -/
theorem liAssociatedGraded_algebraMap (W : VertexOperatorAlgebra V) (c : ℂ) :
    (@algebraMap ℂ (⨁ d : ℕ × ℕ, liWeightLayer W d.1 d.2) _
      (DirectSum.semiring (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2))
      (DirectSum.instAlgebra ℂ (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2))) c =
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (0, 0)
        (c • liWeightLayerVacuum W) :=
  rfl

/-! ## Translation -/

/-- Translation raises both Li degree and conformal weight by one. -/
theorem liWeightPiece_L_neg_one_mem (W : VertexOperatorAlgebra V)
    {p N : ℕ} {x : V} (hx : x ∈ liWeightPiece W p N) :
    W.L (-1) x ∈ liWeightPiece W (p + 1) (N + 1) := by
  change x ∈ liFiltration W p ⊓ W.grading N at hx
  change W.L (-1) x ∈ liFiltration W (p + 1) ⊓ W.grading (N + 1)
  rw [Submodule.mem_inf] at hx ⊢
  refine ⟨liFiltration_L_neg_one_mem W hx.1, ?_⟩
  have hgr := W.toPreVertexAlgebra.T_mem_grading hx.2
  rw [VertexOperatorAlgebra.T_eq_Lneg1] at hgr
  simpa only [Nat.cast_add, Nat.cast_one] using hgr

/-- Translation on representatives, projected to the target exact Li layer. -/
noncomputable def liWeightPieceTranslation (W : VertexOperatorAlgebra V) (p N : ℕ) :
    liWeightPiece W p N →ₗ[ℂ] liWeightLayer W (p + 1) (N + 1) where
  toFun x :=
    ((liWeightPiece W (p + 1 + 1) (N + 1)).comap
      (liWeightPiece W (p + 1) (N + 1)).subtype).mkQ
        ⟨W.L (-1) x.1, liWeightPiece_L_neg_one_mem W x.property⟩
  map_add' x y := by
    apply congrArg ((liWeightPiece W (p + 1 + 1) (N + 1)).comap
      (liWeightPiece W (p + 1) (N + 1)).subtype).mkQ
    apply Subtype.ext
    exact map_add (W.L (-1)) x.1 y.1
  map_smul' c x := by
    apply congrArg ((liWeightPiece W (p + 1 + 1) (N + 1)).comap
      (liWeightPiece W (p + 1) (N + 1)).subtype).mkQ
    apply Subtype.ext
    exact map_smul (W.L (-1)) c x.1

private theorem liWeightPieceTranslation_ker (W : VertexOperatorAlgebra V) (p N : ℕ) :
    (liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype ≤
      LinearMap.ker (liWeightPieceTranslation W p N) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change W.L (-1) x.1 ∈ liWeightPiece W (p + 1 + 1) (N + 1)
  have hx' : x.1 ∈ liWeightPiece W (p + 1) N := by simpa using hx
  exact liWeightPiece_L_neg_one_mem W hx'

/-- Translation descended to an exact fixed-weight Li layer. -/
noncomputable def liWeightLayerTranslation (W : VertexOperatorAlgebra V) (p N : ℕ) :
    liWeightLayer W p N →ₗ[ℂ] liWeightLayer W (p + 1) (N + 1) :=
  ((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).liftQ
    (liWeightPieceTranslation W p N) (liWeightPieceTranslation_ker W p N)

/-- Evaluation of descended translation on a representative. -/
@[simp] theorem liWeightLayerTranslation_mk (W : VertexOperatorAlgebra V) (p N : ℕ)
    (x : liWeightPiece W p N) :
    liWeightLayerTranslation W p N
      (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x) =
    ((liWeightPiece W (p + 1 + 1) (N + 1)).comap
      (liWeightPiece W (p + 1) (N + 1)).subtype).mkQ
        ⟨W.L (-1) x.1, liWeightPiece_L_neg_one_mem W x.property⟩ :=
  rfl

/-- Translation assembled over all bidegrees of the external Li associated graded. -/
noncomputable def liAssociatedGradedTranslation (W : VertexOperatorAlgebra V) :
    liAssociatedGraded W →ₗ[ℂ] liAssociatedGraded W :=
  DirectSum.toModule ℂ (ℕ × ℕ) (liAssociatedGraded W) fun d => by
    rcases d with ⟨p, N⟩
    exact (DirectSum.lof ℂ (ℕ × ℕ)
      (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p + 1, N + 1)).comp
        (liWeightLayerTranslation W p N)

/-- On a homogeneous inclusion, assembled translation is the inclusion of translated layer. -/
@[simp] theorem liAssociatedGradedTranslation_of (W : VertexOperatorAlgebra V)
    (p N : ℕ) (x : liWeightLayer W p N) :
    liAssociatedGradedTranslation W
        (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) x) =
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p + 1, N + 1)
        (liWeightLayerTranslation W p N x) := by
  rw [liAssociatedGradedTranslation]
  change
    (DirectSum.toModule ℂ (ℕ × ℕ) (liAssociatedGraded W) _)
        (DirectSum.lof ℂ (ℕ × ℕ)
          (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) x) = _
  rw [DirectSum.toModule_lof, LinearMap.comp_apply, DirectSum.lof_eq_of]

private theorem liAssociatedGradedTranslation_mul_of (W : VertexOperatorAlgebra V)
    (p q N M : ℕ) (x : liWeightLayer W p N) (y : liWeightLayer W q M) :
    liAssociatedGradedTranslation W
        ((DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) x :
          liAssociatedGraded W) *
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (q, M) y) =
      liAssociatedGradedTranslation W
          (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) x) *
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (q, M) y +
        DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) x *
          liAssociatedGradedTranslation W
            (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (q, M) y) := by
  rw [DirectSum.of_mul_of]
  change liAssociatedGradedTranslation W
      (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p + q, N + M)
        (liWeightLayerMul W p q N M x y)) = _
  rw [liAssociatedGradedTranslation_of, liAssociatedGradedTranslation_of,
    liAssociatedGradedTranslation_of, DirectSum.of_mul_of, DirectSum.of_mul_of]
  change
    DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p + q + 1, N + M + 1)
        (liWeightLayerTranslation W (p + q) (N + M)
          (liWeightLayerMul W p q N M x y)) =
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + 1 + q, N + 1 + M)
          (liWeightLayerMul W (p + 1) q (N + 1) M
            (liWeightLayerTranslation W p N x) y) +
        DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + (q + 1), N + (M + 1))
          (liWeightLayerMul W p (q + 1) N (M + 1) x
            (liWeightLayerTranslation W q M y))
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  refine Submodule.Quotient.induction_on _ y fun y => ?_
  change
    DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p + q + 1, N + M + 1)
        (liWeightLayerTranslation W (p + q) (N + M)
          (liWeightLayerMul W p q N M
            (((liWeightPiece W (p + 1) N).comap
              (liWeightPiece W p N).subtype).mkQ x)
            (((liWeightPiece W (q + 1) M).comap
              (liWeightPiece W q M).subtype).mkQ y))) =
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + 1 + q, N + 1 + M)
          (liWeightLayerMul W (p + 1) q (N + 1) M
            (liWeightLayerTranslation W p N
              (((liWeightPiece W (p + 1) N).comap
                (liWeightPiece W p N).subtype).mkQ x))
            (((liWeightPiece W (q + 1) M).comap
              (liWeightPiece W q M).subtype).mkQ y)) +
        DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + (q + 1), N + (M + 1))
          (liWeightLayerMul W p (q + 1) N (M + 1)
            (((liWeightPiece W (p + 1) N).comap
              (liWeightPiece W p N).subtype).mkQ x)
            (liWeightLayerTranslation W q M
              (((liWeightPiece W (q + 1) M).comap
                (liWeightPiece W q M).subtype).mkQ y)))
  rw [liWeightLayerMul_mk, liWeightLayerTranslation_mk,
    liWeightLayerTranslation_mk, liWeightLayerMul_mk,
    liWeightLayerTranslation_mk, liWeightLayerMul_mk]
  have hxT := liWeightPiece_L_neg_one_mem W x.property
  have hyT := liWeightPiece_L_neg_one_mem W y.property
  have hprod := liWeightPiece_smul_neg_one_mem W x.property y.property
  have hLprod := liWeightPiece_L_neg_one_mem W hprod
  have hAown := liWeightPiece_smul_neg_one_mem W hxT y.property
  have hBown := liWeightPiece_smul_neg_one_mem W x.property hyT
  have hAcommon : W.smul (W.L (-1) x.1) (-1) y.1 ∈
      liWeightPiece W (p + q + 1) (N + M + 1) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAown
  have hBcommon : W.smul x.1 (-1) (W.L (-1) y.1) ∈
      liWeightPiece W (p + q + 1) (N + M + 1) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBown
  have hderiv : W.L (-1) (W.smul x.1 (-1) y.1) =
      W.smul (W.L (-1) x.1) (-1) y.1 + W.smul x.1 (-1) (W.L (-1) y.1) := by
    have h := W.L_neg_one_deriv x.1 y.1 (-1)
    rw [sub_eq_iff_eq_add] at h
    simpa only [add_comm] using h
  have hLayerCommon :
      ((liWeightPiece W (p + q + 1 + 1) (N + M + 1)).comap
        (liWeightPiece W (p + q + 1) (N + M + 1)).subtype).mkQ
          ⟨W.L (-1) (W.smul x.1 (-1) y.1), hLprod⟩ =
        ((liWeightPiece W (p + q + 1 + 1) (N + M + 1)).comap
          (liWeightPiece W (p + q + 1) (N + M + 1)).subtype).mkQ
            ⟨W.smul (W.L (-1) x.1) (-1) y.1, hAcommon⟩ +
        ((liWeightPiece W (p + q + 1 + 1) (N + M + 1)).comap
          (liWeightPiece W (p + q + 1) (N + M + 1)).subtype).mkQ
            ⟨W.smul x.1 (-1) (W.L (-1) y.1), hBcommon⟩ := by
    rw [← map_add]
    apply congrArg ((liWeightPiece W (p + q + 1 + 1) (N + M + 1)).comap
      (liWeightPiece W (p + q + 1) (N + M + 1)).subtype).mkQ
    exact Subtype.ext hderiv
  change
    DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p + q + 1, N + M + 1)
        (((liWeightPiece W (p + q + 1 + 1) (N + M + 1)).comap
          (liWeightPiece W (p + q + 1) (N + M + 1)).subtype).mkQ
            ⟨W.L (-1) (W.smul x.1 (-1) y.1), hLprod⟩) =
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + 1 + q, N + 1 + M)
          (((liWeightPiece W (p + 1 + q + 1) (N + 1 + M)).comap
            (liWeightPiece W (p + 1 + q) (N + 1 + M)).subtype).mkQ
              ⟨W.smul (W.L (-1) x.1) (-1) y.1, hAown⟩) +
        DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + (q + 1), N + (M + 1))
          (((liWeightPiece W (p + (q + 1) + 1) (N + (M + 1))).comap
            (liWeightPiece W (p + (q + 1)) (N + (M + 1))).subtype).mkQ
              ⟨W.smul x.1 (-1) (W.L (-1) y.1), hBown⟩)
  rw [hLayerCommon, map_add]
  apply congrArg₂ (· + ·)
  · exact liAssociatedGraded_mkQ_reindex W (by omega) (by omega) hAcommon hAown
  · exact liAssociatedGraded_mkQ_reindex W (by omega) (by omega) hBcommon hBown

/-- Translation is a derivation of the associated-graded multiplication. -/
theorem liAssociatedGradedTranslation_leibniz (W : VertexOperatorAlgebra V)
    (a b : liAssociatedGraded W) :
    liAssociatedGradedTranslation W (a * b) =
      liAssociatedGradedTranslation W a * b + a * liAssociatedGradedTranslation W b := by
  change liAssociatedGradedTranslation W
      (DirectSum.mulHom (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) a b) =
    DirectSum.mulHom (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
        (liAssociatedGradedTranslation W a) b +
      DirectSum.mulHom (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) a
        (liAssociatedGradedTranslation W b)
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply, zero_add]
  | of i x =>
      rcases i with ⟨p, N⟩
      induction b using DirectSum.induction_on with
      | zero => simp only [map_zero, zero_add]
      | of j y =>
          rcases j with ⟨q, M⟩
          exact liAssociatedGradedTranslation_mul_of W p q N M x y
      | add b c hb hc =>
          simp only [map_add]
          rw [hb, hc]
          abel
  | add a b ha hb =>
      simp only [map_add, AddMonoidHom.add_apply]
      rw [ha, hb]
      abel

/-- Every homogeneous bidegree of the Li associated graded is finite-dimensional. -/
theorem liAssociatedGraded_component_finiteDimensional (W : VertexOperatorAlgebra V)
    (p N : ℕ) : FiniteDimensional ℂ (liWeightLayer W p N) := by
  letI : FiniteDimensional ℂ (liWeightPiece W p N) :=
    liWeightPiece_finiteDimensional W p N
  infer_instance

/-- The bidegree `(p,N)` component vanishes above the diagonal `p = N`. -/
theorem liAssociatedGraded_component_eq_zero_of_weight_lt_degree
    (W : VertexOperatorAlgebra V) {p N : ℕ} (h : N < p)
    (x : liWeightLayer W p N) : x = 0 := by
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  have hx : (x : V) = 0 := by
    have hle : liWeightPiece W p N ≤ (⊥ : Submodule ℂ V) := by
      rw [liWeightPiece_eq_bot_of_lt W h]
    exact (Submodule.mem_bot ℂ).mp (hle x.property)
  have hxsub : x = 0 := Subtype.ext hx
  rw [hxsub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.zero_mem _

end LiGradedAlgebra

end VOA
