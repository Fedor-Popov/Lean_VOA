import VOA.Filtered.LiGradedAlgebra
import Mathlib.Algebra.Polynomial.Basic

/-!
# Nonnegative vertex modes on Li layers

Each nonnegative vertex mode descends independently of both representatives, with
output bidegree `(p+q-n, N+M-n-1)`. The explicit inequalities keep both target indices
nonnegative. This is the operation-level foundation for the Poisson vertex structure;
its skew-symmetry, Jacobi, and Leibniz identities are not asserted here.
-/

namespace VOA

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A nonnegative vertex mode preserves the predicted Li and conformal degrees. -/
theorem liWeightPiece_smul_nonneg_mem (W : VertexOperatorAlgebra V)
    {p q N M n : ℕ} (hn : n ≤ p + q) (hN : n + 1 ≤ N + M)
    {x y : V} (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) :
    W.smul x (n : ℤ) y ∈ liWeightPiece W (p + q - n) (N + M - (n + 1)) := by
  refine ⟨liFiltration_smul_nonneg_mem W hn hx.1 hy.1, ?_⟩
  have hgr := W.smul_mem_grading hx.2 hy.2 (n : ℤ)
  have heq : ((N + M - (n + 1) : ℕ) : ℤ) = (N : ℤ) + M - n - 1 := by
    rw [Nat.cast_sub hN, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    ring
  simpa only [heq] using hgr

/-- The representative-level nonnegative mode, already projected to the target Li layer. -/
noncomputable def liWeightPieceMode (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M) :
    liWeightPiece W p N →ₗ[ℂ]
      liWeightPiece W q M →ₗ[ℂ] liWeightLayer W (p + q - n) (N + M - (n + 1)) where
  toFun x :=
    { toFun := fun y =>
        ((liWeightPiece W (p + q - n + 1) (N + M - (n + 1))).comap
          (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype).mkQ
            ⟨W.smul x.1 (n : ℤ) y.1,
              liWeightPiece_smul_nonneg_mem W hn hN x.property y.property⟩
      map_add' := fun y₁ y₂ => by
        apply congrArg ((liWeightPiece W (p + q - n + 1) (N + M - (n + 1))).comap
          (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype).mkQ
        ext
        exact W.smul_add_right x.1 (n : ℤ) y₁.1 y₂.1
      map_smul' := fun c y => by
        apply congrArg ((liWeightPiece W (p + q - n + 1) (N + M - (n + 1))).comap
          (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype).mkQ
        ext
        exact W.smul_smul_right x.1 c (n : ℤ) y.1 }
  map_add' x₁ x₂ := by
    refine LinearMap.ext fun y => ?_
    apply congrArg ((liWeightPiece W (p + q - n + 1) (N + M - (n + 1))).comap
      (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype).mkQ
    ext
    exact W.smul_add_left x₁.1 x₂.1 (n : ℤ) y.1
  map_smul' c x := by
    refine LinearMap.ext fun y => ?_
    apply congrArg ((liWeightPiece W (p + q - n + 1) (N + M - (n + 1))).comap
      (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype).mkQ
    ext
    exact W.smul_smul_left c x.1 (n : ℤ) y.1

private theorem liWeightPieceMode_right_ker (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M)
    (x : liWeightPiece W p N) :
    (liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype ≤
      LinearMap.ker (liWeightPieceMode W p q N M n hn hN x) := by
  intro y hy
  rw [LinearMap.mem_ker, liWeightPieceMode]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change W.smul x.1 (n : ℤ) y.1 ∈ liWeightPiece W (p + q - n + 1) (N + M - (n + 1))
  have hy' : y.1 ∈ liWeightPiece W (q + 1) M := by simpa using hy
  have hprod := liWeightPiece_smul_nonneg_mem W (show n ≤ p + (q + 1) by omega) hN x.property hy'
  have heq : p + (q + 1) - n = p + q - n + 1 := by omega
  simpa only [heq] using hprod

/-- For a representative of the first layer, the mode descends through the second layer. -/
noncomputable def liWeightLayerModeRight (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M)
    (x : liWeightPiece W p N) :
    liWeightLayer W q M →ₗ[ℂ] liWeightLayer W (p + q - n) (N + M - (n + 1)) :=
  ((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).liftQ
    (liWeightPieceMode W p q N M n hn hN x) (liWeightPieceMode_right_ker W p q N M n hn hN x)

/-- The partially descended mode is linear in the remaining representative. -/
noncomputable def liWeightLayerModeLeft (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M) :
    liWeightPiece W p N →ₗ[ℂ]
      liWeightLayer W q M →ₗ[ℂ] liWeightLayer W (p + q - n) (N + M - (n + 1)) where
  toFun := liWeightLayerModeRight W p q N M n hn hN
  map_add' x₁ x₂ := by
    refine LinearMap.ext fun ybar => ?_
    refine Submodule.Quotient.induction_on _ ybar fun y => ?_
    change liWeightPieceMode W p q N M n hn hN (x₁ + x₂) y =
      liWeightPieceMode W p q N M n hn hN x₁ y + liWeightPieceMode W p q N M n hn hN x₂ y
    exact LinearMap.congr_fun (map_add (liWeightPieceMode W p q N M n hn hN) x₁ x₂) y
  map_smul' c x := by
    refine LinearMap.ext fun ybar => ?_
    refine Submodule.Quotient.induction_on _ ybar fun y => ?_
    change liWeightPieceMode W p q N M n hn hN (c • x) y =
      c • liWeightPieceMode W p q N M n hn hN x y
    exact LinearMap.congr_fun (map_smul (liWeightPieceMode W p q N M n hn hN) c x) y

private theorem liWeightLayerModeLeft_ker (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M) :
    (liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype ≤
      LinearMap.ker (liWeightLayerModeLeft W p q N M n hn hN) := by
  intro x hx
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun ybar => ?_
  refine Submodule.Quotient.induction_on _ ybar fun y => ?_
  change liWeightPieceMode W p q N M n hn hN x y = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change W.smul x.1 (n : ℤ) y.1 ∈ liWeightPiece W (p + q - n + 1) (N + M - (n + 1))
  have hx' : x.1 ∈ liWeightPiece W (p + 1) N := by simpa using hx
  have hprod := liWeightPiece_smul_nonneg_mem W (show n ≤ (p + 1) + q by omega) hN hx' y.property
  have heq : (p + 1) + q - n = p + q - n + 1 := by omega
  simpa only [heq] using hprod

/-- The nonnegative mode descends to exact Li and conformal bidegree layers. -/
noncomputable def liWeightLayerMode (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M) :
    liWeightLayer W p N →ₗ[ℂ]
      liWeightLayer W q M →ₗ[ℂ] liWeightLayer W (p + q - n) (N + M - (n + 1)) :=
  ((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).liftQ
    (liWeightLayerModeLeft W p q N M n hn hN) (liWeightLayerModeLeft_ker W p q N M n hn hN)

/-- Evaluation of the descended layer mode on representatives. -/
@[simp] theorem liWeightLayerMode_mk (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M)
    (x : liWeightPiece W p N) (y : liWeightPiece W q M) :
    liWeightLayerMode W p q N M n hn hN
        (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
        (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y) =
      ((liWeightPiece W (p + q - n + 1) (N + M - (n + 1))).comap
        (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype).mkQ
          ⟨W.smul x.1 (n : ℤ) y.1,
            liWeightPiece_smul_nonneg_mem W hn hN x.property y.property⟩ := by
  rfl


/-- A homogeneous mode as a map into the total associated graded, set to zero when
its Li or conformal output degree would be negative. -/
noncomputable def liWeightLayerModeToGraded (W : VertexOperatorAlgebra V)
    (d e : ℕ × ℕ) (n : ℕ) :
    liWeightLayer W d.1 d.2 →ₗ[ℂ]
      liWeightLayer W e.1 e.2 →ₗ[ℂ] liAssociatedGraded W :=
  if hn : n ≤ d.1 + e.1 then
    if hN : n + 1 ≤ d.2 + e.2 then
      (liWeightLayerMode W d.1 e.1 d.2 e.2 n hn hN).compr₂
        (DirectSum.lof ℂ (ℕ × ℕ)
          (fun f : ℕ × ℕ => liWeightLayer W f.1 f.2)
          (d.1 + e.1 - n, d.2 + e.2 - (n + 1)))
    else 0
  else 0

/-- Nonnegative vertex modes assembled into bilinear operations on the whole Li algebra. -/
noncomputable def liAssociatedGradedMode (W : VertexOperatorAlgebra V) (n : ℕ) :
    liAssociatedGraded W →ₗ[ℂ] liAssociatedGraded W →ₗ[ℂ] liAssociatedGraded W :=
  DirectSum.toModule ℂ (ℕ × ℕ) (liAssociatedGraded W →ₗ[ℂ] liAssociatedGraded W)
    fun d => (DirectSum.toModule ℂ (ℕ × ℕ)
      (liWeightLayer W d.1 d.2 →ₗ[ℂ] liAssociatedGraded W)
      fun e => (liWeightLayerModeToGraded W d e n).flip).flip

/-- Homogeneous inputs recover the descended vertex mode. -/
@[simp] theorem liAssociatedGradedMode_of_of (W : VertexOperatorAlgebra V) (n : ℕ)
    (d e : ℕ × ℕ) (x : liWeightLayer W d.1 d.2) (y : liWeightLayer W e.1 e.2) :
    liAssociatedGradedMode W n
        (DirectSum.of (fun f : ℕ × ℕ => liWeightLayer W f.1 f.2) d x)
        (DirectSum.of (fun f : ℕ × ℕ => liWeightLayer W f.1 f.2) e y) =
      liWeightLayerModeToGraded W d e n x y := by
  change liAssociatedGradedMode W n
    ((DirectSum.lof ℂ (ℕ × ℕ) _ d) x) ((DirectSum.lof ℂ (ℕ × ℕ) _ e) y) = _
  simp only [liAssociatedGradedMode, DirectSum.toModule_lof, LinearMap.flip_apply]

/-- A homogeneous mode vanishes beyond the sum of its Li degrees. -/
theorem liWeightLayerModeToGraded_eq_zero (W : VertexOperatorAlgebra V)
    (d e : ℕ × ℕ) (n : ℕ) (hn : d.1 + e.1 < n) :
    liWeightLayerModeToGraded W d e n = 0 := by
  simp [liWeightLayerModeToGraded, Nat.not_le.mpr hn]

/-- The descended nonnegative modes are eventually zero on every pair of elements.
This bound follows from finite Li support, independently of representatives. -/
theorem liAssociatedGradedMode_eventually_zero (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) :
    ∃ B : ℕ, ∀ n, B ≤ n → liAssociatedGradedMode W n x y = 0 := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, fun n _ => by simp⟩
  | of d x =>
      induction y using DirectSum.induction_on with
      | zero => exact ⟨0, fun n _ => by simp⟩
      | of e y =>
          refine ⟨d.1 + e.1 + 1, fun n hn => ?_⟩
          rw [liAssociatedGradedMode_of_of,
            liWeightLayerModeToGraded_eq_zero W d e n (by omega)]
          rfl
      | add y z hy hz =>
          obtain ⟨B, hB⟩ := hy
          obtain ⟨C, hC⟩ := hz
          refine ⟨max B C, fun n hn => ?_⟩
          rw [map_add, hB n (le_trans (le_max_left _ _) hn),
            hC n (le_trans (le_max_right _ _) hn), add_zero]
  | add x z hx hz =>
      obtain ⟨B, hB⟩ := hx
      obtain ⟨C, hC⟩ := hz
      refine ⟨max B C, fun n hn => ?_⟩
      simp only [map_add, LinearMap.add_apply,
        hB n (le_trans (le_max_left _ _) hn),
        hC n (le_trans (le_max_right _ _) hn), add_zero]

/-- Finite support of the factorial-normalized mode coefficients. -/
theorem liAssociatedGradedMode_normalized_support_finite (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) :
    (Function.support (fun n : ℕ =>
      (n.factorial : ℂ)⁻¹ • liAssociatedGradedMode W n x y)).Finite := by
  obtain ⟨B, hB⟩ := liAssociatedGradedMode_eventually_zero W x y
  apply (Finset.finite_toSet (Finset.range B)).subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  apply hn
  change (n.factorial : ℂ)⁻¹ • liAssociatedGradedMode W n x y = 0
  rw [hB n (Nat.le_of_not_gt h), smul_zero]

/-- The genuine polynomial lambda-bracket operation formed from the descended vertex modes.
The PVA identities for this operation are separate obligations. -/
noncomputable def liLambdaBracket (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) : Polynomial (liAssociatedGraded W) :=
  Polynomial.ofFinsupp (Finsupp.ofSupportFinite
    (fun n : ℕ => (n.factorial : ℂ)⁻¹ • liAssociatedGradedMode W n x y)
    (liAssociatedGradedMode_normalized_support_finite W x y))

@[simp] theorem coeff_liLambdaBracket (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) (n : ℕ) :
    (liLambdaBracket W x y).coeff n =
      (n.factorial : ℂ)⁻¹ • liAssociatedGradedMode W n x y := by
  simp [liLambdaBracket, Polynomial.coeff_ofFinsupp, Finsupp.ofSupportFinite_coe]

/-- Additivity in the first lambda-bracket argument. -/
theorem liLambdaBracket_add_left (W : VertexOperatorAlgebra V)
    (x y z : liAssociatedGraded W) :
    liLambdaBracket W (x + y) z = liLambdaBracket W x z + liLambdaBracket W y z := by
  apply Polynomial.ext
  intro n
  simp [smul_add]

/-- Additivity in the second lambda-bracket argument. -/
theorem liLambdaBracket_add_right (W : VertexOperatorAlgebra V)
    (x y z : liAssociatedGraded W) :
    liLambdaBracket W x (y + z) = liLambdaBracket W x y + liLambdaBracket W x z := by
  apply Polynomial.ext
  intro n
  simp [smul_add]

/-- Scalar linearity in the first lambda-bracket argument. -/
theorem liLambdaBracket_smul_left (W : VertexOperatorAlgebra V)
    (c : ℂ) (x y : liAssociatedGraded W) :
    liLambdaBracket W (c • x) y = c • liLambdaBracket W x y := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_smul, coeff_liLambdaBracket, map_smul,
    LinearMap.smul_apply, RingHom.id_apply]
  exact smul_comm _ _ _

/-- Scalar linearity in the second lambda-bracket argument. -/
theorem liLambdaBracket_smul_right (W : VertexOperatorAlgebra V)
    (c : ℂ) (x y : liAssociatedGraded W) :
    liLambdaBracket W x (c • y) = c • liLambdaBracket W x y := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_smul, coeff_liLambdaBracket, map_smul,
    LinearMap.smul_apply, RingHom.id_apply]
  exact smul_comm _ _ _

end VOA
