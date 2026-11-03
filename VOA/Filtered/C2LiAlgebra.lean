import VOA.Filtered.LiC2Bridge
import VOA.Modules.FiniteGeneration
import VOA.Modules.PoissonQuotient
import Mathlib.Algebra.Algebra.Bilinear

/-!
# The canonical C2 algebra inside the genuine Li associated graded

Weight decomposition constructs the global degree-zero symbol map. It kills the
actual C2 subspace and respects products, so arbitrary C2 relations transfer to Li.
-/
namespace VOA
open scoped DirectSum BigOperators
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V)
local instance gradingDecomposition : DirectSum.Decomposition W.grading :=
  W.isInternal.chooseDecomposition W.grading

/-- The linear degree-zero symbol on one conformal homogeneous piece. -/
def liDegreeZeroLinear (N : ℕ) : W.grading (N : ℤ) →ₗ[ℂ] liAssociatedGraded W :=
  (liHomogeneousClassLinear W 0 N).comp (Submodule.inclusion (by
    rw [liWeightPiece,liFiltration_zero_eq_top,top_inf_eq]))

/-- On integer-indexed pieces, negative weights contribute zero. -/
def liWeightZeroLinear (n : ℤ) : W.grading n →ₗ[ℂ] liAssociatedGraded W :=
  if hn : 0 ≤ n then
    (liDegreeZeroLinear W n.toNat).comp
      (Submodule.inclusion (by rw [Int.toNat_of_nonneg hn]))
  else 0

/-- The global degree-zero Li symbol of a state, formed by its actual weight decomposition. -/
def stateToLiZero : V →ₗ[ℂ] liAssociatedGraded W :=
  (DirectSum.toModule ℂ ℤ (liAssociatedGraded W) (liWeightZeroLinear W)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem stateToLiZero_homogeneous (N : ℕ) (x : W.grading (N : ℤ)) :
    stateToLiZero W x.1 = liDegreeZeroClass W N x := by
  have h := DirectSum.decompose_coe (ℳ := fun i => (W.grading i : Submodule ℂ V)) x
  change DirectSum.toModule ℂ ℤ (liAssociatedGraded W) (liWeightZeroLinear W)
    (DirectSum.decompose W.grading x.1) = _
  rw [h]
  change DirectSum.toModule ℂ ℤ (liAssociatedGraded W) (liWeightZeroLinear W)
    (DirectSum.lof ℂ ℤ (fun i => W.grading i) (N : ℤ) x) = _
  rw [DirectSum.toModule_lof]
  simp only [liWeightZeroLinear,dif_pos (Int.natCast_nonneg N),Int.toNat_natCast,LinearMap.comp_apply]
  rfl

/-- Actual C2 relations vanish under the global Li symbol map. -/
theorem stateToLiZero_O₂ (x : V) (hx : x ∈ O₂ W) : stateToLiZero W x = 0 := by
  rw [O₂_eq_span_homGen] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p,q,a,b,ha,hb,rfl⟩ := hx
      have hg := gen_mem_grading W ha hb
      by_cases hn : 0 ≤ p+q+1
      · have hg' : W.smul a (-2) b ∈ W.grading (((p+q+1).toNat : ℕ) : ℤ) := by
          simpa [Int.toNat_of_nonneg hn] using hg
        rw [stateToLiZero_homogeneous W _ ⟨_,hg'⟩]
        exact liDegreeZeroClass_eq_zero_of_mem_O₂ W _ _ (Submodule.subset_span ⟨a,b,rfl⟩)
      · have hz : W.smul a (-2) b = 0 := by
          rw [W.positivity _ (by omega),Submodule.mem_bot] at hg
          exact hg
        rw [hz,map_zero]
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add,hx,hy,add_zero]
  | smul c x _ hx => rw [map_smul,hx,smul_zero]

/-- The global C2-to-Li symbol, with actual quotient well-definedness. -/
def c2ToLiLinear : A₂ W →ₗ[ℂ] liAssociatedGraded W :=
  (O₂ W).liftQ (stateToLiZero W) (fun x hx => stateToLiZero_O₂ W x hx)

@[simp] theorem c2ToLiLinear_mk (x : V) :
    c2ToLiLinear W (mk₂ W x) = stateToLiZero W x := rfl

/-- On every homogeneous state the quotient symbol is its actual zeroth Li class. -/
theorem c2ToLiLinear_homogeneous (N : ℕ) (x : W.grading (N : ℤ)) :
    c2ToLiLinear W (mk₂ W x.1) = liDegreeZeroClass W N x :=
  stateToLiZero_homogeneous W N x

/-- The global degree-zero symbol respects the actual minus-one product. -/
theorem stateToLiZero_mul (x y : V) :
    stateToLiZero W (poissonMul W x y) = stateToLiZero W x * stateToLiZero W y := by
  have heq : (poissonMulₗ W).compr₂ (stateToLiZero W) =
      (LinearMap.mul ℂ (liAssociatedGraded W)).compl₁₂ (stateToLiZero W) (stateToLiZero W) := by
    apply LinearMap.ext_on (span_homog_eq_top W)
    rintro a ⟨p,hp⟩
    by_cases hpn : 0 ≤ p
    · apply LinearMap.ext_on (span_homog_eq_top W)
      rintro b ⟨q,hq⟩
      by_cases hqn : 0 ≤ q
      · have ha : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by simpa [Int.toNat_of_nonneg hpn] using hp
        have hb : b ∈ W.grading ((q.toNat : ℕ) : ℤ) := by simpa [Int.toNat_of_nonneg hqn] using hq
        have hab : W.smul a (-1) b ∈ W.grading ((p.toNat+q.toNat : ℕ) : ℤ) := by
          simpa using W.smul_mem_grading ha hb (-1)
        change stateToLiZero W (W.smul a (-1) b) = stateToLiZero W a * stateToLiZero W b
        rw [stateToLiZero_homogeneous W _ ⟨_,hab⟩,
          stateToLiZero_homogeneous W _ ⟨_,ha⟩,stateToLiZero_homogeneous W _ ⟨_,hb⟩]
        simp only [liDegreeZeroClass_eq_liHomogeneousClass,liHomogeneousClass_mul]
      · have hb0 : b=0 := by rw [W.positivity q (by omega),Submodule.mem_bot] at hq; exact hq
        subst b
        simp
    · have ha0 : a=0 := by rw [W.positivity p (by omega),Submodule.mem_bot] at hp; exact hp
      subst a
      simp
  exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

/-- The global C2-to-Li symbol is a genuine algebra homomorphism. -/
def c2ToLiAlgebra : A₂ W →ₐ[ℂ] liAssociatedGraded W where
  toFun := c2ToLiLinear W
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    change stateToLiZero W W.vacuum = 1
    rw [stateToLiZero_homogeneous W 0 ⟨_,W.vacuum_mem_grading_zero⟩,
      liDegreeZeroClass_eq_liHomogeneousClass]
    exact liHomogeneousClass_vacuum W
  map_mul' x y := by
    obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective (O₂ W) x
    obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective (O₂ W) y
    change c2ToLiLinear W (mk₂ W a * mk₂ W b) = _
    rw [A₂_mul_mk]
    exact stateToLiZero_mul W a b
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul]
    change c • stateToLiZero W W.vacuum = _
    rw [stateToLiZero_homogeneous W 0 ⟨_,W.vacuum_mem_grading_zero⟩,
      liDegreeZeroClass_eq_liHomogeneousClass,liHomogeneousClass_vacuum,
      Algebra.algebraMap_eq_smul_one]

@[simp] theorem c2ToLiAlgebra_homogeneous (N : ℕ) (x : W.grading (N : ℤ)) :
    c2ToLiAlgebra W (mk₂ W x.1) = liDegreeZeroClass W N x :=
  c2ToLiLinear_homogeneous W N x

/-- Arbitrary polynomial relations among homogeneous currents transfer from actual C2 to Li. -/
theorem c2ToLiAlgebra_aeval {σ : Type*} (weight : σ → ℕ)
    (gen : ∀ i, W.grading (weight i : ℤ)) (f : MvPolynomial σ ℂ) :
    c2ToLiAlgebra W (MvPolynomial.aeval (fun i => mk₂ W (gen i).1) f) =
      MvPolynomial.aeval (fun i => liDegreeZeroClass W (weight i) (gen i)) f := by
  have h : (c2ToLiAlgebra W).comp (MvPolynomial.aeval (fun i => mk₂ W (gen i).1)) =
      MvPolynomial.aeval (fun i => liDegreeZeroClass W (weight i) (gen i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact DFunLike.congr_fun h f

end
end VOA
