import VOA.Huang.GenusOneIntCoordVacuumTrace

/-!
# Finite square-weight decomposition of the vacuum iterate coefficients

This file proves the expansion with each finite square-weight sum grouped at its
original inner mode. It does not exchange the two sums without joint summability.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint GenusOneG1c VerlindeFusion VerlindeTransport TensorCat
open scoped BigOperators DirectSum
universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The canonical finite natural square-weight decomposition. -/
def squareParts (v : V) : ⨁ n : ℕ, sqWeightSpace W (n : ℂ) :=
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  DirectSum.decompose (fun n : ℕ => sqWeightSpace W (n : ℂ)) v

def squareSupport (v : V) : Finset ℕ := by
  classical
  exact (squareParts (W := W) v).support

def squarePart (v : V) (n : ℕ) : V := squareParts (W := W) v n

theorem squarePart_mem (v : V) (n : ℕ) :
    squarePart (W := W) v n ∈ sqWeightSpace W (n : ℂ) :=
  (squareParts (W := W) v n).property

theorem sum_squarePart (v : V) :
    ∑ n ∈ squareSupport (W := W) v, squarePart (W := W) v n = v := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  exact DirectSum.sum_support_decompose (fun n : ℕ => sqWeightSpace W (n : ℂ)) v

theorem squarePart_eq_zero_of_not_mem {v : V} {n : ℕ}
    (hn : n ∉ squareSupport (W := W) v) : squarePart (W := W) v n = 0 := by
  classical
  have he : squareParts (W := W) v n = 0 :=
    DFinsupp.notMem_support_iff.mp hn
  exact congrArg (fun t : sqWeightSpace W (n : ℂ) => (t : V)) he

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- C₂ convergence makes the ordinary Zhu trace linear in its state. -/
def traceFunStateLinear (hC2 : C2Cofinite W) (x : ι) (τ : UpperHalfPlane) : V →ₗ[ℂ] ℂ where
  toFun v := traceFun D.Mfam D.h x v τ
  map_add' v w := by
    unfold traceFun
    rw [torusOnePoint_add]
    apply qEvalAt_add
    · simpa only [trace_moduleIntertwiner, torusOnePoint] using
        (summable_trace_moduleIntertwiner (D.Mfam x).isMod (D.hasWeight x)
          hC2 (norm_qParam_lt_one τ) v).of_norm
    · simpa only [trace_moduleIntertwiner, torusOnePoint] using
        (summable_trace_moduleIntertwiner (D.Mfam x).isMod (D.hasWeight x)
          hC2 (norm_qParam_lt_one τ) w).of_norm
  map_smul' c v := by
    simp only [traceFun, torusOnePoint_smul, qEvalAt_smul, RingHom.id_apply, smul_eq_mul]

/-- Each individual inner coefficient splits into finitely many honest Zhu
one-point traces on square-weight states. -/
theorem traceFun_eq_sum_squarePart (hC2 : C2Cofinite W) (x : ι) (τ : UpperHalfPlane) (v : V) :
    traceFun D.Mfam D.h x v τ =
      ∑ n ∈ squareSupport (W := W) v, traceFun D.Mfam D.h x (squarePart (W := W) v n) τ := by
  exact (congrArg (traceFunStateLinear D hC2 x τ) (sum_squarePart (W := W) v)).symm.trans
    (map_sum (traceFunStateLinear D hC2 x τ) _ _)

/-- A convergent grouped square-weight expansion of the actual vacuum channel.
The two indexing functions depend on the insertions alone; δ depends on τ. -/
theorem vacuumChannel_grouped_square_expansion (hV : StronglyRational W)
    (F : FusionChoice W) (hv : W.vacuum ≠ 0) {a b : ι} (c : TransferChoice F D a b)
    {wa : (lwOf D a).carrier} {wb : (lwOf D b).carrier} {α β : ℂ}
    (hwa : wa ∈ (lwOf D a).isMod.weight α) (hwb : wb ∈ (lwOf D b).isMod.weight β)
    (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι) (z : ℂ), 0 < z.re → ‖z‖ < δ →
      HasSum (fun k : ℕ => z ^ ((k : ℂ) - α - β) *
        ∑ n ∈ squareSupport (W := W) (vacuumInnerCoeff (epsInt F c) wa wb α β k),
          traceFun D.Mfam D.h x
            (squarePart (W := W) (vacuumInnerCoeff (epsInt F c) wa wb α β k) n) τ)
        (iterF (Q := vacuumLW W hv) (N := lwOf D x)
          (moduleIntertwiner (lwOf D x).isMod) (epsInt F c) wa wb α β τ z) := by
  obtain ⟨δ, hδ, hs⟩ := vacuumChannel_plane_expansion D hV F hv c hwa hwb τ
  refine ⟨δ, hδ, fun x z hz hnorm => (hs x z hz hnorm).congr_fun fun k => ?_⟩
  rw [← traceFun_eq_sum_squarePart D hV.c2Cofinite]

end VOA.Huang.GenusOne.IntCoord
