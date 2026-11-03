import VOA.Huang.GenusOneIntCoordTraceBound

/-!
# Triangular support and the quantitative bracket-expansion reduction

An ordinary degree `k` coefficient has square components only in degrees `0..k`.
This gives a fixed finite formula for its absolute square-trace mass; a bound
uniform in `k` is still required for convergence.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint GenusOneG1c VerlindeFusion VerlindeTransport TensorCat
open scoped BigOperators DirectSum
universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

theorem squarePart_zero (n : ℕ) : squarePart (W := W) 0 n = 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  simp [squarePart, squareParts]

theorem squarePart_add (v w : V) (n : ℕ) :
    squarePart (W := W) (v + w) n = squarePart (W := W) v n + squarePart (W := W) w n := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  simp [squarePart, squareParts]

theorem squarePart_eq_zero_of_mem_sqWeightSpace {v : V} {m n : ℕ}
    (hv : v ∈ sqWeightSpace W (m : ℂ)) (hmn : m ≠ n) :
    squarePart (W := W) v n = 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  exact DirectSum.decompose_of_mem_ne (fun i : ℕ => sqWeightSpace W (i : ℂ)) hv hmn

/-- The triangular square grading gives an explicit upper bound on support. -/
theorem squarePart_eq_zero_of_mem_gradeLE (m n : ℕ) (hmn : m ≤ n)
    {v : V} (hv : v ∈ gradeLE W ((m : ℤ) - 1)) :
    squarePart (W := W) v n = 0 := by
  induction m generalizing v with
  | zero =>
    have hv0 : v = 0 := by simpa [gradeLE_eq_bot W (by norm_num : (-1 : ℤ) < 0)] using hv
    rw [hv0, squarePart_zero]
  | succ m ih =>
    have hv' : v ∈ W.grading (m : ℤ) ⊔ gradeLE W ((m : ℤ) - 1) := by
      rw [← gradeLE_split]
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv'
    rw [squarePart_add, ih (by omega) hy, add_zero]
    have hw := Lsq_zero_sub_smul_mem_gradeLE W hx
    obtain ⟨t, ht, he⟩ := sub_smul_surj W (m : ℤ) m
      (Lsq W 0 x - ((m : ℤ) : ℂ) • x) hw (by omega)
    have heig : x - t ∈ sqWeightSpace W (m : ℂ) := by
      rw [mem_sqWeightSpace_iff, map_sub, smul_sub]
      push_cast at he
      linear_combination (norm := abel) -he
    have hx' : x = (x - t) + t := by abel
    rw [hx', squarePart_add,
      squarePart_eq_zero_of_mem_sqWeightSpace heig (by omega), ih (by omega) ht, add_zero]

theorem squarePart_eq_zero_of_grading_lt {v : V} {k n : ℕ}
    (hv : v ∈ W.grading (k : ℤ)) (hkn : k < n) :
    squarePart (W := W) v n = 0 :=
  squarePart_eq_zero_of_mem_gradeLE (k + 1) n (by omega)
    (mem_gradeLE_of_mem_grading W (by omega) hv)

variable {P Q : LWModule W} {ι : Type w} [Fintype ι] [DecidableEq ι]
  (D : VOA.ModularData W ι)

/-- For homogeneous insertions the mass has at most `k+1` summands. -/
theorem squareTraceMass_eq_sum_range (hC2 : C2Cofinite W)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    {wa : P.carrier} {wb : Q.carrier} {α β : ℂ}
    (hwa : wa ∈ P.isMod.weight α) (hwb : wb ∈ Q.isMod.weight β)
    (x : ι) (τ : UpperHalfPlane) (k : ℕ) :
    squareTraceMass D Y wa wb α β x τ k =
      ∑ n ∈ Finset.range (k + 1), ‖traceFun D.Mfam D.h x
        (squarePart (W := W) (vacuumInnerCoeff Y wa wb α β k) n) τ‖ := by
  apply tsum_eq_sum
  intro n hn
  rw [squarePart_eq_zero_of_grading_lt (vacuumInnerCoeff_mem_grading Y hwa hwb k)
    (by simpa using hn)]
  change ‖traceFunStateLinear D hC2 x τ 0‖ = 0
  rw [map_zero, norm_zero]

/-- The existing bracket-expansion statement from the explicit mass bound.
The mass bound for strongly rational VOAs is not discharged here. -/
theorem vacuumChannelBracketExpansion_of_squareTraceMass_bound
    (hV : StronglyRational W) (F : FusionChoice W) (hv : W.vacuum ≠ 0)
    {a b : ι} (c : TransferChoice F D a b)
    (hbound : ∀ {α β : ℂ} {wa : (lwOf D a).carrier} {wb : (lwOf D b).carrier},
      wa ∈ (lwOf D a).isMod.weight α → wb ∈ (lwOf D b).isMod.weight β →
      ∀ τ : UpperHalfPlane, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
        ∀ (x : ι) (k : ℕ), squareTraceMass D (epsInt F c) wa wb α β x τ k ≤ C * B ^ k) :
    VacuumChannelBracketExpansion F hv c :=
  vacuumChannelBracketExpansion_of_logSquareTraceSummable hV F hv c
    (fun hwa hwb => logSquareTraceSummable_of_squareTraceMass_bound D hV.c2Cofinite
      (epsInt F c) _ _ _ _ (hbound hwa hwb))

end VOA.Huang.GenusOne.IntCoord
