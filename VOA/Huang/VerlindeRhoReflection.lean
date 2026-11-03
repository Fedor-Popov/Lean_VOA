import VOA.Huang.VerlindeRhoInput

/-!
# Reflection reduced to a single commutator

The ordinary-weight filtration makes the square-weight reflection identity
equivalent to commutation with `L[0]`. The commutator is retained as an explicit
coordinate-change obligation; no general change-of-coordinate law is assumed.
-/

namespace VOA.Huang.VerlindeRho

open VOA VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

theorem grading_disjoint_gradeLE (W : VertexOperatorAlgebra V) (d : ℤ) :
    Disjoint (W.grading d) (gradeLE W (d - 1)) := by
  apply (W.isInternal.submodule_iSupIndep d).mono_right
  exact iSup_le fun j => le_iSup_of_le (j : ℤ)
    (le_iSup_of_le (by have := j.2; omega : (j : ℤ) ≠ d) le_rfl)

theorem Lsq_zero_mem_gradeLE {d : ℤ} {v : V} (hv : v ∈ gradeLE W d) :
    Lsq W 0 v ∈ gradeLE W d := by
  induction hv using Submodule.iSup_induction' with
  | mem j x hx =>
    have hr := Lsq_zero_sub_smul_mem_gradeLE W hx
    have he : Lsq W 0 x =
        (Lsq W 0 x - ((j : ℤ) : ℂ) • x) + ((j : ℤ) : ℂ) • x := by abel
    rw [he]
    exact Submodule.add_mem _
      (gradeLE_mono W (by have := j.2; omega) hr)
      (Submodule.smul_mem _ _ (mem_gradeLE_of_mem_grading W j.2 hx))
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- If the eigenvalue differs from the top ordinary grade, that grade vanishes. -/
theorem sq_eigen_lower {d n : ℤ} {v : V} (hv : v ∈ gradeLE W d)
    (he : Lsq W 0 v = (n : ℂ) • v) (hdn : d ≠ n) :
    v ∈ gradeLE W (d - 1) := by
  rw [gradeLE_split W d] at hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  have hc : (d : ℂ) - (n : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hdn)
  have hlow : ((d : ℂ) - (n : ℂ)) • x ∈ gradeLE W (d - 1) := by
    have hr := Lsq_zero_sub_smul_mem_gradeLE W hx
    have ht := Lsq_zero_mem_gradeLE hy
    have heq : ((d : ℂ) - (n : ℂ)) • x =
        (n : ℂ) • y - Lsq W 0 y - (Lsq W 0 x - (d : ℂ) • x) := by
      rw [map_add, smul_add] at he
      linear_combination (norm := module) he
    rw [heq]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) ht) hr
  have hz : ((d : ℂ) - (n : ℂ)) • x = 0 :=
    (Submodule.disjoint_def.mp (grading_disjoint_gradeLE W d)) _
      (Submodule.smul_mem _ _ hx) hlow
  have hx0 : x = 0 := (smul_eq_zero.mp hz).resolve_left hc
  simpa only [hx0, zero_add] using hy

/-- An eigenvector with eigenvalue at least `d` cannot lie below grade `d`. -/
theorem sq_eigen_eq_zero_below (d : ℕ) {n : ℤ} (hdn : (d : ℤ) ≤ n)
    {v : V} (hv : v ∈ gradeLE W ((d : ℤ) - 1))
    (he : Lsq W 0 v = (n : ℂ) • v) : v = 0 := by
  induction d with
  | zero =>
    simpa only [Nat.cast_zero, zero_sub, gradeLE_eq_bot W (by norm_num : (-1 : ℤ) < 0),
      Submodule.mem_bot] using hv
  | succ d ih =>
    have hv' : v ∈ gradeLE W (d : ℤ) := by simpa using hv
    exact ih (by omega) (sq_eigen_lower hv' he (by omega))

/-- A square-weight `n` vector has no ordinary grades above `n`. -/
theorem sqWeight_le_gradeLE (n : ℕ) : sqWeightSpace W (n : ℂ) ≤ gradeLE W (n : ℤ) := by
  intro v hv
  have he : Lsq W 0 v = ((n : ℤ) : ℂ) • v := (mem_sqWeightSpace_iff W _ v).mp hv
  obtain ⟨d, hd⟩ := exists_mem_gradeLE W v
  have aux : ∀ k : ℕ, ∀ v ∈ gradeLE W (k : ℤ),
      Lsq W 0 v = ((n : ℤ) : ℂ) • v → v ∈ gradeLE W (n : ℤ) := by
    intro k
    induction k with
    | zero => intro v hv _; exact gradeLE_mono W (by omega) hv
    | succ k ih =>
      intro v hv he
      by_cases hkn : (k + 1 : ℕ) ≤ n
      · exact gradeLE_mono W (by exact_mod_cast hkn) hv
      · apply ih v
        · simpa using sq_eigen_lower hv he (by omega)
        · exact he
  exact aux d.toNat v (gradeLE_mono W (by omega) hd) he

theorem contraTwist_sub_mem_gradeLE {n : ℤ} {v : V} (hv : v ∈ W.grading n) :
    contraTwist W v - (-1 : ℂ) ^ n • v ∈ gradeLE W (n - 1) := by
  classical
  rw [contraTwist_homogeneous hv, contraState, Finset.sum_range_succ']
  simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul]
  rw [smul_add, add_sub_cancel_right]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (mem_gradeLE_of_mem_grading W (by omega)
    (L_one_pow_mem W hv (j + 1)))

theorem contraTwist_mem_gradeLE {d : ℤ} {v : V} (hv : v ∈ gradeLE W d) :
    contraTwist W v ∈ gradeLE W d := by
  induction hv using Submodule.iSup_induction' with
  | mem j x hx =>
    have hr := contraTwist_sub_mem_gradeLE hx
    have he : contraTwist W x =
        (contraTwist W x - (-1 : ℂ) ^ (j : ℤ) • x) + (-1 : ℂ) ^ (j : ℤ) • x := by abel
    rw [he]
    exact Submodule.add_mem _ (gradeLE_mono W (by have := j.2; omega) hr)
      (Submodule.smul_mem _ _ (mem_gradeLE_of_mem_grading W j.2 hx))
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The remaining coordinate calculation concerns just one operator. -/
def SquareBracketReflectionCommutes (W : VertexOperatorAlgebra V) : Prop :=
  ∀ v, contraTwist W (Lsq W 0 v) = Lsq W 0 (contraTwist W v)

/-- Commutation and triangularity force the claimed square-weight sign. -/
theorem squareBracketReflection_of_commutes
    (hc : SquareBracketReflectionCommutes W) : SquareBracketReflection W := by
  intro n v hv
  have he := (mem_sqWeightSpace_iff W _ v).mp hv
  have hlow : contraTwist W v - (-1 : ℂ) ^ n • v ∈ gradeLE W ((n : ℤ) - 1) := by
    have hfil := sqWeight_le_gradeLE n hv
    rw [gradeLE_split W (n : ℤ)] at hfil
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hfil
    have hx' := contraTwist_sub_mem_gradeLE hx
    rw [zpow_natCast] at hx'
    have hy' := Submodule.sub_mem _ (contraTwist_mem_gradeLE hy)
      (Submodule.smul_mem _ ((-1 : ℂ) ^ n) hy)
    convert Submodule.add_mem _ hx' hy' using 1
    simp only [map_add, smul_add]
    abel
  have he' : Lsq W 0 (contraTwist W v - (-1 : ℂ) ^ n • v) =
      ((n : ℤ) : ℂ) • (contraTwist W v - (-1 : ℂ) ^ n • v) := by
    rw [map_sub, ← hc, he, map_smul, map_smul, he, smul_sub, smul_comm ((-1 : ℂ) ^ n)]
    simp only [Int.cast_natCast]
  exact sub_eq_zero.mp (sq_eigen_eq_zero_below n le_rfl hlow he')

/-- Conversely, square-weight reflection commutes with `L[0]` on the whole VOA. -/
theorem squareBracketReflectionCommutes_of_reflection
    (hr : SquareBracketReflection W) : SquareBracketReflectionCommutes W := by
  intro v
  have hv : v ∈ ⨆ n : ℕ, sqWeightSpace W (n : ℂ) := by
    rw [sqWeightSpace_nat_spans_top]; trivial
  refine Submodule.iSup_induction (fun n : ℕ => sqWeightSpace W (n : ℂ))
    (motive := fun v => contraTwist W (Lsq W 0 v) = Lsq W 0 (contraTwist W v)) hv ?_ ?_ ?_
  · intro n v hv
    have he := (mem_sqWeightSpace_iff W _ v).mp hv
    rw [he, map_smul, hr n v hv, map_smul, he, smul_comm]
  · simp only [map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem squareBracketReflection_iff_commutes :
    SquareBracketReflection W ↔ SquareBracketReflectionCommutes W :=
  ⟨squareBracketReflectionCommutes_of_reflection, squareBracketReflection_of_commutes⟩

end VOA.Huang.VerlindeRho
