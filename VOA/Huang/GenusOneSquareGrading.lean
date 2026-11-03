import VOA.Huang.GenusOneSClosure

/-!
# Square weights of an ordinary insertion module

The triangular proof of `VOA.sqWeightSpace_isInternal` works on a lowest-weight
module with eigenvalues `h + n`. No rationality, realness of h, or C₂ hypothesis
is needed. This supplies the missing simultaneous decomposition for the S-slash.
Source: Zhu, JAMS 9 (1996), §4; Miyamoto, math/0010180, §2 and Theorem 5.1.
-/
namespace VOA.Huang.GenusOne
open VOA
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The actual eigenspaces of the module operator L[0]. -/
noncomputable def insertionSqWeight (A : OrdVModule W M) (α : ℂ) : Submodule ℂ M :=
  Module.End.eigenspace (sqL A 0) α

theorem mem_insertionSqWeight (A : OrdVModule W M) (α : ℂ) (x : M) :
    x ∈ insertionSqWeight A α ↔ sqL A 0 x = α • x :=
  Module.End.mem_eigenspace_iff

/-- The first n ordinary weight spaces in a fixed lowest-weight coset. -/
noncomputable def insertionBelow (A : OrdVModule W M) (h : ℂ) : ℕ → Submodule ℂ M
  | 0 => ⊥
  | n + 1 => A.weight (h + n) ⊔ insertionBelow A h n

theorem weight_le_insertionBelow (A : OrdVModule W M) (h : ℂ) {j n : ℕ}
    (hjn : j < n) : A.weight (h + j) ≤ insertionBelow A h n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hjn) with rfl | hj
    · exact le_sup_left
    · exact le_trans (ih hj) le_sup_right

/-- L[0] differs from L(0) by strictly lowering terms on each ordinary weight. -/
theorem sqL_zero_sub_mem_insertionBelow (A : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight A h) {n : ℕ} {x : M} (hx : x ∈ A.weight (h + n)) :
    sqL A 0 x - (h + n) • x ∈ insertionBelow A h n := by
  classical
  let f : ℤ → M := fun i => sqBracketCoeffZ 2 1 i • mode (A.YM W.conformalVector) i x
  have hf : (Function.support f).Finite := sqAct_support_finite A W.conformalVector 2 1 x
  have hs : Function.support f ⊆ (insert (1 : ℤ) hf.toFinset : Finset ℤ) := by
    intro i hi
    exact Finset.mem_insert_of_mem (hf.mem_toFinset.mpr hi)
  have he : sqL A 0 x = ∑ i ∈ insert (1 : ℤ) hf.toFinset, f i := by
    simp only [sqL, show (0 : ℤ) ≠ -2 by norm_num, if_false, zero_smul, sub_zero]
    exact finsum_eq_finsetSum_of_support_subset f hs
  rw [he, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self 1 hf.toFinset)]
  have h1 : f 1 = (h + n) • x := by
    simp only [f]
    rw [sqBracketCoeffZ_diag' 2 1, one_smul, A.L0_weight _ _ hx]
  rw [h1, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi1 : i ≠ 1 := (Finset.mem_erase.mp hi).1
  by_cases hi0 : i < 1
  · simp only [f]
    rw [sqBracketCoeffZ_of_lt 2 hi0, zero_smul]
    exact Submodule.zero_mem _
  have hm := mode_mem_weight A W.conformal_mem hx i
  by_cases hb : A.weight (h + (n : ℂ) + (2 : ℤ) - i - 1) = ⊥
  · rw [hb, Submodule.mem_bot] at hm
    simp only [f]
    rw [hm, smul_zero]
    exact Submodule.zero_mem _
  obtain ⟨j, hj⟩ := hlow _ hb
  have heq : (n : ℤ) + 1 - i = (j : ℤ) := by
    have hc : ((n : ℂ) + 1 - (i : ℂ)) = (j : ℂ) := by
      linear_combination hj
    exact_mod_cast hc
  rw [hj] at hm
  exact Submodule.smul_mem _ _ (weight_le_insertionBelow A h (by omega : j < n) hm)

/-- The shifted square operator is surjective below its diagonal eigenvalue. -/
theorem insertion_sq_sub_surj (A : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight A h) (d : ℕ) :
    ∀ n : ℕ, n ≤ d → ∀ w ∈ insertionBelow A h n,
      ∃ y ∈ insertionBelow A h n, sqL A 0 y - (h + d) • y = w := by
  intro n
  induction n with
  | zero =>
    intro _ w hw
    have hw0 : w = 0 := hw
    exact ⟨0, Submodule.zero_mem _, by simp [hw0]⟩
  | succ n ih =>
    intro hnd w hw
    obtain ⟨x, hx, t, ht, rfl⟩ := Submodule.mem_sup.mp hw
    have hc : (h + n) - (h + d) ≠ 0 := by
      have hne : (n : ℂ) ≠ (d : ℂ) := by exact_mod_cast (by omega : n ≠ d)
      simpa only [add_sub_add_left_eq_sub, sub_ne_zero] using hne
    let y₀ : M := ((h + n) - (h + d))⁻¹ • x
    have hy₀ : y₀ ∈ A.weight (h + n) := Submodule.smul_mem _ _ hx
    have hcy : ((h + n) - (h + d)) • y₀ = x := by
      dsimp only [y₀]
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hrem := sqL_zero_sub_mem_insertionBelow A hlow hy₀
    obtain ⟨y₁, hy₁, he₁⟩ := ih (by omega) _ (Submodule.sub_mem _ ht hrem)
    refine ⟨y₀ + y₁, Submodule.add_mem _
      (Submodule.mem_sup_left hy₀) (Submodule.mem_sup_right hy₁), ?_⟩
    rw [map_add, smul_add]
    rw [sub_smul] at hcy
    linear_combination (norm := module) he₁ + hcy

theorem insertionBelow_le_sqWeights (A : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight A h) :
    ∀ n, insertionBelow A h n ≤ ⨆ α : ℂ, insertionSqWeight A α := by
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    refine sup_le (fun x hx => ?_) ih
    obtain ⟨y, hy, he⟩ := insertion_sq_sub_surj A hlow n n le_rfl _
      (sqL_zero_sub_mem_insertionBelow A hlow hx)
    have heig : x - y ∈ insertionSqWeight A (h + n) := by
      rw [mem_insertionSqWeight, map_sub, smul_sub]
      linear_combination (norm := module) -he
    have hx' : x = (x - y) + y := by abel
    rw [hx']
    exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem (h + n) heig) (ih hy)

/-- Square weights span every ordinary module supported on a lowest-weight coset. -/
theorem insertionSqWeight_spans (A : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight A h) : (⨆ α : ℂ, insertionSqWeight A α) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  refine FusionTop.induction_weight A x (Submodule.zero_mem _)
    (fun _ _ hx hy => Submodule.add_mem _ hx hy) ?_
  intro α y hy
  by_cases hb : A.weight α = ⊥
  · rw [hb, Submodule.mem_bot] at hy
    rw [hy]; exact Submodule.zero_mem _
  obtain ⟨n, rfl⟩ := hlow α hb
  exact insertionBelow_le_sqWeights A hlow (n + 1) (Submodule.mem_sup_left hy)

/-- The internal square-weight decomposition, with arbitrary complex lowest weight. -/
theorem insertionSqWeight_isInternal (A : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight A h) : DirectSum.IsInternal (insertionSqWeight A) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Module.End.eigenspaces_iSupIndep (sqL A 0)) (insertionSqWeight_spans A hlow)

theorem insertionSqWeight_isInternal_of_irreducible (A : OrdVModule W M)
    (hA : A.IsIrreducible) : DirectSum.IsInternal (insertionSqWeight A) := by
  obtain ⟨h, hlow, _⟩ := A.exists_isLowestWeight_of_irreducible hA
  exact insertionSqWeight_isInternal A hlow

end VOA.Huang.GenusOne
