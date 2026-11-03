import VOA.Huang.GenusTwoPointSepCoordinateWard
import VOA.Huang.GenusOneScaleModes

/-!
# Triangularity of the actual coordinate exponentials and square modes

All filtrations in this file are ordinary weight filtrations. In particular,
triangularity does not assert the still separate square-weight conjugation law.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u

section FilteredExponential
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A strictly lowering exponential is the identity on the associated graded. -/
theorem expFun_sub_mem_lower (F : ℤ → Submodule ℂ M)
    (hF : Monotone F) {D : Module.End ℂ M} (hD : IsLocNilp D)
    (hLower : ∀ (d : ℤ) (x : M), x ∈ F d → D x ∈ F (d - 1))
    {d : ℤ} {x : M} (hx : x ∈ F d) : expFun hD x - x ∈ F (d - 1) := by
  obtain ⟨N, hN⟩ := hD x
  have hp : ∀ n : ℕ, (D ^ n) x ∈ F (d - n) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [VOA.pow_succ'_apply]
      convert hLower _ _ ih using 1
      congr 1
      push_cast
      ring
  rw [expFun_eq_expSum hD (pow_apply_eq_zero_of_le hN (Nat.le_succ N)), expSum,
    Finset.sum_range_succ']
  simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _
    (hF (by omega : d - ((n + 1 : ℕ) : ℤ) ≤ d - 1) (hp (n + 1)))

theorem expFun_mem_filtration (F : ℤ → Submodule ℂ M)
    (hF : Monotone F) {D : Module.End ℂ M} (hD : IsLocNilp D)
    (hLower : ∀ (d : ℤ) (x : M), x ∈ F d → D x ∈ F (d - 1))
    {d : ℤ} {x : M} (hx : x ∈ F d) : expFun hD x ∈ F d := by
  have ht := expFun_sub_mem_lower F hF hD hLower hx
  have := Submodule.add_mem (F d) (hF (by omega : d - 1 ≤ d) ht) hx
  simpa only [sub_add_cancel] using this

end FilteredExponential

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

theorem normalizedCoordinateChange_sub_mem_lower (P : LWModule W)
    {d : ℤ} {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    normalizedCoordinateChange P x - x ∈ moduleLevelLE P (d - 1) := by
  apply expFun_sub_mem_lower (moduleLevelLE P) (fun _ _ h => moduleLevelLE_mono P h)
    (moduleCoordGen_isLocNilp P _).neg _ hx
  intro e y hy
  exact Submodule.neg_mem _ (moduleCoordGen_mem_lower P _ hy)

theorem normalizedCoordinateChange_mem (P : LWModule W)
    {d : ℤ} {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    normalizedCoordinateChange P x ∈ moduleLevelLE P d := by
  have ht := normalizedCoordinateChange_sub_mem_lower P hx
  have := Submodule.add_mem _ (moduleLevelLE_mono P (by omega : d - 1 ≤ d) ht) hx
  simpa only [sub_add_cancel] using this

theorem normalizedCoordinateChange_symm_mem (P : LWModule W)
    {d : ℤ} {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    (normalizedCoordinateChange P).symm x ∈ moduleLevelLE P d := by
  change expFun ((moduleCoordGen_isLocNilp P _).neg.neg) x ∈ _
  apply expFun_mem_filtration (moduleLevelLE P) (fun _ _ h => moduleLevelLE_mono P h)
    _ _ hx
  intro e y hy
  simpa only [neg_neg] using moduleCoordGen_mem_lower P
    (iterativeLog (logarithmicCoordinate 1)) hy

theorem normalizedStateChange_sub_mem_lower
    {d : ℤ} {a : V} (ha : a ∈ gradeLE W d) :
    normalizedStateChange W a - a ∈ gradeLE W (d - 1) := by
  apply expFun_sub_mem_lower (gradeLE W) (fun _ _ h => gradeLE_mono W h)
    (coordGen_isLocNilp W _) _ ha
  intro e y hy
  exact coordGen_mem_gradeLE W _ hy

theorem normalizedStateChange_mem
    {d : ℤ} {a : V} (ha : a ∈ gradeLE W d) :
    normalizedStateChange W a ∈ gradeLE W d := by
  have ht := normalizedStateChange_sub_mem_lower ha
  have := Submodule.add_mem _ (gradeLE_mono W (by omega : d - 1 ≤ d) ht) ha
  simpa only [sub_add_cancel] using this

/-- Ordinary modes respect the sum filtration, with the exact mode shift. -/
theorem mode_mem_level_of_homogeneous (P : LWModule W)
    {k e : ℤ} {a : V} (ha : a ∈ W.grading k) {x : P.carrier}
    (hx : x ∈ moduleLevelLE P e) (m : ℤ) :
    mode (P.isMod.YM a) m x ∈ moduleLevelLE P (k + e - m - 1) := by
  induction hx using Submodule.iSup_induction' with
  | mem j y hy =>
    have hm := mode_mem_weight P.isMod ha hy m
    have he : P.h + ((j : ℤ) : ℂ) + k - m - 1 =
        P.h + ((k + (j : ℤ) - m - 1 : ℤ) : ℂ) := by push_cast; ring
    rw [he] at hm
    exact mem_moduleLevelLE P (by have := j.2; omega) hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem sqMode_mem_level_of_homogeneous (P : LWModule W)
    {k e : ℤ} {a : V} (ha : a ∈ W.grading k) {x : P.carrier}
    (hx : x ∈ moduleLevelLE P e) (m : ℤ) :
    SquareModule.sqMode P.isMod m a x ∈ moduleLevelLE P (k + e - m - 1) := by
  rw [SquareModule.sqMode_of_mem_grading P.isMod ha]
  obtain ⟨J, hJ⟩ := P.isMod.truncation a x
  rw [sqAct_eq_range P.isMod a k.toNat m x J hJ]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact moduleLevelLE_mono P (by have := (Finset.mem_Ico.mp hi).1; omega)
    (mode_mem_level_of_homogeneous P ha hx i)

theorem sqMode_mem_level (P : LWModule W)
    {d e : ℤ} {a : V} (ha : a ∈ gradeLE W d) {x : P.carrier}
    (hx : x ∈ moduleLevelLE P e) (m : ℤ) :
    SquareModule.sqMode P.isMod m a x ∈ moduleLevelLE P (d + e - m - 1) := by
  induction ha using Submodule.iSup_induction' with
  | mem j b hb =>
    exact moduleLevelLE_mono P (by have := j.2; omega)
      (sqMode_mem_level_of_homogeneous P hb hx m)
  | zero => simp
  | add a b _ _ ha hb =>
    simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ ha hb

/-- The coefficient of the original mode is one; all other terms lower level. -/
theorem sqMode_sub_mode_mem_lower (P : LWModule W)
    {k e : ℤ} {a : V} (ha : a ∈ W.grading k) {x : P.carrier}
    (hx : x ∈ moduleLevelLE P e) (m : ℤ) :
    SquareModule.sqMode P.isMod m a x - mode (P.isMod.YM a) m x ∈
      moduleLevelLE P (k + e - m - 2) := by
  classical
  let f : ℤ → P.carrier := fun i =>
    sqBracketCoeffZ k.toNat m i • mode (P.isMod.YM a) i x
  have hf : (Function.support f).Finite := sqAct_support_finite P.isMod a k.toNat m x
  have hs : Function.support f ⊆ (insert m hf.toFinset : Finset ℤ) := by
    intro i hi
    exact Finset.mem_insert_of_mem (hf.mem_toFinset.mpr hi)
  rw [SquareModule.sqMode_of_mem_grading P.isMod ha, sqAct_apply,
    finsum_eq_finsetSum_of_support_subset f hs,
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self m hf.toFinset)]
  have hm : f m = mode (P.isMod.YM a) m x := by
    simp only [f, sqBracketCoeffZ_diag', one_smul]
  rw [hm, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun i hi => ?_
  by_cases him : i < m
  · simp only [f, sqBracketCoeffZ_of_lt k.toNat him, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _
      (moduleLevelLE_mono P (by have := (Finset.mem_erase.mp hi).1; omega)
        (mode_mem_level_of_homogeneous P ha hx i))

/-- Both sides of the requested conjugation formula have the same leading term.
This statement is unconditional and retains every integer mode. -/
theorem normalizedSquare_defect_mem_lower (P : LWModule W)
    {k e : ℤ} {a : V} (ha : a ∈ W.grading k) {x : P.carrier}
    (hx : x ∈ moduleLevelLE P e) (m : ℤ) :
    normalizedCoordinateChange P (mode (P.isMod.YM a) m x) -
      SquareModule.sqMode P.isMod m (normalizedStateChange W a)
        (normalizedCoordinateChange P x) ∈ moduleLevelLE P (k + e - m - 2) := by
  have ha' := mem_gradeLE_of_mem_grading W (le_refl k) ha
  have h₁ := normalizedCoordinateChange_sub_mem_lower P
    (mode_mem_level_of_homogeneous P ha hx m)
  have h₂ := sqMode_sub_mode_mem_lower P ha hx m
  have h₃ := sqMode_mem_level P (normalizedStateChange_sub_mem_lower ha')
    (normalizedCoordinateChange_mem P hx) m
  have h₄ := sqMode_mem_level P ha' (normalizedCoordinateChange_sub_mem_lower P hx) m
  have e₁ : k + e - m - 1 - 1 = k + e - m - 2 := by omega
  have e₃ : k - 1 + e - m - 1 = k + e - m - 2 := by omega
  have e₄ : k + (e - 1) - m - 1 = k + e - m - 2 := by omega
  rw [e₁] at h₁
  rw [e₃] at h₃
  rw [e₄] at h₄
  have h := Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ h₁ h₂) h₃) h₄
  simp only [map_sub, LinearMap.sub_apply] at h
  convert h using 1
  module

end VOA.Huang.GenusTwoPoint.Separate
