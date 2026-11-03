import VOA.Huang.VerlindeRhoReflection
import VOA.Huang.LiRegularExp

/-! # The ordinary Virasoro calculation underlying reflection -/

namespace VOA.Huang.VerlindeRho
open VOA VertexOperatorAlgebra
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

noncomputable def expL1 (W : VertexOperatorAlgebra V) : Module.End ℂ V :=
  LiRegular.expOp (isLocNilp_L_one W) 1

theorem contraTwist_eq_expL1 {n : ℤ} {v : V} (hv : v ∈ W.grading n) :
    contraTwist W v = (-1 : ℂ) ^ n • expL1 W v := by
  rw [contraTwist_homogeneous hv, contraState, expL1,
    LiRegular.expOp_eq_sum _ _ (L_one_pow_eq_zero W hv
      (by omega : n - (n.toNat + 1 : ℕ) < 0))]
  simp only [one_pow, one_div]

theorem expL1_mem_gradeLE {d : ℤ} {v : V} (hv : v ∈ gradeLE W d) :
    expL1 W v ∈ gradeLE W d := by
  induction hv using Submodule.iSup_induction' with
  | mem j x hx =>
    have ht := contraTwist_mem_gradeLE (mem_gradeLE_of_mem_grading W j.2 hx)
    rw [contraTwist_eq_expL1 hx] at ht
    exact (Submodule.smul_mem_iff _ (zpow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))).mp ht
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The positive-mode tail vanishes on the ordinary-weight filtration. -/
theorem L_eq_zero_of_mem_gradeLE {d a : ℤ} {v : V}
    (hv : v ∈ gradeLE W d) (ha : d < a) : W.L a v = 0 := by
  induction hv using Submodule.iSup_induction' with
  | mem j x hx =>
    have ht := L_mem_grading W hx a
    rw [W.positivity _ (by have := j.2; omega), Submodule.mem_bot] at ht
    exact ht
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]

/-- The exponential conjugation formula uses only the ordinary Virasoro bracket. -/
theorem expL1_L (a : ℤ) (v : V) :
    expL1 W (W.L a v) = ∑ᶠ k : ℕ,
      cbz (1 - a) k • W.L (a + k) (expL1 W v) := by
  have hc : ∀ (n : ℤ) (y : V),
      W.L 1 (W.L (1 - n) y) - W.L (1 - n) (W.L 1 y) =
        (n : ℂ) • W.L (1 - (n - 1)) y := by
    intro n y
    have h := congrArg (fun F : Module.End ℂ V => F y) (W.L_virasoro 1 (1 - n))
    simpa [Ring.lie_def, sub_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have ht : ∀ y : V, ∃ K : ℤ, ∀ n : ℤ, n ≤ K → W.L (1 - n) y = 0 := by
    intro y
    obtain ⟨d, hd⟩ := exists_mem_gradeLE W y
    exact ⟨-d, fun n hn => L_eq_zero_of_mem_gradeLE hd (by omega)⟩
  have h := LiRegular.expOp_conj (isLocNilp_L_one W)
    (fun n => W.L (1 - n)) hc ht 1 (1 - a) v
  simpa only [show 1 - (1 - a) = a by omega, one_pow, mul_one,
    show ∀ k : ℕ, 1 - (1 - a - (k : ℤ)) = a + k by intro k; omega] using h

theorem expL1_L_eq_sum (d a : ℕ) {v : V} (hv : v ∈ gradeLE W (d : ℤ)) :
    expL1 W (W.L (a : ℤ) v) = ∑ k ∈ Finset.range (d + 1 - a),
      cbz (1 - (a : ℤ)) k • W.L ((a : ℤ) + k) (expL1 W v) := by
  rw [expL1_L]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hk (by rw [L_eq_zero_of_mem_gradeLE (expL1_mem_gradeLE hv) (by omega), smul_zero])

/-- The coefficients of `L[0]` in the ordinary Virasoro modes. -/
noncomputable def reflectionCoeff (a : ℕ) : ℂ := sqBracketCoeffZ 2 1 ((a : ℤ) + 1)

theorem Lsq_zero_eq_sum (d : ℕ) {v : V} (hv : v ∈ gradeLE W (d : ℤ)) :
    Lsq W 0 v = ∑ a ∈ Finset.range (d + 1), reflectionCoeff a • W.L (a : ℤ) v := by
  rw [Lsq_zero_apply]
  have hs : Function.support (fun a : ℤ => sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.L a v)
      ⊆ (Finset.range (d + 1)).image (fun a : ℕ => (a : ℤ)) := by
    intro a ha
    rw [Function.mem_support] at ha
    have ha0 : 0 ≤ a := by
      by_contra h
      exact ha (by rw [sqBracketCoeff_zero_of_neg (by omega), zero_smul])
    have had : a ≤ d := by
      by_contra h
      exact ha (by rw [L_eq_zero_of_mem_gradeLE hv (by omega), smul_zero])
    exact Finset.mem_image.mpr ⟨a.toNat, Finset.mem_range.mpr (by omega), Int.toNat_of_nonneg ha0⟩
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_image]
  · rfl
  · intro a _ b _ h; exact Int.ofNat_injective h

/-- The scalar Mobius-reflection identity for the coefficients of `L[0]`.
This is a finite identity in complex numbers, independent of any VOA. -/
def ReflectionBinomialIdentity : Prop :=
  ∀ m : ℕ, ∑ a ∈ Finset.range (m + 1),
    ((-1 : ℂ) ^ a * reflectionCoeff a * cbz (1 - (a : ℤ)) (m - a : ℕ)) =
      reflectionCoeff m

theorem contraTwist_Lsq_homogeneous (hb : ReflectionBinomialIdentity)
    (n : ℕ) {v : V} (hv : v ∈ W.grading (n : ℤ)) :
    contraTwist W (Lsq W 0 v) = Lsq W 0 (contraTwist W v) := by
  classical
  have hfil := mem_gradeLE_of_mem_grading W le_rfl hv
  have hsign (a : ℕ) : (-1 : ℂ) ^ ((n : ℤ) - a) = (-1 : ℂ) ^ n * (-1 : ℂ) ^ a := by
    rw [negOne_zpow_eq ((n : ℤ) - a) ((n : ℤ) + a) ⟨-(a : ℤ), by ring⟩,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, zpow_natCast]
  rw [Lsq_zero_eq_sum n hfil, map_sum, contraTwist_eq_expL1 hv, map_smul,
    zpow_natCast, Lsq_zero_eq_sum n (expL1_mem_gradeLE hfil)]
  have hterm : ∀ a ∈ Finset.range (n + 1),
      contraTwist W (reflectionCoeff a • W.L (a : ℤ) v) =
      (-1 : ℂ) ^ n • ∑ k ∈ Finset.range (n + 1 - a),
        ((-1 : ℂ) ^ a * reflectionCoeff a * cbz (1 - (a : ℤ)) k) •
          W.L ((a : ℤ) + k) (expL1 W v) := by
    intro a _
    rw [map_smul, contraTwist_eq_expL1 (L_mem_grading W hv (a : ℤ)),
      hsign, expL1_L_eq_sum n a hfil, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [smul_smul]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum]
  congr 1
  rw [← LiRegular.tri_reindex (n + 1) (fun a k =>
    ((-1 : ℂ) ^ a * reflectionCoeff a * cbz (1 - (a : ℤ)) k) •
      W.L ((a : ℤ) + k) (expL1 W v))]
  apply Finset.sum_congr rfl
  intro m _
  have ht : ∀ a ∈ Finset.range (m + 1),
      ((-1 : ℂ) ^ a * reflectionCoeff a * cbz (1 - (a : ℤ)) (m - a : ℕ)) •
          W.L ((a : ℤ) + (m - a : ℕ)) (expL1 W v) =
      ((-1 : ℂ) ^ a * reflectionCoeff a * cbz (1 - (a : ℤ)) (m - a : ℕ)) •
          W.L (m : ℤ) (expL1 W v) := by
    intro a ha
    rw [show (a : ℤ) + (m - a : ℕ) = m by have := Finset.mem_range.mp ha; omega]
  rw [Finset.sum_congr rfl ht, ← Finset.sum_smul, hb m]

/-- The entire operator identity follows from the scalar binomial identity. -/
theorem squareBracketReflectionCommutes_of_binomial (hb : ReflectionBinomialIdentity) :
    SquareBracketReflectionCommutes W := by
  intro v
  have hv : v ∈ ⨆ n : ℤ, W.grading n := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading
    (motive := fun v => contraTwist W (Lsq W 0 v) = Lsq W 0 (contraTwist W v)) hv ?_ ?_ ?_
  · intro n v hv
    by_cases hn : 0 ≤ n
    · have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
      exact contraTwist_Lsq_homogeneous hb n.toNat (hn' ▸ hv)
    · rw [W.positivity n (by omega), Submodule.mem_bot] at hv
      simp only [hv, map_zero]
  · simp only [map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem squareBracketReflection_of_binomial (hb : ReflectionBinomialIdentity) :
    SquareBracketReflection W :=
  squareBracketReflection_of_commutes (squareBracketReflectionCommutes_of_binomial hb)

end VOA.Huang.VerlindeRho
