/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroAnalytic
import VOA.Moonshine.MoonshineCNGenusZeroInterface
import VOA.Moonshine.MoonshineCNGammaZeroFamily

/-!
# Genus zero on the abstract interface: Shimizu's lemma for symmetry groups

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. If a holomorphic `ψ : ℍ → ℂ` is invariant under
`T = (1 1; 0 1)` and under some `g = (a b; c d)` of determinant `1` with `0 < |c| < 1`, then `ψ`
is constant (`eq_of_invariant_of_lowerLeft_abs_lt_one`). Hence (**Shimizu's lemma**) every
element `g` of the symmetry group of a non-constant holomorphic `f` with `T ∈ symmetryGroup f`
has `g 1 0 = 0` or `|g 1 0| ≥ 1` (`one_le_abs_lowerLeft_of_mem_symmetryGroup`); for a
`J`-dominated `q`-series this holds unconditionally (`one_le_abs_lowerLeft_qSeriesFun`).

The proof generalises the Shimizu sequence of `MoonshineCNGammaZeroShimizu` (which starts at
`(1 0; y 1)`) to an arbitrary starting matrix: `B 0 = g`, `B (n+1) = B n T (B n)⁻¹`, whose
lower-left entries are `c_{n+1} = −c_n²`, so `|c_n| ≤ |c|^{n+1} → 0`, while the upper-left
entries `a_{n+1} = 1 − a_n c_n` stay bounded and tend to `1`. The witnesses
`C n = B (n+1) T⁻¹ → 1` act non-trivially, and `eq_of_invariant_of_entries_tendsto_one` applies.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Matrix
open scoped MatrixGroups Manifold

/-! ### Shimizu's sequence from an arbitrary start -/

/-- The pair `(a n, c n)` of upper-left and lower-left entries of Shimizu's sequence started at a
matrix with entries `(a, c)` in the first column. -/
noncomputable def shimizuPairFrom (a c : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, c)
  | n + 1 => (1 - (shimizuPairFrom a c n).1 * (shimizuPairFrom a c n).2,
      -((shimizuPairFrom a c n).2 ^ 2))

/-- Shimizu's sequence started at `g`: `B 0 = g`, `B (n + 1) = (1 - a c, a²; -c², 1 + a c)` with
`(a, c) = shimizuPairFrom (g 0 0) (g 1 0) n`. -/
noncomputable def shimizuMatrixFrom (g : GL (Fin 2) ℝ) : ℕ → GL (Fin 2) ℝ
  | 0 => g
  | n + 1 => glOfDetOne
      (1 - (shimizuPairFrom (g 0 0) (g 1 0) n).1 * (shimizuPairFrom (g 0 0) (g 1 0) n).2)
      ((shimizuPairFrom (g 0 0) (g 1 0) n).1 ^ 2) (-((shimizuPairFrom (g 0 0) (g 1 0) n).2 ^ 2))
      (1 + (shimizuPairFrom (g 0 0) (g 1 0) n).1 * (shimizuPairFrom (g 0 0) (g 1 0) n).2)
      (by ring)

lemma shimizuMatrixFrom_entry00 (g : GL (Fin 2) ℝ) (n : ℕ) :
    shimizuMatrixFrom g n 0 0 = (shimizuPairFrom (g 0 0) (g 1 0) n).1 := by
  cases n <;> simp [shimizuMatrixFrom, shimizuPairFrom]

lemma shimizuMatrixFrom_entry10 (g : GL (Fin 2) ℝ) (n : ℕ) :
    shimizuMatrixFrom g n 1 0 = (shimizuPairFrom (g 0 0) (g 1 0) n).2 := by
  cases n <;> simp [shimizuMatrixFrom, shimizuPairFrom]

lemma shimizuMatrixFrom_det {g : GL (Fin 2) ℝ} (hg : g.det.val = 1) (n : ℕ) :
    shimizuMatrixFrom g n 0 0 * shimizuMatrixFrom g n 1 1 -
      shimizuMatrixFrom g n 0 1 * shimizuMatrixFrom g n 1 0 = 1 := by
  cases n with
  | zero =>
    rw [GeneralLinearGroup.val_det_apply, det_fin_two] at hg
    simpa [shimizuMatrixFrom] using hg
  | succ n => simp [shimizuMatrixFrom]; ring

/-- The defining relation `B (n + 1) * B n = B n * T`. -/
lemma shimizuMatrixFrom_succ_mul {g : GL (Fin 2) ℝ} (hg : g.det.val = 1) (n : ℕ) :
    shimizuMatrixFrom g (n + 1) * shimizuMatrixFrom g n =
      shimizuMatrixFrom g n * glUpperUnipotent 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set p := shimizuPairFrom (g 0 0) (g 1 0) n with hp
  have hB : (shimizuMatrixFrom g n : Matrix (Fin 2) (Fin 2) ℝ) =
      !![p.1, shimizuMatrixFrom g n 0 1; p.2, shimizuMatrixFrom g n 1 1] := by
    rw [hp, ← shimizuMatrixFrom_entry00, ← shimizuMatrixFrom_entry10]
    exact eta_fin_two _
  have hdet : p.1 * shimizuMatrixFrom g n 1 1 - shimizuMatrixFrom g n 0 1 * p.2 = 1 := by
    rw [hp, ← shimizuMatrixFrom_entry00, ← shimizuMatrixFrom_entry10]
    exact shimizuMatrixFrom_det hg n
  rw [hB]
  simp only [shimizuMatrixFrom, glUpperUnipotent, glOfDetOne_val]
  exact shimizu_step_identity _ _ _ _ hdet

lemma shimizuMatrixFrom_mem {H : Subgroup (GL (Fin 2) ℝ)} {g : GL (Fin 2) ℝ}
    (hg : g.det.val = 1) (hT : glUpperUnipotent 1 ∈ H) (hgH : g ∈ H) (n : ℕ) :
    shimizuMatrixFrom g n ∈ H := by
  induction n with
  | zero => exact hgH
  | succ n ih =>
    rw [eq_mul_inv_of_mul_eq (shimizuMatrixFrom_succ_mul hg n)]
    exact H.mul_mem (H.mul_mem ih hT) (H.inv_mem ih)

/-- The non-discreteness witness `C n = B (n + 1) T⁻¹`. -/
noncomputable def shimizuWitnessFrom (g : GL (Fin 2) ℝ) (n : ℕ) : GL (Fin 2) ℝ :=
  shimizuMatrixFrom g (n + 1) * (glUpperUnipotent 1)⁻¹

lemma shimizuWitnessFrom_mem {H : Subgroup (GL (Fin 2) ℝ)} {g : GL (Fin 2) ℝ}
    (hg : g.det.val = 1) (hT : glUpperUnipotent 1 ∈ H) (hgH : g ∈ H) (n : ℕ) :
    shimizuWitnessFrom g n ∈ H :=
  H.mul_mem (shimizuMatrixFrom_mem hg hT hgH (n + 1)) (H.inv_mem hT)

lemma shimizuWitnessFrom_val (g : GL (Fin 2) ℝ) (n : ℕ) :
    ((shimizuWitnessFrom g n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - (shimizuPairFrom (g 0 0) (g 1 0) n).1 * (shimizuPairFrom (g 0 0) (g 1 0) n).2,
          (shimizuPairFrom (g 0 0) (g 1 0) n).1 ^ 2 - 1 +
            (shimizuPairFrom (g 0 0) (g 1 0) n).1 * (shimizuPairFrom (g 0 0) (g 1 0) n).2;
        -((shimizuPairFrom (g 0 0) (g 1 0) n).2 ^ 2),
          (shimizuPairFrom (g 0 0) (g 1 0) n).2 ^ 2 + 1 +
            (shimizuPairFrom (g 0 0) (g 1 0) n).1 * (shimizuPairFrom (g 0 0) (g 1 0) n).2] := by
  rw [shimizuWitnessFrom, glUpperUnipotent_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shimizuMatrixFrom, glUpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma shimizuWitnessFrom_det (g : GL (Fin 2) ℝ) (n : ℕ) :
    0 < (shimizuWitnessFrom g n).det.val := by
  rw [GeneralLinearGroup.val_det_apply, shimizuWitnessFrom_val, det_fin_two_of]
  set a := (shimizuPairFrom (g 0 0) (g 1 0) n).1
  set c := (shimizuPairFrom (g 0 0) (g 1 0) n).2
  have h : (1 - a * c) * (c ^ 2 + 1 + a * c) - (a ^ 2 - 1 + a * c) * -(c ^ 2) = 1 := by ring
  rw [h]
  exact one_pos

/-! ### Estimates for the entries -/

variable {a c : ℝ}

lemma shimizuPairFrom_snd_ne_zero (hc : c ≠ 0) (n : ℕ) : (shimizuPairFrom a c n).2 ≠ 0 := by
  induction n with
  | zero => exact hc
  | succ n ih => simpa [shimizuPairFrom] using ih

lemma shimizuPairFrom_snd_abs_le (hc1 : |c| ≤ 1) (n : ℕ) :
    |(shimizuPairFrom a c n).2| ≤ |c| ^ (n + 1) := by
  induction n with
  | zero => simp [shimizuPairFrom]
  | succ n ih =>
    simp only [shimizuPairFrom, abs_neg, abs_pow]
    calc |(shimizuPairFrom a c n).2| ^ 2 ≤ (|c| ^ (n + 1)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) ih 2
      _ = |c| ^ (2 * n + 2) := by ring
      _ ≤ |c| ^ (n + 1 + 1) := pow_le_pow_of_le_one (abs_nonneg c) hc1 (by omega)

lemma shimizuPairFrom_snd_abs_le_self (hc1 : |c| ≤ 1) (n : ℕ) :
    |(shimizuPairFrom a c n).2| ≤ |c| :=
  (shimizuPairFrom_snd_abs_le hc1 n).trans
    (by simpa using pow_le_pow_of_le_one (abs_nonneg c) hc1 (Nat.succ_pos n))

lemma shimizuPairFrom_fst_abs_le (hc1 : |c| < 1) (n : ℕ) :
    |(shimizuPairFrom a c n).1| ≤ max |a| (1 / (1 - |c|)) := by
  have h1c : 0 < 1 - |c| := by linarith
  set A := max |a| (1 / (1 - |c|)) with hAdef
  have hA : 1 / (1 - |c|) ≤ A := le_max_right _ _
  have hA' : 1 ≤ A * (1 - |c|) := by rwa [div_le_iff₀ h1c] at hA
  have hA0 : 0 ≤ A := (abs_nonneg a).trans (le_max_left _ _)
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    simp only [shimizuPairFrom]
    have hcn := shimizuPairFrom_snd_abs_le_self (a := a) hc1.le n
    calc |1 - (shimizuPairFrom a c n).1 * (shimizuPairFrom a c n).2|
        ≤ |(1 : ℝ)| + |(shimizuPairFrom a c n).1 * (shimizuPairFrom a c n).2| := abs_sub _ _
      _ = 1 + |(shimizuPairFrom a c n).1| * |(shimizuPairFrom a c n).2| := by
          rw [abs_one, abs_mul]
      _ ≤ 1 + A * |c| := by
          have := mul_le_mul ih hcn (abs_nonneg _) hA0
          linarith
      _ ≤ A := by nlinarith

lemma shimizuPairFrom_snd_tendsto (hc1 : |c| < 1) :
    Tendsto (fun n => (shimizuPairFrom a c n).2) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => |c| ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg c) hc1).comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero_norm (fun n => by
    rw [Real.norm_eq_abs]; exact shimizuPairFrom_snd_abs_le hc1.le n) hpow

lemma shimizuPairFrom_fst_tendsto (hc1 : |c| < 1) :
    Tendsto (fun n => (shimizuPairFrom a c n).1) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hc := shimizuPairFrom_snd_tendsto (a := a) hc1
  have hbound : ∀ n, ‖(shimizuPairFrom a c (n + 1)).1 - 1‖ ≤
      max |a| (1 / (1 - |c|)) * |(shimizuPairFrom a c n).2| := by
    intro n
    simp only [shimizuPairFrom, Real.norm_eq_abs, sub_sub_cancel_left, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_right (shimizuPairFrom_fst_abs_le hc1 n) (abs_nonneg _)
  have hlim : Tendsto (fun n => max |a| (1 / (1 - |c|)) * |(shimizuPairFrom a c n).2|) atTop
      (𝓝 0) := by
    simpa using (hc.abs).const_mul (max |a| (1 / (1 - |c|)))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) hbound hlim)

/-- **Shimizu's sequence from `g` converges to the identity** when `|g 1 0| < 1`. -/
theorem shimizuWitnessFrom_entries_tendsto {g : GL (Fin 2) ℝ} (hc1 : |g 1 0| < 1)
    (i j : Fin 2) :
    Tendsto (fun n => (shimizuWitnessFrom g n : Matrix (Fin 2) (Fin 2) ℝ) i j) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)) := by
  have ha := shimizuPairFrom_fst_tendsto (a := g 0 0) hc1
  have hc := shimizuPairFrom_snd_tendsto (a := g 0 0) hc1
  simp only [shimizuWitnessFrom_val]
  fin_cases i <;> fin_cases j
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (ha.mul hc)
  · simpa using ((ha.pow 2).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).add (ha.mul hc)
  · simpa using (hc.pow 2).neg
  · simpa using ((hc.pow 2).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).add (ha.mul hc)

/-- Each witness acts non-trivially when `g 1 0 ≠ 0`. -/
theorem shimizuWitnessFrom_moves {g : GL (Fin 2) ℝ} (hc0 : g 1 0 ≠ 0) (n : ℕ) :
    ∃ τ : ℍ, shimizuWitnessFrom g n • τ ≠ τ := by
  refine exists_smul_ne_of_lowerLeft_ne_zero (shimizuWitnessFrom_det g n) ?_
  have h : (shimizuWitnessFrom g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      -((shimizuPairFrom (g 0 0) (g 1 0) n).2 ^ 2) := by
    rw [shimizuWitnessFrom_val]; simp
  rw [h, neg_ne_zero]
  exact pow_ne_zero 2 (shimizuPairFrom_snd_ne_zero hc0 n)

/-! ### Constancy and Shimizu's lemma -/

/-- **Invariance under `T` and a matrix with `0 < |c| < 1` forces constancy.** -/
theorem eq_of_invariant_of_lowerLeft_abs_lt_one {ψ : ℍ → ℂ}
    (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ) {g : GL (Fin 2) ℝ} (hdet : g.det.val = 1)
    (hc0 : g 1 0 ≠ 0) (hc1 : |g 1 0| < 1) (hT : ∀ τ, ψ (glUpperUnipotent 1 • τ) = ψ τ)
    (hg : ∀ τ, ψ (g • τ) = ψ τ) (τ σ : ℍ) : ψ τ = ψ σ :=
  eq_of_invariant_of_entries_tendsto_one hψ (shimizuWitnessFrom_entries_tendsto hc1)
    (shimizuWitnessFrom_moves hc0)
    (fun n => shimizuWitnessFrom_mem (H := precompInvariantSubgroup ψ) hdet hT hg n) τ σ

lemma det_val_eq_one_of_mem_symmetryGroup {f : ℍ → ℂ} {g : GL (Fin 2) ℝ}
    (hg : g ∈ symmetryGroup f) : g.det.val = 1 := by
  rw [hg.1, Units.val_one]

/-- **Shimizu's lemma.** If `f` is holomorphic and non-constant and `T ∈ symmetryGroup f`, every
`g ∈ symmetryGroup f` with `g 1 0 ≠ 0` has `|g 1 0| ≥ 1`. -/
theorem one_le_abs_lowerLeft_of_mem_symmetryGroup {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ∃ τ σ : ℍ, f τ ≠ f σ)
    (hT : glUpperUnipotent 1 ∈ symmetryGroup f) {g : GL (Fin 2) ℝ}
    (hg : g ∈ symmetryGroup f) (hc0 : g 1 0 ≠ 0) : 1 ≤ |g 1 0| := by
  by_contra h
  rw [not_le] at h
  obtain ⟨τ, σ, hne⟩ := hnc
  exact hne (eq_of_invariant_of_lowerLeft_abs_lt_one hf
    (det_val_eq_one_of_mem_symmetryGroup hg) hc0 h hT.2 hg.2 τ σ)

/-! ### Application to `J`-dominated `q`-series -/

lemma glUpperUnipotent_one_mem_symmetryGroup_qSeriesFun (c : ℕ → ℂ) :
    glUpperUnipotent 1 ∈ symmetryGroup (qSeriesFun c) :=
  ⟨Units.val_eq_one.mp (glOfDetOne_det _ _ _ _ _), qSeriesFun_periodic c⟩

/-- A `J`-dominated `q`-series is not constant (it has a pole at `i∞`). -/
lemma qSeriesFun_exists_ne {c : ℕ → ℂ} (hc : IsJDominated c) :
    ∃ τ σ : ℍ, qSeriesFun c τ ≠ qSeriesFun c σ := by
  by_contra h
  have h : ∀ τ σ : ℍ, qSeriesFun c τ = qSeriesFun c σ := fun τ σ =>
    not_not.mp fun hne => h ⟨τ, σ, hne⟩
  have hsmall := (tendsto_qSeriesFun_sub_inv_qPar hc).eventually (Metric.ball_mem_nhds 0 one_pos)
  have hlarge := tendsto_norm_inv_qPar_atTop.eventually_gt_atTop
    (‖qSeriesFun c UpperHalfPlane.I‖ + 1)
  obtain ⟨τ, hτ1, hτ2⟩ := (hsmall.and hlarge).exists
  rw [dist_zero_right, h τ UpperHalfPlane.I] at hτ1
  have htri : ‖(qPar τ)⁻¹‖ ≤
      ‖qSeriesFun c UpperHalfPlane.I‖ + ‖qSeriesFun c UpperHalfPlane.I - (qPar τ)⁻¹‖ := by
    calc ‖(qPar τ)⁻¹‖ = ‖qSeriesFun c UpperHalfPlane.I -
          (qSeriesFun c UpperHalfPlane.I - (qPar τ)⁻¹)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- **Shimizu's lemma for `J`-dominated `q`-series.** -/
theorem one_le_abs_lowerLeft_qSeriesFun {c : ℕ → ℂ} (hc : IsJDominated c) {g : GL (Fin 2) ℝ}
    (hg : g ∈ symmetryGroup (qSeriesFun c)) (hc0 : g 1 0 ≠ 0) : 1 ≤ |g 1 0| :=
  one_le_abs_lowerLeft_of_mem_symmetryGroup (mdifferentiable_qSeriesFun hc)
    (qSeriesFun_exists_ne hc) (glUpperUnipotent_one_mem_symmetryGroup_qSeriesFun c) hg hc0

end VOA.Moonshine.ConwayNorton
