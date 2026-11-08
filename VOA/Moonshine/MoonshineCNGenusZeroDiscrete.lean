/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroCritical
import VOA.Moonshine.MoonshineCNGenusZeroGroup

/-!
# Genus zero on the abstract interface: discreteness of the symmetry group

Shimura's finiteness lemma (Cummins–Gannon, Lemma 5.2; blueprint
`Notes/moonshine/MOON_M8_LEAN.md`). For a `J`-dominated `q`-series `f` with symmetry group
`G = symmetryGroup f`:

* an element of `G` whose entries are close to those of the identity is the identity
  (`eq_one_of_mem_symmetryGroup_of_near`: Shimizu's lemma kills the lower-left entry, the
  stabiliser of `∞` consists of integer translations);
* **finiteness**: the elements of `G` with entries bounded by `B` form a finite set
  (`finite_bounded_mem_symmetryGroup`; Bolzano–Weierstrass in `ℝ⁴` and the previous point);
* **finitely many residues**: for a fixed lower-left entry `c₀ ≠ 0`, the pairs
  `(fract (a / c₀), fract (d / c₀))` of elements `(a b; c₀ d) ∈ G` form a finite set
  (`finite_fract_diag_div_lowerLeft`): multiplying by integer translations on both sides
  normalises `a` and `d` into `[0, |c₀|)`, which bounds all entries.

Also collected here: the conjugation formula
`M (1 h; 0 1) M⁻¹ = (1 - h a c, h a²; -h c², 1 + h a c)` (`conj_glUpperUnipotent`), the
explicit inverse of a determinant-one matrix, and membership of integer translations and of
`-1` in `G`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set Matrix

/-! ### Matrix helpers -/

lemma glFinTwo_mul_apply (g h : GL (Fin 2) ℝ) (i j : Fin 2) :
    (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma glFinTwo_det_eq (g : GL (Fin 2) ℝ) : g.det.val = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
  rw [GeneralLinearGroup.val_det_apply, det_fin_two]

@[simp] lemma glOfDetOne_apply_zero_zero (a b c d : ℝ) (h : a * d - b * c = 1) :
    glOfDetOne a b c d h 0 0 = a := by simp

@[simp] lemma glOfDetOne_apply_zero_one (a b c d : ℝ) (h : a * d - b * c = 1) :
    glOfDetOne a b c d h 0 1 = b := by simp

@[simp] lemma glOfDetOne_apply_one_zero (a b c d : ℝ) (h : a * d - b * c = 1) :
    glOfDetOne a b c d h 1 0 = c := by simp

@[simp] lemma glOfDetOne_apply_one_one (a b c d : ℝ) (h : a * d - b * c = 1) :
    glOfDetOne a b c d h 1 1 = d := by simp

lemma det_entries_of_mem_symmetryGroup {f : ℍ → ℂ} {g : GL (Fin 2) ℝ}
    (hg : g ∈ symmetryGroup f) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  rw [← glFinTwo_det_eq]; exact det_val_eq_one_of_mem_symmetryGroup hg

/-- The inverse of a determinant-one matrix is its adjugate. -/
lemma glFinTwo_inv_eq {h : GL (Fin 2) ℝ} (hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1) :
    h⁻¹ = glOfDetOne (h 1 1) (-h 0 1) (-h 1 0) (h 0 0) (by linear_combination hdet) := by
  refine (inv_eq_of_mul_eq_one_left ?_)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

/-- **Conjugation of a translation**: for `det M = 1`,
`M (1 h; 0 1) M⁻¹ = (1 - h a c, h a²; -h c², 1 + h a c)` with `(a, c)` the first column of `M`. -/
lemma conj_glUpperUnipotent {M : GL (Fin 2) ℝ} (hM : M.det.val = 1) (h : ℝ) :
    M * glUpperUnipotent h * M⁻¹ =
      glOfDetOne (1 - h * M 0 0 * M 1 0) (h * M 0 0 ^ 2) (-(h * M 1 0 ^ 2))
        (1 + h * M 0 0 * M 1 0) (by ring) := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← glFinTwo_det_eq]; exact hM
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, glUpperUnipotent]
  · ring
  · linear_combination (-(h * M 0 0)) * hdet
  · ring
  · linear_combination (-(h * M 1 0)) * hdet

/-- Integer translations are symmetries of every `q`-series. -/
lemma glUpperUnipotent_intCast_mem_symmetryGroup (c : ℕ → ℂ) (n : ℤ) :
    glUpperUnipotent n ∈ symmetryGroup (qSeriesFun c) := by
  refine ⟨Units.val_eq_one.mp (glOfDetOne_det _ _ _ _ _), fun τ => ?_⟩
  have hn : (((n : ℝ) : ℂ)) = (n : ℂ) := by push_cast; rfl
  rw [← qSeriesExt_coe, coe_glUpperUnipotent_smul, hn, qSeriesExt_add_intCast c τ.im_pos n,
    qSeriesExt_coe]

/-- `-1` acts trivially on `ℍ`, so it is a symmetry of every function. -/
lemma neg_one_mem_symmetryGroup (f : ℍ → ℂ) : (-1 : GL (Fin 2) ℝ) ∈ symmetryGroup f := by
  refine ⟨Units.ext ?_, fun τ => by rw [UpperHalfPlane.neg_smul, one_smul]⟩
  simp [GeneralLinearGroup.val_det_apply, Matrix.det_neg]

/-! ### Elements near the identity -/

/-- **Elements of the symmetry group near the identity are the identity.** -/
theorem eq_one_of_mem_symmetryGroup_of_near {c : ℕ → ℂ} (hc : IsJDominated c)
    {g : GL (Fin 2) ℝ} (hg : g ∈ symmetryGroup (qSeriesFun c)) (h00 : |g 0 0 - 1| < 1)
    (h01 : |g 0 1| < 1) (h10 : |g 1 0| < 1) : g = 1 := by
  have hc0 : g 1 0 = 0 := by
    by_contra hne
    exact absurd (one_le_abs_lowerLeft_qSeriesFun hc hg hne) (not_le.mpr h10)
  have hdet := det_entries_of_mem_symmetryGroup hg
  rw [hc0, mul_zero, sub_zero] at hdet
  have hd : g 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  obtain ⟨n, hn⟩ := exists_int_smul_eq_add_of_lowerLeft_eq_zero hc hg hc0
  have hI := hn UpperHalfPlane.I
  rw [coe_smul_of_det_pos (by rw [det_val_eq_one_of_mem_symmetryGroup hg]; exact one_pos),
    num, denom, hc0, Complex.ofReal_zero, zero_mul, zero_add,
    div_eq_iff (by exact_mod_cast hd)] at hI
  have hre : g 0 1 = n * g 1 1 := by simpa using congrArg Complex.re hI
  have him : g 0 0 = g 1 1 := by simpa using congrArg Complex.im hI
  have hsq : g 0 0 * g 0 0 = 1 := by rw [him] at hdet ⊢; linarith
  have ha : g 0 0 = 1 := by
    have h' : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h' with h' | h'
    · linarith
    · exfalso
      have : g 0 0 = -1 := by linarith
      rw [this] at h00
      norm_num at h00
  have hdd : g 1 1 = 1 := by rw [← him, ha]
  have hb : g 0 1 = n := by rw [hre, hdd, mul_one]
  have hn0 : n = 0 := by
    rw [hb] at h01
    have h1 : |(n : ℝ)| < 1 := h01
    rw [← Int.cast_abs] at h1
    have h2 : |n| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hc0, hdd, hb, hn0]

/-! ### Finiteness of bounded subsets -/

lemma abs_mul_sub_mul_le {x y u v B ε : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) (hu : |u| ≤ ε)
    (hv : |v| ≤ ε) : |x * u - y * v| ≤ 2 * (B * ε) := by
  have hB : 0 ≤ B := (abs_nonneg x).trans hx
  calc |x * u - y * v| ≤ |x * u| + |y * v| := abs_sub _ _
    _ = |x| * |u| + |y| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ B * ε + B * ε :=
        add_le_add (mul_le_mul hx hu (abs_nonneg _) hB) (mul_le_mul hy hv (abs_nonneg _) hB)
    _ = 2 * (B * ε) := by ring

/-- Two elements of the symmetry group with entries bounded by `B` and entrywise closer than
`1 / (4 B + 4)` are equal. -/
theorem eq_of_mem_symmetryGroup_of_close {c : ℕ → ℂ} (hc : IsJDominated c) {B : ℝ}
    {g h : GL (Fin 2) ℝ} (hg : g ∈ symmetryGroup (qSeriesFun c))
    (hh : h ∈ symmetryGroup (qSeriesFun c)) (hhB : ∀ i j, |h i j| ≤ B)
    (hclose : ∀ i j, |g i j - h i j| ≤ 1 / (4 * B + 4)) : g = h := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hhB 0 0)
  have hdet := det_entries_of_mem_symmetryGroup hh
  have hk := (symmetryGroup _).mul_mem ((symmetryGroup _).inv_mem hh) hg
  set ε : ℝ := 1 / (4 * B + 4) with hε
  have h4 : 0 < 4 * B + 4 := by linarith
  have hsmall : 2 * (B * ε) < 1 := by
    have : 2 * (B * ε) = 2 * B / (4 * B + 4) := by rw [hε]; field_simp
    rw [this, div_lt_one h4]
    linarith
  have hinv := glFinTwo_inv_eq hdet
  have e00 : (h⁻¹ * g) 0 0 - 1 = h 1 1 * (g 0 0 - h 0 0) - h 0 1 * (g 1 0 - h 1 0) := by
    rw [glFinTwo_mul_apply, hinv]
    simp only [glOfDetOne_apply_zero_zero, glOfDetOne_apply_zero_one]
    linear_combination hdet
  have e01 : (h⁻¹ * g) 0 1 = h 1 1 * (g 0 1 - h 0 1) - h 0 1 * (g 1 1 - h 1 1) := by
    rw [glFinTwo_mul_apply, hinv]
    simp only [glOfDetOne_apply_zero_zero, glOfDetOne_apply_zero_one]
    ring
  have e10 : (h⁻¹ * g) 1 0 = h 0 0 * (g 1 0 - h 1 0) - h 1 0 * (g 0 0 - h 0 0) := by
    rw [glFinTwo_mul_apply, hinv]
    simp only [glOfDetOne_apply_one_zero, glOfDetOne_apply_one_one]
    ring
  have b00 : |(h⁻¹ * g) 0 0 - 1| < 1 := by
    rw [e00]
    exact (abs_mul_sub_mul_le (hhB 1 1) (hhB 0 1) (hclose 0 0) (hclose 1 0)).trans_lt hsmall
  have b01 : |(h⁻¹ * g) 0 1| < 1 := by
    rw [e01]
    exact (abs_mul_sub_mul_le (hhB 1 1) (hhB 0 1) (hclose 0 1) (hclose 1 1)).trans_lt hsmall
  have b10 : |(h⁻¹ * g) 1 0| < 1 := by
    rw [e10]
    exact (abs_mul_sub_mul_le (hhB 0 0) (hhB 1 0) (hclose 1 0) (hclose 0 0)).trans_lt hsmall
  have hk1 := eq_one_of_mem_symmetryGroup_of_near hc hk b00 b01 b10
  exact (inv_mul_eq_one.mp hk1).symm

/-- **Shimura's finiteness lemma**: the elements of the symmetry group of a `J`-dominated
`q`-series with all entries bounded by `B` form a finite set. -/
theorem finite_bounded_mem_symmetryGroup {c : ℕ → ℂ} (hc : IsJDominated c) (B : ℝ) :
    {g : GL (Fin 2) ℝ | g ∈ symmetryGroup (qSeriesFun c) ∧ ∀ i j, |g i j| ≤ B}.Finite := by
  by_contra hinf
  set S := {g : GL (Fin 2) ℝ | g ∈ symmetryGroup (qSeriesFun c) ∧ ∀ i j, |g i j| ≤ B}
    with hSdef
  have hS : S.Infinite := hinf
  let e := hS.natEmbedding
  have hB0 : 0 ≤ B := by
    obtain ⟨x, hx⟩ := hS.nonempty
    exact (abs_nonneg _).trans (hx.2 0 0)
  let v : ℕ → (Fin 2 → Fin 2 → ℝ) := fun n i j => ((e n : S) : GL (Fin 2) ℝ) i j
  have hvb : ∀ n, v n ∈ Metric.closedBall (0 : Fin 2 → Fin 2 → ℝ) B := by
    intro n
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hB0).mpr fun i =>
      (pi_norm_le_iff_of_nonneg hB0).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    exact (e n).2.2 i j
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hvb
  set ε : ℝ := 1 / (4 * B + 4) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  have h1 : dist (v (φ n₀)) a < ε / 2 := hn₀ n₀ le_rfl
  have h2 : dist (v (φ (n₀ + 1))) a < ε / 2 := hn₀ (n₀ + 1) (Nat.le_succ n₀)
  have hd : dist (v (φ n₀)) (v (φ (n₀ + 1))) < ε := by
    calc dist (v (φ n₀)) (v (φ (n₀ + 1)))
        ≤ dist (v (φ n₀)) a + dist a (v (φ (n₀ + 1))) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by rw [dist_comm a]; exact add_lt_add h1 h2
      _ = ε := by ring
  have hentry : ∀ i j, |((e (φ n₀) : S) : GL (Fin 2) ℝ) i j -
      ((e (φ (n₀ + 1)) : S) : GL (Fin 2) ℝ) i j| ≤ ε := by
    intro i j
    have h3 : dist (v (φ n₀) i j) (v (φ (n₀ + 1)) i j) ≤ dist (v (φ n₀)) (v (φ (n₀ + 1))) :=
      (dist_le_pi_dist (v (φ n₀) i) (v (φ (n₀ + 1)) i) j).trans (dist_le_pi_dist _ _ i)
    rw [Real.dist_eq] at h3
    exact h3.trans hd.le
  have heq := eq_of_mem_symmetryGroup_of_close hc (e (φ n₀)).2.1 (e (φ (n₀ + 1))).2.1
    (e (φ (n₀ + 1))).2.2 hentry
  have := e.injective (Subtype.ext heq)
  exact absurd this (hφ (Nat.lt_succ_self n₀)).ne

/-! ### Finitely many residues for a fixed lower-left entry -/

/-- **Finitely many residues**: for `c₀ ≠ 0`, the pairs `(fract (a / c₀), fract (d / c₀))`
of elements `(a b; c₀ d)` of the symmetry group form a finite set. -/
theorem finite_fract_diag_div_lowerLeft {c : ℕ → ℂ} (hc : IsJDominated c) {c₀ : ℝ}
    (hc₀ : c₀ ≠ 0) :
    ((fun g : GL (Fin 2) ℝ => (Int.fract (g 0 0 / c₀), Int.fract (g 1 1 / c₀))) ''
      {g | g ∈ symmetryGroup (qSeriesFun c) ∧ g 1 0 = c₀}).Finite := by
  have habs : 0 < |c₀| := abs_pos.mpr hc₀
  set B : ℝ := |c₀| + (c₀ ^ 2 + 1) / |c₀| with hB
  refine ((finite_bounded_mem_symmetryGroup hc B).image
    (fun m : GL (Fin 2) ℝ => (m 0 0 / c₀, m 1 1 / c₀))).subset ?_
  rintro _ ⟨g, ⟨hg, hgc⟩, rfl⟩
  set n₁ : ℤ := -⌊g 0 0 / c₀⌋ with hn₁
  set n₂ : ℤ := -⌊g 1 1 / c₀⌋ with hn₂
  set m := glUpperUnipotent n₁ * g * glUpperUnipotent n₂ with hmdef
  have hm : m ∈ symmetryGroup (qSeriesFun c) :=
    (symmetryGroup _).mul_mem ((symmetryGroup _).mul_mem
      (glUpperUnipotent_intCast_mem_symmetryGroup c n₁) hg)
      (glUpperUnipotent_intCast_mem_symmetryGroup c n₂)
  have m00 : m 0 0 = g 0 0 + n₁ * c₀ := by
    rw [hmdef, glFinTwo_mul_apply, glFinTwo_mul_apply, glFinTwo_mul_apply]
    simp [glUpperUnipotent, hgc]
  have m10 : m 1 0 = c₀ := by
    rw [hmdef, glFinTwo_mul_apply, glFinTwo_mul_apply, glFinTwo_mul_apply]
    simp [glUpperUnipotent, hgc]
  have m11 : m 1 1 = c₀ * n₂ + g 1 1 := by
    rw [hmdef, glFinTwo_mul_apply, glFinTwo_mul_apply, glFinTwo_mul_apply]
    simp [glUpperUnipotent, hgc]
  have hf1 : m 0 0 / c₀ = Int.fract (g 0 0 / c₀) := by
    rw [m00, Int.fract, hn₁]; push_cast; field_simp; ring
  have hf2 : m 1 1 / c₀ = Int.fract (g 1 1 / c₀) := by
    rw [m11, Int.fract, hn₂]; push_cast; field_simp; ring
  have hb1 : |m 0 0| ≤ |c₀| := by
    have : m 0 0 = c₀ * Int.fract (g 0 0 / c₀) := by rw [← hf1]; field_simp
    rw [this, abs_mul, abs_of_nonneg (Int.fract_nonneg (g 0 0 / c₀))]
    exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
  have hb2 : |m 1 1| ≤ |c₀| := by
    have : m 1 1 = c₀ * Int.fract (g 1 1 / c₀) := by rw [← hf2]; field_simp
    rw [this, abs_mul, abs_of_nonneg (Int.fract_nonneg (g 1 1 / c₀))]
    exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
  have hdetm := det_entries_of_mem_symmetryGroup hm
  rw [m10] at hdetm
  have hm01 : m 0 1 = (m 0 0 * m 1 1 - 1) / c₀ := by
    field_simp; linear_combination -hdetm
  have hb3 : |m 0 1| ≤ (c₀ ^ 2 + 1) / |c₀| := by
    rw [hm01, abs_div]
    refine div_le_div_of_nonneg_right ?_ habs.le
    calc |m 0 0 * m 1 1 - 1| ≤ |m 0 0 * m 1 1| + |(1 : ℝ)| := abs_sub _ _
      _ = |m 0 0| * |m 1 1| + 1 := by rw [abs_mul, abs_one]
      _ ≤ |c₀| * |c₀| + 1 := by gcongr
      _ = c₀ ^ 2 + 1 := by rw [← abs_mul, abs_mul_self, sq]
  have hBc : |c₀| ≤ B := le_add_of_nonneg_right (by positivity)
  have hB2 : (c₀ ^ 2 + 1) / |c₀| ≤ B := le_add_of_nonneg_left habs.le
  refine ⟨m, ⟨hm, fun i j => ?_⟩, by simp only [hf1, hf2]⟩
  fin_cases i <;> fin_cases j
  · exact hb1.trans hBc
  · exact hb3.trans hB2
  · simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue]; rw [m10]; exact hBc
  · exact hb2.trans hBc

/-- Finitely many residues `fract (a / c₀)` of upper-left entries. -/
theorem finite_fract_upperLeft_div_lowerLeft {c : ℕ → ℂ} (hc : IsJDominated c) {c₀ : ℝ}
    (hc₀ : c₀ ≠ 0) :
    ((fun g : GL (Fin 2) ℝ => Int.fract (g 0 0 / c₀)) ''
      {g | g ∈ symmetryGroup (qSeriesFun c) ∧ g 1 0 = c₀}).Finite :=
  ((finite_fract_diag_div_lowerLeft hc hc₀).image Prod.fst).subset (by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩)

/-- Finitely many residues `fract (d / c₀)` of lower-right entries. -/
theorem finite_fract_lowerRight_div_lowerLeft {c : ℕ → ℂ} (hc : IsJDominated c) {c₀ : ℝ}
    (hc₀ : c₀ ≠ 0) :
    ((fun g : GL (Fin 2) ℝ => Int.fract (g 1 1 / c₀)) ''
      {g | g ∈ symmetryGroup (qSeriesFun c) ∧ g 1 0 = c₀}).Finite :=
  ((finite_fract_diag_div_lowerLeft hc hc₀).image Prod.snd).subset (by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩)

end VOA.Moonshine.ConwayNorton
