/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Instances.Matrix

/-!
# Invariance under a non-discrete set of Möbius maps forces constancy

This file supplies the analytic engine of the `Γ₁ ⇒ Γ₀` upgrade (blueprint
`Notes/moonshine/MOON_MONSTER.md`): a holomorphic function on `ℍ` that is invariant under a
sequence of real Möbius maps `C n → 1` acting non-trivially is constant
(`eq_of_invariant_of_entries_tendsto_one`, `eq_of_invariant_of_tendsto_one`), and Shimizu's
sequence shows that invariance under `τ ↦ τ + 1` and `τ ↦ τ / (y τ + 1)` with `0 < y < 1`
already produces such a sequence (`eq_of_invariant_upper_lower_unipotent`).

The proof of constancy avoids the inverse function theorem: a point moved by infinitely many
`C n` is an accumulation point of a level set, and the identity theorem
(`UpperHalfPlane.eq_zero_of_frequently`) does the rest.  A real Möbius map of positive determinant
fixing two points of `ℍ` is the identity (`smul_eq_self_of_two_fixed`).
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Matrix
open scoped MatrixGroups Manifold

/-! ### Precomposition-invariance subgroup -/

/-- The subgroup of `GL(2, ℝ)` of elements `g` with `ψ (g • τ) = ψ τ` for every `τ ∈ ℍ`. -/
def precompInvariantSubgroup (ψ : ℍ → ℂ) : Subgroup (GL (Fin 2) ℝ) where
  carrier := {g | ∀ τ : ℍ, ψ (g • τ) = ψ τ}
  mul_mem' {a b} ha hb τ := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_smul, ha, hb]
  one_mem' τ := by simp
  inv_mem' {a} ha τ := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [← ha (a⁻¹ • τ), smul_inv_smul]

@[simp] lemma mem_precompInvariantSubgroup {ψ : ℍ → ℂ} {g : GL (Fin 2) ℝ} :
    g ∈ precompInvariantSubgroup ψ ↔ ∀ τ : ℍ, ψ (g • τ) = ψ τ :=
  Iff.rfl

/-! ### Elements of `GL(2, ℝ)` from entries -/

/-- The element `(a b; c d)` of `GL(2, ℝ)`, for `a d - b c = 1`. -/
noncomputable def glOfDetOne (a b c d : ℝ) (h : a * d - b * c = 1) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rw [det_fin_two_of, h]; exact one_ne_zero)

@[simp] lemma glOfDetOne_val (a b c d : ℝ) (h : a * d - b * c = 1) :
    ((glOfDetOne a b c d h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
  rfl

lemma glOfDetOne_det (a b c d : ℝ) (h : a * d - b * c = 1) :
    (glOfDetOne a b c d h).det.val = 1 := by
  rw [GeneralLinearGroup.val_det_apply, glOfDetOne_val, det_fin_two_of, h]

/-- The translation `τ ↦ τ + x`, as `(1 x; 0 1) ∈ GL(2, ℝ)`. -/
noncomputable def glUpperUnipotent (x : ℝ) : GL (Fin 2) ℝ := glOfDetOne 1 x 0 1 (by ring)

/-- The map `τ ↦ τ / (y τ + 1)`, as `(1 0; y 1) ∈ GL(2, ℝ)`. -/
noncomputable def glLowerUnipotent (y : ℝ) : GL (Fin 2) ℝ := glOfDetOne 1 0 y 1 (by ring)

lemma glUpperUnipotent_mul (x x' : ℝ) :
    glUpperUnipotent x * glUpperUnipotent x' = glUpperUnipotent (x + x') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glUpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma glUpperUnipotent_inv (x : ℝ) : (glUpperUnipotent x)⁻¹ = glUpperUnipotent (-x) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [glUpperUnipotent_mul, add_neg_cancel]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glUpperUnipotent]

lemma coe_glUpperUnipotent_smul (x : ℝ) (τ : ℍ) :
    ((glUpperUnipotent x • τ : ℍ) : ℂ) = τ + x := by
  rw [coe_smul_of_det_pos (by rw [glUpperUnipotent, glOfDetOne_det]; exact one_pos)]
  simp [num, denom, glUpperUnipotent]

lemma coe_glLowerUnipotent_smul (y : ℝ) (τ : ℍ) :
    ((glLowerUnipotent y • τ : ℍ) : ℂ) = τ / (y * τ + 1) := by
  rw [coe_smul_of_det_pos (by rw [glLowerUnipotent, glOfDetOne_det]; exact one_pos)]
  simp [num, denom, glLowerUnipotent]

/-! ### Fixed points of real Möbius maps -/

/-- The fixed-point equation `c τ² + (d - a) τ - b = 0` of `(a b; c d)`. -/
lemma fixed_point_quadratic {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) {τ : ℍ} (h : g • τ = τ) :
    ((g 1 0 : ℝ) : ℂ) * (τ : ℂ) ^ 2 + ((g 1 1 - g 0 0 : ℝ) : ℂ) * τ - (g 0 1 : ℂ) = 0 := by
  have h1 := congrArg UpperHalfPlane.coe h
  rw [coe_smul_of_det_pos hg, div_eq_iff (denom_ne_zero g τ)] at h1
  simp only [num, denom] at h1
  push_cast
  linear_combination -h1

/-- A real Möbius map of positive determinant fixing two distinct points of `ℍ` is scalar. -/
theorem entries_of_two_fixed {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) {τ₁ τ₂ : ℍ}
    (hne : τ₁ ≠ τ₂) (h₁ : g • τ₁ = τ₁) (h₂ : g • τ₂ = τ₂) :
    g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 1 1 = g 0 0 := by
  have q₁ := fixed_point_quadratic hg h₁
  have q₂ := fixed_point_quadratic hg h₂
  set A : ℝ := g 1 0 with hAdef
  set B : ℝ := g 1 1 - g 0 0 with hBdef
  have hprod : ((τ₁ : ℂ) - τ₂) * ((A : ℂ) * (τ₁ + τ₂) + B) = 0 := by
    linear_combination q₁ - q₂
  have hsub : ((τ₁ : ℂ) - τ₂) ≠ 0 := sub_ne_zero.mpr fun h => hne (UpperHalfPlane.ext h)
  have hlin : (A : ℂ) * (τ₁ + τ₂) + B = 0 := (mul_eq_zero.mp hprod).resolve_left hsub
  have him := congrArg Complex.im hlin
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at him
  have hA : A = 0 := by
    have hpos : 0 < τ₁.im + τ₂.im := add_pos τ₁.im_pos τ₂.im_pos
    have : A * (τ₁.im + τ₂.im) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hpos.ne'
  have hB : B = 0 := by
    rw [hA] at hlin
    simpa using hlin
  refine ⟨hA, ?_, by linarith [hB, hBdef]⟩
  rw [hA, hB] at q₁
  simpa using q₁

/-- A real Möbius map of positive determinant that is scalar acts trivially. -/
theorem smul_eq_self_of_scalar {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (h10 : g 1 0 = 0)
    (h01 : g 0 1 = 0) (h11 : g 1 1 = g 0 0) (τ : ℍ) : g • τ = τ := by
  have hdet : g.det.val = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
    rw [GeneralLinearGroup.val_det_apply, det_fin_two]
  have h00 : g 0 0 ≠ 0 := by
    intro h0
    rw [hdet, h0, h01] at hg
    simp at hg
  ext1
  rw [coe_smul_of_det_pos hg]
  simp only [num, denom, h10, h01, h11, Complex.ofReal_zero, zero_mul, zero_add, add_zero]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr h00)

/-- The point `2i ∈ ℍ`. -/
def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

lemma I_ne_twoI : UpperHalfPlane.I ≠ twoI := by
  intro h
  have h' : Complex.I = 2 * Complex.I := congrArg UpperHalfPlane.coe h
  have h0 : Complex.I = 0 := by linear_combination -h'
  exact Complex.I_ne_zero h0

/-- A real Möbius map of positive determinant acting non-trivially moves `i` or `2i`. -/
theorem moves_I_or_twoI {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (hmove : ∃ τ : ℍ, g • τ ≠ τ) :
    g • UpperHalfPlane.I ≠ UpperHalfPlane.I ∨ g • twoI ≠ twoI := by
  by_contra! h
  obtain ⟨h10, h01, h11⟩ := entries_of_two_fixed hg I_ne_twoI h.1 h.2
  obtain ⟨τ, hτ⟩ := hmove
  exact hτ (smul_eq_self_of_scalar hg h10 h01 h11 τ)

/-- Positive determinant and nonzero lower-left entry: the map acts non-trivially. -/
theorem exists_smul_ne_of_lowerLeft_ne_zero {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    (h10 : g 1 0 ≠ 0) : ∃ τ : ℍ, g • τ ≠ τ := by
  by_contra! h
  exact h10 (entries_of_two_fixed hg I_ne_twoI (h _) (h _)).1

/-! ### Convergence of the action -/

/-- Entrywise convergence `C n → 1` implies `C n • τ → τ`, and eventually positive determinant. -/
theorem eventually_det_pos_of_entries_tendsto {C : ℕ → GL (Fin 2) ℝ}
    (hC : ∀ i j, Tendsto (fun n => (C n : Matrix (Fin 2) (Fin 2) ℝ) i j) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j))) :
    ∀ᶠ n in atTop, 0 < (C n).det.val := by
  have h00 : Tendsto (fun n => (C n : Matrix (Fin 2) (Fin 2) ℝ) 0 0) atTop (𝓝 1) := by
    simpa using hC 0 0
  have h01 : Tendsto (fun n => (C n : Matrix (Fin 2) (Fin 2) ℝ) 0 1) atTop (𝓝 0) := by
    simpa using hC 0 1
  have h10 : Tendsto (fun n => (C n : Matrix (Fin 2) (Fin 2) ℝ) 1 0) atTop (𝓝 0) := by
    simpa using hC 1 0
  have h11 : Tendsto (fun n => (C n : Matrix (Fin 2) (Fin 2) ℝ) 1 1) atTop (𝓝 1) := by
    simpa using hC 1 1
  have hdet : Tendsto (fun n => (C n).det.val) atTop (𝓝 1) := by
    have := (h00.mul h11).sub (h01.mul h10)
    simp only [mul_one, mul_zero, sub_zero] at this
    refine this.congr fun n => ?_
    rw [GeneralLinearGroup.val_det_apply, det_fin_two]
  exact hdet.eventually (lt_mem_nhds one_pos)

theorem tendsto_smul_of_entries_tendsto {C : ℕ → GL (Fin 2) ℝ}
    (hC : ∀ i j, Tendsto (fun n => (C n : Matrix (Fin 2) (Fin 2) ℝ) i j) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j))) (τ : ℍ) :
    Tendsto (fun n => C n • τ) atTop (𝓝 τ) := by
  rw [isOpenEmbedding_coe.isInducing.tendsto_nhds_iff]
  have hc : ∀ i j, Tendsto (fun n => (((C n : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ)) atTop
      (𝓝 (((1 : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ)) := fun i j =>
    (Complex.continuous_ofReal.tendsto _).comp (hC i j)
  have hnum : Tendsto (fun n => num (C n) τ) atTop (𝓝 (τ : ℂ)) := by
    have := ((hc 0 0).mul_const (τ : ℂ)).add (hc 0 1)
    simpa [num] using this
  have hden : Tendsto (fun n => denom (C n) τ) atTop (𝓝 (1 : ℂ)) := by
    have := ((hc 1 0).mul_const (τ : ℂ)).add (hc 1 1)
    simpa [denom] using this
  have hq := hnum.div hden one_ne_zero
  rw [div_one] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_det_pos_of_entries_tendsto hC] with n hn
  rw [Function.comp_apply, coe_smul_of_det_pos hn, Pi.div_apply]

/-! ### Constancy -/

/-- If infinitely many `C n` move `τ₀` while `C n • τ₀ → τ₀`, an invariant holomorphic `ψ` is
constant. -/
theorem eq_of_invariant_of_frequently_moved {ψ : ℍ → ℂ} (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ)
    {C : ℕ → GL (Fin 2) ℝ} (hinv : ∀ n τ, ψ (C n • τ) = ψ τ) {τ₀ : ℍ}
    (hlim : Tendsto (fun n => C n • τ₀) atTop (𝓝 τ₀))
    (hfreq : ∃ᶠ n in atTop, C n • τ₀ ≠ τ₀) (τ : ℍ) : ψ τ = ψ τ₀ := by
  have hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ψ - fun _ : ℍ => ψ τ₀) :=
    MDifferentiable.sub hψ mdifferentiable_const
  have hzero : ∃ᶠ z in 𝓝[≠] τ₀, (ψ - fun _ : ℍ => ψ τ₀) z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨u, hu, hτu, huU⟩ := mem_nhdsWithin.mp hU
    obtain ⟨n, hn, hnu⟩ := (hfreq.and_eventually (hlim.eventually (hu.mem_nhds hτu))).exists
    exact ⟨C n • τ₀, huU ⟨hnu, hn⟩, by rw [Pi.sub_apply, hinv, sub_self]⟩
  have := congrFun (eq_zero_of_frequently hφ hzero) τ
  simpa [sub_eq_zero] using this

/-- **Constancy under a non-discrete set of Möbius maps** (entrywise form). A holomorphic
`ψ : ℍ → ℂ` invariant under every `C n`, where `C n → 1` entrywise and each `C n` acts
non-trivially on `ℍ`, is constant. -/
theorem eq_of_invariant_of_entries_tendsto_one {ψ : ℍ → ℂ}
    (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ) {C : ℕ → GL (Fin 2) ℝ}
    (hC : ∀ i j, Tendsto (fun n => (C n : Matrix (Fin 2) (Fin 2) ℝ) i j) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)))
    (hmove : ∀ n, ∃ τ : ℍ, C n • τ ≠ τ) (hinv : ∀ n τ, ψ (C n • τ) = ψ τ) (τ σ : ℍ) :
    ψ τ = ψ σ := by
  have hev : ∀ᶠ n in atTop,
      C n • UpperHalfPlane.I ≠ UpperHalfPlane.I ∨ C n • twoI ≠ twoI := by
    filter_upwards [eventually_det_pos_of_entries_tendsto hC] with n hn
    exact moves_I_or_twoI hn (hmove n)
  rcases frequently_or_distrib.mp hev.frequently with h | h
  · rw [eq_of_invariant_of_frequently_moved hψ hinv (tendsto_smul_of_entries_tendsto hC _) h τ,
      eq_of_invariant_of_frequently_moved hψ hinv (tendsto_smul_of_entries_tendsto hC _) h σ]
  · rw [eq_of_invariant_of_frequently_moved hψ hinv (tendsto_smul_of_entries_tendsto hC _) h τ,
      eq_of_invariant_of_frequently_moved hψ hinv (tendsto_smul_of_entries_tendsto hC _) h σ]

/-- **Constancy under a non-discrete set of Möbius maps** (topological form): `C n → 1` in
`GL(2, ℝ)`, each `C n` acting non-trivially, `ψ` holomorphic and `C n`-invariant. -/
theorem eq_of_invariant_of_tendsto_one {ψ : ℍ → ℂ} (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ)
    {C : ℕ → GL (Fin 2) ℝ} (hC : Tendsto C atTop (𝓝 1))
    (hmove : ∀ n, ∃ τ : ℍ, C n • τ ≠ τ) (hinv : ∀ n τ, ψ (C n • τ) = ψ τ) (τ σ : ℍ) :
    ψ τ = ψ σ := by
  refine eq_of_invariant_of_entries_tendsto_one hψ (fun i j => ?_) hmove hinv τ σ
  have hval : Tendsto (fun n => ((C n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) atTop
      (𝓝 ((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (Units.continuous_val.tendsto _).comp hC
  rw [Units.val_one] at hval
  simpa using ((continuous_id.matrix_elem i j).tendsto _).comp hval

/-! ### Shimizu's sequence -/

/-- The pair `(a n, c n)` of upper-left and lower-left entries of Shimizu's sequence
`B 0 = (1 0; y 1)`, `B (n + 1) = B n T (B n)⁻¹`: `a (n+1) = 1 - a n c n`, `c (n+1) = -(c n)²`. -/
noncomputable def shimizuPair (y : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, y)
  | n + 1 => (1 - (shimizuPair y n).1 * (shimizuPair y n).2, -((shimizuPair y n).2 ^ 2))

/-- Shimizu's sequence `B 0 = (1 0; y 1)`, `B (n + 1) = (1 - a c, a²; -c², 1 + a c)` with
`(a, c) = shimizuPair y n`. -/
noncomputable def shimizuMatrix (y : ℝ) : ℕ → GL (Fin 2) ℝ
  | 0 => glLowerUnipotent y
  | n + 1 => glOfDetOne (1 - (shimizuPair y n).1 * (shimizuPair y n).2) ((shimizuPair y n).1 ^ 2)
      (-((shimizuPair y n).2 ^ 2)) (1 + (shimizuPair y n).1 * (shimizuPair y n).2) (by ring)

lemma shimizuMatrix_entry00 (y : ℝ) (n : ℕ) : shimizuMatrix y n 0 0 = (shimizuPair y n).1 := by
  cases n <;> simp [shimizuMatrix, shimizuPair, glLowerUnipotent]

lemma shimizuMatrix_entry10 (y : ℝ) (n : ℕ) : shimizuMatrix y n 1 0 = (shimizuPair y n).2 := by
  cases n <;> simp [shimizuMatrix, shimizuPair, glLowerUnipotent]

lemma shimizuMatrix_det (y : ℝ) (n : ℕ) :
    shimizuMatrix y n 0 0 * shimizuMatrix y n 1 1 - shimizuMatrix y n 0 1 * shimizuMatrix y n 1 0
      = 1 := by
  cases n with
  | zero => simp [shimizuMatrix, glLowerUnipotent]
  | succ n => simp [shimizuMatrix]; ring

/-- The matrix identity behind Shimizu's recursion: for `a d - b c = 1`,
`(1 - a c, a²; -c², 1 + a c) (a b; c d) = (a b; c d) (1 1; 0 1)`. -/
lemma shimizu_step_identity (a b c d : ℝ) (h : a * d - b * c = 1) :
    !![1 - a * c, a ^ 2; -(c ^ 2), 1 + a * c] * !![a, b; c, d] =
      !![a, b; c, d] * !![1, 1; 0, 1] := by
  rw [mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp; ring
  · simp; linear_combination a * h
  · simp; ring
  · simp; linear_combination c * h

/-- The defining relation `B (n + 1) * B n = B n * T`. -/
lemma shimizuMatrix_succ_mul (y : ℝ) (n : ℕ) :
    shimizuMatrix y (n + 1) * shimizuMatrix y n = shimizuMatrix y n * glUpperUnipotent 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hB : (shimizuMatrix y n : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(shimizuPair y n).1, shimizuMatrix y n 0 1;
        (shimizuPair y n).2, shimizuMatrix y n 1 1] := by
    rw [← shimizuMatrix_entry00, ← shimizuMatrix_entry10]
    exact eta_fin_two _
  have hdet : (shimizuPair y n).1 * shimizuMatrix y n 1 1 -
      shimizuMatrix y n 0 1 * (shimizuPair y n).2 = 1 := by
    rw [← shimizuMatrix_entry00, ← shimizuMatrix_entry10]
    exact shimizuMatrix_det y n
  rw [hB]
  simp only [shimizuMatrix, glUpperUnipotent, glOfDetOne_val]
  exact shimizu_step_identity _ _ _ _ hdet

lemma shimizuMatrix_succ_eq (y : ℝ) (n : ℕ) :
    shimizuMatrix y (n + 1) = shimizuMatrix y n * glUpperUnipotent 1 * (shimizuMatrix y n)⁻¹ :=
  eq_mul_inv_of_mul_eq (shimizuMatrix_succ_mul y n)

lemma shimizuMatrix_mem {H : Subgroup (GL (Fin 2) ℝ)} {y : ℝ} (hT : glUpperUnipotent 1 ∈ H)
    (hL : glLowerUnipotent y ∈ H) (n : ℕ) : shimizuMatrix y n ∈ H := by
  induction n with
  | zero => exact hL
  | succ n ih =>
    rw [shimizuMatrix_succ_eq]
    exact H.mul_mem (H.mul_mem ih hT) (H.inv_mem ih)

/-- The non-discreteness witness `C n = B (n + 1) T⁻¹`. -/
noncomputable def shimizuWitness (y : ℝ) (n : ℕ) : GL (Fin 2) ℝ :=
  shimizuMatrix y (n + 1) * (glUpperUnipotent 1)⁻¹

lemma shimizuWitness_mem {H : Subgroup (GL (Fin 2) ℝ)} {y : ℝ} (hT : glUpperUnipotent 1 ∈ H)
    (hL : glLowerUnipotent y ∈ H) (n : ℕ) : shimizuWitness y n ∈ H :=
  H.mul_mem (shimizuMatrix_mem hT hL (n + 1)) (H.inv_mem hT)

lemma shimizuWitness_val (y : ℝ) (n : ℕ) :
    ((shimizuWitness y n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - (shimizuPair y n).1 * (shimizuPair y n).2,
          (shimizuPair y n).1 ^ 2 - 1 + (shimizuPair y n).1 * (shimizuPair y n).2;
        -((shimizuPair y n).2 ^ 2),
          (shimizuPair y n).2 ^ 2 + 1 + (shimizuPair y n).1 * (shimizuPair y n).2] := by
  rw [shimizuWitness, glUpperUnipotent_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shimizuMatrix, glUpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma shimizuWitness_det (y : ℝ) (n : ℕ) : 0 < (shimizuWitness y n).det.val := by
  rw [GeneralLinearGroup.val_det_apply, shimizuWitness_val, det_fin_two_of]
  set a := (shimizuPair y n).1
  set c := (shimizuPair y n).2
  have h : (1 - a * c) * (c ^ 2 + 1 + a * c) - (a ^ 2 - 1 + a * c) * -(c ^ 2) = 1 := by ring
  rw [h]
  exact one_pos

lemma shimizuPair_snd_ne_zero {y : ℝ} (hy : y ≠ 0) (n : ℕ) : (shimizuPair y n).2 ≠ 0 := by
  induction n with
  | zero => exact hy
  | succ n ih => simpa [shimizuPair] using ih

lemma shimizuPair_snd_abs_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) :
    |(shimizuPair y n).2| ≤ y ^ (n + 1) := by
  induction n with
  | zero => simp [shimizuPair, abs_of_nonneg hy0]
  | succ n ih =>
    simp only [shimizuPair, abs_neg, abs_pow]
    calc |(shimizuPair y n).2| ^ 2 ≤ (y ^ (n + 1)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) ih 2
      _ = y ^ (2 * n + 2) := by ring
      _ ≤ y ^ (n + 1 + 1) := pow_le_pow_of_le_one hy0 hy1 (by omega)

lemma shimizuPair_snd_abs_le_self {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) :
    |(shimizuPair y n).2| ≤ y :=
  (shimizuPair_snd_abs_le hy0 hy1 n).trans
    (by simpa using pow_le_pow_of_le_one hy0 hy1 (Nat.succ_pos n))

lemma shimizuPair_fst_abs_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (n : ℕ) :
    |(shimizuPair y n).1| ≤ 1 / (1 - y) := by
  have h1y : 0 < 1 - y := by linarith
  induction n with
  | zero =>
    simp only [shimizuPair, abs_one]
    rw [le_div_iff₀ h1y]
    linarith
  | succ n ih =>
    simp only [shimizuPair]
    have hc := shimizuPair_snd_abs_le_self hy0 hy1.le n
    calc |1 - (shimizuPair y n).1 * (shimizuPair y n).2|
        ≤ |(1 : ℝ)| + |(shimizuPair y n).1 * (shimizuPair y n).2| := abs_sub _ _
      _ = 1 + |(shimizuPair y n).1| * |(shimizuPair y n).2| := by rw [abs_one, abs_mul]
      _ ≤ 1 + 1 / (1 - y) * y := by
          have := mul_le_mul ih hc (abs_nonneg _) (div_pos one_pos h1y).le
          linarith
      _ = 1 / (1 - y) := by
          have h' : 1 / (1 - y) * (1 - y) = 1 := div_mul_cancel₀ 1 h1y.ne'
          linear_combination -h'

lemma shimizuPair_snd_tendsto {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Tendsto (fun n => (shimizuPair y n).2) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => y ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hy0 hy1).comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero_norm (fun n => by
    rw [Real.norm_eq_abs]; exact shimizuPair_snd_abs_le hy0 hy1.le n) hpow

lemma shimizuPair_fst_tendsto {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Tendsto (fun n => (shimizuPair y n).1) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hc := shimizuPair_snd_tendsto hy0 hy1
  have hbound : ∀ n, ‖(shimizuPair y (n + 1)).1 - 1‖ ≤ 1 / (1 - y) * |(shimizuPair y n).2| := by
    intro n
    simp only [shimizuPair, Real.norm_eq_abs, sub_sub_cancel_left, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_right (shimizuPair_fst_abs_le hy0 hy1 n) (abs_nonneg _)
  have hlim : Tendsto (fun n => 1 / (1 - y) * |(shimizuPair y n).2|) atTop (𝓝 0) := by
    simpa using (hc.abs).const_mul (1 / (1 - y))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) hbound hlim)

/-- **Shimizu's sequence converges to the identity**, entrywise. -/
theorem shimizuWitness_entries_tendsto {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (i j : Fin 2) :
    Tendsto (fun n => (shimizuWitness y n : Matrix (Fin 2) (Fin 2) ℝ) i j) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)) := by
  have ha := shimizuPair_fst_tendsto hy0 hy1
  have hc := shimizuPair_snd_tendsto hy0 hy1
  simp only [shimizuWitness_val]
  fin_cases i <;> fin_cases j
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (ha.mul hc)
  · simpa using ((ha.pow 2).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).add (ha.mul hc)
  · simpa using (hc.pow 2).neg
  · simpa using ((hc.pow 2).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).add (ha.mul hc)

/-- Each `C n` of Shimizu's sequence acts non-trivially (its lower-left entry is `-(c n)² ≠ 0`). -/
theorem shimizuWitness_moves {y : ℝ} (hy : y ≠ 0) (n : ℕ) :
    ∃ τ : ℍ, shimizuWitness y n • τ ≠ τ := by
  refine exists_smul_ne_of_lowerLeft_ne_zero (shimizuWitness_det y n) ?_
  have h : (shimizuWitness y n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -((shimizuPair y n).2 ^ 2) := by
    rw [shimizuWitness_val]; simp
  rw [h, neg_ne_zero]
  exact pow_ne_zero 2 (shimizuPair_snd_ne_zero hy n)

/-- **Shimizu + constancy.** A holomorphic `ψ : ℍ → ℂ` with `ψ (τ + 1) = ψ τ` and
`ψ (τ / (y τ + 1)) = ψ τ` for some `0 < y < 1` is constant. -/
theorem eq_of_invariant_upper_lower_unipotent {ψ : ℍ → ℂ} (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hT : ∀ τ, ψ (glUpperUnipotent 1 • τ) = ψ τ)
    (hL : ∀ τ, ψ (glLowerUnipotent y • τ) = ψ τ) (τ σ : ℍ) : ψ τ = ψ σ :=
  eq_of_invariant_of_entries_tendsto_one hψ (shimizuWitness_entries_tendsto hy0.le hy1)
    (shimizuWitness_moves hy0.ne')
    (fun n => (shimizuWitness_mem (H := precompInvariantSubgroup ψ) hT hL n)) τ σ

end VOA.Moonshine.ConwayNorton
