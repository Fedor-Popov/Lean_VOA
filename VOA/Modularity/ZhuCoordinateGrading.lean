/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.ZhuCoordinateCurrent

/-!
# Weight bookkeeping for square-bracket `C₂` terms

* `sqWeightSpace_le_gradeLE` — an `L[0]`-eigenvector of weight `q` has `L₀`-components only in
  degrees `≤ q` (`V_[q] ⊆ V^{≤q}`);
* `vSqZ_mem_gradeLE` — `a[n]` maps `V^{≤e}` into `V^{≤p+e-n-1}` for `a ∈ V_p`;
* `sqC2Span W N` — the span of `a[-2]b` with `a ∈ V_p` (`p ≥ 1`), `b ∈ V^{≤N-p-1}`, and
  `vSqZ_neg_mem_sqC2Span`: every `a[-n]b` (`n ≥ 2`) with the same weight bound lies in it
  (translation rule);
* `currentC2` / `currentC2At` — the span of square current modes `J[-n]y` (`n ≥ 2`) and its
  weight-`w` part; `mem_currentC2At_of_mem` — a vector of `currentC2` of `L[0]`-weight `w` lies
  in `currentC2At w` (independence of the `L[0]`-eigenspaces).
-/

namespace VOA.ZhuCoordinate

open VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-! ## `L₀`-filtration facts -/

theorem grading_inf_gradeLE_pred (d : ℤ) : W.grading d ⊓ gradeLE W (d - 1) = ⊥ := by
  have hind := W.isInternal.submodule_iSupIndep d
  refine eq_bot_iff.mpr fun x hx => ?_
  have hle : gradeLE W (d - 1) ≤ ⨆ (j : ℤ) (_ : j ≠ d), W.grading j := by
    refine iSup_le fun j => ?_
    exact le_iSup₂_of_le (j : ℤ) (by have := j.2; omega) le_rfl
  have := hind.le_bot ⟨hx.1, hle hx.2⟩
  exact this

/-- `L[0]` preserves the `L₀`-filtration. -/
theorem Lsq_zero_mem_gradeLE {e : ℤ} {x : 𝒱} (hx : x ∈ gradeLE W e) :
    Lsq W 0 x ∈ gradeLE W e := by
  refine Submodule.iSup_induction (fun j : {j : ℤ // j ≤ e} => W.grading j)
    (motive := fun x => Lsq W 0 x ∈ gradeLE W e) hx ?_ (by simp) ?_
  · intro j y hy
    have h1 := Lsq_zero_sub_smul_mem_gradeLE W hy
    have h2 : Lsq W 0 y = (Lsq W 0 y - ((j : ℤ) : ℂ) • y) + ((j : ℤ) : ℂ) • y := by abel
    rw [h2]
    exact Submodule.add_mem _ (gradeLE_mono W (by have := j.2; omega) h1)
      (Submodule.smul_mem _ _ (mem_gradeLE_of_mem_grading W j.2 hy))
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- **`V_[q] ⊆ V^{≤q}`**: an `L[0]`-eigenvector of integer weight `q` has no `L₀`-component above
`q`. -/
theorem sqWeightSpace_le_gradeLE (q : ℤ) : sqWeightSpace W (q : ℂ) ≤ gradeLE W q := by
  intro x hx
  rw [mem_sqWeightSpace_iff] at hx
  have key : ∀ k : ℕ, ∀ x : 𝒱, x ∈ gradeLE W (q + k) → Lsq W 0 x = (q : ℂ) • x →
      x ∈ gradeLE W q := by
    intro k
    induction k with
    | zero => intro x hx _; simpa using hx
    | succ k ih =>
      intro x hxk hxe
      rw [show q + ((k + 1 : ℕ) : ℤ) = q + k + 1 by push_cast; ring, gradeLE_split,
        show q + (k : ℤ) + 1 - 1 = q + k by ring] at hxk
      obtain ⟨xt, hxt, x', hx', rfl⟩ := Submodule.mem_sup.mp hxk
      have h1 := Lsq_zero_sub_smul_mem_gradeLE W hxt
      have h2 := Lsq_zero_mem_gradeLE W hx'
      have hr : (((k : ℂ) + 1)) • xt ∈ gradeLE W (q + k) := by
        have e : ((k : ℂ) + 1) • xt
            = (q : ℂ) • x' - Lsq W 0 x' - (Lsq W 0 xt - ((q + k + 1 : ℤ) : ℂ) • xt) := by
          rw [map_add] at hxe
          rw [smul_add] at hxe
          push_cast
          linear_combination (norm := module) hxe
        rw [e]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hx') h2) ?_
        simpa [show q + (k : ℤ) + 1 - 1 = q + k by ring] using h1
      have hxt0 : xt = 0 := by
        have hmem : xt ∈ gradeLE W (q + k) := by
          have hne : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
          simpa [smul_smul, inv_mul_cancel₀ hne] using
            Submodule.smul_mem _ ((k : ℂ) + 1)⁻¹ hr
        have := grading_inf_gradeLE_pred W (q + k + 1)
        rw [show q + (k : ℤ) + 1 - 1 = q + k by ring] at this
        have h := (Submodule.mem_inf.mpr ⟨hxt, hmem⟩)
        rw [this] at h
        exact (Submodule.mem_bot ℂ).mp h
      subst hxt0
      rw [zero_add] at hxe ⊢
      exact ih x' hx' hxe
  obtain ⟨d, hd⟩ := exists_mem_gradeLE W x
  exact key (d - q).toNat x (gradeLE_mono W (by omega) hd) hx

/-- `V^{≤0} = ℂ|0⟩`. -/
theorem gradeLE_zero : gradeLE W 0 = Submodule.span ℂ {W.vacuum} := by
  rw [gradeLE_split, show (0 : ℤ) - 1 = -1 by norm_num, gradeLE_eq_bot W (by norm_num),
    sup_bot_eq, W.vacuum_grade]

/-- `a[n]` maps `V^{≤e}` to `V^{≤p+e-n-1}`. -/
theorem vSqZ_mem_gradeLE {a : 𝒱} {p : ℤ} (ha : a ∈ W.grading p) (k : ℕ) (n : ℤ) {e : ℤ}
    {y : 𝒱} (hy : y ∈ gradeLE W e) : vSqZ W a k n y ∈ gradeLE W (p + e - n - 1) := by
  refine Submodule.iSup_induction (fun j : {j : ℤ // j ≤ e} => W.grading j)
    (motive := fun y => vSqZ W a k n y ∈ gradeLE W (p + e - n - 1)) hy ?_ (by simp) ?_
  · intro j z hz
    rw [vSqZ_eq_sum W ha hz k n ((p + j - n).toNat) (by omega)]
    refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
    exact mem_gradeLE_of_mem_grading W (by have := j.2; omega) (W.smul_mem_grading ha hz _)
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-! ## The square-bracket `C₂` span with weight bounds -/

/-- `C₂[V]` at total weight `≤ N`: the span of `a[-2]b`, `a ∈ V_p` (`p ≥ 1`), `b ∈ V^{≤N-p-1}`. -/
def sqC2Span (N : ℤ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ (p : ℕ) (a b : 𝒱), 1 ≤ p ∧ a ∈ W.grading (p : ℤ) ∧
    b ∈ gradeLE W (N - p - 1) ∧ x = vSqZ W a p (-2) b}

/-- **`a[-n]b ∈ C₂[V]` for `n ≥ 2`** (with the weight bound), by the translation rule
`a[-n-1] = (1/n)((L₋₁a)[-n] + p·a[-n])`. -/
theorem vSqZ_neg_mem_sqC2Span (N : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∀ (P : ℕ) (a y : 𝒱), a ∈ W.grading ((P + 1 : ℕ) : ℤ) →
      y ∈ gradeLE W (N - (P + 1 : ℕ) - n + 1) →
      vSqZ W a (P + 1) (-(n : ℤ)) y ∈ sqC2Span W N := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro P a y ha hy
      refine Submodule.subset_span ⟨P + 1, a, y, by omega, ha, ?_, by norm_num⟩
      convert hy using 2
      push_cast; ring
  | succ n hn ih =>
      intro P a y ha hy
      have hLa : W.L (-1) a ∈ W.grading ((P + 1 + 1 : ℕ) : ℤ) := by
        have := L_mem_grading W ha (-1); simpa [add_assoc] using this
      have hrule := LinearMap.congr_fun (vSqZ_L_neg_one W P ha (-(n : ℤ))) y
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply] at hrule
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have e : vSqZ W a (P + 1) (-((n + 1 : ℕ) : ℤ)) y
          = (n : ℂ)⁻¹ • (vSqZ W (W.L (-1) a) (P + 2) (-(n : ℤ)) y
            + ((P : ℂ) + 1) • vSqZ W a (P + 1) (-(n : ℤ)) y) := by
        rw [hrule, show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring]
        push_cast
        rw [neg_neg, sub_add_cancel, smul_smul, inv_mul_cancel₀ hn0, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_))
      · exact ih (P + 1) (W.L (-1) a) y hLa (gradeLE_mono W (by push_cast; omega) hy)
      · exact ih P a y ha (gradeLE_mono W (by push_cast; omega) hy)

/-! ## Square current `C₂` spans and their `L[0]`-weight parts -/

variable {ι : Type*} (g : ι → 𝒱)

/-- The span of the square current modes `J[-n]y`, `n ≥ 2`, `y` arbitrary. -/
def currentC2 : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ (i : ι) (n : ℕ) (y : 𝒱), 2 ≤ n ∧ x = vSqZ W (g i) 1 (-(n : ℤ)) y}

/-- Its `L[0]`-weight-`w` part: `y ∈ V_[w-n]`. -/
def currentC2At (w : ℂ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ (i : ι) (n : ℕ) (y : 𝒱), 2 ≤ n ∧ y ∈ sqWeightSpace W (w - n) ∧
    x = vSqZ W (g i) 1 (-(n : ℤ)) y}

variable {g}

theorem currentC2At_le (hg : ∀ i, g i ∈ W.grading 1) (hg1 : ∀ i, W.L 1 (g i) = 0) (w : ℂ) :
    currentC2At W g w ≤ sqWeightSpace W w := by
  rw [currentC2At, Submodule.span_le]
  rintro x ⟨i, n, y, -, hy, rfl⟩
  have := vSqZ_mem_sqWeightSpace W (hg i) (hg1 i) (-(n : ℤ)) hy
  simpa using this

/-- **Weight extraction**: a vector of `currentC2` of `L[0]`-weight `w` lies in
`currentC2At w`. -/
theorem mem_currentC2At_of_mem (hg : ∀ i, g i ∈ W.grading 1) (hg1 : ∀ i, W.L 1 (g i) = 0)
    {w : ℂ} {x : 𝒱} (hx : x ∈ currentC2 W g) (hw : x ∈ sqWeightSpace W w) :
    x ∈ currentC2At W g w := by
  -- every element of `currentC2` is `y + r` with `y ∈ currentC2At w`, `r` of other weights
  set R : Submodule ℂ 𝒱 := ⨆ (j : ℂ) (_ : j ≠ w), sqWeightSpace W j with hR
  have hsplit : ∀ z ∈ currentC2 W g, ∃ y ∈ currentC2At W g w, z - y ∈ R := by
    intro z hz
    refine Submodule.span_induction ?_ ⟨0, Submodule.zero_mem _, by simp⟩ ?_ ?_ hz
    · rintro z ⟨i, n, y, hn, rfl⟩
      have hy : y ∈ ⨆ k : ℂ, sqWeightSpace W k := by
        rw [(sqWeightSpace_isInternal W).submodule_iSup_eq_top]; trivial
      refine Submodule.iSup_induction (fun k : ℂ => sqWeightSpace W k)
        (motive := fun y => ∃ y' ∈ currentC2At W g w, vSqZ W (g i) 1 (-(n : ℤ)) y - y' ∈ R)
        hy ?_ ⟨0, Submodule.zero_mem _, by simp⟩ ?_
      · intro k u hu
        by_cases hk : k + n = w
        · refine ⟨vSqZ W (g i) 1 (-(n : ℤ)) u, Submodule.subset_span ⟨i, n, u, hn, ?_, rfl⟩,
            by simp⟩
          rw [← hk]; simpa using hu
        · refine ⟨0, Submodule.zero_mem _, ?_⟩
          rw [sub_zero]
          have hm := vSqZ_mem_sqWeightSpace W (hg i) (hg1 i) (-(n : ℤ)) hu
          push_cast at hm
          rw [sub_neg_eq_add] at hm
          exact Submodule.mem_iSup_of_mem (k + n) (Submodule.mem_iSup_of_mem hk hm)
      · rintro u v ⟨yu, hyu, hu⟩ ⟨yv, hyv, hv⟩
        refine ⟨yu + yv, Submodule.add_mem _ hyu hyv, ?_⟩
        rw [map_add, show vSqZ W (g i) 1 (-(n : ℤ)) u + vSqZ W (g i) 1 (-(n : ℤ)) v - (yu + yv)
          = (vSqZ W (g i) 1 (-(n : ℤ)) u - yu) + (vSqZ W (g i) 1 (-(n : ℤ)) v - yv) by abel]
        exact Submodule.add_mem _ hu hv
    · rintro u v - - ⟨yu, hyu, hu⟩ ⟨yv, hyv, hv⟩
      refine ⟨yu + yv, Submodule.add_mem _ hyu hyv, ?_⟩
      rw [show u + v - (yu + yv) = (u - yu) + (v - yv) by abel]
      exact Submodule.add_mem _ hu hv
    · rintro c u - ⟨yu, hyu, hu⟩
      refine ⟨c • yu, Submodule.smul_mem _ c hyu, ?_⟩
      rw [← smul_sub]
      exact Submodule.smul_mem _ c hu
  obtain ⟨y, hy, hr⟩ := hsplit x hx
  have hyw : y ∈ sqWeightSpace W w := currentC2At_le W hg hg1 w hy
  have hdis := (sqWeightSpace_isInternal W).submodule_iSupIndep w
  have h0 : x - y = 0 := by
    have hmem : x - y ∈ sqWeightSpace W w ⊓ R :=
      Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hw hyw, hr⟩
    rw [hdis.eq_bot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  rw [sub_eq_zero.mp h0]
  exact hy

/-- **From square current `C₂` terms to the weighted `C₂[V]` span** at `L[0]`-weight `N`. -/
theorem currentC2At_le_sqC2Span (hg : ∀ i, g i ∈ W.grading 1) (N : ℤ) :
    currentC2At W g (N : ℂ) ≤ sqC2Span W N := by
  rw [currentC2At, Submodule.span_le]
  rintro x ⟨i, n, y, hn, hy, rfl⟩
  have hy' : y ∈ gradeLE W (N - n) := by
    have := sqWeightSpace_le_gradeLE W (N - n)
    push_cast at this
    exact this hy
  have := vSqZ_neg_mem_sqC2Span W N n hn 0 (g i) y (by simpa using hg i)
    (gradeLE_mono W (by omega) hy')
  simpa using this

end VOA.ZhuCoordinate

section AxiomAudit
#print axioms VOA.ZhuCoordinate.sqWeightSpace_le_gradeLE
#print axioms VOA.ZhuCoordinate.vSqZ_neg_mem_sqC2Span
#print axioms VOA.ZhuCoordinate.mem_currentC2At_of_mem
#print axioms VOA.ZhuCoordinate.currentC2At_le_sqC2Span
end AxiomAudit
