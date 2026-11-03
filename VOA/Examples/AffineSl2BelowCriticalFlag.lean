/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2JointPBW
import VOA.Core.GoodFiltration

/-!
# The ordinary current-length flag on the universal affine `sl₂` vacuum VOA

`F_p` is the span of all creation words `J^{a₁}_{-n₁-1} ⋯ J^{a_r}_{-n_r-1} |0⟩` with at most `p`
letters (any colours, any order, any depths); the flag piece at weight `n` is `F_p ∩ V_n`.
This is the ordinary current-PBW length filtration used in the below-critical
graded-unitarity argument.  It is **not** the
corrected filtration of `Examples.AffineSl2GoodFiltration` (where the Sugawara vector has degree
one); here the Sugawara vector has degree two.

Main results, all unconditional:

* `ordinaryFlag k hk : GradedFlag (universal k hk)`;
* `J_mem_ordinaryPiece_of_nonneg` — nonnegative current modes preserve `F_p`;
* `J_mem_ordinaryPiece_succ_of_neg` — negative current modes map `F_p` into `F_{p+1}`;
* `J_mem_grading` — `J^a_m` lowers the conformal weight by `m`;
* `grading_le_span_creation` — every positive weight space is spanned by negative-mode images
  of lower weight spaces.
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The span of current creation words of length at most `p`. -/
def ordinaryPiece (p : ℕ) : Submodule ℂ (WakModule k) :=
  Submodule.span ℂ (Set.range (fun w : {w : List (Fin 3 × ℕ) // w.length ≤ p} =>
    wordStateA k w.1))

variable {k}

theorem wordStateA_mem_ordinaryPiece {w : List (Fin 3 × ℕ)} {p : ℕ} (hw : w.length ≤ p) :
    wordStateA k w ∈ ordinaryPiece k p :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

theorem ordinaryPiece_mono {p q : ℕ} (hpq : p ≤ q) : ordinaryPiece k p ≤ ordinaryPiece k q := by
  rw [ordinaryPiece, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact wordStateA_mem_ordinaryPiece (w.2.trans hpq)

/-- A negative current mode adds one letter. -/
theorem J_mem_ordinaryPiece_succ_of_neg (a : Fin 3) {m : ℤ} (hm : m < 0) {p : ℕ}
    {x : WakModule k} (hx : x ∈ ordinaryPiece k p) : J k a m x ∈ ordinaryPiece k (p + 1) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨w, hw⟩, rfl⟩ := hz
      have h := wordStateA_mem_ordinaryPiece (k := k) (w := (a, (-m - 1).toNat) :: w)
        (p := p + 1) (by simp [hw])
      rw [wordStateA_cons] at h
      have hm' : -(((-m - 1).toNat : ℕ) : ℤ) - 1 = m := by omega
      simpa only [hm'] using h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- On a single creation word, a nonnegative mode does not increase the length. -/
theorem J_wordStateA_mem_of_nonneg (w : List (Fin 3 × ℕ)) :
    ∀ (a : Fin 3) {m : ℤ}, 0 ≤ m → J k a m (wordStateA k w) ∈ ordinaryPiece k w.length := by
  induction w with
  | nil =>
      intro a m hm
      rw [wordStateA_nil, J_vacuum_nonneg k a hm]
      exact Submodule.zero_mem _
  | cons b w ih =>
      intro a m hm
      rw [wordStateA_cons]
      set n : ℤ := -(b.2 : ℤ) - 1 with hn
      have hcomm := LinearMap.congr_fun (current_comm k a b.1 m n) (wordStateA k w)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at hcomm
      rw [sub_eq_iff_eq_add] at hcomm
      rw [hcomm]
      have hlen : w.length + 1 = (b :: w).length := by simp
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · -- the commutator terms
        apply Submodule.sum_mem
        intro c _
        apply Submodule.smul_mem
        by_cases hmn : 0 ≤ m + n
        · exact ordinaryPiece_mono (by simp) (ih c hmn)
        · rw [← hlen]
          exact J_mem_ordinaryPiece_succ_of_neg c (by omega)
            (wordStateA_mem_ordinaryPiece le_rfl)
      · -- the central term
        split_ifs
        · rw [LinearMap.smul_apply, LinearMap.id_apply]
          exact Submodule.smul_mem _ _
            (wordStateA_mem_ordinaryPiece (by simp))
        · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
      · -- the reordered term
        rw [← hlen]
        exact J_mem_ordinaryPiece_succ_of_neg b.1 (by omega) (ih a hm)

/-- Nonnegative current modes preserve each piece of the ordinary flag. -/
theorem J_mem_ordinaryPiece_of_nonneg (a : Fin 3) {m : ℤ} (hm : 0 ≤ m) {p : ℕ}
    {x : WakModule k} (hx : x ∈ ordinaryPiece k p) : J k a m x ∈ ordinaryPiece k p := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨w, hw⟩, rfl⟩ := hz
      exact ordinaryPiece_mono hw (J_wordStateA_mem_of_nonneg w a hm)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- Length zero is the vacuum line. -/
theorem ordinaryPiece_zero : ordinaryPiece k 0 = ℂ ∙ vacuumA k := by
  apply le_antisymm
  · rw [ordinaryPiece, Submodule.span_le]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw0
    exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_le]
    rintro _ rfl
    exact wordStateA_mem_ordinaryPiece (w := []) (by simp)

/-- The ordinary pieces exhaust the vacuum module. -/
theorem iSup_ordinaryPiece : (⨆ p : ℕ, ordinaryPiece k p) = ⊤ := by
  rw [eq_top_iff, ← wordStateA_span k, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact Submodule.mem_iSup_of_mem w.length (wordStateA_mem_ordinaryPiece le_rfl)

variable (k)

/-- The ordinary flag piece of length `≤ p` and conformal weight `n`. -/
def ordinaryWeightPiece (p : ℕ) (n : ℤ) : Submodule ℂ (WakModule k) :=
  ordinaryPiece k p ⊓ (universal k hk).grading n

/-- **The ordinary current-length graded flag** on `V^k(sl₂)`. -/
def ordinaryFlag : GradedFlag (universal k hk) where
  piece := ordinaryWeightPiece k hk
  le_grading := fun _ _ => inf_le_right
  mono := by
    intro p q n hpq
    exact inf_le_inf_right _ (ordinaryPiece_mono hpq)
  bot := by
    intro n hn
    rw [ordinaryWeightPiece, ordinaryPiece_zero]
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx0 : x ∈ (universal k hk).grading 0 := by
      rw [(universal k hk).vacuum_grade]
      exact hx.1
    have hd : Disjoint ((universal k hk).grading 0) ((universal k hk).grading n) :=
      (universal k hk).isInternal.submodule_iSupIndep.pairwiseDisjoint (by omega)
    exact Submodule.disjoint_def.mp hd x hx0 hx.2
  vacuum_zero := by
    change ordinaryPiece k 0 ⊓ (universal k hk).grading 0 = _
    rw [ordinaryPiece_zero]
    change (ℂ ∙ (universal k hk).vacuum) ⊓ (universal k hk).grading 0 = _
    rw [(universal k hk).vacuum_grade, inf_idem]
  exhaustive := by
    intro n
    apply le_antisymm
    · exact iSup_le fun _ => inf_le_right
    · intro x hx
      have hall : x ∈ ⨆ p : ℕ, ordinaryPiece k p := by
        rw [iSup_ordinaryPiece]; trivial
      obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _
        (fun p q => ⟨max p q, ordinaryPiece_mono (le_max_left p q),
          ordinaryPiece_mono (le_max_right p q)⟩)).mp hall
      exact Submodule.mem_iSup_of_mem p ⟨hp, hx⟩

@[simp] theorem ordinaryFlag_piece (p : ℕ) (n : ℤ) :
    (ordinaryFlag k hk).piece p n = ordinaryPiece k p ⊓ (universal k hk).grading n := rfl

variable {k}

/-- `J^a_m` lowers the conformal weight by `m`. -/
theorem J_mem_grading (a : Fin 3) (m : ℤ) {n : ℤ} {x : WakModule k}
    (hx : x ∈ (universal k hk).grading n) : J k a m x ∈ (universal k hk).grading (n - m) := by
  have h := (universal k hk).smul_mem_grading (currentState_mem_grading k hk a) hx m
  rw [smul_currentState_eq_J] at h
  convert h using 2
  ring

/-- Flag-level form: nonnegative modes preserve the flag degree. -/
theorem J_mem_ordinaryFlag_of_nonneg (a : Fin 3) {m : ℤ} (hm : 0 ≤ m) {p : ℕ} {n : ℤ}
    {x : WakModule k} (hx : x ∈ (ordinaryFlag k hk).piece p n) :
    J k a m x ∈ (ordinaryFlag k hk).piece p (n - m) :=
  ⟨J_mem_ordinaryPiece_of_nonneg a hm hx.1, J_mem_grading hk a m hx.2⟩

/-- Flag-level form: a negative mode `J^a_{-m}` (`m > 0`) raises the flag degree by at most
one. -/
theorem J_mem_ordinaryFlag_of_neg (a : Fin 3) {m : ℤ} (hm : 0 < m) {p : ℕ} {n : ℤ}
    {x : WakModule k} (hx : x ∈ (ordinaryFlag k hk).piece p n) :
    J k a (-m) x ∈ (ordinaryFlag k hk).piece (p + 1) (n + m) := by
  refine ⟨J_mem_ordinaryPiece_succ_of_neg a (by omega) hx.1, ?_⟩
  have h := J_mem_grading hk a (-m) hx.2
  simpa only [sub_neg_eq_add] using h

/-- Every creation word is homogeneous of its total depth. -/
theorem wordStateA_mem_grading (w : List (Fin 3 × ℕ)) :
    wordStateA k w ∈ (universal k hk).grading (wordDegA w) :=
  creation_state_grading k hk w

/-- Every positive weight space is spanned by negative-mode images of lower weight spaces. -/
theorem grading_le_span_creation {n : ℤ} (hn : 0 < n) :
    (universal k hk).grading n ≤ Submodule.span ℂ
      {x | ∃ (a : Fin 3) (m : ℕ) (y : WakModule k), 0 < m ∧
        y ∈ (universal k hk).grading (n - m) ∧ x = J k a (-(m : ℤ)) y} := by
  intro x hx
  have hx' : x ∈ gradingZA k n := by simpa only [closed_grading] using hx
  have hH := gradingZA_le_hspan k n hx'
  refine (Submodule.span_le.mpr ?_) hH
  rintro _ ⟨l, hl, rfl⟩
  cases l with
  | nil => simp at hl; omega
  | cons b w =>
      refine Submodule.subset_span ⟨b.1, b.2 + 1, wordStateA k w, by omega, ?_, ?_⟩
      · have h := wordStateA_mem_grading hk w
        rw [wordDegA_cons] at hl
        convert h using 2
        push_cast
        omega
      · rw [wordStateA_cons]
        congr 2
        push_cast
        ring

end

end AffineSl2BelowCritical

end VOA
