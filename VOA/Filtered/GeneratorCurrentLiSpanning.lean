/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.GeneratorWordLiSurjectivity
import VOA.Filtered.AffineCurrentLi

/-!
# Li filtration = generator-word filtration, for any finite generator family

Let `W` be a VOA and `gen : Fin g → V` a finite family of states.  Write `C_q` for the span of
the generator words `gen_{i₁ (-n₁-1)} ⋯ gen_{i_s (-n_s-1)} vacuum` with `n₁ + ⋯ + n_s ≥ q`
(`genWordPiece`).  This file proves, generically:

* `generatorWordsSpanLiFiltration_of_tracked`: if the words span `V` and every generator mode
  obeys the *tracked estimate* `gen_{i (m)} C_q ⊆ C_{max(q-m-1,0)}`, then Li's filtration is the
  word filtration (`GeneratorWordsSpanLiFiltration`).  This is the Borcherds-iterate argument of
  `AffineCurrentLi` / `VirasoroWordLi`, stated once.
* `generatorModeTracked_of_current_comm`: the tracked estimate holds for **Lie currents**, i.e. as
  soon as the generator modes `J i m` satisfy `[J^i_m, J^j_p] = Σ_c f^{ij}_c J^c_{m+p} +
  δ_{m+p,0} κ(i,j,m)` and kill the vacuum for `m ≥ 0`.  This covers the universal affine VOA of
  any Lie algebra with a chosen basis.
* `generatorWordsSpanLiFiltration_quotient`: the property passes to every graded quotient, with
  the projected generators.

Together with `GeneratorWordLiSurjectivity` this gives surjectivity of the canonical jet map
`J_∞ → gr^{Li}` for every graded quotient of an affine VOA, with no PBW basis and no `C₂`
cofiniteness assumption.
-/

namespace VOA

open VOA.AffineVOA.CurrentLi (currentModeTarget)

universe u

noncomputable section

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) {g : ℕ} (gen : Fin g → V) (wt : Fin g → ℕ)

theorem genWordState_nil : genWordState W gen wt [] = W.vacuum := rfl

theorem genWordState_cons (i : Fin g) (r : ℕ) (l : List (Fin g × ℕ)) :
    genWordState W gen wt ((i, r) :: l) =
      W.smul (gen i) (-(r : ℤ) - 1) (genWordState W gen wt l) := by
  simp only [genWordState, genWord_cons, wordAct_cons, PreVertexAlgebra.smul_def]
  rfl

theorem genWordState_mem_genWordPiece (p : ℕ) (l : List (Fin g × ℕ)) (hp : p ≤ pairsLevel l) :
    genWordState W gen wt l ∈ genWordPiece W gen wt p :=
  Submodule.subset_span ⟨l, hp, rfl⟩

theorem genWordPiece_antitone {p q : ℕ} (hpq : p ≤ q) :
    genWordPiece W gen wt q ≤ genWordPiece W gen wt p := by
  rw [genWordPiece, genWordPiece, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact genWordState_mem_genWordPiece W gen wt p l (hpq.trans hl)

/-- The tracked estimate: mode `m` of a generator maps `C_q` into `C_{max(q-m-1,0)}`. -/
def GeneratorModeTracked : Prop :=
  ∀ (i : Fin g) (m : ℤ) (q : ℕ) (v : V), v ∈ genWordPiece W gen wt q →
    W.smul (gen i) m v ∈ genWordPiece W gen wt (currentModeTarget q m)

variable {W gen wt}

/-- **All-mode estimate for generator words**, by the Borcherds iterate formula. -/
theorem genWordState_mode_mem (htrack : GeneratorModeTracked W gen wt) :
    ∀ (left : List (Fin g × ℕ)) (q : ℕ) (v : V),
      v ∈ genWordPiece W gen wt q → ∀ N : ℤ,
        W.smul (genWordState W gen wt left) N v ∈
          genWordPiece W gen wt (currentModeTarget q N) := by
  intro left
  induction left with
  | nil =>
      intro q v hv N
      rw [genWordState_nil, PreVertexAlgebra.smul_vacuum_left]
      split_ifs with hN
      · subst N
        simpa [currentModeTarget] using hv
      · exact Submodule.zero_mem _
  | cons ir rest ih =>
      obtain ⟨i, r⟩ := ir
      intro q v hv N
      rw [genWordState_cons, VertexOperatorAlgebra.mode_iterate]
      apply QuotVOA.finsum_mem_submodule
      intro n
      apply Submodule.smul_mem
      apply Submodule.sub_mem
      · apply genWordPiece_antitone W gen wt
          (p := currentModeTarget q N)
          (q := currentModeTarget (currentModeTarget q (N + (n : ℤ)))
            (-(r : ℤ) - 1 - (n : ℤ)))
        · simp only [currentModeTarget]
          omega
        · exact htrack i _ _ _ (ih q v hv (N + (n : ℤ)))
      · apply Submodule.smul_mem
        apply genWordPiece_antitone W gen wt
          (p := currentModeTarget q N)
          (q := currentModeTarget (currentModeTarget q (n : ℤ))
            ((-(r : ℤ) - 1) + N - (n : ℤ)))
        · simp only [currentModeTarget]
          omega
        · exact ih (currentModeTarget q (n : ℤ)) _ (htrack i (n : ℤ) q v hv)
            ((-(r : ℤ) - 1) + N - (n : ℤ))

/-- Negative-mode closure of the word filtration, for an arbitrary left state. -/
theorem genWordNegativeModeClosed (htrack : GeneratorModeTracked W gen wt)
    (hspan : Submodule.span ℂ (Set.range (genWordState W gen wt)) = ⊤)
    (q n : ℕ) (u : V) {v : V} (hv : v ∈ genWordPiece W gen wt q) :
    W.smul u (-(n : ℤ) - 1) v ∈ genWordPiece W gen wt (q + n) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (genWordState W gen wt)) := by
    rw [hspan]; exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨left, rfl⟩ := hz
      have h := genWordState_mode_mem htrack left q v hv (-(n : ℤ) - 1)
      have ht : currentModeTarget q (-(n : ℤ) - 1) = q + n := by
        simp only [currentModeTarget]
        omega
      rwa [ht] at h
  | zero => rw [PreVertexAlgebra.smul_zero_left]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [PreVertexAlgebra.smul_add_left]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx =>
      rw [PreVertexAlgebra.smul_smul_left]; exact Submodule.smul_mem _ a ihx

private theorem wordAct_mem_genWordPiece (htrack : GeneratorModeTracked W gen wt)
    (hspan : Submodule.span ℂ (Set.range (genWordState W gen wt)) = ⊤) :
    ∀ l : List (Letter V),
      wordAct (adjointWeakModule W) l W.vacuum ∈ genWordPiece W gen wt (wordLevel l) := by
  intro l
  induction l with
  | nil =>
      change W.vacuum ∈ genWordPiece W gen wt 0
      exact genWordState_mem_genWordPiece W gen wt 0 [] (Nat.zero_le _)
  | cons a rest ih =>
      rw [wordAct_cons, wordLevel_cons]
      simpa only [PreVertexAlgebra.smul_def, Nat.add_comm] using
        genWordNegativeModeClosed htrack hspan (wordLevel rest) a.2.2 a.1 ih

/-- **Li filtration = generator-word filtration**, from spanning plus the tracked estimate. -/
theorem generatorWordsSpanLiFiltration_of_tracked (htrack : GeneratorModeTracked W gen wt)
    (hspan : Submodule.span ℂ (Set.range (genWordState W gen wt)) = ⊤) :
    GeneratorWordsSpanLiFiltration W gen wt := by
  intro p
  change Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p : ℤ) ≤ genWordPiece W gen wt p
  rw [Gfil, Submodule.span_le]
  rintro _ ⟨l, w, _hl, hw, hlevel, rfl⟩
  have hw' : w = W.vacuum := Set.mem_singleton_iff.mp hw
  subst w
  exact genWordPiece_antitone W gen wt (by exact_mod_cast hlevel)
    (wordAct_mem_genWordPiece htrack hspan l)

/-! ## Lie currents satisfy the tracked estimate -/

section LieCurrents

variable (J : Fin g → ℤ → Module.End ℂ V)
variable (f : Fin g → Fin g → Fin g → ℂ) (cen : Fin g → Fin g → ℤ → ℂ)

/-- Prepending a negative current mode adds its depth. -/
theorem J_negSucc_mem_genWordPiece_add (hJ : ∀ i m v, W.smul (gen i) m v = J i m v)
    (i : Fin g) (r q : ℕ) {v : V} (hv : v ∈ genWordPiece W gen wt q) :
    J i (-(r : ℤ) - 1) v ∈ genWordPiece W gen wt (q + r) := by
  rw [genWordPiece] at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨right, hright, rfl⟩ := hz
      rw [← hJ, ← genWordState_cons]
      exact genWordState_mem_genWordPiece W gen wt _ ((i, r) :: right) (by
        simp only [pairsLevel_cons] at hright ⊢
        omega)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx => rw [map_smul]; exact Submodule.smul_mem _ a ihx

/-- **Tracked current commutation** on generator words. -/
theorem J_genWordState_mem (hJ : ∀ i m v, W.smul (gen i) m v = J i m v)
    (hcomm : ∀ i j m p, J i m * J j p - J j p * J i m =
      (∑ c, f i j c • J c (m + p)) +
        (if m + p = 0 then cen i j m • (1 : Module.End ℂ V) else 0))
    (hvac : ∀ i m, 0 ≤ m → J i m W.vacuum = 0) :
    ∀ (right : List (Fin g × ℕ)) (i : Fin g) (m : ℤ),
      J i m (genWordState W gen wt right) ∈
        genWordPiece W gen wt (currentModeTarget (pairsLevel right) m) := by
  intro right
  induction right with
  | nil =>
      intro i m
      by_cases hm : 0 ≤ m
      · rw [genWordState_nil, hvac i m hm]
        exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = -(r : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
        subst m
        have ht : currentModeTarget (pairsLevel ([] : List (Fin g × ℕ))) (-(r : ℤ) - 1) = r := by
          simp [currentModeTarget, pairsLevel]
        rw [ht, genWordState_nil, ← hJ, ← genWordState_nil W gen wt, ← genWordState_cons]
        exact genWordState_mem_genWordPiece W gen wt r [(i, r)] (by simp [pairsLevel])
  | cons jr rest ih =>
      obtain ⟨j, r⟩ := jr
      intro i m
      by_cases hm : m < 0
      · obtain ⟨s, hs⟩ : ∃ s : ℕ, m = -(s : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
        subst m
        rw [← hJ, ← genWordState_cons]
        exact genWordState_mem_genWordPiece W gen wt _ ((i, s) :: (j, r) :: rest) (by
          simp only [currentModeTarget, pairsLevel_cons]
          omega)
      · have hm0 : 0 ≤ m := le_of_not_gt hm
        rw [genWordState_cons, hJ]
        have happ := congrArg (fun T : Module.End ℂ V => T (genWordState W gen wt rest))
          (hcomm i j m (-(r : ℤ) - 1))
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
          LinearMap.sum_apply, LinearMap.smul_apply] at happ
        rw [sub_eq_iff_eq_add] at happ
        rw [happ]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact Submodule.sum_mem _ (fun c _ =>
              Submodule.smul_mem _ _ (genWordPiece_antitone W gen wt (by
                simp only [currentModeTarget, pairsLevel_cons]
                omega) (ih c (m + (-(r : ℤ) - 1)))))
          · split_ifs with hzero
            · rw [LinearMap.smul_apply, Module.End.one_apply]
              apply Submodule.smul_mem
              exact genWordPiece_antitone W gen wt
                (p := currentModeTarget (pairsLevel ((j, r) :: rest)) m)
                (q := pairsLevel rest) (by
                  simp only [currentModeTarget, pairsLevel_cons] at hzero ⊢
                  omega)
                (genWordState_mem_genWordPiece W gen wt _ rest le_rfl)
            · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
        · exact genWordPiece_antitone W gen wt
            (p := currentModeTarget (pairsLevel ((j, r) :: rest)) m)
            (q := currentModeTarget (pairsLevel rest) m + r) (by
              simp only [currentModeTarget, pairsLevel_cons]
              omega)
            (J_negSucc_mem_genWordPiece_add J hJ j r _ (ih i m))

/-- **Lie currents obey the tracked estimate.** -/
theorem generatorModeTracked_of_current_comm (hJ : ∀ i m v, W.smul (gen i) m v = J i m v)
    (hcomm : ∀ i j m p, J i m * J j p - J j p * J i m =
      (∑ c, f i j c • J c (m + p)) +
        (if m + p = 0 then cen i j m • (1 : Module.End ℂ V) else 0))
    (hvac : ∀ i m, 0 ≤ m → J i m W.vacuum = 0) :
    GeneratorModeTracked W gen wt := by
  intro i m q v hv
  rw [hJ]
  rw [genWordPiece] at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨right, hright, rfl⟩ := hz
      exact genWordPiece_antitone W gen wt (p := currentModeTarget q m)
        (q := currentModeTarget (pairsLevel right) m) (by
          simp only [currentModeTarget] at hright ⊢
          omega) (J_genWordState_mem J f cen hJ hcomm hvac right i m)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx => rw [map_smul]; exact Submodule.smul_mem _ a ihx

end LieCurrents

/-! ## Passage to graded quotients -/

section Quotient

variable (I : Submodule ℂ V) (hI : W.IsIdeal I) (hgr : QuotVOA.IsGradedIdeal W I)

theorem mkQ_genWordState (l : List (Fin g × ℕ)) :
    I.mkQ (genWordState W gen wt l) =
      genWordState (QuotVOA.quotientVOA W I hI hgr) (fun i => I.mkQ (gen i)) wt l := by
  induction l with
  | nil => rfl
  | cons ir rest ih =>
      obtain ⟨i, r⟩ := ir
      rw [genWordState_cons, genWordState_cons, ← ih, QuotVOA.quotientVOA_mkQ_smul hI hgr]

/-- Generator-word spanning of Li's filtration passes to every graded quotient. -/
theorem generatorWordsSpanLiFiltration_quotient (h : GeneratorWordsSpanLiFiltration W gen wt) :
    GeneratorWordsSpanLiFiltration (QuotVOA.quotientVOA W I hI hgr)
      (fun i => I.mkQ (gen i)) wt := by
  intro p
  rw [AffineVOA.CurrentLi.quotientLiFiltration_eq_map W I hI hgr p]
  refine (Submodule.map_mono (h p)).trans ?_
  rw [genWordPiece, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨l, hl, (mkQ_genWordState I hI hgr l).symm⟩

end Quotient

end

end VOA
