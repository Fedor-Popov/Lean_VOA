/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNSortingLink1
import VOA.Modularity.GNBoundedReach
import VOA.Modularity.C2Extraction

/-!
# Gaberdiel--Neitzke Prop. 8, Link 2: representative replacement

This file isolates the filtration estimate needed to replace a homogeneous letter by its
representative modulo `O₂`.  The first lemma says that a nonnegative mode lowers the GN
field-weight filtration by one.  It is the termination mechanism for the nonnegative-mode tails
in `VertexOperatorAlgebra.mode_iterate` at `ℓ = -2`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A nonnegative mode of a homogeneous vector lowers the total field-weight filtration by one. -/
theorem gnLink2_nonneg_mode_word_mem (W : VertexOperatorAlgebra 𝒱) :
    ∀ (l : List (GNLetter 𝒱)), GNWordOK W l →
      ∀ (u : 𝒱) (wu : ℕ), u ∈ W.grading (wu : ℤ) → ∀ m : ℕ,
        W.smul u (m : ℤ) (gnWord W l W.vacuum)
          ∈ gnGradeFil W (wu + gnWordGrade l - 1) := by
  classical
  intro l
  induction l with
  | nil =>
      intro _ u wu hu m
      rw [gnWord_nil, W.toPreVertexAlgebra.smul_vacuum_nonneg u (by positivity)]
      exact Submodule.zero_mem _
  | cons p l ih =>
      intro hOK u wu hu m
      rcases Nat.eq_zero_or_pos wu with rfl | hwu
      · rw [Nat.cast_zero, W.vacuum_grade, Submodule.mem_span_singleton] at hu
        obtain ⟨c, rfl⟩ := hu
        rw [W.smul_smul_left, W.toPreVertexAlgebra.smul_vacuum_left,
          if_neg (by omega : ¬ ((m : ℤ) = -1)), smul_zero]
        exact Submodule.zero_mem _
      · set x : 𝒱 := gnWord W l W.vacuum with hx
        obtain ⟨K, hcomm⟩ := VertexOperatorAlgebra.mode_commutator
          W u p.1 (m : ℤ) (-(p.2.2 : ℤ))
        have hcommx :
            W.smul u (m : ℤ) (W.smul p.1 (-(p.2.2 : ℤ)) x)
              = W.smul p.1 (-(p.2.2 : ℤ)) (W.smul u (m : ℤ) x)
                + ∑ j : Fin K, gBinom (m : ℤ) (j : ℕ) •
                    W.smul (W.smul u (j : ℕ) p.1)
                      ((m : ℤ) - (p.2.2 : ℤ) - (j : ℕ)) x := by
          have happ := DFunLike.congr_fun hcomm x
          rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
            LinearMap.sum_apply] at happ
          have happ' :
              W.smul u (m : ℤ) (W.smul p.1 (-(p.2.2 : ℤ)) x)
                  - W.smul p.1 (-(p.2.2 : ℤ)) (W.smul u (m : ℤ) x)
                = ∑ j : Fin K, gBinom (m : ℤ) (j : ℕ) •
                    W.smul (W.smul u (j : ℕ) p.1)
                      ((m : ℤ) - (p.2.2 : ℤ) - (j : ℕ)) x := by
            simpa only [LinearMap.smul_apply, ← PreVertexAlgebra.smul_def, sub_eq_add_neg] using happ
          rw [← happ']
          abel
        rw [gnWord_cons, ← hx, hcommx]
        refine Submodule.add_mem _ ?_ ?_
        · have htail := ih hOK.tail u wu hu m
          have hpOK : GNWordOK W ([p] : List (GNLetter 𝒱)) := by
            refine ⟨?_, ?_⟩
            · intro q hq
              rw [List.mem_singleton] at hq
              subst q
              exact hOK.head_mem
            · intro q hq
              rw [List.mem_singleton] at hq
              subst q
              exact hOK.2 p (List.mem_cons_self ..)
          have hpre := gnGradeFil_prepend W hpOK htail
          have hleFil :
              gnWordGrade ([p] : List (GNLetter 𝒱)) + (wu + gnWordGrade l - 1)
                ≤ wu + gnWordGrade (p :: l) - 1 := by
            simp only [gnWordGrade_cons, gnWordGrade_nil, add_zero]
            omega
          simpa only [gnWord_cons, gnWord_nil, gnWordGrade_cons, gnWordGrade_nil, add_zero] using
            (gnGradeFil_mono W hleFil hpre)
        · refine Submodule.sum_mem _ (fun j _ => ?_)
          refine Submodule.smul_mem _ _ ?_
          set c : 𝒱 := W.smul u (j : ℕ) p.1 with hc
          have hcmem :
              c ∈ W.grading ((wu : ℤ) + (p.2.1 : ℤ) - (j : ℕ) - 1) :=
            W.smul_mem_grading hu hOK.head_mem (j : ℕ)
          by_cases hneg : (wu : ℤ) + (p.2.1 : ℤ) - (j : ℕ) - 1 < 0
          · rw [W.positivity _ hneg, Submodule.mem_bot] at hcmem
            rw [hcmem, W.smul_zero_left]
            exact Submodule.zero_mem _
          · push Not at hneg
            obtain ⟨wc, hwc⟩ :
                ∃ wc : ℕ, (wc : ℤ) = (wu : ℤ) + (p.2.1 : ℤ) - (j : ℕ) - 1 :=
              ⟨((wu : ℤ) + (p.2.1 : ℤ) - (j : ℕ) - 1).toNat, by omega⟩
            have hcNat : c ∈ W.grading (wc : ℤ) := by rwa [hwc]
            have hwc_le : wc + 1 ≤ wu + p.2.1 := by
              have hz : (wc : ℤ) + 1 ≤ (wu : ℤ) + (p.2.1 : ℤ) := by omega
              exact_mod_cast hz
            by_cases hk : (m : ℤ) - (p.2.2 : ℤ) - (j : ℕ) < 0
            · obtain ⟨k, hkEq⟩ :
                  ∃ k : ℕ, (m : ℤ) - (p.2.2 : ℤ) - (j : ℕ) = -(k : ℤ) :=
                ⟨(-( (m : ℤ) - (p.2.2 : ℤ) - (j : ℕ))).toNat, by omega⟩
              have hkPos : 1 ≤ k := by
                have : (0 : ℤ) < (k : ℤ) := by omega
                exact_mod_cast this
              have hword :
                  W.smul c ((m : ℤ) - (p.2.2 : ℤ) - (j : ℕ)) x
                    = gnWord W ((c, wc, k) :: l) W.vacuum := by
                rw [gnWord_cons, ← hx, hkEq]
              rw [hword]
              have hleFil : gnWordGrade ((c, wc, k) :: l)
                  ≤ wu + gnWordGrade (p :: l) - 1 := by
                simp only [gnWordGrade_cons]
                omega
              refine gnGradeFil_mono W hleFil (word_mem_gnGradeFil W ?_ (le_refl _))
              refine ⟨?_, ?_⟩
              · intro q hq
                rcases List.mem_cons.mp hq with rfl | hq
                · exact hcNat
                · exact hOK.tail.1 q hq
              · intro q hq
                rcases List.mem_cons.mp hq with rfl | hq
                · exact hkPos
                · exact hOK.tail.2 q hq
            · push Not at hk
              obtain ⟨k, hkEq⟩ :
                  ∃ k : ℕ, (m : ℤ) - (p.2.2 : ℤ) - (j : ℕ) = (k : ℤ) :=
                ⟨((m : ℤ) - (p.2.2 : ℤ) - (j : ℕ)).toNat, by omega⟩
              rw [hkEq]
              have hleFil : wc + gnWordGrade l - 1
                  ≤ wu + gnWordGrade (p :: l) - 1 := by
                simp only [gnWordGrade_cons]
                omega
              exact gnGradeFil_mono W hleFil (ih hOK.tail c wc hcNat k)

/-- Prepending one homogeneous negative-mode letter adds its weight to the filtration index. -/
theorem gnLink2_prepend_mem (W : VertexOperatorAlgebra 𝒱) {a x : 𝒱} {wa n G : ℕ}
    (ha : a ∈ W.grading (wa : ℤ)) (hn : 1 ≤ n) (hx : x ∈ gnGradeFil W G) :
    W.smul a (-(n : ℤ)) x ∈ gnGradeFil W (wa + G) := by
  have hOK : GNWordOK W ([(a, wa, n)] : List (GNLetter 𝒱)) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst p
      exact ha
    · intro p hp
      rw [List.mem_singleton] at hp
      subst p
      exact hn
  simpa only [gnWord_cons, gnWord_nil, gnWordGrade_cons, gnWordGrade_nil, add_zero] using
    (gnGradeFil_prepend W hOK hx)

/-- A homogeneous `O₂` generator acting by a negative mode lowers GN field-weight by one. -/
theorem gnLink2_O₂homGenDeg_word_mem (W : VertexOperatorAlgebra 𝒱) {c : 𝒱} {wc n : ℕ}
    (hc : c ∈ O₂homGenDeg W (wc : ℤ)) (hn : 1 ≤ n)
    {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l) :
    W.smul c (-(n : ℤ)) (gnWord W l W.vacuum)
      ∈ gnGradeFil W (wc + gnWordGrade l - 1) := by
  classical
  obtain ⟨pa, pb, a, b, ha, hb, hpq, rfl⟩ := hc
  rcases lt_or_ge pa 0 with hpa | hpa
  · rw [W.positivity pa hpa, Submodule.mem_bot] at ha
    subst a
    rw [W.smul_zero_left, W.smul_zero_left]
    exact Submodule.zero_mem _
  · rcases lt_or_ge pb 0 with hpb | hpb
    · rw [W.positivity pb hpb, Submodule.mem_bot] at hb
      subst b
      rw [W.smul_zero_right, W.smul_zero_left]
      exact Submodule.zero_mem _
    · obtain ⟨wa, hwa⟩ : ∃ wa : ℕ, (wa : ℤ) = pa :=
        ⟨pa.toNat, Int.toNat_of_nonneg hpa⟩
      obtain ⟨wb, hwb⟩ : ∃ wb : ℕ, (wb : ℤ) = pb :=
        ⟨pb.toNat, Int.toNat_of_nonneg hpb⟩
      have haNat : a ∈ W.grading (wa : ℤ) := by rwa [hwa]
      have hbNat : b ∈ W.grading (wb : ℤ) := by rwa [hwb]
      have hwc : wa + wb + 1 = wc := by
        exact_mod_cast (by omega : (wa : ℤ) + (wb : ℤ) + 1 = (wc : ℤ))
      set x : 𝒱 := gnWord W l W.vacuum with hx
      rw [VertexOperatorAlgebra.mode_iterate W a b (-2) (-(n : ℤ)) x]
      refine finsum_mem_submodule_pd _ _ (fun i => ?_)
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · by_cases hi : -(n : ℤ) + (i : ℤ) < 0
        · obtain ⟨k, hk⟩ : ∃ k : ℕ, -(n : ℤ) + (i : ℤ) = -(k : ℤ) :=
            ⟨(-(-(n : ℤ) + (i : ℤ))).toNat, by omega⟩
          have hkPos : 1 ≤ k := by
            have : (0 : ℤ) < (k : ℤ) := by omega
            exact_mod_cast this
          have hword :
              W.smul a (-2 - (i : ℤ)) (W.smul b (-(n : ℤ) + (i : ℤ)) x)
                = gnWord W ((a, wa, i + 2) :: (b, wb, k) :: l) W.vacuum := by
            rw [gnWord_cons, gnWord_cons, ← hx, hk]
            congr 1
            push_cast
            ring
          rw [hword]
          have hwordOK : GNWordOK W ((a, wa, i + 2) :: (b, wb, k) :: l) := by
            refine ⟨?_, ?_⟩
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact haNat
              · rcases List.mem_cons.mp hp with rfl | hp
                · exact hbNat
                · exact hOK.1 p hp
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · show 1 ≤ i + 2
                omega
              · rcases List.mem_cons.mp hp with rfl | hp
                · exact hkPos
                · exact hOK.2 p hp
          have hleFil : gnWordGrade ((a, wa, i + 2) :: (b, wb, k) :: l)
              ≤ wc + gnWordGrade l - 1 := by
            simp only [gnWordGrade_cons]
            omega
          exact gnGradeFil_mono W hleFil
            (word_mem_gnGradeFil W hwordOK (le_refl _))
        · have hiNonneg : 0 ≤ -(n : ℤ) + (i : ℤ) := le_of_not_gt hi
          obtain ⟨k, hk⟩ : ∃ k : ℕ, -(n : ℤ) + (i : ℤ) = (k : ℤ) :=
            ⟨(-(n : ℤ) + (i : ℤ)).toNat, (Int.toNat_of_nonneg hiNonneg).symm⟩
          have hinner := gnLink2_nonneg_mode_word_mem W l hOK b wb hbNat k
          have houter := gnLink2_prepend_mem W haNat (by omega : 1 ≤ i + 2) hinner
          have hleFil : wa + (wb + gnWordGrade l - 1)
              ≤ wc + gnWordGrade l - 1 := by omega
          rw [hk]
          have hidx : (-2 : ℤ) - (i : ℤ) = -((i + 2 : ℕ) : ℤ) := by
            push_cast
            ring
          rw [hidx]
          exact gnGradeFil_mono W hleFil houter
      · have hinner := gnLink2_nonneg_mode_word_mem W l hOK a wa haNat i
        have houter := gnLink2_prepend_mem W hbNat (by omega : 1 ≤ n + i + 2) hinner
        have hleFil : wb + (wa + gnWordGrade l - 1)
            ≤ wc + gnWordGrade l - 1 := by omega
        have hidx : (-2 : ℤ) + -(n : ℤ) - (i : ℤ) = -((n + i + 2 : ℕ) : ℤ) := by
          push_cast
          ring
        rw [hidx]
        have hsign : ((-1 : ℂ) ^ (-2 : ℤ)) = 1 := by norm_num
        rw [hsign, one_smul, hx]
        exact gnGradeFil_mono W hleFil houter

/-- A homogeneous element of `O₂` acting by a negative mode lowers GN field-weight by one. -/
theorem gnLink2_O₂_word_mem (W : VertexOperatorAlgebra 𝒱) {c : 𝒱} {wc n : ℕ}
    (hcO : c ∈ O₂ W) (hcW : c ∈ W.grading (wc : ℤ)) (hn : 1 ≤ n)
    {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l) :
    W.smul c (-(n : ℤ)) (gnWord W l W.vacuum)
      ∈ gnGradeFil W (wc + gnWordGrade l - 1) := by
  have hcSpan : c ∈ Submodule.span ℂ (O₂homGenDeg W (wc : ℤ)) :=
    O₂_inf_grading_le_span_deg W (wc : ℤ) ⟨hcO, hcW⟩
  refine Submodule.span_induction
    (p := fun c _ => W.smul c (-(n : ℤ)) (gnWord W l W.vacuum)
      ∈ gnGradeFil W (wc + gnWordGrade l - 1)) ?_ ?_ ?_ ?_ hcSpan
  · intro d hd
    exact gnLink2_O₂homGenDeg_word_mem W hd hn hOK
  · change W.smul 0 (-(n : ℤ)) (gnWord W l W.vacuum)
      ∈ gnGradeFil W (wc + gnWordGrade l - 1)
    rw [W.smul_zero_left]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [W.smul_add_left]
    exact Submodule.add_mem _ ha hb
  · intro z a _ ha
    rw [W.smul_smul_left]
    exact Submodule.smul_mem _ _ ha

/-! ## Homogeneous representatives and the grade-bounded raw generator span -/

/-- Representatives of one fixed conformal weight: matching generators, plus the vacuum only in
weight zero. -/
def gnLink2WeightReps (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (w : ℕ) : Set 𝒱 :=
  {x | (∃ i : Fin g, wt i = w ∧ x = gen i) ∨ (w = 0 ∧ x = W.vacuum)}

/-- Projecting the spanning-mod-`O₂` decomposition to one weight gives only representatives of
that same weight and a homogeneous `O₂` remainder. -/
theorem gnLink2_homog_mem_repSpan_sup_O₂ (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {x : 𝒱} {w : ℕ} (hx : x ∈ W.grading (w : ℤ)) :
    x ∈ Submodule.span ℂ (gnLink2WeightReps W gen wt w) ⊔
      (O₂ W ⊓ W.grading (w : ℤ)) := by
  classical
  have hxtop : x ∈ Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W :=
    hdec ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hxtop
  obtain ⟨a, ha, b, hb, hab⟩ := hxtop
  have hpix : piHom W (w : ℤ) x = x := piHom_of_mem W hx
  have hpa : piHom W (w : ℤ) a ∈
      Submodule.span ℂ (gnLink2WeightReps W gen wt w) := by
    refine Submodule.span_induction
      (p := fun a _ => piHom W (w : ℤ) a ∈
        Submodule.span ℂ (gnLink2WeightReps W gen wt w)) ?_ ?_ ?_ ?_ ha
    · intro y hy
      rcases hy with ⟨i, rfl⟩ | hy
      · by_cases hi : wt i = w
        · subst w
          rw [piHom_of_mem W (hgen i)]
          exact Submodule.subset_span (Or.inl ⟨i, rfl, rfl⟩)
        · have hiZ : (wt i : ℤ) ≠ (w : ℤ) := by exact_mod_cast hi
          rw [piHom_of_mem_ne W hiZ (hgen i)]
          exact Submodule.zero_mem _
      · have hyv : y = W.vacuum := Set.mem_singleton_iff.mp hy
        subst y
        by_cases hw : w = 0
        · subst w
          change piHom W (0 : ℤ) W.vacuum ∈
            Submodule.span ℂ (gnLink2WeightReps W gen wt 0)
          rw [piHom_of_mem W W.vacuum_mem_grading_zero]
          exact Submodule.subset_span (Or.inr ⟨rfl, rfl⟩)
        · rw [piHom_of_mem_ne W (by omega : (0 : ℤ) ≠ (w : ℤ))
              W.vacuum_mem_grading_zero]
          exact Submodule.zero_mem _
    · change piHom W (w : ℤ) 0 ∈ Submodule.span ℂ (gnLink2WeightReps W gen wt w)
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    · intro c y _ hy
      rw [map_smul]
      exact Submodule.smul_mem _ _ hy
  have hpbO : piHom W (w : ℤ) b ∈ O₂ W := piHom_maps_O₂ W (w : ℤ) hb
  have hpbg : piHom W (w : ℤ) b ∈ W.grading (w : ℤ) := piHom_mem W (w : ℤ) b
  rw [← hpix, ← hab, map_add]
  exact Submodule.add_mem_sup hpa ⟨hpbO, hpbg⟩

/-- The grade-bounded span of admissible words over `gen`, before any mode sorting. -/
noncomputable def gnLink2RawSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (G : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ l : List (GNLetter 𝒱),
    GNWordOK W l ∧ OverGens gen wt l ∧ gnWordGrade l ≤ G ∧
      x = gnWord W l W.vacuum}

theorem gnLink2_word_mem_rawSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {G : ℕ} {l : List (GNLetter 𝒱)}
    (hOK : GNWordOK W l) (hgen : OverGens gen wt l) (hG : gnWordGrade l ≤ G) :
    gnWord W l W.vacuum ∈ gnLink2RawSpan W gen wt G :=
  Submodule.subset_span ⟨l, hOK, hgen, hG, rfl⟩

theorem gnLink2_rawSpan_mono (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) {G G' : ℕ} (h : G ≤ G') :
    gnLink2RawSpan W gen wt G ≤ gnLink2RawSpan W gen wt G' := by
  rw [gnLink2RawSpan, Submodule.span_le]
  rintro x ⟨l, hOK, hgens, hG, rfl⟩
  exact gnLink2_word_mem_rawSpan W hOK hgens (le_trans hG h)

/-- A generator negative mode prepends its letter to the raw generator span. -/
theorem gnLink2_prepend_rawSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (i : Fin g) {n G : ℕ} (hn : 1 ≤ n) {x : 𝒱}
    (hx : x ∈ gnLink2RawSpan W gen wt G) :
    W.smul (gen i) (-(n : ℤ)) x ∈ gnLink2RawSpan W gen wt (wt i + G) := by
  refine Submodule.span_induction
    (p := fun x _ => W.smul (gen i) (-(n : ℤ)) x
      ∈ gnLink2RawSpan W gen wt (wt i + G)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hOK, hgens, hG, rfl⟩
    change gnWord W ((gen i, wt i, n) :: l) W.vacuum
      ∈ gnLink2RawSpan W gen wt (wt i + G)
    refine gnLink2_word_mem_rawSpan W ?_ ?_ (by simp only [gnWordGrade_cons]; omega)
    · refine ⟨?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hgen i
        · exact hOK.1 p hp
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hn
        · exact hOK.2 p hp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨i, rfl, rfl⟩
      · exact hgens p hp
  · change W.smul (gen i) (-(n : ℤ)) 0 ∈ gnLink2RawSpan W gen wt (wt i + G)
    rw [W.smul_zero_right]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [W.smul_add_right]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]
    exact Submodule.smul_mem _ _ hy

/-- The genuinely lower part of the GN filtration.  Unlike `gnGradeFil (G-1)`, it is bottom at
`G=0`, avoiding the information loss caused by truncated natural subtraction. -/
noncomputable def gnLink2LowerFil (W : VertexOperatorAlgebra 𝒱) (G : ℕ) : Submodule ℂ 𝒱 :=
  if G = 0 then ⊥ else gnGradeFil W (G - 1)

/-- A grade-zero admissible word is already in the raw generator span: all its letters are scalar
multiples of the vacuum, so the word is a scalar multiple of the empty word. -/
theorem gnLink2_grade_zero_word_mem_rawSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) {l : List (GNLetter 𝒱)}
    (hOK : GNWordOK W l) (hgrade : gnWordGrade l = 0) :
    gnWord W l W.vacuum ∈ gnLink2RawSpan W gen wt 0 := by
  have hvacLetters : ∀ p ∈ l, ∃ c : ℂ, p.1 = c • W.vacuum := by
    intro p hp
    have hpw : p.2.1 = 0 := gnWordGrade_zero_wt hgrade p hp
    have hpmem : p.1 ∈ W.grading 0 := by
      have := hOK.1 p hp
      rwa [hpw, Nat.cast_zero] at this
    rw [W.vacuum_grade, Submodule.mem_span_singleton] at hpmem
    obtain ⟨c, hc⟩ := hpmem
    exact ⟨c, hc.symm⟩
  have hspan := gnWord_vacuumLetters l hvacLetters
  refine (Submodule.span_le.mpr ?_) hspan
  intro x hx
  have hxv : x = W.vacuum := Set.mem_singleton_iff.mp hx
  subst x
  exact gnLink2_word_mem_rawSpan W (GNWordOK.nil W) (by simp [OverGens]) (by simp)

/-- **Representative normalization, word-wise and grade-bounded.**  Every admissible word is a
linear combination of generator words of no larger grade, modulo the genuinely lower GN
filtration.  The same-grade branches replace a letter without changing its weight or mode index. -/
theorem gnLink2_word_mem_rawSpan_sup_lower (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W) :
    ∀ (l : List (GNLetter 𝒱)), GNWordOK W l →
      gnWord W l W.vacuum ∈
        gnLink2RawSpan W gen wt (gnWordGrade l) ⊔ gnLink2LowerFil W (gnWordGrade l) := by
  classical
  intro l
  induction l with
  | nil =>
      intro _
      exact Submodule.mem_sup_left
        (gnLink2_word_mem_rawSpan W (GNWordOK.nil W) (by simp [OverGens]) (by simp))
  | cons p l ih =>
      intro hOK
      by_cases htotal : gnWordGrade (p :: l) = 0
      · exact Submodule.mem_sup_left
          (by simpa only [htotal] using
            (gnLink2_grade_zero_word_mem_rawSpan W gen wt hOK htotal))
      · have hpdec := gnLink2_homog_mem_repSpan_sup_O₂ W gen wt hgen hdec hOK.head_mem
        have htotalSum : p.2.1 + gnWordGrade l ≠ 0 := by
          simpa only [gnWordGrade_cons] using htotal
        rw [Submodule.mem_sup] at hpdec
        obtain ⟨a, ha, b, hb, hab⟩ := hpdec
        rw [gnWord_cons, ← hab, W.smul_add_left]
        refine Submodule.add_mem _ ?_ ?_
        · refine Submodule.span_induction
            (p := fun a _ => W.smul a (-(p.2.2 : ℤ)) (gnWord W l W.vacuum) ∈
              gnLink2RawSpan W gen wt (gnWordGrade (p :: l)) ⊔
                gnLink2LowerFil W (gnWordGrade (p :: l))) ?_ ?_ ?_ ?_ ha
          · intro y hy
            rcases hy with ⟨i, hiw, rfl⟩ | ⟨hpzero, rfl⟩
            · have htail := ih hOK.tail
              rw [Submodule.mem_sup] at htail
              obtain ⟨yr, hyr, z, hz, hyz⟩ := htail
              rw [← hyz, W.smul_add_right]
              refine Submodule.add_mem _ ?_ ?_
              · have hraw := gnLink2_prepend_rawSpan W hgen i
                  (hOK.2 p (List.mem_cons_self ..)) hyr
                exact Submodule.mem_sup_left (by
                  simpa only [gnWordGrade_cons, hiw] using hraw)
              · by_cases hrest : gnWordGrade l = 0
                · have hz0 : z = 0 := by
                    simpa [gnLink2LowerFil, hrest, Submodule.mem_bot] using hz
                  rw [hz0, W.smul_zero_right]
                  exact Submodule.zero_mem _
                · have hzF : z ∈ gnGradeFil W (gnWordGrade l - 1) := by
                    simpa [gnLink2LowerFil, hrest] using hz
                  have hprep := gnLink2_prepend_mem W (hgen i)
                    (hOK.2 p (List.mem_cons_self ..)) hzF
                  have hleFil : wt i + (gnWordGrade l - 1)
                      ≤ gnWordGrade (p :: l) - 1 := by
                    simp only [gnWordGrade_cons, hiw]
                    omega
                  have hprep' := gnGradeFil_mono W hleFil hprep
                  have hlow : W.smul (gen i) (-(p.2.2 : ℤ)) z ∈
                      gnLink2LowerFil W (gnWordGrade (p :: l)) := by
                    rw [gnLink2LowerFil, if_neg htotal]
                    exact hprep'
                  exact Submodule.mem_sup_right hlow
            · rw [W.toPreVertexAlgebra.smul_vacuum_left]
              by_cases hn1 : (-(p.2.2 : ℤ)) = -1
              · rw [if_pos hn1]
                simpa only [gnWordGrade_cons, hpzero, zero_add] using ih hOK.tail
              · rw [if_neg hn1]
                exact Submodule.zero_mem _
          · change W.smul 0 (-(p.2.2 : ℤ)) (gnWord W l W.vacuum) ∈
              gnLink2RawSpan W gen wt (gnWordGrade (p :: l)) ⊔
                gnLink2LowerFil W (gnWordGrade (p :: l))
            rw [W.smul_zero_left]
            exact Submodule.zero_mem _
          · intro y z _ _ hy hz
            rw [W.smul_add_left]
            exact Submodule.add_mem _ hy hz
          · intro c y _ hy
            rw [W.smul_smul_left]
            exact Submodule.smul_mem _ _ hy
        · have hbact := gnLink2_O₂_word_mem W hb.1 hb.2
            (hOK.2 p (List.mem_cons_self ..)) hOK.tail
          exact Submodule.mem_sup_right (by
            simpa only [gnWordGrade_cons, gnLink2LowerFil, if_neg htotalSum] using hbact)

theorem gnLink2_lowerFil_mono (W : VertexOperatorAlgebra 𝒱) {G G' : ℕ} (h : G ≤ G') :
    gnLink2LowerFil W G ≤ gnLink2LowerFil W G' := by
  intro x hx
  by_cases hG : G = 0
  · rw [gnLink2LowerFil, if_pos hG, Submodule.mem_bot] at hx
    subst x
    exact Submodule.zero_mem _
  · have hG' : G' ≠ 0 := by omega
    rw [gnLink2LowerFil, if_neg hG] at hx
    rw [gnLink2LowerFil, if_neg hG']
    exact gnGradeFil_mono W (by omega) hx

/-- Span-level form of representative normalization, with the grade cap retained. -/
theorem gnLink2_gradeFil_le_rawSpan_sup_lower (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W) (G : ℕ) :
    gnGradeFil W G ≤ gnLink2RawSpan W gen wt G ⊔ gnLink2LowerFil W G := by
  rw [gnGradeFil, Submodule.span_le]
  rintro x ⟨l, hOK, hgrade, rfl⟩
  have hnorm := gnLink2_word_mem_rawSpan_sup_lower W gen wt hgen hdec l hOK
  exact (sup_le_sup (gnLink2_rawSpan_mono W gen wt hgrade)
    (gnLink2_lowerFil_mono W hgrade)) hnorm

/-! ## Link 1 + Link 2: the `N=0` base case -/

/-- Sorting sends the grade-bounded raw generator span into the bounded `N=0` target, provided
all strictly lower grades have already been reached. -/
theorem gnLink2_rawSpan_le_bounded_zero (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hwt : ∀ i, 1 ≤ wt i)
    (G : ℕ) (hLower : ∀ G' : ℕ, G' < G → GNReachBounded W gen wt G' 0) :
    gnLink2RawSpan W gen wt G ≤ gnSpanBounded W gen wt G 0 := by
  rw [gnLink2RawSpan, Submodule.span_le]
  rintro x ⟨l, hOK, hover, hgrade, rfl⟩
  have hallPos : ∀ p ∈ l, 1 ≤ p.2.1 := by
    intro p hp
    obtain ⟨i, _, hpw⟩ := hover p hp
    rw [hpw]
    exact hwt i
  rcases Nat.eq_zero_or_pos G with rfl | hG
  · have hgrade0 : gnWordGrade l = 0 := Nat.eq_zero_of_le_zero hgrade
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons p rest =>
          have hp := hallPos p (List.mem_cons_self ..)
          rw [gnWordGrade_cons] at hgrade0
          omega
    subst l
    exact Submodule.subset_span
      ⟨[], hOK, hgrade, by simp [GNWeakDec], gnNoRepeatLE_zero hOK, hover, rfl⟩
  · obtain ⟨l', hperm, hOK', hwd, herr⟩ :=
      gnWord_sort_mod_lower W l hOK hallPos (G - 1) (by omega)
    have hgrade' : gnWordGrade l' ≤ G := by
      rw [← gnWordGrade_eq_of_perm hperm]
      exact hgrade
    have hover' : OverGens gen wt l' := by
      intro p hp
      exact hover p (hperm.mem_iff.mpr hp)
    have hsorted : gnWord W l' W.vacuum ∈ gnSpanBounded W gen wt G 0 :=
      Submodule.subset_span
        ⟨l', hOK', hgrade', hwd, gnNoRepeatLE_zero hOK', hover', rfl⟩
    have herrLower :
        gnWord W l W.vacuum - gnWord W l' W.vacuum ∈
          gnSpanBounded W gen wt (G - 1) 0 :=
      (hLower (G - 1) (by omega)) herr
    have herrHere :
        gnWord W l W.vacuum - gnWord W l' W.vacuum ∈
          gnSpanBounded W gen wt G 0 :=
      gnSpanBounded_mono_grade W gen wt (by omega) herrLower
    have hadd := Submodule.add_mem (gnSpanBounded W gen wt G 0) herrHere hsorted
    convert hadd using 1 <;> abel

/-- The genuinely lower filtration is absorbed by the strictly lower bounded-reach hypothesis. -/
theorem gnLink2_lowerFil_le_bounded_zero (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (G : ℕ)
    (hLower : ∀ G' : ℕ, G' < G → GNReachBounded W gen wt G' 0) :
    gnLink2LowerFil W G ≤ gnSpanBounded W gen wt G 0 := by
  intro x hx
  rcases Nat.eq_zero_or_pos G with rfl | hG
  · rw [gnLink2LowerFil, if_pos rfl, Submodule.mem_bot] at hx
    subst x
    exact Submodule.zero_mem _
  · have hx' : x ∈ gnGradeFil W (G - 1) := by
      simpa [gnLink2LowerFil, Nat.ne_of_gt hG] using hx
    have hlow : x ∈ gnSpanBounded W gen wt (G - 1) 0 :=
      (hLower (G - 1) (by omega)) hx'
    exact gnSpanBounded_mono_grade W gen wt (by omega) hlow

/-- **Link 1 + Link 2, bounded form.**  The outer-induction base `N=0`: representative
replacement followed by sorting, with every error absorbed at a strictly smaller grade. -/
theorem gnLink2_GNReachBounded_zero (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (G : ℕ) (hLower : ∀ G' : ℕ, G' < G → GNReachBounded W gen wt G' 0) :
    GNReachBounded W gen wt G 0 := by
  refine le_trans (gnLink2_gradeFil_le_rawSpan_sup_lower W gen wt hgen hdec G) ?_
  exact sup_le (gnLink2_rawSpan_le_bounded_zero W gen wt hwt G hLower)
    (gnLink2_lowerFil_le_bounded_zero W gen wt G hLower)

/-- Ordinary `GNReach` corollary of the grade-bounded `N=0` base case. -/
theorem gnLink2_GNReach_zero (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (G : ℕ) (hLower : ∀ G' : ℕ, G' < G → GNReachBounded W gen wt G' 0) :
    GNReach W gen wt G 0 :=
  (gnLink2_GNReachBounded_zero W gen wt hgen hwt hdec G hLower).toGNReach

/-! ## Count-preserving representative normalization for Link 4 -/

/-- Contribution of one mode index to `gnCountAt`. -/
def gnLink2CountHead (N k : ℕ) : ℕ := if k = N then 1 else 0

@[simp] theorem gnCountAt_cons_link2 (N : ℕ) (p : GNLetter 𝒱)
    (l : List (GNLetter 𝒱)) :
    gnCountAt N (p :: l) = gnLink2CountHead N p.2.2 + gnCountAt N l := by
  classical
  by_cases h : p.2.2 = N <;> simp [gnCountAt, gnLink2CountHead, h] <;> omega

/-- Raw generator words retaining both the grade cap and a bound on the multiplicity of one
chosen mode index. -/
noncomputable def gnLink2RawCountSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (G N S : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ l : List (GNLetter 𝒱),
    GNWordOK W l ∧ OverGens gen wt l ∧ gnWordGrade l ≤ G ∧ gnCountAt N l ≤ S ∧
      x = gnWord W l W.vacuum}

theorem gnLink2_word_mem_rawCountSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {G N S : ℕ} {l : List (GNLetter 𝒱)}
    (hOK : GNWordOK W l) (hgen : OverGens gen wt l)
    (hG : gnWordGrade l ≤ G) (hS : gnCountAt N l ≤ S) :
    gnWord W l W.vacuum ∈ gnLink2RawCountSpan W gen wt G N S :=
  Submodule.subset_span ⟨l, hOK, hgen, hG, hS, rfl⟩

/-- Prepending a generator preserves the exact head contribution to the count bound. -/
theorem gnLink2_prepend_rawCountSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (i : Fin g) {k G N S : ℕ} (hk : 1 ≤ k) {x : 𝒱}
    (hx : x ∈ gnLink2RawCountSpan W gen wt G N S) :
    W.smul (gen i) (-(k : ℤ)) x ∈
      gnLink2RawCountSpan W gen wt (wt i + G) N (gnLink2CountHead N k + S) := by
  refine Submodule.span_induction
    (p := fun x _ => W.smul (gen i) (-(k : ℤ)) x ∈
      gnLink2RawCountSpan W gen wt (wt i + G) N (gnLink2CountHead N k + S))
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hOK, hover, hG, hS, rfl⟩
    change gnWord W ((gen i, wt i, k) :: l) W.vacuum ∈
      gnLink2RawCountSpan W gen wt (wt i + G) N (gnLink2CountHead N k + S)
    refine gnLink2_word_mem_rawCountSpan W ?_ ?_ (by
      simp only [gnWordGrade_cons]; omega) (by
      rw [gnCountAt_cons_link2]
      change gnLink2CountHead N k + gnCountAt N l ≤ gnLink2CountHead N k + S
      omega)
    · refine ⟨?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hgen i
        · exact hOK.1 p hp
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hk
        · exact hOK.2 p hp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨i, rfl, rfl⟩
      · exact hover p hp
  · change W.smul (gen i) (-(k : ℤ)) 0 ∈
      gnLink2RawCountSpan W gen wt (wt i + G) N (gnLink2CountHead N k + S)
    rw [W.smul_zero_right]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [W.smul_add_right]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]
    exact Submodule.smul_mem _ _ hy

/-- The complete mode-index skeleton of a word. -/
def gnLink2Skeleton (l : List (GNLetter 𝒱)) : List ℕ := l.map (fun p => p.2.2)

theorem GNWeakDec_iff_link2Skeleton {l : List (GNLetter 𝒱)} :
    GNWeakDec l ↔ List.Pairwise (fun a b : ℕ => b ≤ a) (gnLink2Skeleton l) := by
  rw [gnLink2Skeleton, List.pairwise_map]
  rfl

theorem GNNoRepeatLE_iff_link2Skeleton {B : ℕ} {l : List (GNLetter 𝒱)} :
    GNNoRepeatLE B l ↔ List.Pairwise
      (fun a b : ℕ => a ≤ B → b ≤ B → a ≠ b) (gnLink2Skeleton l) := by
  rw [gnLink2Skeleton, List.pairwise_map]
  rfl

theorem GNWeakDec_of_link2Skeleton_eq {l l' : List (GNLetter 𝒱)}
    (hsk : gnLink2Skeleton l' = gnLink2Skeleton l) (h : GNWeakDec l) : GNWeakDec l' := by
  rw [GNWeakDec_iff_link2Skeleton] at h ⊢
  rwa [hsk]

theorem GNNoRepeatLE_of_link2Skeleton_eq {B : ℕ} {l l' : List (GNLetter 𝒱)}
    (hsk : gnLink2Skeleton l' = gnLink2Skeleton l)
    (h : GNNoRepeatLE B l) : GNNoRepeatLE B l' := by
  rw [GNNoRepeatLE_iff_link2Skeleton] at h ⊢
  rwa [hsk]

theorem gnCountAt_eq_countP_link2Skeleton (N : ℕ) (l : List (GNLetter 𝒱)) :
    gnCountAt N l = (gnLink2Skeleton l).countP (fun k => decide (k = N)) := by
  classical
  rw [gnCountAt, gnLink2Skeleton, List.countP_map, List.countP_eq_length_filter]
  rfl

theorem gnCountAt_eq_of_link2Skeleton_eq (N : ℕ) {l l' : List (GNLetter 𝒱)}
    (hsk : gnLink2Skeleton l' = gnLink2Skeleton l) : gnCountAt N l' = gnCountAt N l := by
  rw [gnCountAt_eq_countP_link2Skeleton, gnCountAt_eq_countP_link2Skeleton, hsk]

/-- Raw generator words with an exact prescribed mode-index skeleton. -/
noncomputable def gnLink2RawSkeletonSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (G : ℕ) (sk : List ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ l : List (GNLetter 𝒱),
    GNWordOK W l ∧ OverGens gen wt l ∧ gnWordGrade l ≤ G ∧
      gnLink2Skeleton l = sk ∧ x = gnWord W l W.vacuum}

theorem gnLink2_word_mem_rawSkeletonSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {G : ℕ} {sk : List ℕ}
    {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l) (hgen : OverGens gen wt l)
    (hG : gnWordGrade l ≤ G) (hsk : gnLink2Skeleton l = sk) :
    gnWord W l W.vacuum ∈ gnLink2RawSkeletonSpan W gen wt G sk :=
  Submodule.subset_span ⟨l, hOK, hgen, hG, hsk, rfl⟩

/-- Prepending a generator prepends exactly its mode index to the retained skeleton. -/
theorem gnLink2_prepend_rawSkeletonSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (i : Fin g) {k G : ℕ} {sk : List ℕ} (hk : 1 ≤ k) {x : 𝒱}
    (hx : x ∈ gnLink2RawSkeletonSpan W gen wt G sk) :
    W.smul (gen i) (-(k : ℤ)) x ∈
      gnLink2RawSkeletonSpan W gen wt (wt i + G) (k :: sk) := by
  refine Submodule.span_induction
    (p := fun x _ => W.smul (gen i) (-(k : ℤ)) x ∈
      gnLink2RawSkeletonSpan W gen wt (wt i + G) (k :: sk)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hOK, hover, hG, hsk, rfl⟩
    change gnWord W ((gen i, wt i, k) :: l) W.vacuum ∈
      gnLink2RawSkeletonSpan W gen wt (wt i + G) (k :: sk)
    refine gnLink2_word_mem_rawSkeletonSpan W ?_ ?_ (by
      simp only [gnWordGrade_cons]; omega) (by
      change k :: gnLink2Skeleton l = k :: sk
      rw [hsk])
    · refine ⟨?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hgen i
        · exact hOK.1 p hp
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hk
        · exact hOK.2 p hp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨i, rfl, rfl⟩
      · exact hover p hp
  · change W.smul (gen i) (-(k : ℤ)) 0 ∈
      gnLink2RawSkeletonSpan W gen wt (wt i + G) (k :: sk)
    rw [W.smul_zero_right]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [W.smul_add_right]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]
    exact Submodule.smul_mem _ _ hy

/-- **Exact-skeleton representative normalization.**  For a positive-weight admissible word,
every same-grade generator-word witness has exactly the input word's complete mode-index list.
Thus weak decrease, every no-repeat predicate, and every `gnCountAt` are all retained. -/
theorem gnLink2_word_mem_rawSkeletonSpan_sup_lower (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W) :
    ∀ (l : List (GNLetter 𝒱)), GNWordOK W l → (∀ p ∈ l, 1 ≤ p.2.1) →
      gnWord W l W.vacuum ∈
        gnLink2RawSkeletonSpan W gen wt (gnWordGrade l) (gnLink2Skeleton l) ⊔
          gnLink2LowerFil W (gnWordGrade l) := by
  classical
  intro l
  induction l with
  | nil =>
      intro _ _
      exact Submodule.mem_sup_left
        (gnLink2_word_mem_rawSkeletonSpan W (GNWordOK.nil W) (by simp [OverGens])
          (by simp) rfl)
  | cons p l ih =>
      intro hOK hpos
      have hpPos : 1 ≤ p.2.1 := hpos p (List.mem_cons_self ..)
      have htailPos : ∀ q ∈ l, 1 ≤ q.2.1 :=
        fun q hq => hpos q (List.mem_cons_of_mem _ hq)
      have htotal : gnWordGrade (p :: l) ≠ 0 := by
        rw [gnWordGrade_cons]
        omega
      have hpdec := gnLink2_homog_mem_repSpan_sup_O₂ W gen wt hgen hdec hOK.head_mem
      rw [Submodule.mem_sup] at hpdec
      obtain ⟨a, ha, b, hb, hab⟩ := hpdec
      rw [gnWord_cons, ← hab, W.smul_add_left]
      refine Submodule.add_mem _ ?_ ?_
      · refine Submodule.span_induction
          (p := fun a _ => W.smul a (-(p.2.2 : ℤ)) (gnWord W l W.vacuum) ∈
            gnLink2RawSkeletonSpan W gen wt (gnWordGrade (p :: l))
                (gnLink2Skeleton (p :: l)) ⊔ gnLink2LowerFil W (gnWordGrade (p :: l)))
          ?_ ?_ ?_ ?_ ha
        · intro y hy
          rcases hy with ⟨i, hiw, rfl⟩ | ⟨hpzero, rfl⟩
          · have htail := ih hOK.tail htailPos
            rw [Submodule.mem_sup] at htail
            obtain ⟨yr, hyr, z, hz, hyz⟩ := htail
            rw [← hyz, W.smul_add_right]
            refine Submodule.add_mem _ ?_ ?_
            · have hraw := gnLink2_prepend_rawSkeletonSpan W hgen i
                (hOK.2 p (List.mem_cons_self ..)) hyr
              exact Submodule.mem_sup_left (by
                simpa only [gnWordGrade_cons, gnLink2Skeleton, List.map_cons, hiw] using hraw)
            · by_cases hrest : gnWordGrade l = 0
              · have hz0 : z = 0 := by
                  simpa [gnLink2LowerFil, hrest, Submodule.mem_bot] using hz
                rw [hz0, W.smul_zero_right]
                exact Submodule.zero_mem _
              · have hzF : z ∈ gnGradeFil W (gnWordGrade l - 1) := by
                  simpa [gnLink2LowerFil, hrest] using hz
                have hprep := gnLink2_prepend_mem W (hgen i)
                  (hOK.2 p (List.mem_cons_self ..)) hzF
                have hleFil : wt i + (gnWordGrade l - 1)
                    ≤ gnWordGrade (p :: l) - 1 := by
                  simp only [gnWordGrade_cons, hiw]
                  omega
                have hprep' := gnGradeFil_mono W hleFil hprep
                have hlow : W.smul (gen i) (-(p.2.2 : ℤ)) z ∈
                    gnLink2LowerFil W (gnWordGrade (p :: l)) := by
                  rw [gnLink2LowerFil, if_neg htotal]
                  exact hprep'
                exact Submodule.mem_sup_right hlow
          · omega
        · change W.smul 0 (-(p.2.2 : ℤ)) (gnWord W l W.vacuum) ∈
            gnLink2RawSkeletonSpan W gen wt (gnWordGrade (p :: l))
                (gnLink2Skeleton (p :: l)) ⊔ gnLink2LowerFil W (gnWordGrade (p :: l))
          rw [W.smul_zero_left]
          exact Submodule.zero_mem _
        · intro y z _ _ hy hz
          rw [W.smul_add_left]
          exact Submodule.add_mem _ hy hz
        · intro c y _ hy
          rw [W.smul_smul_left]
          exact Submodule.smul_mem _ _ hy
      · have hbact := gnLink2_O₂_word_mem W hb.1 hb.2
          (hOK.2 p (List.mem_cons_self ..)) hOK.tail
        have hlow : W.smul b (-(p.2.2 : ℤ)) (gnWord W l W.vacuum) ∈
            gnLink2LowerFil W (gnWordGrade (p :: l)) := by
          rw [gnLink2LowerFil, if_neg htotal]
          simpa only [gnWordGrade_cons] using hbact
        exact Submodule.mem_sup_right hlow

/-- If the retained skeleton is ordered and no-repeat up to `B`, its raw generator span lies in
the corresponding grade-bounded GN target. -/
theorem gnLink2_rawSkeletonSpan_le_bounded (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) {G B : ℕ} {l₀ : List (GNLetter 𝒱)}
    (hwd : GNWeakDec l₀) (hnr : GNNoRepeatLE B l₀) :
    gnLink2RawSkeletonSpan W gen wt G (gnLink2Skeleton l₀) ≤
      gnSpanBounded W gen wt G B := by
  rw [gnLink2RawSkeletonSpan, gnSpanBounded, Submodule.span_le]
  rintro x ⟨l, hOK, hover, hgrade, hsk, rfl⟩
  exact Submodule.subset_span
    ⟨l, hOK, hgrade, GNWeakDec_of_link2Skeleton_eq hsk hwd,
      GNNoRepeatLE_of_link2Skeleton_eq hsk hnr, hover, rfl⟩

/-- Ready-to-consume ordered form: representative replacement preserves the input word's order
and no-repeat data on every same-grade branch; only the lower-grade error remains. -/
theorem gnLink2_sorted_word_mem_bounded_sup_lower (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {B : ℕ} {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l)
    (hpos : ∀ p ∈ l, 1 ≤ p.2.1) (hwd : GNWeakDec l) (hnr : GNNoRepeatLE B l) :
    gnWord W l W.vacuum ∈
      gnSpanBounded W gen wt (gnWordGrade l) B ⊔ gnLink2LowerFil W (gnWordGrade l) := by
  have hnorm := gnLink2_word_mem_rawSkeletonSpan_sup_lower
    W gen wt hgen hdec l hOK hpos
  exact (sup_le_sup (gnLink2_rawSkeletonSpan_le_bounded W gen wt hwd hnr) le_rfl) hnorm

end VOA
