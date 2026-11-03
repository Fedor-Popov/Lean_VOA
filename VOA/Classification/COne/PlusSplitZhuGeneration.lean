import VOA.Classification.COne.PlusSplitGenerators

/-! # Strong generation descends to generation of the actual Zhu algebra

This argument takes place in the quotient itself, not just on ordinary
irreducible top spaces. It therefore does not discard a possible radical.
-/
set_option maxSynthPendingDepth 3
noncomputable section

namespace VOA.Classification.COne.PlusZhuGeneration
open PlusUnitary
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V)
@[reducible] local instance zhuRing : Ring (VOA.A W) := VOA.instRingA W
@[reducible] local instance zhuAlgebra : Algebra ℂ (VOA.A W) := VOA.instAlgebraA W

/-- Pull back a Zhu subalgebra as a linear subspace of states. -/
def preimage (B : Subalgebra ℂ (VOA.A W)) : Submodule ℂ V :=
  B.toSubmodule.comap (VOA.mk W)

theorem vacuum_mem_preimage (B : Subalgebra ℂ (VOA.A W)) :
    W.vacuum ∈ preimage W B := B.one_mem

theorem O_le_preimage (B : Subalgebra ℂ (VOA.A W)) : O W ≤ preimage W B := by
  intro x hx
  change VOA.mk W x ∈ B
  have hz : VOA.mk W x = 0 := (Submodule.Quotient.mk_eq_zero (O W)).mpr hx
  rw [hz]; exact B.zero_mem

theorem zhuMul_mem_preimage (B : Subalgebra ℂ (VOA.A W)) {x y : V}
    (hx : x ∈ preimage W B) (hy : y ∈ preimage W B) :
    zhuMul W x y ∈ preimage W B := by
  change VOA.mk W (zhuMul W x y) ∈ B
  rw [← Amul_mk (zhuRingData_holds W)]
  exact B.mul_mem hx hy

/-- Reduce a negative mode using the Zhu product or a Frenkel--Zhu residue. -/
theorem negative_mode_mem (B : Subalgebra ℂ (VOA.A W))
    {k : ℕ} {l : ℤ} {s y : V} (hs : s ∈ W.grading (k : ℤ))
    (hy : y ∈ W.grading l) (hsB : s ∈ preimage W B) (hyB : y ∈ preimage W B)
    {p : ℤ} (hp : 1 ≤ p)
    (IH : ∀ w' : ℤ, w' < k + l + p - 1 → W.grading w' ≤ preimage W B) :
    W.smul s (-p) y ∈ preimage W B := by
  have hlow : ∀ j : ℤ, -p < j → W.smul s j y ∈ preimage W B := by
    intro j hj
    exact IH _ (by omega) (W.smul_mem_grading hs hy j)
  rcases eq_or_lt_of_le hp with rfl | hp2
  · have hz := zhuMul_homogeneous W hs y
    rw [show ((k : ℤ)).toNat = k by simp, Finset.sum_range_succ',
      show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num] at hz
    have hc0 : cbz (k : ℤ) ((0 : ℕ) : ℤ) = 1 := by
      simp [cbz_apply_nonneg, gBinom]
    rw [hc0, one_smul] at hz
    have hsplit : W.smul s (-1) y = zhuMul W s y -
        ∑ i ∈ Finset.range k, cbz (k : ℤ) ((i + 1 : ℕ) : ℤ) •
          W.smul s (((i + 1 : ℕ) : ℤ) - 1) y := by
      rw [hz]; exact (add_sub_cancel_left _ _).symm
    rw [show -(1 : ℤ) = -1 from rfl, hsplit]
    exact (preimage W B).sub_mem (zhuMul_mem_preimage W B hsB hyB)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hlow _ (by omega)))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) + 2 := ⟨(p - 2).toNat, by omega⟩
    have hP : Pres W k s y n = W.smul s (-((n : ℤ) + 2)) y +
        ∑ i ∈ Finset.range (k + n), cbz ((k : ℤ) + n) ((i + 1 : ℕ) : ℤ) •
          W.smul s (((i + 1 : ℕ) : ℤ) - 2 - n) y := by
      rw [Pres, Finset.sum_range_succ']
      have hc0 : cbz ((k : ℤ) + n) ((0 : ℕ) : ℤ) = 1 := by
        simp [cbz_apply_nonneg, gBinom]
      rw [hc0, one_smul,
        show ((0 : ℕ) : ℤ) - 2 - n = -((n : ℤ) + 2) by push_cast; ring, add_comm]
    have hsplit : W.smul s (-((n : ℤ) + 2)) y = Pres W k s y n -
        ∑ i ∈ Finset.range (k + n), cbz ((k : ℤ) + n) ((i + 1 : ℕ) : ℤ) •
          W.smul s (((i + 1 : ℕ) : ℤ) - 2 - n) y := by
      rw [hP]; exact (add_sub_cancel_right _ _).symm
    rw [hsplit]
    exact (preimage W B).sub_mem (O_le_preimage W B (Pres_mem_O W hs y n))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hlow _ (by omega)))

theorem iterProd_mem (B : Subalgebra ℂ (VOA.A W)) {G : Set V}
    (hhom : ∀ s ∈ G, ∃ k : ℕ, s ∈ W.grading (k : ℤ))
    (hG : ∀ s ∈ G, ∀ k : ℤ, s ∈ W.grading k →
      (∀ w' : ℤ, w' < k → W.grading w' ≤ preimage W B) → s ∈ preimage W B)
    {x : V} (hx : IsIterProd W G x) :
    ∀ w : ℤ, x ∈ W.grading w →
      (∀ w' : ℤ, w' < w → W.grading w' ≤ preimage W B) → x ∈ preimage W B := by
  induction hx with
  | vacuum => intros; exact vacuum_mem_preimage W B
  | step s hs p hp y hy ih =>
    intro w hw IH
    obtain ⟨k, hk⟩ := hhom s hs
    obtain ⟨l, hl⟩ := isIterProd_homog (fun s hs =>
      let ⟨k, hk⟩ := hhom s hs; ⟨(k : ℤ), hk⟩) hy
    have hmem := W.smul_mem_grading hk hl (-p)
    by_cases hw' : w = (k : ℤ) + l + p - 1
    swap
    · rw [PlusUnitary.eq_zero_of_mem_grading_ne (by omega) hmem hw]
      exact (preimage W B).zero_mem
    subst hw'
    by_cases hl0 : 0 ≤ l
    swap
    · rw [show y = 0 by rw [W.positivity l (by omega), Submodule.mem_bot] at hl; exact hl,
        W.smul_zero_right]
      exact (preimage W B).zero_mem
    exact negative_mode_mem W B hk hl (hG s hs k hk fun w' hw' => IH w' (by omega))
      (ih l hl fun w' hw' => IH w' (by omega)) hp IH

/-- All strong products of homogeneous generators map into their Zhu subalgebra. -/
theorem iterProdSpan_le_preimage (B : Subalgebra ℂ (VOA.A W)) {G : Set V}
    (hhom : ∀ s ∈ G, ∃ k : ℕ, s ∈ W.grading (k : ℤ))
    (hG : ∀ s ∈ G, ∀ k : ℤ, s ∈ W.grading k →
      (∀ w' : ℤ, w' < k → W.grading w' ≤ preimage W B) → s ∈ preimage W B)
    (htop : iterProdSpan W G = ⊤) : preimage W B = ⊤ := by
  have hgrade : ∀ w : ℤ, W.grading w ≤ preimage W B := by
    refine int_strong_ind _ (fun w hw x hx => ?_) (fun w _ IH x hx => ?_)
    · rw [W.positivity w hw, Submodule.mem_bot] at hx
      rw [hx]; exact (preimage W B).zero_mem
    · have hspan : x ∈ Submodule.span ℂ {x | IsIterProd W G x} := by
        change x ∈ iterProdSpan W G; rw [htop]; trivial
      have hpi : piHom W w x ∈ preimage W B := by
        refine Submodule.span_induction (p := fun x _ => piHom W w x ∈ preimage W B)
          ?_ ?_ ?_ ?_ hspan
        · intro y hy
          obtain ⟨k, hk⟩ := isIterProd_homog (fun s hs =>
            let ⟨k, hk⟩ := hhom s hs; ⟨(k : ℤ), hk⟩) hy
          by_cases hkw : k = w
          · subst k; rw [piHom_of_mem W hk]
            exact iterProd_mem W B hhom hG hy w hk IH
          · rw [piHom_of_mem_ne W hkw hk]; exact (preimage W B).zero_mem
        · simp only [map_zero]; exact (preimage W B).zero_mem
        · intro y z _ _ hy hz
          simpa only [map_add] using (preimage W B).add_mem hy hz
        · intro c y _ hy
          simpa only [map_smul] using (preimage W B).smul_mem c hy
      rwa [piHom_of_mem W hx] at hpi
  apply top_unique
  rw [← W.isInternal.submodule_iSup_eq_top]
  exact iSup_le hgrade

/-- Generator descent from a homogeneous spanning set modulo C2. -/
theorem adjoin_eq_top_of_iterProd_mod_C2 {G : Set V}
    (hhom : ∀ s ∈ G, ∃ k : ℕ, s ∈ W.grading (k : ℤ))
    (htop : (⊤ : Submodule ℂ V) = iterProdSpan W G ⊔ O₂ W) :
    Algebra.adjoin ℂ (VOA.mk W '' G) = ⊤ := by
  let B := Algebra.adjoin ℂ (VOA.mk W '' G)
  let H := {x | IsIterProd W G x}
  have hHhom : ∀ s ∈ H, ∃ k : ℕ, s ∈ W.grading (k : ℤ) := by
    intro s hs
    obtain ⟨k, hk⟩ := isIterProd_homog (fun s hs =>
      let ⟨k, hk⟩ := hhom s hs; ⟨(k : ℤ), hk⟩) hs
    by_cases hkn : 0 ≤ k
    · exact ⟨k.toNat, by simpa [Int.toNat_of_nonneg hkn] using hk⟩
    · have hz : s = 0 := by
        rw [W.positivity k (by omega), Submodule.mem_bot] at hk; exact hk
      exact ⟨0, by rw [hz]; exact (W.grading 0).zero_mem⟩
  have hHtop : iterProdSpan W H = ⊤ :=
    iterProdSpan_eq_top W H (fun s hs =>
      let ⟨k, hk⟩ := hHhom s hs; ⟨(k : ℤ), hk⟩) htop
  have hpre : preimage W B = ⊤ := iterProdSpan_le_preimage W B hHhom
    (fun s hs k hk IH => iterProd_mem W B hhom
      (fun t ht _ _ _ => Algebra.subset_adjoin ⟨t, ht, rfl⟩) hs k hk IH) hHtop
  apply top_unique
  intro a _
  obtain ⟨v, rfl⟩ := VOA.mk_surjective W a
  change v ∈ preimage W B
  rw [hpre]; trivial

end VOA.Classification.COne.PlusZhuGeneration

namespace VOA.Classification.COne
open PlusUnitary PlusZhuGeneration

/-- The actual plus Zhu algebra is generated by [omega], [W], and [E]. -/
theorem V2mPlus_zhu_adjoin_generators (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI := instRingA (V2mPlus m hm)
    letI := instAlgebraA (V2mPlus m hm)
    Algebra.adjoin ℂ (Set.range (fun i : Fin 3 =>
      VOA.mk (V2mPlus m hm) (gP m hm i))) = ⊤ := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  have h := adjoin_eq_top_of_iterProd_mod_C2 (V2mPlus m hm)
    (G := Set.range (gP m hm))
    (by rintro s ⟨i, rfl⟩; exact ⟨wtP m i, gP_mem_grading m hm i⟩)
    (top_eq_span_iterProd m hm hm2)
  simpa only [← Set.range_comp', Function.comp_def] using h

end VOA.Classification.COne
