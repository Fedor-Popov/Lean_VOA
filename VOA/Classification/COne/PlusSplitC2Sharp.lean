import VOA.Classification.COne.PlusSplitC2Boundary
import VOA.Classification.COne.PlusSplitZhuBoundary

/-! The C₂ shortcut closes the sharp Zhu dimension bound for every m ≥ 2. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusC2Sharp
open PlusC2 PlusUnitary VOA.TripletNilp VOA.LatGen VOA.LatGen.Triplet
  VOA.IntegralLattice HeisenbergN VOA.Moonshine

section Algebra
variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem neutral_monomial_mem_boundary (m : ℕ) (o w : R) (ρ σ : ℂ)
    (h8 : w ^ 2 = ρ • (o ^ 2 * w) + σ • o ^ 4) (h10 : o ^ 3 * w = 0)
    (hb : o ^ (m + 1) ∈ Submodule.span ℂ (Set.range (neutralList m o w))) (a b : ℕ) :
    o ^ a * w ^ b ∈ Submodule.span ℂ (Set.range (neutralList m o w)) := by
  let S := Submodule.span ℂ (Set.range (neutralList m o w))
  have how (a : ℕ) : o ^ a * w ∈ S := by
    by_cases ha : a < 3
    · exact Submodule.subset_span ⟨.inr ⟨a, ha⟩, rfl⟩
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + 3 := ⟨a - 3, by omega⟩
      rw [pow_add, mul_assoc, h10, mul_zero]
      exact S.zero_mem
  have hs {x : R} (hx : x ∈ S) : o * x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i | i, rfl⟩ := hx
      · change o * o ^ i.val ∈ S
        rw [← pow_succ']
        by_cases hi : i.val + 1 < m + 1
        · exact Submodule.subset_span ⟨.inl ⟨i.val + 1, hi⟩, rfl⟩
        · have he : i.val + 1 = m + 1 := by have := i.isLt; omega
          simpa only [he] using hb
      · simpa only [neutralList, ← mul_assoc, ← pow_succ'] using how (i.val + 1)
    | zero => simp only [mul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact S.smul_mem _ hx
  have ho (a : ℕ) : o ^ a ∈ S := by
    induction a with
    | zero => exact Submodule.subset_span ⟨.inl ⟨0, by omega⟩, rfl⟩
    | succ a ih => simpa only [pow_succ'] using hs ih
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases b with _ | _ | b
    · simpa using ho a
    · simpa using how a
    · have heq : o ^ a * w ^ (b + 2) =
          ρ • (o ^ (a + 2) * w ^ (b + 1)) + σ • (o ^ (a + 4) * w ^ b) := by
        rw [pow_add w b 2, h8]
        simp only [mul_add, mul_smul_comm]
        ring_nf
      rw [heq]
      exact S.add_mem (S.smul_mem _ (ih (b + 1) (by omega) (a + 2)))
        (S.smul_mem _ (ih b (by omega) (a + 4)))
end Algebra

variable (m : ℕ) (hm : 1 ≤ m)

theorem spanningList_card : Fintype.card ((Fin (m + 1) ⊕ Fin 3) ⊕ Fin 3) = m + 7 := by
  simp only [Fintype.card_sum, Fintype.card_fin]

theorem neutral_monomial_all (hm2 : 2 ≤ m) (a b : ℕ) :
    o m hm ^ a * w m hm ^ b ∈ neutralSpan m hm := by
  obtain ⟨ρ, σ, h8⟩ := rel8M_holds m hm
  have h8' := congrArg (poissonIncl m hm) h8
  simp only [map_pow, map_add, map_smul, map_mul, poissonIncl_mk₂] at h8'
  apply neutral_monomial_mem_boundary m (o m hm) (w m hm) ρ σ h8'
    (omega_cubed_W m hm)
  by_cases hm4 : 4 ≤ m
  · rw [omega_pow_eq_zero_ge4 m hm hm4]; exact Submodule.zero_mem _
  · obtain ⟨c, hc⟩ := omega_boundary_relation m hm hm2
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr ⟨m - 1, by omega⟩, rfl⟩)

theorem neutral_mem_all (hm2 : 2 ≤ m) (v : (m1Sub m hm).carrier) :
    mk₂ (V2mPlus m hm) (incl m hm v) ∈ neutralSpan m hm := by
  let T := (neutralSpan m hm).comap ((mk₂ (V2mPlus m hm)).comp (incl m hm))
  suffices h : (⊤ : Submodule ℂ (m1Sub m hm).carrier) ≤ T from h Submodule.mem_top
  rw [← span_homog_eq_top (M1P m hm), Submodule.span_le]
  rintro x ⟨d, hx⟩
  have h := neutral_class_mem_monSpan m hm x hx
  change poissonIncl m hm (mk₂ (M1P m hm) x) ∈ neutralSpan m hm
  refine Submodule.span_induction
    (p := fun y _ => poissonIncl m hm y ∈ neutralSpan m hm) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨a, b, -, rfl⟩
    simp only [map_mul, map_pow, poissonIncl_mk₂]
    exact neutral_monomial_all m hm hm2 a b
  · simp only [map_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem sec0_mem_neutralSpan_all (hm2 : 2 ≤ m) (q : FockN (rank (latP m))) :
    mk₂ (V2mPlus m hm) (PP m hm (latStateGen (latP m) q 0)) ∈ neutralSpan m hm := by
  let q' := (1 / 2 : ℂ) • (q + sigmaN _ q)
  have hσ : sigmaN (rank (latP m)) q' = q' := by
    dsimp [q']; rw [map_smul, map_add, sigmaN_sigmaN, add_comm]
  let v : (m1Sub m hm).carrier :=
    ⟨latStateGen (latP m) q' 0, (mem_m1Carrier_iff m hm _).mpr ⟨_, hσ, rfl⟩⟩
  have he : PP m hm (latStateGen (latP m) q 0) = incl m hm v := by
    apply Subtype.ext
    rw [PP_coe, incl_coe, thetaLat_latStateGen, neg_zero,
      ← latStateGen_add_boson, ← latStateGen_csmul]
  rw [he]
  exact neutral_mem_all m hm hm2 v

theorem c2_span_eq_top_all (hm2 : 2 ≤ m) : neutralSpan m hm ⊔ chargedSpan m hm = ⊤ := by
  let S := neutralSpan m hm ⊔ chargedSpan m hm
  let T := S.comap (mk₂ (V2mPlus m hm))
  have hO : O₂ (V2mPlus m hm) ≤ T := by
    intro x hx
    change mk₂ _ x ∈ S
    rw [(mk₂_eq_zero_iff _).mpr hx]
    exact S.zero_mem
  have h0 : sectorP m hm 0 ≤ T := by
    rw [sectorP, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact Submodule.mem_sup_left (sec0_mem_neutralSpan_all m hm hm2 q)
  have hE : eTimesM1Plus m hm ≤ T := by
    rw [eTimesM1Plus, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change mk₂ _ ((V2mPlus m hm).smul (EP m hm) (-1) _) ∈ S
    rw [mk₂_smul_neg_one, EP_eq_y0, map_smul, smul_mul_assoc]
    exact Submodule.mem_sup_right (Submodule.smul_mem _ _
      (E_mul_neutral_mem m hm hm2 (sec0_mem_neutralSpan_all m hm hm2 q)))
  have h1 : sectorP m hm (1 : ℤ) ≤ T := by
    rw [sectorP, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact (sup_le hO hE) (sectorOneViaE_holds m hm hm2 q)
  apply top_unique
  intro x _
  obtain ⟨v, rfl⟩ := (O₂ (V2mPlus m hm)).mkQ_surjective x
  exact (sup_le hO (sup_le h0 h1)) (sector_reduction m hm v)

/-- The m+7 explicit Poisson monomials span for every m≥2, including squares. -/
theorem spanningList_span_all (hm2 : 2 ≤ m) :
    Submodule.span ℂ (Set.range (spanningList m hm)) = ⊤ := by
  rw [spanningList, Set.Sum.elim_range, Submodule.span_union]
  exact c2_span_eq_top_all m hm hm2

/-- The sharp C₂ bound, uniformly in m. -/
theorem finrank_c2_le_all (hm2 : 2 ≤ m) :
    Module.finrank ℂ (A₂ (V2mPlus m hm)) ≤ m + 7 := by
  have h := finrank_range_le_card (R := ℂ) (spanningList m hm)
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (spanningList m hm))) ≤ _ at h
  rw [spanningList_span_all m hm hm2, finrank_top] at h
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using h

end VOA.Classification.COne.PlusC2Sharp

namespace VOA.Classification.COne

/-- The original sharp Zhu dimension target is discharged by the C₂ shortcut. -/
theorem v2mPlusZhuDimensionBound_holds : V2mPlusZhuDimensionBound :=
  zhuDimensionBound_of_c2DimensionBound PlusC2Sharp.finrank_c2_le_all

/-- Only the character input remains in the Zhu semisimplicity step. -/
theorem zhuV2mPlusSemisimple_of_distinctCharacters
    (hc : V2mPlusZhuDistinctCharacters) : ZhuV2mPlusSemisimple :=
  zhuV2mPlusSemisimple_of_dimension_characters v2mPlusZhuDimensionBound_holds hc

end VOA.Classification.COne
