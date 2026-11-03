import VOA.Classification.COne.OrbOctaMain
import VOA.Classification.COne.OrbSpanConverse

/-! The two Virasoro seeds below weight 36, at the state level. -/

set_option Elab.async false

noncomputable section
namespace VOA.Classification.COne.OrbOctaR
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbOcta OrbC2b OrbC2c MvPolynomial

abbrev W := orbifoldVOA octa
abbrev X := Tav I4

noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

/-- The actual octahedral seed, with its multiplet normalization. -/
theorem X_coe : (X : VOA.LatGen.LatModuleGen (VOA.LatGen.Triplet.latP 1)) =
    (2 : ℂ) • wv 4 0 + (28 : ℂ) • wv 4 4 + (2 : ℂ) • wv 4 8 := by
  rw [Tav_coe ⟨isA4Inv_I4, s3_I4⟩, T2_I4]

theorem X_grading : X ∈ W.grading 16 := by
  rw [orb_mem_grading, Tav_coe ⟨isA4Inv_I4, s3_I4⟩]
  convert T2_grad I4_hom using 1

/-- All negative Virasoro descendants of the vacuum and the weight-16 primary. -/
def twoSeedSpan : Submodule ℂ (orbifold octa).carrier :=
  Submodule.span ℂ {v | ∃ ks : List ℕ,
    v = virWord W ks W.vacuum ∨ v = virWord W ks X}

theorem vacuum_mem_twoSeedSpan : W.vacuum ∈ twoSeedSpan :=
  Submodule.subset_span ⟨[], Or.inl rfl⟩

theorem X_mem_twoSeedSpan : X ∈ twoSeedSpan :=
  Submodule.subset_span ⟨[], Or.inr rfl⟩

theorem L_mem_twoSeedSpan (m : ℕ) {v : (orbifold octa).carrier}
    (hv : v ∈ twoSeedSpan) : W.L (-(m : ℤ) - 1) v ∈ twoSeedSpan := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨ks, rfl | rfl⟩ := hv
    · exact Submodule.subset_span ⟨m :: ks, Or.inl rfl⟩
    · exact Submodule.subset_span ⟨m :: ks, Or.inr rfl⟩
  | zero => simp
  | add v w _ _ hv hw => exact map_add (W.L _) v w ▸ Submodule.add_mem _ hv hw
  | smul c v _ hv => exact map_smul (W.L _) c v ▸ Submodule.smul_mem _ c hv

theorem Tav_genMon_low (t : ℕ × ℕ × ℕ × ℕ)
    (ht : gdeg t < 6) (hp : par t % 2 = 0) : Tav (genMon t) ∈ twoSeedSpan := by
  obtain ⟨a, b, c, d⟩ := t
  by_cases ha : a = 0
  · subst a
    simp only [gdeg, par] at ht hp
    have hd : d = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 ∨ c = 1 := by omega
    subst d b
    rcases hc with rfl | rfl
    · simpa [genMon, Tav_one] using vacuum_mem_twoSeedSpan
    · simpa [genMon] using X_mem_twoSeedSpan
  · have hz : Tav (genMon (a, b, c, d)) = 0 := by
      apply Subtype.ext
      rw [Tav_coe (isS4Inv_genMon hp), T2_apply]
      simp [genMon, psi_r2, ha]
    rw [hz]
    exact Submodule.zero_mem _

/-- At low weights the primary reduction needs no products in the C2 space. -/
theorem primary_low (N : ℤ) (hN : N < 36) :
    prim W N ≤ twoSeedSpan ⊔ lowerDesc W N := by
  intro p hp
  have hp' := v2_prim_span N (orb_prim_coe octa hp)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
  have hpa : p = OrbC2.average octa a + OrbC2.average octa b := by
    rw [← map_add, hab, OrbC2.average_fixed]
  rw [hpa]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (average_lowerDesc octa hb))
  have hmap := Submodule.mem_map_of_mem (f := OrbC2.average octa) ha
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨F, ⟨n, hn, hnN⟩, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, average_T2]
  have hn6 : n < 6 := by
    have : (n : ℤ) < 6 := by nlinarith [sq_nonneg ((n : ℤ) - 6)]
    exact_mod_cast this
  have hs := mem_span_evenMon (isS4Inv_reyO F) (reyO_hom hn)
  have hmap2 := Submodule.mem_map_of_mem (f := Tav) hs
  rw [Submodule.map_span] at hmap2
  refine (Submodule.span_le.mpr ?_) hmap2
  rintro _ ⟨_, ⟨t, ⟨ht, hpar⟩, rfl⟩, rfl⟩
  exact Submodule.mem_sup_left (Tav_genMon_low t (ht ▸ hn6) hpar)

/-- Every state below weight 36 is a combination of descendants of 1 and X. -/
theorem grading_lt_36 (N : ℤ) (hN : N < 36) : W.grading N ≤ twoSeedSpan := by
  have hnat : ∀ n : ℕ, n < 36 → W.grading (n : ℤ) ≤ twoSeedSpan := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hd : lowerDesc W (n : ℤ) ≤ twoSeedSpan := by
        apply Submodule.span_le.mpr
        rintro v ⟨m, y, hy, rfl⟩
        apply L_mem_twoSeedSpan
        by_cases hneg : (n : ℤ) - m - 1 < 0
        · rw [W.positivity _ hneg, Submodule.mem_bot] at hy
          rw [hy]
          exact Submodule.zero_mem _
        · have he : (n : ℤ) - m - 1 = ((n - m - 1 : ℕ) : ℤ) := by omega
          rw [he] at hy
          exact ih (n - m - 1) (by omega) (by omega) hy
      exact le_trans (virPrimaryDecomp_orbifold 1 le_rfl octa n)
        (sup_le (le_trans (primary_low n (by exact_mod_cast hn)) (sup_le le_rfl hd)) hd)
  by_cases hneg : N < 0
  · rw [W.positivity _ hneg]
    exact bot_le
  · simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ N)] using hnat N.toNat (by omega)

end VOA.Classification.COne.OrbOctaR
