import VOA.Classification.COne.OrbOctaZDSeed36

/-! Graded descent for the zero conformal fiber, retaining the invariant primaries. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbOcta OrbC2b OrbC2c OrbOctaZC OrbOctaR

noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

theorem q24_grading_below (B : ℕ)
    (hmon : ∀ t : ℕ × ℕ × ℕ × ℕ, par t % 2 = 0 → 0 < gdeg t →
      gdeg t ^ 2 < B → q24L (mk W (Tav (genMon t))) = 0) :
    ∀ N : ℤ, 0 < N → N < B → ∀ y ∈ W.grading N, q24L (mk W y) = 0 := by
  have hnat : ∀ n : ℕ, 0 < n → n < B → ∀ y ∈ W.grading (n : ℤ),
      q24L (mk W y) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hpos hB
      have hd : lowerDesc W (n : ℤ) ≤ zeroKernel := by
        intro y hy
        exact q24_lowerDesc (fun d hp hn z hz => by
          have he : d = (d.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
          rw [he] at hz
          exact ih d.toNat (by omega) (by omega) (by omega) z hz) hy
      have hp : prim W (n : ℤ) ≤ zeroKernel := by
        intro p hp
        have hp' := v2_prim_span (n : ℤ) (orb_prim_coe octa hp)
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
        have he : p = OrbC2.average octa a + OrbC2.average octa b := by
          rw [← map_add, hab, OrbC2.average_fixed]
        rw [he]
        apply Submodule.add_mem _ ?_ (hd (average_lowerDesc octa hb))
        have hm := Submodule.mem_map_of_mem (f := OrbC2.average octa) ha
        rw [Submodule.map_span] at hm
        refine (Submodule.span_le.mpr ?_) hm
        rintro _ ⟨_, ⟨F, ⟨s, hs, hsn⟩, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, average_T2]
        have hm2 := Submodule.mem_map_of_mem (f := Tav)
          (mem_span_evenMon (isS4Inv_reyO F) (reyO_hom hs))
        rw [Submodule.map_span] at hm2
        refine (Submodule.span_le.mpr ?_) hm2
        rintro _ ⟨_, ⟨t, ⟨ht, hpar⟩, rfl⟩, rfl⟩
        apply hmon t hpar
        · have hn0 : (0 : ℤ) < n := by omega
          rw [← hsn, ← ht] at hn0
          by_contra h
          have : gdeg t = 0 := by omega
          simp [this] at hn0
        · have he : gdeg t ^ 2 = n := by exact_mod_cast (ht ▸ hsn)
          omega
      intro y hy
      exact sup_le hp hd (virPrimaryDecomp_orbifold 1 le_rfl octa n hy)
  intro N hp hB y hy
  have he : N = (N.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  rw [he] at hy
  exact hnat N.toNat (by omega) (by omega) y hy

theorem Tav_genMon_r2 (a b c d : ℕ) (ha : 0 < a) : Tav (genMon (a, b, c, d)) = 0 := by
  apply Subtype.ext
  have hz : T2 (genMon (a, b, c, d)) = 0 := by
    simp [T2_apply, genMon, psi_r2, ha.ne']
  change (OrbC2.average octa (T2 (genMon (a, b, c, d)))).val = 0
  rw [hz, map_zero]
  rfl

/-- The two known invariant primaries exhaust the positive primary degrees below eight. -/
theorem q24_grading_lt64 : ∀ N : ℤ, 0 < N → N < 64 →
    ∀ y ∈ W.grading N, q24L (mk W y) = 0 := by
  apply q24_grading_below 64
  rintro ⟨a, b, c, d⟩ hp hn hb
  by_cases ha : 0 < a
  · rw [Tav_genMon_r2 a b c d ha, map_zero, map_zero]
  · have ha0 : a = 0 := by omega
    subst a
    have ht : 3 * b + 4 * c + 6 * d < 8 := by
      simp only [gdeg] at hb
      nlinarith
    simp only [par, gdeg] at hp hn
    have he : (b = 0 ∧ c = 1 ∧ d = 0) ∨ (b = 2 ∧ c = 0 ∧ d = 0) := by
      have hb2 : b ≤ 2 := by omega
      have hc1 : c ≤ 1 := by omega
      have hd1 : d ≤ 1 := by omega
      interval_cases b <;> interval_cases c <;> interval_cases d <;> omega
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simpa [genMon] using q24_seed16
    · simpa [genMon, pow_two] using q24_seed_two

end VOA.Classification.COne.OrbOctaZD
