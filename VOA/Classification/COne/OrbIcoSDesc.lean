import VOA.Classification.COne.OrbIcoMain
import VOA.Classification.COne.OrbOctaRDecomposition

/-! State-level Virasoro generation below weight 100 for the explicit icosahedral orbifold. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoS
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbIco OrbOcta MvPolynomial

/-- All negative Virasoro descendants of the vacuum and the weight-36 primary. -/
def twoSeedSpan : Submodule ℂ (orbifold ico).carrier :=
  Submodule.span ℂ {v | ∃ ks : List ℕ,
    v = virWord Wi ks Wi.vacuum ∨ v = virWord Wi ks Xico}

theorem vacuum_mem_twoSeedSpan : Wi.vacuum ∈ twoSeedSpan :=
  Submodule.subset_span ⟨[], Or.inl rfl⟩

theorem Xico_mem_twoSeedSpan : Xico ∈ twoSeedSpan :=
  Submodule.subset_span ⟨[], Or.inr rfl⟩

theorem L_mem_twoSeedSpan (m : ℕ) {v : (orbifold ico).carrier}
    (hv : v ∈ twoSeedSpan) : Wi.L (-(m : ℤ) - 1) v ∈ twoSeedSpan := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨ks, rfl | rfl⟩ := hv
    · exact Submodule.subset_span ⟨m :: ks, Or.inl rfl⟩
    · exact Submodule.subset_span ⟨m :: ks, Or.inr rfl⟩
  | zero => simp
  | add v w _ _ hv hw => exact map_add (Wi.L _) v w ▸ Submodule.add_mem _ hv hw
  | smul c v _ hv => exact map_smul (Wi.L _) c v ▸ Submodule.smul_mem _ c hv

theorem TavI_inv_low {F : P3} {n : ℕ} (hF : IcoInv F)
    (hh : F.IsHomogeneous n) (hn : n < 10) : TavI F ∈ twoSeedSpan := by
  have hs := icoInvariantSpan J10 icoInv_J10 J10_hom eval_J10 n F hF hh
  have ht := Submodule.mem_map_of_mem (f := Tb) hs
  rw [Submodule.map_span, ← Set.image_comp, ← T2_apply] at ht
  have ha := Submodule.mem_map_of_mem (f := OrbC2.average ico) ht
  rw [Submodule.map_span, ← Set.image_comp, TavI_of_inv hF] at ha
  refine (Submodule.span_le.mpr ?_) ha
  rintro _ ⟨_, ⟨a, b, c, hd, rfl⟩, rfl⟩
  have hb : b = 0 := by omega
  have hc : c = 0 := by omega
  have ha : a = 0 ∨ a = 1 := by omega
  subst b c
  rcases ha with rfl | rfl
  · simp only [Function.comp_apply, pow_zero, mul_one]
    rw [← T2_apply, TavI_of_inv icoInv_one, TavI_one]
    exact vacuum_mem_twoSeedSpan
  · simpa [Function.comp_def, TavI_of_inv, pow_zero, Xico] using Xico_mem_twoSeedSpan

/-- Below weight 100 the invariant primaries have only the vacuum and spin-six seeds. -/
theorem primary_low (N : ℤ) (hN : N < 100) :
    prim Wi N ≤ twoSeedSpan ⊔ lowerDesc Wi N := by
  intro p hp
  have hp' := v2_prim_span N (orb_prim_coe ico hp)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
  have hpa : p = OrbC2.average ico a + OrbC2.average ico b := by
    rw [← map_add, hab, OrbC2.average_fixed]
  rw [hpa]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (average_lowerDesc ico hb))
  have hmap := Submodule.mem_map_of_mem (f := OrbC2.average ico) ha
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨F, ⟨n, hn, hnN⟩, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, average_T2_ico]
  have hn10 : n < 10 := by
    have : (n : ℤ) < 10 := by nlinarith [sq_nonneg ((n : ℤ) - 10)]
    exact_mod_cast this
  exact Submodule.mem_sup_left (TavI_inv_low (icoInv_reyI F) (reyI_hom hn) hn10)

/-- Every state below weight 100 is a combination of descendants of 1 and X. -/
theorem grading_lt_100 (N : ℤ) (hN : N < 100) : Wi.grading N ≤ twoSeedSpan := by
  have hnat : ∀ n : ℕ, n < 100 → Wi.grading (n : ℤ) ≤ twoSeedSpan := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hd : lowerDesc Wi (n : ℤ) ≤ twoSeedSpan := by
        apply Submodule.span_le.mpr
        rintro v ⟨m, y, hy, rfl⟩
        apply L_mem_twoSeedSpan
        by_cases hneg : (n : ℤ) - m - 1 < 0
        · rw [Wi.positivity _ hneg, Submodule.mem_bot] at hy
          rw [hy]
          exact Submodule.zero_mem _
        · have he : (n : ℤ) - m - 1 = ((n - m - 1 : ℕ) : ℤ) := by omega
          rw [he] at hy
          exact ih (n - m - 1) (by omega) (by omega) hy
      exact le_trans (virPrimaryDecomp_orbifold 1 le_rfl ico n)
        (sup_le (le_trans (primary_low n (by exact_mod_cast hn)) (sup_le le_rfl hd)) hd)
  by_cases hneg : N < 0
  · rw [Wi.positivity _ hneg]
    exact bot_le
  · simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ N)] using hnat N.toNat (by omega)

end VOA.Classification.COne.OrbIcoS
