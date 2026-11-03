/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbPrimEquiv
import VOA.Classification.COne.OrbC2bOcta
import VOA.Classification.COne.OrbOctaInvariant
import VOA.Classification.COne.OrbOctaGlue

/-! # OrbOcta: the octahedral analogue of Dong--Jiang Lemma 4.2 (finite conformal towers)

For `W = V₂^{S₄}` (`S₄ = OrbC2b.octa`) we prove, with no hypotheses,

`octaConformalTowerSpan_holds : OrbC2b.ConformalTowerSpan (orbifoldVOA octa)`:
`A₂(W) = W/C₂(W)` is spanned by the conformal towers `ω̄ⁿ · s̄ᵢ` of five seeds
`𝟙, T(I₄), T(I₃²), T(I₃I₆), T(I₆²)` (weights `0, 16, 36, 81, 144`).

The proof reuses the group-independent `V₂` machinery of `OrbPrim` (the polynomial model `T2`, its
primary spectrum, the Cartan product `T2_top`, and `T2_equivariant` for every automorphism) and
adds only:

* `phiE_rot2`: the transposition `rot2 = octHom (0 1)` acts on `ℂ[x,y,z]` by
  `s₃ : (x,y,z) ↦ (-x,z,y)`;
* `phiE_octa_fix` / `isS4Inv_of_fix`: the `octa`-invariant polynomials are exactly `IsS4Inv`;
* the `S₄` invariant theory of `OrbOctaInvariant`.

Unlike the tetrahedral case, no "second channel" is needed: the odd atoms `I₃` and `I₆` never
appear alone, and the even atoms `I₃², I₃I₆, I₆²` are simply kept as seeds.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbOcta
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b MvPolynomial Equiv Equiv.Perm
  VOA.LatGen VOA.LatGen.Triplet OrbRat6

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## The transposition on polynomials -/

theorem autL_rot2 (v : Fin 3 → ℂ) : autL rot2 v = ![-v 0, v 2, v 1] := by
  apply xyzL_injective
  rw [xyzL_autL]
  simp only [xyzL_apply, rot2_xyz]
  simp

/-- `rot2` acts on polynomials by `s₃`. -/
theorem phiE_rot2 (F : P3) : phiE rot2 F = s3 F := by
  have h : (phiE rot2 : P3 →ₐ[ℂ] P3) = s3 := by
    apply MvPolynomial.algHom_ext
    intro k
    change phiE _ (X k) = _
    rw [phiE_apply, substL_X, autL_rot2]
    fin_cases k <;> simp [lin, Fin.sum_univ_three, s3]
  exact congrArg (fun φ : P3 →ₐ[ℂ] P3 => φ F) h

theorem phiE_mul (g h : Aut V1) (F : P3) : phiE (g * h) F = phiE g (phiE h F) := by
  change (phiHom (g * h)) F = (phiHom g) ((phiHom h) F)
  rw [map_mul]; rfl

theorem perm_split (s : Perm (Fin 4)) :
    ∃ t : Perm (Fin 4), t ∈ alternatingGroup (Fin 4) ∧ (s = t ∨ s = t * transposition) := by
  have h : ∀ s : Perm (Fin 4), ∃ t : Perm (Fin 4),
      t ∈ alternatingGroup (Fin 4) ∧ (s = t ∨ s = t * transposition) := by
    simp only [mem_alternatingGroup]
    decide +kernel
  exact h s

/-- Every element of `octa` fixes the `S₄`-invariant polynomials. -/
theorem phiE_octa_fix {g : Aut V1} (hg : g ∈ octa) {F : P3} (hF : IsS4Inv F) :
    phiE g F = F := by
  obtain ⟨s, rfl⟩ := hg
  obtain ⟨t, ht, rfl | rfl⟩ := perm_split s
  · exact phiE_fix ht hF.1
  · rw [map_mul, phiE_mul, octHom_transposition, phiE_rot2, hF.2, phiE_fix ht hF.1]

/-- Conversely, `octa`-fixed polynomials are `S₄`-invariant. -/
theorem isS4Inv_of_fix {F : P3} (h : ∀ g ∈ octa, phiE g F = F) : IsS4Inv F := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← phiE_halfX]; exact h _ ⟨_, rfl⟩
  · rw [← phiE_halfY]; exact h _ ⟨_, rfl⟩
  · rw [← phiE_cycInv]; exact h _ ⟨_, rfl⟩
  · rw [← phiE_rot2, ← octHom_transposition]; exact h _ ⟨_, rfl⟩

/-! ## Averaging over `octa` -/

/-- `octa ≅ S₄` is finite. -/
noncomputable local instance octaFintype : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Perm (Fin 4)) octa_group.some.symm.toEquiv)

abbrev Wo : VertexOperatorAlgebra (orbifold octa).carrier := orbifoldVOA octa

/-- The averaged model `T = avg ∘ T₂ : ℂ[x,y,z] → V₂^{S₄}`. -/
abbrev Tav : P3 →ₗ[ℂ] (orbifold octa).carrier := avgT octa T2

theorem T2_mem_octa {F : P3} (hF : IsS4Inv F) : T2 F ∈ (orbifold octa).carrier :=
  fun g hg => by rw [T2_equivariant, phiE_octa_fix hg hF]

theorem Tav_coe {F : P3} (hF : IsS4Inv F) : (Tav F).val = T2 F := by
  have := OrbC2.average_fixed octa ⟨T2 F, T2_mem_octa hF⟩
  simp only [Tav, avgT, LinearMap.comp_apply]
  exact congrArg Subtype.val this

/-- The polynomial Reynolds operator of `octa`. -/
def reyO (F : P3) : P3 := ((Fintype.card octa : ℂ)⁻¹) • ∑ g : octa, phiE g.1 F

theorem reyO_fix (F : P3) {h : Aut V1} (hh : h ∈ octa) : phiE h (reyO F) = reyO F := by
  unfold reyO
  rw [map_smul, map_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft (⟨h, hh⟩ : octa)) (fun g : octa => phiE g.1 F)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Equiv.coe_mulLeft, Subgroup.coe_mul, phiE_mul]

theorem isS4Inv_reyO (F : P3) : IsS4Inv (reyO F) := isS4Inv_of_fix fun _ hg => reyO_fix F hg

theorem reyO_hom {F : P3} {n : ℕ} (hF : F.IsHomogeneous n) : (reyO F).IsHomogeneous n := by
  rw [← mem_homogeneousSubmodule]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ =>
    (mem_homogeneousSubmodule _ _).mpr (by rw [phiE_apply]; exact substL_hom _ hF))

theorem average_T2 (F : P3) : OrbC2.average octa (T2 F) = Tav (reyO F) := by
  apply Subtype.ext
  rw [Tav_coe (isS4Inv_reyO F), OrbC2.average_val, reyO, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun g _ => T2_equivariant g.1 F

theorem average_smul_T2 {A B : P3} (hA : IsS4Inv A) (hB : IsS4Inv B) (k : ℤ) :
    OrbC2.average octa ((V2m 1 le_rfl).smul (T2 A) k (T2 B)) = Wo.smul (Tav A) k (Tav B) := by
  have hmem : (V2m 1 le_rfl).smul (T2 A) k (T2 B) ∈ (orbifold octa).carrier :=
    (orbifold octa).smul_mem _ (T2_mem_octa hA) _ _ (T2_mem_octa hB)
  rw [show (V2m 1 le_rfl).smul (T2 A) k (T2 B) =
      ((⟨_, hmem⟩ : (orbifold octa).carrier) : LatModuleGen (latP 1)) from rfl,
    OrbC2.average_fixed]
  apply Subtype.ext
  change _ = (V2m 1 le_rfl).smul (Tav A).val k (Tav B).val
  rw [Tav_coe hA, Tav_coe hB]

/-! ## The primary reduction -/

/-- The five seeds: `𝟙, T(I₄), T(I₃²), T(I₃I₆), T(I₆²)`. -/
def octaSeeds : Fin 5 → (orbifold octa).carrier :=
  ![Wo.vacuum, Tav I4, Tav (I3 * I3), Tav (I3 * I6), Tav (I6 * I6)]

theorem Tav_one : Tav 1 = Wo.vacuum := by
  apply Subtype.ext
  rw [Tav_coe ⟨⟨by simp, by simp, by simp⟩, by simp⟩, T2_vac]
  rfl

theorem seed_mem {x : (orbifold octa).carrier} (hx : x ∈ Set.range octaSeeds) (N : ℤ) :
    x ∈ O₂ Wo ⊔ Submodule.span ℂ (Set.range octaSeeds) ⊔ lowerDesc Wo N :=
  Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hx))

theorem Tav_genMon_mem (t : ℕ × ℕ × ℕ × ℕ) (ht : par t % 2 = 0) :
    Tav (genMon t) ∈ O₂ Wo ⊔ Submodule.span ℂ (Set.range octaSeeds) ⊔
      lowerDesc Wo ((gdeg t : ℤ) ^ 2) := by
  rcases evenMon_cases t ht with rfl | rfl | rfl | rfl | rfl | rfl |
    ⟨u, v, hu, hv, hu1, hv1, huv, he⟩
  · rw [genMon_one, Tav_one]; exact seed_mem ⟨0, rfl⟩ _
  · rw [genMon_r2]
    have h := average_lowerDesc octa T2_r2
    exact Submodule.mem_sup_right (by simpa [gdeg] using h)
  · rw [genMon_I4]; exact seed_mem ⟨1, rfl⟩ _
  · rw [genMon_I3sq]; exact seed_mem ⟨2, rfl⟩ _
  · rw [genMon_I3I6]; exact seed_mem ⟨3, rfl⟩ _
  · rw [genMon_I6sq]; exact seed_mem ⟨4, rfl⟩ _
  · rw [he]
    have hU := isS4Inv_genMon hu
    have hV := isS4Inv_genMon hv
    obtain ⟨c, hc⟩ := T2_top (genMon u) (genMon v) (gdeg u) (gdeg v) (genMon_hom u)
      (genMon_hom v)
    have hav := average_lowerDesc octa hc
    rw [map_sub, map_smul, average_smul_T2 hU hV] at hav
    have hO : Wo.smul (Tav (genMon u)) (-((2 * gdeg u * gdeg v : ℕ) : ℤ) - 1)
        (Tav (genMon v)) ∈ O₂ Wo := by
      apply smul_le_neg_two_mem_O₂
      have : 1 ≤ 2 * gdeg u * gdeg v := by nlinarith
      omega
    have key : Tav (genMon u * genMon v) =
        c • Wo.smul (Tav (genMon u)) (-((2 * gdeg u * gdeg v : ℕ) : ℤ) - 1) (Tav (genMon v)) +
        (OrbC2.average octa (T2 (genMon u * genMon v)) - c • Wo.smul (Tav (genMon u))
          (-((2 * gdeg u * gdeg v : ℕ) : ℤ) - 1) (Tav (genMon v))) := by
      simp only [Tav, avgT, LinearMap.comp_apply]; abel
    rw [key]
    have hidx : (((gdeg u + gdeg v : ℕ) : ℤ) ^ 2) = ((gdeg t : ℤ) ^ 2) := by rw [huv]
    rw [hidx] at hav
    exact Submodule.add_mem_sup (Submodule.mem_sup_left (Submodule.smul_mem _ _ hO)) hav

/-- The `V₂`-level spanning statement (H1), from the proved spectrum bound. -/
theorem v2_prim_span (N : ℤ) : prim (V2m 1 le_rfl) N ≤
    Submodule.span ℂ (T2 '' {F | ∃ n : ℕ, F.IsHomogeneous n ∧ (n : ℤ) ^ 2 = N}) ⊔
      lowerDesc (V2m 1 le_rfl) N :=
  span_of_spectrum (V2m 1 le_rfl) primSpectrumBound_V2 (fun _ _ hF => T2_prim hF) T2_rank N

/-- **Primary reduction for `V₂^{S₄}`.** -/
theorem octaPrimaryReduction_holds : PrimaryC2Reduction Wo (Set.range octaSeeds) := by
  intro N p hp
  have hp' := v2_prim_span N (orb_prim_coe octa hp)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
  have hpa : p = OrbC2.average octa a + OrbC2.average octa b := by
    rw [← map_add, hab, OrbC2.average_fixed]
  rw [hpa]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (average_lowerDesc octa hb))
  have hmap := Submodule.mem_map_of_mem (f := OrbC2.average octa) ha
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨F, ⟨n, hn, hN⟩, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, average_T2]
  have hs := mem_span_evenMon (isS4Inv_reyO F) (reyO_hom hn)
  have hmap2 := Submodule.mem_map_of_mem (f := Tav) hs
  rw [Submodule.map_span] at hmap2
  refine (Submodule.span_le.mpr ?_) hmap2
  rintro _ ⟨_, ⟨t, ⟨ht, hpar⟩, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, ← hN, ← ht]
  exact Tav_genMon_mem t hpar

/-- **Finite conformal towers for `V₂^{S₄}`** (octahedral Dong--Jiang Lemma 4.2),
with no hypotheses. -/
theorem octaConformalTowerSpan_holds : ConformalTowerSpan (orbifoldVOA octa) :=
  conformalTowerSpan_of_primary _ octaSeeds (virPrimaryDecomp_orbifold 1 le_rfl octa)
    octaPrimaryReduction_holds

end VOA.Classification.COne.OrbOcta
