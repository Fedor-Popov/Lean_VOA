/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Examples.GradedUnitaryCohomologyTransfer
import VOA.Examples.LeeYangCosetTransferDimension

/-!
# The weightwise harmonic step in the Lee--Yang assembly

An injective map identifying a VOA weight flag with the even steps of a Kähler
harmonic flag transports nondegeneracy and signed positivity. Vanishing of the
odd harmonic degrees is stated separately: otherwise the predecessor of degree
`2p` would differ from the image of the predecessor of filtration degree `p`.
The hypotheses concern forms, maps, and harmonic degrees, not source positivity.
-/

namespace VOA.LeeYangTransferAssembly

open GradedUnitaryCohomology
open VertexOperatorAlgebra

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}
variable {K : Type v} [AddCommGroup K] [Module ℂ K]

section Squeeze

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Equality of filtered cohomology images gives equality of harmonic flag
images: the canonical map from harmonics to cohomology is injective. -/
theorem map_eq_harmonic_flag_of_cohom_map_eq
    [FiniteDimensional ℂ K] (C : KahlerComplex K)
    (P : Submodule ℂ E) (i : E →ₗ[ℂ] C.harm) (j : ℤ)
    (hclass : P.map ((LeeYangCosetTransfer.harmonicToCohomology C.D C.Dadj).comp i) =
      C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 j) 0)) :
    P.map (C.harm.subtype.comp i) = C.flag 0 j := by
  have hPi : P.map i = C.harmOn (KahlerComplex.rowSet (Finset.Icc 0 j) 0) := by
    apply Submodule.map_injective_of_injective
      (LeeYangCosetTransfer.harmonicToCohomology_injective C.P C.pos C.D C.Dadj C.adj_D)
    exact (Submodule.map_comp i
      (LeeYangCosetTransfer.harmonicToCohomology C.D C.Dadj) P).symm.trans
      (hclass.trans (C.cohomFilt_eq_map_harm _))
  rw [Submodule.map_comp, hPi]
  exact Submodule.map_comap_subtype _ _

/-- The leading-cohomology dimension bound and source character equality force
the exact harmonic flag images used in the metric transfer theorem. -/
theorem harmonic_maps_eq_of_finrank_squeeze
    [FiniteDimensional ℂ K] (C : KahlerComplex K)
    (P : ℕ → Submodule ℂ E) (i : E →ₗ[ℂ] C.harm)
    (hi : Function.Injective
      ((LeeYangCosetTransfer.harmonicToCohomology C.D C.Dadj).comp i))
    (hfiltered : ∀ p : ℕ,
      (P p).map ((LeeYangCosetTransfer.harmonicToCohomology C.D C.Dadj).comp i) ≤
        C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0))
    (hcharacter : ∀ p : ℕ,
      (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), Module.finrank ℂ (C.leadCohom (j, 0))) =
        Module.finrank ℂ (P p)) :
    ∀ p : ℕ, (P p).map (C.harm.subtype.comp i) = C.flag 0 (2 * (p : ℤ)) := by
  intro p
  apply map_eq_harmonic_flag_of_cohom_map_eq C (P p) i (2 * (p : ℤ))
  exact LeeYangCosetTransfer.maps_eq_of_finrank_squeeze
    ((LeeYangCosetTransfer.harmonicToCohomology C.D C.Dadj).comp i) hi P
    (fun p => C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0))
    (fun p => ∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), Module.finrank ℂ (C.leadCohom (j, 0)))
    hfiltered (fun p => C.finrank_cohomFilt_row_le_lead _ 0) hcharacter p

end Squeeze

/-- Integer `R` support of ghost-zero harmonics, in the `2R` coordinate. -/
def IntegralHarmonicSupport (C : KahlerComplex K) : Prop :=
  ∀ p : ℕ, C.harmDeg (2 * (p : ℤ) + 1, 0) = ⊥

/-- The image of a predecessor flag is the predecessor harmonic flag when the
intermediate odd harmonic degree vanishes. -/
theorem pieceLT_map_eq_harmonic_predecessor
    (C : KahlerComplex K) (F : GradedFlag W) (n : ℤ)
    (i : W.grading n →ₗ[ℂ] K)
    (hpiece : ∀ p : ℕ, (F.pieceIn p n).map i = C.flag 0 (2 * (p : ℤ)))
    (hintegral : IntegralHarmonicSupport C) (p : ℕ) :
    (F.pieceLT p n).map i = C.flag 0 (2 * (p : ℤ) - 1) := by
  cases p with
  | zero =>
      simp only [GradedFlag.pieceLT_zero, Submodule.map_bot, Nat.cast_zero,
        mul_zero, zero_sub]
      rw [C.flag_eq_iSup]
      simp
  | succ p =>
      rw [GradedFlag.pieceLT_succ, hpiece p]
      have heq : 2 * ((p + 1 : ℕ) : ℤ) - 1 = 2 * (p : ℤ) + 1 := by omega
      rw [heq, C.flag_succ (L := 0) (j := 2 * (p : ℤ) + 1) (by omega),
        hintegral p, bot_sup_eq]
      congr 1
      omega

/-- Nondegeneracy and positivity descend from the positive Kähler model through
an exact filtered isometry at one conformal weight. -/
theorem gradedUnitaryAt_of_harmonic_filteredIso
    [FiniteDimensional ℂ K]
    (C : KahlerComplex K) (G : GUData C)
    (F : GradedFlag W) (n : ℤ)
    (β : LinearMap.BilinForm ℂ (W.grading n)) (h : SesqForm (W.grading n))
    (i : W.grading n →ₗ[ℂ] K) (hi : Function.Injective i)
    (hB : ∀ x y, β x y = G.B (i x) (i y))
    (hh : ∀ x y, h x y = G.h (i x) (i y))
    (hpiece : ∀ p : ℕ, (F.pieceIn p n).map i = C.flag 0 (2 * (p : ℤ)))
    (hintegral : IntegralHarmonicSupport C) :
    GradedUnitaryAt F n β h := by
  haveI : FiniteDimensional ℂ (W.grading n) := W.finrank n
  constructor
  · intro p
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingRight
    intro x hx
    apply Subtype.ext
    apply hi
    change i (x : W.grading n) = i 0
    rw [map_zero]
    apply G.eq_zero_of_B_flag (L := 0) (j := 2 * (p : ℤ))
    · rw [← hpiece p]
      exact Submodule.mem_map.mpr ⟨x, x.2, rfl⟩
    · intro y hy
      rw [← hpiece p] at hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      rw [← hB]
      exact hx ⟨z, hz⟩
  · intro p x hx hne
    have himem : i x ∈ G.layer 0 (2 * (p : ℤ)) := by
      constructor
      · rw [← hpiece p]
        exact Submodule.mem_map.mpr ⟨x, hx.1, rfl⟩
      · intro y hy
        rw [← pieceLT_map_eq_harmonic_predecessor C F n i hpiece hintegral p] at hy
        obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
        change G.B (i z) (i x) = 0
        rw [← hB]
        exact hx.2 z hz
    have hine : i x ≠ 0 := fun hzero => hne (hi (hzero.trans (map_zero i).symm))
    obtain ⟨r, hr, hvalue⟩ := G.layer_signed_pos p (by omega) (i x) himem hine
    refine ⟨r, hr, ?_⟩
    simpa only [signedForm_apply, hh] using hvalue

end VOA.LeeYangTransferAssembly
