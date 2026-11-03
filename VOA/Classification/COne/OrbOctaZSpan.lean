import VOA.Classification.COne.OrbOctaRCFinal
import VOA.Classification.COne.OrbZhuTower
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Explicit octahedral Zhu towers

The five named homogeneous seeds and the certified C2 relation give an
unconditional 125-dimensional upper bound for Zhu's algebra. Cayley-Hamilton
then gives a monic conformal annihilator of degree at most 125. Its roots are
not identified by this argument.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZ
open VOA Polynomial VertexOperatorAlgebra OrbC2b OrbC2c OrbSpan OrbPrim OrbOcta OrbZhu

section General
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- Retain the specified seeds in the graded-descent tower span. -/
theorem towerSpan_eq_top_of_gradedDescent {ι : Type*} (s : ι → V)
    (h : GradedDescent W (Set.range s)) :
    towerSpan W (fun i => mk₂ W (s i)) = ⊤ := by
  let f : ι → A₂ W := fun i => mk₂ W (s i)
  let S : Submodule ℂ V := (towerSpan W f).comap (mk₂ W)
  have hT : Submodule.span ℂ (Set.range s) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change mk₂ W (s i) ∈ towerSpan W f
    exact Submodule.subset_span ⟨(i, 0), by simp [f]⟩
  have hO : O₂ W ≤ S := by
    intro x hx
    change mk₂ W x ∈ towerSpan W f
    rw [(mk₂_eq_zero_iff W).mpr hx]
    exact Submodule.zero_mem _
  have hL : ∀ (m : ℕ) (y : V), y ∈ S → W.L (-(m : ℤ) - 1) y ∈ S := fun m y hy =>
    mk₂_virWord_mem W f y hy [m]
  have hnat : ∀ N : ℕ, W.grading (N : ℤ) ≤ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      refine le_trans (h N) (sup_le (sup_le hO hT) ?_)
      apply Submodule.span_le.mpr
      rintro x ⟨m, y, hy, rfl⟩
      apply hL
      by_cases hneg : (N : ℤ) - m - 1 < 0
      · rw [W.positivity _ hneg, Submodule.mem_bot] at hy
        rw [hy]; exact Submodule.zero_mem _
      · have hk : (N : ℤ) - m - 1 = ((N - m - 1 : ℕ) : ℤ) := by omega
        rw [hk] at hy
        exact ih (N - m - 1) (by omega) hy
  have hall : ∀ N : ℤ, W.grading N ≤ S := by
    intro N
    by_cases hN : N < 0
    · rw [W.positivity N hN]; exact bot_le
    · have := hnat N.toNat
      rwa [Int.toNat_of_nonneg (by omega)] at this
  have hS : S = ⊤ := by
    apply top_unique
    rw [← W.isInternal.submodule_iSup_eq_top]
    exact iSup_le hall
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := mk₂_surjective W y
  have hx : x ∈ S := by rw [hS]; trivial
  exact hx

end General

abbrev W := orbifoldVOA octa

private noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

/-- The weights of the five octahedral seeds. -/
def seedWeight : Fin 5 → ℕ := ![0, 16, 36, 81, 144]

theorem seeds_homogeneous (i : Fin 5) : octaSeeds i ∈ W.grading (seedWeight i) := by
  fin_cases i
  · exact W.vacuum_mem
  · exact OrbOctaR.X_grading
  · change Tav (I3 * I3) ∈ W.grading 36
    rw [orb_mem_grading, Tav_coe (show IsS4Inv (I3 * I3) from
      ⟨isA4Inv_mul isA4Inv_I3 isA4Inv_I3, by simp [s3_I3]⟩)]
    convert T2_grad (I3_hom.mul I3_hom) using 1
  · change Tav (I3 * I6) ∈ W.grading 81
    rw [orb_mem_grading, Tav_coe (show IsS4Inv (I3 * I6) from
      ⟨isA4Inv_mul isA4Inv_I3 isA4Inv_I6, by simp [s3_I3, s3_I6]⟩)]
    convert T2_grad (I3_hom.mul I6_hom) using 1
  · change Tav (I6 * I6) ∈ W.grading 144
    rw [orb_mem_grading, Tav_coe (show IsS4Inv (I6 * I6) from
      ⟨isA4Inv_mul isA4Inv_I6 isA4Inv_I6, by simp [s3_I6]⟩)]
    convert T2_grad (I6_hom.mul I6_hom) using 1

theorem towers_all : towerSpan W (fun i => mk₂ W (octaSeeds i)) = ⊤ :=
  towerSpan_eq_top_of_gradedDescent W octaSeeds
    (gradedDescent_of_primary W _ (virPrimaryDecomp_orbifold 1 le_rfl octa)
      octaPrimaryReduction_holds)

/-- The 125 explicit C2 classes used to lift to Zhu's algebra. -/
theorem towers25 :
    Submodule.span ℂ (Set.range fun p : (Σ _ : Fin 5, Fin 25) =>
      mk₂ W (((W.L (-2)) ^ (p.2 : ℕ)) (octaSeeds p.1))) = ⊤ := by
  apply top_unique
  rw [← towers_all]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, a⟩, rfl⟩
  by_cases ha : a < 25
  · exact Submodule.subset_span ⟨⟨i, ⟨a, ha⟩⟩, exceptionalConformalEnd_pow_mk W a _ |>.symm⟩
  · obtain ⟨b, rfl⟩ : ∃ b, a = 25 + b := ⟨a - 25, by omega⟩
    dsimp only at ⊢
    rw [pow_add, conformal_pow_eq_zero W OrbOctaRC.conformal_power25_zero,
      zero_mul, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- An unconditional dimension bound; no rationality or module exhaustion. -/
theorem octa_zhu_finite :
    FiniteDimensional ℂ (A W) ∧ Module.finrank ℂ (A W) ≤ 125 := by
  have h := finrank_A_le_of_towers W octaSeeds (fun i => (seedWeight i : ℤ))
    seeds_homogeneous (fun _ => 25) (fun _ => 25) towers25
    (fun i _ ha => pow_mem_towerSub W (mk W (octaSeeds i)) ha)
  simpa using h

/-- A monic conformal relation exists; positivity of its roots remains open. -/
theorem exists_monic_conformal_annihilator :
    ∃ P : ℂ[X], P.Monic ∧ P.natDegree ≤ 125 ∧
      Polynomial.aeval (omegaL W) P = 0 := by
  letI := octa_zhu_finite.1
  exact ⟨(omegaL W).charpoly, (omegaL W).charpoly_monic,
    (omegaL W).charpoly_natDegree ▸ octa_zhu_finite.2,
    (omegaL W).aeval_self_charpoly⟩

end VOA.Classification.COne.OrbOctaZ
