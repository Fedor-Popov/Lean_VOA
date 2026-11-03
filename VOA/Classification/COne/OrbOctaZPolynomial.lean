import VOA.Classification.COne.OrbOctaZSpan
import VOA.Classification.COne.OrbB5Tetra

/-! # Roots forced by the tetrahedral characters

Restriction of the thirteen known tetrahedral Zhu characters along the
inclusion W8 → V2^A4 forces thirteen distinct rational roots of every
conformal annihilator of W8. This is a necessary condition only: the Zhu
map goes from the smaller VOA to the larger VOA and need not be injective.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZ
open VOA Polynomial OrbC2b OrbZhu

/-- Inclusion of the octahedral fixed algebra in the tetrahedral one. -/
def toTetra : (orbifold octa).carrier →ₗ[ℂ] (orbifold tetra).carrier :=
  Submodule.inclusion (by
    intro x hx g hg
    exact hx g ((show tetra ≤ octa by rw [octa_eq_join]; exact le_sup_left) hg))

theorem toTetra_hom : IsVOAHom W Wt toTetra := ⟨rfl, fun _ _ _ => rfl⟩

theorem toTetra_conformal : toTetra W.conformalVector = Wt.conformalVector := rfl

/-- Every octahedral conformal relation vanishes at the thirteen A4 weights. -/
theorem forced_roots {P : ℂ[X]}
    (hP : (aeval (omegaL W) P) (mk W W.vacuum) = 0) (i : Fin 13) :
    P.eval (lam i) = 0 := by
  have h := congrArg (zhuMap toTetra_hom toTetra_conformal) hP
  rw [zhuMap_aeval, zhuMap_mk, toTetra_hom.map_vacuum, map_zero] at h
  obtain ⟨ψ, hmul, h1, hw⟩ := exists_psi
  have he := congrArg (ψ (lamIdx i)) h
  rw [psi_aeval (hmul _) (h1 _) (hw _), tetraWeight_lamIdx, map_zero] at he
  exact he

/-- The product of the thirteen roots forced by restriction. -/
def forcedPolynomial : ℂ[X] := ∏ i : Fin 13, (X - Polynomial.C (lam i))

theorem forcedPolynomial_natDegree : forcedPolynomial.natDegree = 13 := by
  rw [forcedPolynomial, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

/-- A precise divisibility obstruction on any proposed annihilator. -/
theorem forcedPolynomial_dvd {P : ℂ[X]}
    (hP : (aeval (omegaL W) P) (mk W W.vacuum) = 0) : forcedPolynomial ∣ P := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact pairwise_coprime_X_sub_C lam_injective hij
  · intro i _
    exact dvd_iff_isRoot.mpr (forced_roots hP i)

theorem annihilator_degree_ge_thirteen {P : ℂ[X]} (hne : P ≠ 0)
    (hP : (aeval (omegaL W) P) (mk W W.vacuum) = 0) : 13 ≤ P.natDegree := by
  rw [← forcedPolynomial_natDegree]
  exact natDegree_le_of_dvd (forcedPolynomial_dvd hP) hne

/-- C2 nilpotence cannot be copied verbatim into Zhu's algebra. -/
theorem omegaL_power_ne_zero (n : ℕ) : (omegaL W ^ n) (mk W W.vacuum) ≠ 0 := by
  intro hn
  have hP : (aeval (omegaL W) (X ^ n : ℂ[X])) (mk W W.vacuum) = 0 := by
    simpa using hn
  have h := forced_roots hP 9
  have h1 : lam 9 = 1 := by
    change ((1 : ℚ) : ℂ) = 1
    norm_num
  rw [eval_pow, eval_X, h1, one_pow] at h
  exact one_ne_zero h

/-- The currently proved interval for a monic annihilator's degree. -/
theorem exists_monic_conformal_annihilator_bounds :
    ∃ P : ℂ[X], P.Monic ∧ 13 ≤ P.natDegree ∧ P.natDegree ≤ 125 ∧
      aeval (omegaL W) P = 0 := by
  obtain ⟨P, hm, hd, hp⟩ := exists_monic_conformal_annihilator
  have hv : (aeval (omegaL W) P) (mk W W.vacuum) = 0 := by rw [hp]; rfl
  exact ⟨P, hm, annihilator_degree_ge_thirteen hm.ne_zero hv, hd, hp⟩

end VOA.Classification.COne.OrbOctaZ
