import VOA.Classification.COne.OrbPos12FixedJacobi
import VOA.Classification.COne.OrbPos11Dictionary

/-! The exact Jacobi residual can exclude first insertions in the fixed algebra.
This is an explicit conditional reduction, not an assertion of the residual. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos12
open VOA CategoryTheory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.TensorCat.BraidRibbon OrbPos9 OrbPos10 OrbPos11

/-- One coefficient of the unchanged twisted Jacobi identity. -/
def ActionJacobiAt (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hSR : StronglyRational (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G))
    (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X) (N : ℕ)
    (u v : (ambient G).carrier) (x : X.carrier) (ℓ k m : ℤ) : Prop :=
  let Y := actionModes G hSR X a N
  (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
    (Y u (ℓ * N + k - i * N) (Y v (m + i * N) x) -
      negOnePow ℓ • Y v (ℓ * N + m - i * N) (Y u (k + i * N) x))) =
    ∑ᶠ i : ℕ, cbinom ((k : ℂ) / N) i •
      Y ((V2m 1 le_rfl).smul u (ℓ + i) v) (k + m - i * N) x

set_option maxHeartbeats 1000000 in
-- The concrete lattice carrier makes scalar-action conversion expensive.
/-- Every fixed-point first insertion satisfies the required supported identity,
including a zero insertion and every possible eigenspace label. -/
theorem actionJacobiAt_fixed (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR)
    (X : Ordinary (orbifoldVOA G))
    (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)
    (ha : ActionLaws G hSR E X a) (g : G) {N : ℕ} (hN : 0 < N)
    (j : ℕ) (u : (ambient G).carrier) (hu : u ∈ g.1.twistedEigenspace N j)
    (hfix : u ∈ (orbifold G).carrier) (v : (ambient G).carrier) (x : X.carrier)
    (ℓ k m : ℤ) (hk : (k + j) % (N : ℤ) = 0) :
    ActionJacobiAt G hSR X a N u v x ℓ k m := by
  by_cases hu0 : u = 0
  · subst u
    have hz (i : ℕ) : (V2m 1 le_rfl).smul 0 (ℓ + i) v = 0 :=
      PreVertexAlgebra.smul_zero_left _ _ _
    simp only [ActionJacobiAt, map_zero, Pi.zero_apply, LinearMap.zero_apply,
      smul_zero, sub_zero, finsum_zero]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    erw [hz i]
    erw [(actionModes G hSR X a N).map_zero]
    simp only [Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have hc : Complex.exp (-(2 * Real.pi * Complex.I * j) / N) = 1 := by
    have he := (Module.End.mem_eigenspace_iff (f := g.1.toLinearEquiv.toLinearMap)).mp hu
    apply smul_left_injective ℂ hu0
    exact he.symm.trans ((hfix g.1 g.2).trans (one_smul ℂ u).symm)
  have hj : (j : ℤ) % (N : ℤ) = 0 := by
    have he := (fractional_phase_iff hN 0 j).mp (by
      rw [monodromy_phase]
      simp only [Int.cast_zero, zero_div, zero_add, mul_one, Complex.exp_neg,
        Complex.exp_two_pi_mul_I, inv_one, hc])
    simpa only [zero_add] using he
  have hk0 : k % (N : ℤ) = 0 := by
    rw [Int.add_emod, hj, add_zero, Int.emod_emod] at hk
    exact hk
  obtain ⟨t, rfl⟩ := Int.dvd_of_emod_eq_zero hk0
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have he := actionModes_jacobi_fixed G hSR X a E ha hN ⟨u, hfix⟩ v x ℓ t m
  have hfrac : (((N : ℤ) * t : ℤ) : ℂ) / N = t := by
    push_cast
    exact mul_div_cancel_left₀ _ hnC
  unfold ActionJacobiAt
  dsimp only
  rw [hfrac]
  convert he using 1 <;> congr 1 <;> ext i <;> congr 3 <;> ring

/-- OPEN: the original Jacobi obligation only for first insertions outside U.
The carrier, action, twist, fractional indices and support restriction are pinned. -/
def ExceptionalActionJacobiAwayFixed : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR),
      letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      letI := E.monoid
      ∀ (Q : SimpleAction (ambient G)) (g : G),
        ActionMonodromyThrough G hSR Q.obj Q.act g →
          ∀ (j : ℕ) (u : (ambient G).carrier), u ∈ g.1.twistedEigenspace (orderOf g.1) j →
            u ∉ (orbifold G).carrier → ∀ (v : (ambient G).carrier) (x : Q.obj.carrier)
              (ℓ k m : ℤ), (k + j) % (orderOf g.1 : ℤ) = 0 →
                ActionJacobiAt G hSR Q.obj Q.act (orderOf g.1) u v x ℓ k m

/-- The proved fixed-insertion identity removes exactly that part of the
original residual; all nonfixed insertions remain an explicit premise. -/
theorem exceptionalActionTwistedJacobi_of_awayFixed
    (h : ExceptionalActionJacobiAwayFixed) : ExceptionalActionTwistedJacobi := by
  intro G hG hSR E Q g hm j u hu v x ℓ k m hk
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  by_cases hf : u ∈ (orbifold G).carrier
  · exact actionJacobiAt_fixed G hSR E Q.obj Q.act Q.laws g
      (OrbPos2.exceptional_element_order_bounds hG g).1 j u hu hf v x ℓ k m hk
  · exact h G hG hSR E Q g hm j u hu hf v x ℓ k m hk

/-- The reduced obligation is equivalent to the original, not a weakened
replacement of the requested theorem. -/
theorem exceptionalActionJacobiAwayFixed_iff :
    ExceptionalActionJacobiAwayFixed ↔ ExceptionalActionTwistedJacobi := by
  refine ⟨exceptionalActionTwistedJacobi_of_awayFixed, ?_⟩
  intro h G hG hSR E Q g hm j u hu _ v x ℓ k m hk
  exact h G hG hSR E Q g hm j u hu v x ℓ k m hk

/-- B5 still explicitly depends on genuine group-sector projections and the
nonfixed-insertion Jacobi identities. Neither premise is proved here. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_projections_awayFixed
    (hP : ExceptionalSectorProjections) (hJ : ExceptionalActionJacobiAwayFixed) :
    ExceptionalOrbifoldPositiveWeightsFact :=
  exceptionalOrbifoldPositiveWeightsFact_of_projections_jacobi hP
    (exceptionalActionTwistedJacobi_of_awayFixed hJ)

end VOA.Classification.COne.OrbPos12
