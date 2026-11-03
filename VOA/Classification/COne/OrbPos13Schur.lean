import VOA.Classification.COne.OrbPos11Irreducible
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! Schur's lemma for the actual simple extension action. The underlying
ordinary module is not assumed simple. No descent of monodromy is assumed. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos13
open VOA CategoryTheory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.HKLRational OrbPos9 OrbPos10 OrbPos11

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR)

set_option maxHeartbeats 1000000 in
-- Conversions involving the concrete lattice carrier need additional unfolding.
/-- A-linearity implies commutation with every coefficient of the action. -/
theorem actionLinear_coefficients (X : Ordinary (orbifoldVOA G))
    (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)
    (f : X ⟶ X)
    (hf : letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      IsLinear a a f) (n : ℂ) (v : (ambient G).carrier) (x : X.carrier) :
    f.val ((actionIntertwiner G hSR X a).val n v x) =
      (actionIntertwiner G hSR X a).val n v (f.val x) := by
  have he := congrArg (fun t => t.val
    (((fusionChoice_pbw hSR) (ambient G) X).intertwiner.val n v x)) hf
  change (a.val ((tensorHom (fusionChoice_pbw hSR) (𝟙 (ambient G)) f).val
    (((fusionChoice_pbw hSR) (ambient G) X).intertwiner.val n v x))) =
      f.val (a.val (((fusionChoice_pbw hSR) (ambient G) X).intertwiner.val n v x)) at he
  rw [tensorHom_intertwiner, Ordinary.id_apply] at he
  exact he.symm

set_option maxHeartbeats 1000000 in
-- Eigenspace stability unfolds scalar actions on the concrete lattice carrier.
/-- Full Schur lemma on End_A(Q). Finite dimensionality is used only for the
ordinary endomorphism space, not for Q's generally infinite carrier. -/
theorem simpleAction_endomorphism_scalar :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    ∀ (Q : SimpleAction (ambient G)) (f : Q.obj ⟶ Q.obj),
      IsLinear Q.act Q.act f → ∃ c : ℂ, f = c • 𝟙 Q.obj := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  intro Q f hf
  letI := VOA.Huang.TensorCat.RepPackaging.finiteDimensional_hom_pbw hSR Q.obj Q.obj
  letI : Nontrivial (Q.obj ⟶ Q.obj) := ⟨⟨𝟙 Q.obj, 0, Q.nonzero⟩⟩
  let L : Module.End ℂ (Q.obj ⟶ Q.obj) :=
    { toFun := fun t => t ≫ f
      map_add' := by intros; simp [Preadditive.add_comp]
      map_smul' := by intros; simp }
  obtain ⟨c, hc⟩ := L.exists_eigenvalue
  obtain ⟨t, ht⟩ := hc.exists_hasEigenvector
  let K := Module.End.eigenspace f.val c
  have hK : ∀ n v x, x ∈ K →
      (actionIntertwiner G hSR Q.obj Q.act).val n v x ∈ K := by
    intro n v x hx
    have hx := Module.End.mem_eigenspace_iff.mp hx
    apply Module.End.mem_eigenspace_iff.mpr
    change f.val ((actionIntertwiner G hSR Q.obj Q.act).val n v x) = _
    rw [actionLinear_coefficients G hSR Q.obj Q.act f hf, hx, map_smul]
  have hne : K ≠ ⊥ := by
    intro hz
    apply ht.2
    apply Ordinary.hom_ext
    intro x
    have hx : t.val x ∈ K := by
      apply Module.End.mem_eigenspace_iff.mpr
      exact congrArg (fun k : Q.obj ⟶ Q.obj => k.val x) ht.apply_eq_smul
    simpa only [hz, Submodule.mem_bot] using hx
  have htop := (simpleAction_coefficient_irreducible G hSR E Q K hK).resolve_left hne
  refine ⟨c, Ordinary.hom_ext _ _ (fun x => ?_)⟩
  have hx : x ∈ K := by rw [htop]; trivial
  exact Module.End.mem_eigenspace_iff.mp hx

/-- A finite-order A-linear endomorphism has a single root-of-unity scalar.
This does not identify that scalar with a group element. -/
theorem simpleAction_finiteOrder_scalar :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    ∀ (Q : SimpleAction (ambient G)) (f : CategoryTheory.End Q.obj),
      IsLinear Q.act Q.act f → IsOfFinOrder f →
        ∃ (c : ℂ) (n : ℕ), 0 < n ∧ c ^ n = 1 ∧ f = c • 𝟙 Q.obj := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  intro Q f hf hfin
  obtain ⟨c, hc⟩ := simpleAction_endomorphism_scalar G hSR E Q f hf
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  refine ⟨c, n, hn, ?_, hc⟩
  have hc' : f = c • (1 : CategoryTheory.End Q.obj) := hc
  have he : c ^ n • (𝟙 Q.obj) = (1 : ℂ) • 𝟙 Q.obj := by
    simpa only [hc', smul_pow, one_pow, one_smul] using hpow
  exact (smul_left_injective ℂ Q.nonzero) he

end VOA.Classification.COne.OrbPos13
