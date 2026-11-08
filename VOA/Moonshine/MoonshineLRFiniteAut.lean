import VOA.Moonshine.MoonshineLRFinOrderRigid
import VOA.Moonshine.MoonshineLRFiniteRigid

/-!
# `Aut V♮` acts faithfully on the rigid idempotents of `V♮₂`

* `vnatRigidSet`: the rigid idempotents `e·e = 2e`, `e·y = y ⇒ y = 0` of the Griess algebra `V♮₂`;
  it is stable under `Aut V♮` (`autRestrict_mem_vnatRigidSet`) and contains the Ising vectors;
* `eq_one_of_fix_rigid`: an automorphism fixing every rigid idempotent is the identity (the Ising
  vectors and their `σ`-conjugates, as in `autVnat_isOfFinOrder`);
* **`finite_autVnat_of_finite_rigid`**: if `vnatRigidSet` is finite, then `AutVnat` is finite;
* **`finite_autVnat : Finite AutVnat`**, with `finite_setOf_rigid_idempotent` for a general
finite-dimensional algebra.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop
open VOA.Moonshine.TrialityTw VOA.LatGen VOA.IntegralLattice HeisenbergN
open VOA.Moonshine.SigmaExist VOA.Moonshine.Extraspecial

/-- The Griess product on `V♮₂` as a bilinear map. -/
def vnatGriessBilin :
    VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2 :=
  LinearMap.mk₂ ℂ VnatVOA.griessMul VnatVOA.griessMul_add_left
    (fun c x y => Subtype.ext (VnatVOA.smul_smul_left c x 1 y))
    VnatVOA.griessMul_add_right
    (fun c x y => Subtype.ext (VnatVOA.smul_smul_right x c 1 y))

theorem vnatGriessBilin_apply (u v : VnatVOA.grading 2) :
    vnatGriessBilin u v = VnatVOA.griessMul u v := rfl

/-- The rigid idempotents of the Griess algebra `V♮₂`. -/
def vnatRigidSet : Set (VnatVOA.grading 2) :=
  {e | vnatGriessBilin e e = (2 : ℂ) • e ∧ ∀ y, vnatGriessBilin e y = y → y = 0}

/-- Automorphisms permute the rigid idempotents. -/
theorem autRestrict_mem_vnatRigidSet (g : AutVnat) {e : VnatVOA.grading 2}
    (he : e ∈ vnatRigidSet) : GriessAut.autRestrict g 2 e ∈ vnatRigidSet := by
  obtain ⟨h1, h2⟩ := he
  set A := GriessAut.autRestrict g 2
  constructor
  · rw [vnatGriessBilin_apply, ← GriessAut.griessMul_aut, ← vnatGriessBilin_apply, h1, map_smul]
  · intro y hy
    have hy' : vnatGriessBilin e (A.symm y) = A.symm y := by
      apply A.injective
      rw [A.apply_symm_apply, vnatGriessBilin_apply, GriessAut.griessMul_aut,
        A.apply_symm_apply, ← vnatGriessBilin_apply]
      exact hy
    rw [← A.apply_symm_apply y, h2 _ hy', A.map_zero]

theorem isingVec_mem_vnatRigidSet {α : leech.carrier} (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) :
    (⟨isingVec α s, isingVec_mem_grading_two hα s⟩ : VnatVOA.grading 2) ∈ vnatRigidSet :=
  ⟨Subtype.ext (isingVec_one_self hα s hs), isingVec_rigid hα s hs⟩

/-- An automorphism fixing every rigid idempotent fixes the untwisted block. -/
theorem fix_untwisted_of_fix_rigid (k : AutVnat)
    (hk : ∀ e ∈ vnatRigidSet, GriessAut.autRestrict k 2 e = e) :
    ∀ x : VPlus, k ((x, 0) : Vnat) = ((x, 0) : Vnat) := by
  obtain ⟨hq, hx⟩ := aut_fix_quad_minimal_of_fix_ising k (by
    intro α hα
    have hc : FrameT.sqrtEps leech α ^ 2 * latticeCocycle leech α (-α) = 1 := by
      rw [pow_two, FrameT.sqrtEps_mul_self, latticeCocycle_neg_right, latticeCocycle_sq]
    have hc' : (-FrameT.sqrtEps leech α) ^ 2 * latticeCocycle leech α (-α) = 1 := by
      rw [neg_sq]
      exact hc
    exact ⟨FrameT.sqrtEps leech α, hc,
      congrArg Subtype.val (hk _ (isingVec_mem_vnatRigidSet hα _ hc)),
      congrArg Subtype.val (hk _ (isingVec_mem_vnatRigidSet hα _ hc'))⟩)
  exact aut_fix_untwisted_of_fix_quad_minimal k hq hx

/-- **Faithfulness:** an automorphism fixing every rigid idempotent of `V♮₂` is the identity. -/
theorem eq_one_of_fix_rigid (k : AutVnat)
    (hk : ∀ e ∈ vnatRigidSet, GriessAut.autRestrict k 2 e = e) : k = 1 := by
  apply aut_eq_one_of_fix_untwisted_twistedGen k (fix_untwisted_of_fix_rigid k hk)
  have hσk : ∀ e ∈ vnatRigidSet,
      GriessAut.autRestrict (sigmaAut * k * sigmaAut⁻¹) 2 e = e := by
    intro e he
    have h1 := congrArg Subtype.val
      (hk _ (autRestrict_mem_vnatRigidSet sigmaAut⁻¹ he))
    simp only [GriessAut.autRestrict_coe] at h1
    apply Subtype.ext
    simp only [GriessAut.autRestrict_coe, Aut.mul_apply]
    rw [h1, ← Aut.mul_apply, mul_inv_cancel]
    rfl
  have hU := fix_untwisted_of_fix_rigid _ hσk
  have hsx : sigmaAut ((0, xGen) : Vnat) = ((Dnat.Ψ xGen, 0) : Vnat) := by
    rw [sigmaAut_apply, M8hKey.sigNat_Ts Dnat xGen_mem]
  apply sigmaAut.toLinearEquiv.injective
  have h := hU (Dnat.Ψ xGen)
  rw [← hsx, Aut.mul_apply, Aut.mul_apply, Aut.inv_apply,
    ← Aut.coe_toLinearEquiv, LinearEquiv.symm_apply_apply] at h
  exact h

/-- **`Aut V♮` is finite once its rigid idempotents are finite in number.** -/
theorem finite_autVnat_of_finite_rigid (hR : vnatRigidSet.Finite) : Finite AutVnat := by
  haveI : Finite vnatRigidSet := hR.to_subtype
  let Φ : AutVnat → (vnatRigidSet → vnatRigidSet) := fun g e =>
    ⟨GriessAut.autRestrict g 2 e, autRestrict_mem_vnatRigidSet g e.2⟩
  refine Finite.of_injective Φ fun g h hgh => ?_
  have hfix : ∀ e ∈ vnatRigidSet, GriessAut.autRestrict (h⁻¹ * g) 2 e = e := by
    intro e he
    have h1 := congrArg Subtype.val (congrFun hgh ⟨e, he⟩)
    apply Subtype.ext
    have h2 : g (e : Vnat) = h (e : Vnat) := congrArg Subtype.val h1
    change (h⁻¹ * g) (e : Vnat) = (e : Vnat)
    rw [Aut.mul_apply, h2, ← Aut.mul_apply, inv_mul_cancel]
    rfl
  exact (inv_mul_eq_one.mp (eq_one_of_fix_rigid _ hfix)).symm

/-- **`Aut V♮` is finite**, with no hypotheses. -/
theorem finite_autVnat : Finite AutVnat := by
  letI : FiniteDimensional ℂ (VnatVOA.grading 2) := by
    change FiniteDimensional ℂ (gradingNat 2)
    infer_instance
  exact finite_autVnat_of_finite_rigid
    (finite_setOf_rigid_idempotent vnatGriessBilin vnat_griessMul_comm)

end VOA.Moonshine.ConwayNorton.M8
