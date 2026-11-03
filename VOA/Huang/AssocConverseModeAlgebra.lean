import VOA.Huang.AssocConverseSeparation
import Mathlib.Algebra.FreeAlgebra

/-! # A common mode algebra for different intermediate modules

The free associative algebra on mode labels acts on every module. This allows
semisimplicity to compare different irreducibles, including equal-weight ones.
-/

namespace VOA.Huang.AssocConverse
open VOA VOA.Huang.FusionUnit

universe u v w
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}

abbrev CommonModeAlgebra (𝒱 : Type u) := FreeAlgebra ℂ (𝒱 × ℤ)

noncomputable def commonModeRep (Q : LWModule W) :
    CommonModeAlgebra 𝒱 →ₐ[ℂ] Module.End ℂ Q.carrier :=
  FreeAlgebra.lift ℂ (fun am => mode (Q.isMod.YM am.1) am.2)

@[reducible] noncomputable def commonModeModule (Q : LWModule W) :
    Module (CommonModeAlgebra 𝒱) Q.carrier :=
  Module.compHom Q.carrier (commonModeRep Q).toRingHom

theorem commonModeTower (Q : LWModule W) :
    letI := commonModeModule Q
    IsScalarTower ℂ (CommonModeAlgebra 𝒱) Q.carrier := by
  letI := commonModeModule Q
  constructor
  intro c a x
  change commonModeRep Q (c • a) x = c • commonModeRep Q a x
  rw [map_smul]
  rfl

theorem commonModeSimple (Q : LWModule W) (iQ : Q.IsIrreducibleLW) :
    letI := commonModeModule Q
    IsSimpleModule (CommonModeAlgebra 𝒱) Q.carrier := by
  letI := commonModeModule Q
  letI := commonModeTower Q
  letI := iQ.1
  refine { eq_bot_or_eq_top := fun S => ?_ }
  let T : WeakModule.Submodule' Q.isMod.toWeakModule :=
    { carrier := S.restrictScalars ℂ
      act_mem := fun a m x hx => by
        have h := S.smul_mem (FreeAlgebra.ι ℂ (a, m)) hx
        change commonModeRep Q (FreeAlgebra.ι ℂ (a, m)) x ∈ S at h
        simpa only [commonModeRep, FreeAlgebra.lift_ι_apply] using h }
  rcases iQ.2 T with h | h
  · left; ext x; exact SetLike.ext_iff.mp h x
  · right; ext x; exact SetLike.ext_iff.mp h x

/-- Schur vanishing uses module isomorphism classes, not conformal weights. -/
theorem hom_eq_zero_of_not_iso {Q R : LWModule W}
    (iQ : Q.IsIrreducibleLW) (iR : R.IsIrreducibleLW)
    (hne : ¬ LWModule.Iso W Q R)
    (f : Q.carrier →ₗ[ℂ] R.carrier) (hf : f ∈ homSpace Q.isMod R.isMod) : f = 0 := by
  by_contra h
  let e := LinearEquiv.ofBijective f (bijective_of_hom iQ iR hf h)
  exact hne ⟨⟨e, fun a m x => hf a m x⟩⟩

open Classical in
/-- Every submodule of a finite sum of mutually nonisomorphic isotypic blocks
is stable under projection to each block. Multiplicity spaces may be arbitrary
finite sets. -/
theorem single_mem_of_mode_stable {ι : Type v} [Finite ι]
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j)
    (κ : ι → Type w) [∀ j, Finite (κ j)]
    (S : Submodule ℂ (∀ j, κ j → (R j).carrier))
    (hS : ∀ a m z, z ∈ S →
      (fun j k => mode ((R j).isMod.YM a) m (z j k)) ∈ S)
    {z : ∀ j, κ j → (R j).carrier} (hz : z ∈ S) (j : ι) :
    Pi.single j (z j) ∈ S := by
  classical
  letI := Fintype.ofFinite ι
  letI (j : ι) := Fintype.ofFinite (κ j)
  letI (j : ι) := commonModeModule (R j)
  letI (j : ι) := commonModeTower (R j)
  letI (j : ι) := commonModeSimple (R j) (iR j)
  have hstable (a : CommonModeAlgebra 𝒱) {z : ∀ j, κ j → (R j).carrier}
      (hz : z ∈ S) : a • z ∈ S := by
    induction a using FreeAlgebra.induction generalizing z with
    | grade0 c =>
      have he : (algebraMap ℂ (CommonModeAlgebra 𝒱) c) • z = c • z := by
        ext j k
        change commonModeRep (R j) (algebraMap ℂ _ c) (z j k) = c • z j k
        rw [AlgHom.commutes]
        rfl
      rw [he]; exact S.smul_mem c hz
    | grade1 am =>
      change (fun j k => commonModeRep (R j) (FreeAlgebra.ι ℂ am) (z j k)) ∈ S
      simpa only [commonModeRep, FreeAlgebra.lift_ι_apply] using hS am.1 am.2 z hz
    | add a b ha hb => simpa only [add_smul] using S.add_mem (ha hz) (hb hz)
    | mul a b ha hb => simpa only [mul_smul] using ha (hb hz)
  let T : Submodule (CommonModeAlgebra 𝒱) (∀ j, κ j → (R j).carrier) :=
    { carrier := S
      zero_mem' := S.zero_mem
      add_mem' := S.add_mem
      smul_mem' := fun a _ hz => hstable a hz }
  obtain ⟨U, hU⟩ := exists_isCompl T
  let p := U.projection T hU.symm
  have hoff (l i : ι) (hli : i ≠ l) (k : κ l) (b : κ i) :
      ∀ x : (R i).carrier, p (Pi.single i (Pi.single b x)) l k = 0 := by
    let f : (R i).carrier →ₗ[ℂ] (R l).carrier :=
      (LinearMap.proj k).comp ((LinearMap.proj l).comp
        ((p.restrictScalars ℂ).comp
          ((LinearMap.single ℂ (fun j => κ j → (R j).carrier) i).comp
            (LinearMap.single ℂ (fun _ : κ i => (R i).carrier) b))))
    have hf : f ∈ homSpace (R i).isMod (R l).isMod := by
      intro a m x
      have he : Pi.single i (Pi.single b (mode ((R i).isMod.YM a) m x)) =
          FreeAlgebra.ι ℂ (a, m) •
            (Pi.single i (Pi.single b x) : ∀ j, κ j → (R j).carrier) := by
        rw [← Pi.single_smul, ← Pi.single_smul]
        have he : FreeAlgebra.ι ℂ (a, m) • x = mode ((R i).isMod.YM a) m x :=
          congrArg (fun g : Module.End ℂ (R i).carrier => g x)
            (FreeAlgebra.lift_ι_apply _ _)
        rw [he]
      change p (Pi.single i (Pi.single b (mode ((R i).isMod.YM a) m x))) l k = _
      rw [he, p.map_smul]
      exact congrArg (fun g : Module.End ℂ (R l).carrier => g (p (Pi.single i (Pi.single b x)) l k))
        (FreeAlgebra.lift_ι_apply _ _)
    have hf0 := hom_eq_zero_of_not_iso (iR i) (iR l) (fun h => hli (hne i l h)) f hf
    intro x
    exact LinearMap.congr_fun hf0 x
  have hblock (l : ι) (x : κ l → (R l).carrier) (i : ι) (hil : l ≠ i) :
      p (Pi.single l x) i = 0 := by
    funext k
    change ((p.restrictScalars ℂ).comp
      (LinearMap.single ℂ (fun j => κ j → (R j).carrier) l)) x i k = 0
    rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_eq_zero fun b _ => hoff i l hil k b (x b)
  have hpz : p z = 0 := Submodule.projection_apply_of_mem_right hU.symm hz
  have hpj : p (Pi.single j (z j)) = 0 := by
    funext i
    by_cases hi : i = j
    · subst i
      have h := congrFun hpz j
      conv_lhs at h => rw [← Finset.univ_sum_single z]
      rw [map_sum, Finset.sum_apply] at h
      simpa only [Finset.sum_eq_single j (fun b _ hb => hblock b (z b) j hb)
        (fun h => (h (Finset.mem_univ j)).elim)] using h
    · exact hblock j (z j) i (Ne.symm hi)
  exact (Submodule.projection_apply_eq_zero_iff hU.symm).mp hpj

end VOA.Huang.AssocConverse
