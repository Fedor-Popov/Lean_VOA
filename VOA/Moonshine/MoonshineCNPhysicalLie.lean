import VOA.Moonshine.MoonshineCNNearConsequences
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! The physical-state Lie algebra of a near-VOA, defined without a bilinear form. -/

namespace VOA.NearVOA

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

/-- Weight-one states annihilated by every positive Virasoro mode. -/
def primaryWeightOne : Submodule ℂ H where
  carrier := {v | V.L 0 v = v ∧ ∀ n : ℤ, 0 < n → V.L n v = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hxpos⟩ ⟨hy, hypos⟩
    exact ⟨by rw [map_add, hx, hy], fun n hn => by rw [map_add, hxpos n hn, hypos n hn, add_zero]⟩
  smul_mem' := by
    rintro c x ⟨hx, hxpos⟩
    exact ⟨by rw [map_smul, hx], fun n hn => by rw [map_smul, hxpos n hn, smul_zero]⟩

theorem primary_zeroMode_closed (u v : V.primaryWeightOne) :
    V.smul u 0 v ∈ V.primaryWeightOne := by
  constructor
  · rw [← V.primary_zeroMode_commutes u u.property.1 u.property.2, v.property.1]
  · intro n hn
    rw [← V.primary_zeroMode_commutes u u.property.1 u.property.2, v.property.2 n hn]
    exact map_zero (mode (V.Y u) 0)

/-- The zero-product before taking the spurious quotient is bilinear. -/
noncomputable def primaryZeroProduct :
    V.primaryWeightOne →ₗ[ℂ] V.primaryWeightOne →ₗ[ℂ] V.primaryWeightOne where
  toFun u :=
    { toFun := fun v => ⟨V.smul u 0 v, V.primary_zeroMode_closed u v⟩
      map_add' := fun v w => Subtype.ext (map_add (mode (V.Y u) 0) (v : H) (w : H))
      map_smul' := fun c v => Subtype.ext (map_smul (mode (V.Y u) 0) c (v : H)) }
  map_add' u v := by
    ext w
    change (V.Y ((u : H) + v)) (-1) w = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' c u := by
    ext v
    change (V.Y (c • (u : H))) (-1) v = _
    simp only [map_smul, LinearMap.smul_apply]
    rfl

/-- The physical part of the space of negative Virasoro descendants. -/
noncomputable def primarySpurious : Submodule ℂ V.primaryWeightOne :=
  V.spurious.comap V.primaryWeightOne.subtype

theorem negativeVirasoro_mem_spurious (n : ℕ) (v : H) :
    V.L (-(n + 1 : ℤ)) v ∈ V.spurious :=
  (le_iSup (fun n : ℕ => LinearMap.range (V.L (-(n + 1 : ℤ)))) n) ⟨v, rfl⟩

theorem primarySpurious_right (u v : V.primaryWeightOne) (hv : v ∈ V.primarySpurious) :
    V.primaryZeroProduct u v ∈ V.primarySpurious :=
  V.zeroMode_preserves_spurious u u.property.1 u.property.2 v hv

theorem primarySpurious_left (u v : V.primaryWeightOne) (hu : u ∈ V.primarySpurious) :
    V.primaryZeroProduct u v ∈ V.primarySpurious := by
  have hs := V.skew_zero (u : H) v
  obtain ⟨z, hz⟩ := hs
  have hsum : V.smul u 0 v + V.smul v 0 u ∈ V.spurious :=
    hz ▸ V.negativeVirasoro_mem_spurious 0 z
  have hvu := V.zeroMode_preserves_spurious v v.property.1 v.property.2 u hu
  change V.smul u 0 v ∈ V.spurious
  simpa only [add_sub_cancel_right] using V.spurious.sub_mem hsum hvu

theorem primary_zeroMode_self_spurious (u : V.primaryWeightOne) :
    V.primaryZeroProduct u u ∈ V.primarySpurious := by
  obtain ⟨z, hz⟩ := V.skew_zero (u : H) u
  have hs : V.smul u 0 u + V.smul u 0 u ∈ V.spurious :=
    hz ▸ V.negativeVirasoro_mem_spurious 0 z
  have he : (2 : ℂ)⁻¹ • (V.smul u 0 u + V.smul u 0 u) = V.smul u 0 u := by
    rw [← two_smul ℂ, inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]
  change V.smul u 0 u ∈ V.spurious
  exact he ▸ V.spurious.smul_mem (2 : ℂ)⁻¹ hs

theorem primary_zeroMode_leibniz (u v w : V.primaryWeightOne) :
    V.primaryZeroProduct u (V.primaryZeroProduct v w) =
      V.primaryZeroProduct (V.primaryZeroProduct u v) w +
        V.primaryZeroProduct v (V.primaryZeroProduct u w) := by
  apply Subtype.ext
  have h := DFunLike.congr_fun (V.zeroMode_derivation u v 0) (w : H)
  change V.smul u 0 (V.smul v 0 w) - V.smul v 0 (V.smul u 0 w) =
    V.smul (V.smul u 0 v) 0 w at h
  exact sub_eq_iff_eq_add.mp h

/-- Physical states modulo physical spurious states. No form or charge assumption is used. -/
abbrev primaryLieQuotient := V.primaryWeightOne ⧸ V.primarySpurious

/-- The zero-product descends in both arguments. -/
noncomputable def primaryLieBracket :
    V.primaryLieQuotient →ₗ[ℂ] V.primaryLieQuotient →ₗ[ℂ] V.primaryLieQuotient :=
  let b := V.primaryZeroProduct.compr₂ V.primarySpurious.mkQ
  b.liftQ₂ V.primarySpurious V.primarySpurious
    (by
      intro u hu
      apply LinearMap.ext
      intro v
      exact (Submodule.Quotient.mk_eq_zero V.primarySpurious).mpr (V.primarySpurious_left u v hu))
    (by
      intro v hv
      apply LinearMap.ext
      intro u
      exact (Submodule.Quotient.mk_eq_zero V.primarySpurious).mpr (V.primarySpurious_right u v hv))

theorem primaryQuotient_mk_bracket (u v : V.primaryWeightOne) :
    V.primaryLieBracket (V.primarySpurious.mkQ u) (V.primarySpurious.mkQ v) =
      V.primarySpurious.mkQ (V.primaryZeroProduct u v) := rfl

noncomputable instance primaryLieRing : LieRing V.primaryLieQuotient where
  bracket := fun x y => V.primaryLieBracket x y
  add_lie x y z := LinearMap.congr_fun (map_add V.primaryLieBracket x y) z
  lie_add x y z := map_add (V.primaryLieBracket x) y z
  lie_self x := by
    induction x using Submodule.Quotient.induction_on with
    | _ u => exact (Submodule.Quotient.mk_eq_zero V.primarySpurious).mpr (V.primary_zeroMode_self_spurious u)
  leibniz_lie x y z := by
    induction x using Submodule.Quotient.induction_on with
    | _ u =>
      induction y using Submodule.Quotient.induction_on with
      | _ v =>
        induction z using Submodule.Quotient.induction_on with
        | _ w =>
          change V.primarySpurious.mkQ (V.primaryZeroProduct u (V.primaryZeroProduct v w)) = _
          rw [V.primary_zeroMode_leibniz, map_add]
          rfl

noncomputable instance primaryLieAlgebra : LieAlgebra ℂ V.primaryLieQuotient where
  lie_smul c x y := map_smul (V.primaryLieBracket x) c y

end VOA.NearVOA
