import VOA.Classification.COne.OrbIcoTBinary
import VOA.Classification.COne.OrbIcoSPrimary

/-! The nonzero sixth-channel coupling for the actual icosahedral VOA primary. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbIco VOA.LatGen VOA.LatGen.Triplet

/-- The normalization in the repository's icosahedral frame. -/
def icoSixthCoupling : ℂ := mu6 * OrbIcoS.sixthScalar

theorem icoSixthCoupling_ne_zero : icoSixthCoupling ≠ 0 :=
  mul_ne_zero mu6_ne_zero OrbIcoS.sixthScalar_ne_zero

theorem Xico_eq_Tb : (Xico : LatModuleGen (latP 1)) = Tb fpoly := by
  change (TavI J6).val = _
  rw [TavI_coe icoInv_J6, T2_J6]

/-- The sixth-channel VOA bridge, with the actual invariant seed. -/
theorem ico_sixth_channel :
    V2v.smul (Xico : LatModuleGen (latP 1)) 35 Xico -
      icoSixthCoupling • (Xico : LatModuleGen (latP 1)) ∈ lowerDesc V2v 36 := by
  rw [Xico_eq_Tb]
  exact sixth_ico

theorem form_lowerDesc_primary {N : ℤ} {x p : LatModuleGen (latP 1)}
    (hx : x ∈ lowerDesc V2v N) (hp : p ∈ prim V2v N) :
    (v2mVirUnitary 1 le_rfl).form x p = 0 := by
  rw [mem_prim] at hp
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, y, hy, rfl⟩ := hz
    rw [(v2mVirUnitary 1 le_rfl).adjoint,
      show -(-(m : ℤ) - 1) = (m : ℤ) + 1 by ring, hp.2 m, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

/-- The residual primary-field measurement used by the level-38/40 Ward identities. -/
theorem ico_ground_coupling :
    (v2mVirUnitary 1 le_rfl).form
      (V2v.smul (Xico : LatModuleGen (latP 1)) 35 Xico) Xico =
        icoSixthCoupling * (v2mVirUnitary 1 le_rfl).form
          (Xico : LatModuleGen (latP 1)) Xico := by
  have h := form_lowerDesc_primary ico_sixth_channel OrbIcoS.Xico_ambient_primary
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact sub_eq_zero.mp h

theorem ico_ground_coupling_ne_zero :
    (v2mVirUnitary 1 le_rfl).form
      (V2v.smul (Xico : LatModuleGen (latP 1)) 35 Xico) Xico ≠ 0 := by
  rw [ico_ground_coupling]
  exact mul_ne_zero icoSixthCoupling_ne_zero OrbIcoS.Xico_norm_ne_zero

/-- Ward evaluation with the certified residual coupling. -/
theorem ico_charged_mode_combo (n : ℤ) (N : ℕ) (hn : n + (N : ℤ) = 35)
    (cs : List (ℚ × List ℕ))
    (hcs : ∀ t ∈ cs, t.2.sum = N ∧ ∀ k ∈ t.2, 0 < k) :
    OrbIcoS.chargedProbe
      (OrbOctaRC.virCombo (V2m 1 le_rfl) (Xico : LatModuleGen (latP 1)) cs)
      (Wi.smul Xico n Xico) =
        (OrbOctaRC.wardSum 36 n cs : ℂ) * icoSixthCoupling *
          (v2mVirUnitary 1 le_rfl).form (Xico : LatModuleGen (latP 1)) Xico := by
  rw [OrbIcoS.charged_mode_combo _ n N cs hcs, hn]
  change _ * (v2mVirUnitary 1 le_rfl).form
    (V2v.smul (Xico : LatModuleGen (latP 1)) 35 Xico) Xico = _
  rw [ico_ground_coupling, mul_assoc]

end VOA.Classification.COne.OrbIcoT
