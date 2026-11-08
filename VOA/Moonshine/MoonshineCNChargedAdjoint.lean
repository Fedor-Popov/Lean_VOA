import VOA.Moonshine.MoonshineCNDressingAdjoint
import VOA.Moonshine.MoonshineCNRealization

/-! FHL adjointness for the actual complex-frame charged generators. -/

namespace VOA.Moonshine.ConwayNorton

open IntegralLattice LatGen HeisenbergN Nondeg

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem latForm_canonicalChargedField_state (hEven : L.Even) (γ : L.carrier) (n : ℤ) (p q : FockN (rank L))
    (β δ : L.carrier) :
    latForm L (mode (canonicalChargedField F γ) n (latStateGen L p β)) (latStateGen L q δ)
      = (-1 : ℂ) ^ (LatGen.halfNorm L γ) * latForm L (latStateGen L p β)
          (mode (canonicalChargedField F γ) (2 * LatGen.halfNorm L γ - n - 2) (latStateGen L q δ)) := by
  rw [mode_apply, mode_apply, canonicalChargedField_tmul, canonicalChargedField_tmul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, map_smul, smul_eq_mul, latForm_state, latForm_state]
  by_cases h : γ + β + δ = 0
  · have hδ : δ = -(γ + β) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    subst hδ
    have h2 := two_halfNorm L hEven γ
    rw [if_pos (show γ + β + -(γ + β) = 0 by abel), if_pos (show β + (γ + -(γ + β)) = 0 by abel),
      uForm_dressingField_adjoint]
    have hidx : -(-n - 1 - L.form γ β)
        = -(2 * LatGen.halfNorm L γ - n - 2) - 1 - L.form γ (-(γ + β)) := by
      simp only [map_neg, map_add]
      omega
    rw [hidx, latticeCocycle_neg_right, latticeCocycle_add_right, chSign_add L hEven, chSign]
    ring
  · rw [if_neg (show ¬(γ + β + δ = 0) from h),
      if_neg (show ¬(β + (γ + δ) = 0) by intro h'; apply h; rw [← h']; abel)]
    ring

/-- **FHL invariance of `latForm` at `e^γ`**: `B(e^γ₍ₙ₎ x, y) = (−1)^N B(x, e^γ₍₂N−n−2₎ y)`,
`N = ⟨γ,γ⟩/2` (the contragredient of the primary field `Y(e^γ,z)`). -/
theorem latForm_canonicalChargedField_adjoint (hEven : L.Even) (γ : L.carrier) (n : ℤ) (x y : LatModuleGen L) :
    latForm L (mode (canonicalChargedField F γ) n x) y
      = (-1 : ℂ) ^ (LatGen.halfNorm L γ) *
          latForm L x (mode (canonicalChargedField F γ) (2 * LatGen.halfNorm L γ - n - 2) y) := by
  induction x using induction_latState L with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply, mul_add]
  | hsmul c x hx => rw [map_smul, map_smul, LinearMap.smul_apply, hx, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  | hst p β =>
    induction y using induction_latState L with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, map_add, mul_add]
    | hsmul c y hy => rw [map_smul, smul_eq_mul, hy, map_smul, map_smul, smul_eq_mul]; ring
    | hst q δ => exact latForm_canonicalChargedField_state F hEven γ n p q β δ

/-- Charged-state adjointness for the reconstructed state-field map itself. -/
theorem latForm_frameStateField_charge_adjoint (hEven : L.Even) (γ : L.carrier)
    (n : ℤ) (x y : LatModuleGen L) :
    latForm L (mode (frameStateField F hEven (latChargeGen L γ)) n x) y =
      (-1 : ℂ) ^ (LatGen.halfNorm L γ) *
        latForm L x (mode (frameStateField F hEven (latChargeGen L γ))
          (2 * LatGen.halfNorm L γ - n - 2) y) := by
  rw [frameStateField_charge]
  exact latForm_canonicalChargedField_adjoint F hEven γ n x y

end VOA.Moonshine.ConwayNorton
