/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeNormPolynomial

/-!
# Actual mode actions are affine in central charge

In fixed PBW coordinates, a single mode action depends affinely on charge.
Commuting it through a creation word can use the central term only once.
This yields a regular actual second-mode response for the q=3 family.
A nonzero norm derivative requires a further canonical pairing calculation.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- In fixed coordinates, every actual mode on a creation word is the
affine interpolation of its actions at charges zero and one. -/
theorem chargeTransport_mode_word_affine (c h : ℂ) (m : ℤ) (w : List ℕ) :
    chargeTransport c 0 h (vermaMode c h m (negWord c h w)) =
      (1-c) • vermaMode 0 h m (negWord 0 h w)+
      c • chargeTransport 1 0 h (vermaMode 1 h m (negWord 1 h w)) := by
  induction w generalizing m with
  | nil =>
    rw [negWord_nil,negWord_nil,negWord_nil]
    by_cases hm : m<0
    · simp only [chargeTransport_negative _ _ _ m hm,chargeTransport_highest]
      module
    · by_cases hz : m=0
      · subst m
        simp only [vermaMode,verma_zero_acts,map_smul,chargeTransport_highest]
        module
      · simp [vermaMode,verma_pos_annihilate _ _ m (by omega)]
  | cons i w ih =>
    rw [negWord_cons,negWord_cons,negWord_cons,
      vermaMode_comm_apply c h m (-(i:ℤ)-1),
      vermaMode_comm_apply 0 h m (-(i:ℤ)-1),
      vermaMode_comm_apply 1 h m (-(i:ℤ)-1)]
    simp only [map_add,map_smul,chargeTransport_creation,ih,chargeTransport_word]
    split_ifs <;> simp only [LinearMap.smul_apply,Module.End.one_apply,map_smul,
      chargeTransport_word,map_zero,map_add,map_smul]
    all_goals module

/-- Transporting a state to a new charge does not change its PBW
coordinates. This composition law follows directly from the two bases. -/
theorem chargeTransport_trans (a b c h : ℂ) (v : Verma a h) :
    chargeTransport b c h (chargeTransport a b h v)=chargeTransport a c h v := by
  simp [chargeTransport]

/-- Transport to the same charge is the identity on every actual state. -/
@[simp] theorem chargeTransport_self (c h : ℂ) (v : Verma c h) :
    chargeTransport c c h v=v := by simp [chargeTransport]

/-- Fixed-coordinate mode action as an endomorphism of the charge-zero
carrier. All charge dependence is in the operator, not its domain. -/
noncomputable def chargeMode (c h : ℂ) (m : ℤ) : Module.End ℂ (Verma 0 h) :=
  (chargeTransport c 0 h).toLinearMap.comp
    ((vermaMode c h m).comp (chargeTransport 0 c h).toLinearMap)

/-- Every fixed-coordinate mode operator is affine in the charge. This
extends the word calculation to all actual states by the proved PBW basis. -/
theorem chargeMode_affine (c h : ℂ) (m : ℤ) :
    chargeMode c h m=(1-c) • chargeMode 0 h m+c • chargeMode 1 h m := by
  apply (vermaSortedBasis 0 h).ext
  intro w
  simp only [LinearMap.add_apply,LinearMap.smul_apply,chargeMode,LinearMap.comp_apply,
    LinearEquiv.coe_coe,vermaSortedBasis_apply,chargeTransport_word,chargeTransport_self]
  exact chargeTransport_mode_word_affine c h m w.val

/-- The charge derivative of a mode in fixed PBW coordinates is its
constant difference between charges one and zero. -/
noncomputable def chargeModeResponse (h : ℂ) (m : ℤ) : Module.End ℂ (Verma 0 h) :=
  chargeMode 1 h m-chargeMode 0 h m

/-- Centering the affine formula at any reference charge gives an exact
first-order response identity, with no limit or division at the root. -/
theorem chargeMode_centered (c a h : ℂ) (m : ℤ) (v : Verma 0 h) :
    chargeMode c h m v=chargeMode a h m v+(c-a) • chargeModeResponse h m v := by
  rw [chargeMode_affine c,chargeMode_affine a]
  simp only [chargeModeResponse,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply]
  module

/-- The chosen terminal source is already singular in the actual Verma
module at the minimal charge, before its vacuum projection. -/
theorem minimalThreeChargeSource_L2_at_root (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    vermaMode (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0 2
      (minimalThreeChargeSource p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ))))=0 := by
  exact nonresonant_terminal_L2 0
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 ((p-1)*2)
    (minimal_three_parameter_ne_zero p (by omega)) (by omega)
    (minimalThreeChargeKernel p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ))))
    (minimalThreeChargeKernel_below p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ))))
    (fun r hr hrN => minimalThree_diagonal_interior p r hp hcop hr hrN)
    (by omega) (minimalThree_diagonal_terminal p hp)

/-- The regular second-mode response, stored at charge zero in actual PBW
coordinates. It is defined by a finite difference of actual mode actions. -/
noncomputable def minimalThreeSecondResponseBase (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) : Verma 0 0 :=
  chargeModeResponse 0 2 (minimalThreeChargeSource p hp hcop 0)

/-- At every charge the actual second-mode defect factors by the charge
difference. The response is transported from a fixed state, so no division
at the minimal charge or unproved regularity assumption is involved. -/
theorem minimalThreeChargeSource_L2_factor (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) :
    vermaMode c 0 2 (minimalThreeChargeSource p hp hcop c) =
      (c-vermaBSACharge ((3:ℂ)/(p:ℂ))) •
        chargeTransport 0 c 0 (minimalThreeSecondResponseBase p hp hcop) := by
  have hh := chargeMode_centered c (vermaBSACharge ((3:ℂ)/(p:ℂ))) 0 2
    (minimalThreeChargeSource p hp hcop 0)
  simp only [chargeMode,LinearMap.comp_apply,LinearEquiv.coe_coe,
    chargeTransport_minimalThree_source,minimalThreeChargeSource_L2_at_root,
    map_zero,zero_add] at hh
  apply (chargeTransport c 0 0).injective
  rw [map_smul,chargeTransport_trans,chargeTransport_self]
  exact hh

/-- A fixed finite vacuum word expression for the actual second response. -/
noncomputable def minimalThreeSecondResponseExpression (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) : VirModule.VirWordExpression :=
  chargeWordExpression (minimalThreeSecondResponseBase p hp hcop)

/-- The actual vacuum L2 defect is the charge difference times the fixed
response expression evaluated at that charge. Its pairing, not just this
vector factorization, determines the still-open norm derivative. -/
theorem minimalThreeChargeVacuum_L2_factor (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) :
    VirModule.Lop c 2 (minimalThreeChargeVacuum p hp hcop c) =
      (c-vermaBSACharge ((3:ℂ)/(p:ℂ))) •
        VirModule.wordExpressionEval c (minimalThreeSecondResponseExpression p hp hcop) := by
  rw [minimalThreeChargeVacuum,← vacuumProjection_mode,minimalThreeChargeSource_L2_factor,
    map_smul,minimalThreeSecondResponseExpression,chargeWordExpression_eval]

/-- All higher positive modes have the same charge factor on the actual
quasiprimary family. The remaining response is an explicit L1 iterate. -/
theorem minimalThreeChargeVacuum_positive_factor (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) (c : ℂ) (m : ℕ) :
    VirModule.Lop c ((m:ℤ)+2) (minimalThreeChargeVacuum p hp hcop c) =
      (c-vermaBSACharge ((3:ℂ)/(p:ℂ))) • (VirModule.positiveLadderCoefficient m •
        ((VirModule.Lop c 1)^m)
          (VirModule.wordExpressionEval c (minimalThreeSecondResponseExpression p hp hcop))) := by
  rw [VirModule.Lop_positive_of_quasiprimary c _ (minimalThreeChargeVacuum_L1 p hp hcop c),
    minimalThreeChargeVacuum_L2_factor,map_smul,smul_comm]

end VOA.InverseDS.VirasoroVerma
