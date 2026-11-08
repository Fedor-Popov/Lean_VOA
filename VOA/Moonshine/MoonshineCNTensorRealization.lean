import VOA.Moonshine.MoonshineCNTensorGrading
import VOA.Moonshine.MoonshineCNRealization
import VOA.Moonshine.AutVnat

/-! The genuine tensor-product near-VOA of central charge 26. -/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct
open AutMonster

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- Tensor products of near-VOAs require neither finite weight spaces nor a lower bound. -/
noncomputable def nearTensorVOA (V : NearVOA A) (W : NearVOA B) : NearVOA (A ⊗[ℂ] B) where
  grading := nearTensorGrading V W
  isInternal := nearTensorGrading_isInternal V W
  Y := nearTensorField V W
  vacuum := V.vacuum ⊗ₜ W.vacuum
  vacuum_mem := by simpa only [zero_add] using nearTensorGrading_tmul V W V.vacuum_mem W.vacuum_mem
  grading_mode := nearTensorGrading_mode V W
  vacuum_Y := nearTensorField_vacuum V W
  creation u := by
    refine ⟨?_, fun n hn => ?_⟩
    · simpa only [mode_apply, neg_neg, sub_self] using (nearTensorField_creation V W u).1
    · exact (nearTensorField_creation V W u).2 (-n - 1) (by omega)
  locality := nearTensorField_local V W
  regularity u v := by
    obtain ⟨N, hN⟩ := nearTensorField_isField V W u v
    exact ⟨-N, fun n hn => hN (-n - 1) (by omega)⟩
  conformalVector := nearTensorConformalVector V W
  conformal_mem := by
    apply Submodule.add_mem
    · simpa only [add_zero] using nearTensorGrading_tmul V W V.conformal_mem W.vacuum_mem
    · simpa only [zero_add] using nearTensorGrading_tmul V W V.vacuum_mem W.conformal_mem
  centralCharge := V.centralCharge + W.centralCharge
  virasoro := nearTensorField_virasoro V W
  L0_grading u hu := by
    rw [show (1 : ℤ) = 0 + 1 from rfl, nearTensorField_conformal_mode]
    exact nearTensorGrading_energy V W hu
  translation := nearTensorField_translation V W

/-- The matter space in the no-ghost construction. -/
abbrev moonshineMatterSpace := Vnat ⊗[ℂ] LorentzianFockSpace

/-- `V♮ ⊗ V_{II_{1,1}}`, with its full tensor state–field map and total integer weight. -/
noncomputable def moonshineMatterNearVOA : NearVOA moonshineMatterSpace :=
  nearTensorVOA VnatVOA.toNearVOA lorentzianNearVOA

/-- The central charge is exactly `24 + 2 = 26`, without hypotheses. -/
theorem moonshineMatterNearVOA_centralCharge : moonshineMatterNearVOA.centralCharge = 26 := by
  change (24 : ℂ) + lorentzianNearVOA.centralCharge = 26
  rw [lorentzianNearVOA_centralCharge]
  norm_num

theorem moonshineMatterNearVOA_conformalVector :
    moonshineMatterNearVOA.conformalVector =
      VnatVOA.conformalVector ⊗ₜ lorentzianNearVOA.vacuum +
        VnatVOA.vacuum ⊗ₜ lorentzianNearVOA.conformalVector := rfl

theorem moonshineMatterNearVOA_tmul_field (a x : Vnat) (b y : LorentzianFockSpace) (s : ℤ) :
    moonshineMatterNearVOA.Y (a ⊗ₜ b) s (x ⊗ₜ y) =
      ∑ᶠ m : ℤ, (VnatVOA.Y a m x) ⊗ₜ[ℂ] (lorentzianNearVOA.Y b (s - m) y) :=
  nearTensorField_tmul_apply _ _ a x b y s

end VOA.Moonshine.ConwayNorton
