import VOA.Moonshine.MoonshineCNVnatSectorLaws
import VOA.Moonshine.MoonshineCNStringModule

/-! # The actual charge-26 string module and its proved light-cone split -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster
open scoped TensorProduct

/-- Both longitudinal choices, including at zero momentum. -/
def vnatStringModule (x y : ℤ) (a : Fin 2) : StringModule (Vnat ⊗[ℂ] hypFock) where
  wt := vnatSectorWeight x y
  wt_isInternal := vnatSectorWeight_isInternal x y
  wt_finite := vnatSectorWeight_finiteDimensional x y
  wt_bdd := ⟨x * y, fun N hN => vnatSectorWeight_negative x y N hN⟩
  c := 26
  L := vnatHypMode x y
  K := vnatHypLongitudinal a x y
  L_wt := vnatSectorWeight_mode x y
  K_wt := fun n N u _ hu => vnatSectorWeight_oscillator x y n N a u hu
  L_zero := vnatSectorWeight_energy x y
  L_comm := vnatHypMode_virasoro x y
  K_comm := vnatHypLongitudinal_comm a x y
  LK_comm := fun m n _ _ => vnatHypLongitudinal_mixed a x y m n
  B := vnatHypForm
  B_symm := ⟨vnatHypForm_symm⟩
  B_orth := vnatSectorWeight_orthogonal x y
  B_nondeg := vnatSectorWeight_nondegenerate x y
  L_adj := vnatHypForm_adjoint x y
  K_adj := vnatHypLongitudinal_adjoint a x y

theorem vnatNonzeroMomentum_cast (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    (x : ℂ) ≠ 0 ∨ (y : ℂ) ≠ 0 := by exact_mod_cast h

/-- Choose the longitudinal family furnished by the concrete PBW splitting. -/
def stringSectorFamily (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) : Fin 2 :=
  (vnatHypMode_lightConeSplit x y (vnatNonzeroMomentum_cast x y h)).choose

/-- The actual nonzero-momentum moonshine string sector. No splitting datum is assumed. -/
def stringSector (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    StringModule (Vnat ⊗[ℂ] hypFock) := vnatStringModule x y (stringSectorFamily x y h)

theorem stringSector_lightConeSplit (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    (stringSector x y h).LightConeSplit :=
  (vnatHypMode_lightConeSplit x y (vnatNonzeroMomentum_cast x y h)).choose_spec

theorem stringSector_charge (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    (stringSector x y h).c = 26 := rfl

end VOA.Moonshine.ConwayNorton
