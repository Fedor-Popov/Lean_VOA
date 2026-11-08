import VOA.Moonshine.MoonshineCNVnatNoGhost
import VOA.Moonshine.MoonshineCNVnatZeroQuotient

/-! # Homogeneous splitting and dimensions of the physical radical quotients -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster
open scoped TensorProduct

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup
  stringSectorWeightAddCommGroup stringSectorSliceAddCommGroup

theorem stringSector_weight_split (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) (N : ℤ)
    (u : Vnat ⊗[ℂ] hypFock) (hu : u ∈ vnatSectorWeight x y N) :
    ∃ s ∈ (stringSector x y h).spurious, ∃ k ∈ (stringSector x y h).kVacuum,
      s ∈ vnatSectorWeight x y N ∧ k ∈ vnatSectorWeight x y N ∧ s + k = u :=
  (stringSector x y h).lightConeSplit_decompose_weight
    (stringSector_lightConeSplit x y h) N u hu

theorem stringSectorNoGhost_finrank (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    Module.finrank ℂ
      ((stringSector x y h).weightRadicalQuotient (stringSector x y h).physical 1) =
      Module.finrank ℂ (VnatVOA.grading (1 - x * y)) :=
  (stringSectorNoGhostEquiv x y h).finrank_eq

theorem vnatZeroNoGhost_finrank :
    Module.finrank ℂ
      ((vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1) = 2 := by
  rw [vnatZeroNoGhostEquiv.finrank_eq]
  simp

end VOA.Moonshine.ConwayNorton
