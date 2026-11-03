import VOA.Classification.COne.OrbC2eSeeds
import VOA.Classification.COne.OrbC2bTetra

/-! # Concrete cubic action on the tetrahedral generators in V₂

The generators are written in the weight-one currents, so the action is
computed from `rotC_xyz`, rather than postulated for an abstract automorphism.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2f
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 LatMod OrbC2c OrbC2e OrbC2b

local notation "W" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)
local notation "e" => latChargeGen (latP 1) (1 : ℤ)
local notation "f" => latChargeGen (latP 1) (-1 : ℤ)
local notation "h" => hSt (latP 1) (1 : ℤ)

theorem eps1_eq_one : eps1 = 1 := PlusCharacterTable.rankOne_cocycle 1 _ _

theorem rotC_e : rotC e = (1/2 : ℂ) • h + (-Complex.I/2) • (e+f) := by
  conv_lhs => rw [latChargeGen_eq_xyz, rotC_xyz]
  simp only [xyz, vec3, eps1_eq_one]
  change (-Complex.I/2 + Complex.I*0) • e + (1/2 : ℂ) • h +
    (1*(-Complex.I/2)-Complex.I*1*0) • f = _
  module

theorem rotC_f : rotC f = (1/2 : ℂ) • h + (Complex.I/2) • (e+f) := by
  have hf : f = xyz (1/2) (Complex.I/2) 0 := by
    simp only [xyz, vec3, eps1_eq_one, mul_one, one_mul]
    have hi : Complex.I * (Complex.I/2) = (-1/2 : ℂ) := by
      linear_combination (1/2 : ℂ) * Complex.I_mul_I
    rw [hi]
    norm_num [a1]
    rfl
  conv_lhs => rw [hf, rotC_xyz]
  simp only [xyz, vec3, eps1_eq_one]
  change (Complex.I/2 + Complex.I*0) • e + (1/2 : ℂ) • h +
    (1*(Complex.I/2)-Complex.I*1*0) • f = _
  module

theorem rotC_h : rotC h = Complex.I • e + (-Complex.I) • f := by
  conv_lhs => rw [hSt_eq_xyz, rotC_xyz]
  simp only [xyz, vec3, eps1_eq_one]
  change (0+Complex.I*1) • e + (0 : ℂ) • h + (1*0-Complex.I*1*1) • f = _
  module

/-- The norm-eight exponential generator inside V₂. -/
def cubicE : LatModuleGen (latP 1) := (W).smul e (-3) e + (W).smul f (-3) f

/-- The corresponding neutral primary generator, in current coordinates. -/
def cubicJ : LatModuleGen (latP 1) := (-6 : ℂ) • rotC cubicE - (3 : ℂ) • cubicE

/-- The orbit sum is exactly zero; this is a calculation in the actual VOA. -/
theorem cubicE_orbit_sum : cubicE + rotC cubicE + rotC (rotC cubicE) = 0 := by
  simp only [cubicE, map_add, Aut.map_smul, rotC_e, rotC_f, rotC_h,
    map_smul, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

/-- The two generator formulas for the actual ambient cubic automorphism. -/
theorem rotC_cubic_generators :
    rotC cubicJ = (-1/2 : ℂ) • cubicJ + (9/2 : ℂ) • cubicE ∧
    rotC cubicE = (-1/6 : ℂ) • cubicJ + (-1/2 : ℂ) • cubicE := by
  have ho := cubicE_orbit_sum
  constructor
  · simp only [cubicJ, map_sub, map_smul]
    linear_combination (norm := module) (-6 : ℂ) • ho
  · dsimp only [cubicJ]
    module

/-- The actual weight-nine expression in the standard ambient realization. -/
def cubicNine : LatModuleGen (latP 1) :=
  (W).smul cubicJ (-2) cubicE - (W).smul cubicE (-2) cubicJ

def cubicSixteen : LatModuleGen (latP 1) :=
  (W).smul cubicJ (-9) cubicJ + (27 : ℂ) • (W).smul cubicE (-9) cubicE

theorem cubicNine_fixed : rotC cubicNine = cubicNine := by
  obtain ⟨hj,he⟩ := rotC_cubic_generators
  simp only [cubicNine, map_sub, Aut.map_smul, hj, he,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  module

theorem cubicSixteen_fixed : rotC cubicSixteen = cubicSixteen := by
  obtain ⟨hj,he⟩ := rotC_cubic_generators
  simp only [cubicSixteen, map_add, map_smul, Aut.map_smul, hj, he,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  module

end VOA.Classification.COne.OrbC2f
