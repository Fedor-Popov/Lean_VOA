/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroWeight6Norm

/-!
# The actual weight-twelve tricritical Ising relation and norm

The rational generator in Notes/certificates/virasoro_tricritical.py proposes
normal forms. Every reduction below is checked from the actual Virasoro
commutator, central commutation and vacuum annihilation. Python is not trusted.
The central operator is retained, so the norm identity also applies to
first-order deformations with a nilpotent central correction.
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false
namespace VOA.VirDeformModes
open Module (End)
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable (A : CentralVirasoroData E)

/-- The twenty-one partition words of weight twelve, with all parts at
least two. Their ordering fixes the coordinates of the singular relation. -/
def tricriticalWords : Fin 21 → List ℤ := ![[-12],[-10,-2],[-9,-3],[-8,-4],[-8,-2,-2],[-7,-5],[-7,-3,-2],[-6,-6],[-6,-4,-2],[-6,-3,-3],[-6,-2,-2,-2],[-5,-5,-2],[-5,-4,-3],[-5,-3,-2,-2],[-4,-4,-4],[-4,-4,-2,-2],[-4,-3,-3,-2],[-4,-2,-2,-2,-2],[-3,-3,-3,-3],[-3,-3,-2,-2,-2],[-2,-2,-2,-2,-2,-2]]

/-- Integral coordinates of the charge-seven-tenths singular relation.
They are certified below by the actual L1 and L2 equations. -/
def tricriticalCoefficients : Fin 21 → ℂ := ![40552600,-72017120,28090280,3678640,-31800000,33737880,-22292800,-36195760,-53429440,45116600,9395200,57477600,-24431680,-35433600,3052224,33602240,8015600,-10419200,-4547875,3632000,512000]

/-- The weight-twelve singular-word expression acting on a supplied vacuum. -/
noncomputable def tricriticalState (L : ℤ → End ℂ E) (v : E) : E :=
  ∑ i, tricriticalCoefficients i • virWord L (tricriticalWords i) v

/-- The adjoint row reverses every creation word and changes each mode sign.
Its application to the state computes the actual vacuum norm polynomial. -/
noncomputable def tricriticalAdjoint (L : ℤ → End ℂ E) : End ℂ E :=
  ∑ i, tricriticalCoefficients i • virWord L ((tricriticalWords i).reverse.map Neg.neg)

variable (v : E) (hv : ∀ n : ℤ, -1 ≤ n → A.L n v = 0)
include hv
/-- Commute mode 1 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_000 :
    A.L (1) (A.L (-12) (v)) = (13 : ℂ) • (A.L (-11) (v)) := by
  rw [vir_push A (1) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_001 :
    A.L (2) (A.L (-12) (v)) = (14 : ℂ) • (A.L (-10) (v)) := by
  rw [vir_push A (2) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_002 :
    A.L (1) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_003 :
    A.L (1) (A.L (-10) (A.L (-2) (v))) = (11 : ℂ) • (A.L (-9) (A.L (-2) (v))) := by
  rw [vir_push A (1) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_004 :
    A.L (2) (A.L (-2) (v)) = (1/2 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_005 :
    A.L (2) (A.L (-10) (A.L (-2) (v))) = (12 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-10) (v))) := by
  rw [vir_push A (2) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_006 :
    A.L (1) (A.L (-3) (v)) = (4 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_007 :
    A.L (1) (A.L (-9) (A.L (-3) (v))) = (4 : ℂ) • (A.L (-9) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-8) (A.L (-3) (v))) := by
  rw [vir_push A (1) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_006 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_008 :
    A.L (2) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_009 :
    A.L (2) (A.L (-9) (A.L (-3) (v))) = (11 : ℂ) • (A.L (-7) (A.L (-3) (v))) := by
  rw [vir_push A (2) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_008 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_010 :
    A.L (1) (A.L (-4) (v)) = (5 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_011 :
    A.L (1) (A.L (-8) (A.L (-4) (v))) = (5 : ℂ) • (A.L (-8) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-7) (A.L (-4) (v))) := by
  rw [vir_push A (1) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_010 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_012 :
    A.L (2) (A.L (-4) (v)) = (6 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_013 :
    A.L (2) (A.L (-8) (A.L (-4) (v))) = (6 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-6) (A.L (-4) (v))) := by
  rw [vir_push A (2) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_012 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_014 :
    A.L (-1) (A.L (-2) (v)) = A.L (-3) (v) := by
  rw [vir_push A (-1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_015 :
    A.L (1) (A.L (-2) (A.L (-2) (v))) = (3 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv, reduce12_014 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_016 :
    A.L (1) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (3 : ℂ) • (A.L (-8) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-7) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_017 :
    A.L (0) (A.L (-2) (v)) = (2 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (0) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_018 :
    A.L (2) (A.L (-2) (A.L (-2) (v))) = (8 : ℂ) • (A.L (-2) (v)) + (A.central ^ 1) (A.L (-2) (v)) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv, reduce12_017 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_019 :
    A.L (2) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (8 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-6) (A.L (-2) (A.L (-2) (v)))) + (A.central ^ 1) (A.L (-8) (A.L (-2) (v))) := by
  rw [vir_push A (2) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_020 :
    A.L (1) (A.L (-5) (v)) = (6 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (1) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_021 :
    A.L (1) (A.L (-7) (A.L (-5) (v))) = (6 : ℂ) • (A.L (-7) (A.L (-4) (v))) + (8 : ℂ) • (A.L (-6) (A.L (-5) (v))) := by
  rw [vir_push A (1) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_020 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_022 :
    A.L (2) (A.L (-5) (v)) = (7 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_023 :
    A.L (2) (A.L (-7) (A.L (-5) (v))) = (7 : ℂ) • (A.L (-7) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-5) (A.L (-5) (v))) := by
  rw [vir_push A (2) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_022 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_024 :
    A.L (1) (A.L (-3) (A.L (-2) (v))) = (4 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_025 :
    A.L (1) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (4 : ℂ) • (A.L (-7) (A.L (-2) (A.L (-2) (v)))) + (8 : ℂ) • (A.L (-6) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_024 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_026 :
    A.L (2) (A.L (-3) (A.L (-2) (v))) = (5 : ℂ) • (A.L (-3) (v)) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv, reduce12_014 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_027 :
    A.L (2) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (5 : ℂ) • (A.L (-7) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-7) (A.L (-3) (v)))) := by
  rw [vir_push A (2) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_026 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_028 :
    A.L (1) (A.L (-6) (v)) = (7 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (1) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -5 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_029 :
    A.L (-5) (A.L (-6) (v)) = A.L (-11) (v) + A.L (-6) (A.L (-5) (v)) := by
  rw [vir_push A (-5) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_030 :
    A.L (1) (A.L (-6) (A.L (-6) (v))) = (7 : ℂ) • (A.L (-11) (v)) + (14 : ℂ) • (A.L (-6) (A.L (-5) (v))) := by
  rw [vir_push A (1) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_028 A v hv, reduce12_029 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_031 :
    A.L (2) (A.L (-6) (v)) = (8 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -4 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_032 :
    A.L (-4) (A.L (-6) (v)) = (2 : ℂ) • (A.L (-10) (v)) + A.L (-6) (A.L (-4) (v)) := by
  rw [vir_push A (-4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_033 :
    A.L (2) (A.L (-6) (A.L (-6) (v))) = (16 : ℂ) • (A.L (-10) (v)) + (16 : ℂ) • (A.L (-6) (A.L (-4) (v))) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_031 A v hv, reduce12_032 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_034 :
    A.L (1) (A.L (-4) (A.L (-2) (v))) = (5 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_035 :
    A.L (1) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (5 : ℂ) • (A.L (-6) (A.L (-3) (A.L (-2) (v)))) + (7 : ℂ) • (A.L (-5) (A.L (-4) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_034 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_036 :
    A.L (2) (A.L (-4) (A.L (-2) (v))) = (6 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_037 :
    A.L (2) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (6 : ℂ) • (A.L (-6) (A.L (-2) (A.L (-2) (v)))) + (8 : ℂ) • (A.L (-4) (A.L (-4) (A.L (-2) (v)))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-6) (A.L (-4) (v)))) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_036 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_038 :
    A.L (-2) (A.L (-3) (v)) = A.L (-5) (v) + A.L (-3) (A.L (-2) (v)) := by
  rw [vir_push A (-2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_039 :
    A.L (1) (A.L (-3) (A.L (-3) (v))) = (4 : ℂ) • (A.L (-5) (v)) + (8 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_006 A v hv, reduce12_038 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_040 :
    A.L (1) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (4 : ℂ) • (A.L (-6) (A.L (-5) (v))) + (8 : ℂ) • (A.L (-6) (A.L (-3) (A.L (-2) (v)))) + (7 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (1) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_039 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_041 :
    A.L (-1) (A.L (-3) (v)) = (2 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_042 :
    A.L (2) (A.L (-3) (A.L (-3) (v))) = (10 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_008 A v hv, reduce12_041 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_043 :
    A.L (2) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (10 : ℂ) • (A.L (-6) (A.L (-4) (v))) + (8 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_042 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_044 :
    A.L (-1) (A.L (-2) (A.L (-2) (v))) = A.L (-5) (v) + (2 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (-1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_014 A v hv, reduce12_038 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_045 :
    A.L (1) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (6 : ℂ) • (A.L (-5) (v)) + (9 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv, reduce12_038 A v hv, reduce12_044 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_046 :
    A.L (1) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (6 : ℂ) • (A.L (-6) (A.L (-5) (v))) + (9 : ℂ) • (A.L (-6) (A.L (-3) (A.L (-2) (v)))) + (7 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (1) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_045 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_047 :
    A.L (0) (A.L (-2) (A.L (-2) (v))) = (4 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (0) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_048 :
    A.L (2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (24 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (3/2 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv, reduce12_047 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_049 :
    A.L (2) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (24 : ℂ) • (A.L (-6) (A.L (-2) (A.L (-2) (v)))) + (8 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (3/2 : ℂ) • ((A.central ^ 1) (A.L (-6) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_048 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_050 :
    A.L (1) (A.L (-5) (A.L (-2) (v))) = (6 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (1) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -4 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_051 :
    A.L (-4) (A.L (-5) (A.L (-2) (v))) = A.L (-9) (A.L (-2) (v)) + A.L (-5) (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (-4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_052 :
    A.L (1) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (6 : ℂ) • (A.L (-9) (A.L (-2) (v))) + (12 : ℂ) • (A.L (-5) (A.L (-4) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_050 A v hv, reduce12_051 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_053 :
    A.L (2) (A.L (-5) (A.L (-2) (v))) = (7 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-5) (v))) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_054 :
    A.L (-3) (A.L (-5) (A.L (-2) (v))) = (2 : ℂ) • (A.L (-8) (A.L (-2) (v))) + A.L (-5) (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (-3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_055 :
    A.L (2) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (14 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (14 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-5) (v)))) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_053 A v hv, reduce12_054 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_056 :
    A.L (1) (A.L (-4) (A.L (-3) (v))) = (4 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (5 : ℂ) • (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_006 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_057 :
    A.L (1) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (4 : ℂ) • (A.L (-5) (A.L (-4) (A.L (-2) (v)))) + (5 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-3) (v)))) + (6 : ℂ) • (A.L (-4) (A.L (-4) (A.L (-3) (v)))) := by
  rw [vir_push A (1) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_056 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_058 :
    A.L (2) (A.L (-4) (A.L (-3) (v))) = (6 : ℂ) • (A.L (-5) (v)) + (6 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_008 A v hv, reduce12_038 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_059 :
    A.L (-3) (A.L (-4) (A.L (-3) (v))) = A.L (-7) (A.L (-3) (v)) + A.L (-4) (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (-3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_060 :
    A.L (2) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (7 : ℂ) • (A.L (-7) (A.L (-3) (v))) + (6 : ℂ) • (A.L (-5) (A.L (-5) (v))) + (6 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + (7 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_058 A v hv, reduce12_059 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_061 :
    A.L (1) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (3 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (4 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_062 :
    A.L (1) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (3 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-3) (v)))) + (4 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (6 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (1) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_061 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_063 :
    A.L (2) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (5 : ℂ) • (A.L (-5) (v)) + (18 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (A.central ^ 1) (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv, reduce12_044 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_064 :
    A.L (2) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (5 : ℂ) • (A.L (-5) (A.L (-5) (v))) + (18 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + (7 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) + (A.central ^ 1) (A.L (-5) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_063 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_065 :
    A.L (-3) (A.L (-4) (v)) = A.L (-7) (v) + A.L (-4) (A.L (-3) (v)) := by
  rw [vir_push A (-3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_066 :
    A.L (1) (A.L (-4) (A.L (-4) (v))) = (5 : ℂ) • (A.L (-7) (v)) + (10 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_010 A v hv, reduce12_065 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -4 through the ordered creation word [-7].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_067 :
    A.L (-4) (A.L (-7) (v)) = (3 : ℂ) • (A.L (-11) (v)) + A.L (-7) (A.L (-4) (v)) := by
  rw [vir_push A (-4) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_068 :
    A.L (-3) (A.L (-4) (A.L (-4) (v))) = (3 : ℂ) • (A.L (-11) (v)) + (2 : ℂ) • (A.L (-7) (A.L (-4) (v))) + A.L (-4) (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (-3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_065 A v hv, reduce12_067 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_069 :
    A.L (1) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (30 : ℂ) • (A.L (-11) (v)) + (15 : ℂ) • (A.L (-7) (A.L (-4) (v))) + (15 : ℂ) • (A.L (-4) (A.L (-4) (A.L (-3) (v)))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_070 :
    A.L (-2) (A.L (-4) (v)) = (2 : ℂ) • (A.L (-6) (v)) + A.L (-4) (A.L (-2) (v)) := by
  rw [vir_push A (-2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_071 :
    A.L (2) (A.L (-4) (A.L (-4) (v))) = (12 : ℂ) • (A.L (-6) (v)) + (12 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_012 A v hv, reduce12_070 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_072 :
    A.L (-2) (A.L (-4) (A.L (-4) (v))) = (4 : ℂ) • (A.L (-10) (v)) + (4 : ℂ) • (A.L (-6) (A.L (-4) (v))) + A.L (-4) (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (-2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_032 A v hv, reduce12_070 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_073 :
    A.L (2) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (48 : ℂ) • (A.L (-10) (v)) + (36 : ℂ) • (A.L (-6) (A.L (-4) (v))) + (18 : ℂ) • (A.L (-4) (A.L (-4) (A.L (-2) (v)))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_032 A v hv, reduce12_071 A v hv, reduce12_072 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_074 :
    A.L (1) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (3 : ℂ) • (A.L (-4) (A.L (-3) (v))) + (5 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_075 :
    A.L (-3) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = A.L (-7) (A.L (-2) (A.L (-2) (v))) + A.L (-4) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (-3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_076 :
    A.L (1) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (5 : ℂ) • (A.L (-7) (A.L (-2) (A.L (-2) (v)))) + (3 : ℂ) • (A.L (-4) (A.L (-4) (A.L (-3) (v)))) + (10 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_074 A v hv, reduce12_075 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_077 :
    A.L (2) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (8 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (6 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (A.central ^ 1) (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_078 :
    A.L (-2) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (2 : ℂ) • (A.L (-6) (A.L (-2) (A.L (-2) (v)))) + A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (-2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_079 :
    A.L (2) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (12 : ℂ) • (A.L (-6) (A.L (-2) (A.L (-2) (v)))) + (8 : ℂ) • (A.L (-4) (A.L (-4) (A.L (-2) (v)))) + (12 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (A.central ^ 1) (A.L (-4) (A.L (-4) (A.L (-2) (v)))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_077 A v hv, reduce12_078 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_080 :
    A.L (-2) (A.L (-3) (A.L (-2) (v))) = A.L (-5) (A.L (-2) (v)) + A.L (-3) (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (-2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_081 :
    A.L (1) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (4 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (8 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_024 A v hv, reduce12_080 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_082 :
    A.L (1) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (4 : ℂ) • (A.L (-9) (A.L (-2) (v))) + (4 : ℂ) • (A.L (-5) (A.L (-4) (A.L (-2) (v)))) + (8 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) + (5 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_051 A v hv, reduce12_081 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_083 :
    A.L (-1) (A.L (-3) (A.L (-2) (v))) = (2 : ℂ) • (A.L (-4) (A.L (-2) (v))) + A.L (-3) (A.L (-3) (v)) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_014 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_084 :
    A.L (2) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (10 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_026 A v hv, reduce12_083 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_085 :
    A.L (-2) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (2 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (2 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (-2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_054 A v hv, reduce12_080 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_086 :
    A.L (2) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (12 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (12 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + (10 : ℂ) • (A.L (-4) (A.L (-4) (A.L (-2) (v)))) + (10 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-3) (v)))) + (6 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-3) (A.L (-3) (v))))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_084 A v hv, reduce12_085 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_087 :
    A.L (-2) (A.L (-5) (v)) = (3 : ℂ) • (A.L (-7) (v)) + A.L (-5) (A.L (-2) (v)) := by
  rw [vir_push A (-2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_088 :
    A.L (-1) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (3 : ℂ) • (A.L (-7) (v)) + (3 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (3 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (-1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_044 A v hv, reduce12_080 A v hv, reduce12_087 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_089 :
    A.L (1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (27 : ℂ) • (A.L (-7) (v)) + (24 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (18 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_045 A v hv, reduce12_080 A v hv, reduce12_087 A v hv, reduce12_088 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_090 :
    A.L (1) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (81 : ℂ) • (A.L (-11) (v)) + (24 : ℂ) • (A.L (-9) (A.L (-2) (v))) + (27 : ℂ) • (A.L (-7) (A.L (-4) (v))) + (24 : ℂ) • (A.L (-5) (A.L (-4) (A.L (-2) (v)))) + (18 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) + (5 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_051 A v hv, reduce12_067 A v hv, reduce12_089 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_091 :
    A.L (0) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (6 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (0) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_047 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_092 :
    A.L (2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (48 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_048 A v hv, reduce12_091 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_093 :
    A.L (2) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (48 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (6 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_092 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_094 :
    A.L (-3) (A.L (-5) (v)) = (2 : ℂ) • (A.L (-8) (v)) + A.L (-5) (A.L (-3) (v)) := by
  rw [vir_push A (-3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_095 :
    A.L (-2) (A.L (-3) (A.L (-3) (v))) = (2 : ℂ) • (A.L (-8) (v)) + (2 : ℂ) • (A.L (-5) (A.L (-3) (v))) + A.L (-3) (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (-2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_038 A v hv, reduce12_094 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_096 :
    A.L (1) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (16 : ℂ) • (A.L (-8) (v)) + (12 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (12 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_039 A v hv, reduce12_094 A v hv, reduce12_095 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-5, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_097 :
    A.L (-3) (A.L (-5) (A.L (-3) (v))) = (2 : ℂ) • (A.L (-8) (A.L (-3) (v))) + A.L (-5) (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (-3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-8].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_098 :
    A.L (-3) (A.L (-8) (v)) = (5 : ℂ) • (A.L (-11) (v)) + A.L (-8) (A.L (-3) (v)) := by
  rw [vir_push A (-3) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_099 :
    A.L (-2) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (10 : ℂ) • (A.L (-11) (v)) + (6 : ℂ) • (A.L (-8) (A.L (-3) (v))) + (3 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-3) (v)))) + A.L (-3) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (-2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_095 A v hv, reduce12_097 A v hv, reduce12_098 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_100 :
    A.L (1) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (120 : ℂ) • (A.L (-11) (v)) + (64 : ℂ) • (A.L (-8) (A.L (-3) (v))) + (24 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-3) (v)))) + (16 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_101 :
    A.L (-1) (A.L (-3) (A.L (-3) (v))) = (2 : ℂ) • (A.L (-7) (v)) + (4 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_041 A v hv, reduce12_065 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_102 :
    A.L (2) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (20 : ℂ) • (A.L (-7) (v)) + (30 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_042 A v hv, reduce12_065 A v hv, reduce12_101 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-7].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_103 :
    A.L (-3) (A.L (-7) (v)) = (4 : ℂ) • (A.L (-10) (v)) + A.L (-7) (A.L (-3) (v)) := by
  rw [vir_push A (-3) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_104 :
    A.L (-1) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (8 : ℂ) • (A.L (-10) (v)) + (6 : ℂ) • (A.L (-7) (A.L (-3) (v))) + (6 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_059 A v hv, reduce12_101 A v hv, reduce12_103 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_105 :
    A.L (2) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (120 : ℂ) • (A.L (-10) (v)) + (80 : ℂ) • (A.L (-7) (A.L (-3) (v))) + (60 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_059 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_106 :
    A.L (1) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (12 : ℂ) • (A.L (-8) (v)) + (6 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) + (4 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_045 A v hv, reduce12_094 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_107 :
    A.L (-2) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = A.L (-5) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (-2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_108 :
    A.L (1) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (60 : ℂ) • (A.L (-11) (v)) + (24 : ℂ) • (A.L (-8) (A.L (-3) (v))) + (6 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-3) (v)))) + (4 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (9 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) + (8 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_106 A v hv, reduce12_107 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_109 :
    A.L (2) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (15 : ℂ) • (A.L (-7) (v)) + (15 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (39 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) + (3/2 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_048 A v hv, reduce12_088 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_110 :
    A.L (-1) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (12 : ℂ) • (A.L (-10) (v)) + (6 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (3 : ℂ) • (A.L (-7) (A.L (-3) (v))) + (3 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + (2 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (3 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_054 A v hv, reduce12_088 A v hv, reduce12_103 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_111 :
    A.L (2) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (120 : ℂ) • (A.L (-10) (v)) + (60 : ℂ) • (A.L (-8) (A.L (-2) (v))) + (30 : ℂ) • (A.L (-7) (A.L (-3) (v))) + (30 : ℂ) • (A.L (-5) (A.L (-3) (A.L (-2) (v)))) + (10 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (54 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) + (3/2 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_054 A v hv, reduce12_103 A v hv, reduce12_109 A v hv, reduce12_110 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_112 :
    A.L (-2) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = A.L (-5) (A.L (-2) (A.L (-2) (v))) + A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (-2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_113 :
    A.L (-2) (A.L (-5) (A.L (-2) (v))) = (3 : ℂ) • (A.L (-7) (A.L (-2) (v))) + A.L (-5) (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (-2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-7].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_114 :
    A.L (-2) (A.L (-7) (v)) = (5 : ℂ) • (A.L (-9) (v)) + A.L (-7) (A.L (-2) (v)) := by
  rw [vir_push A (-2) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_115 :
    A.L (-1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (15 : ℂ) • (A.L (-9) (v)) + (12 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (6 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) + (4 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (-1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_088 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_116 :
    A.L (1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (180 : ℂ) • (A.L (-9) (v)) + (135 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (60 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) + (30 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_089 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-5, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_117 :
    A.L (-2) (A.L (-5) (A.L (-2) (A.L (-2) (v)))) = (3 : ℂ) • (A.L (-7) (A.L (-2) (A.L (-2) (v)))) + A.L (-5) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (-2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-7, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_118 :
    A.L (-2) (A.L (-7) (A.L (-2) (v))) = (5 : ℂ) • (A.L (-9) (A.L (-2) (v))) + A.L (-7) (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (-2) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-9].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_119 :
    A.L (-2) (A.L (-9) (v)) = (7 : ℂ) • (A.L (-11) (v)) + A.L (-9) (A.L (-2) (v)) := by
  rw [vir_push A (-2) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_120 :
    A.L (-1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (105 : ℂ) • (A.L (-11) (v)) + (75 : ℂ) • (A.L (-9) (A.L (-2) (v))) + (30 : ℂ) • (A.L (-7) (A.L (-2) (A.L (-2) (v)))) + (10 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (5 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (-1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_107 A v hv, reduce12_115 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_121 :
    A.L (1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (1575 : ℂ) • (A.L (-11) (v)) + (1080 : ℂ) • (A.L (-9) (A.L (-2) (v))) + (405 : ℂ) • (A.L (-7) (A.L (-2) (A.L (-2) (v)))) + (120 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (45 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_107 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_122 :
    A.L (0) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (8 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (0) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_091 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_123 :
    A.L (2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (80 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (5/2 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_092 A v hv, reduce12_122 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_124 :
    A.L (0) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (10 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (0) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_122 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_125 :
    A.L (2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (120 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) + (3 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_123 A v hv, reduce12_124 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_126 :
    A.L (12) (A.L (-12) (v)) = (143 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_127 :
    A.L (12) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (12) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_128 :
    A.L (12) (A.L (-10) (A.L (-2) (v))) = (11 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv, reduce12_127 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_129 :
    A.L (12) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_130 :
    A.L (3) (A.L (-3) (v)) = (2 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_131 :
    A.L (12) (A.L (-9) (A.L (-3) (v))) = (42 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_129 A v hv, reduce12_130 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_132 :
    A.L (12) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_133 :
    A.L (4) (A.L (-4) (v)) = (5 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_134 :
    A.L (12) (A.L (-8) (A.L (-4) (v))) = (100 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_132 A v hv, reduce12_133 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_135 :
    A.L (10) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (10) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_136 :
    A.L (12) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (12) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_127 A v hv, reduce12_135 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_137 :
    A.L (4) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_138 :
    A.L (4) (A.L (-2) (A.L (-2) (v))) = (3 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv, reduce12_137 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_139 :
    A.L (12) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (60 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_136 A v hv, reduce12_138 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_140 :
    A.L (12) (A.L (-5) (v)) = 0 := by
  rw [vir_push A (12) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_141 :
    A.L (5) (A.L (-5) (v)) = (10 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (5) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_142 :
    A.L (12) (A.L (-7) (A.L (-5) (v))) = (190 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_140 A v hv, reduce12_141 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_143 :
    A.L (9) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (9) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_144 :
    A.L (12) (A.L (-3) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_127 A v hv, reduce12_143 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_145 :
    A.L (5) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (5) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_146 :
    A.L (5) (A.L (-3) (A.L (-2) (v))) = (4 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv, reduce12_145 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_147 :
    A.L (12) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (76 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_144 A v hv, reduce12_146 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_148 :
    A.L (12) (A.L (-6) (v)) = 0 := by
  rw [vir_push A (12) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_149 :
    A.L (6) (A.L (-6) (v)) = (35/2 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_150 :
    A.L (12) (A.L (-6) (A.L (-6) (v))) = (315 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_148 A v hv, reduce12_149 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_151 :
    A.L (8) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (8) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_152 :
    A.L (12) (A.L (-4) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_127 A v hv, reduce12_151 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_153 :
    A.L (6) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_154 :
    A.L (6) (A.L (-4) (A.L (-2) (v))) = (5 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv, reduce12_153 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_155 :
    A.L (12) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (90 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_152 A v hv, reduce12_154 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_156 :
    A.L (9) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_157 :
    A.L (12) (A.L (-3) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_129 A v hv, reduce12_156 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_158 :
    A.L (6) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_159 :
    A.L (6) (A.L (-3) (A.L (-3) (v))) = (18 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_130 A v hv, reduce12_158 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_160 :
    A.L (12) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (324 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_157 A v hv, reduce12_159 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_161 :
    A.L (10) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (10) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_135 A v hv, reduce12_151 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_162 :
    A.L (12) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (12) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_136 A v hv, reduce12_161 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_163 :
    A.L (6) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_137 A v hv, reduce12_153 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_164 :
    A.L (6) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (24 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_138 A v hv, reduce12_163 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_165 :
    A.L (12) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (432 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_162 A v hv, reduce12_164 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_166 :
    A.L (7) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (7) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_167 :
    A.L (12) (A.L (-5) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (12) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_127 A v hv, reduce12_166 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_168 :
    A.L (7) (A.L (-5) (A.L (-2) (v))) = (6 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (7) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv, reduce12_166 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_169 :
    A.L (12) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (102 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_167 A v hv, reduce12_168 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_170 :
    A.L (8) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_171 :
    A.L (12) (A.L (-4) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_129 A v hv, reduce12_170 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_172 :
    A.L (7) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_173 :
    A.L (7) (A.L (-4) (A.L (-3) (v))) = (22 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_130 A v hv, reduce12_172 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_174 :
    A.L (12) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (374 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_171 A v hv, reduce12_173 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_175 :
    A.L (9) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (9) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_143 A v hv, reduce12_166 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_176 :
    A.L (12) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_136 A v hv, reduce12_175 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_177 :
    A.L (7) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (7) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_145 A v hv, reduce12_166 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_178 :
    A.L (7) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (30 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_138 A v hv, reduce12_177 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_179 :
    A.L (12) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (510 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_176 A v hv, reduce12_178 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_180 :
    A.L (8) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_181 :
    A.L (12) (A.L (-4) (A.L (-4) (v))) = 0 := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_132 A v hv, reduce12_180 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_182 :
    A.L (8) (A.L (-4) (A.L (-4) (v))) = (60 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_133 A v hv, reduce12_180 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_183 :
    A.L (12) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (960 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_181 A v hv, reduce12_182 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_184 :
    A.L (8) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (8) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_151 A v hv, reduce12_153 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_185 :
    A.L (12) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_136 A v hv, reduce12_184 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_186 :
    A.L (8) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (36 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_138 A v hv, reduce12_184 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_187 :
    A.L (12) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (576 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_185 A v hv, reduce12_186 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_188 :
    A.L (9) (A.L (-3) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_143 A v hv, reduce12_153 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_189 :
    A.L (12) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_144 A v hv, reduce12_188 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_190 :
    A.L (8) (A.L (-3) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_145 A v hv, reduce12_151 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_191 :
    A.L (8) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (44 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_146 A v hv, reduce12_190 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_192 :
    A.L (12) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (704 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_189 A v hv, reduce12_191 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_193 :
    A.L (10) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (10) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_161 A v hv, reduce12_184 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_194 :
    A.L (12) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = 0 := by
  rw [vir_push A (12) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_162 A v hv, reduce12_193 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_195 :
    A.L (8) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (8) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_163 A v hv, reduce12_184 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_196 :
    A.L (8) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (240 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (8) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_164 A v hv, reduce12_195 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_197 :
    A.L (12) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (3840 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_194 A v hv, reduce12_196 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_198 :
    A.L (9) (A.L (-3) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_156 A v hv, reduce12_158 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_199 :
    A.L (12) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = 0 := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_157 A v hv, reduce12_198 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_200 :
    A.L (9) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (216 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_159 A v hv, reduce12_198 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_201 :
    A.L (12) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (3240 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_199 A v hv, reduce12_200 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_202 :
    A.L (9) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (9) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_175 A v hv, reduce12_177 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_203 :
    A.L (12) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = 0 := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_162 A v hv, reduce12_202 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_204 :
    A.L (9) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (288 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_164 A v hv, reduce12_202 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_205 :
    A.L (12) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (4320 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_203 A v hv, reduce12_204 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_206 :
    A.L (10) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = 0 := by
  rw [vir_push A (10) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_193 A v hv, reduce12_195 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_207 :
    A.L (12) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = 0 := by
  rw [vir_push A (12) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_194 A v hv, reduce12_206 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_208 :
    A.L (10) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (2880 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (10) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_196 A v hv, reduce12_206 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 12 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_209 :
    A.L (12) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (40320 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (12) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_207 A v hv, reduce12_208 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_210 :
    A.L (10) (A.L (-12) (v)) = (22 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_211 :
    A.L (10) (A.L (-10) (A.L (-2) (v))) = (40 : ℂ) • (A.L (-2) (v)) + (165/2 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv, reduce12_135 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_212 :
    A.L (10) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_213 :
    A.L (10) (A.L (-9) (A.L (-3) (v))) = (76 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_006 A v hv, reduce12_212 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_214 :
    A.L (10) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_215 :
    A.L (10) (A.L (-8) (A.L (-4) (v))) = (108 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_012 A v hv, reduce12_214 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_216 :
    A.L (10) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (144 : ℂ) • (A.L (-2) (v)) + (18 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv, reduce12_161 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_217 :
    A.L (10) (A.L (-5) (v)) = 0 := by
  rw [vir_push A (10) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_218 :
    A.L (3) (A.L (-5) (v)) = (8 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_219 :
    A.L (10) (A.L (-7) (A.L (-5) (v))) = (136 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_217 A v hv, reduce12_218 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_220 :
    A.L (10) (A.L (-3) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_135 A v hv, reduce12_166 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_221 :
    A.L (3) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_222 :
    A.L (3) (A.L (-3) (A.L (-2) (v))) = (12 : ℂ) • (A.L (-2) (v)) + (2 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_223 :
    A.L (10) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (204 : ℂ) • (A.L (-2) (v)) + (34 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_220 A v hv, reduce12_222 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_224 :
    A.L (10) (A.L (-6) (v)) = 0 := by
  rw [vir_push A (10) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_225 :
    A.L (4) (A.L (-6) (v)) = (10 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_226 :
    A.L (10) (A.L (-6) (A.L (-6) (v))) = (160 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_224 A v hv, reduce12_225 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_227 :
    A.L (10) (A.L (-4) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_135 A v hv, reduce12_153 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_228 :
    A.L (4) (A.L (-4) (A.L (-2) (v))) = (16 : ℂ) • (A.L (-2) (v)) + (5 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv, reduce12_137 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_229 :
    A.L (10) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (256 : ℂ) • (A.L (-2) (v)) + (80 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_227 A v hv, reduce12_228 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_230 :
    A.L (10) (A.L (-3) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_172 A v hv, reduce12_212 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_231 :
    A.L (4) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_232 :
    A.L (4) (A.L (-3) (A.L (-3) (v))) = (28 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_006 A v hv, reduce12_231 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_233 :
    A.L (10) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (448 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_230 A v hv, reduce12_232 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_234 :
    A.L (4) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (48 : ℂ) • (A.L (-2) (v)) + (9 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv, reduce12_138 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_235 :
    A.L (10) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (768 : ℂ) • (A.L (-2) (v)) + (144 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_193 A v hv, reduce12_234 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_236 :
    A.L (10) (A.L (-5) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (10) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_135 A v hv, reduce12_145 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_237 :
    A.L (5) (A.L (-5) (A.L (-2) (v))) = (20 : ℂ) • (A.L (-2) (v)) + (10 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (5) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv, reduce12_145 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_238 :
    A.L (10) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (300 : ℂ) • (A.L (-2) (v)) + (150 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_236 A v hv, reduce12_237 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_239 :
    A.L (10) (A.L (-4) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_158 A v hv, reduce12_212 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_240 :
    A.L (5) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_241 :
    A.L (5) (A.L (-4) (A.L (-3) (v))) = (36 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_006 A v hv, reduce12_240 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_242 :
    A.L (10) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (540 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_239 A v hv, reduce12_241 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_243 :
    A.L (10) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_161 A v hv, reduce12_177 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_244 :
    A.L (5) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (5) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_145 A v hv, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_245 :
    A.L (5) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (64 : ℂ) • (A.L (-2) (v)) + (8 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv, reduce12_244 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_246 :
    A.L (10) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (960 : ℂ) • (A.L (-2) (v)) + (120 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_243 A v hv, reduce12_245 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_247 :
    A.L (6) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_248 :
    A.L (10) (A.L (-4) (A.L (-4) (v))) = 0 := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_214 A v hv, reduce12_247 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_249 :
    A.L (6) (A.L (-4) (A.L (-4) (v))) = (60 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_012 A v hv, reduce12_247 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_250 :
    A.L (10) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (840 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_248 A v hv, reduce12_249 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_251 :
    A.L (10) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_161 A v hv, reduce12_163 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_252 :
    A.L (6) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (80 : ℂ) • (A.L (-2) (v)) + (10 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv, reduce12_163 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_253 :
    A.L (10) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (1120 : ℂ) • (A.L (-2) (v)) + (140 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_251 A v hv, reduce12_252 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_254 :
    A.L (7) (A.L (-3) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_137 A v hv, reduce12_166 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_255 :
    A.L (10) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_220 A v hv, reduce12_254 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_256 :
    A.L (6) (A.L (-3) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_153 A v hv, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_257 :
    A.L (6) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (108 : ℂ) • (A.L (-2) (v)) + (18 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_222 A v hv, reduce12_256 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_258 :
    A.L (10) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (1512 : ℂ) • (A.L (-2) (v)) + (252 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_255 A v hv, reduce12_257 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_259 :
    A.L (6) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (384 : ℂ) • (A.L (-2) (v)) + (96 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_164 A v hv, reduce12_234 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_260 :
    A.L (10) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (5376 : ℂ) • (A.L (-2) (v)) + (1344 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_206 A v hv, reduce12_259 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_261 :
    A.L (7) (A.L (-3) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_172 A v hv, reduce12_231 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_262 :
    A.L (10) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = 0 := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_230 A v hv, reduce12_261 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_263 :
    A.L (7) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (280 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_232 A v hv, reduce12_261 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_264 :
    A.L (10) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (3640 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_262 A v hv, reduce12_263 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_265 :
    A.L (7) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (7) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_177 A v hv, reduce12_244 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_266 :
    A.L (10) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = 0 := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_193 A v hv, reduce12_265 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_267 :
    A.L (7) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (480 : ℂ) • (A.L (-2) (v)) + (90 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_234 A v hv, reduce12_265 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_268 :
    A.L (10) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (6240 : ℂ) • (A.L (-2) (v)) + (1170 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_266 A v hv, reduce12_267 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_269 :
    A.L (8) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (3840 : ℂ) • (A.L (-2) (v)) + (1200 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (8) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_196 A v hv, reduce12_259 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 10 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_270 :
    A.L (10) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (46080 : ℂ) • (A.L (-2) (v)) + (17280 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (10) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_208 A v hv, reduce12_269 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_271 :
    A.L (9) (A.L (-12) (v)) = (21 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_272 :
    A.L (9) (A.L (-10) (A.L (-2) (v))) = (19 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_014 A v hv, reduce12_143 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_273 :
    A.L (0) (A.L (-3) (v)) = (3 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_274 :
    A.L (9) (A.L (-9) (A.L (-3) (v))) = (54 : ℂ) • (A.L (-3) (v)) + (60 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_156 A v hv, reduce12_273 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_275 :
    A.L (9) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_276 :
    A.L (9) (A.L (-8) (A.L (-4) (v))) = (85 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_010 A v hv, reduce12_275 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_277 :
    A.L (9) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (51 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv, reduce12_175 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_278 :
    A.L (9) (A.L (-5) (v)) = 0 := by
  rw [vir_push A (9) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_279 :
    A.L (9) (A.L (-7) (A.L (-5) (v))) = (112 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_022 A v hv, reduce12_278 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_280 :
    A.L (9) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (80 : ℂ) • (A.L (-3) (v)) + (8 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_026 A v hv, reduce12_188 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_281 :
    A.L (9) (A.L (-6) (v)) = 0 := by
  rw [vir_push A (9) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_282 :
    A.L (3) (A.L (-6) (v)) = (9 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_283 :
    A.L (9) (A.L (-6) (A.L (-6) (v))) = (135 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_281 A v hv, reduce12_282 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_284 :
    A.L (9) (A.L (-4) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_143 A v hv, reduce12_145 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_285 :
    A.L (3) (A.L (-4) (A.L (-2) (v))) = (7 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_014 A v hv, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_286 :
    A.L (9) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (105 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_284 A v hv, reduce12_285 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_287 :
    A.L (3) (A.L (-3) (A.L (-3) (v))) = (18 : ℂ) • (A.L (-3) (v)) + (4 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_130 A v hv, reduce12_273 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_288 :
    A.L (9) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (270 : ℂ) • (A.L (-3) (v)) + (60 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_198 A v hv, reduce12_287 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_289 :
    A.L (3) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_290 :
    A.L (3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (15 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_291 :
    A.L (9) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (225 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_202 A v hv, reduce12_290 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_292 :
    A.L (9) (A.L (-5) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (9) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_137 A v hv, reduce12_143 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_293 :
    A.L (4) (A.L (-5) (A.L (-2) (v))) = (9 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_014 A v hv, reduce12_137 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_294 :
    A.L (9) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (126 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_292 A v hv, reduce12_293 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_295 :
    A.L (9) (A.L (-4) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_156 A v hv, reduce12_240 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_296 :
    A.L (4) (A.L (-4) (A.L (-3) (v))) = (24 : ℂ) • (A.L (-3) (v)) + (5 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_231 A v hv, reduce12_273 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_297 :
    A.L (9) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (336 : ℂ) • (A.L (-3) (v)) + (70 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_295 A v hv, reduce12_296 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_298 :
    A.L (9) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_163 A v hv, reduce12_175 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_299 :
    A.L (4) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (21 : ℂ) • (A.L (-3) (v)) + (3 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv, reduce12_138 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_300 :
    A.L (9) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (294 : ℂ) • (A.L (-3) (v)) + (42 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_298 A v hv, reduce12_299 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_301 :
    A.L (5) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_302 :
    A.L (9) (A.L (-4) (A.L (-4) (v))) = 0 := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_275 A v hv, reduce12_301 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_303 :
    A.L (5) (A.L (-4) (A.L (-4) (v))) = (45 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_010 A v hv, reduce12_301 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_304 :
    A.L (9) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (585 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_302 A v hv, reduce12_303 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_305 :
    A.L (9) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_175 A v hv, reduce12_244 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_306 :
    A.L (5) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (27 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_015 A v hv, reduce12_244 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_307 :
    A.L (9) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (351 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_305 A v hv, reduce12_306 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_308 :
    A.L (9) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_188 A v hv, reduce12_256 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_309 :
    A.L (5) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (40 : ℂ) • (A.L (-3) (v)) + (8 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_026 A v hv, reduce12_146 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_310 :
    A.L (9) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (520 : ℂ) • (A.L (-3) (v)) + (104 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_308 A v hv, reduce12_309 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_311 :
    A.L (9) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = 0 := by
  rw [vir_push A (9) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_202 A v hv, reduce12_265 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_312 :
    A.L (5) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (5) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_244 A v hv, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_313 :
    A.L (5) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (105 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (5) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_290 A v hv, reduce12_312 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_314 :
    A.L (9) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (1365 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_311 A v hv, reduce12_313 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_315 :
    A.L (6) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (162 : ℂ) • (A.L (-3) (v)) + (54 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_159 A v hv, reduce12_287 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_316 :
    A.L (9) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (1944 : ℂ) • (A.L (-3) (v)) + (864 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_200 A v hv, reduce12_315 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_317 :
    A.L (6) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (135 : ℂ) • (A.L (-3) (v)) + (24 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_164 A v hv, reduce12_290 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_318 :
    A.L (9) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (1620 : ℂ) • (A.L (-3) (v)) + (576 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (9) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_204 A v hv, reduce12_317 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_319 :
    A.L (7) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = 0 := by
  rw [vir_push A (7) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_265 A v hv, reduce12_312 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_320 :
    A.L (9) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = 0 := by
  rw [vir_push A (9) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_311 A v hv, reduce12_319 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_321 :
    A.L (7) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (945 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (7) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_313 A v hv, reduce12_319 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 9 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_322 :
    A.L (9) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (10395 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (9) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_320 A v hv, reduce12_321 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_323 :
    A.L (8) (A.L (-12) (v)) = (20 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (8) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_324 :
    A.L (8) (A.L (-10) (A.L (-2) (v))) = (18 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (8) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_151 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_325 :
    A.L (8) (A.L (-9) (A.L (-3) (v))) = (34 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (8) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_041 A v hv, reduce12_170 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_326 :
    A.L (0) (A.L (-4) (v)) = (4 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (0) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_327 :
    A.L (8) (A.L (-8) (A.L (-4) (v))) = (64 : ℂ) • (A.L (-4) (v)) + (42 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (8) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_180 A v hv, reduce12_326 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_328 :
    A.L (8) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (64 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (42 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (8) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_047 A v hv, reduce12_184 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_329 :
    A.L (8) (A.L (-5) (v)) = 0 := by
  rw [vir_push A (8) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_330 :
    A.L (8) (A.L (-7) (A.L (-5) (v))) = (90 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (8) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_020 A v hv, reduce12_329 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_331 :
    A.L (8) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (60 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (8) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_024 A v hv, reduce12_190 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_332 :
    A.L (8) (A.L (-6) (v)) = 0 := by
  rw [vir_push A (8) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_333 :
    A.L (8) (A.L (-6) (A.L (-6) (v))) = (112 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (8) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_031 A v hv, reduce12_332 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_334 :
    A.L (8) (A.L (-4) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_137 A v hv, reduce12_151 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_335 :
    A.L (8) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (84 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (7 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (8) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_036 A v hv, reduce12_334 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_336 :
    A.L (8) (A.L (-3) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_170 A v hv, reduce12_240 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_337 :
    A.L (8) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (140 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (8) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_042 A v hv, reduce12_336 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_338 :
    A.L (8) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (336 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (21 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (8) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_048 A v hv, reduce12_195 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_339 :
    A.L (8) (A.L (-5) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (8) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_151 A v hv, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_340 :
    A.L (3) (A.L (-5) (A.L (-2) (v))) = (8 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_341 :
    A.L (8) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (104 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (8) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_339 A v hv, reduce12_340 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_342 :
    A.L (8) (A.L (-4) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_170 A v hv, reduce12_231 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_343 :
    A.L (3) (A.L (-4) (A.L (-3) (v))) = (14 : ℂ) • (A.L (-4) (v)) + (2 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_041 A v hv, reduce12_130 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_344 :
    A.L (8) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (182 : ℂ) • (A.L (-4) (v)) + (26 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (8) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_342 A v hv, reduce12_343 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_345 :
    A.L (8) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_184 A v hv, reduce12_244 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_346 :
    A.L (3) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (24 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_047 A v hv, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_347 :
    A.L (8) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (312 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (26 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (8) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_345 A v hv, reduce12_346 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_348 :
    A.L (4) (A.L (-4) (A.L (-4) (v))) = (32 : ℂ) • (A.L (-4) (v)) + (10 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_133 A v hv, reduce12_326 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_349 :
    A.L (8) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (384 : ℂ) • (A.L (-4) (v)) + (180 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_182 A v hv, reduce12_348 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_350 :
    A.L (4) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (32 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (3 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_047 A v hv, reduce12_138 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_351 :
    A.L (8) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (384 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (72 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) + (60 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_186 A v hv, reduce12_350 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_352 :
    A.L (4) (A.L (-3) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv, reduce12_137 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_353 :
    A.L (4) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (28 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_024 A v hv, reduce12_352 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_354 :
    A.L (8) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (336 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (44 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_191 A v hv, reduce12_353 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_355 :
    A.L (4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (192 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (18 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_048 A v hv, reduce12_234 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_356 :
    A.L (8) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (2304 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (240 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) + (216 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (8) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_196 A v hv, reduce12_355 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_357 :
    A.L (5) (A.L (-3) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_008 A v hv, reduce12_240 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_358 :
    A.L (8) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = 0 := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_336 A v hv, reduce12_357 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_359 :
    A.L (5) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (80 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_042 A v hv, reduce12_357 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_360 :
    A.L (8) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (880 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_358 A v hv, reduce12_359 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_361 :
    A.L (8) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = 0 := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_195 A v hv, reduce12_312 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_362 :
    A.L (5) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (192 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (12 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_048 A v hv, reduce12_312 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_363 :
    A.L (8) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (2112 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (132 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (8) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_361 A v hv, reduce12_362 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_364 :
    A.L (6) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (1920 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (240 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_259 A v hv, reduce12_355 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 8 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_365 :
    A.L (8) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (23040 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (3600 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (8) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_269 A v hv, reduce12_364 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_366 :
    A.L (7) (A.L (-12) (v)) = (19 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (7) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_367 :
    A.L (7) (A.L (-10) (A.L (-2) (v))) = (17 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_166 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_368 :
    A.L (7) (A.L (-9) (A.L (-3) (v))) = (16 : ℂ) • (A.L (-5) (v)) + (16 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_038 A v hv, reduce12_172 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_369 :
    A.L (7) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_370 :
    A.L (-1) (A.L (-4) (v)) = (3 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (-1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_371 :
    A.L (7) (A.L (-8) (A.L (-4) (v))) = (45 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (7) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_369 A v hv, reduce12_370 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_372 :
    A.L (7) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (15 : ℂ) • (A.L (-5) (v)) + (30 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_044 A v hv, reduce12_177 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_373 :
    A.L (7) (A.L (-5) (v)) = 0 := by
  rw [vir_push A (7) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_374 :
    A.L (0) (A.L (-5) (v)) = (5 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (0) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_375 :
    A.L (7) (A.L (-7) (A.L (-5) (v))) = (70 : ℂ) • (A.L (-5) (v)) + (28 : ℂ) • ((A.central ^ 1) (A.L (-5) (v))) := by
  rw [vir_push A (7) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_373 A v hv, reduce12_374 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_376 :
    A.L (0) (A.L (-3) (A.L (-2) (v))) = (5 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_377 :
    A.L (7) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (70 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (28 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (7) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_254 A v hv, reduce12_376 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_378 :
    A.L (7) (A.L (-6) (v)) = 0 := by
  rw [vir_push A (7) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_379 :
    A.L (7) (A.L (-6) (A.L (-6) (v))) = (91 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (7) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_028 A v hv, reduce12_378 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_380 :
    A.L (7) (A.L (-4) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_166 A v hv, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_381 :
    A.L (7) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (65 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_034 A v hv, reduce12_380 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_382 :
    A.L (7) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (52 : ℂ) • (A.L (-5) (v)) + (104 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_039 A v hv, reduce12_261 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_383 :
    A.L (7) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (78 : ℂ) • (A.L (-5) (v)) + (117 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_045 A v hv, reduce12_265 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_384 :
    A.L (7) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (84 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (12 : ℂ) • ((A.central ^ 1) (A.L (-5) (v))) := by
  rw [vir_push A (7) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_053 A v hv, reduce12_168 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_385 :
    A.L (7) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (72 : ℂ) • (A.L (-5) (v)) + (72 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (22 : ℂ) • ((A.central ^ 1) (A.L (-5) (v))) := by
  rw [vir_push A (7) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_058 A v hv, reduce12_173 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_386 :
    A.L (7) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (60 : ℂ) • (A.L (-5) (v)) + (216 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (30 : ℂ) • ((A.central ^ 1) (A.L (-5) (v))) + (12 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (7) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_063 A v hv, reduce12_178 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_387 :
    A.L (3) (A.L (-4) (v)) = 0 := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_388 :
    A.L (7) (A.L (-4) (A.L (-4) (v))) = 0 := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_369 A v hv, reduce12_387 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_389 :
    A.L (3) (A.L (-4) (A.L (-4) (v))) = (21 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_370 A v hv, reduce12_387 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_390 :
    A.L (7) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (231 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_388 A v hv, reduce12_389 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_391 :
    A.L (7) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_177 A v hv, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_392 :
    A.L (3) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (7 : ℂ) • (A.L (-5) (v)) + (14 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_044 A v hv, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_393 :
    A.L (7) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (77 : ℂ) • (A.L (-5) (v)) + (154 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_391 A v hv, reduce12_392 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_394 :
    A.L (7) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_254 A v hv, reduce12_352 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_395 :
    A.L (3) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (42 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (4 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_222 A v hv, reduce12_376 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_396 :
    A.L (7) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (462 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (44 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_394 A v hv, reduce12_395 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_397 :
    A.L (3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (45 : ℂ) • (A.L (-5) (v)) + (60 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_038 A v hv, reduce12_045 A v hv, reduce12_290 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_398 :
    A.L (7) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (495 : ℂ) • (A.L (-5) (v)) + (660 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_319 A v hv, reduce12_397 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_399 :
    A.L (4) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (28 : ℂ) • (A.L (-5) (v)) + (84 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_039 A v hv, reduce12_232 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_400 :
    A.L (7) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (280 : ℂ) • (A.L (-5) (v)) + (1120 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_263 A v hv, reduce12_399 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_401 :
    A.L (4) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (42 : ℂ) • (A.L (-5) (v)) + (111 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (9 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_045 A v hv, reduce12_234 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_402 :
    A.L (7) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (420 : ℂ) • (A.L (-5) (v)) + (1590 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (180 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (7) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_267 A v hv, reduce12_401 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_403 :
    A.L (5) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (420 : ℂ) • (A.L (-5) (v)) + (525 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (5) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_038 A v hv, reduce12_313 A v hv, reduce12_397 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 7 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_404 :
    A.L (7) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (4725 : ℂ) • (A.L (-5) (v)) + (5670 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (7) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_038 A v hv, reduce12_321 A v hv, reduce12_403 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_405 :
    A.L (6) (A.L (-12) (v)) = (18 : ℂ) • (A.L (-6) (v)) := by
  rw [vir_push A (6) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_406 :
    A.L (6) (A.L (-10) (A.L (-2) (v))) = (16 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (6) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_153 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_407 :
    A.L (6) (A.L (-9) (A.L (-3) (v))) = (15 : ℂ) • (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (6) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_158 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_408 :
    A.L (6) (A.L (-8) (A.L (-4) (v))) = (28 : ℂ) • (A.L (-6) (v)) + (14 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (6) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_070 A v hv, reduce12_247 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_409 :
    A.L (6) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (14 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (6) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_163 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_410 :
    A.L (6) (A.L (-5) (v)) = 0 := by
  rw [vir_push A (6) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_411 :
    A.L (-1) (A.L (-5) (v)) = (4 : ℂ) • (A.L (-6) (v)) := by
  rw [vir_push A (-1) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_412 :
    A.L (6) (A.L (-7) (A.L (-5) (v))) = (52 : ℂ) • (A.L (-6) (v)) := by
  rw [vir_push A (6) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_410 A v hv, reduce12_411 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_413 :
    A.L (6) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (26 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (13 : ℂ) • (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (6) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_083 A v hv, reduce12_256 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_414 :
    A.L (0) (A.L (-6) (v)) = (6 : ℂ) • (A.L (-6) (v)) := by
  rw [vir_push A (0) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_415 :
    A.L (6) (A.L (-6) (A.L (-6) (v))) = (72 : ℂ) • (A.L (-6) (v)) + (35 : ℂ) • ((A.central ^ 1) (A.L (-6) (v))) := by
  rw [vir_push A (6) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_149 A v hv, reduce12_414 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_416 :
    A.L (0) (A.L (-4) (A.L (-2) (v))) = (6 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (0) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_417 :
    A.L (6) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (72 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-6) (v))) + (35/2 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (v)))) := by
  rw [vir_push A (6) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_154 A v hv, reduce12_416 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_418 :
    A.L (0) (A.L (-3) (A.L (-3) (v))) = (6 : ℂ) • (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_273 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_419 :
    A.L (6) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (72 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (18 : ℂ) • ((A.central ^ 1) (A.L (-6) (v))) + (35/2 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (6) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_159 A v hv, reduce12_418 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_420 :
    A.L (6) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (72 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (24 : ℂ) • ((A.central ^ 1) (A.L (-6) (v))) + (35/2 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (6) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_091 A v hv, reduce12_164 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_421 :
    A.L (6) (A.L (-5) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (6) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv, reduce12_153 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_422 :
    A.L (6) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (66 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (6) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_050 A v hv, reduce12_421 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_423 :
    A.L (6) (A.L (-4) (A.L (-3) (v))) = 0 := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_008 A v hv, reduce12_158 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_424 :
    A.L (6) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (44 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (55 : ℂ) • (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (6) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_056 A v hv, reduce12_423 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_425 :
    A.L (6) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = 0 := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_163 A v hv, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_426 :
    A.L (6) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (33 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (44 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (6) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_061 A v hv, reduce12_425 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_427 :
    A.L (6) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (120 : ℂ) • (A.L (-6) (v)) + (180 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_071 A v hv, reduce12_249 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_428 :
    A.L (6) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (160 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (60 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (20 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (v)))) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_077 A v hv, reduce12_252 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_429 :
    A.L (6) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (208 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (100 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (18 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (v)))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_084 A v hv, reduce12_257 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_430 :
    A.L (6) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (384 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (480 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (96 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (v)))) + (20 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_092 A v hv, reduce12_259 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_431 :
    A.L (3) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (54 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (6 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_287 A v hv, reduce12_418 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_432 :
    A.L (6) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (648 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (108 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_315 A v hv, reduce12_431 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_433 :
    A.L (3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (15 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (36 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_091 A v hv, reduce12_290 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_434 :
    A.L (6) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (270 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (324 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (24 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (v)))) + (18 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_317 A v hv, reduce12_433 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_435 :
    A.L (4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (480 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (30 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_092 A v hv, reduce12_355 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_436 :
    A.L (6) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (5760 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) + (480 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_364 A v hv, reduce12_435 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_437 :
    A.L (5) (A.L (-12) (v)) = (17 : ℂ) • (A.L (-7) (v)) := by
  rw [vir_push A (5) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_438 :
    A.L (5) (A.L (-10) (A.L (-2) (v))) = (15 : ℂ) • (A.L (-5) (A.L (-2) (v))) := by
  rw [vir_push A (5) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_145 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_439 :
    A.L (5) (A.L (-9) (A.L (-3) (v))) = (14 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (5) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_240 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_440 :
    A.L (5) (A.L (-8) (A.L (-4) (v))) = (13 : ℂ) • (A.L (-7) (v)) + (13 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (5) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_065 A v hv, reduce12_301 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_441 :
    A.L (5) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (13 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (5) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_244 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_442 :
    A.L (5) (A.L (-7) (A.L (-5) (v))) = (36 : ℂ) • (A.L (-7) (v)) + (12 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (10 : ℂ) • ((A.central ^ 1) (A.L (-7) (v))) := by
  rw [vir_push A (5) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_087 A v hv, reduce12_141 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_443 :
    A.L (5) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (12 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (12 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) + (4 : ℂ) • ((A.central ^ 1) (A.L (-7) (v))) := by
  rw [vir_push A (5) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_080 A v hv, reduce12_146 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_444 :
    A.L (5) (A.L (-6) (v)) = 0 := by
  rw [vir_push A (5) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_445 :
    A.L (-1) (A.L (-6) (v)) = (5 : ℂ) • (A.L (-7) (v)) := by
  rw [vir_push A (-1) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_446 :
    A.L (5) (A.L (-6) (A.L (-6) (v))) = (55 : ℂ) • (A.L (-7) (v)) := by
  rw [vir_push A (5) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_444 A v hv, reduce12_445 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_447 :
    A.L (5) (A.L (-4) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_002 A v hv, reduce12_145 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_448 :
    A.L (-1) (A.L (-4) (A.L (-2) (v))) = (3 : ℂ) • (A.L (-5) (A.L (-2) (v))) + A.L (-4) (A.L (-3) (v)) := by
  rw [vir_push A (-1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_014 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_449 :
    A.L (5) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (33 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (11 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (5) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_447 A v hv, reduce12_448 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_450 :
    A.L (5) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (22 : ℂ) • (A.L (-7) (v)) + (44 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (5) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_101 A v hv, reduce12_357 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_451 :
    A.L (5) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (33 : ℂ) • (A.L (-7) (v)) + (33 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (33 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (5) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_088 A v hv, reduce12_312 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_452 :
    A.L (0) (A.L (-5) (A.L (-2) (v))) = (7 : ℂ) • (A.L (-5) (A.L (-2) (v))) := by
  rw [vir_push A (0) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_017 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_453 :
    A.L (5) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (90 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (20 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-2) (v)))) := by
  rw [vir_push A (5) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_237 A v hv, reduce12_452 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_454 :
    A.L (0) (A.L (-4) (A.L (-3) (v))) = (7 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (0) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_273 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_455 :
    A.L (5) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (36 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (70 : ℂ) • (A.L (-4) (A.L (-3) (v))) + (10 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-3) (v)))) := by
  rw [vir_push A (5) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_241 A v hv, reduce12_454 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_456 :
    A.L (0) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (7 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_047 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_457 :
    A.L (5) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (64 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (70 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) + (8 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-2) (v)))) + (10 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (5) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_245 A v hv, reduce12_456 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_458 :
    A.L (5) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (45 : ℂ) • (A.L (-7) (v)) + (135 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_066 A v hv, reduce12_303 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_459 :
    A.L (5) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (54 : ℂ) • (A.L (-4) (A.L (-3) (v))) + (45 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_074 A v hv, reduce12_306 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_460 :
    A.L (5) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (36 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (40 : ℂ) • (A.L (-4) (A.L (-3) (v))) + (72 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) + (8 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-3) (v)))) := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_081 A v hv, reduce12_309 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_461 :
    A.L (5) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (243 : ℂ) • (A.L (-7) (v)) + (216 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (105 : ℂ) • (A.L (-4) (A.L (-3) (v))) + (162 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (5) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_089 A v hv, reduce12_313 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_462 :
    A.L (5) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (240 : ℂ) • (A.L (-7) (v)) + (320 : ℂ) • (A.L (-4) (A.L (-3) (v))) := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_065 A v hv, reduce12_102 A v hv, reduce12_359 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_463 :
    A.L (5) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (120 : ℂ) • (A.L (-7) (v)) + (120 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (504 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) + (24 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (5) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_109 A v hv, reduce12_362 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_464 :
    A.L (3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (270 : ℂ) • (A.L (-7) (v)) + (225 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (150 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_080 A v hv, reduce12_087 A v hv, reduce12_089 A v hv, reduce12_397 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_465 :
    A.L (5) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (3150 : ℂ) • (A.L (-7) (v)) + (2520 : ℂ) • (A.L (-5) (A.L (-2) (v))) + (1575 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (5) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_080 A v hv, reduce12_087 A v hv, reduce12_403 A v hv, reduce12_464 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 5 through the ordered creation word [-7].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_466 :
    A.L (5) (A.L (-7) (v)) = (12 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (5) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-7].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_467 :
    A.L (4) (A.L (-7) (v)) = (11 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (4) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-7].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_468 :
    A.L (3) (A.L (-7) (v)) = (10 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (3) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_469 :
    A.L (4) (A.L (-12) (v)) = (16 : ℂ) • (A.L (-8) (v)) := by
  rw [vir_push A (4) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_470 :
    A.L (4) (A.L (-10) (A.L (-2) (v))) = (14 : ℂ) • (A.L (-6) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_137 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_471 :
    A.L (4) (A.L (-9) (A.L (-3) (v))) = (13 : ℂ) • (A.L (-5) (A.L (-3) (v))) := by
  rw [vir_push A (4) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_231 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_472 :
    A.L (4) (A.L (-8) (A.L (-4) (v))) = (12 : ℂ) • (A.L (-4) (A.L (-4) (v))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-8) (v))) := by
  rw [vir_push A (4) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_133 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_473 :
    A.L (4) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (12 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (3 : ℂ) • ((A.central ^ 1) (A.L (-8) (v))) := by
  rw [vir_push A (4) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_138 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_474 :
    A.L (4) (A.L (-5) (v)) = 0 := by
  rw [vir_push A (4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_475 :
    A.L (4) (A.L (-7) (A.L (-5) (v))) = (22 : ℂ) • (A.L (-8) (v)) + (11 : ℂ) • (A.L (-5) (A.L (-3) (v))) := by
  rw [vir_push A (4) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_094 A v hv, reduce12_474 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_476 :
    A.L (4) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (11 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_352 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_477 :
    A.L (-2) (A.L (-6) (v)) = (4 : ℂ) • (A.L (-8) (v)) + A.L (-6) (A.L (-2) (v)) := by
  rw [vir_push A (-2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_478 :
    A.L (4) (A.L (-6) (A.L (-6) (v))) = (40 : ℂ) • (A.L (-8) (v)) + (20 : ℂ) • (A.L (-6) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_225 A v hv, reduce12_477 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_479 :
    A.L (-2) (A.L (-4) (A.L (-2) (v))) = (2 : ℂ) • (A.L (-6) (A.L (-2) (v))) + A.L (-4) (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (-2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_480 :
    A.L (4) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (36 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-6) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_228 A v hv, reduce12_479 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_481 :
    A.L (4) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (20 : ℂ) • (A.L (-8) (v)) + (28 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (20 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (10 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_095 A v hv, reduce12_232 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_482 :
    A.L (4) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (48 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (9 : ℂ) • ((A.central ^ 1) (A.L (-6) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_234 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_483 :
    A.L (-1) (A.L (-5) (A.L (-2) (v))) = (4 : ℂ) • (A.L (-6) (A.L (-2) (v))) + A.L (-5) (A.L (-3) (v)) := by
  rw [vir_push A (-1) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_014 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_484 :
    A.L (4) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (36 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (18 : ℂ) • (A.L (-5) (A.L (-3) (v))) := by
  rw [vir_push A (4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_293 A v hv, reduce12_483 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_485 :
    A.L (-1) (A.L (-4) (A.L (-3) (v))) = (3 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (2 : ℂ) • (A.L (-4) (A.L (-4) (v))) := by
  rw [vir_push A (-1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_041 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_486 :
    A.L (4) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (51 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (18 : ℂ) • (A.L (-4) (A.L (-4) (v))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-3) (v)))) := by
  rw [vir_push A (4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_296 A v hv, reduce12_485 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_487 :
    A.L (-1) (A.L (-3) (A.L (-2) (A.L (-2) (v)))) = (2 : ℂ) • (A.L (-8) (v)) + A.L (-5) (A.L (-3) (v)) + (2 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (2 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_044 A v hv, reduce12_094 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_488 :
    A.L (4) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (18 : ℂ) • (A.L (-8) (v)) + (30 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (18 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (18 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) + (3 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-3) (v)))) := by
  rw [vir_push A (4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_299 A v hv, reduce12_487 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_489 :
    A.L (0) (A.L (-4) (A.L (-4) (v))) = (8 : ℂ) • (A.L (-4) (A.L (-4) (v))) := by
  rw [vir_push A (0) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_326 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_490 :
    A.L (4) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (96 : ℂ) • (A.L (-4) (A.L (-4) (v))) + (15 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-4) (v)))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_348 A v hv, reduce12_489 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_491 :
    A.L (0) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = (8 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (0) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_047 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_492 :
    A.L (4) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (96 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (3 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-4) (v)))) + (10 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_350 A v hv, reduce12_491 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_493 :
    A.L (0) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (8 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_376 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_494 :
    A.L (4) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (28 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (64 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_353 A v hv, reduce12_493 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_495 :
    A.L (4) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (192 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (64 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (18 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) + (5 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_122 A v hv, reduce12_355 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_496 :
    A.L (4) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (168 : ℂ) • (A.L (-8) (v)) + (112 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (168 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_094 A v hv, reduce12_096 A v hv, reduce12_399 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_497 :
    A.L (4) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (168 : ℂ) • (A.L (-8) (v)) + (84 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (174 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) + (28 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (9 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_094 A v hv, reduce12_106 A v hv, reduce12_401 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_498 :
    A.L (4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (960 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (45 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_123 A v hv, reduce12_435 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-8].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_499 :
    A.L (4) (A.L (-8) (v)) = (12 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (4) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-6, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_500 :
    A.L (4) (A.L (-6) (A.L (-2) (v))) = (10 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_137 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the ordered creation word [-5, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_501 :
    A.L (4) (A.L (-5) (A.L (-3) (v))) = (18 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_041 A v hv, reduce12_231 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-8].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_502 :
    A.L (3) (A.L (-8) (v)) = (11 : ℂ) • (A.L (-5) (v)) := by
  rw [vir_push A (3) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-6, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_503 :
    A.L (3) (A.L (-6) (A.L (-2) (v))) = (9 : ℂ) • (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_504 :
    A.L (3) (A.L (-5) (A.L (-3) (v))) = (8 : ℂ) • (A.L (-5) (v)) + (8 : ℂ) • (A.L (-3) (A.L (-2) (v))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-5) (v))) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_038 A v hv, reduce12_130 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-8].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_505 :
    A.L (2) (A.L (-8) (v)) = (10 : ℂ) • (A.L (-6) (v)) := by
  rw [vir_push A (2) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_506 :
    A.L (2) (A.L (-6) (A.L (-2) (v))) = (8 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-6) (v))) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_507 :
    A.L (2) (A.L (-5) (A.L (-3) (v))) = (7 : ℂ) • (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_008 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-12].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_508 :
    A.L (3) (A.L (-12) (v)) = (15 : ℂ) • (A.L (-9) (v)) := by
  rw [vir_push A (3) (-12)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-10, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_509 :
    A.L (3) (A.L (-10) (A.L (-2) (v))) = (13 : ℂ) • (A.L (-7) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-9, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_510 :
    A.L (3) (A.L (-9) (A.L (-3) (v))) = (12 : ℂ) • (A.L (-6) (A.L (-3) (v))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-9) (v))) := by
  rw [vir_push A (3) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_130 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-8, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_511 :
    A.L (3) (A.L (-8) (A.L (-4) (v))) = (11 : ℂ) • (A.L (-5) (A.L (-4) (v))) := by
  rw [vir_push A (3) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_387 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-8, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_512 :
    A.L (3) (A.L (-8) (A.L (-2) (A.L (-2) (v)))) = (11 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -4 through the ordered creation word [-5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_513 :
    A.L (-4) (A.L (-5) (v)) = A.L (-9) (v) + A.L (-5) (A.L (-4) (v)) := by
  rw [vir_push A (-4) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-7, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_514 :
    A.L (3) (A.L (-7) (A.L (-5) (v))) = (10 : ℂ) • (A.L (-9) (v)) + (8 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-5) (A.L (-4) (v))) := by
  rw [vir_push A (3) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_218 A v hv, reduce12_513 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-7, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_515 :
    A.L (3) (A.L (-7) (A.L (-3) (A.L (-2) (v)))) = (12 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (10 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-7) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_222 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_516 :
    A.L (-3) (A.L (-6) (v)) = (3 : ℂ) • (A.L (-9) (v)) + A.L (-6) (A.L (-3) (v)) := by
  rw [vir_push A (-3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-6, -6].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_517 :
    A.L (3) (A.L (-6) (A.L (-6) (v))) = (27 : ℂ) • (A.L (-9) (v)) + (18 : ℂ) • (A.L (-6) (A.L (-3) (v))) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_282 A v hv, reduce12_516 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -3 through the ordered creation word [-4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_518 :
    A.L (-3) (A.L (-4) (A.L (-2) (v))) = A.L (-7) (A.L (-2) (v)) + A.L (-4) (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (-3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-6, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_519 :
    A.L (3) (A.L (-6) (A.L (-4) (A.L (-2) (v)))) = (9 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (7 : ℂ) • (A.L (-6) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_285 A v hv, reduce12_518 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-6, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_520 :
    A.L (3) (A.L (-6) (A.L (-3) (A.L (-3) (v)))) = (18 : ℂ) • (A.L (-6) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (v)))) + (4 : ℂ) • ((A.central ^ 1) (A.L (-6) (A.L (-3) (v)))) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_287 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-6, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_521 :
    A.L (3) (A.L (-6) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (15 : ℂ) • (A.L (-6) (A.L (-3) (v))) + (9 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_290 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5, -5, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_522 :
    A.L (3) (A.L (-5) (A.L (-5) (A.L (-2) (v)))) = (24 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (16 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_113 A v hv, reduce12_340 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -2 through the ordered creation word [-4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_523 :
    A.L (-2) (A.L (-4) (A.L (-3) (v))) = A.L (-9) (v) + (2 : ℂ) • (A.L (-6) (A.L (-3) (v))) + A.L (-5) (A.L (-4) (v)) + A.L (-4) (A.L (-3) (A.L (-2) (v))) := by
  rw [vir_push A (-2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_038 A v hv, reduce12_513 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5, -4, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_524 :
    A.L (3) (A.L (-5) (A.L (-4) (A.L (-3) (v)))) = (8 : ℂ) • (A.L (-9) (v)) + (16 : ℂ) • (A.L (-6) (A.L (-3) (v))) + (22 : ℂ) • (A.L (-5) (A.L (-4) (v))) + (8 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-4) (v)))) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_343 A v hv, reduce12_523 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_525 :
    A.L (3) (A.L (-5) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (32 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) + (8 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_112 A v hv, reduce12_346 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_526 :
    A.L (-1) (A.L (-4) (A.L (-4) (v))) = (3 : ℂ) • (A.L (-9) (v)) + (6 : ℂ) • (A.L (-5) (A.L (-4) (v))) := by
  rw [vir_push A (-1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_370 A v hv, reduce12_513 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -4, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_527 :
    A.L (3) (A.L (-4) (A.L (-4) (A.L (-4) (v)))) = (42 : ℂ) • (A.L (-9) (v)) + (63 : ℂ) • (A.L (-5) (A.L (-4) (v))) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_389 A v hv, reduce12_513 A v hv, reduce12_526 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_528 :
    A.L (-1) (A.L (-4) (A.L (-2) (A.L (-2) (v)))) = A.L (-9) (v) + A.L (-5) (A.L (-4) (v)) + (3 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) + (2 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (-1) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_044 A v hv, reduce12_513 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -4, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_529 :
    A.L (3) (A.L (-4) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) = (14 : ℂ) • (A.L (-9) (v)) + (14 : ℂ) • (A.L (-5) (A.L (-4) (v))) + (21 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) + (28 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_392 A v hv, reduce12_513 A v hv, reduce12_528 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the ordered creation word [-3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_530 :
    A.L (-1) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) = (2 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (4 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) + A.L (-3) (A.L (-3) (A.L (-3) (v))) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_083 A v hv, reduce12_518 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -3, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_531 :
    A.L (3) (A.L (-4) (A.L (-3) (A.L (-3) (A.L (-2) (v))))) = (14 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (70 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) + (7 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (v)))) + (4 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-3) (A.L (-2) (v))))) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_395 A v hv, reduce12_530 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_532 :
    A.L (3) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (150 : ℂ) • (A.L (-9) (v)) + (84 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (45 : ℂ) • (A.L (-5) (A.L (-4) (v))) + (42 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) + (60 : ℂ) • (A.L (-4) (A.L (-3) (A.L (-2) (v)))) + (28 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_115 A v hv, reduce12_397 A v hv, reduce12_513 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_533 :
    A.L (0) (A.L (-3) (A.L (-3) (A.L (-3) (v)))) = (9 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (v)))) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_418 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -3, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_534 :
    A.L (3) (A.L (-3) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) = (108 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (v)))) + (8 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-3) (A.L (-3) (v))))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_431 A v hv, reduce12_533 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the ordered creation word [-3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_535 :
    A.L (0) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (9 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_091 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-3, -3, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_536 :
    A.L (3) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) = (15 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-3) (v)))) + (90 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (4 : ℂ) • ((A.central ^ 1) (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_433 A v hv, reduce12_535 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-2, -2, -2, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_537 :
    A.L (3) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))))) = (2250 : ℂ) • (A.L (-9) (v)) + (1620 : ℂ) • (A.L (-7) (A.L (-2) (v))) + (675 : ℂ) • (A.L (-5) (A.L (-2) (A.L (-2) (v)))) + (300 : ℂ) • (A.L (-3) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_116 A v hv, reduce12_464 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-9].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_538 :
    A.L (3) (A.L (-9) (v)) = (12 : ℂ) • (A.L (-6) (v)) := by
  rw [vir_push A (3) (-9)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-7, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_539 :
    A.L (3) (A.L (-7) (A.L (-2) (v))) = (10 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_221 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-6, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_540 :
    A.L (3) (A.L (-6) (A.L (-3) (v))) = (9 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-6) (v))) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_130 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_541 :
    A.L (3) (A.L (-5) (A.L (-4) (v))) = (16 : ℂ) • (A.L (-6) (v)) + (8 : ℂ) • (A.L (-4) (A.L (-2) (v))) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_070 A v hv, reduce12_387 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-5, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_542 :
    A.L (3) (A.L (-5) (A.L (-2) (A.L (-2) (v)))) = (8 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_289 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the ordered creation word [-4, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_543 :
    A.L (3) (A.L (-4) (A.L (-3) (A.L (-2) (v)))) = (26 : ℂ) • (A.L (-4) (A.L (-2) (v))) + (7 : ℂ) • (A.L (-3) (A.L (-3) (v))) + (2 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (v)))) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_083 A v hv, reduce12_222 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-10].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_544 :
    A.L (2) (A.L (-10) (v)) = (12 : ℂ) • (A.L (-8) (v)) := by
  rw [vir_push A (2) (-10)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-8, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_545 :
    A.L (2) (A.L (-8) (A.L (-2) (v))) = (10 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-8) (v))) := by
  rw [vir_push A (2) (-8)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_004 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-7, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_546 :
    A.L (2) (A.L (-7) (A.L (-3) (v))) = (9 : ℂ) • (A.L (-5) (A.L (-3) (v))) := by
  rw [vir_push A (2) (-7)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_008 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6, -4].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_547 :
    A.L (2) (A.L (-6) (A.L (-4) (v))) = (6 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (8 : ℂ) • (A.L (-4) (A.L (-4) (v))) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_012 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-6, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_548 :
    A.L (2) (A.L (-6) (A.L (-2) (A.L (-2) (v)))) = (8 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (8 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (A.central ^ 1) (A.L (-6) (A.L (-2) (v))) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_018 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5, -5].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_549 :
    A.L (2) (A.L (-5) (A.L (-5) (v))) = (14 : ℂ) • (A.L (-8) (v)) + (14 : ℂ) • (A.L (-5) (A.L (-3) (v))) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_022 A v hv, reduce12_094 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-5, -3, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_550 :
    A.L (2) (A.L (-5) (A.L (-3) (A.L (-2) (v)))) = (5 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (7 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-5) (A.L (-3) (v)))) := by
  rw [vir_push A (2) (-5)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_026 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -4, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_551 :
    A.L (2) (A.L (-4) (A.L (-4) (A.L (-2) (v)))) = (12 : ℂ) • (A.L (-6) (A.L (-2) (v))) + (12 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-4) (v)))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_036 A v hv, reduce12_479 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -3, -3].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_552 :
    A.L (2) (A.L (-4) (A.L (-3) (A.L (-3) (v)))) = (12 : ℂ) • (A.L (-8) (v)) + (12 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (10 : ℂ) • (A.L (-4) (A.L (-4) (v))) + (6 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_042 A v hv, reduce12_095 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-4, -2, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_553 :
    A.L (2) (A.L (-4) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) = (24 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (6 : ℂ) • (A.L (-2) (A.L (-2) (A.L (-2) (A.L (-2) (v))))) + (3/2 : ℂ) • ((A.central ^ 1) (A.L (-4) (A.L (-2) (A.L (-2) (v))))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_048 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the ordered creation word [-3, -3, -2, -2].
The resulting rational coefficients and central powers follow from the
Virasoro bracket; modes at least minus one annihilate the vacuum. -/
private theorem reduce12_554 :
    A.L (2) (A.L (-3) (A.L (-3) (A.L (-2) (A.L (-2) (v))))) = (20 : ℂ) • (A.L (-8) (v)) + (10 : ℂ) • (A.L (-5) (A.L (-3) (v))) + (10 : ℂ) • (A.L (-4) (A.L (-2) (A.L (-2) (v)))) + (28 : ℂ) • (A.L (-3) (A.L (-3) (A.L (-2) (v)))) + (A.central ^ 1) (A.L (-3) (A.L (-3) (A.L (-2) (v)))) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce12_063 A v hv, reduce12_094 A v hv, reduce12_487 A v hv]
  all_goals try simp [hv]
  all_goals module

set_option maxHeartbeats 2000000 in
/-- The actual weight-twelve expression is killed by L1 at charge 7/10.
All coefficients are checked from the Virasoro relations, not assumed
from a classification or a determinant formula. -/
theorem tricritical_L1_zero (hK : A.central=(7/10:ℂ) • 1) :
    A.L 1 (tricriticalState A.L v)=0 := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  try rw [hK]
  norm_num [pow_succ,Module.End.mul_apply,LinearMap.smul_apply]
  module

set_option maxHeartbeats 2000000 in
/-- The actual weight-twelve expression is killed by L2 at charge 7/10.
All coefficients are checked from the Virasoro relations, not assumed
from a classification or a determinant formula. -/
theorem tricritical_L2_zero (hK : A.central=(7/10:ℂ) • 1) :
    A.L 2 (tricriticalState A.L v)=0 := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  try rw [hK]
  norm_num [pow_succ,Module.End.mul_apply,LinearMap.smul_apply]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [12] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_00 :
    virWord A.L [12] (tricriticalState A.L v)=0 := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [10, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_01 :
    virWord A.L [2,10] (tricriticalState A.L v)=(2088100 : ℂ) • ((A.central ^ 1) (v)) + (-2983000 : ℂ) • ((A.central ^ 2) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [9, 3] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_02 :
    virWord A.L [3,9] (tricriticalState A.L v)=(-16704800 : ℂ) • ((A.central ^ 1) (v)) + (23864000 : ℂ) • ((A.central ^ 2) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [8, 4] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_03 :
    virWord A.L [4,8] (tricriticalState A.L v)=(58466800 : ℂ) • ((A.central ^ 1) (v)) + (-83524000 : ℂ) • ((A.central ^ 2) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [8, 2, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_04 :
    virWord A.L [2,2,8] (tricriticalState A.L v)=(-9020592 : ℂ) • ((A.central ^ 1) (v)) + (2863680 : ℂ) • ((A.central ^ 2) (v)) + (14318400 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [7, 5] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_05 :
    virWord A.L [5,7] (tricriticalState A.L v)=(-116933600 : ℂ) • ((A.central ^ 1) (v)) + (167048000 : ℂ) • ((A.central ^ 2) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [7, 3, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_06 :
    virWord A.L [2,3,7] (tricriticalState A.L v)=(85528576 : ℂ) • ((A.central ^ 1) (v)) + (-92115040 : ℂ) • ((A.central ^ 2) (v)) + (-42955200 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [6, 6] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_07 :
    virWord A.L [6,6] (tricriticalState A.L v)=(146167000 : ℂ) • ((A.central ^ 1) (v)) + (-208810000 : ℂ) • ((A.central ^ 2) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [6, 4, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_08 :
    virWord A.L [2,4,6] (tricriticalState A.L v)=(-655982320 : ℂ) • ((A.central ^ 1) (v)) + (2053670800 : ℂ) • ((A.central ^ 2) (v)) + (-1595076000 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [6, 3, 3] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_09 :
    virWord A.L [3,3,6] (tricriticalState A.L v)=(884321760 : ℂ) • ((A.central ^ 1) (v)) + (-3646766400 : ℂ) • ((A.central ^ 2) (v)) + (3404928000 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [6, 2, 2, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_10 :
    virWord A.L [2,2,2,6] (tricriticalState A.L v)=(246220800 : ℂ) • ((A.central ^ 1) (v)) + (-193422480 : ℂ) • ((A.central ^ 2) (v)) + (-366436800 : ℂ) • ((A.central ^ 3) (v)) + (200376000 : ℂ) • ((A.central ^ 4) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [5, 5, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_11 :
    virWord A.L [2,5,5] (tricriticalState A.L v)=(1149928080 : ℂ) • ((A.central ^ 1) (v)) + (-3925975200 : ℂ) • ((A.central ^ 2) (v)) + (3261744000 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [5, 4, 3] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_12 :
    virWord A.L [3,4,5] (tricriticalState A.L v)=(-825854960 : ℂ) • ((A.central ^ 1) (v)) + (3563242400 : ℂ) • ((A.central ^ 2) (v)) + (-3404928000 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [5, 3, 2, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_13 :
    virWord A.L [2,2,3,5] (tricriticalState A.L v)=(-1361288880 : ℂ) • ((A.central ^ 1) (v)) + (4016823840 : ℂ) • ((A.central ^ 2) (v)) + (-2773161600 : ℂ) • ((A.central ^ 3) (v)) + (-267168000 : ℂ) • ((A.central ^ 4) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [4, 4, 4] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_14 :
    virWord A.L [4,4,4] (tricriticalState A.L v)=(2502622080 : ℂ) • ((A.central ^ 1) (v)) + (-10725523200 : ℂ) • ((A.central ^ 2) (v)) + (10214784000 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [4, 4, 2, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_15 :
    virWord A.L [2,2,4,4] (tricriticalState A.L v)=(2450136864 : ℂ) • ((A.central ^ 1) (v)) + (-7912661200 : ℂ) • ((A.central ^ 2) (v)) + (6226740800 : ℂ) • ((A.central ^ 3) (v)) + (109688000 : ℂ) • ((A.central ^ 4) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [4, 3, 3, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_16 :
    virWord A.L [2,3,3,4] (tricriticalState A.L v)=(-45390464 : ℂ) • ((A.central ^ 1) (v)) + (177396240 : ℂ) • ((A.central ^ 2) (v)) + (-364534400 : ℂ) • ((A.central ^ 3) (v)) + (291064000 : ℂ) • ((A.central ^ 4) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [4, 2, 2, 2, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_17 :
    virWord A.L [2,2,2,2,4] (tricriticalState A.L v)=(-1647967776 : ℂ) • ((A.central ^ 1) (v)) + (3909323616 : ℂ) • ((A.central ^ 2) (v)) + (-1692529920 : ℂ) • ((A.central ^ 3) (v)) + (-725232000 : ℂ) • ((A.central ^ 4) (v)) + (-43584000 : ℂ) • ((A.central ^ 5) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [3, 3, 3, 3] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_18 :
    virWord A.L [3,3,3,3] (tricriticalState A.L v)=(-257533472 : ℂ) • ((A.central ^ 1) (v)) + (-487823200 : ℂ) • ((A.central ^ 2) (v)) + (2444937600 : ℂ) • ((A.central ^ 3) (v)) + (-1746384000 : ℂ) • ((A.central ^ 4) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [3, 3, 2, 2, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_19 :
    virWord A.L [2,2,2,3,3] (tricriticalState A.L v)=(2673979056 : ℂ) • ((A.central ^ 1) (v)) + (-7765837488 : ℂ) • ((A.central ^ 2) (v)) + (5091917760 : ℂ) • ((A.central ^ 3) (v)) + (763368000 : ℂ) • ((A.central ^ 4) (v)) + (21792000 : ℂ) • ((A.central ^ 5) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The adjoint of partition [2, 2, 2, 2, 2, 2] paired with the full
tricritical expression. This finite row reduction retains the central operator. -/
private theorem tricritical_row_20 :
    virWord A.L [2,2,2,2,2,2] (tricriticalState A.L v)=(6263591040 : ℂ) • ((A.central ^ 1) (v)) + (-8365055760 : ℂ) • ((A.central ^ 2) (v)) + (-1667494080 : ℂ) • ((A.central ^ 3) (v)) + (1198123200 : ℂ) • ((A.central ^ 4) (v)) + (-12096000 : ℂ) • ((A.central ^ 5) (v)) + (5760000 : ℂ) • ((A.central ^ 6) (v)) := by
  simp only [tricriticalAdjoint, tricriticalState, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce12_000 A v hv, reduce12_001 A v hv, reduce12_002 A v hv, reduce12_003 A v hv, reduce12_004 A v hv, reduce12_005 A v hv, reduce12_006 A v hv, reduce12_007 A v hv, reduce12_008 A v hv, reduce12_009 A v hv, reduce12_010 A v hv, reduce12_011 A v hv, reduce12_012 A v hv, reduce12_013 A v hv, reduce12_014 A v hv, reduce12_015 A v hv, reduce12_016 A v hv, reduce12_017 A v hv, reduce12_018 A v hv, reduce12_019 A v hv, reduce12_020 A v hv, reduce12_021 A v hv, reduce12_022 A v hv, reduce12_023 A v hv, reduce12_024 A v hv, reduce12_025 A v hv, reduce12_026 A v hv, reduce12_027 A v hv, reduce12_028 A v hv, reduce12_029 A v hv, reduce12_030 A v hv, reduce12_031 A v hv, reduce12_032 A v hv, reduce12_033 A v hv, reduce12_034 A v hv, reduce12_035 A v hv, reduce12_036 A v hv, reduce12_037 A v hv, reduce12_038 A v hv, reduce12_039 A v hv, reduce12_040 A v hv, reduce12_041 A v hv, reduce12_042 A v hv, reduce12_043 A v hv, reduce12_044 A v hv, reduce12_045 A v hv, reduce12_046 A v hv, reduce12_047 A v hv, reduce12_048 A v hv, reduce12_049 A v hv, reduce12_050 A v hv, reduce12_051 A v hv, reduce12_052 A v hv, reduce12_053 A v hv, reduce12_054 A v hv, reduce12_055 A v hv, reduce12_056 A v hv, reduce12_057 A v hv, reduce12_058 A v hv, reduce12_059 A v hv, reduce12_060 A v hv, reduce12_061 A v hv, reduce12_062 A v hv, reduce12_063 A v hv, reduce12_064 A v hv, reduce12_065 A v hv, reduce12_066 A v hv, reduce12_067 A v hv, reduce12_068 A v hv, reduce12_069 A v hv, reduce12_070 A v hv, reduce12_071 A v hv, reduce12_072 A v hv, reduce12_073 A v hv, reduce12_074 A v hv, reduce12_075 A v hv, reduce12_076 A v hv, reduce12_077 A v hv, reduce12_078 A v hv, reduce12_079 A v hv, reduce12_080 A v hv, reduce12_081 A v hv, reduce12_082 A v hv, reduce12_083 A v hv, reduce12_084 A v hv, reduce12_085 A v hv, reduce12_086 A v hv, reduce12_087 A v hv, reduce12_088 A v hv, reduce12_089 A v hv, reduce12_090 A v hv, reduce12_091 A v hv, reduce12_092 A v hv, reduce12_093 A v hv, reduce12_094 A v hv, reduce12_095 A v hv, reduce12_096 A v hv, reduce12_097 A v hv, reduce12_098 A v hv, reduce12_099 A v hv, reduce12_100 A v hv, reduce12_101 A v hv, reduce12_102 A v hv, reduce12_103 A v hv, reduce12_104 A v hv, reduce12_105 A v hv, reduce12_106 A v hv, reduce12_107 A v hv, reduce12_108 A v hv, reduce12_109 A v hv, reduce12_110 A v hv, reduce12_111 A v hv, reduce12_112 A v hv, reduce12_113 A v hv, reduce12_114 A v hv, reduce12_115 A v hv, reduce12_116 A v hv, reduce12_117 A v hv, reduce12_118 A v hv, reduce12_119 A v hv, reduce12_120 A v hv, reduce12_121 A v hv, reduce12_122 A v hv, reduce12_123 A v hv, reduce12_124 A v hv, reduce12_125 A v hv, reduce12_126 A v hv, reduce12_127 A v hv, reduce12_128 A v hv, reduce12_129 A v hv, reduce12_130 A v hv, reduce12_131 A v hv, reduce12_132 A v hv, reduce12_133 A v hv, reduce12_134 A v hv, reduce12_135 A v hv, reduce12_136 A v hv, reduce12_137 A v hv, reduce12_138 A v hv, reduce12_139 A v hv, reduce12_140 A v hv, reduce12_141 A v hv, reduce12_142 A v hv, reduce12_143 A v hv, reduce12_144 A v hv, reduce12_145 A v hv, reduce12_146 A v hv, reduce12_147 A v hv, reduce12_148 A v hv, reduce12_149 A v hv, reduce12_150 A v hv, reduce12_151 A v hv, reduce12_152 A v hv, reduce12_153 A v hv, reduce12_154 A v hv, reduce12_155 A v hv, reduce12_156 A v hv, reduce12_157 A v hv, reduce12_158 A v hv, reduce12_159 A v hv, reduce12_160 A v hv, reduce12_161 A v hv, reduce12_162 A v hv, reduce12_163 A v hv, reduce12_164 A v hv, reduce12_165 A v hv, reduce12_166 A v hv, reduce12_167 A v hv, reduce12_168 A v hv, reduce12_169 A v hv, reduce12_170 A v hv, reduce12_171 A v hv, reduce12_172 A v hv, reduce12_173 A v hv, reduce12_174 A v hv, reduce12_175 A v hv, reduce12_176 A v hv, reduce12_177 A v hv, reduce12_178 A v hv, reduce12_179 A v hv, reduce12_180 A v hv, reduce12_181 A v hv, reduce12_182 A v hv, reduce12_183 A v hv, reduce12_184 A v hv, reduce12_185 A v hv, reduce12_186 A v hv, reduce12_187 A v hv, reduce12_188 A v hv, reduce12_189 A v hv, reduce12_190 A v hv, reduce12_191 A v hv, reduce12_192 A v hv, reduce12_193 A v hv, reduce12_194 A v hv, reduce12_195 A v hv, reduce12_196 A v hv, reduce12_197 A v hv, reduce12_198 A v hv, reduce12_199 A v hv, reduce12_200 A v hv, reduce12_201 A v hv, reduce12_202 A v hv, reduce12_203 A v hv, reduce12_204 A v hv, reduce12_205 A v hv, reduce12_206 A v hv, reduce12_207 A v hv, reduce12_208 A v hv, reduce12_209 A v hv, reduce12_210 A v hv, reduce12_211 A v hv, reduce12_212 A v hv, reduce12_213 A v hv, reduce12_214 A v hv, reduce12_215 A v hv, reduce12_216 A v hv, reduce12_217 A v hv, reduce12_218 A v hv, reduce12_219 A v hv, reduce12_220 A v hv, reduce12_221 A v hv, reduce12_222 A v hv, reduce12_223 A v hv, reduce12_224 A v hv, reduce12_225 A v hv, reduce12_226 A v hv, reduce12_227 A v hv, reduce12_228 A v hv, reduce12_229 A v hv, reduce12_230 A v hv, reduce12_231 A v hv, reduce12_232 A v hv, reduce12_233 A v hv, reduce12_234 A v hv, reduce12_235 A v hv, reduce12_236 A v hv, reduce12_237 A v hv, reduce12_238 A v hv, reduce12_239 A v hv, reduce12_240 A v hv, reduce12_241 A v hv, reduce12_242 A v hv, reduce12_243 A v hv, reduce12_244 A v hv, reduce12_245 A v hv, reduce12_246 A v hv, reduce12_247 A v hv, reduce12_248 A v hv, reduce12_249 A v hv, reduce12_250 A v hv, reduce12_251 A v hv, reduce12_252 A v hv, reduce12_253 A v hv, reduce12_254 A v hv, reduce12_255 A v hv, reduce12_256 A v hv, reduce12_257 A v hv, reduce12_258 A v hv, reduce12_259 A v hv, reduce12_260 A v hv, reduce12_261 A v hv, reduce12_262 A v hv, reduce12_263 A v hv, reduce12_264 A v hv, reduce12_265 A v hv, reduce12_266 A v hv, reduce12_267 A v hv, reduce12_268 A v hv, reduce12_269 A v hv, reduce12_270 A v hv, reduce12_271 A v hv, reduce12_272 A v hv, reduce12_273 A v hv, reduce12_274 A v hv, reduce12_275 A v hv, reduce12_276 A v hv, reduce12_277 A v hv, reduce12_278 A v hv, reduce12_279 A v hv, reduce12_280 A v hv, reduce12_281 A v hv, reduce12_282 A v hv, reduce12_283 A v hv, reduce12_284 A v hv, reduce12_285 A v hv, reduce12_286 A v hv, reduce12_287 A v hv, reduce12_288 A v hv, reduce12_289 A v hv, reduce12_290 A v hv, reduce12_291 A v hv, reduce12_292 A v hv, reduce12_293 A v hv, reduce12_294 A v hv, reduce12_295 A v hv, reduce12_296 A v hv, reduce12_297 A v hv, reduce12_298 A v hv, reduce12_299 A v hv, reduce12_300 A v hv, reduce12_301 A v hv, reduce12_302 A v hv, reduce12_303 A v hv, reduce12_304 A v hv, reduce12_305 A v hv, reduce12_306 A v hv, reduce12_307 A v hv, reduce12_308 A v hv, reduce12_309 A v hv, reduce12_310 A v hv, reduce12_311 A v hv, reduce12_312 A v hv, reduce12_313 A v hv, reduce12_314 A v hv, reduce12_315 A v hv, reduce12_316 A v hv, reduce12_317 A v hv, reduce12_318 A v hv, reduce12_319 A v hv, reduce12_320 A v hv, reduce12_321 A v hv, reduce12_322 A v hv, reduce12_323 A v hv, reduce12_324 A v hv, reduce12_325 A v hv, reduce12_326 A v hv, reduce12_327 A v hv, reduce12_328 A v hv, reduce12_329 A v hv, reduce12_330 A v hv, reduce12_331 A v hv, reduce12_332 A v hv, reduce12_333 A v hv, reduce12_334 A v hv, reduce12_335 A v hv, reduce12_336 A v hv, reduce12_337 A v hv, reduce12_338 A v hv, reduce12_339 A v hv, reduce12_340 A v hv, reduce12_341 A v hv, reduce12_342 A v hv, reduce12_343 A v hv, reduce12_344 A v hv, reduce12_345 A v hv, reduce12_346 A v hv, reduce12_347 A v hv, reduce12_348 A v hv, reduce12_349 A v hv, reduce12_350 A v hv, reduce12_351 A v hv, reduce12_352 A v hv, reduce12_353 A v hv, reduce12_354 A v hv, reduce12_355 A v hv, reduce12_356 A v hv, reduce12_357 A v hv, reduce12_358 A v hv, reduce12_359 A v hv, reduce12_360 A v hv, reduce12_361 A v hv, reduce12_362 A v hv, reduce12_363 A v hv, reduce12_364 A v hv, reduce12_365 A v hv, reduce12_366 A v hv, reduce12_367 A v hv, reduce12_368 A v hv, reduce12_369 A v hv, reduce12_370 A v hv, reduce12_371 A v hv, reduce12_372 A v hv, reduce12_373 A v hv, reduce12_374 A v hv, reduce12_375 A v hv, reduce12_376 A v hv, reduce12_377 A v hv, reduce12_378 A v hv, reduce12_379 A v hv, reduce12_380 A v hv, reduce12_381 A v hv, reduce12_382 A v hv, reduce12_383 A v hv, reduce12_384 A v hv, reduce12_385 A v hv, reduce12_386 A v hv, reduce12_387 A v hv, reduce12_388 A v hv, reduce12_389 A v hv, reduce12_390 A v hv, reduce12_391 A v hv, reduce12_392 A v hv, reduce12_393 A v hv, reduce12_394 A v hv, reduce12_395 A v hv, reduce12_396 A v hv, reduce12_397 A v hv, reduce12_398 A v hv, reduce12_399 A v hv, reduce12_400 A v hv, reduce12_401 A v hv, reduce12_402 A v hv, reduce12_403 A v hv, reduce12_404 A v hv, reduce12_405 A v hv, reduce12_406 A v hv, reduce12_407 A v hv, reduce12_408 A v hv, reduce12_409 A v hv, reduce12_410 A v hv, reduce12_411 A v hv, reduce12_412 A v hv, reduce12_413 A v hv, reduce12_414 A v hv, reduce12_415 A v hv, reduce12_416 A v hv, reduce12_417 A v hv, reduce12_418 A v hv, reduce12_419 A v hv, reduce12_420 A v hv, reduce12_421 A v hv, reduce12_422 A v hv, reduce12_423 A v hv, reduce12_424 A v hv, reduce12_425 A v hv, reduce12_426 A v hv, reduce12_427 A v hv, reduce12_428 A v hv, reduce12_429 A v hv, reduce12_430 A v hv, reduce12_431 A v hv, reduce12_432 A v hv, reduce12_433 A v hv, reduce12_434 A v hv, reduce12_435 A v hv, reduce12_436 A v hv, reduce12_437 A v hv, reduce12_438 A v hv, reduce12_439 A v hv, reduce12_440 A v hv, reduce12_441 A v hv, reduce12_442 A v hv, reduce12_443 A v hv, reduce12_444 A v hv, reduce12_445 A v hv, reduce12_446 A v hv, reduce12_447 A v hv, reduce12_448 A v hv, reduce12_449 A v hv, reduce12_450 A v hv, reduce12_451 A v hv, reduce12_452 A v hv, reduce12_453 A v hv, reduce12_454 A v hv, reduce12_455 A v hv, reduce12_456 A v hv, reduce12_457 A v hv, reduce12_458 A v hv, reduce12_459 A v hv, reduce12_460 A v hv, reduce12_461 A v hv, reduce12_462 A v hv, reduce12_463 A v hv, reduce12_464 A v hv, reduce12_465 A v hv, reduce12_466 A v hv, reduce12_467 A v hv, reduce12_468 A v hv, reduce12_469 A v hv, reduce12_470 A v hv, reduce12_471 A v hv, reduce12_472 A v hv, reduce12_473 A v hv, reduce12_474 A v hv, reduce12_475 A v hv, reduce12_476 A v hv, reduce12_477 A v hv, reduce12_478 A v hv, reduce12_479 A v hv, reduce12_480 A v hv, reduce12_481 A v hv, reduce12_482 A v hv, reduce12_483 A v hv, reduce12_484 A v hv, reduce12_485 A v hv, reduce12_486 A v hv, reduce12_487 A v hv, reduce12_488 A v hv, reduce12_489 A v hv, reduce12_490 A v hv, reduce12_491 A v hv, reduce12_492 A v hv, reduce12_493 A v hv, reduce12_494 A v hv, reduce12_495 A v hv, reduce12_496 A v hv, reduce12_497 A v hv, reduce12_498 A v hv, reduce12_499 A v hv, reduce12_500 A v hv, reduce12_501 A v hv, reduce12_502 A v hv, reduce12_503 A v hv, reduce12_504 A v hv, reduce12_505 A v hv, reduce12_506 A v hv, reduce12_507 A v hv, reduce12_508 A v hv, reduce12_509 A v hv, reduce12_510 A v hv, reduce12_511 A v hv, reduce12_512 A v hv, reduce12_513 A v hv, reduce12_514 A v hv, reduce12_515 A v hv, reduce12_516 A v hv, reduce12_517 A v hv, reduce12_518 A v hv, reduce12_519 A v hv, reduce12_520 A v hv, reduce12_521 A v hv, reduce12_522 A v hv, reduce12_523 A v hv, reduce12_524 A v hv, reduce12_525 A v hv, reduce12_526 A v hv, reduce12_527 A v hv, reduce12_528 A v hv, reduce12_529 A v hv, reduce12_530 A v hv, reduce12_531 A v hv, reduce12_532 A v hv, reduce12_533 A v hv, reduce12_534 A v hv, reduce12_535 A v hv, reduce12_536 A v hv, reduce12_537 A v hv, reduce12_538 A v hv, reduce12_539 A v hv, reduce12_540 A v hv, reduce12_541 A v hv, reduce12_542 A v hv, reduce12_543 A v hv, reduce12_544 A v hv, reduce12_545 A v hv, reduce12_546 A v hv, reduce12_547 A v hv, reduce12_548 A v hv, reduce12_549 A v hv, reduce12_550 A v hv, reduce12_551 A v hv, reduce12_552 A v hv, reduce12_553 A v hv, reduce12_554 A v hv]
  simp only [pow_one]
  module

set_option maxHeartbeats 2000000 in
/-- The exact operator-valued norm polynomial of the tricritical relation.
The individual adjoint rows have already been reduced from commutators;
this last step only collects their scalar coefficients. -/
theorem tricritical_weight12_polynomial :
    tricriticalAdjoint A.L (tricriticalState A.L v)=(321372476328566880 : ℂ) • ((A.central ^ 1) (v)) + (-1083581144832396000 : ℂ) • ((A.central ^ 2) (v)) + (866474649917232000 : ℂ) • ((A.central ^ 3) (v)) + (36252776782320000 : ℂ) • ((A.central ^ 4) (v)) + (527065804800000 : ℂ) • ((A.central ^ 5) (v)) + (2949120000000 : ℂ) • ((A.central ^ 6) (v)) := by
  simp only [tricriticalAdjoint, tricriticalWords, tricriticalCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, add_zero, tricritical_row_00 A v hv, tricritical_row_01 A v hv, tricritical_row_02 A v hv, tricritical_row_03 A v hv, tricritical_row_04 A v hv, tricritical_row_05 A v hv, tricritical_row_06 A v hv, tricritical_row_07 A v hv, tricritical_row_08 A v hv, tricritical_row_09 A v hv, tricritical_row_10 A v hv, tricritical_row_11 A v hv, tricritical_row_12 A v hv, tricritical_row_13 A v hv, tricritical_row_14 A v hv, tricritical_row_15 A v hv, tricritical_row_16 A v hv, tricritical_row_17 A v hv, tricritical_row_18 A v hv, tricritical_row_19 A v hv, tricritical_row_20 A v hv]
  simp only [pow_one]
  module

end VOA.VirDeformModes
