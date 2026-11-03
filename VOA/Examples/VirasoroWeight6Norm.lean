/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroWordPairing

/-!
# Actual weight-six singular-word central polynomials

The generator in Notes/certificates/virasoro_weight6.py proposes these finite
normal forms. Lean checks each reduction from the Virasoro commutators. The
center remains an operator throughout, so tangent corrections are retained.
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false
namespace VOA.VirDeformModes
open Module (End)
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable (A : CentralVirasoroData E)

/-- Moving a mode through a power of the central operator preserves the word. -/
theorem vir_central_pow (m : ℤ) (p : ℕ) (x : E) :
    A.L m ((A.central ^ p) x) = (A.central ^ p) (A.L m x) :=
  (LinearMap.congr_fun ((A.central_comm m).pow_left p) x).symm

/-- Nested central powers add their exponents. -/
theorem vir_central_pow_apply (p q : ℕ) (x : E) :
    (A.central ^ p) ((A.central ^ q) x) = (A.central ^ (p+q)) x := by
  rw [pow_add, Module.End.mul_apply]

/-- The four creation words of weight six, ordered by partitions
6, 4+2, 3+3, and 2+2+2. -/
def weight6Words : Fin 4 → List ℤ := ![[-6],[-4,-2],[-3,-3],[-2,-2,-2]]

/-- Integral coefficients of the Ising null relation in this word order. -/
def isingCoefficients : Fin 4 → ℂ := ![-108,-264,93,64]

/-- Integral coefficients of the M(2,7) null relation in this word order. -/
def m27Coefficients : Fin 4 → ℂ := ![-38,-77,-7,49]

/-- A weight-six word combination acting on a supplied vacuum. -/
noncomputable def weight6State (L : ℤ → End ℂ E) (r : Fin 4 → ℂ) (v : E) : E :=
  ∑ i, r i • virWord L (weight6Words i) v

/-- The adjoint combination reverses every word and negates its indices. -/
noncomputable def weight6Adjoint (L : ℤ → End ℂ E) (r : Fin 4 → ℂ) : End ℂ E :=
  ∑ i, r i • virWord L ((weight6Words i).reverse.map Neg.neg)

variable (v : E) (hv : ∀ n : ℤ, -1 ≤ n → A.L n v = 0)
include hv
/-- Commute mode 6 through the creation word [-6].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_000 :
    A.L (6) (A.L (-6) (v)) = (35/2 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the creation word [-2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_001 :
    A.L (6) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_002 :
    A.L (2) (A.L (-2) (v)) = (1/2 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the creation word [-4, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_003 :
    A.L (6) (A.L (-4) (A.L (-2) (v))) = (5 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the creation word [-3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_004 :
    A.L (6) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the creation word [-3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_005 :
    A.L (3) (A.L (-3) (v)) = (2 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the creation word [-3, -3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_006 :
    A.L (6) (A.L (-3) (A.L (-3) (v))) = (18 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the creation word [-2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_007 :
    A.L (4) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the creation word [-2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_008 :
    A.L (6) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the creation word [-2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_009 :
    A.L (4) (A.L (-2) (A.L (-2) (v))) = (3 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 6 through the creation word [-2, -2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_010 :
    A.L (6) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (24 : ℂ) • ((A.central ^ 1) (v)) := by
  rw [vir_push A (6) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the creation word [-6].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_011 :
    A.L (4) (A.L (-6) (v)) = (10 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (4) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the creation word [-2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_012 :
    A.L (0) (A.L (-2) (v)) = (2 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (0) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the creation word [-4, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_013 :
    A.L (4) (A.L (-4) (A.L (-2) (v))) = (16 : ℂ) • (A.L (-2) (v)) + (5 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the creation word [-3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_014 :
    A.L (4) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the creation word [-3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_015 :
    A.L (1) (A.L (-3) (v)) = (4 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the creation word [-3, -3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_016 :
    A.L (4) (A.L (-3) (A.L (-3) (v))) = (28 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (4) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_017 :
    A.L (2) (A.L (-2) (A.L (-2) (v))) = (8 : ℂ) • (A.L (-2) (v)) + (A.central ^ 1) (A.L (-2) (v)) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 4 through the creation word [-2, -2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_018 :
    A.L (4) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (48 : ℂ) • (A.L (-2) (v)) + (9 : ℂ) • ((A.central ^ 1) (A.L (-2) (v))) := by
  rw [vir_push A (4) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the creation word [-6].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_019 :
    A.L (3) (A.L (-6) (v)) = (9 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (3) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the creation word [-2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_020 :
    A.L (3) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the creation word [-2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_021 :
    A.L (-1) (A.L (-2) (v)) = A.L (-3) (v) := by
  rw [vir_push A (-1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the creation word [-4, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_022 :
    A.L (3) (A.L (-4) (A.L (-2) (v))) = (7 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (3) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the creation word [-3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_023 :
    A.L (0) (A.L (-3) (v)) = (3 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (0) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the creation word [-3, -3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_024 :
    A.L (3) (A.L (-3) (A.L (-3) (v))) = (18 : ℂ) • (A.L (-3) (v)) + (4 : ℂ) • ((A.central ^ 1) (A.L (-3) (v))) := by
  rw [vir_push A (3) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the creation word [-2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_025 :
    A.L (1) (A.L (-2) (v)) = 0 := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the creation word [-2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_026 :
    A.L (3) (A.L (-2) (A.L (-2) (v))) = 0 := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 1 through the creation word [-2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_027 :
    A.L (1) (A.L (-2) (A.L (-2) (v))) = (3 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (1) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 3 through the creation word [-2, -2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_028 :
    A.L (3) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (15 : ℂ) • (A.L (-3) (v)) := by
  rw [vir_push A (3) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-6].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_029 :
    A.L (2) (A.L (-6) (v)) = (8 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (2) (-6)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-4, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_030 :
    A.L (2) (A.L (-4) (A.L (-2) (v))) = (6 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (1/2 : ℂ) • ((A.central ^ 1) (A.L (-4) (v))) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_031 :
    A.L (2) (A.L (-3) (v)) = 0 := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode -1 through the creation word [-3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_032 :
    A.L (-1) (A.L (-3) (v)) = (2 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (-1) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv, reduce6_031 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-3, -3].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_033 :
    A.L (2) (A.L (-3) (A.L (-3) (v))) = (10 : ℂ) • (A.L (-4) (v)) := by
  rw [vir_push A (2) (-3)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv, reduce6_031 A v hv, reduce6_032 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 0 through the creation word [-2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_034 :
    A.L (0) (A.L (-2) (A.L (-2) (v))) = (4 : ℂ) • (A.L (-2) (A.L (-2) (v))) := by
  rw [vir_push A (0) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv, reduce6_031 A v hv, reduce6_032 A v hv, reduce6_033 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-2, -2, -2].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_035 :
    A.L (2) (A.L (-2) (A.L (-2) (A.L (-2) (v)))) = (24 : ℂ) • (A.L (-2) (A.L (-2) (v))) + (3/2 : ℂ) • ((A.central ^ 1) (A.L (-2) (A.L (-2) (v)))) := by
  rw [vir_push A (2) (-2)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv, reduce6_031 A v hv, reduce6_032 A v hv, reduce6_033 A v hv, reduce6_034 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Commute mode 2 through the creation word [-4].
The central contribution is retained, and modes at least −1 kill the vacuum. -/
private theorem reduce6_036 :
    A.L (2) (A.L (-4) (v)) = (6 : ℂ) • (A.L (-2) (v)) := by
  rw [vir_push A (2) (-4)]
  norm_num
  all_goals try simp only [map_add, map_smul, map_zero, vir_central_pow, vir_central_pow_apply, pow_zero, Module.End.one_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv, reduce6_031 A v hv, reduce6_032 A v hv, reduce6_033 A v hv, reduce6_034 A v hv, reduce6_035 A v hv]
  all_goals try simp [hv]
  all_goals module

/-- Exact operator-valued norm of the ising word. The displayed polynomial
is computed before substituting a central charge, including its tangent term. -/
theorem ising_weight6_polynomial :
    weight6Adjoint A.L isingCoefficients (weight6State A.L isingCoefficients v) =
      (-83316 : ℂ) • ((A.central ^ 1) (v)) + (165096 : ℂ) • ((A.central ^ 2) (v)) + (3072 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [weight6Adjoint, weight6State, weight6Words, isingCoefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv, reduce6_031 A v hv, reduce6_032 A v hv, reduce6_033 A v hv, reduce6_034 A v hv, reduce6_035 A v hv, reduce6_036 A v hv]
  simp only [pow_one]
  module

/-- Exact operator-valued norm of the m27 word. The displayed polynomial
is computed before substituting a central charge, including its tangent term. -/
theorem m27_weight6_polynomial :
    weight6Adjoint A.L m27Coefficients (weight6State A.L m27Coefficients v) =
      (67830 : ℂ) • ((A.central ^ 1) (v)) + (48951/2 : ℂ) • ((A.central ^ 2) (v)) + (7203/4 : ℂ) • ((A.central ^ 3) (v)) := by
  simp only [weight6Adjoint, weight6State, weight6Words, m27Coefficients,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.reverse_cons, List.reverse_nil, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, neg_neg, virWord, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_add, map_smul, map_zero, add_zero,
    vir_central_pow, vir_central_pow_apply, reduce6_000 A v hv, reduce6_001 A v hv, reduce6_002 A v hv, reduce6_003 A v hv, reduce6_004 A v hv, reduce6_005 A v hv, reduce6_006 A v hv, reduce6_007 A v hv, reduce6_008 A v hv, reduce6_009 A v hv, reduce6_010 A v hv, reduce6_011 A v hv, reduce6_012 A v hv, reduce6_013 A v hv, reduce6_014 A v hv, reduce6_015 A v hv, reduce6_016 A v hv, reduce6_017 A v hv, reduce6_018 A v hv, reduce6_019 A v hv, reduce6_020 A v hv, reduce6_021 A v hv, reduce6_022 A v hv, reduce6_023 A v hv, reduce6_024 A v hv, reduce6_025 A v hv, reduce6_026 A v hv, reduce6_027 A v hv, reduce6_028 A v hv, reduce6_029 A v hv, reduce6_030 A v hv, reduce6_031 A v hv, reduce6_032 A v hv, reduce6_033 A v hv, reduce6_034 A v hv, reduce6_035 A v hv, reduce6_036 A v hv]
  simp only [pow_one]
  module

end VOA.VirDeformModes
