/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AdmissibleVacuumRoot
import VOA.Examples.AffineSl2VacuumSimpleRoot

/-!
# Uniform graded rigidity at negative admissible affine sl2 levels

The actual screening construction and Verma Kac formula, the exact vacuum
sequence and its first Gram coefficient, and admissible label arithmetic
prove a simple vacuum determinant root. The actual two-relation deformation
obstruction then proves rigidity without a remaining representation premise.
-/
namespace VOA.AffineSl2GeneralRigidity
noncomputable section

/-- Every admissible rational shifted level is noncritical. -/
theorem admissible_level_noncritical (p q : ℕ) (hp : 2≤p) (hq : 0<q) :
    (p : ℂ)/q-2+2≠0 := by
  rw [sub_add_cancel]
  exact div_ne_zero (by exact_mod_cast (show p≠0 by omega))
    (by exact_mod_cast (Nat.ne_of_gt hq))

/-- An admissible shifted level `p/q - 2` is nonzero as soon as `p ≠ 2q`
(for coprime labels this excludes only `(p,q) = (2,1)`, i.e. `k = 0`). -/
theorem admissible_level_ne_zero (p q : ℕ) (hq : 0<q) (hne : p ≠ 2*q) :
    (p : ℂ)/q-2≠0 := by
  intro hz
  have hqC : (q : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have he : (p : ℂ)=2*q := (div_eq_iff hqC).mp (sub_eq_zero.mp hz)
  have hn : p=2*q := by exact_mod_cast he
  exact hne hn

/-- A negative admissible level is nonzero; the strict numerator bound
is exactly the requested negative-level restriction. Special case of
`admissible_level_ne_zero`. -/
theorem negative_admissible_level_ne_zero (p q : ℕ) (hq : 0<q) (hneg : p<2*q) :
    (p : ℂ)/q-2≠0 :=
  admissible_level_ne_zero p q hq (by omega)

/-- Every graded first-order deformation of the simple affine sl2 VOA
at any nonzero admissible level `k = p/q - 2` is trivial. Only the numerical
admissibility conditions remain: positive coprime labels, `p ≥ 2`, and
`p ≠ 2q` (i.e. `k ≠ 0`; the sign of `k` plays no role). All singular,
determinant, multiplicity and reconstruction inputs are proved.
(Generalises `negative_admissible_graded_rigidity`.) -/
theorem admissible_graded_rigidity (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (hne : p ≠ 2*q) :
    Deform.IsRigidGraded (simple ((p : ℂ)/q-2) (admissible_level_noncritical p q hp hq)) := by
  obtain ⟨hz,hd⟩ := Wak.Charged.vacuumChevalleyDeterminant_admissible_simple p q hp hq hcop
  exact graded_rigidity_of_vacuum_simple_root _ (admissible_level_noncritical p q hp hq)
    (admissible_level_ne_zero p q hq hne) (q*(p-1)) ((p : ℤ)-1) hz hd

/-- Every graded first-order deformation of the simple affine sl2 VOA
at a negative admissible level (`p < 2q`) is trivial. This is the
negative-level specialisation of `admissible_graded_rigidity`; the bound
`p < 2q` is used only to ensure `k ≠ 0`, and the general theorem needs
only `p ≠ 2q`. -/
theorem negative_admissible_graded_rigidity (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (hneg : p<2*q) :
    Deform.IsRigidGraded (simple ((p : ℂ)/q-2) (admissible_level_noncritical p q hp hq)) :=
  admissible_graded_rigidity p q hp hq hcop (by omega)

end
end VOA.AffineSl2GeneralRigidity
