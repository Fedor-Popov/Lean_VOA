/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Lattice.Defs
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Sublattices

A `ℤ`-submodule of an integral lattice, with the restricted form, is again an integral lattice.
This file provides that constructor together with the three notions that the gluing theory of
§3.3 rests on: **primitive** (saturated) sublattices, the **saturation** of a sublattice, and the
**orthogonal complement**.

## Main definitions

* `IntegralLattice.ofSubmodule` — a submodule as a lattice.
* `IntegralLattice.IsPrimitive` — `Γ/N` is torsion free.
* `IntegralLattice.saturation` — the smallest primitive submodule containing `N`.
* `IntegralLattice.orthComp` — the orthogonal complement `N^⊥ ⊆ Γ`.

## References

Ebeling, *Lattices and Codes*, 3rd ed., §1.1 and §3.3.
-/

namespace IntegralLattice

variable (Γ : IntegralLattice)

/-! ### Submodules as lattices -/

/-- A `ℤ`-submodule of `Γ`, with the restricted form, is an integral lattice. -/
def ofSubmodule (N : Submodule ℤ Γ) : IntegralLattice where
  carrier := ↥N
  bilin := Γ.bilin.compl₁₂ N.subtype N.subtype
  bilin_symm _ _ := Γ.bilin_symm _ _

@[simp] theorem ofSubmodule_bilin (N : Submodule ℤ Γ) (x y : N) :
    (Γ.ofSubmodule N).bilin x y = Γ.bilin x y := rfl

theorem isEven_ofSubmodule {N : Submodule ℤ Γ} (h : Γ.IsEven) : (Γ.ofSubmodule N).IsEven := by
  show ∀ x : N, (2 : ℤ) ∣ Γ.bilin (x : Γ) (x : Γ)
  exact fun x => h (x : Γ)

theorem isPosDef_ofSubmodule {N : Submodule ℤ Γ} (h : Γ.IsPosDef) :
    (Γ.ofSubmodule N).IsPosDef := by
  show ∀ x : N, x ≠ 0 → 0 < Γ.bilin (x : Γ) (x : Γ)
  intro x hx
  exact h (x : Γ) fun hc => hx (Subtype.ext hc)

theorem rank_ofSubmodule_le (N : Submodule ℤ Γ) : (Γ.ofSubmodule N).rank ≤ Γ.rank :=
  Submodule.finrank_le N

/-! ### Primitive sublattices and saturation -/

/-- A submodule `N ≤ Γ` is **primitive** (equivalently: saturated) when `Γ/N` is torsion free:
if a nonzero multiple of `x` lies in `N` then so does `x`. -/
def IsPrimitive (N : Submodule ℤ Γ) : Prop :=
  ∀ (m : ℤ) (x : Γ), m ≠ 0 → m • x ∈ N → x ∈ N

/-- The **saturation** of a submodule: the vectors some nonzero multiple of which lies in `N`. -/
def saturation (N : Submodule ℤ Γ) : Submodule ℤ Γ where
  carrier := {x | ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ N}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨k, hk, hb⟩
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    have hexp : (m * k) • (a + b) = k • (m • a) + m • (k • b) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm k m]
    rw [hexp]
    exact N.add_mem (N.smul_mem k ha) (N.smul_mem m hb)
  smul_mem' := by
    rintro c a ⟨m, hm, ha⟩
    exact ⟨m, hm, by rw [smul_comm]; exact N.smul_mem c ha⟩

@[simp] theorem mem_saturation {N : Submodule ℤ Γ} {x : Γ} :
    x ∈ Γ.saturation N ↔ ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ N := Iff.rfl

theorem le_saturation (N : Submodule ℤ Γ) : N ≤ Γ.saturation N :=
  fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩

theorem saturation_isPrimitive (N : Submodule ℤ Γ) : Γ.IsPrimitive (Γ.saturation N) := by
  rintro m x hm ⟨k, hk, hkx⟩
  refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
  rwa [mul_smul]

theorem IsPrimitive.saturation_eq {N : Submodule ℤ Γ} (h : Γ.IsPrimitive N) :
    Γ.saturation N = N := by
  refine le_antisymm ?_ (Γ.le_saturation N)
  rintro x ⟨m, hm, hmx⟩
  exact h m x hm hmx

theorem saturation_mono {N P : Submodule ℤ Γ} (h : N ≤ P) : Γ.saturation N ≤ Γ.saturation P := by
  rintro x ⟨m, hm, hmx⟩
  exact ⟨m, hm, h hmx⟩

/-! ### Orthogonal complements -/

/-- The **orthogonal complement** of a submodule inside `Γ`. -/
def orthComp (N : Submodule ℤ Γ) : Submodule ℤ Γ where
  carrier := {x | ∀ y ∈ N, Γ.bilin x y = 0}
  zero_mem' := by intro y _; simp
  add_mem' := by
    intro a b ha hb y hy
    rw [bilin_add_left, ha y hy, hb y hy, add_zero]
  smul_mem' := by
    intro c a ha y hy
    rw [bilin_smul_left, ha y hy, mul_zero]

@[simp] theorem mem_orthComp {N : Submodule ℤ Γ} {x : Γ} :
    x ∈ Γ.orthComp N ↔ ∀ y ∈ N, Γ.bilin x y = 0 := Iff.rfl

theorem orthComp_antitone {N P : Submodule ℤ Γ} (h : N ≤ P) : Γ.orthComp P ≤ Γ.orthComp N :=
  fun _ hx y hy => hx y (h hy)

theorem le_orthComp_orthComp (N : Submodule ℤ Γ) : N ≤ Γ.orthComp (Γ.orthComp N) := by
  intro x hx y hy
  rw [Γ.bilin_symm]
  exact hy x hx

/-- Orthogonal complements are always primitive. -/
theorem orthComp_isPrimitive (N : Submodule ℤ Γ) : Γ.IsPrimitive (Γ.orthComp N) := by
  intro m x hm hmx y hy
  have h := hmx y hy
  rw [bilin_smul_left] at h
  exact (mul_eq_zero.mp h).resolve_left hm

theorem saturation_orthComp (N : Submodule ℤ Γ) :
    Γ.saturation (Γ.orthComp N) = Γ.orthComp N :=
  (Γ.orthComp_isPrimitive N).saturation_eq

/-- In a positive definite lattice a submodule meets its orthogonal complement only in `0`. -/
theorem inf_orthComp_eq_bot (h : Γ.IsPosDef) (N : Submodule ℤ Γ) :
    N ⊓ Γ.orthComp N = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro x ⟨hxN, hxO⟩
  have : normSq x = 0 := hxO x hxN
  simpa using h.normSq_eq_zero_iff.mp this

end IntegralLattice
