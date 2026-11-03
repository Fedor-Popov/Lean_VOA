/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ZhuGenGround
import VOA.Moonshine.GroundLatticeCoord

/-!
# The ground-state lattice residual `GroundLattice` is a theorem

`ZhuGenGround.lean` reduced the ground-state part of the Zhu-generation residual R-gen to the
lattice statement `GroundLattice`: every `x_γ = e^γ + e^{-γ}`, `γ ∈ Λ₀`, `|γ|² ≥ 6`, lies in the
span of the ground relations `GroundRel (½|γ|²)`.  `GroundLatticeCoord.lean` proves the Golay
coordinate form `GroundLat.groundLatticeA`.  Here it is transported along the isometry
`lambda0Equiv : A ≃ Λ₀` (`A = Leech.subA`, `⟨x,y⟩ = x·y/2`):

* `GroundLat.Direct g` gives a single ground relation `x_γ` (`groundRel_of_direct`);
* `GroundLat.ZeroRel u v` gives the relation `x_u + x_v` (`groundRel_of_zeroRel`), and
  `|u|² = |v|²` (`halfNorm_of_zeroRel`);
* a triangle `u → u' → u'' → u` gives
  `x_u = ½[(x_u + x_{u'}) − (x_{u'} + x_{u''}) + (x_{u''} + x_u)]`.

## Main results
* `groundLattice : GroundLattice`.
* `zhuGenerated_weightTwo_of_fock_excited : FockSpanned → ExcitedSpanned →
  ZhuGenerated weightTwo` (R-gen rests on the two Fock-space residuals only).

## Status
`sorry`-free, no project axiom.  Imported by the umbrella `VOA/Moonshine.lean`.
-/

namespace VOA.Moonshine.SigmaExist

open VOA VOA.Moonshine VOA.Moonshine.ZhuGen LatGen IntegralLattice HeisenbergN
open Submodule

/-- `A → Λ₀ ⊆ Λ`, `a ↦ 2a`. -/
noncomputable def iotaA (a : ↥Leech.subA) : leech.carrier := (lambda0Equiv a : leech.carrier)

theorem iotaA_mem (a : ↥Leech.subA) : iotaA a ∈ lambda0 := (lambda0Equiv a).2

theorem iotaA_add (a b : ↥Leech.subA) : iotaA (a + b) = iotaA a + iotaA b := by
  simp [iotaA, map_add]

theorem iotaA_sub (a b : ↥Leech.subA) : iotaA (a - b) = iotaA a - iotaA b := by
  simp [iotaA, map_sub]

theorem iotaA_form (a b : ↥Leech.subA) :
    leech.form (iotaA a) (iotaA b) = ((a : Fin 24 → ℤ) ⬝ᵥ (b : Fin 24 → ℤ)) / 2 :=
  lambda0Equiv_form a b

theorem iotaA_ne_zero {a : ↥Leech.subA} (h : (a : Fin 24 → ℤ) ≠ 0) : iotaA a ≠ 0 := by
  intro h0
  apply h
  have : lambda0Equiv a = 0 := Subtype.ext h0
  rw [LinearEquiv.map_eq_zero_iff] at this
  rw [this]
  rfl

theorem x0_congr {β β' : leech.carrier} (h : β = β') (hβ : β ∈ lambda0) (hβ' : β' ∈ lambda0) :
    x0 hβ = x0 hβ' := by
  subst h; rfl

/-- `x_{ι a}` for `a ∈ A`. -/
noncomputable def xA (a : ↥Leech.subA) : V0Sub.carrier := x0 (iotaA_mem a)

theorem groundRel_of_direct {u : ↥Leech.subA} (h : GroundLat.Direct (u : Fin 24 → ℤ)) :
    xA u ∈ GroundRel (LatGen.halfNorm leech (iotaA u)) := by
  obtain ⟨a, ha, ha0, hb0, hk⟩ := h
  set A : ↥Leech.subA := ⟨a, ha⟩
  set B : ↥Leech.subA := ⟨(u : Fin 24 → ℤ) - a, Leech.subA.sub_mem u.2 ha⟩
  have hAB : A + B = u := Subtype.ext (by simp [A, B])
  have hsum : iotaA A + iotaA B = iotaA u := by rw [← iotaA_add, hAB]
  refine ⟨iotaA A, iotaA B, iotaA_mem A, iotaA_mem B, iotaA_ne_zero ha0, iotaA_ne_zero hb0,
    by rw [hsum], Or.inl ⟨?_, x0_congr hsum.symm _ _⟩⟩
  rw [iotaA_form]
  change a ⬝ᵥ ((u : Fin 24 → ℤ) - a) / 2 = -1 ∨ 1 ≤ a ⬝ᵥ ((u : Fin 24 → ℤ) - a) / 2
  omega

theorem zeroRel_mem {u v : Fin 24 → ℤ} (h : GroundLat.ZeroRel u v) :
    u ∈ Leech.subA ∧ v ∈ Leech.subA := by
  obtain ⟨a, ha, b, hb, -, -, -, rfl, rfl⟩ := h
  exact ⟨Leech.subA.add_mem ha hb, Leech.subA.sub_mem ha hb⟩

theorem groundRel_of_zeroRel {u v : ↥Leech.subA}
    (h : GroundLat.ZeroRel (u : Fin 24 → ℤ) (v : Fin 24 → ℤ)) :
    xA u + xA v ∈ GroundRel (LatGen.halfNorm leech (iotaA u)) := by
  obtain ⟨a, ha, b, hb, ha0, hb0, hab, hsum, hdiff⟩ := h
  set A : ↥Leech.subA := ⟨a, ha⟩
  set B : ↥Leech.subA := ⟨b, hb⟩
  have hs : iotaA A + iotaA B = iotaA u := by
    rw [← iotaA_add]; congr 1; exact Subtype.ext hsum
  have hd : iotaA A - iotaA B = iotaA v := by
    rw [← iotaA_sub]; congr 1; exact Subtype.ext hdiff
  refine ⟨iotaA A, iotaA B, iotaA_mem A, iotaA_mem B, iotaA_ne_zero ha0, iotaA_ne_zero hb0,
    by rw [hs], Or.inr ⟨?_, ?_⟩⟩
  · rw [iotaA_form]
    change a ⬝ᵥ b / 2 = 0
    rw [hab]; rfl
  · rw [xA, xA, x0_congr hs.symm (iotaA_mem u), x0_congr hd.symm (iotaA_mem v)]

theorem halfNorm_of_zeroRel {u v : ↥Leech.subA}
    (h : GroundLat.ZeroRel (u : Fin 24 → ℤ) (v : Fin 24 → ℤ)) :
    LatGen.halfNorm leech (iotaA v) = LatGen.halfNorm leech (iotaA u) := by
  obtain ⟨a, ha, b, hb, -, -, hab, hsum, hdiff⟩ := h
  have hba : b ⬝ᵥ a = 0 := by rw [dotProduct_comm, hab]
  have hvv : (v : Fin 24 → ℤ) ⬝ᵥ (v : Fin 24 → ℤ) = (u : Fin 24 → ℤ) ⬝ᵥ (u : Fin 24 → ℤ) := by
    rw [← hsum, ← hdiff]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, hab, hba]
    ring
  simp only [LatGen.halfNorm, iotaA_form, hvv]

/-- **The ground-state lattice residual holds.** -/
theorem groundLattice : GroundLattice := by
  intro γ hγ h6
  set u : ↥Leech.subA := lambda0Equiv.symm ⟨γ, hγ⟩
  have hu : iotaA u = γ := by simp [iotaA, u]
  have h12 : 12 ≤ (u : Fin 24 → ℤ) ⬝ᵥ (u : Fin 24 → ℤ) := by
    have h1 := iotaA_form u u
    rw [hu] at h1
    have := Leech.two_dvd_dot_subA u.2 u.2
    omega
  have key : xA u ∈ span ℂ (GroundRel (LatGen.halfNorm leech (iotaA u))) := by
    rcases GroundLat.groundLatticeA u u.2 h12 with hd | ⟨g', g'', h1, h2, h3⟩
    · exact subset_span (groundRel_of_direct hd)
    · set U' : ↥Leech.subA := ⟨g', (zeroRel_mem h1).2⟩
      set U'' : ↥Leech.subA := ⟨g'', (zeroRel_mem h2).2⟩
      have r1 := groundRel_of_zeroRel (u := u) (v := U') h1
      have r2 := groundRel_of_zeroRel (u := U') (v := U'') h2
      have r3 := groundRel_of_zeroRel (u := U'') (v := u) h3
      have n1 := halfNorm_of_zeroRel (u := u) (v := U') h1
      have n2 := halfNorm_of_zeroRel (u := U') (v := U'') h2
      rw [n1] at r2
      rw [n2, n1] at r3
      have hcomb : xA u = (1 / 2 : ℂ) • ((xA u + xA U') - (xA U' + xA U'') + (xA U'' + xA u)) := by
        module
      rw [hcomb]
      exact smul_mem _ _ (add_mem (sub_mem (subset_span r1) (subset_span r2)) (subset_span r3))
  have e : x0 hγ = xA u := x0_congr hu.symm hγ (iotaA_mem u)
  rw [e]
  rwa [hu] at key

/-- **R-gen from the two Fock-space residuals.** -/
theorem zhuGenerated_weightTwo_of_fock_excited (hF : FockSpanned) (hE : ExcitedSpanned) :
    ZhuGenerated weightTwo :=
  zhuGenerated_weightTwo_of_residuals hF hE groundLattice

end VOA.Moonshine.SigmaExist
