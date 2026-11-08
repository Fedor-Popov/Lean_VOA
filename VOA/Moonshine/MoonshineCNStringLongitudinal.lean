/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStringGrading
import Mathlib.Tactic.LinearCombination

/-! # The longitudinal spurious splitting

The lower bound on weights is used in the strong induction proving `S_K ≤ S ⊔ (K ⊓ S_K)`.
This is a consequence of the light-cone splitting, not a further decomposition assumption.
-/

namespace VOA.Moonshine.ConwayNorton.StringModule

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

theorem lightConeSplit_decompose_weight (hF : M.LightConeSplit) (N : ℤ)
    (x : H) (hx : x ∈ M.wt N) :
    ∃ s ∈ M.spurious, ∃ k ∈ M.kVacuum, s ∈ M.wt N ∧ k ∈ M.wt N ∧ s + k = x := by
  have h := (M.lightConeSplit_weight hF N).sup_eq_top
  obtain ⟨s, hs, k, hk, he⟩ := Submodule.mem_sup.mp
    (show (⟨x, hx⟩ : M.wt N) ∈ M.weightSlice M.spurious N ⊔ M.weightSlice M.kVacuum N by
      rw [h]; trivial)
  exact ⟨s, hs, k, hk, s.property, k.property, congrArg Subtype.val he⟩

/-- Moving a negative longitudinal operator past a negative Virasoro operator. -/
theorem negative_K_negative_L (m n : ℕ) (x : H) :
    M.K (-(m + 1 : ℤ)) (M.L (-(n + 1 : ℤ)) x) =
      M.L (-(n + 1 : ℤ)) (M.K (-(m + 1 : ℤ)) x) -
        (m + 1 : ℂ) • M.K (-(↑(m + n + 1) + 1 : ℤ)) x := by
  have h := M.LK_comm_apply (-(n + 1 : ℤ)) (-(m + 1 : ℤ)) (by omega) (by omega) x
  rw [show -(n + 1 : ℤ) + -(m + 1 : ℤ) = -(↑(m + n + 1) + 1 : ℤ) by omega] at h
  push_cast at h ⊢
  linear_combination (norm := module) -h

/-- The induction behind the longitudinal splitting, on a homogeneous source. -/
theorem kSpurious_negative_mem_split (hF : M.LightConeSplit) (N : ℤ)
    (x : H) (hx : x ∈ M.wt N) (m : ℕ) :
    M.K (-(m + 1 : ℤ)) x ∈ M.spurious ⊔ (M.kVacuum ⊓ M.kSpurious) := by
  let U := M.spurious ⊔ (M.kVacuum ⊓ M.kSpurious)
  obtain ⟨N₀, hN₀⟩ := M.wt_bdd
  have below : ∀ Q < N₀, ∀ y ∈ M.wt Q, ∀ j : ℕ, M.K (-(j + 1 : ℤ)) y ∈ U := by
    intro Q hQ y hy j
    rw [hN₀ Q hQ, Submodule.mem_bot] at hy
    rw [hy, map_zero]
    exact U.zero_mem
  have step : ∀ d : ℕ, ∀ Q : ℤ, (Q - N₀).toNat = d → ∀ y ∈ M.wt Q,
      ∀ j : ℕ, M.K (-(j + 1 : ℤ)) y ∈ U := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hd y hy j
      by_cases hQ : Q < N₀
      · exact below Q hQ y hy j
      have lower : ∀ R < Q, ∀ z ∈ M.wt R, ∀ i : ℕ, M.K (-(i + 1 : ℤ)) z ∈ U := by
        intro R hR z hz i
        by_cases hR₀ : R < N₀
        · exact below R hR₀ z hz i
        · exact ih (R - N₀).toNat (by omega) R rfl z hz i
      obtain ⟨s, hs, k, hk, hsw, hkw, he⟩ := M.lightConeSplit_decompose_weight hF Q y hy
      obtain ⟨a, ha, b, hb, hab⟩ := M.spurious_weight_two Q s hs hsw
      have image : ∀ (n : ℕ) z, z ∈ M.wt (Q - (n + 1)) →
          M.K (-(j + 1 : ℤ)) (M.L (-(n + 1 : ℤ)) z) ∈ U := by
        intro n z hz
        rw [M.negative_K_negative_L]
        exact U.sub_mem
          ((show M.spurious ≤ U from le_sup_left) (M.negative_L_mem_spurious n _))
          (U.smul_mem _ (lower (Q - (n + 1)) (by omega) z hz (j + n + 1)))
      have hka : M.K (-(j + 1 : ℤ)) (M.L (-1) a) ∈ U := image 0 a ha
      have hkb : M.K (-(j + 1 : ℤ)) (M.L (-2) b) ∈ U := image 1 b hb
      have hkk : M.K (-(j + 1 : ℤ)) k ∈ U :=
        (show M.kVacuum ⊓ M.kSpurious ≤ U from le_sup_right)
          ⟨M.kVacuum_K_stable _ k hk, M.negative_K_mem_kSpurious j k⟩
      rw [← he, ← hab, map_add, map_add]
      exact U.add_mem (U.add_mem hka hkb) hkk
  exact step (N - N₀).toNat N rfl x hx m

/-- The global inclusion `S_K ≤ S ⊔ (K ⊓ S_K)`, at every central charge. -/
theorem kSpurious_le_spurious_sup (hF : M.LightConeSplit) :
    M.kSpurious ≤ M.spurious ⊔ (M.kVacuum ⊓ M.kSpurious) := by
  apply iSup_le
  intro m
  rintro _ ⟨x, rfl⟩
  let U := M.spurious ⊔ (M.kVacuum ⊓ M.kSpurious)
  induction x using DirectSum.Decomposition.inductionOn M.wt with
  | zero => simpa only [map_zero] using U.zero_mem
  | homogeneous x => exact M.kSpurious_negative_mem_split hF _ x x.property m
  | add x y hx hy => simpa only [map_add] using U.add_mem hx hy

/-- The two intersections `S_K ⊓ S` and `S_K ⊓ K` span the longitudinal spurious subspace. -/
theorem kSpurious_eq_intersections_sup (hF : M.LightConeSplit) :
    M.kSpurious = (M.kSpurious ⊓ M.spurious) ⊔ (M.kSpurious ⊓ M.kVacuum) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, k, hk, he⟩ := Submodule.mem_sup.mp (M.kSpurious_le_spurious_sup hF hx)
    have hsk : s ∈ M.kSpurious := by
      have hsub := M.kSpurious.sub_mem hx hk.2
      rw [← he, add_sub_cancel_right] at hsub
      exact hsub
    exact Submodule.mem_sup.mpr ⟨s, ⟨hsk, hs⟩, k, ⟨hk.2, hk.1⟩, he⟩
  · exact sup_le inf_le_left inf_le_left

end VOA.Moonshine.ConwayNorton.StringModule
