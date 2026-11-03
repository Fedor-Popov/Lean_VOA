/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroGrading

/-!
# The graded-field structure and VA1 for the Virasoro VOA

The **graded-field predicate** `GradedFieldVir a D` (`a`'s `zʲ`-coefficient shifts conformal grade
by `D + j`), its closure under `+`, `•`, `∂_z`, and normal product `nprod` (mirroring the lattice
`GradedFieldLatGen`), the base case that `Y(ω,z)` is a graded field of weight `2` (each mode
`Lₘ` shifts energy by `−m`), and hence every word field `YwordVir ws` is graded of weight
`energy(ws)`.  This yields **VA1 (`grading_mode`)**: `u₍ₙ₎v ∈ 𝒱_{k+ℓ−n−1}`.

`sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open VOA.Reconstruction

variable (c : ℂ)

/-! ## §1  The graded-field predicate. -/

/-- A **graded field of weight `D`**: the `zʲ`-coefficient `a j` shifts conformal grade by `D + j`
(so the mode `a₍ₙ₎ = a(−n−1)` shifts by `D − n − 1`). -/
def GradedFieldVir (a : FormalDist (End ℂ (VirUniv c))) (D : ℤ) : Prop :=
  ∀ (j q : ℤ) (x : VirUniv c), x ∈ gradingVir c q → a j x ∈ gradingVir c (D + q + j)

/-! ## §2  Modes shift grade: `Lₘ : 𝒱_q → 𝒱_{q−m}`. -/

/-- A creation mode `L₋ᵢ₋₂` raises grade by `i+2` (it prepends a letter to each monomial). -/
theorem Lop_neg_maps_grading (i : ℕ) {q : ℤ} {x : VirUniv c} (hx : x ∈ gradingVir c q) :
    Lop c (-(i : ℤ) - 2) x ∈ gradingVir c (q + ((i : ℤ) + 2)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ws, hen, rfl⟩ := hy
      rw [← negWordVir_cons,
        show q + ((i : ℤ) + 2) = (energyVir (i :: ws) : ℤ) from by
          rw [energyVir_cons]; push_cast; omega]
      exact negWord_mem_gradingVir c (i :: ws)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **A general mode on a monomial** shifts grade by `−m`: `Lₘ · negWordVir ws ∈ 𝒱_{energy ws − m}`
(commute `Lₘ` to the right; the central cocycle only fires when it exactly lands on grade `energy
rest`). -/
theorem Lop_maps_grading_word (m : ℤ) (ws : List ℕ) :
    Lop c m (negWordVir c ws) ∈ gradingVir c ((energyVir ws : ℤ) - m) := by
  induction ws generalizing m with
  | nil =>
      rw [negWordVir_nil, energyVir_nil, Nat.cast_zero, zero_sub]
      rcases lt_or_ge m (-1) with hm | hm
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -(n : ℤ) - 2 := ⟨(-m - 2).toNat, by omega⟩
        have h := negWord_mem_gradingVir c [n]
        rw [negWordVir_cons, negWordVir_nil] at h
        rwa [show (energyVir [n] : ℤ) = -(-(n : ℤ) - 2) from by
          rw [energyVir_cons, energyVir_nil]; push_cast; ring] at h
      · rw [Lop_vacuum c hm]; exact Submodule.zero_mem _
  | cons i rest ih =>
      rw [negWordVir_cons]
      change virVacRho c (L m) (virVacRho c (L (-(i : ℤ) - 2)) (negWordVir c rest)) ∈ _
      rw [virVacRho_comm]
      apply Submodule.add_mem
      · have h1 := Lop_neg_maps_grading c i (ih m)
        rwa [show (energyVir rest : ℤ) - m + ((i : ℤ) + 2) = (energyVir (i :: rest) : ℤ) - m from by
          rw [energyVir_cons]; push_cast; ring] at h1
      · rw [virasoro_bracket, map_add, LinearMap.add_apply]
        apply Submodule.add_mem
        · rw [map_smul, LinearMap.smul_apply]
          refine Submodule.smul_mem _ _ ?_
          have h2 := ih (m + (-(i : ℤ) - 2))
          rwa [show (energyVir rest : ℤ) - (m + (-(i : ℤ) - 2)) = (energyVir (i :: rest) : ℤ) - m from by
            rw [energyVir_cons]; push_cast; ring] at h2
        · split_ifs with hc
          · rw [map_smul, LinearMap.smul_apply, vac_acts_central, LinearMap.smul_apply,
              LinearMap.id_coe, id_eq]
            refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
            have h3 := negWord_mem_gradingVir c rest
            rwa [show (energyVir rest : ℤ) = (energyVir (i :: rest) : ℤ) - m from by
              rw [energyVir_cons]; push_cast; omega] at h3
          · rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- A general mode `Lₘ` maps grade `q` to grade `q − m` (from the monomial case + linearity). -/
theorem Lop_maps_grading (m : ℤ) {q : ℤ} {x : VirUniv c} (hx : x ∈ gradingVir c q) :
    Lop c m x ∈ gradingVir c (q - m) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ws, hen, rfl⟩ := hy
      rw [show (q - m) = (energyVir ws : ℤ) - m from by rw [hen]]
      exact Lop_maps_grading_word c m ws
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-! ## §3  The generator fields are graded; closure of graded fields. -/

/-- **`Y(ω,z)` is a graded field of weight `2`** (its mode `Lₘ` shifts grade by `−m`; the
`zʲ`-coefficient is `L₋ⱼ₋₂`, shifting by `2 + j`). -/
theorem YomegaVir_gradedField : GradedFieldVir c (YomegaVir c) 2 := by
  intro j q x hx
  rw [YomegaVir_apply]
  have := Lop_maps_grading c (-j - 2) hx
  rwa [show q - (-j - 2) = 2 + q + j from by ring] at this

/-- The identity field has weight zero. Its only nonzero coefficient acts by the identity, so it preserves every conformal grade. -/
theorem idFieldVir_gradedField : GradedFieldVir c (idFieldVir c) 0 := by
  intro j q x hx
  rw [idFieldVir]
  by_cases hj : j = 0
  · rw [if_pos hj, hj, LinearMap.id_apply]; rwa [show (0 : ℤ) + q + 0 = q from by ring]
  · rw [if_neg hj, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- Adding two fields of the same weight preserves their common grade-shift rule, since each homogeneous space is closed under addition. -/
theorem GradedFieldVir.add {a b : FormalDist (End ℂ (VirUniv c))} {D : ℤ}
    (ha : GradedFieldVir c a D) (hb : GradedFieldVir c b D) : GradedFieldVir c (a + b) D := by
  intro j q x hx
  change (a j + b j) x ∈ _
  rw [LinearMap.add_apply]; exact Submodule.add_mem _ (ha j q x hx) (hb j q x hx)

/-- Scaling a field preserves its weight and grade shifts. Only the coefficient values change. -/
theorem GradedFieldVir.smul' {a : FormalDist (End ℂ (VirUniv c))} {D : ℤ} (r : ℂ)
    (ha : GradedFieldVir c a D) : GradedFieldVir c (r • a) D := by
  intro j q x hx
  change (r • a j) x ∈ _
  rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ r (ha j q x hx)

/-- Differentiating a formal field raises its conformal weight by one: the coefficient index shifts by one, producing exactly the required extra grade shift. -/
theorem GradedFieldVir.deriv {a : FormalDist (End ℂ (VirUniv c))} {D : ℤ}
    (ha : GradedFieldVir c a D) : GradedFieldVir c (VOA.deriv a) (D + 1) := by
  intro j q x hx
  rw [deriv_apply, ← Int.cast_smul_eq_zsmul ℂ (j + 1), LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have := ha (j + 1) q x hx
  rwa [show D + q + (j + 1) = D + 1 + q + j from by ring] at this

/-- Taking i formal derivatives raises a field of weight D to weight D+i. This iterates the one-derivative grading calculation. -/
theorem GradedFieldVir.deriv_iterate {a : FormalDist (End ℂ (VirUniv c))} {D : ℤ}
    (ha : GradedFieldVir c a D) (i : ℕ) :
    GradedFieldVir c (VOA.deriv^[i] a) (D + i) := by
  induction i with
  | zero => rw [Function.iterate_zero, id]; rwa [Nat.cast_zero, add_zero]
  | succ p ih =>
      rw [Function.iterate_succ', Function.comp_apply]
      have := ih.deriv c
      rwa [show D + (p : ℤ) + 1 = D + ((p : ℤ) + 1) from by ring, ← Nat.cast_succ] at this

/-- A finite-support finsum of submodule elements lies in the submodule. -/
theorem finsum_mem_submodule_vir {ι : Type*} (S : Submodule ℂ (VirUniv c))
    (g : ι → VirUniv c) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- The normal-ordered product of two fields has weight equal to the sum of their weights. Both orders of mode composition have the same total grade shift, and field truncation makes the diagonal sum finite. -/
theorem GradedFieldVir.nprod {a b : FormalDist (End ℂ (VirUniv c))} (haf : IsField a)
    (hbf : IsField b) {Da Db : ℤ} (ha : GradedFieldVir c a Da) (hb : GradedFieldVir c b Db) :
    GradedFieldVir c (VOA.nprod haf hbf) (Da + Db) := by
  intro s q x hx
  rw [nprod_apply]
  refine finsum_mem_submodule_vir c _ _ (normalOrdered_diag_support_finite haf hbf s x)
    (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have hb' := hb (s - m) q x hx
    have ha' := ha m (Db + q + (s - m)) _ hb'
    rwa [show Da + (Db + q + (s - m)) + m = Da + Db + q + s from by ring] at ha'
  · rw [if_neg h0, Module.End.mul_apply]
    have ha' := ha m q x hx
    have hb' := hb (s - m) (Da + q + m) _ ha'
    rwa [show Db + (Da + q + m) + (s - m) = Da + Db + q + s from by ring] at hb'

/-! ## §4  The word fields are graded; VA1. -/

/-- The generator field `genFieldVir i = (i!)⁻¹ ∂^i Y(ω,z)` is a graded field of weight `i + 2`. -/
theorem genFieldVir_gradedField (i : ℕ) : GradedFieldVir c (genFieldVir c i) ((i : ℤ) + 2) := by
  rw [genFieldVir]
  have := ((YomegaVir_gradedField c).deriv_iterate c i).smul' c ((i.factorial : ℂ)⁻¹)
  rwa [show (2 : ℤ) + (i : ℤ) = (i : ℤ) + 2 from by ring] at this

/-- Every word field `YwordVir ws` is a graded field of weight `energy(ws)`. -/
theorem YwordVir_gradedField : ∀ ws : List ℕ, GradedFieldVir c (YwordVir c ws) (energyVir ws : ℤ)
  | [] => by rw [YwordVir_nil, energyVir_nil, Nat.cast_zero]; exact idFieldVir_gradedField c
  | (i :: rest) => by
      rw [YwordVir_cons, energyVir_cons]
      have := GradedFieldVir.nprod c (genFieldVir_isField c i) (YwordVir_isField c rest)
        (genFieldVir_gradedField c i) (YwordVir_gradedField rest)
      rwa [show ((i : ℤ) + 2) + (energyVir rest : ℤ) = (((i + 2) + energyVir rest : ℕ) : ℤ) from by
        push_cast; ring] at this

/-- **VA1 (`grading_mode`)**: for `u ∈ 𝒱ₖ`, `v ∈ 𝒱ₗ`, the product `u₍ₙ₎v` lies in `𝒱_{k+ℓ−n−1}`.
Reduce `u` to a creation monomial (span-induction); then `virYA u = YwordVir ws` is a graded field
of weight `k = energy(ws)`, so `u₍ₙ₎v = (YwordVir ws)(−n−1) v ∈ 𝒱_{k+ℓ−n−1}`. -/
theorem virYA_grading_mode {k ℓ : ℤ} (u : VirUniv c) (hu : u ∈ gradingVir c k) (v : VirUniv c)
    (hv : v ∈ gradingVir c ℓ) (n : ℤ) :
    mode (virYA c u) n v ∈ gradingVir c (k + ℓ - n - 1) := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ws, hen, rfl⟩ := hy
      rw [mode_apply, virYA_word]
      have := YwordVir_gradedField c ws (-n - 1) ℓ v hv
      rwa [show (energyVir ws : ℤ) + ℓ + (-n - 1) = k + ℓ - n - 1 from by rw [hen]; ring] at this
  | zero => rw [map_zero, mode_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
      rw [map_add, mode_add, LinearMap.add_apply]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
      rw [map_smul, mode_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ r ha

end VOA.VirModule
