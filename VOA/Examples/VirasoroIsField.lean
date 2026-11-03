/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroField

/-!
# `Y(ω,z)` is a field

`IsField (YomegaVir c)`: for each state `x`, the modes `Lₘ` annihilate `x` for `m` large.  Proved by
the cyclic structure: `x = a·|0⟩`; commuting `Lₘ` to the right past `a` (via the abstract Virasoro
relation `Lop_bracket`) shifts every mode up past the annihilation threshold of `|0⟩`, and the
central cocycle vanishes.  `⁅Lₘ, x⁆` depends only on the Witt part of `x` (the `C`-part is central).

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra

variable (c : ℂ)

/-- The operator identity `virVacRho ⁅Lₘ, x⁆ z = Lₘ(x·z) − x·(Lₘ z)` (from the Lie hom `virVacRho`). -/
theorem virVacRho_Lbracket (m : ℤ) (x : Virasoro) (z : VirUniv c) :
    virVacRho c ⁅L m, x⁆ z = Lop c m (virVacRho c x z) - virVacRho c x (Lop c m z) := by
  have h := (virVacRho c).map_lie (L m) x
  rw [LieRing.of_associative_ring_bracket] at h
  have := congrArg (fun (T : End ℂ (VirUniv c)) => T z) h
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, Lop] using this

/-- **The `⁅Lₘ, x⁆`-bound**: for `m` large, `⁅Lₘ, x⁆` shifts all `L`-modes of `x` up past the
annihilation threshold `Mz` of `z`, and the central cocycle vanishes, so `virVacRho ⁅Lₘ,x⁆ z = 0`. -/
theorem Lm_bracket_ann (x : Virasoro) (z : VirUniv c) (Mz : ℤ)
    (hz : ∀ m : ℤ, Mz ≤ m → Lop c m z = 0) :
    ∃ M : ℤ, ∀ m : ℤ, M ≤ m → virVacRho c ⁅L m, x⁆ z = 0 := by
  obtain ⟨⟨w, ζ⟩, rfl⟩ := (ofProd gfCocycle).surjective x
  -- the `ζ·C` part is central, so it drops from `⁅Lₘ, ·⁆`; reduce to the Witt part `w`
  suffices h : ∃ M : ℤ, ∀ m : ℤ, M ≤ m → virVacRho c ⁅L m, ofProd gfCocycle (w, 0)⁆ z = 0 by
    obtain ⟨M, hM⟩ := h
    refine ⟨M, fun m hm => ?_⟩
    rw [show ofProd gfCocycle (w, ζ) = ofProd gfCocycle (w, 0) + ζ • C from by
        simp only [C, ← of_smul, ← of_add, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
          Prod.mk_add_mk, add_zero, zero_add],
      lie_add, lie_smul, show ⁅L m, C⁆ = 0 from by rw [← lie_skew, C_central, neg_zero],
      smul_zero, add_zero]
    exact hM m hm
  induction w using Finsupp.induction_linear with
  | zero =>
      refine ⟨0, fun m _ => ?_⟩
      rw [show ofProd gfCocycle ((0 : Witt), (0 : ℂ)) = (0 : Virasoro) from rfl,
        lie_zero, map_zero, LinearMap.zero_apply]
  | add w₁ w₂ h₁ h₂ =>
      obtain ⟨M₁, hM₁⟩ := h₁
      obtain ⟨M₂, hM₂⟩ := h₂
      refine ⟨max M₁ M₂, fun m hm => ?_⟩
      rw [show ofProd gfCocycle (w₁ + w₂, (0 : ℂ))
            = ofProd gfCocycle (w₁, 0) + ofProd gfCocycle (w₂, 0) from by
          rw [← of_add, Prod.mk_add_mk, add_zero],
        lie_add, map_add, LinearMap.add_apply,
        hM₁ m (le_trans (le_max_left _ _) hm), hM₂ m (le_trans (le_max_right _ _) hm), add_zero]
  | single k a =>
      refine ⟨max (Mz - k) (-k + 1), fun m hm => ?_⟩
      have hLk : ofProd gfCocycle (Finsupp.single k a, (0 : ℂ)) = a • L k := by
        rw [L, Witt.gen, ← of_smul, Prod.smul_mk, Finsupp.smul_single, smul_eq_mul, mul_one, smul_zero]
      rw [hLk, lie_smul, virasoro_bracket, map_smul, LinearMap.smul_apply, map_add,
        LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        show virVacRho c (L (m + k)) z = Lop c (m + k) z from rfl,
        hz (m + k) (by omega : Mz ≤ m + k), smul_zero,
        if_neg (by omega : ¬ m + k = 0), map_zero, LinearMap.zero_apply, add_zero, smul_zero]

/-- `U(𝔙𝔦𝔯)`-valued wrapper of `RingQuot.mkAlgHom` — codomain declared as `UVir` (not the raw
`RingQuot`) so the quotient-module smul instances `HSMul UVir (VirUniv c)` resolve for `map_add` /
`add_smul` / `mul_smul` / `algebraMap_smul`. -/
noncomputable def mkU : TensorAlgebra ℂ Virasoro →ₐ[ℂ] UVir := RingQuot.mkAlgHom ℂ (Rel ℂ Virasoro)

/-- Every element of the universal enveloping algebra has a tensor-algebra
representative. This permits induction on tensors when proving eventual
annihilation by sufficiently large positive modes; it asserts spanning
through the quotient, not a PBW independence theorem. -/
theorem mkU_surjective (a : UVir) : ∃ p, mkU p = a :=
  (RingQuot.mkAlgHom_surjective ℂ (Rel ℂ Virasoro)) a

/-- **The combined annihilation bound**: for any `a ∈ U(𝔙𝔦𝔯)` and any `z` whose modes eventually
annihilate, the modes of `a·z` eventually annihilate.  The multiplicative case chains the bound
(`a·(b·z)`), the `ι x` case commutes `Lₘ` past `ι x` via `Lm_bracket_ann`. -/
theorem Lop_ann (a : UVir) (z : VirUniv c) (Mz : ℤ) (hz : ∀ m : ℤ, Mz ≤ m → Lop c m z = 0) :
    ∃ M : ℤ, ∀ m : ℤ, M ≤ m → Lop c m (a • z) = 0 := by
  obtain ⟨p, rfl⟩ := mkU_surjective a
  induction p using TensorAlgebra.induction generalizing z Mz with
  | algebraMap r =>
      refine ⟨Mz, fun m hm => ?_⟩
      rw [AlgHom.commutes, algebraMap_smul UVir, map_smul, hz m hm, smul_zero]
  | ι x =>
      obtain ⟨M', hM'⟩ := Lm_bracket_ann c x z Mz hz
      refine ⟨max Mz M', fun m hm => ?_⟩
      change Lop c m (virVacRho c x z) = 0
      have hb := virVacRho_Lbracket c m x z
      rw [hz m (le_trans (le_max_left _ _) hm), map_zero, sub_zero] at hb
      rw [← hb, hM' m (le_trans (le_max_right _ _) hm)]
  | add p q hp hq =>
      obtain ⟨Mp, hMp⟩ := hp z Mz hz
      obtain ⟨Mq, hMq⟩ := hq z Mz hz
      refine ⟨max Mp Mq, fun m hm => ?_⟩
      rw [map_add, add_smul, map_add, hMp m (le_trans (le_max_left _ _) hm),
        hMq m (le_trans (le_max_right _ _) hm), add_zero]
  | mul p q hp hq =>
      obtain ⟨Mq, hMq⟩ := hq z Mz hz
      obtain ⟨M, hM⟩ := hp (mkU q • z) Mq hMq
      refine ⟨M, fun m hm => ?_⟩
      rw [map_mul, mul_smul]
      exact hM m hm

/-- **`Y(ω,z)` is a field**: the modes `Lₘ` annihilate any state for `m` large (bounded below). -/
theorem YomegaVir_isField : IsField (YomegaVir c) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hvac : ∀ m : ℤ, (-1 : ℤ) ≤ m → Lop c m (vacVec c) = 0 := fun m hm => Lop_vacuum c hm
  obtain ⟨M, hM⟩ := Lop_ann c a (vacVec c) (-1) hvac
  refine ⟨-M - 1, fun t ht => ?_⟩
  rw [YomegaVir_apply]
  have : (Submodule.Quotient.mk a : VirUniv c) = a • vacVec c := by
    rw [vacVec, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  rw [this]
  exact hM (-t - 2) (by omega)

end VOA.VirModule
