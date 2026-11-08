/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenSugawaraTmul
import VOA.Examples.LatticeBackgroundChargeA
import VOA.Examples.LatticeGenInstance

/-!
# Zero modes of the quadratic states `h_a(−1)h_b(−1)𝟙` on a lattice VOA
(Aut(V♮) campaign, step 3, route C, node C1 of `Notes/MONSTER_AUT_PLAN.md`)

For an even positive-definite lattice `L` and two orthonormal frame directions `a, b`, the state
`q_ab = h_a(−1)h_b(−1)𝟙` (`quadState a b`) has vertex operator `:α^a(z) α^b(z):`.  Its zero mode
`o(q_ab) = q_ab₍₁₎` acts on a charged Fock state as

  `o(q_ab)(p ⊗ e^γ) = (γ_a γ_b) · p ⊗ e^γ + N_ab(p) ⊗ e^γ`,

where `γ_a = chargeCoord γ a` and `N_ab` is the charge-independent Fock operator
`nprod (α^a) (α^b) (−2)` (on `FockN`, `Σ_{k ≥ 0} (k+1)(X_{k,a} ∂_{k,b} + X_{k,b} ∂_{k,a})`).
The momentum cross terms `γ_b·α^a_0 + γ_a·α^b_0` vanish because the Fock zero mode `α^a_0` is `0`.

This file generalises the single-direction Sugawara split of `LatticeGenSugawaraTmul` to two
directions `a, b`.

## Main results
* `nprod_alphaLatGen_tmul₂` — `nprod (α^a) (α^b) s` on `q ⊗ e^γ`, every `s`.
* `quadState`, `YfullGen_quadState` — `Y(q_ab) = nprod (α^a) (α^b)`.
* ⭐ `smul_quadState_one` — the zero-mode formula above.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §1  The three momentum cross terms for two directions -/

theorem nprod_lift_ZfGen₂ (a b : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (liftFGen_currentN_isField L a) (ZfGen_isField L b) s (mkEα L γ q)
      = chargeCoord L γ b • mkEα L γ (currentN (rank L) 1 a (s + 1) q) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ s + 1 →
      normalOrdered (liftFGen L (currentN (rank L) 1 a)) (ZfGen L b) m (s - m) (mkEα L γ q) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : ZfGen L b (s - m) = 0 := by
      show (if s - m = -1 then zGradeOpGen L b else 0) = 0; rw [if_neg (by omega)]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m) * ZfGen L b (s - m)) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
    · rw [if_neg h0]
      change (ZfGen L b (s - m) * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
  have hZss : ZfGen L b (s - (s + 1)) = zGradeOpGen L b := by
    show (if s - (s + 1) = -1 then zGradeOpGen L b else 0) = zGradeOpGen L b; rw [if_pos (by ring)]
  rw [finsum_eq_single _ (s + 1) hsupp, normalOrdered_apply, hZss]
  by_cases h0 : 0 ≤ s + 1
  · rw [if_pos h0]
    change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)) * zGradeOpGen L b)
      (mkEα L γ q) = _
    rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, zGradeOpGen_latStateGen,
      map_smul]
    change chargeCoord L γ b • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
      (q ⊗ₜ[ℂ] eGen L γ) = _
    rw [LinearMap.rTensor_tmul]; rfl
  · rw [if_neg h0]
    change (zGradeOpGen L b * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
      (mkEα L γ q) = _
    rw [Module.End.mul_apply]
    change zGradeOpGen L b (latStateGen L (currentN (rank L) 1 a (s + 1) q) γ) = _
    rw [zGradeOpGen_latStateGen]; rfl

theorem nprod_ZfGen_lift₂ (a b : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (ZfGen_isField L a) (liftFGen_currentN_isField L b) s (mkEα L γ q)
      = chargeCoord L γ a • mkEα L γ (currentN (rank L) 1 b (s + 1) q) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ -1 →
      normalOrdered (ZfGen L a) (liftFGen L (currentN (rank L) 1 b)) m (s - m) (mkEα L γ q) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : ZfGen L a m = 0 := by
      show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg hm]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      change (ZfGen L a m * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b (s - m))) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]
      change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b (s - m)) * ZfGen L a m) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
  have hZm1 : ZfGen L a (-1) = zGradeOpGen L a := by
    show (if (-1 : ℤ) = -1 then zGradeOpGen L a else 0) = zGradeOpGen L a; rw [if_pos rfl]
  rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
    hZm1]
  change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b (s - -1)) * zGradeOpGen L a)
    (mkEα L γ q) = _
  rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, zGradeOpGen_latStateGen,
    map_smul, show s - -1 = s + 1 from by ring]
  change chargeCoord L γ a • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b (s + 1)))
    (q ⊗ₜ[ℂ] eGen L γ) = _
  rw [LinearMap.rTensor_tmul]; rfl

theorem nprod_ZfGen_ZfGen₂ (a b : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (ZfGen_isField L a) (ZfGen_isField L b) s (mkEα L γ q)
      = if s = -2 then (chargeCoord L γ a * chargeCoord L γ b) • mkEα L γ q else 0 := by
  rw [nprod_apply]
  by_cases hs : s = -2
  · have hsupp : ∀ m : ℤ, m ≠ -1 →
        normalOrdered (ZfGen L a) (ZfGen L b) m (s - m) (mkEα L γ q) = 0 := by
      intro m hm
      rw [normalOrdered_apply]
      have hZ : ZfGen L a m = 0 := by
        show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg hm]
      by_cases h0 : 0 ≤ m
      · rw [if_pos h0]; change (ZfGen L a m * ZfGen L b (s - m)) _ = 0
        rw [hZ, zero_mul, LinearMap.zero_apply]
      · rw [if_neg h0]; change (ZfGen L b (s - m) * ZfGen L a m) _ = 0
        rw [hZ, mul_zero, LinearMap.zero_apply]
    have hZm1 : ZfGen L a (-1) = zGradeOpGen L a := by
      show (if (-1 : ℤ) = -1 then zGradeOpGen L a else 0) = zGradeOpGen L a; rw [if_pos rfl]
    have hZsm : ZfGen L b (s - -1) = zGradeOpGen L b := by
      show (if s - -1 = -1 then zGradeOpGen L b else 0) = zGradeOpGen L b; rw [if_pos (by omega)]
    rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
      hZm1, hZsm, if_pos hs]
    change (zGradeOpGen L b * zGradeOpGen L a) (mkEα L γ q) = _
    rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, zGradeOpGen_latStateGen,
      map_smul, zGradeOpGen_latStateGen, smul_smul, mul_comm]
  · rw [if_neg hs]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      have hZ : ZfGen L a m = 0 := by
        show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg (by omega)]
      change (ZfGen L a m * ZfGen L b (s - m)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]
      by_cases hm1 : m = -1
      · subst hm1
        have hZ : ZfGen L b (s - -1) = 0 := by
          show (if s - -1 = -1 then zGradeOpGen L b else 0) = 0; rw [if_neg (by omega)]
        change (ZfGen L b (s - -1) * ZfGen L a (-1)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
      · have hZ : ZfGen L a m = 0 := by
          show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg hm1]
        change (ZfGen L b (s - m) * ZfGen L a m) _ = 0; rw [hZ, mul_zero, LinearMap.zero_apply]

theorem nprod_lift_lift_tmul₂ (a b : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (liftFGen_currentN_isField L a) (liftFGen_currentN_isField L b) s (mkEα L γ q)
      = mkEα L γ (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b) s q) := by
  have heq : nprod (liftFGen_currentN_isField L a) (liftFGen_currentN_isField L b)
      = liftFGen L (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b)) :=
    liftFGen_nprod L (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b)
  rw [heq]
  show LinearMap.rTensor (L.carrier →₀ ℂ)
      (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b) s) (q ⊗ₜ[ℂ] eGen L γ) = _
  rw [LinearMap.rTensor_tmul]; rfl

/-! ## §2  The two-direction split -/

/-- `nprod (α^a) (α^b) s` on a basis state `q ⊗ e^γ`. -/
theorem nprod_alphaLatGen_tmul₂ (a b : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (alphaLatGen_isField L a) (alphaLatGen_isField L b) s (mkEα L γ q)
      = mkEα L γ (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b) s q)
        + chargeCoord L γ b • mkEα L γ (currentN (rank L) 1 a (s + 1) q)
        + chargeCoord L γ a • mkEα L γ (currentN (rank L) 1 b (s + 1) q)
        + (if s = -2 then (chargeCoord L γ a * chargeCoord L γ b) • mkEα L γ q else 0) := by
  classical
  have hAZa : IsField (liftFGen L (currentN (rank L) 1 a) + ZfGen L a) :=
    alphaLatGen_eq L a ▸ alphaLatGen_isField L a
  have hAZb : IsField (liftFGen L (currentN (rank L) 1 b) + ZfGen L b) :=
    alphaLatGen_eq L b ▸ alphaLatGen_isField L b
  rw [nprodGen_congr L (alphaLatGen_isField L a) (alphaLatGen_isField L b) hAZa hAZb
      (alphaLatGen_eq L a) (alphaLatGen_eq L b)]
  rw [nprodGen_add_left L (liftFGen_currentN_isField L a) (ZfGen_isField L a) hAZb hAZa s
    (mkEα L γ q)]
  rw [nprodGen_add_right L (liftFGen_currentN_isField L a) (liftFGen_currentN_isField L b)
        (ZfGen_isField L b) hAZb s (mkEα L γ q),
    nprodGen_add_right L (ZfGen_isField L a) (liftFGen_currentN_isField L b) (ZfGen_isField L b)
        hAZb s (mkEα L γ q)]
  rw [nprod_lift_lift_tmul₂, nprod_lift_ZfGen₂, nprod_ZfGen_lift₂, nprod_ZfGen_ZfGen₂]
  abel

/-! ## §3  The quadratic state and its zero mode -/

/-- The quadratic state `q_ab = h_a(−1)h_b(−1)𝟙`. -/
noncomputable abbrev quadState (a b : Fin (rank L)) : LatModuleGen L :=
  wordStateLatGen L [(0, a), (0, b)] 0

/-- `Y(q_ab, z) = :α^a(z) α^b(z):`. -/
theorem YfullGen_quadState (hEven : L.Even) (hPos : L.PosDef) (a b : Fin (rank L)) :
    YfullGen L hEven hPos (quadState L a b)
      = nprod (alphaLatGen_isField L a) (alphaLatGen_isField L b) := by
  rw [quadState, YfullGen_word, YwordLatGen_cons]
  exact nprodGen_congr L _ _ _ _ (genFieldLatGen_zero L a)
    ((BgA.YwordLatGen_singleton L 0 b).trans (genFieldLatGen_zero L b))

/-- The Fock zero mode of a current vanishes: `α^a_0 = 0` on `FockN`. -/
theorem currentN_neg_one (a : Fin (rank L)) (q : FockN (rank L)) :
    currentN (rank L) 1 a (-1) q = 0 := by
  rw [currentN_apply, show -(-1 : ℤ) - 1 = 0 by ring, oscN_zero, LinearMap.zero_apply]

/-- ⭐ **The zero mode of `q_ab`**: `o(q_ab)(p ⊗ e^γ) = (γ_a γ_b)·(p ⊗ e^γ) + N_ab(p) ⊗ e^γ`. -/
theorem smul_quadState_one (hEven : L.Even) (hPos : L.PosDef) (a b : Fin (rank L))
    (q : FockN (rank L)) (γ : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (quadState L a b) 1 (latStateGen L q γ)
      = latStateGen L
          ((chargeCoord L γ a * chargeCoord L γ b) • q
            + nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b) (-2) q) γ := by
  change mode (YfullGen L hEven hPos (quadState L a b)) 1 (mkEα L γ q) = _
  rw [YfullGen_quadState, mode_apply, show -(1 : ℤ) - 1 = -2 by ring, nprod_alphaLatGen_tmul₂,
    show (-2 : ℤ) + 1 = -1 by ring, currentN_neg_one, currentN_neg_one, map_zero, smul_zero,
    smul_zero, add_zero, add_zero, if_pos rfl]
  change mkEα L γ _ + (chargeCoord L γ a * chargeCoord L γ b) • mkEα L γ q
    = mkEα L γ ((chargeCoord L γ a * chargeCoord L γ b) • q + _)
  rw [map_add, map_smul, add_comm]

end VOA.LatGen
