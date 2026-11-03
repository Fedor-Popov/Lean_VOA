/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenConformal

/-!
# The frame Sugawara mode decomposition `sugFieldGen s (q ⊗ e^γ)`

The `nprod`-split infrastructure for the general even-lattice frame Sugawara field, ported from
A₁'s `LatticeVOAInstance.lean` (lines 205-448) with the single boson replaced by the orthonormal
frame `∑_{a : Fin (rank L)}`, the level-2 `1/4` replaced by level-1 `1/2`, the momentum eigenvalue
`2k` replaced by `chargeCoord γ a`, and `k² → ½⟨γ,γ⟩`.  The keystone `sugFieldGen_tmul` decomposes
`T(z)` on a basis state into the total boson Virasoro mode `Lₙ`, the charge oscillator, and the
`⟨γ,γ⟩` zero-mode.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §A  The lift–`nprod` interchange (generic over the boson factor). -/

/-- `liftFGen` carries `normalOrdered` of two boson fields to `normalOrdered` of their lifts. -/
theorem normalOrdered_liftFGen (a b : FormalDist (End ℂ (FockN (rank L)))) (m n : ℤ) :
    normalOrdered (liftFGen L a) (liftFGen L b) m n
      = LinearMap.rTensor (L.carrier →₀ ℂ) (normalOrdered a b m n) := by
  rw [normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h]
    change LinearMap.rTensor (L.carrier →₀ ℂ) (a m) * LinearMap.rTensor (L.carrier →₀ ℂ) (b n)
      = LinearMap.rTensor (L.carrier →₀ ℂ) (a m * b n)
    rw [rTensorGen_mul]
  · rw [if_neg h, if_neg h]
    change LinearMap.rTensor (L.carrier →₀ ℂ) (b n) * LinearMap.rTensor (L.carrier →₀ ℂ) (a m)
      = LinearMap.rTensor (L.carrier →₀ ℂ) (b n * a m)
    rw [rTensorGen_mul]

/-- **The lift–`nprod` interchange**: `nprod (liftFGen a) (liftFGen b) = liftFGen (nprod a b)`. -/
theorem liftFGen_nprod {a b : FormalDist (End ℂ (FockN (rank L)))} (ha : IsField a) (hb : IsField b) :
    nprod (liftFGen_isField L ha) (liftFGen_isField L hb) = liftFGen L (nprod ha hb) := by
  funext s
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; change liftFGen L (nprod ha hb) s 0 = 0; rw [map_zero]
  | add x y hx hy =>
      rw [map_add, hx, hy]; change _ = liftFGen L (nprod ha hb) s (x + y)
      rw [map_add]
  | tmul p g =>
      rw [nprod_apply]
      change _ = LinearMap.rTensor (L.carrier →₀ ℂ) (nprod ha hb s) (p ⊗ₜ[ℂ] g)
      rw [show (nprod ha hb s) = nprodCoeff ha hb s from rfl,
        LinearMap.rTensor_tmul (L.carrier →₀ ℂ) (nprodCoeff ha hb s) g p,
        show (nprodCoeff ha hb s p) = ∑ᶠ m : ℤ, normalOrdered a b m (s - m) p from rfl]
      have hfin : (Function.support
          (fun m : ℤ => normalOrdered a b m (s - m) p)).Finite :=
        normalOrdered_diag_support_finite ha hb s p
      rw [finsum_congr (fun m => by
        rw [show normalOrdered (liftFGen L a) (liftFGen L b) m (s - m) (p ⊗ₜ[ℂ] g)
            = LinearMap.rTensor (L.carrier →₀ ℂ) (normalOrdered a b m (s - m)) (p ⊗ₜ[ℂ] g) from by
              rw [normalOrdered_liftFGen L a b m (s - m)],
          LinearMap.rTensor_tmul,
          show (normalOrdered a b m (s - m) p) ⊗ₜ[ℂ] g
            = ((TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip g)
                (normalOrdered a b m (s - m) p) from rfl])]
      rw [← map_finsum ((TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip g) hfin]
      rfl

/-! ## §B  `nprod` bilinearity and congruence (on `V_L`). -/

/-- `nprod` is additive in its left argument. -/
theorem nprodGen_add_left {a₁ a₂ b : FormalDist (End ℂ (LatModuleGen L))}
    (ha₁ : IsField a₁) (ha₂ : IsField a₂) (hb : IsField b)
    (hadd : IsField (a₁ + a₂)) (s : ℤ) (x : LatModuleGen L) :
    nprod hadd hb s x = nprod ha₁ hb s x + nprod ha₂ hb s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha₁ hb s x)
      (normalOrdered_diag_support_finite ha₂ hb s x)]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, if_pos h]
    change ((a₁ m + a₂ m) * b (s - m)) x = (a₁ m * b (s - m)) x + (a₂ m * b (s - m)) x
    rw [add_mul, LinearMap.add_apply]
  · rw [if_neg h, if_neg h, if_neg h]
    change (b (s - m) * (a₁ m + a₂ m)) x = (b (s - m) * a₁ m) x + (b (s - m) * a₂ m) x
    rw [mul_add, LinearMap.add_apply]

/-- `nprod` is additive in its right argument. -/
theorem nprodGen_add_right {a b₁ b₂ : FormalDist (End ℂ (LatModuleGen L))}
    (ha : IsField a) (hb₁ : IsField b₁) (hb₂ : IsField b₂)
    (hadd : IsField (b₁ + b₂)) (s : ℤ) (x : LatModuleGen L) :
    nprod ha hadd s x = nprod ha hb₁ s x + nprod ha hb₂ s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha hb₁ s x)
      (normalOrdered_diag_support_finite ha hb₂ s x)]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, if_pos h]
    change (a m * (b₁ (s - m) + b₂ (s - m))) x = (a m * b₁ (s - m)) x + (a m * b₂ (s - m)) x
    rw [mul_add, LinearMap.add_apply]
  · rw [if_neg h, if_neg h, if_neg h]
    change ((b₁ (s - m) + b₂ (s - m)) * a m) x = (b₁ (s - m) * a m) x + (b₂ (s - m) * a m) x
    rw [add_mul, LinearMap.add_apply]

/-- `nprod` depends only on the underlying distributions, not on the field-witness proofs. -/
theorem nprodGen_congr {a b a' b' : FormalDist (End ℂ (LatModuleGen L))}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (haa : a = a') (hbb : b = b') : nprod ha hb = nprod ha' hb' := by
  subst haa; subst hbb; rfl

/-! ## §C  The momentum field `ZfGen a` and the split `alphaLatGen a = liftFGen (α^a) + ZfGen a`. -/

/-- The per-frame momentum field `ZfGen a j = (j = -1 ? zGradeOpGen a : 0)`. -/
noncomputable def ZfGen (a : Fin (rank L)) : FormalDist (End ℂ (LatModuleGen L)) :=
  fun j => if j = -1 then zGradeOpGen L a else 0

theorem ZfGen_isField (a : Fin (rank L)) : IsField (ZfGen L a) := by
  intro x; refine ⟨-1, fun n hn => ?_⟩
  show (if n = -1 then zGradeOpGen L a else 0) x = 0
  rw [if_neg (by omega : ¬ n = -1)]; rfl

/-- `alphaLatGen a = liftFGen (α^a) + ZfGen a`. -/
theorem alphaLatGen_eq (a : Fin (rank L)) :
    alphaLatGen L a = liftFGen L (currentN (rank L) 1 a) + ZfGen L a := by
  funext j
  show alphaLatGen L a j = liftFGen L (currentN (rank L) 1 a) j + ZfGen L a j
  rw [alphaLatGen_apply, liftFGen, ZfGen]

/-- `liftFGen (α^a)` is a field. -/
theorem liftFGen_currentN_isField (a : Fin (rank L)) : IsField (liftFGen L (currentN (rank L) 1 a)) :=
  liftFGen_isField L (currentN_isField (rank L) 1 a)

/-! ## §D  The three cross terms on a basis state `q ⊗ e^γ`. -/

/-- The cross-term `nprod (liftF α^a) (ZfGen a)` on `q ⊗ e^γ`: only `m = s+1` survives. -/
theorem nprod_lift_ZfGen (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (liftFGen_currentN_isField L a) (ZfGen_isField L a) s (mkEα L γ q)
      = chargeCoord L γ a • mkEα L γ (currentN (rank L) 1 a (s + 1) q) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ s + 1 →
      normalOrdered (liftFGen L (currentN (rank L) 1 a)) (ZfGen L a) m (s - m) (mkEα L γ q) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : ZfGen L a (s - m) = 0 := by
      show (if s - m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg (by omega)]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m) * ZfGen L a (s - m)) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
    · rw [if_neg h0]
      change (ZfGen L a (s - m) * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
  have hZss : ZfGen L a (s - (s + 1)) = zGradeOpGen L a := by
    show (if s - (s + 1) = -1 then zGradeOpGen L a else 0) = zGradeOpGen L a; rw [if_pos (by ring)]
  rw [finsum_eq_single _ (s + 1) hsupp, normalOrdered_apply, hZss]
  by_cases h0 : 0 ≤ s + 1
  · rw [if_pos h0]
    change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)) * zGradeOpGen L a)
      (mkEα L γ q) = _
    rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, zGradeOpGen_latStateGen,
      map_smul]
    change chargeCoord L γ a • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
      (q ⊗ₜ[ℂ] eGen L γ) = _
    rw [LinearMap.rTensor_tmul]; rfl
  · rw [if_neg h0]
    change (zGradeOpGen L a * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
      (mkEα L γ q) = _
    rw [Module.End.mul_apply]
    change zGradeOpGen L a (latStateGen L (currentN (rank L) 1 a (s + 1) q) γ) = _
    rw [zGradeOpGen_latStateGen]; rfl

/-- The cross-term `nprod (ZfGen a) (liftF α^a)` on `q ⊗ e^γ`: only `m = -1` survives. -/
theorem nprod_ZfGen_lift (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (ZfGen_isField L a) (liftFGen_currentN_isField L a) s (mkEα L γ q)
      = chargeCoord L γ a • mkEα L γ (currentN (rank L) 1 a (s + 1) q) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ -1 →
      normalOrdered (ZfGen L a) (liftFGen L (currentN (rank L) 1 a)) m (s - m) (mkEα L γ q) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : ZfGen L a m = 0 := by
      show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg hm]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      change (ZfGen L a m * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s - m))) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]
      change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s - m)) * ZfGen L a m) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
  have hZm1 : ZfGen L a (-1) = zGradeOpGen L a := by
    show (if (-1 : ℤ) = -1 then zGradeOpGen L a else 0) = zGradeOpGen L a; rw [if_pos rfl]
  rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
    hZm1]
  change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s - -1)) * zGradeOpGen L a)
    (mkEα L γ q) = _
  rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, zGradeOpGen_latStateGen,
    map_smul, show s - -1 = s + 1 from by ring]
  change chargeCoord L γ a • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
    (q ⊗ₜ[ℂ] eGen L γ) = _
  rw [LinearMap.rTensor_tmul]; rfl

/-- The `ZfGen ZfGen` term on `q ⊗ e^γ`: `= (s = -2 ? (chargeCoord γ a)² • (q ⊗ e^γ) : 0)`. -/
theorem nprod_ZfGen_ZfGen (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (ZfGen_isField L a) (ZfGen_isField L a) s (mkEα L γ q)
      = if s = -2 then (chargeCoord L γ a * chargeCoord L γ a) • mkEα L γ q else 0 := by
  rw [nprod_apply]
  by_cases hs : s = -2
  · have hsupp : ∀ m : ℤ, m ≠ -1 →
        normalOrdered (ZfGen L a) (ZfGen L a) m (s - m) (mkEα L γ q) = 0 := by
      intro m hm
      rw [normalOrdered_apply]
      have hZ : ZfGen L a m = 0 := by
        show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg hm]
      by_cases h0 : 0 ≤ m
      · rw [if_pos h0]; change (ZfGen L a m * ZfGen L a (s - m)) _ = 0
        rw [hZ, zero_mul, LinearMap.zero_apply]
      · rw [if_neg h0]; change (ZfGen L a (s - m) * ZfGen L a m) _ = 0
        rw [hZ, mul_zero, LinearMap.zero_apply]
    have hZm1 : ZfGen L a (-1) = zGradeOpGen L a := by
      show (if (-1 : ℤ) = -1 then zGradeOpGen L a else 0) = zGradeOpGen L a; rw [if_pos rfl]
    have hZsm : ZfGen L a (s - -1) = zGradeOpGen L a := by
      show (if s - -1 = -1 then zGradeOpGen L a else 0) = zGradeOpGen L a; rw [if_pos (by omega)]
    rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
      hZm1, hZsm, if_pos hs]
    change (zGradeOpGen L a * zGradeOpGen L a) (mkEα L γ q) = _
    rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, zGradeOpGen_latStateGen,
      map_smul, zGradeOpGen_latStateGen, smul_smul]
  · rw [if_neg hs]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      have hZ : ZfGen L a m = 0 := by
        show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg (by omega)]
      change (ZfGen L a m * ZfGen L a (s - m)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]
      by_cases hm1 : m = -1
      · subst hm1
        have hZ : ZfGen L a (s - -1) = 0 := by
          show (if s - -1 = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg (by omega)]
        change (ZfGen L a (s - -1) * ZfGen L a (-1)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
      · have hZ : ZfGen L a m = 0 := by
          show (if m = -1 then zGradeOpGen L a else 0) = 0; rw [if_neg hm1]
        change (ZfGen L a (s - m) * ZfGen L a m) _ = 0; rw [hZ, mul_zero, LinearMap.zero_apply]

/-- The lift mode of the boson Sugawara on a basis state. -/
theorem nprod_lift_lift_tmul (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (liftFGen_currentN_isField L a) (liftFGen_currentN_isField L a) s (mkEα L γ q)
      = mkEα L γ (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s q) := by
  have heq : nprod (liftFGen_currentN_isField L a) (liftFGen_currentN_isField L a)
      = liftFGen L (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a)) :=
    liftFGen_nprod L (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a)
  rw [heq]
  show LinearMap.rTensor (L.carrier →₀ ℂ)
      (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s) (q ⊗ₜ[ℂ] eGen L γ) = _
  rw [LinearMap.rTensor_tmul]; rfl

/-! ## §E  The per-frame Sugawara decomposition and the total mode bridge. -/

/-- **The per-frame Sugawara mode decomposition** on a basis state `q ⊗ e^γ`. -/
theorem nprod_alphaLatGen_tmul (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a) s (mkEα L γ q)
      = mkEα L γ (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s q)
        + (2 * chargeCoord L γ a) • mkEα L γ (currentN (rank L) 1 a (s + 1) q)
        + (if s = -2 then (chargeCoord L γ a * chargeCoord L γ a) • mkEα L γ q else 0) := by
  classical
  have hAZ : IsField (liftFGen L (currentN (rank L) 1 a) + ZfGen L a) :=
    alphaLatGen_eq L a ▸ alphaLatGen_isField L a
  rw [nprodGen_congr L (alphaLatGen_isField L a) (alphaLatGen_isField L a) hAZ hAZ
      (alphaLatGen_eq L a) (alphaLatGen_eq L a)]
  rw [nprodGen_add_left L (liftFGen_currentN_isField L a) (ZfGen_isField L a) hAZ hAZ s (mkEα L γ q)]
  rw [nprodGen_add_right L (liftFGen_currentN_isField L a) (liftFGen_currentN_isField L a)
        (ZfGen_isField L a) hAZ s (mkEα L γ q),
    nprodGen_add_right L (ZfGen_isField L a) (liftFGen_currentN_isField L a) (ZfGen_isField L a)
        hAZ s (mkEα L γ q)]
  rw [nprod_lift_lift_tmul, nprod_lift_ZfGen, nprod_ZfGen_lift, nprod_ZfGen_ZfGen]
  rw [two_mul, add_smul]
  abel

/-- `(1/2)·(nprod α^a α^a s) = LvirNa (rank L) 1 a (-s-2)` (per-frame boson Sugawara mode bridge). -/
theorem half_nprod_currentN (a : Fin (rank L)) (s : ℤ) :
    (1 / 2 : ℂ) • nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s
      = HeisenbergN.LvirNa (rank L) 1 a (-s - 2) := by
  rw [HeisenbergN.LvirNa, show -(-s - 2) - 2 = s from by ring,
    show (1 / (2 * 1) : ℂ) = (1 / 2 : ℂ) from by norm_num]

/-- The charge oscillator on a basis vector as the frame sum: `chargeOsc γ n q = ∑ₐ cc·α^a_F(-n-1) q`
in `currentN` form, i.e. `chargeOsc γ (-s-2) q = ∑ₐ cc·(currentN a (s+1) q)`. -/
theorem chargeOsc_neg_apply (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    chargeOsc L γ (-s - 2) q
      = ∑ a : Fin (rank L), chargeCoord L γ a • currentN (rank L) 1 a (s + 1) q := by
  rw [chargeOsc_eq_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [LinearMap.smul_apply, currentN_apply, show -(s + 1) - 1 = -s - 2 from by ring]

/-- **The frame Sugawara field on a basis state** `q ⊗ e^γ` (the keystone mode decomposition):
`T(z)` splits into the total boson Virasoro mode `L_{-s-2}`, the charge oscillator `γ(-s-2)`, and
the `½⟨γ,γ⟩` zero-mode. -/
theorem sugFieldGen_tmul (hPos : L.PosDef) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    sugFieldGen L s (latStateGen L q γ)
      = latStateGen L (HeisenbergN.LvirN (rank L) 1 (-s - 2) q) γ
        + latStateGen L (chargeOsc L γ (-s - 2) q) γ
        + (if s = -2 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • latStateGen L q γ else 0) := by
  classical
  rw [sugFieldGen]
  change (1 / 2 : ℂ) • (((∑ a : Fin (rank L),
      nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) s) (mkEα L γ q)) = _
  rw [show ((∑ a : Fin (rank L),
          nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) s : End ℂ (LatModuleGen L))
        = ∑ a : Fin (rank L), nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a) s from
      Finset.sum_apply (s := Finset.univ)
        (g := fun a : Fin (rank L) => nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) s,
    LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_congr rfl (fun a _ => nprod_alphaLatGen_tmul L a s q γ),
    Finset.sum_add_distrib, Finset.sum_add_distrib, smul_add, smul_add]
  congr 1
  · congr 1
    · -- bulk: (1/2)•∑ₐ mkEα γ(nprod α^a α^a s q) = latStateGen (LvirN (-s-2) q) γ
      rw [← map_sum (mkEα L γ), ← map_smul (mkEα L γ)]
      refine congrArg (mkEα L γ) ?_
      rw [HeisenbergN.LvirN_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← half_nprod_currentN L a s, LinearMap.smul_apply]
    · -- cross: (1/2)•∑ₐ (2cc)•mkEα γ(α^a_F(s+1) q) = latStateGen (chargeOsc γ (-s-2) q) γ
      rw [Finset.sum_congr rfl (fun a _ => (map_smul (mkEα L γ) (2 * chargeCoord L γ a)
          (currentN (rank L) 1 a (s + 1) q)).symm),
        ← map_sum (mkEα L γ), ← map_smul (mkEα L γ)]
      refine congrArg (mkEα L γ) ?_
      -- goal: (1/2)•∑ₐ (2cc)•currentN a (s+1) q = chargeOsc γ (-s-2) q
      rw [chargeOsc_neg_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [smul_smul]
      congr 1
      ring
  · -- zero-mode: (1/2)•∑ₐ (if s=-2 then cc²•mkEα γ q) = (if s=-2 then ½⟨γ,γ⟩•latStateGen q γ)
    by_cases hs : s = -2
    · rw [Finset.sum_congr rfl (fun a _ => by rw [if_pos hs]), if_pos hs,
        ← Finset.sum_smul, smul_smul, sum_chargeCoord L hPos γ γ]
      rfl
    · rw [Finset.sum_congr rfl (fun a _ => by rw [if_neg hs]), if_neg hs,
        Finset.sum_const_zero, smul_zero]

end VOA.LatGen
