/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedUnique

/-!
# The defect of the twisted product formula at the exponentials  (Moonshine step M6)

For states `u` and the exponential `e^β`, the **defect**

  `Def u e e' ℓ = star (e/2) F_e(u) ℓ F_{e'}(e^β) − F_{e+e'}((piE e u)₍ℓ₎ e^β)`

measures the failure of the twisted product formula `PF u (e^β)`.  This file proves the
structural relations of the defect at `u = e^α` that reduce `PF (e^α) (e^β)` to two vacuum
expectations:

* `Def_shift_left/right` — `Def` moves by `z` when a class moves by `2`;
* `Def_eventually_zero` — `Def` vanishes at large `ℓ`;
* `Def_hgen` — the defect of `h_b(−1) w` through the twisted iterate formula;
* `Def_T` — translation: `Def (T e^α) e e' ℓ = −ℓ Def (e^α) e e' (ℓ−1)`;
* `Def_ode` — **the recursion**: if `Def (e^α) (e−1) e' m = 0` for all `m ≥ ℓ`, then
  `−ℓ Def (e^α) e e' (ℓ−1) = ⟨α,β⟩ Def (e^α) (e−1) (e'+1) (ℓ−1)`;
* `Def_charge` — **the charge relation**: if `Def (e^α)` vanishes above level `m`, then
  `star ½ (Fgen_b) s (Def e e' m) = δ_{s0} (β_b Def e (e'+1) m + α_b Def (e+1) e' m)`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

/-! ## Facts about the projections -/

theorem piE_add_two (e : ℤ) (u : LatModuleGen L) : piE L (e + 2) u = piE L e u := by
  rw [piE, piE, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  norm_num

theorem piE_sum {ι : Type*} (e : ℤ) (s : Finset ι) (f : ι → LatModuleGen L) :
    piE L e (∑ i ∈ s, f i) = ∑ i ∈ s, piE L e (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [piE]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, piE_add, ih]

theorem theta_T (u : LatModuleGen L) :
    thetaLat L ((latticeVOAGen L hEven hPos).toPreVertexAlgebra.T u)
      = (latticeVOAGen L hEven hPos).toPreVertexAlgebra.T (thetaLat L u) := by
  rw [T_eq_smul_omega', T_eq_smul_omega']
  have h := thetaLat_mode L hEven hPos (omegaLatGen L) 0 u
  rw [thetaLat_omega] at h
  exact h

theorem piE_T (e : ℤ) (u : LatModuleGen L) :
    piE L e ((latticeVOAGen L hEven hPos).toPreVertexAlgebra.T u)
      = (latticeVOAGen L hEven hPos).toPreVertexAlgebra.T (piE L e u) := by
  rw [piE, piE, theta_T L hEven hPos, map_smul, map_add, map_smul]

/-! ## The defect -/

/-- **The defect of the twisted product formula** against `e^β`. -/
noncomputable def Def (β : L.carrier) (u : LatModuleGen L) (e e' ℓ : ℤ) : Fld (MT L hEven hU) :=
  star ((e : ℂ) / 2) (FL L hEven hU e u) ℓ (FL L hEven hU e' (echg L β))
    - FL L hEven hU (e + e') ((latticeVOAGen L hEven hPos).smul (piE L e u) ℓ (echg L β))

include hPos in
theorem PF_echg_of_Def (α β : L.carrier) (h : ∀ e e' ℓ, Def L hEven hU hPos β (echg L α) e e' ℓ = 0) :
    PF L hEven hU hPos (echg L α) (echg L β) := fun e e' ℓ => sub_eq_zero.mp (h e e' ℓ)

theorem Def_add (β : L.carrier) (u v : LatModuleGen L) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β (u + v) e e' ℓ
      = Def L hEven hU hPos β u e e' ℓ + Def L hEven hU hPos β v e e' ℓ := by
  rw [Def, Def, Def, map_add, star_add_left (FLloc L hEven hU hPos _ _ _ _)
    (FLloc L hEven hU hPos _ _ _ _), piE_add, PreVertexAlgebra.smul_add_left, map_add]
  abel

theorem Def_smul (β : L.carrier) (c : ℂ) (u : LatModuleGen L) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β (c • u) e e' ℓ = c • Def L hEven hU hPos β u e e' ℓ := by
  rw [Def, Def, map_smul, star_smul_left (FLloc L hEven hU hPos _ _ _ _), piE_smul,
    PreVertexAlgebra.smul_smul_left, map_smul, smul_sub]

theorem Def_sum {ι : Type*} (β : L.carrier) (s : Finset ι) (f : ι → LatModuleGen L)
    (e e' ℓ : ℤ) :
    Def L hEven hU hPos β (∑ i ∈ s, f i) e e' ℓ = ∑ i ∈ s, Def L hEven hU hPos β (f i) e e' ℓ := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, show (0 : LatModuleGen L) = (0 : ℂ) • 0 by simp,
        Def_smul, zero_smul]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Def_add, ih]

/-! ## Shifts of the classes -/

theorem Def_shift_left (β : L.carrier) (u : LatModuleGen L) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β u (e + 2) e' ℓ = fzmul 1 (Def L hEven hU hPos β u e e' ℓ) := by
  rw [Def, Def, show e + 2 = e + 2 * 1 by ring, FL_shift, star_fzmul_left
      (FLloc L hEven hU hPos _ _ _ _), show e + 2 * 1 + e' = e + e' + 2 * 1 by ring, FL_shift,
    show e + 2 * 1 = e + 2 by ring, piE_add_two, fzmul_sub]
  congr 3
  push_cast
  ring

theorem Def_shift_right (β : L.carrier) (u : LatModuleGen L) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β u e (e' + 2) ℓ = fzmul 1 (Def L hEven hU hPos β u e e' ℓ) := by
  rw [Def, Def, show e' + 2 = e' + 2 * 1 by ring, FL_shift, star_fzmul_right,
    show e + (e' + 2 * 1) = e + e' + 2 * 1 by ring, FL_shift, fzmul_sub]

theorem Def_shift_left' (β : L.carrier) (u : LatModuleGen L) (e e' ℓ c : ℤ) :
    Def L hEven hU hPos β u (e + 2 * c) e' ℓ = fzmul c (Def L hEven hU hPos β u e e' ℓ) := by
  induction c using Int.induction_on with
  | zero => simp
  | succ c ih => rw [show e + 2 * (c + 1) = (e + 2 * c) + 2 by ring, Def_shift_left, ih,
      fzmul_fzmul, add_comm]
  | pred c ih =>
      have h := Def_shift_left L hEven hU hPos β u (e + 2 * (-(c : ℤ) - 1)) e' ℓ
      rw [show e + 2 * (-(c : ℤ) - 1) + 2 = e + 2 * (-(c : ℤ)) by ring, ih] at h
      have h' := congrArg (fzmul (-1)) h
      rw [fzmul_fzmul, fzmul_fzmul, show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift] at h'
      rw [← h', show (-1 : ℤ) + -(c : ℤ) = -(c : ℤ) - 1 by ring]

theorem Def_shift_right' (β : L.carrier) (u : LatModuleGen L) (e e' ℓ c : ℤ) :
    Def L hEven hU hPos β u e (e' + 2 * c) ℓ = fzmul c (Def L hEven hU hPos β u e e' ℓ) := by
  induction c using Int.induction_on with
  | zero => simp
  | succ c ih => rw [show e' + 2 * (c + 1) = (e' + 2 * c) + 2 by ring, Def_shift_right, ih,
      fzmul_fzmul, add_comm]
  | pred c ih =>
      have h := Def_shift_right L hEven hU hPos β u e (e' + 2 * (-(c : ℤ) - 1)) ℓ
      rw [show e' + 2 * (-(c : ℤ) - 1) + 2 = e' + 2 * (-(c : ℤ)) by ring, ih] at h
      have h' := congrArg (fzmul (-1)) h
      rw [fzmul_fzmul, fzmul_fzmul, show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift] at h'
      rw [← h', show (-1 : ℤ) + -(c : ℤ) = -(c : ℤ) - 1 by ring]

/-- Moving `2` from one class to the other leaves the defect unchanged. -/
theorem Def_balance (β : L.carrier) (u : LatModuleGen L) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β u (e + 2) (e' - 2) ℓ = Def L hEven hU hPos β u e e' ℓ := by
  rw [Def_shift_left, show e' - 2 = e' + 2 * (-1) by ring, Def_shift_right', fzmul_fzmul,
    show (1 : ℤ) + -1 = 0 by norm_num, fzmul_zero_shift]

/-- **The defect vanishes at large `ℓ`**, uniformly in the classes. -/
theorem Def_eventually_zero (β : L.carrier) (u : LatModuleGen L) :
    ∃ L0 : ℤ, ∀ e e' ℓ : ℤ, L0 ≤ ℓ → Def L hEven hU hPos β u e e' ℓ = 0 := by
  have hrep : ∀ e0 e0' : ℤ, ∃ N : ℤ, ∀ ℓ, N ≤ ℓ → Def L hEven hU hPos β u e0 e0' ℓ = 0 := by
    intro e0 e0'
    obtain ⟨N1, hN1⟩ := star_eventually_zero (FLloc L hEven hU hPos e0 e0' u (echg L β))
      ((e0 : ℂ) / 2)
    obtain ⟨N2, hN2⟩ := PreVertexAlgebra.smul_eventually_zero
      (latticeVOAGen L hEven hPos).toPreVertexAlgebra (piE L e0 u) (echg L β)
    exact ⟨max N1 N2, fun ℓ hℓ => by
      rw [Def, hN1 ℓ (le_of_max_le_left hℓ), hN2 ℓ (le_of_max_le_right hℓ), map_zero, sub_zero]⟩
  obtain ⟨N00, h00⟩ := hrep 0 0
  obtain ⟨N01, h01⟩ := hrep 0 1
  obtain ⟨N10, h10⟩ := hrep 1 0
  obtain ⟨N11, h11⟩ := hrep 1 1
  refine ⟨max (max N00 N01) (max N10 N11), fun e e' ℓ hℓ => ?_⟩
  obtain ⟨c, e0, he0, rfl⟩ : ∃ c e0 : ℤ, (e0 = 0 ∨ e0 = 1) ∧ e = e0 + 2 * c :=
    ⟨e / 2, e % 2, by omega, by omega⟩
  obtain ⟨c', e0', he0', rfl⟩ : ∃ c' e0' : ℤ, (e0' = 0 ∨ e0' = 1) ∧ e' = e0' + 2 * c' :=
    ⟨e' / 2, e' % 2, by omega, by omega⟩
  rw [Def_shift_left', Def_shift_right']
  rcases he0 with rfl | rfl <;> rcases he0' with rfl | rfl
  · rw [h00 ℓ (by omega), fzmul_zero, fzmul_zero]
  · rw [h01 ℓ (by omega), fzmul_zero, fzmul_zero]
  · rw [h10 ℓ (by omega), fzmul_zero, fzmul_zero]
  · rw [h11 ℓ (by omega), fzmul_zero, fzmul_zero]

/-! ## The defect of a generator creation -/

include hPos in
/-- The defect of `h_b(−1) w`, through the twisted iterate formula: if the defect of `w` vanishes
at levels `≥ ℓ` on the class pair `(e−1, e')`, then the defect of `h_b(−1)w` at `(e, e', ℓ)` is
`β_b` times the defect of `w` at `(e−1, e'+1, ℓ−1)`. -/
theorem Def_hgen (β : L.carrier) (b : Fin (rank L)) (w : LatModuleGen L) (e e' ℓ : ℤ)
    (h : ∀ m : ℤ, ℓ ≤ m → Def L hEven hU hPos β w (e - 1) e' m = 0) :
    Def L hEven hU hPos β ((latticeVOAGen L hEven hPos).smul (hgen L b) (-1) w) e e' ℓ
      = chargeCoord L β b • Def L hEven hU hPos β w (e - 1) (e' + 1) (ℓ - 1) := by
  set X := FL L hEven hU (e - 1) w with hX
  set Y := FL L hEven hU e' (echg L β) with hY
  have hFu : FL L hEven hU e ((latticeVOAGen L hEven hPos).smul (hgen L b) (-1) w)
      = star (1 / 2) (FgT b) (-1) X := by
    rw [show e = e - 1 + 1 by ring, show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 by norm_num,
      FL_smul_hgen_neg L hEven hU hPos]
  -- bounds
  obtain ⟨N1, hN1⟩ := star_eventually_zero (FLloc L hEven hU hPos (e - 1) e' w (echg L β))
    (((e - 1 : ℤ) : ℂ) / 2)
  obtain ⟨N2, hN2⟩ := star_eventually_zero (tloc L hEven hU hPos (FgT_mem L hEven hU b)
    (FL_mem L hEven hU hPos e' (echg L β))) (1 / 2)
  obtain ⟨N3, hN3⟩ := PreVertexAlgebra.smul_eventually_zero
    (latticeVOAGen L hEven hPos).toPreVertexAlgebra (piE L (e - 1) w) (echg L β)
  set K : ℕ := (N1 - ℓ).toNat + N2.toNat + (N3 - ℓ).toNat + 1 with hK
  rw [Def, hFu, show (e : ℂ) / 2 = 1 / 2 + (((e - 1 : ℤ) : ℂ) / 2) by push_cast; ring,
    star_iterate_range (latGenSet_local L hEven hU hPos) (FgT_mem L hEven hU b)
      (FL_mem L hEven hU hPos _ _) (FL_mem L hEven hU hPos _ _) _ _ _ _ K (fun i hi =>
        ⟨hN1 _ (by omega), hN2 _ (by omega)⟩),
    show (latticeVOAGen L hEven hPos).smul (hgen L b) (-1) w
      = (latticeVOAGen L hEven hPos).smul (hgen L b) (-1) w from rfl,
    piE_smul_hgen L hEven hPos, VertexOperatorAlgebra.mode_iterate,
    finsum_eq_sum_of_support_subset _ (s := Finset.range K) (by
      intro i hi
      rw [Function.mem_support] at hi
      by_contra hc
      rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
      apply hi
      rw [hN3 _ (by omega), PreVertexAlgebra.smul_zero_right,
        smul_hgen_echg_nonneg L hEven hPos b (by omega), if_neg (by omega),
        PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero, smul_zero]),
    map_sum, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single 0 (fun i _ hi => ?_) (fun h0 => absurd (Finset.mem_range.mpr
      (by omega)) h0)]
  · -- the `i = 0` term
    have hY0 : star (1 / 2) (FgT b) ((0 : ℕ) : ℤ) (FL L hEven hU e' (echg L β))
        = chargeCoord L β b • FL L hEven hU (e' + 1) (echg L β) := by
      rw [genPF L hEven hU hPos, smul_hgen_echg_nonneg L hEven hPos b (by norm_num),
        if_pos (by norm_num), map_smul]
    have hs0 : (latticeVOAGen L hEven hPos).smul (hgen L b) ((0 : ℕ) : ℤ) (echg L β)
        = chargeCoord L β b • echg L β := by
      rw [smul_hgen_echg_nonneg L hEven hPos b (by norm_num), if_pos (by norm_num)]
    have hgen' : ∀ (m : ℤ) (z : LatModuleGen L),
        FL L hEven hU (e + e') ((latticeVOAGen L hEven hPos).smul (hgen L b) m z)
          = star (1 / 2) (FgT b) m (FL L hEven hU (e - 1 + e') z) := by
      intro m z
      rw [genPF L hEven hU hPos, show e - 1 + e' + 1 = e + e' by ring]
    have hD := h ℓ le_rfl
    rw [Def, sub_eq_zero] at hD
    rw [hY0, hs0, star_smul_right (FLloc L hEven hU hPos _ _ _ _), PreVertexAlgebra.smul_smul_right,
      map_smul, map_sub, map_smul, map_smul, hgen', gBinom_neg_one]
    simp only [Nat.cast_zero, sub_zero, add_zero, pow_zero, one_mul, one_smul]
    rw [hD, Def, show e - 1 + (e' + 1) = e + e' by ring, show (-1 : ℤ) + ℓ = ℓ - 1 by ring]
    module
  · -- the terms `i ≠ 0`
    have hYi : star (1 / 2) (FgT b) (i : ℤ) (FL L hEven hU e' (echg L β)) = 0 := by
      rw [genPF L hEven hU hPos, smul_hgen_echg_nonneg L hEven hPos b (by omega),
        if_neg (by omega), map_zero]
    have hsi : (latticeVOAGen L hEven hPos).smul (hgen L b) (i : ℤ) (echg L β) = 0 := by
      rw [smul_hgen_echg_nonneg L hEven hPos b (by omega), if_neg (by omega)]
    have hD := h (ℓ + i) (by omega)
    rw [Def, sub_eq_zero] at hD
    simp only [hYi, hsi, star_zero_right, PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
    rw [map_smul, hD, genPF L hEven hU hPos, show e - 1 + e' + 1 = e + e' by ring, sub_self]

/-! ## Translation and the recursion -/

include hPos in
/-- **Translation**: `Def (T e^α) e e' ℓ = −ℓ · Def (e^α) e e' (ℓ−1)`. -/
theorem Def_T (α β : L.carrier) (e e' ℓ : ℤ) :
    Def L hEven hU hPos β ((latticeVOAGen L hEven hPos).toPreVertexAlgebra.T (echg L α)) e e' ℓ
      = (-(ℓ : ℂ)) • Def L hEven hU hPos β (echg L α) e e' (ℓ - 1) := by
  rw [Def, Def, FL_T_echg L hEven hU hPos, star_deriv_left (FLloc L hEven hU hPos _ _ _ _),
    piE_T L hEven hPos, smul_T_left', map_smul, smul_sub]

include hPos in
/-- **The recursion for the exponential defect.** -/
theorem Def_ode (α β : L.carrier) (e e' ℓ : ℤ)
    (h : ∀ m : ℤ, ℓ ≤ m → Def L hEven hU hPos β (echg L α) (e - 1) e' m = 0) :
    (-(ℓ : ℂ)) • Def L hEven hU hPos β (echg L α) e e' (ℓ - 1)
      = ((L.form α β : ℤ) : ℂ) • Def L hEven hU hPos β (echg L α) (e - 1) (e' + 1) (ℓ - 1) := by
  rw [← Def_T, T_echg, Def_sum]
  simp only [Def_smul, Def_hgen L hEven hU hPos β _ _ e e' ℓ h, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [← sum_chargeCoord L hPos α β]

/-! ## The charge relation -/

theorem neg_mem_tgen {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Set (Fld M)) {X : Fld M}
    (hX : X ∈ TGenerated S) : -X ∈ TGenerated S := by
  rw [show -X = (-1 : ℂ) • X by simp]
  exact smul_mem_tgenerated _ hX


include hPos in
/-- **The charge relation of the exponential defect**: if the defect vanishes above level
`m` (all classes), then
`star ½ (Fgen_b) s (Def e e' m) = δ_{s0} (β_b Def e (e'+1) m + α_b Def (e+1) e' m)`. -/
theorem Def_charge (α β : L.carrier) (m : ℤ)
    (h : ∀ e e' m' : ℤ, m < m' → Def L hEven hU hPos β (echg L α) e e' m' = 0)
    (b : Fin (rank L)) (e e' : ℤ) (s : ℕ) :
    star (1 / 2) (FgT b) s (Def L hEven hU hPos β (echg L α) e e' m)
      = if s = 0 then chargeCoord L β b • Def L hEven hU hPos β (echg L α) e (e' + 1) m
          + chargeCoord L α b • Def L hEven hU hPos β (echg L α) (e + 1) e' m else 0 := by
  have hl : ∀ X : Fld (MT L hEven hU), X ∈ TGenerated (latGenSet L hEven hU) →
      Local (FgT (Tm := Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) b).1 X.1 :=
    fun X hX => tloc L hEven hU hPos (FgT_mem L hEven hU b) hX
  -- bounds
  obtain ⟨K1, hK1⟩ := exists_prod_offset_zero (hl _ (FL_mem L hEven hU hPos e (echg L α))) 0
  obtain ⟨K2, hK2⟩ := PreVertexAlgebra.smul_eventually_zero
    (latticeVOAGen L hEven hPos).toPreVertexAlgebra (hgen L b) (piE L e (echg L α))
  set Lb : ℕ := K1 + K2.toNat + 1 with hLb
  -- the generator against the two exponentials
  have hA0 : star (1 / 2) (FgT b) ((0 : ℕ) : ℤ) (FL L hEven hU e (echg L α))
      = chargeCoord L α b • FL L hEven hU (e + 1) (echg L α) := by
    rw [FL_echg L hEven hU hPos, star_FgT_YTLFld L hEven hU b α e (by norm_num),
      if_pos (by norm_num), FL_echg L hEven hU hPos]
  have hAt : ∀ t : ℕ, t ≠ 0 → star (1 / 2) (FgT b) (t : ℤ) (FL L hEven hU e (echg L α)) = 0 := by
    intro t ht
    rw [FL_echg L hEven hU hPos, star_FgT_YTLFld L hEven hU b α e (by omega),
      if_neg (by exact_mod_cast ht)]
  have hBs : star (1 / 2) (FgT b) (s : ℤ) (FL L hEven hU e' (echg L β))
      = if s = 0 then chargeCoord L β b • FL L hEven hU (e' + 1) (echg L β) else 0 := by
    rw [FL_echg L hEven hU hPos, star_FgT_YTLFld L hEven hU b β e' (by omega),
      FL_echg L hEven hU hPos]
    simp only [Nat.cast_eq_zero]
  have hx0 : (latticeVOAGen L hEven hPos).smul (hgen L b) ((0 : ℕ) : ℤ) (piE L e (echg L α))
      = chargeCoord L α b • piE L (e + 1) (echg L α) := by
    have := piE_smul_hgen L hEven hPos (e + 1) b ((0 : ℕ) : ℤ) (echg L α)
    rw [show e + 1 - 1 = e by ring, smul_hgen_echg_nonneg L hEven hPos b (by norm_num),
      if_pos (by norm_num), piE_smul] at this
    exact this.symm
  have hxt : ∀ t : ℕ, t ≠ 0 →
      (latticeVOAGen L hEven hPos).smul (hgen L b) (t : ℤ) (piE L e (echg L α)) = 0 := by
    intro t ht
    have := piE_smul_hgen L hEven hPos (e + 1) b (t : ℤ) (echg L α)
    rw [show e + 1 - 1 = e by ring, smul_hgen_echg_nonneg L hEven hPos b (by omega),
      if_neg (by exact_mod_cast ht)] at this
    rw [← this]
    simp [piE]
  have hbs : (latticeVOAGen L hEven hPos).smul (hgen L b) (s : ℤ) (echg L β)
      = if s = 0 then chargeCoord L β b • echg L β else 0 := by
    rw [smul_hgen_echg_nonneg L hEven hPos b (by omega)]
    simp only [Nat.cast_eq_zero]
  -- the field side, by the twisted commutator formula
  have hT := star_comm (latGenSet_local L hEven hU hPos) (FgT_mem L hEven hU b)
    (FL_mem L hEven hU hPos e (echg L α)) (FL_mem L hEven hU hPos e' (echg L β)) (1 / 2)
    ((e : ℂ) / 2) s m Lb (fun t ht => by have := hK1 t (by omega); rwa [zero_add] at this)
  rw [Finset.sum_eq_single 0 (fun t _ ht => by rw [hAt t ht, star_zero_left, smul_zero])
    (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0), gBinom_zero, one_smul, hA0,
    star_smul_left (FLloc L hEven hU hPos _ _ _ _), hBs,
    show (1 / 2 : ℂ) + (e : ℂ) / 2 = ((e + 1 : ℤ) : ℂ) / 2 by push_cast; ring,
    show (s : ℤ) + m - ((0 : ℕ) : ℤ) = s + m by push_cast; ring] at hT
  -- the state side, by the commutator formula of `V_L`
  have hV := voa_comm (latticeVOAGen L hEven hPos) (hgen L b) (piE L e (echg L α)) (echg L β)
    s m Lb (fun k hk => hK2 _ (by omega))
  rw [Finset.sum_eq_single 0 (fun t _ ht => by rw [hxt t ht, PreVertexAlgebra.smul_zero_left,
      smul_zero]) (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0), gBinom_zero, one_smul,
    hx0, PreVertexAlgebra.smul_smul_left, hbs,
    show (s : ℤ) + m - ((0 : ℕ) : ℤ) = s + m by push_cast; ring] at hV
  -- assemble
  rw [Def, sub_eq_add_neg, star_add_right (hl _ (star_mem (latGenSet_local L hEven hU hPos)
      (FL_mem L hEven hU hPos _ _) (FL_mem L hEven hU hPos _ _) _ _))
    (hl _ (neg_mem_tgen _ (FL_mem L hEven hU hPos _ _))),
    show -(FL L hEven hU (e + e') ((latticeVOAGen L hEven hPos).smul (piE L e (echg L α)) m
        (echg L β))) = (-1 : ℂ) • FL L hEven hU (e + e') ((latticeVOAGen L hEven hPos).smul
          (piE L e (echg L α)) m (echg L β)) by rw [neg_one_smul],
    star_smul_right (hl _ (FL_mem L hEven hU hPos _ _)), genPF L hEven hU hPos,
    eq_add_of_sub_eq hT, eq_add_of_sub_eq hV]
  split_ifs with hs0
  · subst hs0
    rw [star_smul_right (FLloc L hEven hU hPos _ _ _ _), PreVertexAlgebra.smul_smul_right]
    simp only [Nat.cast_zero, zero_add, map_add, map_smul, Def]
    rw [show e + (e' + 1) = e + e' + 1 by ring, show e + 1 + e' = e + e' + 1 by ring]
    module
  · have hz := h (e + 1) e' (s + m) (by omega)
    rw [Def, sub_eq_zero] at hz
    simp only [star_zero_right, PreVertexAlgebra.smul_zero_right, add_zero, map_smul]
    rw [hz, show e + e' + 1 = e + 1 + e' by ring]
    module

end VOA.Moonshine.LatticeTwisted
