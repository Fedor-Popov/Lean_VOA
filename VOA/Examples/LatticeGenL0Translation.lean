/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenVirasoro

/-!
# `L₀`-grading and translation for the general even-lattice VOA

The conformal translation operator `L₋₁ = mode (YfullGen ω) 0 = TrecGen`, VOA3
(`YfullGen_translation_omega`), the `L₀` operator `mode (YfullGen ω) 1 = sugFieldGen(-2)` acting as
the conformal weight `w + ½⟨α,α⟩`, and VOA2 (`YfullGen_L0_grading`).  Cross-charge lift of A₁'s
`LatticeVOAInstance` (lines 471-616); `n² → halfNorm L α`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §A  The conformal translation operator `L₋₁ = TrecGen`. -/

/-- The lattice conformal translation operator `LtransGen := mode (sugFieldGen) 0 = sugFieldGen(-1)`. -/
noncomputable def LtransGen : End ℂ (LatModuleGen L) := mode (sugFieldGen L) 0

theorem LtransGen_eq : LtransGen L = sugFieldGen L (-1) := by
  rw [LtransGen, mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring]

/-- **The bridge `LtransGen = TrecGen`**: the abstract Sugawara translation equals the explicit
reconstruction translation operator (both `L₋₁ + γ(-1)` on `q ⊗ e^γ`). -/
theorem LtransGen_eq_TrecGen (hPos : L.PosDef) : LtransGen L = TrecGen L := by
  rw [LtransGen_eq]
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 h1 h2 => rw [map_add, map_add, h1, h2]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; rw [map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add]; rw [map_add, map_add, h1, h2]
      | single c a =>
          rw [(Finsupp.smul_single_one c a).symm,
            show (Finsupp.single c 1 : L.carrier →₀ ℂ) = eGen L c from rfl]
          erw [TensorProduct.tmul_smul, map_smul, map_smul]
          rw [show p ⊗ₜ[ℂ] eGen L c = latStateGen L p c from rfl,
            sugFieldGen_tmul L hPos, TrecGen_tmul, if_neg (by norm_num : ¬ (-1 : ℤ) = -2),
            add_zero, show (-(-1 : ℤ) - 2) = -1 from by ring]

/-- `mode (YfullGen ω) 0 = TrecGen` (the conformal `L₋₁` is the reconstruction translation operator). -/
theorem mode_YfullGen_omega_zero (hEven : L.Even) (hPos : L.PosDef) :
    mode (YfullGen L hEven hPos (omegaLatGen L)) 0 = TrecGen L := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring, YfullGen_omega_eq, ← LtransGen_eq,
    LtransGen_eq_TrecGen L hPos]

/-! ## §B  VOA3 — translation `YfullGen (L₋₁ v) = ∂_z YfullGen v`. -/

/-- `(YfullGen v) 1 |0⟩ = TrecGen v` (the first creation-tower step, from `TrecGen`-covariance). -/
theorem YfullGen_one_vac (hEven : L.Even) (hPos : L.PosDef) (v : LatModuleGen L) :
    (YfullGen L hEven hPos v) 1 (latVacuumGen L) = TrecGen L v := by
  have h := congrArg (fun (R : End ℂ (LatModuleGen L)) => R (latVacuumGen L))
    (YfullGen_DCov L hEven hPos v 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [TrecGen_vacuum, map_zero, sub_zero, YfullGen_cre0, show ((0 : ℤ) + 1) = 1 from by ring,
    one_zsmul] at h
  exact h.symm

/-- **VOA3 (translation), `L₋₁ = TrecGen` form**: `YfullGen (TrecGen v) = ∂_z YfullGen v`. -/
theorem YfullGen_translation (hEven : L.Even) (hPos : L.PosDef) (v : LatModuleGen L) :
    YfullGen L hEven hPos (TrecGen L v) = deriv (YfullGen L hEven hPos v) := by
  have hGcov : Reconstruction.DCovariant (TrecGen L) (deriv (YfullGen L hEven hPos v)) :=
    Reconstruction.DCovariant.deriv' (YfullGen_DCov L hEven hPos v)
  have hGneg : ∀ q : ℤ, q < 0 → (deriv (YfullGen L hEven hPos v)) q (latVacuumGen L) = 0 := by
    intro q hq
    rw [deriv_apply]
    show ((q + 1 : ℤ) • (YfullGen L hEven hPos v) (q + 1)) (latVacuumGen L) = 0
    rw [← Int.cast_smul_eq_zsmul ℂ (q + 1), LinearMap.smul_apply]
    by_cases hq1 : q + 1 < 0
    · rw [YfullGen_creneg L hEven hPos v hq1, smul_zero]
    · rw [show q + 1 = (0 : ℤ) from by omega, Int.cast_zero, zero_smul]
  have hbase : (YfullGen L hEven hPos (TrecGen L v)) 0 (latVacuumGen L)
      = (deriv (YfullGen L hEven hPos v)) 0 (latVacuumGen L) := by
    rw [YfullGen_cre0, deriv_apply]
    show TrecGen L v = ((0 + 1 : ℤ) • (YfullGen L hEven hPos v) (0 + 1)) (latVacuumGen L)
    rw [show (0 + 1 : ℤ) = 1 from by ring, one_zsmul, YfullGen_one_vac]
  have hAvac : ∀ p : ℤ,
      (YfullGen L hEven hPos (TrecGen L v) - deriv (YfullGen L hEven hPos v)) p (latVacuumGen L) = 0 := by
    intro p
    show ((YfullGen L hEven hPos (TrecGen L v)) p - (deriv (YfullGen L hEven hPos v)) p)
      (latVacuumGen L) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (YfullGen_DCov L hEven hPos (TrecGen L v)) hGcov
      (TrecGen_vacuum L) hbase
      (fun q hq => YfullGen_creneg L hEven hPos (TrecGen L v) hq) hGneg p
  have hloc : ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Local (YfullGen L hEven hPos (TrecGen L v) - deriv (YfullGen L hEven hPos v))
        (YwordLatGen L l α) := by
    intro l α
    have h1 : Local (YfullGen L hEven hPos (TrecGen L v)) (YwordLatGen L l α) := by
      rw [← YfullGen_word L hEven hPos l α]
      exact YfullGen_local L hEven hPos (TrecGen L v) (wordStateLatGen L l α)
    have h2 : Local (deriv (YfullGen L hEven hPos v)) (YwordLatGen L l α) := by
      have hv : Local (YfullGen L hEven hPos v) (YwordLatGen L l α) := by
        rw [← YfullGen_word L hEven hPos l α]
        exact YfullGen_local L hEven hPos v (wordStateLatGen L l α)
      exact Local.derivL hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (deriv (YfullGen L hEven hPos v))]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hz := Reconstruction.field_eq_zero_of_vacuum (latVacuumGen L)
    (YfullGen L hEven hPos (TrecGen L v) - deriv (YfullGen L hEven hPos v))
    (Function.uncurry (wordStateLatGen L))
    (Function.uncurry (fun l α => YwordLatGen L l α))
    (fun lα => hloc lα.1 lα.2)
    (fun lα => YwordLatGen_vacuum_base L lα.1 lα.2)
    (fun lα q hq => YwordLatGen_vacuum_neg L lα.1 lα.2 hq)
    hAvac (wordStateLatGen_span L)
  rwa [sub_eq_zero] at hz

/-- **VOA3** (`translation` field): `YfullGen (mode (YfullGen ω) 0 v) = ∂_z YfullGen v`. -/
theorem YfullGen_translation_omega (hEven : L.Even) (hPos : L.PosDef) (v : LatModuleGen L) :
    YfullGen L hEven hPos (mode (YfullGen L hEven hPos (omegaLatGen L)) 0 v)
      = deriv (YfullGen L hEven hPos v) := by
  rw [mode_YfullGen_omega_zero L hEven hPos]; exact YfullGen_translation L hEven hPos v

/-! ## §C  VOA2 — `L₀ = mode (YfullGen ω) 1 = sugFieldGen(-2)`. -/

/-- `mode (YfullGen ω) 1 = sugFieldGen(-2)`. -/
theorem mode_YfullGen_omega_one (hEven : L.Even) (hPos : L.PosDef) :
    mode (YfullGen L hEven hPos (omegaLatGen L)) 1 = sugFieldGen L (-2) := by
  rw [mode_apply, show (-(1 : ℤ) - 1) = -2 from by ring, YfullGen_omega_eq]

/-- `sugFieldGen(-2)` acts as `(w + ½⟨α,α⟩)` on `mkEα α p`, `p ∈ gradingWN (rank L) w`: the boson `L₀`
gives `w`, the charge zero-mode `γ(0) = 0` drops out, and the `ZfZf` term gives `halfNorm α`. -/
theorem sugFieldGen_neg_two_bigradα (hEven : L.Even) (hPos : L.PosDef) {w : ℕ} {α : L.carrier}
    {p : FockN (rank L)} (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    sugFieldGen L (-2) (mkEα L α p) = (((w : ℤ) + halfNorm L α : ℤ) : ℂ) • mkEα L α p := by
  rw [show mkEα L α p = latStateGen L p α from rfl, sugFieldGen_tmul L hPos,
    show (-(-2 : ℤ) - 2) = 0 from by ring, if_pos rfl,
    LvirN_zero_gradingWN (rank L) 1 one_ne_zero hp, chargeOsc_zero, LinearMap.zero_apply,
    show latStateGen L (0 : FockN (rank L)) α = 0 from by rw [latStateGen, TensorProduct.zero_tmul],
    add_zero,
    show latStateGen L ((w : ℂ) • p) α = (w : ℂ) • latStateGen L p α from by
      rw [latStateGen, latStateGen, TensorProduct.smul_tmul'],
    show ((1 / 2 : ℂ) * ((L.form α α : ℤ) : ℂ)) • latStateGen L p α
        = ((halfNorm L α : ℤ) : ℂ) • latStateGen L p α from by
      congr 1
      have h2 := two_halfNorm L hEven α
      rw [show ((L.form α α : ℤ) : ℂ) = ((2 * halfNorm L α : ℤ) : ℂ) from by rw [h2]]
      push_cast; ring,
    ← add_smul,
    show (w : ℂ) + ((halfNorm L α : ℤ) : ℂ) = (((w : ℤ) + halfNorm L α : ℤ) : ℂ) from by push_cast; ring]

/-- `sugFieldGen(-2)` acts as the scalar `k` on every `bigradα p'` with `p' ∈ fiberPosGen k`. -/
theorem sugFieldGen_neg_two_bigradα_fiber (hEven : L.Even) (hPos : L.PosDef) (k : ℤ)
    (p' : ℤ × L.carrier) (hp' : p' ∈ fiberPosGen L k)
    {x : LatModuleGen L} (hx : x ∈ bigradα L p') : sugFieldGen L (-2) x = (k : ℂ) • x := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨hfib, hpos⟩ := hp'
  obtain ⟨w, hw⟩ : ∃ w : ℕ, p'.1 = (w : ℤ) := ⟨p'.1.toNat, by omega⟩
  have hqW : q ∈ HeisenbergN.gradingWN (rank L) w := by
    rw [hw, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hq; exact hq
  rw [sugFieldGen_neg_two_bigradα L hEven hPos hqW]
  congr 1
  rw [← hfib, hw]

/-- **VOA2** (`L0_grading`): `mode (YfullGen ω) 1 v = n•v` for `v ∈ gradingLatGen n`. -/
theorem YfullGen_L0_grading (hEven : L.Even) (hPos : L.PosDef) {n : ℤ} (v : LatModuleGen L)
    (hv : v ∈ gradingLatGen L n) :
    mode (YfullGen L hEven hPos (omegaLatGen L)) 1 v = (n : ℂ) • v := by
  rw [mode_YfullGen_omega_one L hEven hPos]
  have hker : v ∈ LinearMap.ker (sugFieldGen L (-2) - (n : ℂ) • LinearMap.id) := by
    refine (?_ : gradingLatGen L n ≤ LinearMap.ker (sugFieldGen L (-2) - (n : ℂ) • LinearMap.id)) hv
    rw [gradingLatGen_eq_biSup_pos L hEven hPos n]
    refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sugFieldGen_neg_two_bigradα_fiber L hEven hPos n p' hp' hx, sub_self]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at hker
  exact hker

end VOA.LatGen
