/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenSugawaraTmul

/-!
# The Virasoro relation for the general even-lattice VOA, central charge `c = rank L`

The lattice Virasoro modes `Lₙ = mode (YfullGen ω)(n+1) = sugFieldGen(-n-2)`, the pure-operator
Virasoro core `hbos_core_vec` (boson `c = rank L` central term with the charge-sector contribution
absorbed into the `(m−n)Lₘ₊ₙ` zero-mode), and the target VOA1 axiom `YfullGen_virasoro` with
`centralCharge = rank L`.  Cross-charge lift of A₁'s `LatticeVOAInstance` (lines 634-803).

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §A  The lattice Virasoro mode operator `LLGen`. -/

/-- The lattice Virasoro mode operator `LLGen n := sugFieldGen(-n-2) = mode (YfullGen ω)(n+1)`. -/
noncomputable def LLGen (n : ℤ) : End ℂ (LatModuleGen L) := sugFieldGen L (-n - 2)

/-- `LLGen n` on a basis vector `q ⊗ e^γ`: the boson Virasoro `Lₙ`, plus the charge `γ(n)`, plus the
`[n=0]·½⟨γ,γ⟩` zero-mode. -/
theorem LLGen_tmul (hPos : L.PosDef) (n : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    LLGen L n (latStateGen L q γ)
      = latStateGen L (HeisenbergN.LvirN (rank L) 1 n q) γ
        + latStateGen L (chargeOsc L γ n q) γ
        + (if n = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • latStateGen L q γ else 0) := by
  rw [LLGen, sugFieldGen_tmul L hPos, show (-(-n - 2) - 2 : ℤ) = n from by ring]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos (by omega : (-n - 2 : ℤ) = -2)]
  · rw [if_neg hn, if_neg (by omega : ¬ (-n - 2 : ℤ) = -2)]

/-- `mode (YfullGen ω)(j) = sugFieldGen(-j-1)`. -/
theorem mode_YfullGen_omega (hEven : L.Even) (hPos : L.PosDef) (j : ℤ) :
    mode (YfullGen L hEven hPos (omegaLatGen L)) j = sugFieldGen L (-j - 1) := by
  rw [mode_apply, YfullGen_omega_eq]

/-- `mode (YfullGen ω)(n+1) = LLGen n`. -/
theorem mode_YfullGen_omega_eq_LLGen (hEven : L.Even) (hPos : L.PosDef) (n : ℤ) :
    mode (YfullGen L hEven hPos (omegaLatGen L)) (n + 1) = LLGen L n := by
  rw [mode_YfullGen_omega, LLGen, show (-(n + 1) - 1 : ℤ) = -n - 2 from by ring]

/-! ## §B  The Virasoro–charge commutator and the pure-operator Virasoro core. -/

/-- The charge oscillator on a basis vector as the frame sum. -/
theorem chargeOsc_apply_sum (γ : L.carrier) (n : ℤ) (y : FockN (rank L)) :
    chargeOsc L γ n y = ∑ a : Fin (rank L), chargeCoord L γ a • HeisenbergN.oscN (rank L) 1 a n y := by
  rw [chargeOsc_eq_sum, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => rfl)

/-- **`[Lₘ, γ(n)] = -n·γ(m+n)`** in vector form (the general-`m` Virasoro–charge commutator). -/
theorem LvirN_chargeOsc (γ : L.carrier) (m n : ℤ) (y : FockN (rank L)) :
    HeisenbergN.LvirN (rank L) 1 m (chargeOsc L γ n y)
      = (-(n : ℂ)) • chargeOsc L γ (m + n) y
        + chargeOsc L γ n (HeisenbergN.LvirN (rank L) 1 m y) := by
  rw [chargeOsc_apply_sum, map_sum,
    Finset.sum_congr rfl (fun a _ => by
      rw [map_smul, HeisenbergN.LvirN_oscN (rank L) 1 one_ne_zero a m n y, smul_add,
        smul_comm (chargeCoord L γ a) (-(n : ℂ))]),
    Finset.sum_add_distrib, ← Finset.smul_sum, ← chargeOsc_apply_sum, ← chargeOsc_apply_sum]

/-- **The pure boson-operator core** of the lattice Sugawara Virasoro relation, central charge `cL`.
With `Op s y = Lv s y + av s y + δ_{s,0}·½·mf·y`, `[Op m, Op n] = (m−n)Op(m+n) + δ_{m+n,0}·cL·(m³−m)/12`:
the boson `cL` central term, with the charge-sector `mf·m·δ` absorbed into the `(m−n)Op(m+n)`
zero-mode (whence central charge exactly `cL`). -/
theorem hbos_core_vec (m n : ℤ) (q : FockN (rank L)) (cL mf : ℂ)
    (Lv : ℤ → End ℂ (FockN (rank L))) (av : ℤ → End ℂ (FockN (rank L)))
    (hLL : ∀ (s t : ℤ) (y : FockN (rank L)),
      Lv s (Lv t y) - Lv t (Lv s y)
        = ((s : ℂ) - t) • Lv (s + t) y
          + (if s + t = 0 then cL * ((s : ℂ) ^ 3 - s) / 12 else 0) • y)
    (hLa : ∀ (s t : ℤ) (y : FockN (rank L)),
      Lv s (av t y) = (-(t : ℂ)) • av (s + t) y + av t (Lv s y))
    (haa : ∀ (s t : ℤ) (y : FockN (rank L)),
      av s (av t y) - av t (av s y) = (if s + t = 0 then mf * (s : ℂ) else 0) • y)
    (Op : ℤ → FockN (rank L) → FockN (rank L))
    (hOp : Op = fun s y => Lv s y + av s y + (if s = 0 then ((1 / 2 : ℂ) * mf) • y else 0)) :
    Op m (Op n q) - Op n (Op m q)
      = ((m : ℂ) - (n : ℂ)) • Op (m + n) q
        + (if m + n = 0 then (cL * ((m : ℂ) ^ 3 - (m : ℂ)) / 12) • q else 0) := by
  subst hOp
  simp only [map_add]
  have eLL : Lv m (Lv n q) = Lv n (Lv m q) + (((m : ℂ) - n) • Lv (m + n) q
      + (if m + n = 0 then cL * ((m : ℂ) ^ 3 - m) / 12 else 0) • q) := by
    rw [← hLL m n q]; abel
  have eaa : av m (av n q) = av n (av m q) + (if m + n = 0 then mf * (m : ℂ) else 0) • q := by
    rw [← haa m n q]; abel
  have eLan : Lv m (av n q) = (-(n : ℂ)) • av (m + n) q + av n (Lv m q) := hLa m n q
  have eLam : Lv n (av m q) = (-(m : ℂ)) • av (m + n) q + av m (Lv n q) := by
    have := hLa n m q
    rwa [add_comm n m] at this
  rw [eLL, eLan, eLam, eaa]
  by_cases hmn : m + n = 0
  · by_cases hm0 : m = 0
    · have hn0 : n = 0 := by omega
      subst hm0; subst hn0
      simp only [if_pos, map_smul]
      push_cast
      module
    · have hn0 : n ≠ 0 := by omega
      have hnm : (n : ℂ) = -(m : ℂ) := by
        have : n = -m := by omega
        rw [this]; push_cast; ring
      simp only [if_neg hm0, if_neg hn0, if_pos hmn, map_zero, add_zero]
      rw [hnm]
      module
  · by_cases hm0 : m = 0
    · have hn0 : n ≠ 0 := by omega
      simp only [if_neg hmn, if_neg hn0, if_pos hm0, map_zero, add_zero, map_smul]
      subst hm0
      module
    · by_cases hn0 : n = 0
      · simp only [if_neg hmn, if_neg hm0, if_pos hn0, map_zero, add_zero, map_smul]
        subst hn0
        module
      · simp only [if_neg hmn, if_neg hm0, if_neg hn0, map_zero, add_zero]
        module

/-! ## §C  The lattice Virasoro relation on a basis vector and the VOA1 axiom. -/

/-- **The lattice Sugawara Virasoro relation on a basis vector** `q ⊗ e^γ` (`c = rank L`). -/
theorem LLGen_comm_tmul (hPos : L.PosDef) (m n : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    (LLGen L m * LLGen L n - LLGen L n * LLGen L m) (latStateGen L q γ)
      = (((m : ℂ) - n) • LLGen L (m + n)
          + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ)) • (1 : End ℂ (LatModuleGen L))
             else 0)) (latStateGen L q γ) := by
  classical
  set Lv := HeisenbergN.LvirN (rank L) 1 with hLv
  set av := chargeOsc L γ with hav
  have hLL : ∀ (s t : ℤ) (y : FockN (rank L)),
      Lv s (Lv t y) - Lv t (Lv s y)
        = ((s : ℂ) - t) • Lv (s + t) y
          + (if s + t = 0 then (rank L : ℂ) * ((s : ℂ) ^ 3 - s) / 12 else 0) • y := by
    intro s t y
    have h := congrArg (fun (T : End ℂ (FockN (rank L))) => T y)
      (HeisenbergN.L_virasoroN (rank L) 1 one_ne_zero s t)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at h
    exact h
  have hLa : ∀ (s t : ℤ) (y : FockN (rank L)),
      Lv s (av t y) = (-(t : ℂ)) • av (s + t) y + av t (Lv s y) := fun s t y =>
    LvirN_chargeOsc L γ s t y
  have haa : ∀ (s t : ℤ) (y : FockN (rank L)),
      av s (av t y) - av t (av s y) = (if s + t = 0 then ((L.form γ γ : ℤ) : ℂ) * (s : ℂ) else 0) • y := by
    intro s t y
    have h := congrArg (fun (T : End ℂ (FockN (rank L))) => T y)
      (chargeOsc_comm L hPos γ γ s t)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at h
    exact h
  set Op : ℤ → FockN (rank L) → FockN (rank L) :=
    fun s y => Lv s y + av s y + (if s = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • y else 0)
    with hOp
  have hLLOp : ∀ (s : ℤ) (y : FockN (rank L)),
      LLGen L s (latStateGen L y γ) = latStateGen L (Op s y) γ := by
    intro s y
    rw [LLGen_tmul L hPos, hOp]
    simp only
    rw [show latStateGen L (Lv s y + av s y
          + (if s = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • y else 0)) γ
        = mkEα L γ (Lv s y + av s y
          + (if s = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • y else 0)) from rfl]
    simp only [map_add, apply_ite (mkEα L γ), map_zero]
    rfl
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hLLOp, hLLOp, hLLOp, hLLOp,
    LinearMap.add_apply, LinearMap.smul_apply, hLLOp]
  rw [show latStateGen L (Op m (Op n q)) γ - latStateGen L (Op n (Op m q)) γ
      = mkEα L γ (Op m (Op n q) - Op n (Op m q)) from by rw [map_sub]; rfl]
  have hbos : Op m (Op n q) - Op n (Op m q)
      = ((m : ℂ) - (n : ℂ)) • Op (m + n) q
        + (if m + n = 0 then ((rank L : ℂ) * ((m : ℂ) ^ 3 - (m : ℂ)) / 12) • q else 0) :=
    hbos_core_vec L m n q (rank L : ℂ) ((L.form γ γ : ℤ) : ℂ) Lv av hLL hLa haa Op hOp
  rw [hbos, map_add, map_smul]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      show (rank L : ℂ) * ((m : ℂ) ^ 3 - m) / 12 = ((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ) from by ring]
    rfl
  · rw [if_neg hmn, if_neg hmn, map_zero, add_zero, LinearMap.zero_apply, add_zero]
    rfl

/-- **VOA1 (conformal symmetry)** for the general even-lattice VOA, `centralCharge = rank L`. -/
theorem YfullGen_virasoro (hEven : L.Even) (hPos : L.PosDef) (m n : ℤ) :
    ⁅mode (YfullGen L hEven hPos (omegaLatGen L)) (m + 1),
      mode (YfullGen L hEven hPos (omegaLatGen L)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YfullGen L hEven hPos (omegaLatGen L)) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ)) • (1 : End ℂ (LatModuleGen L))
           else 0) := by
  rw [mode_YfullGen_omega_eq_LLGen, mode_YfullGen_omega_eq_LLGen,
    show m + n + 1 = (m + n) + 1 from by ring, mode_YfullGen_omega_eq_LLGen,
    LieRing.of_associative_ring_bracket]
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y1 y2 hy1 hy2 => rw [map_add, map_add, hy1, hy2]
  | tmul q g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; rw [map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add]; rw [map_add, map_add, h1, h2]
      | single c b =>
          rw [(Finsupp.smul_single_one c b).symm,
            show (Finsupp.single c 1 : L.carrier →₀ ℂ) = eGen L c from rfl]
          erw [TensorProduct.tmul_smul]
          rw [map_smul, map_smul, show q ⊗ₜ[ℂ] eGen L c = latStateGen L q c from rfl,
            LLGen_comm_tmul L hPos]

end VOA.LatGen
