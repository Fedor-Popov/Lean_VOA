import VOA.Moonshine.MoonshineCNSugawara

/-!
# Complex-frame lattice construction: Virasoro

Structural adaptation of `LatticeGenVirasoro` using a complex bilinear
frame. The carrier, formal-distribution conventions and finite-support proofs
are preserved. No positive-definiteness hypothesis is introduced.
-/

set_option maxHeartbeats 1600000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen Reconstruction

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

noncomputable def frameVirasoroMode (n : ℤ) : End ℂ (LatModuleGen L) := frameSugawaraField F (-n - 2)


theorem frameVirasoroMode_tmul  (n : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    frameVirasoroMode F n (latStateGen L q γ)
      = latStateGen L (HeisenbergN.LvirN (rank L) 1 n q) γ
        + latStateGen L (frameOscillator F γ n q) γ
        + (if n = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • latStateGen L q γ else 0) := by
  rw [frameVirasoroMode, frameSugawaraField_tmul F, show (-(-n - 2) - 2 : ℤ) = n from by ring]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos (by omega : (-n - 2 : ℤ) = -2)]
  · rw [if_neg hn, if_neg (by omega : ¬ (-n - 2 : ℤ) = -2)]


theorem mode_frameStateField_omega (hEven : L.Even)  (j : ℤ) :
    mode (frameStateField F hEven (latticeConformalVector L)) j = frameSugawaraField F (-j - 1) := by
  rw [mode_apply, frameStateField_omega_eq]


theorem mode_frameStateField_omega_eq_frameVirasoroMode (hEven : L.Even)  (n : ℤ) :
    mode (frameStateField F hEven (latticeConformalVector L)) (n + 1) = frameVirasoroMode F n := by
  rw [mode_frameStateField_omega, frameVirasoroMode, show (-(n + 1) - 1 : ℤ) = -n - 2 from by ring]


theorem frameOscillator_apply_sum (γ : L.carrier) (n : ℤ) (y : FockN (rank L)) :
    frameOscillator F γ n y = ∑ a : Fin (rank L), frameCoordinate F γ a • HeisenbergN.oscN (rank L) 1 a n y := by
  rw [frameOscillator_eq_sum, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => rfl)


theorem LvirN_frameOscillator (γ : L.carrier) (m n : ℤ) (y : FockN (rank L)) :
    HeisenbergN.LvirN (rank L) 1 m (frameOscillator F γ n y)
      = (-(n : ℂ)) • frameOscillator F γ (m + n) y
        + frameOscillator F γ n (HeisenbergN.LvirN (rank L) 1 m y) := by
  rw [frameOscillator_apply_sum, map_sum,
    Finset.sum_congr rfl (fun a _ => by
      rw [map_smul, HeisenbergN.LvirN_oscN (rank L) 1 one_ne_zero a m n y, smul_add,
        smul_comm (frameCoordinate F γ a) (-(n : ℂ))]),
    Finset.sum_add_distrib, ← Finset.smul_sum, ← frameOscillator_apply_sum, ← frameOscillator_apply_sum]


theorem shiftedBoson_virasoro_commutator (L : IntegralLattice) (m n : ℤ) (q : FockN (rank L)) (cL mf : ℂ)
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


theorem frameVirasoroMode_comm_tmul  (m n : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    (frameVirasoroMode F m * frameVirasoroMode F n - frameVirasoroMode F n * frameVirasoroMode F m) (latStateGen L q γ)
      = (((m : ℂ) - n) • frameVirasoroMode F (m + n)
          + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ)) • (1 : End ℂ (LatModuleGen L))
             else 0)) (latStateGen L q γ) := by
  classical
  set Lv := HeisenbergN.LvirN (rank L) 1 with hLv
  set av := frameOscillator F γ with hav
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
    LvirN_frameOscillator F γ s t y
  have haa : ∀ (s t : ℤ) (y : FockN (rank L)),
      av s (av t y) - av t (av s y) = (if s + t = 0 then ((L.form γ γ : ℤ) : ℂ) * (s : ℂ) else 0) • y := by
    intro s t y
    have h := congrArg (fun (T : End ℂ (FockN (rank L))) => T y)
      (frameOscillator_commutator F γ γ s t)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at h
    exact h
  set Op : ℤ → FockN (rank L) → FockN (rank L) :=
    fun s y => Lv s y + av s y + (if s = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • y else 0)
    with hOp
  have hLLOp : ∀ (s : ℤ) (y : FockN (rank L)),
      frameVirasoroMode F s (latStateGen L y γ) = latStateGen L (Op s y) γ := by
    intro s y
    rw [frameVirasoroMode_tmul F, hOp]
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
    shiftedBoson_virasoro_commutator L m n q (rank L : ℂ) ((L.form γ γ : ℤ) : ℂ) Lv av hLL hLa haa Op hOp
  rw [hbos, map_add, map_smul]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      show (rank L : ℂ) * ((m : ℂ) ^ 3 - m) / 12 = ((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ) from by ring]
    rfl
  · rw [if_neg hmn, if_neg hmn, map_zero, add_zero, LinearMap.zero_apply, add_zero]
    rfl


theorem frameStateField_virasoro (hEven : L.Even)  (m n : ℤ) :
    ⁅mode (frameStateField F hEven (latticeConformalVector L)) (m + 1),
      mode (frameStateField F hEven (latticeConformalVector L)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (frameStateField F hEven (latticeConformalVector L)) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (rank L : ℂ)) • (1 : End ℂ (LatModuleGen L))
           else 0) := by
  rw [mode_frameStateField_omega_eq_frameVirasoroMode, mode_frameStateField_omega_eq_frameVirasoroMode,
    show m + n + 1 = (m + n) + 1 from by ring, mode_frameStateField_omega_eq_frameVirasoroMode,
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
            frameVirasoroMode_comm_tmul F]


end VOA.Moonshine.ConwayNorton
