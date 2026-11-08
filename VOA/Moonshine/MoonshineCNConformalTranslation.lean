import VOA.Moonshine.MoonshineCNVirasoro

/-!
# Complex-frame lattice construction: ConformalTranslation

Structural adaptation of `LatticeGenL0Translation` using a complex bilinear
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

noncomputable def sugawaraTranslation : End ℂ (LatModuleGen L) := mode (frameSugawaraField F) 0


theorem sugawaraTranslation_eq : sugawaraTranslation F = frameSugawaraField F (-1) := by
  rw [sugawaraTranslation, mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring]


theorem sugawaraTranslation_eq_frameTranslation  : sugawaraTranslation F = frameTranslation F := by
  rw [sugawaraTranslation_eq]
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
            frameSugawaraField_tmul F, frameTranslation_tmul, if_neg (by norm_num : ¬ (-1 : ℤ) = -2),
            add_zero, show (-(-1 : ℤ) - 2) = -1 from by ring]


theorem mode_frameStateField_omega_zero (hEven : L.Even)  :
    mode (frameStateField F hEven (latticeConformalVector L)) 0 = frameTranslation F := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring, frameStateField_omega_eq, ← sugawaraTranslation_eq,
    sugawaraTranslation_eq_frameTranslation F]


theorem frameStateField_one_vac (hEven : L.Even)  (v : LatModuleGen L) :
    (frameStateField F hEven v) 1 (latVacuumGen L) = frameTranslation F v := by
  have h := congrArg (fun (R : End ℂ (LatModuleGen L)) => R (latVacuumGen L))
    (frameStateField_DCov F hEven v 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [frameTranslation_vacuum, map_zero, sub_zero, frameStateField_cre0, show ((0 : ℤ) + 1) = 1 from by ring,
    one_zsmul] at h
  exact h.symm


theorem frameStateField_translation (hEven : L.Even)  (v : LatModuleGen L) :
    frameStateField F hEven (frameTranslation F v) = deriv (frameStateField F hEven v) := by
  have hGcov : Reconstruction.DCovariant (frameTranslation F) (deriv (frameStateField F hEven v)) :=
    Reconstruction.DCovariant.deriv' (frameStateField_DCov F hEven v)
  have hGneg : ∀ q : ℤ, q < 0 → (deriv (frameStateField F hEven v)) q (latVacuumGen L) = 0 := by
    intro q hq
    rw [deriv_apply]
    show ((q + 1 : ℤ) • (frameStateField F hEven v) (q + 1)) (latVacuumGen L) = 0
    rw [← Int.cast_smul_eq_zsmul ℂ (q + 1), LinearMap.smul_apply]
    by_cases hq1 : q + 1 < 0
    · rw [frameStateField_creneg F hEven v hq1, smul_zero]
    · rw [show q + 1 = (0 : ℤ) from by omega, Int.cast_zero, zero_smul]
  have hbase : (frameStateField F hEven (frameTranslation F v)) 0 (latVacuumGen L)
      = (deriv (frameStateField F hEven v)) 0 (latVacuumGen L) := by
    rw [frameStateField_cre0, deriv_apply]
    show frameTranslation F v = ((0 + 1 : ℤ) • (frameStateField F hEven v) (0 + 1)) (latVacuumGen L)
    rw [show (0 + 1 : ℤ) = 1 from by ring, one_zsmul, frameStateField_one_vac]
  have hAvac : ∀ p : ℤ,
      (frameStateField F hEven (frameTranslation F v) - deriv (frameStateField F hEven v)) p (latVacuumGen L) = 0 := by
    intro p
    show ((frameStateField F hEven (frameTranslation F v)) p - (deriv (frameStateField F hEven v)) p)
      (latVacuumGen L) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (frameStateField_DCov F hEven (frameTranslation F v)) hGcov
      (frameTranslation_vacuum F) hbase
      (fun q hq => frameStateField_creneg F hEven (frameTranslation F v) hq) hGneg p
  have hloc : ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Local (frameStateField F hEven (frameTranslation F v) - deriv (frameStateField F hEven v))
        (frameWordField F l α) := by
    intro l α
    have h1 : Local (frameStateField F hEven (frameTranslation F v)) (frameWordField F l α) := by
      rw [← frameStateField_word F hEven l α]
      exact frameStateField_local F hEven (frameTranslation F v) (frameWordState L l α)
    have h2 : Local (deriv (frameStateField F hEven v)) (frameWordField F l α) := by
      have hv : Local (frameStateField F hEven v) (frameWordField F l α) := by
        rw [← frameStateField_word F hEven l α]
        exact frameStateField_local F hEven v (frameWordState L l α)
      exact Local.derivL hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (deriv (frameStateField F hEven v))]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hz := Reconstruction.field_eq_zero_of_vacuum (latVacuumGen L)
    (frameStateField F hEven (frameTranslation F v) - deriv (frameStateField F hEven v))
    (Function.uncurry (frameWordState L))
    (Function.uncurry (fun l α => frameWordField F l α))
    (fun lα => hloc lα.1 lα.2)
    (fun lα => frameWordField_vacuum_base F lα.1 lα.2)
    (fun lα q hq => frameWordField_vacuum_neg F lα.1 lα.2 hq)
    hAvac (frameWordState_span L)
  rwa [sub_eq_zero] at hz


theorem frameStateField_translation_omega (hEven : L.Even)  (v : LatModuleGen L) :
    frameStateField F hEven (mode (frameStateField F hEven (latticeConformalVector L)) 0 v)
      = deriv (frameStateField F hEven v) := by
  rw [mode_frameStateField_omega_zero F hEven]; exact frameStateField_translation F hEven v


theorem mode_frameStateField_omega_one (hEven : L.Even)  :
    mode (frameStateField F hEven (latticeConformalVector L)) 1 = frameSugawaraField F (-2) := by
  rw [mode_apply, show (-(1 : ℤ) - 1) = -2 from by ring, frameStateField_omega_eq]


theorem frameSugawaraField_neg_two_bigradα (hEven : L.Even)  {w : ℕ} {α : L.carrier}
    {p : FockN (rank L)} (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    frameSugawaraField F (-2) (mkEα L α p) = (((w : ℤ) + halfNorm L α : ℤ) : ℂ) • mkEα L α p := by
  rw [show mkEα L α p = latStateGen L p α from rfl, frameSugawaraField_tmul F,
    show (-(-2 : ℤ) - 2) = 0 from by ring, if_pos rfl,
    LvirN_zero_gradingWN (rank L) 1 one_ne_zero hp, frameOscillator_zero, LinearMap.zero_apply,
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


theorem frameSugawaraField_neg_two_bigradα_fiber (hEven : L.Even)  (k : ℤ)
    (p' : ℤ × L.carrier) (hp' : p' ∈ fiberPosGen L k)
    {x : LatModuleGen L} (hx : x ∈ bigradα L p') : frameSugawaraField F (-2) x = (k : ℂ) • x := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨hfib, hpos⟩ := hp'
  obtain ⟨w, hw⟩ : ∃ w : ℕ, p'.1 = (w : ℤ) := ⟨p'.1.toNat, by omega⟩
  have hqW : q ∈ HeisenbergN.gradingWN (rank L) w := by
    rw [hw, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hq; exact hq
  rw [frameSugawaraField_neg_two_bigradα F hEven hqW]
  congr 1
  rw [← hfib, hw]


theorem frameStateField_L0_grading (hEven : L.Even)  {n : ℤ} (v : LatModuleGen L)
    (hv : v ∈ gradingLatGen L n) :
    mode (frameStateField F hEven (latticeConformalVector L)) 1 v = (n : ℂ) • v := by
  rw [mode_frameStateField_omega_one F hEven]
  have hker : v ∈ LinearMap.ker (frameSugawaraField F (-2) - (n : ℂ) • LinearMap.id) := by
    refine (?_ : gradingLatGen L n ≤ LinearMap.ker (frameSugawaraField F (-2) - (n : ℂ) • LinearMap.id)) hv
    rw [latticeWeightGrading_eq_positiveFiber L n]
    refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      frameSugawaraField_neg_two_bigradα_fiber F hEven n p' hp' hx, sub_self]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at hker
  exact hker


end VOA.Moonshine.ConwayNorton
