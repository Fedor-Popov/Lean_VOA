import VOA.Classification.COne.OrbSglData
import VOA.Classification.COne.OrbSglFock
import VOA.Classification.COne.PlusSplitSignCharacter

/-!
# OrbSgl (8): the zero mode of `v'` on the five relevant tops

* `V_{L+λ_j}` (`|j| < 4`), top `e^{λ_j}`: only the charge-`0` part `primeFock` contributes, with
  `o(h(-i₁-1)⋯𝟙) = ∏ (-1)^{iₗ} t`, `t² = j²/8`:
  `j = 1`: `27/1342177280`; `j = 2`: `0`; `j = 3`: `-1701/1342177280`.
* `V_L⁻`, top `h(-1)𝟙`: `o(v') h = 0` (kernel check of the oscillator product; the charged
  parts `e^{±2β}₍₁₅₎h` vanish by positivity).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational LatMod OrbC2g OrbC2h OrbC2c OrbC2e OrbC2f PlusC2 PlusC2Eval PlusUnitary

local notation "V8" => V2m 4 four_ge_one

theorem evaluate_primeData : evaluate primeData =
    (27 : ℂ) • latChargeGen (latP 4) ((-2 : ℤ) : (latP 4).carrier) + ls 4 primeFock +
      (27 : ℂ) • latChargeGen (latP 4) ((2 : ℤ) : (latP 4).carrier) := by
  simp only [primeData, evaluate, evRc_liftR, sector, LinearMap.coe_mk, AddHom.coe_mk,
    evRc_cons, evRc_nil, add_zero, evalWordC_nil]
  rw [latStateGen_csmul, latStateGen_csmul]
  push_cast
  rw [add_assoc]
  rfl

theorem charge_mem_grading (k : ℤ) (hk : k = 2 ∨ k = -2) :
    latChargeGen (latP 4) (k : (latP 4).carrier) ∈ (V8).grading 16 := by
  rw [V2m_grading_eq]
  have := latChargeGen_mem_grading (latP 4) (k : (latP 4).carrier)
  have hn : LatGen.halfNorm (latP 4) (k : (latP 4).carrier) = 16 := by
    rcases hk with rfl | rfl <;> simp only [LatGen.halfNorm, latP_form] <;> norm_num
  rwa [hn] at this

theorem oMod_charge_latticeTop (j : ℤ) (hj : |j| < 4) (k : ℤ) (hk : k = 2 ∨ k = -2) :
    oMod (latticeModule 4 four_ge_one j) (latChargeGen (latP 4) (k : (latP 4).carrier))
      (latVacuumGen (latP 4)) = 0 := by
  rw [oMod_homogeneous _ (charge_mem_grading k hk), mode_apply, latVacuumGen,
    show (0 : (latP 4).carrier) = ((0 : ℤ) : (latP 4).carrier) from rfl, latE_vac, if_neg]
  obtain ⟨h1, h2⟩ := abs_lt.mp hj
  rcases hk with rfl | rfl <;> push_cast <;> omega

theorem primeFock_even : ∀ x ∈ primeFock, x.2.length % 2 = 0 := by decide +kernel

/-- The zero mode of `v'` on `e^{λ_j}`. -/
theorem oMod_prime_latticeTop (j : ℤ) (hj : |j| < 4) :
    oMod (latticeModule 4 four_ge_one j) (evaluate primeData) (latVacuumGen (latP 4)) =
      (((evenVal (((j ^ 2 : ℤ) : ℚ) / (2 * (4 : ℕ))) primeFock : ℚ)) : ℂ) •
        latVacuumGen (latP 4) := by
  have hj' : |j| ≤ ((4 : ℕ) : ℤ) := by push_cast; omega
  rw [evaluate_primeData, map_add, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    oMod_charge_latticeTop j hj _ (Or.inr rfl), oMod_charge_latticeTop j hj _ (Or.inl rfl),
    smul_zero, zero_add, add_zero,
    oMod_ls_top 4 four_ge_one _ (latticeModule_isLowestWeight 4 four_ge_one j hj')
      (latticeModule_vacuum_mem 4 four_ge_one j) (oMod_boson_latticeTop 4 four_ge_one j)
      primeFock,
    fockVal_eq_evenVal (chi_zero_sq 4 four_ge_one j) primeFock primeFock_even]

theorem evenVal_one : evenVal ((((1 : ℤ) ^ 2 : ℤ) : ℚ) / (2 * (4 : ℕ))) primeFock =
    27 / 1342177280 := by decide +kernel

theorem evenVal_two : evenVal ((((2 : ℤ) ^ 2 : ℤ) : ℚ) / (2 * (4 : ℕ))) primeFock = 0 := by
  decide +kernel

theorem evenVal_three : evenVal ((((3 : ℤ) ^ 2 : ℤ) : ℚ) / (2 * (4 : ℕ))) primeFock =
    -1701 / 1342177280 := by decide +kernel

/-! ## The sign module -/

theorem primeFock_h : normR (polyActW primeFock (-16) [(1, [0])]) = [] := by decide +kernel

/-- `v'₍₁₅₎ h(-1)𝟙 = 0`. -/
theorem prime_smul_boson :
    (V8).smul (evaluate primeData) 15 (bosonState (latP 4) (a0 4)) = 0 := by
  rw [evaluate_primeData, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_left,
    PlusCharacterTable.charge_positive_boson 4 four_ge_one _ 15 (by norm_num),
    PlusCharacterTable.charge_positive_boson 4 four_ge_one _ 15 (by norm_num), smul_zero, zero_add, add_zero,
    bosonState_eq_evR, ls, V2m_smul_evR_W, ← evR_normR,
    show (-(15 : ℤ) - 1) = -16 by norm_num, primeFock_h, evR_nil]
  simp [latStateGen]

end VOA.Classification.COne.OrbSgl
