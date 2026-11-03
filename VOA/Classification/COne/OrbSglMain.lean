import VOA.Classification.COne.OrbSglTransport
import VOA.Classification.COne.OrbSglValues
import VOA.Classification.COne.OrbSglCws

/-!
# OrbSgl (10): `TetraOddSingleValues` and `CubicZhuDimensionBound`

Transport along the explicit `tetraEquiv : (V₈⁺)^σ ≃ W` (ambient map `scaleMorph 1 2`):

* `v' = wsP` (weight-16 primary, cubic-fixed) maps to `b v` (`prim_sixteen`), `b ≠ 0`;
  `u' = weightNine` maps to `a u` (`prim_nine`), `a ≠ 0`;
* `u'₍₁₅₎ v' = c' u'` with `c' = -190512/5` (`nine_smul_wsP`), hence `b c = c'` and `c ≠ 0`;
* characters from the `V₈⁺` tops (`tetra_character_of_plus_top`): `ψ([v]) = b⁻¹ s_λ` with
  `s_1 = 0` (`V_L⁻`), `s_{1/4} = 0`, `s_{1/16} = 27/1342177280`, `s_{9/16} = -1701/1342177280`
  (`V_{L+λ_j}`), and `s_λ ≠ c' q(λ)` (exact rational arithmetic).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2 OrbZhu OrbOdd
  OrbC2e OrbC2f PlusCharacterTable ConverseUniverse PlusC2 PlusSplitting PlusUnitary OrbRat5
  VOA.LatGen VOA.LatGen.Triplet LatMod Polynomial

/-! ## The transported seeds -/

/-- `v'` as a cubic-fixed vector. -/
def wsF : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
  ⟨wsP, (mem_orbifold_zpowers_iff _ _).mpr wsP_fixed⟩

theorem wsF_prim : tetraEquiv wsF ∈ prim Wt 16 := by
  rw [mem_prim]
  refine ⟨voaHom_map_grading tetraEquiv_hom tetraEquiv_omega wsP_mem, fun m => ?_⟩
  have ht := voaHom_map_L tetraEquiv_hom tetraEquiv_omega ((m : ℤ) + 1) wsF
  simp only [LinearEquiv.coe_coe] at ht
  rw [← ht]
  have h := wsP_primary (m + 1) (by omega)
  push_cast at h
  have h' : (orbifoldVOA (Subgroup.zpowers plusCubic)).L ((m : ℤ) + 1) wsF = 0 :=
    Subtype.ext h
  rw [h', tetraEquiv.map_zero]

theorem nineF_prim : tetraEquiv fixedNine ∈ prim Wt 9 := by
  rw [mem_prim]
  refine ⟨voaHom_map_grading tetraEquiv_hom tetraEquiv_omega fixedNine_nonzero_primary.2.1,
    fun m => ?_⟩
  have ht := voaHom_map_L tetraEquiv_hom tetraEquiv_omega ((m : ℤ) + 1) fixedNine
  simp only [LinearEquiv.coe_coe] at ht
  rw [← ht, fixedNine_nonzero_primary.2.2 _ (by omega), tetraEquiv.map_zero]

theorem nine_smul_wsF :
    (orbifoldVOA (Subgroup.zpowers plusCubic)).smul fixedNine 15 wsF =
      ((-190512 / 5 : ℚ) : ℂ) • fixedNine :=
  Subtype.ext nine_smul_wsP

/-! ## Rational evaluation of `q` -/

/-- Horner evaluation of a `PL` over `ℚ`. -/
def evalQ (r : ℚ) : PL → ℚ
  | [] => 0
  | x :: a => x + r * evalQ r a

theorem zp_eval (r : ℚ) : ∀ a : PL, (zp a).eval ((r : ℚ) : ℂ) = ((evalQ r a : ℚ) : ℂ)
  | [] => by simp [zp, evalQ]
  | x :: a => by
    rw [zp, eval_add, eval_C, eval_mul, eval_X, zp_eval r a, evalQ]
    push_cast; ring

theorem q_vals : evalQ 1 qList = 5 / 75209904 ∧ evalQ (1/4) qList = 215 / 15969569616 ∧
    evalQ (1/16) qList = -1283 / 420906795008 ∧ evalQ (9/16) qList = -3651 / 420906795008 := by
  decide +kernel

/-! ## The lattice characters with values -/

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- The value of a character built from a `V₈⁺`-top on `[v]`, through `v = b⁻¹ τ(v')`. -/
theorem char_value_tetraV {b : ℂ} (hb : tetraEquiv wsF = b • tetraV) (hb0 : b ≠ 0)
    (N : OrdVModule (V2mPlus 4 four_ge_one) M) {x : M} (hx0 : x ≠ 0) {s : ℂ}
    (hs : oMod N wsP x = s • x) (ψ : VOA.A Wt →ₗ[ℂ] ℂ)
    (hval : ∀ (k : ℤ) (a : (orbifold tetra).carrier), a ∈ Wt.grading k →
        ψ (VOA.mk Wt a) • x = oMod N ((tetraEquiv.symm a :
          (orbifold (Subgroup.zpowers plusCubic)).carrier) : VP 4 four_ge_one) x) :
    ψ (VOA.mk Wt tetraV) = b⁻¹ * s := by
  have hv : tetraEquiv.symm tetraV = b⁻¹ • wsF := by
    rw [← LinearEquiv.symm_apply_apply tetraEquiv wsF, hb, map_smul, smul_smul,
      inv_mul_cancel₀ hb0, one_smul]
  have h := hval 16 tetraV tetraV_mem
  rw [hv, Submodule.coe_smul, map_smul, LinearMap.smul_apply] at h
  change _ = b⁻¹ • oMod N wsP x at h
  rw [hs, smul_smul] at h
  have h2 : (ψ (VOA.mk Wt tetraV) - b⁻¹ * s) • x = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx0)

/-- The `V_{L+λ_j}` character (`|j| < 4`) with its value on `[v]`. -/
theorem lattice_char (j : ℤ) (hj : |j| < 4) {b : ℂ} (hb : tetraEquiv wsF = b • tetraV)
    (hb0 : b ≠ 0) :
    ∃ ψ : VOA.A Wt →ₗ[ℂ] ℂ, (∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q) ∧
      ψ (VOA.mk Wt Wt.vacuum) = 1 ∧
      ψ (VOA.mk Wt Wt.conformalVector) = ((((j : ℝ) ^ 2 / (4 * (4 : ℕ)) : ℝ)) : ℂ) ∧
      ψ (VOA.mk Wt tetraV) =
        b⁻¹ * (((evenVal (((j ^ 2 : ℤ) : ℚ) / (2 * (4 : ℕ))) primeFock : ℚ)) : ℂ) := by
  have hj' : |j| < ((4 : ℕ) : ℤ) := by exact_mod_cast hj
  let h : ℂ := ((((j : ℝ) ^ 2 / (4 * (4 : ℕ)) : ℝ)) : ℂ)
  let N := resN 4 four_ge_one (latticeModule 4 four_ge_one j)
  have hlow : IsLowestWeight N h := latticeModule_isLowestWeight 4 four_ge_one j hj'.le
  have hx : latVacuumGen (latP 4) ∈ N.weight h := latticeModule_vacuum_mem 4 four_ge_one j
  have hW : oMod N (WP 4 four_ge_one) (latVacuumGen (latP 4)) =
      (2 * h) • latVacuumGen (latP 4) := by
    rw [oMod_resN 4 four_ge_one _ (WP_mem_grading 4 four_ge_one), WP_coe]
    exact oMod_W_V2m 4 four_ge_one _ hlow hx
  have hE : oMod N (EP 4 four_ge_one) (latVacuumGen (latP 4)) = 0 := by
    rw [oMod_resN 4 four_ge_one _ (EP_mem_grading 4 four_ge_one)]
    exact oMod_E_lat_vac 4 four_ge_one j hj'
  obtain ⟨ψ, hmul, h1, hω, hval⟩ := tetra_character_of_plus_top N hlow hx
    (latVacuumGen_ne_zero' 4 four_ge_one) ![h, 2 * h, 0] (by
      intro i; fin_cases i
      · change oMod N (V2mPlus 4 four_ge_one).conformalVector _ = h • _
        rw [oMod_conformalVector]; exact N.L0_weight _ _ hx
      · exact hW
      · simpa using hE)
  refine ⟨ψ, hmul, h1, hω, char_value_tetraV hb hb0 N (latVacuumGen_ne_zero' 4 four_ge_one)
    ?_ ψ hval⟩
  rw [oMod_resN 4 four_ge_one _ wsP_mem, wsP_coe]
  exact oMod_prime_latticeTop j hj

/-- The `V_L⁻` character (weight `1`) with its value on `[v]`. -/
theorem sign_char {b : ℂ} (hb : tetraEquiv wsF = b • tetraV) (hb0 : b ≠ 0) :
    ∃ ψ : VOA.A Wt →ₗ[ℂ] ℂ, (∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q) ∧
      ψ (VOA.mk Wt Wt.vacuum) = 1 ∧ ψ (VOA.mk Wt Wt.conformalVector) = 1 ∧
      ψ (VOA.mk Wt tetraV) = 0 := by
  obtain ⟨ψ, hmul, h1, hω, hval⟩ := tetra_character_of_plus_top (signModule 4 four_ge_one)
    (signModule_isLowestWeight 4 four_ge_one) (signVector_mem 4 four_ge_one)
    (signVector_ne_zero 4 four_ge_one) ![1, 12, 0] (by
      intro i; fin_cases i
      · change oMod (signModule 4 four_ge_one) (V2mPlus 4 four_ge_one).conformalVector _ = _
        rw [oMod_conformalVector]
        exact (signModule 4 four_ge_one).L0_weight _ _ (signVector_mem 4 four_ge_one)
      · exact signVector_W 4 four_ge_one
      · simpa using signVector_E 4 four_ge_one (by norm_num))
  have hs : oMod (signModule 4 four_ge_one) wsP (signVector 4 four_ge_one) =
      (0 : ℂ) • signVector 4 four_ge_one := by
    rw [zero_smul]
    apply Subtype.ext
    rw [oMod_homogeneous _ wsP_mem]
    change (V2m 4 four_ge_one).smul (wsP : LatModuleGen (latP 4)) ((16 : ℤ) - 1)
      (bosonState (latP 4) (a0 4)) = 0
    rw [wsP_coe, show (16 : ℤ) - 1 = 15 by norm_num]
    exact prime_smul_boson
  refine ⟨ψ, hmul, h1, hω, ?_⟩
  rw [char_value_tetraV hb hb0 _ (signVector_ne_zero 4 four_ge_one) hs ψ hval, mul_zero]

/-! ## The residual -/

/-- The five scalars. -/
theorem tetraOddSingleValues_holds : TetraOddSingleValues := by
  intro c hc
  obtain ⟨b, hb⟩ := prim_sixteen wsF_prim
  obtain ⟨a, ha⟩ := prim_nine nineF_prim
  have hwsF0 : wsF ≠ 0 := by
    intro h0
    have h := oMod_prime_latticeTop 1 (by norm_num)
    rw [← wsP_coe, show wsP = 0 from congrArg Subtype.val h0, ZeroMemClass.coe_zero, map_zero,
      LinearMap.zero_apply, evenVal_one] at h
    have h2 := congrArg (coordEα (latP 4) 0) h
    rw [map_zero, map_smul, latVacuumGen, latStateGen, coordEα_apply, if_pos rfl] at h2
    simp only [HeisenbergN.vacuumN] at h2
    exact (smul_ne_zero (by norm_num) one_ne_zero) h2.symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hb
    exact hwsF0 (tetraEquiv.map_eq_zero_iff.mp hb)
  have hn0 : fixedNine ≠ 0 := fixedNine_nonzero_primary.1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hn0 (tetraEquiv.map_eq_zero_iff.mp ha)
  have hU0 : tetraU ≠ 0 := by
    intro hU
    rw [hU, smul_zero] at ha
    exact hn0 (tetraEquiv.map_eq_zero_iff.mp ha)
  -- `b c = c'`
  have hrel := tetraEquiv_hom.map_smul fixedNine 15 wsF
  rw [nine_smul_wsF, map_smul] at hrel
  change ((-190512 / 5 : ℚ) : ℂ) • tetraEquiv fixedNine =
    Wt.smul (tetraEquiv fixedNine) 15 (tetraEquiv wsF) at hrel
  rw [ha, hb, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, hc, smul_smul,
    smul_smul, smul_smul] at hrel
  have hbc : b * c = ((-190512 / 5 : ℚ) : ℂ) := by
    have h2 : (((-190512 / 5 : ℚ) : ℂ) * a - a * (b * c)) • tetraU = 0 := by
      rw [sub_smul, hrel, mul_assoc, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hU0
    have h4 : a * (((-190512 / 5 : ℚ) : ℂ) - b * c) = 0 := by rw [mul_sub]; linear_combination h3
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left ha0)).symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbc
    norm_num at hbc
  have hcb : c = b⁻¹ * ((-190512 / 5 : ℚ) : ℂ) := by
    rw [← hbc, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
  refine ⟨hc0, fun i => ?_⟩
  obtain ⟨q1, q4, q16, q916⟩ := q_vals
  match i with
  | 0 => -- `λ = 1`
    obtain ⟨ψ, hmul, h1, hω, hv⟩ := sign_char hb hb0
    refine ⟨ψ, hmul, h1, ?_, ?_⟩
    · rw [hω]; simp [sgl4]
    · rw [hv]
      have hq : (zp qList).eval (((sgl4 0 : ℚ)) : ℂ) = ((5 / 75209904 : ℚ) : ℂ) := by
        rw [show sgl4 0 = 1 from rfl, zp_eval, q1]
      rw [hq]
      exact (mul_ne_zero hc0 (by norm_num)).symm
  | 1 => -- `λ = 1/4`: `j = 2`
    obtain ⟨ψ, hmul, h1, hω, hv⟩ := lattice_char 2 (by norm_num) hb hb0
    refine ⟨ψ, hmul, h1, ?_, ?_⟩
    · rw [hω]; simp [sgl4]; norm_num
    · rw [hv, evenVal_two]
      have hq : (zp qList).eval (((sgl4 1 : ℚ)) : ℂ) = ((215 / 15969569616 : ℚ) : ℂ) := by
        rw [show sgl4 1 = 1/4 from rfl, zp_eval, q4]
      rw [hq]
      push_cast
      rw [mul_zero]
      exact (mul_ne_zero hc0 (by norm_num)).symm
  | 2 => -- `λ = 1/16`: `j = 1`
    obtain ⟨ψ, hmul, h1, hω, hv⟩ := lattice_char 1 (by norm_num) hb hb0
    refine ⟨ψ, hmul, h1, ?_, ?_⟩
    · rw [hω]; simp [sgl4]; norm_num
    · rw [hv, evenVal_one]
      have hq : (zp qList).eval (((sgl4 2 : ℚ)) : ℂ) = ((-1283 / 420906795008 : ℚ) : ℂ) := by
        rw [show sgl4 2 = 1/16 from rfl, zp_eval, q16]
      rw [hq, hcb, mul_assoc]
      intro h
      have h' := mul_left_cancel₀ (inv_ne_zero hb0) h
      norm_num at h'
  | 3 => -- `λ = 9/16`: `j = 3`
    obtain ⟨ψ, hmul, h1, hω, hv⟩ := lattice_char 3 (by norm_num) hb hb0
    refine ⟨ψ, hmul, h1, ?_, ?_⟩
    · rw [hω]; simp [sgl4]; norm_num
    · rw [hv, evenVal_three]
      have hq : (zp qList).eval (((sgl4 3 : ℚ)) : ℂ) = ((-3651 / 420906795008 : ℚ) : ℂ) := by
        rw [show sgl4 3 = 9/16 from rfl, zp_eval, q916]
      rw [hq, hcb, mul_assoc]
      intro h
      have h' := mul_left_cancel₀ (inv_ne_zero hb0) h
      norm_num at h'

/-- `TetraOddAnnihilator` holds. -/
theorem tetraOddAnnihilator_holds : TetraOddAnnihilator :=
  tetraOddAnnihilator_of_singleValues tetraOddSingleValues_holds

/-- `CubicZhuDimensionBound` holds. -/
theorem cubicZhuDimensionBound_holds : CubicZhuDimensionBound :=
  cubicZhuDimensionBound_of_singleValues tetraOddSingleValues_holds

end VOA.Classification.COne.OrbSgl
