/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTopFrame

/-!
# `σ` fixes the diagonal frame letters `w_j(−1)²𝟙`

`v0Sigma` is the transport of `golaySigma = G(χz₀)G⁻¹` along `golayToV0`
(`FrameBridgeGolay.lean`).  On the Cartan current `σ(α_j(−1)𝟙) = e^{α_j} + ε_j e^{−α_j}`
(`golaySigma_hSt`).  Hence `σ(α_j(−1)²𝟙) = (e + εf)₍₋₁₎(e + εf)`, and a direct lattice
computation (`root_square`: `e₍₋₁₎e = f₍₋₁₎f = 0`, `e₍₋₁₎f + f₍₋₁₎e = ε(S₂(α) + S₂(−α)) = ε α(−1)²𝟙`)
shows it equals `α_j(−1)²𝟙`: the level-one `sl₂` Sugawara vector is `σ`-invariant.

## Main results
* `root_square` — for a root `α` (general lattice):
  `(e^α + ε e^{−α})₍₋₁₎(e^α + ε e^{−α}) = α(−1)²𝟙`.
* `golaySigma_quadH_root` — `golaySigma (α_j(−1)²𝟙) = α_j(−1)²𝟙`.
* `golayToV0_qN` — `golayToV0` sends `α(−1)β(−1)𝟙 ∈ V_N` to `ι(α)(−1)ι(β)(−1)𝟙 ∈ V_Λ`
  (`α, β ∈ Λ₀`; charge-zero states see neither `golayE` nor the bridge coboundaries).
* `sig_dV_of_golay`, `sig_dV_fw` — `v0Sigma (w_j(−1)²𝟙) = w_j(−1)²𝟙` (`w_j = ι(2α_j)`).

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Unconditional (the
chosen `golayE` drops out).  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.IntegralLattice
open VOA.LatGen HeisenbergN MvPolynomial VOA.Moonshine.Triality
open Module (End)
open scoped TensorProduct

/-! ## §1  `(e + εf)₍₋₁₎(e + εf) = h₍₋₁₎h` for a root -/

section General

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

theorem vSchur_two (α : L.carrier) :
    vSchur L α 2 = (1 / 2 : ℂ) • (vVar L α 0 * vVar L α 0 + vVar L α 1) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, vSchur_succ, Finset.sum_range_succ, Finset.sum_range_one,
    WpC2.vSchur_one', vSchur_zero, mul_one]
  norm_num

theorem quadH_self (α : L.carrier) :
    quadH L hEven hPos α α = (vVar L α 0 * vVar L α 0) ⊗ₜ[ℂ] eGen L 0 := by
  rw [quadH]
  nth_rewrite 1 [hSt_eq_sum]
  rw [smul_sum_left]
  simp only [PreVertexAlgebra.smul_smul_left, hgen_eq_word]
  simp only [show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 by norm_num, LatticeTwisted.smul_hgen_neg]
  rw [LatGen.hSt, WpC2.vSchur_one', latStateGen]
  simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, TensorProduct.smul_tmul']
  rw [← TensorProduct.sum_tmul]
  congr 1
  simp only [← smul_mul_assoc, ← Finset.sum_mul]
  rfl

theorem root_square (α : L.carrier) (hα : L.form α α = 2) :
    (latticeVOAGen L hEven hPos).smul
        (latChargeGen L α + latticeCocycle L α (-α) • latChargeGen L (-α)) (-1)
        (latChargeGen L α + latticeCocycle L α (-α) • latChargeGen L (-α))
      = quadH L hEven hPos α α := by
  have hee := LatticeTwisted.smul_echg_echg L hEven hPos α α (-1)
  have hef := LatticeTwisted.smul_echg_echg L hEven hPos α (-α) (-1)
  have hfe := LatticeTwisted.smul_echg_echg L hEven hPos (-α) α (-1)
  have hff := LatticeTwisted.smul_echg_echg L hEven hPos (-α) (-α) (-1)
  simp only [map_neg, LinearMap.neg_apply, neg_neg, hα] at hee hef hfe hff
  rw [if_neg (by norm_num), TensorProduct.zero_tmul, smul_zero] at hee hff
  rw [if_pos (by norm_num), show (1 - 1 - -2 : ℤ).toNat = 2 from rfl, add_neg_cancel] at hef
  rw [if_pos (by norm_num), show (1 - 1 - -2 : ℤ).toNat = 2 from rfl, neg_add_cancel] at hfe
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right]
  change (latticeVOAGen L hEven hPos).smul (LatticeTwisted.echg L α) (-1) (LatticeTwisted.echg L α)
    + latticeCocycle L α (-α) • (latticeVOAGen L hEven hPos).smul (LatticeTwisted.echg L (-α)) (-1) (LatticeTwisted.echg L α)
    + latticeCocycle L α (-α) • ((latticeVOAGen L hEven hPos).smul (LatticeTwisted.echg L α) (-1) (LatticeTwisted.echg L (-α))
    + latticeCocycle L α (-α) • (latticeVOAGen L hEven hPos).smul (LatticeTwisted.echg L (-α)) (-1) (LatticeTwisted.echg L (-α))) = _
  rw [hee, hef, hfe, hff, latticeCocycle_neg_self_comm, quadH_self, vSchur_two, vSchur_two,
    WpC2.vVar_neg', WpC2.vVar_neg']
  have hsq := latticeCocycle_sq L α (-α)
  simp only [smul_zero, add_zero, zero_add, smul_add, smul_smul, hsq, one_smul, neg_mul_neg,
    ← TensorProduct.add_tmul]
  congr 1
  module

theorem thetaLat_hSt (α : L.carrier) : thetaLat L (hSt L α) = -hSt L α := by
  rw [LatGen.hSt, latStateGen, thetaLat_tmul, WpC2.vSchur_one', neg_zero]
  have : sigmaN (rank L) (vVar L α 0) = -vVar L α 0 := by
    simp only [vVar, map_sum, map_smul, sigmaN_X, smul_neg, Finset.sum_neg_distrib]
  rw [this, TensorProduct.neg_tmul]

theorem thetaLat_quadH (α β : L.carrier) :
    thetaLat L (quadH L hEven hPos α β) = quadH L hEven hPos α β := by
  have h := (thetaAut L hEven hPos).map_smul (hSt L α) (-1) (hSt L β)
  change thetaLat L (quadH L hEven hPos α β) = _ at h
  rw [h]
  change (latticeVOAGen L hEven hPos).smul (thetaLat L (hSt L α)) (-1) (thetaLat L (hSt L β)) = _
  rw [thetaLat_hSt, thetaLat_hSt, ← neg_one_smul ℂ (hSt L α), ← neg_one_smul ℂ (hSt L β),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, smul_smul]
  norm_num
  rfl

end General

/-! ## §2  `golaySigma` fixes `α_j(−1)²𝟙` -/

theorem golaySigma_quadH_root (j : Fin 24) :
    golaySigma (quadH golayN golayN_even golayN_posDef (golayRoot j) (golayRoot j))
      = quadH golayN golayN_even golayN_posDef (golayRoot j) (golayRoot j) := by
  have h := golaySigma.map_smul (hSt golayN (golayRoot j)) (-1) (hSt golayN (golayRoot j))
  change golaySigma (quadH golayN golayN_even golayN_posDef (golayRoot j) (golayRoot j)) = _ at h
  rw [h, golaySigma_hSt]
  have ht : tri j 1 0 (golayEps j) = latChargeGen golayN (golayRoot j)
      + latticeCocycle golayN (golayRoot j) (-golayRoot j) • latChargeGen golayN (-golayRoot j) := by
    simp [tri, vec3, golayEps]
  rw [ht]
  exact root_square golayN golayN_even golayN_posDef (golayRoot j) (golayRoot_norm j)

/-! ## §3  Transport of quadratic letters along `golayToV0` -/

theorem charLat_hSt_lam0 (a : lam0.carrier) : charLat lam0 golayE (hSt lam0 a) = hSt lam0 a := by
  rw [LatGen.hSt, charLat_latStateGen lam0 _ lam0_posDef, charVal_zero, one_smul]

theorem charLat_quadH_lam0 (a b : lam0.carrier) :
    charLat lam0 golayE (quadH lam0 lam0_even lam0_posDef a b) = quadH lam0 lam0_even lam0_posDef a b := by
  have h := lam0CharAut.map_smul (hSt lam0 a) (-1) (hSt lam0 b)
  change charLat lam0 golayE (quadH lam0 lam0_even lam0_posDef a b)
    = lam0VOA.smul (charLat lam0 golayE (hSt lam0 a)) (-1) (charLat lam0 golayE (hSt lam0 b)) at h
  rw [h, charLat_hSt_lam0, charLat_hSt_lam0]
  rfl

theorem bridgeN_quadH (a b : lam0.carrier) :
    bridgeN (quadH lam0 lam0_even lam0_posDef a b) = quadH golayN golayN_even golayN_posDef (inclN a) (inclN b) := by
  have h := bridgeN_isVOAHom.map_smul (hSt lam0 a) (-1) (hSt lam0 b)
  change bridgeN (quadH lam0 lam0_even lam0_posDef a b) = golayVOA.smul (bridgeN (hSt lam0 a)) (-1) (bridgeN (hSt lam0 b)) at h
  rw [h, bridgeN_hSt, bridgeN_hSt]
  rfl

theorem bridgeΛ_hSt (a : lam0.carrier) : bridgeΛ (hSt lam0 a) = hSt leech (inclΛ a) :=
  latMorphC_hSt lam0 leech inclΛ _ (latCob_zero _ _ _) lam0_posDef a

theorem bridgeΛ_quadH (a b : lam0.carrier) :
    bridgeΛ (quadH lam0 lam0_even lam0_posDef a b) = quadH leech leech_even leech_posDef (inclΛ a) (inclΛ b) := by
  have h := bridgeΛ_isVOAHom.map_smul (hSt lam0 a) (-1) (hSt lam0 b)
  change bridgeΛ (quadH lam0 lam0_even lam0_posDef a b) = leechVOA.smul (bridgeΛ (hSt lam0 a)) (-1) (bridgeΛ (hSt lam0 b)) at h
  rw [h, bridgeΛ_hSt, bridgeΛ_hSt]
  rfl

theorem quadH_golay_mem_chargeSec (α β : golayN.carrier) :
    quadH golayN golayN_even golayN_posDef α β ∈ chargeSec golayN 0 :=
  chargeSec_zero_smul_mem golayN golayN_even golayN_posDef (hSt_mem_chargeSec _) (-1)
    (hSt_mem_chargeSec _)

theorem quadH_golay_mem (α β : golayN.carrier) :
    quadH golayN golayN_even golayN_posDef α β ∈ (orbifold golayK).carrier := by
  rw [mem_golayV0_iff]
  refine ⟨golayChi_fix_chargeSec_zero (quadH_golay_mem_chargeSec α β), ?_⟩
  have h := golayTheta.map_smul (hSt golayN α) (-1) (hSt golayN β)
  change golayTheta (quadH golayN golayN_even golayN_posDef α β) = _ at h
  rw [h, golayTheta_hSt_all, golayTheta_hSt_all, ← neg_one_smul ℂ (hSt golayN α),
    ← neg_one_smul ℂ (hSt golayN β), PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    smul_smul]
  norm_num
  rfl

/-- `α(−1)β(−1)𝟙 ∈ V_N^{⟨χ,Θ⟩}` for `α, β ∈ Λ₀ ⊆ N`. -/
noncomputable def qN (a b : lam0.carrier) : (orbifold golayK).carrier :=
  ⟨quadH golayN golayN_even golayN_posDef (inclN a) (inclN b), quadH_golay_mem _ _⟩

/-- **`golayToV0` on quadratic letters**: `α(−1)β(−1)𝟙 ∈ V_N ↦ ι(α)(−1)ι(β)(−1)𝟙 ∈ V_Λ`. -/
theorem golayToV0_qN (a b : lam0.carrier) : golayToV0 (qN a b) = dV (inclΛ a) (inclΛ b) := by
  let z : Lam0PlusCarrier := ⟨quadH lam0 lam0_even lam0_posDef a b,
    (mem_lam0Plus_iff _).mpr (thetaLat_quadH lam0 lam0_even lam0_posDef a b)⟩
  have hz : lam0PlusGolayEquiv z = qN a b := by
    apply Subtype.ext
    change bridgeN (charLat lam0 golayE (quadH lam0 lam0_even lam0_posDef a b)) = _
    rw [charLat_quadH_lam0, bridgeN_quadH]
    rfl
  change lam0PlusEquiv (lam0PlusGolayEquiv.symm (qN a b)) = _
  rw [← hz, LinearEquiv.symm_apply_apply]
  apply Subtype.ext; apply Subtype.ext
  rw [lam0PlusEquiv_coe]
  exact bridgeΛ_quadH a b

/-- **`σ` on a quadratic letter fixed by `golaySigma`.** -/
theorem sig_dV_of_golay (a b : lam0.carrier)
    (hfix : golaySigma (quadH golayN golayN_even golayN_posDef (inclN a) (inclN b))
      = quadH golayN golayN_even golayN_posDef (inclN a) (inclN b)) :
    sig (dV (inclΛ a) (inclΛ b)) = dV (inclΛ a) (inclΛ b) := by
  rw [← golayToV0_qN, sig, ← golayToV0_sigma]
  congr 1
  apply Subtype.ext
  rw [golaySigma0_coe]
  exact hfix

theorem inclN_a4 (j : Fin 24) : inclN (a4 j) = 2 • golayRoot j := by
  apply Subtype.ext
  change (4 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ) = 2 • ((2 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ))
  rw [two_smul, ← add_smul]; norm_num

theorem quadH_nsmul (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef) (n : ℕ) (α : L.carrier) :
    quadH L hEven hPos (n • α) (n • α) = ((n : ℂ) * n) • quadH L hEven hPos α α := by
  rw [quadH, hSt_nsmul, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, smul_smul]
  rfl

/-- **`σ` fixes the diagonal frame letters**: `v0Sigma (w_j(−1)²𝟙) = w_j(−1)²𝟙`. -/
theorem sig_dV_fw (j : Fin 24) : sig (dV (fw j) (fw j)) = dV (fw j) (fw j) := by
  refine sig_dV_of_golay (a4 j) (a4 j) ?_
  rw [inclN_a4, quadH_nsmul, Aut.map_smul_c, golaySigma_quadH_root]

end VOA.Moonshine.SigmaTop
