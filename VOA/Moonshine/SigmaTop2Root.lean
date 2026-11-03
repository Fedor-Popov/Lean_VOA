/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Seed

/-!
# The `(±4,±4,0²²)` lattice letters

In `V_N` the letters on a root pair `j ≠ k` are `H = h_jh_k`, `A_jA_k`, `B_jB_k`
(`A = e + εf`, `B = e − εf`), and `σ` acts by `H ↔ AA`, `BB ↦ BB` (from `golaySigma_tri`,
`σ` on an `sl₂`-triple, which needs the new preimage `golayG_yPreB`).  Transported to `V₀⁺`
(`golayToV0_PPN`, `golayToV0_MMN`, `golayToV0_HHo`):
`σ(u_{γ₊}) = (2κ₊)⁻¹(⅛ w_j(−1)w_k(−1)𝟙 + κ₊ u_{γ₊} − κ₋ u_{γ₋})` (`sig_lV_gP`, `sig_lV_gM`).

## Main results
* `golaySigma_tri_B`, `golaySigma_tri`.
* `sig_lV_gP`, `sig_lV_gM`; `actT_sig_lV_gP`, `actT_sig_lV_gM` (zero modes on `(T⁺)₂`).
* `phiV3_ZM_gP`, `phiV3_ZM_gM` — the root letters intertwine on `V₃⁺` for any even `τ`
  meeting the eigen-conditions and the transport rule `ε(γ,n) τ(γ+n) = (2κ)⁻¹ τ(n)`.

## Status
`sorry`-free.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist
open Module (End)

/-! ## §1  `σ` on the `sl₂`-triples of `V_N` -/

/-- `y_B = (4 − 2√2) e + 0 h − ε(2+√2)/4 f`, with `G y_B = e − εf`. -/
noncomputable def yPreB (j : Fin 24) : LatModuleGen golayN :=
  tri j (4 - 2 * (Real.sqrt 2 : ℂ)) 0 (-(golayEps j) * (2 + (Real.sqrt 2 : ℂ)) / 4)

theorem golayG_yPreB (j : Fin 24) : golayG (yPreB j) = tri j 1 0 (-golayEps j) := by
  rw [yPreB, golayG_tri, golayG1_tri]
  have hs := sqrt2_sq
  have he := golayEps_sq j
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hsdef
  set e := golayEps j with hedef
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [← hsdef]
  apply vec3_congr
  · linear_combination ((-3 : ℂ) * e^2 + (5/4 : ℂ) * e^4 + (5/4 : ℂ) * s^1 * e^2 + (-7/8 : ℂ) * s^1 * e^4 + (1/2 : ℂ) * s^2 * e^4 + (-1/8 : ℂ) * s^3 * e^4) * hs + ((-3 : ℂ) + (5/2 : ℂ) * e^2 + (2 : ℂ) * s^1 + (-7/4 : ℂ) * s^1 * e^2) * he
  · linear_combination ((3/4 : ℂ) * e^2 + (-1/2 : ℂ) * e^4 + (3/8 : ℂ) * s^1 * e^4 + (-1/8 : ℂ) * s^2 * e^4) * hs + ((-1 : ℂ) * e^2 + (3/4 : ℂ) * s^1 * e^2) * he
  · linear_combination ((-1/4 : ℂ) * e^3 + (1/8 : ℂ) * s^1 * e^3) * hs + ((-1/2 : ℂ) * e^1 + (1/4 : ℂ) * s^1 * e^1) * he

theorem golayChiMod_yPreB (j : Fin 24) : golayChiMod (yPreB j) = -yPreB j := by
  rw [yPreB, golayChiMod_tri, tri, vec3_neg]
  apply vec3_congr <;> try ring

/-- `σ(e − εf) = −(e − εf)`. -/
theorem golaySigma_tri_B (j : Fin 24) :
    golaySigma (tri j 1 0 (-golayEps j)) = -tri j 1 0 (-golayEps j) := by
  rw [← golayG_yPreB, golaySigma, Aut.mul_apply, Aut.mul_apply, Aut.inv_apply_apply,
    golayChiMod_yPreB]
  show golayG.toLinearEquiv (-_) = _
  rw [map_neg]

theorem tri_decomp (j : Fin 24) (x₁ x₂ x₃ : ℂ) :
    tri j x₁ x₂ x₃ = x₂ • tri j 0 1 0 + ((x₁ + golayEps j * x₃) / 2) • tri j 1 0 (golayEps j)
      + ((x₁ - golayEps j * x₃) / 2) • tri j 1 0 (-golayEps j) := by
  have he := golayEps_mul_self j
  simp only [tri, vec3_smul, vec3_add]
  apply vec3_congr
  · ring
  · ring
  · linear_combination (-x₃) * he

/-- **`σ` on an `sl₂`-triple**: `h ↦ e+εf`, `e+εf ↦ h`, `e−εf ↦ −(e−εf)`. -/
theorem golaySigma_tri (j : Fin 24) (x₁ x₂ x₃ : ℂ) :
    golaySigma (tri j x₁ x₂ x₃) =
      tri j (x₂ - x₁ / 2 + golayEps j * x₃ / 2) (x₁ / 2 + golayEps j * x₃ / 2)
        (golayEps j * x₂ + golayEps j * x₁ / 2 - x₃ / 2) := by
  have he := golayEps_mul_self j
  rw [tri_decomp j x₁ x₂ x₃, aut_add, aut_add, aut_smul, aut_smul, aut_smul, ← hSt_eq_tri,
    golaySigma_hSt, golaySigma_tri_ef, golaySigma_tri_B, hSt_eq_tri]
  simp only [tri, vec3_smul, vec3_add, vec3_neg]
  apply vec3_congr
  · ring
  · ring
  · linear_combination (-x₃ / 2) * he

/-! ## §2  The weight-two letters `AA, BB, HH` of `V_N` on a pair of roots -/

/-- `x₍₋₁₎ y` in `V_N`. -/
noncomputable def prN (x y : LatModuleGen golayN) : LatModuleGen golayN :=
  (latticeVOAGen golayN golayN_even golayN_posDef).smul x (-1) y

theorem aut_prN (g : Aut golayVOA) (x y : LatModuleGen golayN) : g (prN x y) = prN (g x) (g y) :=
  g.map_smul x (-1) y

theorem prN_neg_neg (x y : LatModuleGen golayN) : prN (-x) (-y) = prN x y := by
  rw [prN, ← neg_one_smul ℂ x, ← neg_one_smul ℂ y, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, smul_smul]
  norm_num; rfl

/-- `A_j A_k = (e_j + f_j)(e_k + f_k)`. -/
noncomputable def AAN (j k : Fin 24) : LatModuleGen golayN := prN (tri j 1 0 (golayEps j)) (tri k 1 0 (golayEps k))
/-- `B_j B_k = (e_j − f_j)(e_k − f_k)`. -/
noncomputable def BBN (j k : Fin 24) : LatModuleGen golayN := prN (tri j 1 0 (-golayEps j)) (tri k 1 0 (-golayEps k))
/-- `h_j h_k`. -/
noncomputable def HHN (j k : Fin 24) : LatModuleGen golayN :=
  quadH golayN golayN_even golayN_posDef (golayRoot j) (golayRoot k)

theorem HHN_eq (j k : Fin 24) : HHN j k = prN (tri j 0 1 0) (tri k 0 1 0) := by
  rw [HHN, quadH, ← hSt_eq_tri, ← hSt_eq_tri]; rfl

theorem golaySigma_AAN (j k : Fin 24) : golaySigma (AAN j k) = HHN j k := by
  rw [AAN, aut_prN, golaySigma_tri_ef, golaySigma_tri_ef, HHN, quadH]; rfl

theorem golaySigma_BBN (j k : Fin 24) : golaySigma (BBN j k) = BBN j k := by
  rw [BBN, aut_prN, golaySigma_tri_B, golaySigma_tri_B, prN_neg_neg]

theorem golaySigma_HHN (j k : Fin 24) : golaySigma (HHN j k) = AAN j k := by
  rw [HHN_eq, aut_prN, ← hSt_eq_tri, ← hSt_eq_tri, golaySigma_hSt, golaySigma_hSt]; rfl

theorem golayChi_tri_A (j : Fin 24) (c : ℂ) : golayChi (tri j 1 0 c) = -tri j 1 0 c := by
  rw [golayChi_tri, tri, tri, vec3_neg]; apply vec3_congr <;> ring

theorem golayChi_AAN (j k : Fin 24) : golayChi (AAN j k) = AAN j k := by
  rw [AAN, aut_prN, golayChi_tri_A, golayChi_tri_A, prN_neg_neg]

theorem golayChi_BBN (j k : Fin 24) : golayChi (BBN j k) = BBN j k := by
  rw [BBN, aut_prN, golayChi_tri_A, golayChi_tri_A, prN_neg_neg]

theorem golayChi_HHN (j k : Fin 24) : golayChi (HHN j k) = HHN j k := by
  rw [HHN_eq, aut_prN, golayChi_tri, golayChi_tri]; simp

theorem golayTheta_AAN (j k : Fin 24) : golayTheta (AAN j k) = AAN j k := by
  rw [golayTheta, Aut.mul_apply, Aut.mul_apply, golaySigma_AAN, golayChi_HHN, golaySigma_HHN]

theorem golayTheta_BBN (j k : Fin 24) : golayTheta (BBN j k) = BBN j k := by
  rw [golayTheta, Aut.mul_apply, Aut.mul_apply, golaySigma_BBN, golayChi_BBN, golaySigma_BBN]

theorem AAN_mem (j k : Fin 24) : AAN j k ∈ (orbifold golayK).carrier :=
  (mem_golayV0_iff _).mpr ⟨golayChi_AAN j k, golayTheta_AAN j k⟩

theorem BBN_mem (j k : Fin 24) : BBN j k ∈ (orbifold golayK).carrier :=
  (mem_golayV0_iff _).mpr ⟨golayChi_BBN j k, golayTheta_BBN j k⟩

/-- The `P`-letter `½(AA + BB) = e_j e_k + f_j f_k ∈ V_N^{⟨χ,Θ⟩}`. -/
noncomputable def PPN (j k : Fin 24) : (orbifold golayK).carrier :=
  (1 / 2 : ℂ) • (⟨AAN j k, AAN_mem j k⟩ + ⟨BBN j k, BBN_mem j k⟩)

/-- The `M`-letter `½(AA − BB) = e_j f_k + f_j e_k`. -/
noncomputable def MMN (j k : Fin 24) : (orbifold golayK).carrier :=
  (1 / 2 : ℂ) • (⟨AAN j k, AAN_mem j k⟩ - ⟨BBN j k, BBN_mem j k⟩)

theorem tri_root (j : Fin 24) (c : ℂ) :
    tri j 1 0 c = latChargeGen golayN (golayRoot j) + c • latChargeGen golayN (-golayRoot j) := by
  simp [tri, vec3]

theorem AAN_charged {j k : Fin 24} (hjk : j ≠ k) :
    AAN j k = ∑ i : Fin 4, cQ j k i • latChargeGen golayN (inclN (aQ j k i)) := by
  rw [AAN, prN, tri_root, tri_root, root_prod golayN golayN_even golayN_posDef _ _ (golayRoot_orth hjk)]
  rw [Fin.sum_univ_four, aQ_0, aQ_1, aQ_2, aQ_3, cQ_0, cQ_1, cQ_2, cQ_3, map_neg, map_neg, inclN_aP,
    inclN_aM, neg_add, neg_neg, neg_add]

theorem BBN_charged {j k : Fin 24} (hjk : j ≠ k) :
    BBN j k = cQ j k 0 • latChargeGen golayN (inclN (aQ j k 0)) - cQ j k 1 • latChargeGen golayN (inclN (aQ j k 1))
      - cQ j k 2 • latChargeGen golayN (inclN (aQ j k 2)) + cQ j k 3 • latChargeGen golayN (inclN (aQ j k 3)) := by
  rw [BBN, prN, tri_root, tri_root, root_prod golayN golayN_even golayN_posDef _ _ (golayRoot_orth hjk)]
  rw [aQ_0, aQ_1, aQ_2, aQ_3, cQ_0, cQ_1, cQ_2, cQ_3, map_neg, map_neg, inclN_aP,
    inclN_aM, neg_add, neg_neg, neg_add]
  simp only [neg_mul, mul_neg, neg_neg, neg_smul]
  abel

theorem PPN_coe {j k : Fin 24} (hjk : j ≠ k) :
    ((PPN j k : (orbifold golayK).carrier) : LatModuleGen golayN)
      = ∑ i ∈ ({0, 3} : Finset (Fin 4)), cQ j k i • latChargeGen golayN (inclN (aQ j k i)) := by
  change (1 / 2 : ℂ) • (AAN j k + BBN j k) = _
  rw [AAN_charged hjk, BBN_charged hjk, Fin.sum_univ_four, Finset.sum_pair (by decide)]
  module

theorem MMN_coe {j k : Fin 24} (hjk : j ≠ k) :
    ((MMN j k : (orbifold golayK).carrier) : LatModuleGen golayN)
      = ∑ i ∈ ({1, 2} : Finset (Fin 4)), cQ j k i • latChargeGen golayN (inclN (aQ j k i)) := by
  change (1 / 2 : ℂ) • (AAN j k - BBN j k) = _
  rw [AAN_charged hjk, BBN_charged hjk, Fin.sum_univ_four, Finset.sum_pair (by decide)]
  module

/-! ## §3  `σ` on the root letters of `V₀⁺` -/

/-- `h_j h_k` as a state of `V_N^{⟨χ,Θ⟩}`. -/
noncomputable def HHo (j k : Fin 24) : (orbifold golayK).carrier := ⟨HHN j k, quadH_golay_mem _ _⟩

theorem golaySigma0_PPN {j k : Fin 24} (hjk : j ≠ k) :
    golaySigma0 (PPN j k) = (1 / 2 : ℂ) • HHo j k + (1 / 2 : ℂ) • PPN j k - (1 / 2 : ℂ) • MMN j k := by
  apply Subtype.ext
  rw [golaySigma0_coe]
  change golaySigma ((1 / 2 : ℂ) • (AAN j k + BBN j k)) =
    (1 / 2 : ℂ) • HHN j k + (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (AAN j k + BBN j k))
      - (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (AAN j k - BBN j k))
  rw [aut_smul, aut_add, golaySigma_AAN, golaySigma_BBN]
  module

theorem golaySigma0_MMN {j k : Fin 24} (hjk : j ≠ k) :
    golaySigma0 (MMN j k) = (1 / 2 : ℂ) • HHo j k - (1 / 2 : ℂ) • PPN j k + (1 / 2 : ℂ) • MMN j k := by
  apply Subtype.ext
  rw [golaySigma0_coe]
  change golaySigma ((1 / 2 : ℂ) • (AAN j k - BBN j k)) =
    (1 / 2 : ℂ) • HHN j k - (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (AAN j k + BBN j k))
      + (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (AAN j k - BBN j k))
  rw [aut_smul, show AAN j k - BBN j k = AAN j k + (-1 : ℂ) • BBN j k by module, aut_add, aut_smul,
    golaySigma_AAN, golaySigma_BBN]
  module

theorem qN_a4_eq (j k : Fin 24) : qN (a4 j) (a4 k) = (4 : ℂ) • HHo j k := by
  apply Subtype.ext
  change quadH golayN golayN_even golayN_posDef (inclN (a4 j)) (inclN (a4 k)) = (4 : ℂ) • HHN j k
  rw [inclN_a4, inclN_a4, quadH_smul_smul, HHN]; norm_num

theorem golayToV0_HHo (j k : Fin 24) : golayToV0 (HHo j k) = (1 / 4 : ℂ) • dV (fw j) (fw k) := by
  have h := golayToV0_qN (a4 j) (a4 k)
  rw [qN_a4_eq, map_smul] at h
  change _ = (1 / 4 : ℂ) • dV (inclΛ (a4 j)) (inclΛ (a4 k))
  rw [← h, smul_smul]; norm_num

theorem kP_eq_dQ (j k : Fin 24) (hjk : j ≠ k) : 2 * kP j k = cQ j k 0 * tc (aQ j k 0) := by
  rw [kP_eq hjk, aQ_0]; ring

theorem golayToV0_PPN {j k : Fin 24} (hjk : j ≠ k) :
    golayToV0 (PPN j k) = (2 * kP j k) • lV (gP j k) (gP_mem j k) := by
  apply Subtype.ext; apply Subtype.ext
  rw [golayToV0_charged _ _ _ _ (PPN_coe hjk), Finset.sum_pair (by decide)]
  have hd := (dQ_symm hjk).1
  unfold dQ at hd
  have e0 : inclΛ (aQ j k 0) = gP j k := rfl
  have e3 : inclΛ (aQ j k 3) = -gP j k := by simp [aQ, gP]
  rw [e0, e3]
  change _ = (2 * kP j k) • frameX0 (gP j k)
  rw [frameX0, kP_eq_dQ j k hjk, smul_add]
  congr 2
  linear_combination -hd / 4

theorem kM_eq_dQ (j k : Fin 24) (hjk : j ≠ k) : 2 * kM j k = cQ j k 1 * tc (aQ j k 1) := by
  rw [kM_eq hjk, aQ_1]; ring

theorem golayToV0_MMN {j k : Fin 24} (hjk : j ≠ k) :
    golayToV0 (MMN j k) = (2 * kM j k) • lV (gM j k) (gM_mem j k) := by
  apply Subtype.ext; apply Subtype.ext
  rw [golayToV0_charged _ _ _ _ (MMN_coe hjk), Finset.sum_pair (by decide)]
  have hd := (dQ_symm hjk).2
  unfold dQ at hd
  have e1 : inclΛ (aQ j k 1) = gM j k := rfl
  have e2 : inclΛ (aQ j k 2) = -gM j k := by simp [aQ, gM]
  rw [e1, e2]
  change _ = (2 * kM j k) • frameX0 (gM j k)
  rw [frameX0, kM_eq_dQ j k hjk, smul_add]
  congr 2
  linear_combination -hd / 4

/-- **`σ` on the `(4,4,0²²)` letter `e^{γ₊} + e^{−γ₊}`**:
`σ(u_{γ₊}) = (2κ₊)⁻¹ (⅛ w_j(−1)w_k(−1)𝟙 + κ₊ u_{γ₊} − κ₋ u_{γ₋})`. -/
theorem sig_lV_gP {j k : Fin 24} (hjk : j ≠ k) :
    sig (lV (gP j k) (gP_mem j k)) = (2 * kP j k)⁻¹ • ((1 / 8 : ℂ) • dV (fw j) (fw k)
      + kP j k • lV (gP j k) (gP_mem j k) - kM j k • lV (gM j k) (gM_mem j k)) := by
  have hk := kP_ne_zero hjk
  have h : lV (gP j k) (gP_mem j k) = (2 * kP j k)⁻¹ • golayToV0 (PPN j k) := by
    rw [golayToV0_PPN hjk, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero hk), one_smul]
  conv_lhs => rw [h]
  rw [sig_smul, sig, ← golayToV0_sigma, golaySigma0_PPN hjk, map_sub, map_add, map_smul, map_smul,
    map_smul, golayToV0_HHo, golayToV0_PPN hjk, golayToV0_MMN hjk]
  congr 1
  simp only [smul_smul]
  module

theorem sig_lV_gM {j k : Fin 24} (hjk : j ≠ k) :
    sig (lV (gM j k) (gM_mem j k)) = (2 * kM j k)⁻¹ • ((1 / 8 : ℂ) • dV (fw j) (fw k)
      - kP j k • lV (gP j k) (gP_mem j k) + kM j k • lV (gM j k) (gM_mem j k)) := by
  have hk := kM_ne_zero hjk
  have h : lV (gM j k) (gM_mem j k) = (2 * kM j k)⁻¹ • golayToV0 (MMN j k) := by
    rw [golayToV0_MMN hjk, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero hk), one_smul]
  conv_lhs => rw [h]
  rw [sig_smul, sig, ← golayToV0_sigma, golaySigma0_MMN hjk, map_add, map_sub, map_smul, map_smul,
    map_smul, golayToV0_HHo, golayToV0_PPN hjk, golayToV0_MMN hjk]
  congr 1
  simp only [smul_smul]
  module

/-! ## §4  Zero modes of `σ(u_{γ±})` on the twisted top -/

theorem actT_sub_left' (u v : V0Sub.carrier) (n : ℤ) (y : TP) :
    actT (u - v) n y = actT u n y - actT v n y := by
  rw [sub_eq_add_neg, actT_add_left, ← neg_one_smul ℂ v, actT_smul_left]; module

theorem hP_two_smul_left (c : ℂ) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    hP (c • v) t = hP v (c • t) := by rw [hP_smul_left, hP_smul_right]

/-- The common block computation behind both root letters. -/
theorem root_block_eval {j k : Fin 24} (hjk : j ≠ k) (m : Fin 24) (t : TLeechT) {l : ℂ}
    (hPt : kP j k • eL (gP j k) t = l • t) (hMt : kM j k • eL (gM j k) t = l • t) (a b : ℂ) :
    a • hP (dL (fw j) (fw k) (cw m)) t
      + b • (kP j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (eL (gP j k) t)))
      - b • (kM j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (eL (gM j k) t)))
      = if m = j then (4 * a - b * l) • hP (cw k) t
        else if m = k then (4 * a - b * l) • hP (cw j) t else 0 := by
  have eP : kP j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (eL (gP j k) t))
      = ((2 : ℂ) ^ (-(3 : ℤ)) * l) • hP (latL (gP j k) (cw m)) t := by
    rw [smul_comm, ← hP_smul_right, hPt, hP_smul_right, smul_smul]
  have eM : kM j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (eL (gM j k) t))
      = ((2 : ℂ) ^ (-(3 : ℤ)) * l) • hP (latL (gM j k) (cw m)) t := by
    rw [smul_comm, ← hP_smul_right, hMt, hP_smul_right, smul_smul]
  rw [eP, eM, dL_fw_off hjk, latL_gP_cw, latL_gM_cw, lv_gP_apply, lv_gM_apply]
  by_cases hmj : m = j
  · subst hmj
    simp only [if_true, if_neg (Ne.symm hjk), if_neg hjk]
    simp only [hP_sub_left, hP_add_left, hP_smul_left]
    push_cast
    have : (2 : ℂ) ^ (-(3 : ℤ)) = 1 / 8 := by norm_num
    rw [this]
    module
  · by_cases hmk : m = k
    · subst hmk
      simp only [if_neg hmj, if_true]
      simp only [hP_sub_left, hP_add_left, hP_smul_left]
      push_cast
      have : (2 : ℂ) ^ (-(3 : ℤ)) = 1 / 8 := by norm_num
      rw [this]
      module
    · simp only [if_neg hmj, if_neg hmk]
      simp only [hP_sub_left, hP_add_left, hP_smul_left]
      push_cast
      have h0 : hP (0 : Fin (rank leech) → ℂ) t = 0 := by
        apply Subtype.ext; simp [hP_coe, hvec]
      simp only [zero_smul, add_zero, sub_zero, h0, smul_zero]
      module

theorem actT_sig_lV_gP {j k : Fin 24} (hjk : j ≠ k) (m : Fin 24) (t : TLeechT) {l : ℂ}
    (hPt : kP j k • eL (gP j k) t = l • t) (hMt : kM j k • eL (gM j k) t = l • t) :
    actT (sig (lV (gP j k) (gP_mem j k))) 1 (hP (cw m) t)
      = (2 * kP j k)⁻¹ • (if m = j then ((1 / 2 : ℂ) - l) • hP (cw k) t
          else if m = k then ((1 / 2 : ℂ) - l) • hP (cw j) t else 0) := by
  rw [sig_lV_gP hjk, actT_smul_left, actT_sub_left', actT_add_left, actT_smul_left, actT_smul_left,
    actT_smul_left, actT_dV_hP, actT_lV_hP (gP_mem j k) (form_gP_self hjk),
    actT_lV_hP (gM_mem j k) (form_gM_self hjk)]
  congr 1
  have h := root_block_eval hjk m t hPt hMt (1 / 8) 1
  simp only [one_smul, one_mul] at h
  rw [h]
  split_ifs <;> norm_num

theorem actT_sig_lV_gM {j k : Fin 24} (hjk : j ≠ k) (m : Fin 24) (t : TLeechT) {l : ℂ}
    (hPt : kP j k • eL (gP j k) t = l • t) (hMt : kM j k • eL (gM j k) t = l • t) :
    actT (sig (lV (gM j k) (gM_mem j k))) 1 (hP (cw m) t)
      = (2 * kM j k)⁻¹ • (if m = j then ((1 / 2 : ℂ) + l) • hP (cw k) t
          else if m = k then ((1 / 2 : ℂ) + l) • hP (cw j) t else 0) := by
  rw [sig_lV_gM hjk, actT_smul_left, actT_add_left, actT_sub_left', actT_smul_left, actT_smul_left,
    actT_smul_left, actT_dV_hP, actT_lV_hP (gP_mem j k) (form_gP_self hjk),
    actT_lV_hP (gM_mem j k) (form_gM_self hjk)]
  congr 1
  have h := root_block_eval hjk m t hPt hMt (1 / 8) (-1)
  simp only [neg_smul, one_smul, sub_neg_eq_add, neg_one_mul] at h
  have e : (1 / 8 : ℂ) • hP (dL (fw j) (fw k) (cw m)) t
      - kP j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (eL (gP j k) t))
      + kM j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (eL (gM j k) t))
      = (1 / 8 : ℂ) • hP (dL (fw j) (fw k) (cw m)) t
      + -(kP j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (eL (gP j k) t)))
      + kM j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (eL (gM j k) t)) := by abel
  rw [e, h]
  split_ifs <;> norm_num

/-! ## §5  The root letters on `V₃⁺` -/

theorem frameX0P_neg (m : leech.carrier) : frameX0P (-m) = frameX0P m := by
  apply Subtype.ext
  change frameX0 (-m) = frameX0 m
  rw [frameX0, frameX0, neg_neg, add_comm]

theorem frameChar_eq_one {m : leech.carrier} (hm : m ∉ lambda0) : frameChar m = 1 := by
  rw [mem_lambda0] at hm
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (frameChar m) with h | h
  · exact absurd h hm
  · exact h

open Classical in
theorem mem_S1_or_neg {m : leech.carrier} (hm0 : m ∉ lambda0) (h4 : leech.form m m = 4) :
    m ∈ halfFourChi 1 ∨ -m ∈ halfFourChi 1 := by
  have hm : m ∈ normFour leech leech_posDef := (mem_normFour leech leech_posDef).mpr h4
  rw [normFour_eq_union] at hm
  rcases Finset.mem_union.mp hm with h | h
  · exact Or.inl (Finset.mem_filter.mpr ⟨h, frameChar_eq_one hm0⟩)
  · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp h
    refine Or.inr (Finset.mem_filter.mpr ⟨by rwa [neg_neg], ?_⟩)
    have := frameChar_eq_one hm0
    rw [map_neg] at this
    rw [neg_neg]
    calc frameChar β = -(-frameChar β) := (neg_neg _).symm
      _ = -1 := by rw [this]
      _ = 1 := by decide

theorem phiV3_frameX0P_any {τ : leech.carrier → TLeechT} (hev : ∀ m, τ (-m) = τ m)
    {m : leech.carrier} (hm0 : m ∉ lambda0) (h4 : leech.form m m = 4) :
    phiV3 τ (frameX0P m) = hP (cw (blk m)) (τ m) := by
  rcases mem_S1_or_neg hm0 h4 with h | h
  · exact phiV3_frameX0P τ h
  · rw [← frameX0P_neg, phiV3_frameX0P τ h, blk_neg, hev]

theorem blk_eq_of_three {m : leech.carrier} (hm0 : m ∉ lambda0) (h4 : leech.form m m = 4) {i : Fin 24}
    (h : lv m i = 3 ∨ lv m i = -3) : blk m = i := by
  have hs := lv_sq hm0 h4 i
  by_contra hne
  rw [if_neg (Ne.symm hne)] at hs
  rcases h with h | h <;> rw [h] at hs <;> norm_num at hs

theorem form_self_add {γ n : leech.carrier} (hγ : leech.form γ γ = 4) (hn : leech.form n n = 4)
    (h : leech.form γ n = -2) : leech.form (γ + n) (γ + n) = 4 := by
  have hs := leech.isSymm.eq n γ
  simp only [LinearMap.flip_apply] at hs
  simp only [map_add, LinearMap.add_apply, hγ, hn, h]
  rw [show leech.form n γ = leech.form γ n from by rw [hs]] ; rw [h]; norm_num

theorem not_mem_add {γ n : leech.carrier} (hγ : γ ∈ lambda0) (hn : n ∉ lambda0) : γ + n ∉ lambda0 := by
  intro h; exact hn (by simpa using sub_mem h hγ)

/-- The values of `lam` in terms of the two coordinates (for `blk n ∈ {j,k}` or not). -/
theorem lam_val (j k : Fin 24) (n : leech.carrier) :
    lam j k n = if blk n = j ∨ blk n = k then -(((lv n j * lv n k : ℤ) : ℂ)) / 6
      else ((lv n j * lv n k : ℤ) : ℂ) / 2 := rfl

/-- **The `γ₊ = 4e_j + 4e_k` letter on `V₃⁺`**, from the eigen-conditions and the transport
rule `ε(γ₊,n) τ(γ₊ + n) = (2κ₊)⁻¹ τ(n)` along the moves `⟨γ₊,n⟩ = −2`. -/
theorem phiV3_ZM_gP {τ : leech.carrier → TLeechT} (hev : ∀ m, τ (-m) = τ m) {j k : Fin 24}
    (hjk : j ≠ k)
    (heig : ∀ n ∈ halfFourChi 1, kP j k • eL (gP j k) (τ n) = lam j k n • τ n ∧
      kM j k • eL (gM j k) (τ n) = lam j k n • τ n)
    (hrule : ∀ n : leech.carrier, n ∉ lambda0 → leech.form n n = 4 → leech.form (gP j k) n = -2 →
      εΛ (gP j k) n • τ (gP j k + n) = (2 * kP j k)⁻¹ • τ n) :
    ZM (phiV3 τ) OmegaV3 (lV (gP j k) (gP_mem j k)) := by
  refine ZM_of_basis _ _ fun n hn => ?_
  obtain ⟨h4, h1⟩ := mem_halfFourChi hn
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, h1]; exact one_ne_zero
  obtain ⟨hPe, hMe⟩ := heig n hn
  rw [actV_lV (gP_mem j k) hn0 (form_gP_self hjk) h4, map_add, phiV3_frameX0P τ hn,
    actT_sig_lV_gP hjk (blk n) (τ n) hPe hMe, form_gP_left]
  have hsq := lv_sq hn0 h4
  have hk2 : (2 * kP j k) ≠ 0 := mul_ne_zero two_ne_zero (kP_ne_zero hjk)
  -- the moved vectors
  have hmove : ∀ m : leech.carrier, m ∉ lambda0 → leech.form m m = 4 → leech.form (gP j k) m = -2 →
      ∀ i, (lv (gP j k + m) i = 3 ∨ lv (gP j k + m) i = -3) →
      εΛ (gP j k) m • phiV3 τ (frameX0P (gP j k + m)) = hP (cw i) ((2 * kP j k)⁻¹ • τ m) := by
    intro m hm0 hm4 hf i hi
    have h0' := not_mem_add (gP_mem j k) hm0
    have h4' := form_self_add (form_gP_self hjk) hm4 hf
    rw [phiV3_frameX0P_any hev h0' h4', blk_eq_of_three h0' h4' hi, ← hP_smul_right, hrule m hm0 hm4 hf]
  rw [lam_val]
  by_cases hbj : blk n = j
  · have hk : k ≠ blk n := hbj ▸ Ne.symm hjk
    have ha := hsq j; rw [if_pos hbj.symm] at ha
    have hb := hsq k; rw [if_neg hk] at hb
    simp only [hbj, true_or, if_true]
    rcases int_sq_nine ha with ha' | ha' <;> rcases int_sq_one hb with hb' | hb' <;> rw [ha', hb']
    · -- (3,1): form = 2
      norm_num
      have hf : leech.form (gP j k) (-n) = -2 := by
        rw [map_neg, form_gP_left, ha', hb']; norm_num
      have := hmove (-n) (fun h => hn0 (by simpa using neg_mem h)) (by simp only [map_neg, LinearMap.neg_apply, neg_neg]; exact h4) hf k
        (by rw [lv_add, lv_neg, Pi.add_apply, Pi.neg_apply, lv_gP_apply, hb']; simp [Ne.symm hjk])
      rw [hev, ← sub_eq_add_neg] at this
      rw [this, hP_smul_right]
      congr 1; rw [mul_inv]; ring
    · norm_num
    · norm_num
    · -- (−3,−1): form = −2
      norm_num
      have hf : leech.form (gP j k) n = -2 := by rw [form_gP_left, ha', hb']; norm_num
      rw [hmove n hn0 h4 hf k (by rw [lv_add, Pi.add_apply, lv_gP_apply, hb']; simp [Ne.symm hjk]),
        hP_smul_right]
      congr 1; rw [mul_inv]; ring
  · by_cases hbk : blk n = k
    · have hj : j ≠ blk n := hbk ▸ hjk
      have ha := hsq j; rw [if_neg hj] at ha
      have hb := hsq k; rw [if_pos hbk.symm] at hb
      simp only [hbk, or_true, if_true, if_neg (Ne.symm hjk)]
      rcases int_sq_one ha with ha' | ha' <;> rcases int_sq_nine hb with hb' | hb' <;> rw [ha', hb']
      · norm_num
        have hf : leech.form (gP j k) (-n) = -2 := by
          rw [map_neg, form_gP_left, ha', hb']; norm_num
        have := hmove (-n) (fun h => hn0 (by simpa using neg_mem h)) (by simp only [map_neg, LinearMap.neg_apply, neg_neg]; exact h4) hf j
          (by rw [lv_add, lv_neg, Pi.add_apply, Pi.neg_apply, lv_gP_apply, ha']; simp [hjk])
        rw [hev, ← sub_eq_add_neg] at this
        rw [this, hP_smul_right]
        congr 1; rw [mul_inv]; ring
      · norm_num
      · norm_num
      · norm_num
        have hf : leech.form (gP j k) n = -2 := by rw [form_gP_left, ha', hb']; norm_num
        rw [hmove n hn0 h4 hf j (by rw [lv_add, Pi.add_apply, lv_gP_apply, ha']; simp [hjk]),
          hP_smul_right]
        congr 1; rw [mul_inv]; ring
    · have ha := hsq j; rw [if_neg (Ne.symm hbj)] at ha
      have hb := hsq k; rw [if_neg (Ne.symm hbk)] at hb
      simp only [hbj, hbk, if_false, or_self, smul_zero]
      rcases int_sq_one ha with ha' | ha' <;> rcases int_sq_one hb with hb' | hb' <;> rw [ha', hb'] <;>
        norm_num

/-- **The `γ₋ = 4e_j − 4e_k` letter on `V₃⁺`**, from the eigen-conditions and the transport
rule `ε(γ₋,n) τ(γ₋ + n) = (2κ₋)⁻¹ τ(n)` along the moves `⟨γ₋,n⟩ = −2`. -/
theorem phiV3_ZM_gM {τ : leech.carrier → TLeechT} (hev : ∀ m, τ (-m) = τ m) {j k : Fin 24}
    (hjk : j ≠ k)
    (heig : ∀ n ∈ halfFourChi 1, kP j k • eL (gP j k) (τ n) = lam j k n • τ n ∧
      kM j k • eL (gM j k) (τ n) = lam j k n • τ n)
    (hrule : ∀ n : leech.carrier, n ∉ lambda0 → leech.form n n = 4 → leech.form (gM j k) n = -2 →
      εΛ (gM j k) n • τ (gM j k + n) = (2 * kM j k)⁻¹ • τ n) :
    ZM (phiV3 τ) OmegaV3 (lV (gM j k) (gM_mem j k)) := by
  refine ZM_of_basis _ _ fun n hn => ?_
  obtain ⟨h4, h1⟩ := mem_halfFourChi hn
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, h1]; exact one_ne_zero
  obtain ⟨hPe, hMe⟩ := heig n hn
  rw [actV_lV (gM_mem j k) hn0 (form_gM_self hjk) h4, map_add, phiV3_frameX0P τ hn,
    actT_sig_lV_gM hjk (blk n) (τ n) hPe hMe, form_gM_left]
  have hsq := lv_sq hn0 h4
  have hk2 : (2 * kM j k) ≠ 0 := mul_ne_zero two_ne_zero (kM_ne_zero hjk)
  -- the moved vectors
  have hmove : ∀ m : leech.carrier, m ∉ lambda0 → leech.form m m = 4 → leech.form (gM j k) m = -2 →
      ∀ i, (lv (gM j k + m) i = 3 ∨ lv (gM j k + m) i = -3) →
      εΛ (gM j k) m • phiV3 τ (frameX0P (gM j k + m)) = hP (cw i) ((2 * kM j k)⁻¹ • τ m) := by
    intro m hm0 hm4 hf i hi
    have h0' := not_mem_add (gM_mem j k) hm0
    have h4' := form_self_add (form_gM_self hjk) hm4 hf
    rw [phiV3_frameX0P_any hev h0' h4', blk_eq_of_three h0' h4' hi, ← hP_smul_right, hrule m hm0 hm4 hf]
  rw [lam_val]
  have hneg4 : leech.form (-n) (-n) = 4 := by simp only [map_neg, LinearMap.neg_apply, neg_neg]; exact h4
  have hneg0 : -n ∉ lambda0 := fun h => hn0 (by simpa using neg_mem h)
  by_cases hbj : blk n = j
  · have hk : k ≠ blk n := hbj ▸ Ne.symm hjk
    have ha := hsq j; rw [if_pos hbj.symm] at ha
    have hb := hsq k; rw [if_neg hk] at hb
    simp only [hbj, true_or, if_true]
    rcases int_sq_nine ha with ha' | ha' <;> rcases int_sq_one hb with hb' | hb' <;> rw [ha', hb']
    · norm_num
    · norm_num
      have hf : leech.form (gM j k) (-n) = -2 := by
        rw [map_neg, form_gM_left, ha', hb']; norm_num
      have := hmove (-n) hneg0 hneg4 hf k
        (by rw [lv_add, lv_neg, Pi.add_apply, Pi.neg_apply, lv_gM_apply, hb']; simp [Ne.symm hjk])
      rw [hev, ← sub_eq_add_neg] at this
      rw [this, hP_smul_right]
      congr 1; rw [mul_inv]; ring
    · norm_num
      have hf : leech.form (gM j k) n = -2 := by rw [form_gM_left, ha', hb']; norm_num
      rw [hmove n hn0 h4 hf k (by rw [lv_add, Pi.add_apply, lv_gM_apply, hb']; simp [Ne.symm hjk]),
        hP_smul_right]
      congr 1; rw [mul_inv]; ring
    · norm_num
  · by_cases hbk : blk n = k
    · have hj : j ≠ blk n := hbk ▸ hjk
      have ha := hsq j; rw [if_neg hj] at ha
      have hb := hsq k; rw [if_pos hbk.symm] at hb
      simp only [hbk, or_true, if_true, if_neg (Ne.symm hjk)]
      rcases int_sq_one ha with ha' | ha' <;> rcases int_sq_nine hb with hb' | hb' <;> rw [ha', hb']
      · norm_num
      · norm_num
        have hf : leech.form (gM j k) (-n) = -2 := by
          rw [map_neg, form_gM_left, ha', hb']; norm_num
        have := hmove (-n) hneg0 hneg4 hf j
          (by rw [lv_add, lv_neg, Pi.add_apply, Pi.neg_apply, lv_gM_apply, ha']; simp [hjk])
        rw [hev, ← sub_eq_add_neg] at this
        rw [this, hP_smul_right]
        congr 1; rw [mul_inv]; ring
      · norm_num
        have hf : leech.form (gM j k) n = -2 := by rw [form_gM_left, ha', hb']; norm_num
        rw [hmove n hn0 h4 hf j (by rw [lv_add, Pi.add_apply, lv_gM_apply, ha']; simp [hjk]),
          hP_smul_right]
        congr 1; rw [mul_inv]; ring
      · norm_num
    · have ha := hsq j; rw [if_neg (Ne.symm hbj)] at ha
      have hb := hsq k; rw [if_neg (Ne.symm hbk)] at hb
      simp only [hbj, hbk, if_false, or_self, smul_zero]
      rcases int_sq_one ha with ha' | ha' <;> rcases int_sq_one hb with hb' | hb' <;> rw [ha', hb'] <;>
        norm_num

end VOA.Moonshine.SigmaTop
