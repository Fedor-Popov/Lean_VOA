import VOA.Classification.COne.PlusRat3Quad

/-! # `H⁴₍ⱼ₎E` as Virasoro descendants of `E`

With `K = ⟨α,α⟩ = 2m` (charge coordinate `c`, `c² = K`), on `e^{±α}` Abe's `H⁴` acts by
`[o(H⁴), Y(e^β,z)] = z Y(β(-1)e^β) + 3z² Y(β(-2)e^β) + 2z³ Y(β(-3)e^β)`, whence

* `H⁴₍₃₎E = 0`, `3 H⁴₍₂₎E = L(-1)E`,
* `(2K-1) H⁴₍₁₎E = 2K L(-2)E - L(-1)²E`,
* `(2K-1)(K-2) H⁴₍₀₎E = 2(K(2K-3) L(-3)E - 2K L(-2)L(-1)E + L(-1)³E)`,

with `L(-2) = ω₍₋₁₎`, `L(-3) = ω₍₋₂₎`.  These are polynomial identities in `c`, certified by
the charged evaluator.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary

/-! ## §1  Charged certificates (variable `0` is the charge coordinate `c`) -/

def P0 : RawPoly ℕ := [(1, [])]
def LmC (P : RawPoly ℕ) : RawPoly ℕ := normR (polyActWC omR (-1) P)
def cc2 (P : RawPoly ℕ) : RawPoly ℕ := prependC 0 (prependC 0 P)

theorem certE3 : normR (polyActWC H4R (-3 - 1) P0) = [] := by decide +kernel

theorem certE2 : normR (scaleR 3 (polyActWC H4R (-2 - 1) P0)) = normR (LmC P0) := by
  decide +kernel

theorem certE1 :
    normR (scaleR 2 (cc2 (polyActWC H4R (-1 - 1) P0)) ++ scaleR (-1) (polyActWC H4R (-1 - 1) P0)) =
      normR (scaleR 2 (cc2 (polyActWC omR (-(-1) - 1) P0)) ++ scaleR (-1) (LmC (LmC P0))) := by
  decide +kernel

theorem certE0 :
    normR (scaleR 2 (cc2 (cc2 (polyActWC H4R (-0 - 1) P0))) ++
        scaleR (-5) (cc2 (polyActWC H4R (-0 - 1) P0)) ++ scaleR 2 (polyActWC H4R (-0 - 1) P0)) =
      normR (scaleR 4 (cc2 (cc2 (polyActWC omR (-(-2) - 1) P0))) ++
        scaleR (-6) (cc2 (polyActWC omR (-(-2) - 1) P0)) ++
        scaleR (-4) (cc2 (polyActWC omR (-(-1) - 1) (LmC P0))) ++
        scaleR 2 (LmC (LmC (LmC P0)))) := by
  decide +kernel

/-! ## §2  The identities in `V⁺` -/

variable (m : ℕ) (hm : 1 ≤ m)

theorem eq_of_hasC {y z : VP m hm} {P Q : RawPoly ℕ} (hy : HasC m hm y P) (hz : HasC m hm z Q)
    (h : normR P = normR Q) : y = z := by
  have := hasC_of_normR_eq m hm hy h
  rw [HasC] at this hz
  rw [this, hz]

theorem hasC_y0 : HasC m hm (y0 m hm) P0 := hasC_stP m hm _

theorem hasC_H4 (j : ℤ) {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) :
    HasC m hm ((V2mPlus m hm).smul (HP m hm 2) j y) (polyActWC H4R (-j - 1) P) :=
  hasC_smul_left m hm (hasN_HP m hm 2 (by norm_num) (by norm_num)) hy j

theorem hasC_om (j : ℤ) {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) :
    HasC m hm ((V2mPlus m hm).smul (V2mPlus m hm).conformalVector j y) (polyActWC omR (-j - 1) P) :=
  hasC_smul_left m hm (hasN_omega m hm) hy j

theorem hasC_Lm {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) :
    HasC m hm ((V2mPlus m hm).L (-1) y) (LmC P) := by
  rw [L_neg_one_eq_smul]
  exact hasC_normR m hm (hasC_om m hm 0 hy)

theorem hasC_cc2 {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) :
    HasC m hm (cα m • cα m • y) (cc2 P) := hasC_c m hm (hasC_c m hm hy)

/-- `H⁴₍₃₎E = 0`. -/
theorem H4_3_E : (V2mPlus m hm).smul (HP m hm 2) 3 (EP m hm) = 0 := by
  rw [EP_eq_y0, PreVertexAlgebra.smul_smul_right]
  have h := eq_of_hasC m hm (hasC_H4 m hm 3 (hasC_y0 m hm)) (hasC_zero m hm) (by
    rw [certE3]; rfl)
  rw [h, smul_zero]

/-- `3 H⁴₍₂₎E = L(-1)E`. -/
theorem H4_2_E : (3 : ℂ) • (V2mPlus m hm).smul (HP m hm 2) 2 (EP m hm) =
    (V2mPlus m hm).L (-1) (EP m hm) := by
  rw [EP_eq_y0, PreVertexAlgebra.smul_smul_right, map_smul, smul_comm]
  congr 1
  have h := eq_of_hasC m hm (hasC_smul m hm (hasC_H4 m hm 2 (hasC_y0 m hm)) 3)
    (hasC_Lm m hm (hasC_y0 m hm)) certE2
  rw [← h]; norm_num

/-- `(2K-1) H⁴₍₁₎E = 2K L(-2)E - L(-1)²E`, `K = 2m`. -/
theorem H4_1_E : (2 * (2 * (m : ℂ)) - 1) • (V2mPlus m hm).smul (HP m hm 2) 1 (EP m hm) =
    (2 * (2 * (m : ℂ))) • (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1) (EP m hm) -
      (V2mPlus m hm).L (-1) ((V2mPlus m hm).L (-1) (EP m hm)) := by
  rw [EP_eq_y0, PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_smul_right, map_smul, map_smul,
    smul_comm _ (2 : ℂ), smul_comm _ (2 : ℂ), ← smul_sub]
  congr 1
  have hA := hasC_H4 m hm 1 (hasC_y0 m hm)
  have hB := hasC_om m hm (-1) (hasC_y0 m hm)
  have hC := hasC_Lm m hm (hasC_Lm m hm (hasC_y0 m hm))
  have h := eq_of_hasC m hm (hasC_add m hm (hasC_smul m hm (hasC_cc2 m hm hA) 2) (hasC_smul m hm hA (-1)))
    (hasC_add m hm (hasC_smul m hm (hasC_cc2 m hm hB) 2) (hasC_smul m hm hC (-1))) certE1
  push_cast at h
  have hsq := cα_sq m hm
  linear_combination (norm := module) h -
    (2 * hsq) • (V2mPlus m hm).smul (HP m hm 2) 1 (y0 m hm) +
    (2 * hsq) • (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1) (y0 m hm)

/-- `(2K²-5K+2) H⁴₍₀₎E = (4K²-6K) L(-3)E - 4K L(-2)L(-1)E + 2 L(-1)³E`, `K = 2m`. -/
theorem H4_0_E : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) •
      (V2mPlus m hm).smul (HP m hm 2) 0 (EP m hm) =
    (4 * (2 * (m : ℂ)) ^ 2 - 6 * (2 * (m : ℂ))) •
        (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-2) (EP m hm) -
      (4 * (2 * (m : ℂ))) • (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1)
        ((V2mPlus m hm).L (-1) (EP m hm)) +
      (2 : ℂ) • (V2mPlus m hm).L (-1) ((V2mPlus m hm).L (-1) ((V2mPlus m hm).L (-1) (EP m hm))) := by
  rw [EP_eq_y0]
  simp only [PreVertexAlgebra.smul_smul_right, map_smul]
  rw [smul_comm _ (2 : ℂ), smul_comm _ (2 : ℂ), smul_comm _ (2 : ℂ), smul_comm _ (2 : ℂ),
    ← smul_sub, ← smul_add]
  congr 1
  have hA := hasC_H4 m hm 0 (hasC_y0 m hm)
  have hB := hasC_om m hm (-2) (hasC_y0 m hm)
  have hD := hasC_om m hm (-1) (hasC_Lm m hm (hasC_y0 m hm))
  have hC := hasC_Lm m hm (hasC_Lm m hm (hasC_Lm m hm (hasC_y0 m hm)))
  have h := eq_of_hasC m hm
    (hasC_add m hm (hasC_add m hm (hasC_smul m hm (hasC_cc2 m hm (hasC_cc2 m hm hA)) 2)
      (hasC_smul m hm (hasC_cc2 m hm hA) (-5))) (hasC_smul m hm hA 2))
    (hasC_add m hm (hasC_add m hm (hasC_add m hm (hasC_smul m hm (hasC_cc2 m hm (hasC_cc2 m hm hB)) 4)
      (hasC_smul m hm (hasC_cc2 m hm hB) (-6))) (hasC_smul m hm (hasC_cc2 m hm hD) (-4)))
      (hasC_smul m hm hC 2)) certE0
  push_cast at h
  have hsq := cα_sq m hm
  have hsq4 : cα m * cα m * cα m * cα m = (2 * (m : ℂ)) ^ 2 := by
    rw [mul_assoc (cα m * cα m), hsq]; ring
  linear_combination (norm := module) h -
    (2 * hsq4) • (V2mPlus m hm).smul (HP m hm 2) 0 (y0 m hm) +
    (5 * hsq) • (V2mPlus m hm).smul (HP m hm 2) 0 (y0 m hm) +
    (4 * hsq4) • (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-2) (y0 m hm) -
    (6 * hsq) • (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-2) (y0 m hm) -
    (4 * hsq) • (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1)
      ((V2mPlus m hm).L (-1) (y0 m hm))

end VOA.Classification.COne.PlusRat3
