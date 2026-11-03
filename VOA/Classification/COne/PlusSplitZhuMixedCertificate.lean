import VOA.Classification.COne.PlusSplitZhuWReduction

/-! A charged O(V) certificate for the mixed Zhu product W E. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuMixed
open PlusUnitary PlusC2 PlusC2Eval VOA.SparseRational

/-- Evaluation of the scalar polynomial used by a charged certificate. -/
def scalarC (c : ℂ) (cs : List (ℚ × ℕ)) : ℂ :=
  (cs.map fun qe => (qe.1 : ℂ) * c ^ qe.2).sum

theorem hasC_cmulR_exact (m : ℕ) (hm : 1 ≤ m)
    {y : VP m hm} {G : RawPoly ℕ} (hy : HasC m hm y G)
    (cs : List (ℚ × ℕ)) :
    HasC m hm (scalarC (cα m) cs • y) (cmulR cs G) := by
  induction cs with
  | nil => simpa [scalarC, cmulR] using hasC_zero m hm
  | cons qe cs ih =>
    simpa [scalarC, cmulR, add_smul, mul_smul] using
      hasC_add m hm (hasC_smul m hm (hasC_cpow m hm hy qe.2) qe.1) ih

def dC : List (ℚ × ℕ) := [(4,4), (-20,2), (9,0)]
def aC : List (ℚ × ℕ) := [(-60,0), (80,2)]
def bC : List (ℚ × ℕ) := [(-18,4), (40,2), (-3,0)]
def cC : List (ℚ × ℕ) := [(15/16,4), (-15/8,2)]
def prefC : List (ℚ × ℕ) := [(1,3), (-2,1)]
def wY : RawPoly ℕ := zhuRC 4 WR Y0
def oY : RawPoly ℕ := zhuRC 2 omR Y0
def ooY : RawPoly ℕ := zhuRC 2 omR oY
def target : RawPoly ℕ := cmulR prefC
  (cmulR dC wY ++ cmulR aC ooY ++ cmulR bC oY ++ cmulR cC Y0)

def certificate : List CEntry :=
[
  ([((-45 / 2 : ℚ), 1), ((135 / 2 : ℚ), 3), ((-705 / 8 : ℚ), 5), ((30 / 1 : ℚ), 7)], [], [], 0),
  ([((13209 / 2 : ℚ), 2), ((97 / 4 : ℚ), 4), ((316 / 1 : ℚ), 6)], [], [1], 0),
  ([((19329 / 1 : ℚ), 0), ((52675 / 2 : ℚ), 2), ((1336 / 1 : ℚ), 4), ((604 / 1 : ℚ), 6)],
    [], [2], 0),
  ([((30942 / 1 : ℚ), 1), ((7247 / 2 : ℚ), 3), ((614 / 1 : ℚ), 5)], [], [1, 1], 0),
  ([((38598 / 1 : ℚ), 0), ((33424 / 1 : ℚ), 2), ((1648 / 1 : ℚ), 4), ((640 / 1 : ℚ), 6)],
    [], [3], 0),
  ([((65079 / 1 : ℚ), 1), ((8072 / 1 : ℚ), 3), ((1064 / 1 : ℚ), 5)], [], [2, 1], 0),
  ([((19314 / 1 : ℚ), 0), ((3529 / 1 : ℚ), 2), ((132 / 1 : ℚ), 4)], [], [1, 1, 1], 0),
  ([((19284 / 1 : ℚ), 0), ((13556 / 1 : ℚ), 2), ((560 / 1 : ℚ), 4), ((272 / 1 : ℚ), 6)],
    [], [4], 0),
  ([((29256 / 1 : ℚ), 1), ((4032 / 1 : ℚ), 3), ((384 / 1 : ℚ), 5)], [], [3, 1], 0),
  ([((4986 / 1 : ℚ), 1), ((224 / 1 : ℚ), 3), ((136 / 1 : ℚ), 5)], [], [2, 2], 0),
  ([((19284 / 1 : ℚ), 0), ((3584 / 1 : ℚ), 2), ((112 / 1 : ℚ), 4)], [], [2, 1, 1], 0),
  ([((-4758 / 1 : ℚ), 1)], [0, 0], [], 0),
  ([((19383 / 1 : ℚ), 1)], [0, 0], [], 1),
  ([((-45 / 1 : ℚ), 0)], [0, 0], [1], 0),
  ([((-17934 / 1 : ℚ), 1)], [0, 0], [], 2),
  ([((-19284 / 1 : ℚ), 0), ((-5594 / 1 : ℚ), 2), ((480 / 1 : ℚ), 4), ((-136 / 1 : ℚ), 6)],
    [0, 0], [1], 1),
  ([((-8154 / 1 : ℚ), 1), ((-1384 / 1 : ℚ), 3), ((-56 / 1 : ℚ), 5)], [0, 0], [1, 1], 0),
  ([((-9642 / 1 : ℚ), 0), ((1184 / 1 : ℚ), 2), ((760 / 1 : ℚ), 4)], [0, 0], [2], 0),
  ([((-744 / 1 : ℚ), 1), ((-204 / 1 : ℚ), 3)], [0, 0, 0, 0], [], 0),
  ([((1488 / 1 : ℚ), 1), ((408 / 1 : ℚ), 3)], [1, 1], [], 0)
]

theorem certificate_even : ∀ t ∈ certificate, Even t.2.1.length := by decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Kernel evaluation of the finite rational certificate needs this local budget.
theorem certificate_check : normR (certC certificate) = normR target := by
  decide +kernel

variable (m : ℕ) (hm : 1 ≤ m)

def mixedState : VP m hm :=
  scalarC (cα m) dC • zhuMul (V2mPlus m hm) (WP m hm) (y0 m hm) +
  scalarC (cα m) aC • zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector
    (zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector (y0 m hm)) +
  scalarC (cα m) bC • zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector (y0 m hm) +
  scalarC (cα m) cC • y0 m hm

theorem hasC_target :
    HasC m hm ((cα m ^ 3 - 2 * cα m) • mixedState m hm) target := by
  have h0 : HasC m hm (y0 m hm) Y0 := hasC_stP m hm Y0
  have ho := hasC_zhuMul m hm (omega_mem m hm) (omega_coe m hm) h0
  have hoo := hasC_zhuMul m hm (omega_mem m hm) (omega_coe m hm) ho
  have hw := hasC_zhuMul m hm (WP_mem_grading m hm) (hasPoly_W m hm) h0
  have h := hasC_cmulR_exact m hm (hasC_add m hm (hasC_add m hm (hasC_add m hm
    (hasC_cmulR_exact m hm hw dC) (hasC_cmulR_exact m hm hoo aC))
    (hasC_cmulR_exact m hm ho bC)) (hasC_cmulR_exact m hm h0 cC)) prefC
  convert h using 1
  simp [mixedState, scalarC, prefC, sub_eq_add_neg]

theorem mixedState_mem_O (hm2 : 2 ≤ m) : mixedState m hm ∈ O (V2mPlus m hm) := by
  obtain ⟨y, hy, hyC⟩ := certC_mem m hm certificate certificate_even
  have he := hasC_of_normR_eq m hm hyC certificate_check
  have ht := hasC_target m hm
  have heq : (cα m ^ 3 - 2 * cα m) • mixedState m hm = y := ht.trans he.symm
  have h := (O (V2mPlus m hm)).smul_mem ((cα m ^ 3 - 2 * cα m)⁻¹) (heq.symm ▸ hy)
  simpa only [smul_smul, inv_mul_cancel₀ (cα_poly_ne_zero m hm hm2), one_smul] using h

end VOA.Classification.COne.PlusZhuMixed

