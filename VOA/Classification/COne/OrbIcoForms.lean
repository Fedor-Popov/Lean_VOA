import VOA.Classification.COne.OrbIcoLift

/-! # OrbIco: the invariants `J₆` and `J₁₅` of `ico`

* `a5 : Fin 6 → ℂ³`, the six five-fold axes `(1, ±φ, 0)`, `(φ, 0, ±1)`, `(0, 1, ±φ)`, and
  `J₆ = ∏ lin (a5 i)`;
* `b2 : Fin 15 → ℂ³`, the fifteen two-fold axes (doubled): the coordinate axes and the cyclic
  permutations of `(φ, ±1, ±φ⁻¹)`, and `J₁₅ = ∏ lin (b2 i)`.

The generators `rotC`, `rotR` permute the axes up to sign (`autL_rotC_b2`, `autL_rotR_b2`, ...),
with total sign `+1`, so `J₆` and `J₁₅` are `ico`-invariant (`icoInv_J6`, `icoInv_J15`).
`b2_reach`: every two-fold axis is the image of the `z`-axis under `ico` (up to sign).
`b2_dot`: the Gram data `|b2 i|² = 4`, `(b2 i · b2 j)² ≠ 16` (`i ≠ j`).
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv OrbPrim OrbOcta
  Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

theorem gp_pow_three : gp ^ 3 = 2 * gp + 1 := by
  rw [pow_succ, gp_sq']; linear_combination gp_sq'
theorem gp_pow_four : gp ^ 4 = 3 * gp + 2 := by
  rw [pow_succ, gp_pow_three]; linear_combination 2 * gp_sq'

/-! ## The axes -/

def a5 : Fin 6 → Fin 3 → ℂ :=
  ![![1, gp, 0], ![1, -gp, 0], ![gp, 0, 1], ![gp, 0, -1], ![0, 1, gp], ![0, 1, -gp]]

def b2 : Fin 15 → Fin 3 → ℂ :=
  ![![0, 0, 2], ![0, 2, 0], ![2, 0, 0],
    ![gp, 1, gq], ![gq, gp, 1], ![1, gq, gp],
    ![gp, 1, -gq], ![-gq, gp, 1], ![1, -gq, gp],
    ![gp, -1, gq], ![gq, gp, -1], ![-1, gq, gp],
    ![gp, -1, -gq], ![-gq, gp, -1], ![-1, -gq, gp]]

def cTab5 : Fin 6 → Fin 6 := ![2, 3, 4, 5, 0, 1]
def cSgn5 : Fin 6 → ℂ := ![1, -1, 1, -1, 1, 1]
def rTab5 : Fin 6 → Fin 6 := ![2, 1, 0, 4, 3, 5]
def rSgn5 : Fin 6 → ℂ := ![1, -1, 1, 1, 1, -1]

def cTab2 : Fin 15 → Fin 15 := ![1, 2, 0, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12, 13]
def rTab2 : Fin 15 → Fin 15 := ![14, 9, 4, 3, 2, 6, 5, 12, 10, 1, 8, 11, 7, 13, 0]
def rSgn2 : Fin 15 → ℂ := ![-1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, -1]

theorem autL_rotC_a5 (i : Fin 6) : autL rotC (a5 i) = cSgn5 i • a5 (cTab5 i) := by
  rw [autL_rotC]
  funext k
  fin_cases i <;> fin_cases k <;> simp [a5, cSgn5, cTab5]

theorem autL_rotR_a5 (i : Fin 6) : autL rotR (a5 i) = rSgn5 i • a5 (rTab5 i) := by
  rw [autL_rotR]
  funext k
  fin_cases i <;> fin_cases k <;> simp [a5, rSgn5, rTab5, gq_eq] <;> ring_nf <;>
    simp only [gp_sq', gp_pow_three] <;> ring_nf

theorem autL_rotC_b2 (i : Fin 15) : autL rotC (b2 i) = b2 (cTab2 i) := by
  rw [autL_rotC]
  funext k
  fin_cases i <;> fin_cases k <;> simp [b2, cTab2]

theorem autL_rotR_b2 (i : Fin 15) : autL rotR (b2 i) = rSgn2 i • b2 (rTab2 i) := by
  rw [autL_rotR]
  funext k
  fin_cases i <;> fin_cases k <;> simp [b2, rSgn2, rTab2, gq_eq] <;> ring_nf <;>
    simp only [gp_sq', gp_pow_three] <;> ring_nf


/-! ## The invariants -/

/-- The degree-six invariant: the product of the five-fold axes. -/
def J6 : P3 := ∏ i, lin (a5 i)

/-- The degree-fifteen invariant: the product of the two-fold axes. -/
def J15 : P3 := ∏ i, lin (b2 i)

theorem J6_hom : J6.IsHomogeneous 6 := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin 6)) (fun i => lin (a5 i))
    (fun _ => 1) (fun i _ => lin_hom (a5 i))
  simpa [J6] using h

theorem J15_hom : J15.IsHomogeneous 15 := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin 15)) (fun i => lin (b2 i)) (fun _ => 1)
    (fun i _ => lin_hom (b2 i))
  simpa [J15] using h

theorem prod_lin_smul {n : ℕ} (c : Fin n → ℂ) (v : Fin n → Fin 3 → ℂ) :
    ∏ i, lin (c i • v i) = MvPolynomial.C (∏ i, c i) * ∏ i, lin (v i) := by
  simp only [map_smul, smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

theorem cTab5_bij : Function.Bijective cTab5 := by decide
theorem rTab5_bij : Function.Bijective rTab5 := by decide
theorem cTab2_bij : Function.Bijective cTab2 := by decide
theorem rTab2_bij : Function.Bijective rTab2 := by decide

theorem phiE_rotC_J6 : phiE rotC J6 = J6 := by
  rw [J6, map_prod]
  simp only [phiE_lin, autL_rotC_a5]
  rw [prod_lin_smul, show ∏ i, cSgn5 i = 1 by simp [Fin.prod_univ_succ, cSgn5], map_one,
    one_mul]
  exact Fintype.prod_bijective cTab5 cTab5_bij _ _ (fun _ => rfl)

theorem phiE_rotR_J6 : phiE rotR J6 = J6 := by
  rw [J6, map_prod]
  simp only [phiE_lin, autL_rotR_a5]
  rw [prod_lin_smul, show ∏ i, rSgn5 i = 1 by simp [Fin.prod_univ_succ, rSgn5], map_one,
    one_mul]
  exact Fintype.prod_bijective rTab5 rTab5_bij _ _ (fun _ => rfl)

theorem phiE_rotC_J15 : phiE rotC J15 = J15 := by
  rw [J15, map_prod]
  simp only [phiE_lin, autL_rotC_b2]
  exact Fintype.prod_bijective cTab2 cTab2_bij _ _ (fun _ => rfl)

theorem phiE_rotR_J15 : phiE rotR J15 = J15 := by
  rw [J15, map_prod]
  simp only [phiE_lin, autL_rotR_b2]
  rw [prod_lin_smul, show ∏ i, rSgn2 i = 1 by simp [Fin.prod_univ_succ, rSgn2], map_one,
    one_mul]
  exact Fintype.prod_bijective rTab2 rTab2_bij _ _ (fun _ => rfl)

theorem icoInv_J6 : IcoInv J6 := icoInv_of_gen phiE_rotC_J6 phiE_rotR_J6
theorem icoInv_J15 : IcoInv J15 := icoInv_of_gen phiE_rotC_J15 phiE_rotR_J15

/-! ## Transitivity on the two-fold axes -/

/-- `b2 i` is the image of the `z`-axis under `ico`, up to a nonzero scalar. -/
def Reach (i : Fin 15) : Prop :=
  ∃ g ∈ ico, ∃ c : ℂ, c ≠ 0 ∧ autL g (b2 0) = c • b2 i

theorem reach_zero : Reach 0 := ⟨1, ico.one_mem, 1, one_ne_zero, by rw [autL_one]; simp⟩

theorem Reach.byC {i : Fin 15} (h : Reach i) : Reach (cTab2 i) := by
  obtain ⟨g, hg, c, hc, he⟩ := h
  refine ⟨rotC * g, ico.mul_mem rotC_mem hg, c, hc, ?_⟩
  rw [autL_mul, LinearMap.comp_apply, he, map_smul, autL_rotC_b2]

theorem Reach.byR {i : Fin 15} (h : Reach i) : Reach (rTab2 i) := by
  obtain ⟨g, hg, c, hc, he⟩ := h
  refine ⟨rotR * g, ico.mul_mem rotR_mem hg, c * rSgn2 i, mul_ne_zero hc ?_, ?_⟩
  · fin_cases i <;> simp [rSgn2]
  · rw [autL_mul, LinearMap.comp_apply, he, map_smul, autL_rotR_b2, smul_smul]

/-- The closure of `{0}` under the two tables, step by step. -/
def reachStep (S : Finset (Fin 15)) : Finset (Fin 15) := S ∪ S.image cTab2 ∪ S.image rTab2

theorem reachStep_all : reachStep (reachStep (reachStep (reachStep (reachStep {0})))) =
    Finset.univ := by decide

theorem reach_of_mem_step {S : Finset (Fin 15)} (h : ∀ i ∈ S, Reach i) :
    ∀ i ∈ reachStep S, Reach i := by
  intro i hi
  simp only [reachStep, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with (hi | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
  · exact h i hi
  · exact (h j hj).byC
  · exact (h j hj).byR

/-- Every two-fold axis is reached from the `z`-axis. -/
theorem b2_reach (i : Fin 15) : Reach i := by
  have h0 : ∀ j ∈ ({0} : Finset (Fin 15)), Reach j := by
    intro j hj; rw [Finset.mem_singleton.mp hj]; exact reach_zero
  have h5 := reach_of_mem_step (reach_of_mem_step (reach_of_mem_step (reach_of_mem_step
    (reach_of_mem_step h0))))
  exact h5 i (by rw [reachStep_all]; exact Finset.mem_univ i)

/-! ## Gram data of the two-fold axes -/

def dvCode : Fin 15 → Fin 15 → Fin 8 :=
  ![![7, 0, 0, 3, 1, 5, 4, 1, 5, 3, 2, 5, 4, 2, 5],
    ![0, 7, 0, 1, 5, 3, 1, 5, 4, 2, 5, 3, 2, 5, 4],
    ![0, 0, 7, 5, 3, 1, 5, 4, 1, 5, 3, 2, 5, 4, 2],
    ![3, 1, 5, 7, 5, 5, 5, 3, 1, 1, 1, 0, 3, 0, 4],
    ![1, 5, 3, 5, 7, 5, 1, 5, 3, 0, 1, 1, 4, 3, 0],
    ![5, 3, 1, 5, 5, 7, 3, 1, 5, 1, 0, 1, 0, 4, 3],
    ![4, 1, 5, 5, 1, 3, 7, 0, 0, 3, 5, 2, 1, 3, 6],
    ![1, 5, 4, 3, 5, 1, 0, 7, 0, 2, 3, 5, 6, 1, 3],
    ![5, 4, 1, 1, 3, 5, 0, 0, 7, 5, 2, 3, 3, 6, 1],
    ![3, 2, 5, 1, 0, 1, 3, 2, 5, 7, 4, 4, 5, 6, 0],
    ![2, 5, 3, 1, 1, 0, 5, 3, 2, 4, 7, 4, 0, 5, 6],
    ![5, 3, 2, 0, 1, 1, 2, 5, 3, 4, 4, 7, 6, 0, 5],
    ![4, 2, 5, 3, 4, 0, 1, 6, 3, 5, 0, 6, 7, 2, 2],
    ![2, 5, 4, 0, 3, 4, 3, 1, 6, 6, 5, 0, 2, 7, 2],
    ![5, 4, 2, 4, 0, 3, 6, 3, 1, 0, 6, 5, 2, 2, 7]]

def dvVal : Fin 8 → ℂ := ![0, 2, -2, 2 * gp - 2, 2 - 2 * gp, 2 * gp, -2 * gp, 4]

def dv (i j : Fin 15) : ℂ := dvVal (dvCode i j)

theorem b2_dot_row0 (j : Fin 15) : b2 0 ⬝ᵥ b2 j = dv 0 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row1 (j : Fin 15) : b2 1 ⬝ᵥ b2 j = dv 1 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row2 (j : Fin 15) : b2 2 ⬝ᵥ b2 j = dv 2 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row3 (j : Fin 15) : b2 3 ⬝ᵥ b2 j = dv 3 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row4 (j : Fin 15) : b2 4 ⬝ᵥ b2 j = dv 4 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row5 (j : Fin 15) : b2 5 ⬝ᵥ b2 j = dv 5 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row6 (j : Fin 15) : b2 6 ⬝ᵥ b2 j = dv 6 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row7 (j : Fin 15) : b2 7 ⬝ᵥ b2 j = dv 7 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row8 (j : Fin 15) : b2 8 ⬝ᵥ b2 j = dv 8 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row9 (j : Fin 15) : b2 9 ⬝ᵥ b2 j = dv 9 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row10 (j : Fin 15) : b2 10 ⬝ᵥ b2 j = dv 10 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row11 (j : Fin 15) : b2 11 ⬝ᵥ b2 j = dv 11 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row12 (j : Fin 15) : b2 12 ⬝ᵥ b2 j = dv 12 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row13 (j : Fin 15) : b2 13 ⬝ᵥ b2 j = dv 13 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_row14 (j : Fin 15) : b2 14 ⬝ᵥ b2 j = dv 14 j := by
  fin_cases j <;> simp [b2, dv, dvCode, dvVal, dotProduct, Fin.sum_univ_three, gq_eq] <;>
    ring_nf <;> simp only [gp_sq'] <;> ring_nf

theorem b2_dot_eq (i j : Fin 15) : b2 i ⬝ᵥ b2 j = dv i j := by
  fin_cases i
  · exact b2_dot_row0 j
  · exact b2_dot_row1 j
  · exact b2_dot_row2 j
  · exact b2_dot_row3 j
  · exact b2_dot_row4 j
  · exact b2_dot_row5 j
  · exact b2_dot_row6 j
  · exact b2_dot_row7 j
  · exact b2_dot_row8 j
  · exact b2_dot_row9 j
  · exact b2_dot_row10 j
  · exact b2_dot_row11 j
  · exact b2_dot_row12 j
  · exact b2_dot_row13 j
  · exact b2_dot_row14 j

theorem gp_re : gp.re = (1 + Real.sqrt 5) / 2 := by
  simp [gp, s5]

theorem gp_ne_three : gp ≠ 3 := by
  intro h
  have := congrArg Complex.re h
  rw [gp_re] at this
  have h5 : Real.sqrt 5 = 5 := by norm_num at this; linarith
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  rw [h5] at this
  norm_num at this

theorem gp_ne_neg_two : gp ≠ -2 := by
  intro h
  have := congrArg Complex.re h
  rw [gp_re] at this
  norm_num at this
  linarith [Real.sqrt_nonneg 5]

theorem dv_sq_ne (i j : Fin 15) (hij : i ≠ j) : (dv i j) ^ 2 ≠ 16 := by
  have k1 : ((2 : ℂ) * gp - 2) ^ 2 ≠ 16 := by
    intro h; apply gp_ne_neg_two; linear_combination (-1 / 4 : ℂ) * h + gp_sq'
  have k2 : ((2 : ℂ) - 2 * gp) ^ 2 ≠ 16 := by
    intro h; apply k1; linear_combination h
  have k3 : ((2 : ℂ) * gp) ^ 2 ≠ 16 := by
    intro h; apply gp_ne_three; linear_combination (1 / 4 : ℂ) * h - gp_sq'
  have k4 : ((-2 : ℂ) * gp) ^ 2 ≠ 16 := by
    intro h; apply k3; linear_combination h
  have k5 : (0 : ℂ) ^ 2 ≠ 16 := by norm_num
  have k6 : (2 : ℂ) ^ 2 ≠ 16 := by norm_num
  have k7 : (-2 : ℂ) ^ 2 ≠ 16 := by norm_num
  have hc : ∀ i j : Fin 15, i ≠ j → dvCode i j ≠ 7 := by decide
  have h7 := hc i j hij
  rw [dv]
  generalize dvCode i j = c at h7 ⊢
  fin_cases c
  · exact k5
  · exact k6
  · exact k7
  · exact k1
  · exact k2
  · exact k3
  · exact k4
  · exact absurd rfl h7

/-- The Gram data of the two-fold axes. -/
theorem b2_dot (i j : Fin 15) (hij : i ≠ j) : (b2 i ⬝ᵥ b2 j) ^ 2 ≠ 16 := by
  rw [b2_dot_eq]; exact dv_sq_ne i j hij

theorem b2_dot_self (i : Fin 15) : b2 i ⬝ᵥ b2 i = 4 := by
  rw [b2_dot_eq]; fin_cases i <;> simp [dv, dvCode, dvVal]

end VOA.Classification.COne.OrbIco
