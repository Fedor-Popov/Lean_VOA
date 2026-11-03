import VOA.Classification.COne.PlusUnitaryEE
import VOA.Classification.COne.PlusC2Degree
import VOA.Classification.COne.LatticeNice
import VOA.Modules.ZhuVermaAnArchFiltrationFinal
import VOA.Modules.ZeroModeMult

/-!
# OrbSgl (3): zero modes of Fock states on the tops `e^{λ_j}` of `V_{L+λ_j}`

For `V_{2m}` (`L = √(2m)ℤ`) and its module `V_{L+λ_j}` (`|j| ≤ m`), let `t = χ_j(0)` be the
`h(0)`-eigenvalue of the top vector `x = e^{λ_j}`.  Then for every word state
`h(-i₁-1)⋯h(-i_k-1)𝟙`,

  `o(h(-i₁-1)⋯h(-i_k-1)𝟙) x = ∏ₗ (-1)^{iₗ} t · x`          (`oMod_word_top`),

and linearly `o(ls P) x = fockVal t P · x` (`oMod_ls_top`).

Proof (Zhu calculus on the lowest-weight space): `h₍₋ₖ₋₂₎y + h₍₋ₖ₋₁₎y ∈ O(V)` (`Hres_mem_O`), so
`o(h₍₋ᵢ₋₁₎y) = (-1)ⁱ o(h₍₋₁₎y)` on `x`; `h * y = h₍₋₁₎y + h₍₀₎y` with `h₍₀₎y = 0` on the
charge-`0` sector, and `o(h * y) x = o(h) o(y) x` (`oMod_zhuMul_lowest`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  LatMod MvPolynomial PlusUnitary PlusC2 PlusC2Eval VOA.SparseRational

variable (m : ℕ) (hm : 1 ≤ m) (j : ℤ)

/-- The word state `h(-i₁-1)⋯h(-i_k-1)𝟙`. -/
abbrev wS (w : List ℕ) : LatModuleGen (latP m) := latStateGen (latP m) (evalWord (xv (a0 m)) w) 0

/-- Its value on a top with `h(0)`-eigenvalue `t`. -/
def wordVal (t : ℂ) : List ℕ → ℂ
  | [] => 1
  | i :: w => (-1 : ℂ) ^ i * t * wordVal t w

/-- The value of a raw polynomial. -/
def fockVal (t : ℂ) (P : RawPoly ℕ) : ℂ := (P.map fun s => ((s.1 : ℚ) : ℂ) * wordVal t s.2).sum

theorem wS_mem (w : List ℕ) : wS m w ∈ (V2m m hm).grading (wWt w : ℤ) :=
  latStateGen_mem_grading m hm (evalWord_mem_grading (a0 m) w)

theorem boson_mem : bosonState (latP m) (a0 m) ∈ (V2m m hm).grading 1 := by
  rw [bosonState_eq_evR]
  exact h_mem_grading m hm

theorem boson_smul_wS_neg (i : ℕ) (w : List ℕ) :
    (V2m m hm).smul (bosonState (latP m) (a0 m)) (-(i : ℤ) - 1) (wS m w) = wS m (i :: w) := by
  unfold V2m
  rw [smul_bosonState_latStateGen, if_neg (by omega), add_zero, oscN_neg_eq_mulXN]
  change _ = latStateGen (latP m) (evalWord (xv (a0 m)) (i :: w)) 0
  rw [evalWord_cons]

theorem boson_smul_wS_zero (w : List ℕ) :
    (V2m m hm).smul (bosonState (latP m) (a0 m)) 0 (wS m w) = 0 := by
  unfold V2m
  rw [smul_bosonState_latStateGen, if_pos rfl, oscN_zero, LinearMap.zero_apply,
    chargeCoord_zero, zero_smul, add_zero]
  simp [latStateGen]

theorem boson_two_term_mem_O (k : ℕ) (y : LatModuleGen (latP m)) :
    (V2m m hm).smul (bosonState (latP m) (a0 m)) (-(k : ℤ) - 2) y +
      (V2m m hm).smul (bosonState (latP m) (a0 m)) (-(k : ℤ) - 1) y ∈ O (V2m m hm) := by
  have h := Hres_mem_O (V2m m hm) (M := 1) (a := bosonState (latP m) (a0 m))
    (by exact_mod_cast boson_mem m hm) y k 0
  unfold Hres Gres at h
  simp only [add_zero, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have c0 : cbz ((1 : ℕ) : ℤ) ((0 : ℕ) : ℤ) = 1 := by simp
  have c1 : cbz ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num), show (((1 : ℕ) : ℤ)).toNat = 1 from rfl, gBinom]
    norm_num [Finset.prod_range_one]
  rw [c0, c1, one_smul, one_smul] at h
  have h0 : ((0 : ℕ) : ℤ) - ((2 + 0 + k : ℕ) : ℤ) = -(k : ℤ) - 2 := by push_cast; ring
  have h1 : ((1 : ℕ) : ℤ) - ((2 + 0 + k : ℕ) : ℤ) = -(k : ℤ) - 1 := by push_cast; ring
  rw [h0, h1] at h
  exact h

section Top

variable {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2m m hm) M) {h : ℂ}
  (hcw : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h)

include hcw hx in
theorem oMod_boson_neg (y : LatModuleGen (latP m)) (i : ℕ) :
    oMod N ((V2m m hm).smul (bosonState (latP m) (a0 m)) (-(i : ℤ) - 1) y) x =
      ((-1 : ℂ) ^ i) • oMod N ((V2m m hm).smul (bosonState (latP m) (a0 m)) (-1) y) x := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h0 := oMod_eq_zero_of_mem_O N hcw (boson_two_term_mem_O m hm i y) hx
    rw [map_add, LinearMap.add_apply, add_eq_zero_iff_eq_neg] at h0
    rw [show (-((i + 1 : ℕ) : ℤ) - 1) = -(i : ℤ) - 2 by push_cast; ring, h0, ih, pow_succ,
      mul_neg_one, neg_smul]

include hcw hx in
/-- The zero mode of a word state on a top with `h(0)`-eigenvalue `t`. -/
theorem oMod_word_top {t : ℂ} (ht : oMod N (bosonState (latP m) (a0 m)) x = t • x) :
    ∀ w : List ℕ, oMod N (wS m w) x = wordVal t w • x
  | [] => by
    have hv : wS m [] = (V2m m hm).vacuum := by
      change latStateGen (latP m) (evalWord (xv (a0 m)) []) 0 = latVacuumGen (latP m)
      rw [evalWord_nil]; rfl
    rw [hv, oMod_vacuum, LinearMap.id_apply, wordVal, one_smul]
  | i :: w => by
    have ih := oMod_word_top ht w
    rw [← boson_smul_wS_neg m hm i w, oMod_boson_neg m hm N hcw hx _ i]
    have hz := oMod_zhuMul_lowest N hcw (boson_mem m hm) (wS_mem m hm w) hx (by norm_num)
      (by positivity)
    rw [zhuMul_homogeneous _ (boson_mem m hm)] at hz
    simp only [show ((1 : ℤ)).toNat + 1 = 2 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add] at hz
    have c0 : cbz (1 : ℤ) ((0 : ℕ) : ℤ) = 1 := by simp
    rw [c0, one_smul, show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num,
      show ((1 : ℕ) : ℤ) - 1 = 0 by norm_num, boson_smul_wS_zero, smul_zero, add_zero, ih,
      map_smul, ht, smul_smul] at hz
    rw [hz, smul_smul, wordVal]
    ring_nf

include hcw hx in
/-- Linear extension: `o(ls P) x = fockVal t P · x`. -/
theorem oMod_ls_top {t : ℂ} (ht : oMod N (bosonState (latP m) (a0 m)) x = t • x) :
    ∀ P : RawPoly ℕ, oMod N (ls m P) x = fockVal t P • x
  | [] => by
    change oMod N (latStateGen (latP m) (evR (a0 m) []) 0) x = _
    rw [evR_nil]
    simp [fockVal, latStateGen]
  | s :: P => by
    have ih := oMod_ls_top ht P
    change oMod N (latStateGen (latP m) (evR (a0 m) (s :: P)) 0) x = _
    rcases s with ⟨c, w⟩
    rw [evR_cons, latStateGen_add_boson, latStateGen_csmul, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]
    change ((c : ℂ)) • oMod N (wS m w) x + oMod N (ls m P) x = _
    rw [oMod_word_top m hm N hcw hx ht w, ih, smul_smul, ← add_smul]
    simp [fockVal, List.map_cons, List.sum_cons]

end Top

/-! ## The lattice-module tops -/

include hm in
theorem oMod_boson_latticeTop :
    oMod (latticeModule m hm j) (bosonState (latP m) (a0 m)) (latVacuumGen (latP m)) =
      chi m j 0 • latVacuumGen (latP m) := by
  rw [oMod_homogeneous _ (boson_mem m hm), show (1 : ℤ) - 1 = 0 by norm_num]
  change mode ((latticeModule m hm j).YM (hb m)) 0 (latStateGen (latP m) (vacuumN _) 0) = _
  rw [← hVec_eq_hb, latticeModule_zeroMode]
  rfl

/-! ## Even words: rational values -/

/-- `∑ c (-1)^{Σ i} s^{k/2}` (the value when `t² = s` and every word has even length). -/
def evenVal (s : ℚ) (P : RawPoly ℕ) : ℚ :=
  (P.map fun x => x.1 * (-1) ^ x.2.sum * s ^ (x.2.length / 2)).sum

theorem wordVal_eq (t : ℂ) : ∀ w : List ℕ, wordVal t w = (-1 : ℂ) ^ w.sum * t ^ w.length
  | [] => by simp [wordVal]
  | i :: w => by
    rw [wordVal, wordVal_eq t w, List.sum_cons, List.length_cons, pow_add, pow_succ]
    ring

theorem fockVal_eq_evenVal {t : ℂ} {s : ℚ} (ht : t ^ 2 = (s : ℂ)) :
    ∀ P : RawPoly ℕ, (∀ x ∈ P, x.2.length % 2 = 0) → fockVal t P = ((evenVal s P : ℚ) : ℂ)
  | [], _ => by simp [fockVal, evenVal]
  | x :: P, h => by
    have ih := fockVal_eq_evenVal ht P (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [fockVal, evenVal, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, wordVal_eq]
    have hl : t ^ x.2.length = (s : ℂ) ^ (x.2.length / 2) := by
      rw [← ht, ← pow_mul]
      congr 1
      omega
    rw [hl]
    push_cast
    ring

include hm in
theorem chi_zero_sq : chi m j 0 ^ 2 = (((j ^ 2 : ℤ) : ℚ) / (2 * m) : ℚ) := by
  rw [chi_zero_eq hm j, div_pow]
  have hc : chargeCoord (latP m) ((1 : ℤ) : (latP m).carrier) (a0 m) ^ 2 = 2 * (m : ℂ) := by
    rw [pow_two]; exact cα_sq m hm
  rw [hc]
  push_cast
  ring

end VOA.Classification.COne.OrbSgl
