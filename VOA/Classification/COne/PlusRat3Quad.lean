import VOA.Classification.COne.PlusUnitaryEE
import VOA.Classification.COne.PlusUnitaryERel

/-! # Abe's quadratic states `H⁴, H⁶, H⁸` in `V_{2m}⁺` and their products

Orthonormal boson `h`, raw variables `x_i = h(-i-1)`.  Abe's states
(`H^{2r}` is characterised by `o(H^{2r}) = Σ_{n>0} n^{2r-2} h(-n)h(n)` on every Fock module):

* `H⁴ = (x₂x₀ - x₁²)/3`,
* `H⁶ = x₄x₀/5 - 13x₃x₁/10 + 11x₂²/10`,
* `H⁸ = x₆x₀/7 - 20x₅x₁/7 + 397x₄x₂/35 - 302x₃²/35`.

This file proves, by the certified neutral evaluator (`decide +kernel`):

* the products `H^{2r}₍ⱼ₎H^{2s}` entering the commutators `[o(H⁴), H⁴₍₂₎]`, `[o(H⁴), H⁶₍₄₎]`,
  `[o(H⁶), H⁴₍₂₎]`, each as an explicit combination of `L(-1)^k H^{2t}` (`H² = ω`);
* `L(1)H⁴`, `L(1)H⁶`, and `W⁴ = 10H⁴ + L(-1)²ω/3`;
* `H⁴, H⁶ ∈ O(V_{2m})` (Frenkel–Zhu residue certificates).

Nothing here is specific to `m`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary

/-! ## §1  Raw polynomials -/

def H4R : RawPoly ℕ := [(1 / 3, [2, 0]), (-1 / 3, [1, 1])]
def H6R : RawPoly ℕ := [(1 / 5, [4, 0]), (-13 / 10, [3, 1]), (11 / 10, [2, 2])]
def H8R : RawPoly ℕ := [(1 / 7, [6, 0]), (-20 / 7, [5, 1]), (397 / 35, [4, 2]), (-302 / 35, [3, 3])]

/-- `H^{2t}` as a raw polynomial (`t = 1` is `ω`). -/
def HR : ℕ → RawPoly ℕ
  | 1 => omR
  | 2 => H4R
  | 3 => H6R
  | 4 => H8R
  | _ => []

/-- `L(-1) = ω₍₀₎` on raw polynomials. -/
def LmR (P : RawPoly ℕ) : RawPoly ℕ := normR (polyActW omR (-1) P)

/-- `L(-1)^k`. -/
def LmPow : ℕ → RawPoly ℕ → RawPoly ℕ
  | 0, P => P
  | k + 1, P => LmR (LmPow k P)

/-- A combination `Σ c · L(-1)^k H^{2t}` given by triples `(c, k, t)`. -/
def combR : List (ℚ × ℕ × ℕ) → RawPoly ℕ
  | [] => []
  | (c, k, t) :: rest => scaleR c (LmPow k (HR t)) ++ combR rest

/-! ## §2  States of `V⁺` described by neutral polynomials -/

variable (m : ℕ) (hm : 1 ≤ m)

/-- `y` is the neutral state of the raw polynomial `P`. -/
def HasN (y : VP m hm) (P : RawPoly ℕ) : Prop := (y : LatModuleGen (latP m)) = ls m P

theorem hasN_add {y z : VP m hm} {P Q : RawPoly ℕ} (hy : HasN m hm y P) (hz : HasN m hm z Q) :
    HasN m hm (y + z) (P ++ Q) := by
  rw [HasN, Submodule.coe_add, hy, hz, ls_append]

theorem hasN_smul {y : VP m hm} {P : RawPoly ℕ} (hy : HasN m hm y P) (q : ℚ) :
    HasN m hm (((q : ℚ) : ℂ) • y) (scaleR q P) := by
  rw [HasN, Submodule.coe_smul, hy, ls_scaleR]

theorem hasN_zero : HasN m hm 0 ([] : RawPoly ℕ) := by
  rw [HasN, ls_nil]; rfl

theorem hasN_smul_left {u v : VP m hm} {Q P : RawPoly ℕ} (hu : HasN m hm u Q) (hv : HasN m hm v P)
    (n : ℤ) : HasN m hm ((V2mPlus m hm).smul u n v) (polyActW Q (-n - 1) P) := by
  rw [HasN, V2mPlus_smul_coe, hu, hv, ls, ls, V2m_smul_evR_W]

theorem hasN_omega : HasN m hm (V2mPlus m hm).conformalVector omR := omega_coe m hm

theorem eq_of_hasN {y z : VP m hm} {P Q : RawPoly ℕ} (hy : HasN m hm y P) (hz : HasN m hm z Q)
    (h : normR P = normR Q) : y = z := by
  apply Subtype.ext
  rw [hy, hz, ← ls_normR m P, h, ls_normR]

/-- The neutral state of an even raw polynomial. -/
def nP (P : RawPoly ℕ) : VP m hm := PP m hm (ls m P)

theorem theta_ls_even (P : RawPoly ℕ) (hP : ∀ t ∈ P, Even t.2.length) :
    thetaLat (latP m) (ls m P) = ls m P := by
  induction P with
  | nil => rw [ls_nil, map_zero]
  | cons t P ih =>
    have hsplit : ls m (t :: P) = ls m [t] + ls m P := by
      rw [← ls_append]; rfl
    rw [hsplit, map_add, ih (fun s hs => hP s (List.mem_cons_of_mem _ hs))]
    congr 1
    rw [ls, thetaLat_latStateGen, neg_zero, evR_singleton, map_smul, sigma_evalWord,
      Even.neg_one_pow (hP t List.mem_cons_self), one_smul]

theorem hasN_nP (P : RawPoly ℕ) (hP : ∀ t ∈ P, Even t.2.length) : HasN m hm (nP m hm P) P := by
  rw [HasN, nP, PP_coe, theta_ls_even m P hP, ← two_smul ℂ, smul_smul]
  norm_num

/-- `H^{2t}` in `V⁺` (`t = 1`: the conformal vector). -/
def HP : ℕ → VP m hm
  | 1 => (V2mPlus m hm).conformalVector
  | t => nP m hm (HR t)

theorem hasN_HP (t : ℕ) (ht : 1 ≤ t) (ht4 : t ≤ 4) : HasN m hm (HP m hm t) (HR t) := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 by omega) with rfl | rfl | rfl | rfl
  · exact hasN_omega m hm
  all_goals
    apply hasN_nP
    intro s hs
    simp only [HR, H4R, H6R, H8R, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> decide

/-- `L(-1)^k` on `V⁺`. -/
def LmV (k : ℕ) (y : VP m hm) : VP m hm := ((V2mPlus m hm).L (-1))^[k] y

theorem L_neg_one_eq_smul (y : VP m hm) :
    (V2mPlus m hm).L (-1) y = (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 0 y := by
  rw [VertexOperatorAlgebra.L_def]; rfl

theorem hasN_LmV {y : VP m hm} {P : RawPoly ℕ} (hy : HasN m hm y P) :
    ∀ k : ℕ, HasN m hm (LmV m hm k y) (LmPow k P)
  | 0 => hy
  | k + 1 => by
    rw [LmV, Function.iterate_succ_apply', ← LmV, L_neg_one_eq_smul]
    have h := hasN_smul_left m hm (hasN_omega m hm) (hasN_LmV hy k) 0
    rw [HasN, LmPow, LmR, ls_normR]
    simpa using h

/-- `Σ c · L(-1)^k H^{2t}` in `V⁺`. -/
def combV : List (ℚ × ℕ × ℕ) → VP m hm
  | [] => 0
  | (c, k, t) :: rest => ((c : ℚ) : ℂ) • LmV m hm k (HP m hm t) + combV rest

theorem hasN_combV : ∀ L : List (ℚ × ℕ × ℕ), (∀ e ∈ L, 1 ≤ e.2.2 ∧ e.2.2 ≤ 4) →
    HasN m hm (combV m hm L) (combR L)
  | [], _ => hasN_zero m hm
  | (c, k, t) :: rest, h => by
    have ht := h (c, k, t) List.mem_cons_self
    exact hasN_add m hm (hasN_smul m hm (hasN_LmV m hm (hasN_HP m hm t ht.1 ht.2) k) c)
      (hasN_combV rest fun e he => h e (List.mem_cons_of_mem _ he))

/-! ## §3  The product tables -/

/-- `H⁴₍ⱼ₎H⁴`, `j = 0,1,2,3`. -/
def T44 : ℕ → List (ℚ × ℕ × ℕ)
  | 0 => [(1 / 60, 5, 1), (3 / 4, 3, 2), (3, 1, 3)]
  | 1 => [(4 / 45, 4, 1), (19 / 6, 2, 2), (6, 0, 3)]
  | 2 => [(7 / 18, 3, 1), (10, 1, 2)]
  | 3 => [(4 / 3, 2, 1), (20, 0, 2)]
  | _ => []

/-- `H⁴₍ⱼ₎H⁶`, `j = 0,1,2,3`. -/
def T46 : ℕ → List (ℚ × ℕ × ℕ)
  | 0 => [(-1 / 1680, 7, 1), (1 / 80, 5, 2), (3 / 4, 3, 3), (3, 1, 4)]
  | 1 => [(-11 / 2520, 6, 1), (1 / 10, 4, 2), (13 / 3, 2, 3), (8, 0, 4)]
  | 2 => [(-1 / 36, 5, 1), (83 / 120, 3, 2), (119 / 6, 1, 3)]
  | 3 => [(-3 / 20, 4, 1), (81 / 20, 2, 2), (63, 0, 3)]
  | _ => []

/-- `H⁶₍ⱼ₎H⁴`, `j = 0,…,5`. -/
def T64 : ℕ → List (ℚ × ℕ × ℕ)
  | 0 => [(5 / 252, 7, 1), (2 / 3, 5, 2), (25 / 6, 3, 3), (5, 1, 4)]
  | 1 => [(38 / 315, 6, 1), (52 / 15, 4, 2), (16, 2, 3), (8, 0, 4)]
  | 2 => [(223 / 360, 5, 1), (117 / 8, 3, 2), (259 / 6, 1, 3)]
  | 3 => [(13 / 5, 4, 1), (189 / 4, 2, 2), (63, 0, 3)]
  | 4 => [(17 / 2, 3, 1), (526 / 5, 1, 2)]
  | 5 => [(20, 2, 1), (124, 0, 2)]
  | _ => []

theorem cert44_0 : normR (polyActW H4R (-0 - 1) H4R) = normR (combR (T44 0)) := by
  decide +kernel

theorem cert44_1 : normR (polyActW H4R (-1 - 1) H4R) = normR (combR (T44 1)) := by
  decide +kernel

theorem cert44_2 : normR (polyActW H4R (-2 - 1) H4R) = normR (combR (T44 2)) := by
  decide +kernel

theorem cert44_3 : normR (polyActW H4R (-3 - 1) H4R) = normR (combR (T44 3)) := by
  decide +kernel

theorem cert46_0 : normR (polyActW H4R (-0 - 1) H6R) = normR (combR (T46 0)) := by
  decide +kernel

theorem cert46_1 : normR (polyActW H4R (-1 - 1) H6R) = normR (combR (T46 1)) := by
  decide +kernel

theorem cert46_2 : normR (polyActW H4R (-2 - 1) H6R) = normR (combR (T46 2)) := by
  decide +kernel

theorem cert46_3 : normR (polyActW H4R (-3 - 1) H6R) = normR (combR (T46 3)) := by
  decide +kernel

theorem cert64_0 : normR (polyActW H6R (-0 - 1) H4R) = normR (combR (T64 0)) := by
  decide +kernel

theorem cert64_1 : normR (polyActW H6R (-1 - 1) H4R) = normR (combR (T64 1)) := by
  decide +kernel

theorem cert64_2 : normR (polyActW H6R (-2 - 1) H4R) = normR (combR (T64 2)) := by
  decide +kernel

theorem cert64_3 : normR (polyActW H6R (-3 - 1) H4R) = normR (combR (T64 3)) := by
  decide +kernel

theorem cert64_4 : normR (polyActW H6R (-4 - 1) H4R) = normR (combR (T64 4)) := by
  decide +kernel

theorem cert64_5 : normR (polyActW H6R (-5 - 1) H4R) = normR (combR (T64 5)) := by
  decide +kernel

theorem certL1H4 : normR (polyActW omR (-2 - 1) H4R) = normR (combR [(-1 / 3, 1, 1)]) := by
  decide +kernel

theorem certL1H6 :
    normR (polyActW omR (-2 - 1) H6R) = normR (combR [(-1 / 60, 3, 1), (-3 / 2, 1, 2)]) := by
  decide +kernel

theorem certW : normR WR = normR (combR [(10, 0, 2), (1 / 3, 2, 1)]) := by
  decide +kernel

/-! ## §4  The identities in `V⁺` -/

theorem smul_HP_eq (r s : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) (hs : 1 ≤ s ∧ s ≤ 4) (j : ℤ)
    (L : List (ℚ × ℕ × ℕ)) (hL : ∀ e ∈ L, 1 ≤ e.2.2 ∧ e.2.2 ≤ 4)
    (hcert : normR (polyActW (HR r) (-j - 1) (HR s)) = normR (combR L)) :
    (V2mPlus m hm).smul (HP m hm r) j (HP m hm s) = combV m hm L :=
  eq_of_hasN m hm (hasN_smul_left m hm (hasN_HP m hm r hr.1 hr.2) (hasN_HP m hm s hs.1 hs.2) j)
    (hasN_combV m hm L hL) hcert

theorem L1_H4 : (V2mPlus m hm).L 1 (HP m hm 2) = combV m hm [(-1 / 3, 1, 1)] := by
  rw [VertexOperatorAlgebra.L_def]
  exact smul_HP_eq m hm 1 2 (by norm_num) (by norm_num) 2 _ (by decide) certL1H4

theorem L1_H6 : (V2mPlus m hm).L 1 (HP m hm 3) = combV m hm [(-1 / 60, 3, 1), (-3 / 2, 1, 2)] := by
  rw [VertexOperatorAlgebra.L_def]
  exact smul_HP_eq m hm 1 3 (by norm_num) (by norm_num) 2 _ (by decide) certL1H6

theorem WP_eq_comb : WP m hm = combV m hm [(10, 0, 2), (1 / 3, 2, 1)] :=
  eq_of_hasN m hm (WP_coe m hm) (hasN_combV m hm _ (by decide)) certW

theorem H44_eq (j : ℕ) (hj : j < 4) :
    (V2mPlus m hm).smul (HP m hm 2) j (HP m hm 2) = combV m hm (T44 j) := by
  interval_cases j
  · exact smul_HP_eq m hm 2 2 (by norm_num) (by norm_num) 0 _ (by decide) cert44_0
  · exact smul_HP_eq m hm 2 2 (by norm_num) (by norm_num) 1 _ (by decide) cert44_1
  · exact smul_HP_eq m hm 2 2 (by norm_num) (by norm_num) 2 _ (by decide) cert44_2
  · exact smul_HP_eq m hm 2 2 (by norm_num) (by norm_num) 3 _ (by decide) cert44_3

theorem H46_eq (j : ℕ) (hj : j < 4) :
    (V2mPlus m hm).smul (HP m hm 2) j (HP m hm 3) = combV m hm (T46 j) := by
  interval_cases j
  · exact smul_HP_eq m hm 2 3 (by norm_num) (by norm_num) 0 _ (by decide) cert46_0
  · exact smul_HP_eq m hm 2 3 (by norm_num) (by norm_num) 1 _ (by decide) cert46_1
  · exact smul_HP_eq m hm 2 3 (by norm_num) (by norm_num) 2 _ (by decide) cert46_2
  · exact smul_HP_eq m hm 2 3 (by norm_num) (by norm_num) 3 _ (by decide) cert46_3

theorem H64_eq (j : ℕ) (hj : j < 6) :
    (V2mPlus m hm).smul (HP m hm 3) j (HP m hm 2) = combV m hm (T64 j) := by
  interval_cases j
  · exact smul_HP_eq m hm 3 2 (by norm_num) (by norm_num) 0 _ (by decide) cert64_0
  · exact smul_HP_eq m hm 3 2 (by norm_num) (by norm_num) 1 _ (by decide) cert64_1
  · exact smul_HP_eq m hm 3 2 (by norm_num) (by norm_num) 2 _ (by decide) cert64_2
  · exact smul_HP_eq m hm 3 2 (by norm_num) (by norm_num) 3 _ (by decide) cert64_3
  · exact smul_HP_eq m hm 3 2 (by norm_num) (by norm_num) 4 _ (by decide) cert64_4
  · exact smul_HP_eq m hm 3 2 (by norm_num) (by norm_num) 5 _ (by decide) cert64_5

end VOA.Classification.COne.PlusRat3
