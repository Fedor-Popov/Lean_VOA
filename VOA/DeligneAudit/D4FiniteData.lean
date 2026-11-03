/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FiniteCompute

/-!
# Data of the D₄ finite identity (F)/(P), in both worlds

Paper d4, eqs. (deligne:d4-finite-polynomials), (deligne:d4-polynomial-certificate).  With
`t = s²`, vector weights `𝒜 = {z₁^±, …, z₄^±}` and `f(a) = (1 - s x a)(1 - s x⁻¹ a)`:

* `d4P0 = ∏_{a ∈ 𝒜} f(a)`, `d4Ptheta = f(z₁⁻¹) f(q z₁⁻¹) f(z₂⁻¹) f(q z₂⁻¹) f(z₃^±) f(z₄^±)`;
* `d4Q = (1 - qt) f(z₁⁻¹) f(z₂⁻¹) f(z₃^±) f(z₄^±) [(1 + z₁z₂/q)(1 + qt) - s(x + x⁻¹)(z₁ + z₂)]`,
  the exact quotient `(P₀ - q⁻² z₁² z₂² P_θ)/(1 - q⁻¹ z₁ z₂)` (`d4Q_spec` in `D4FiniteIdentity`);
* `d4F = π_{s_θ} d4Q`, `π_{s_θ} = π₂ π₁ π₃ π₂ π₄ π₂ π₃ π₁ π₂` in order of application;
* `d4LHS = (1 - x²) t q F`,
  `d4RHS = (1-x²)(1-t)(1-qt) D₊(x) D₊(x⁻¹) - (1-qt)[P(x) D₊(x⁻¹) - x² P(x⁻¹) D₊(x)]`.

The `u, t` counterparts (`fU`, `d4QU`, …) satisfy `psi (·U) = ·` (`psi_fU`, `psi_d4QU`, …).
-/

namespace VOA.DeligneAudit.D4Finite

open scoped BigOperators
open Gen

/-! ## Combinatorial data -/

/-- Simple roots in `z`-coordinates: `α₁ = e₁-e₂`, `α₂ = e₂-e₃`, `α₃ = e₃-e₄`, `α₄ = e₃+e₄`. -/
def d4Roots : List (List ℤ) := [[1, -1, 0, 0], [0, 1, -1, 0], [0, 0, 1, -1], [0, 0, 1, 1]]

/-- Reduced word of `s_θ` (paper `2,1,3,2,4,2,3,1,2`), 0-based, in order of application. -/
def d4Word : List ℕ := [1, 0, 2, 1, 3, 1, 2, 0, 1]

/-- `z`-unit vector `z_j^σ`. -/
def zv (j : ℕ) (σ : ℤ) : List ℤ := (List.range 4).map fun i => if i = j then σ else 0

/-- The eight vector weights, as `(q, z)`-exponent lists. -/
def wtsQZ : List (List ℤ) :=
  (List.range 4).flatMap fun j => [1, -1].map fun σ => [0] ++ zv j σ

/-- The weights of `P_θ`: `z₁⁻¹, q z₁⁻¹, z₂⁻¹, q z₂⁻¹, z₃^±, z₄^±`. -/
def wtsThetaQZ : List (List ℤ) :=
  [[0] ++ zv 0 (-1), [1] ++ zv 0 (-1), [0] ++ zv 1 (-1), [1] ++ zv 1 (-1),
    [0] ++ zv 2 1, [0] ++ zv 2 (-1), [0] ++ zv 3 1, [0] ++ zv 3 (-1)]

/-- The weights in `Q`: `z₁⁻¹, z₂⁻¹, z₃^±, z₄^±`. -/
def wtsQQZ : List (List ℤ) :=
  [[0] ++ zv 0 (-1), [0] ++ zv 1 (-1), [0] ++ zv 2 1, [0] ++ zv 2 (-1), [0] ++ zv 3 1,
    [0] ++ zv 3 (-1)]

/-- `(q, z) ↦ (q, s, x, z)` with `s = x = 0`. -/
def embL (a : List ℤ) : List ℤ :=
  [a.getD 0 0, 0, 0, a.getD 1 0, a.getD 2 0, a.getD 3 0, a.getD 4 0]

noncomputable section Algebraic

/-! ## The `(q, s, x, z)` world -/

/-- `f(a) = (1 - s x a)(1 - s x⁻¹ a)`. -/
def fA (a : List ℤ) : L7 := (1 - mo (addE [0, 1, 1] (embL a))) * (1 - mo (addE [0, 1, -1] (embL a)))

/-- `P₀ = ∏_{a ∈ 𝒜} f(a)`. -/
def d4P0 : L7 := (wtsQZ.map fA).prod

/-- `P_θ`. -/
def d4Ptheta : L7 := (wtsThetaQZ.map fA).prod

/-- `(1 + z₁z₂/q)(1 + qt) - s(x + x⁻¹)(z₁ + z₂)`. -/
def d4L : L7 :=
  (1 + mo [-1, 0, 0, 1, 1]) * (1 + mo [1, 2]) -
    (mo [0, 1, 1] + mo [0, 1, -1]) * (mo [0, 0, 0, 1] + mo [0, 0, 0, 0, 1])

/-- `Q = (P₀ - q⁻² z₁² z₂² P_θ)/(1 - q⁻¹ z₁ z₂)`, in product form. -/
def d4Q : L7 := (1 - mo [1, 2]) * (wtsQQZ.map fA).prod * d4L

/-- `π_{s_θ}`: the Demazure operators of `d4Word`, applied left to right. -/
def piSTheta (f : L7) : L7 := d4Word.foldl (fun acc i => demazure (d4Roots.getD i []) acc) f

/-- `F = π_{s_θ} Q`. -/
def d4F : L7 := piSTheta d4Q

/-- `D₊(x) = (1 - t x²)(1 - q t x²)`. -/
def d4Dplus : L7 := (1 - mo [0, 2, 2]) * (1 - mo [1, 2, 2])

/-- `D₊(x⁻¹)`. -/
def d4Dminus : L7 := (1 - mo [0, 2, -2]) * (1 - mo [1, 2, -2])

/-- `P(x) = ∏_{a ∈ 𝒜} (1 - s x a)`. -/
def d4Pplus : L7 := (wtsQZ.map fun a => 1 - mo (addE [0, 1, 1] (embL a))).prod

/-- `P(x⁻¹)`. -/
def d4Pminus : L7 := (wtsQZ.map fun a => 1 - mo (addE [0, 1, -1] (embL a))).prod

/-- Left side of (P): `(1 - x²) t q F`. -/
def d4LHS : L7 := (1 - mo [0, 0, 2]) * mo [1, 2] * d4F

/-- Right side of (P). -/
def d4RHS : L7 :=
  (1 - mo [0, 2]) * (1 - mo [1, 2]) * (1 - mo [0, 0, 2]) * d4Dplus * d4Dminus -
    (1 - mo [1, 2]) * (d4Pplus * d4Dminus - mo [0, 0, 2] * d4Pminus * d4Dplus)

/-! ## The `(q, u, t, z)` world -/

/-- `f(a) = 1 - u a + t a²`. -/
def fU (a : List ℤ) : LU := 1 - moU a [1] + moU (smulE 2 a) [0, 1]

def d4LU : LU :=
  (1 + moU [-1, 1, 1] []) * (1 + moU [1] [0, 1]) - moU [] [1] * (moU [0, 1] [] + moU [0, 0, 1] [])

def d4QU : LU := (1 - moU [1] [0, 1]) * (wtsQQZ.map fU).prod * d4LU

def d4P0U : LU := (wtsQZ.map fU).prod

def d4PthetaU : LU := (wtsThetaQZ.map fU).prod

def piSThetaU (f : LU) : LU := d4Word.foldl (fun acc i => demazureU (d4Roots.getD i []) acc) f

/-! ## Transfer lemmas -/

theorem mo_mul (l m : List ℤ) : mo l * mo m = mo (addE l m) := by
  rw [mo, mo, mo, AddMonoidAlgebra.single_mul_single, toMon_addE, one_mul]

theorem mo_congr {l m : List ℤ} (h : toMon l = toMon m) : mo l = mo m := by rw [mo, mo, h]

theorem getD_smulE (c : ℤ) (l : List ℤ) (i : ℕ) : (smulE c l).getD i 0 = c * l.getD i 0 := by
  have := congrFun (toMon_smulE c l)
  by_cases hi : i < 7
  · simpa [toMon] using this ⟨i, hi⟩
  · simp only [smulE, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[i]? <;> simp

theorem psi_moU (a : List ℤ) (n : List ℕ) :
    psi (moU a n) = mo (embL a) * uS ^ (n.getD 0 0) * tS ^ (n.getD 1 0) := by
  rw [moU, psi_single]
  congr 3
  funext i
  fin_cases i <;> rfl

theorem toMon_addE_comm (l m : List ℤ) : toMon (addE l m) = toMon (addE m l) := by
  rw [toMon_addE, toMon_addE, add_comm]

theorem psi_fU (a : List ℤ) : psi (fU a) = fA a := by
  rw [fU, map_add, map_sub, map_one, psi_moU, psi_moU, fA]
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, pow_one, pow_zero, mul_one]
  rw [uS, tS, mul_add, mo_mul, mo_mul, mo_mul]
  have h1 : mo (addE (embL a) [0, 1, 1]) = mo (addE [0, 1, 1] (embL a)) :=
    mo_congr (toMon_addE_comm _ _)
  have h2 : mo (addE (embL a) [0, 1, -1]) = mo (addE [0, 1, -1] (embL a)) :=
    mo_congr (toMon_addE_comm _ _)
  have h3 : mo (addE (embL (smulE 2 a)) [0, 2]) =
      mo (addE [0, 1, 1] (embL a)) * mo (addE [0, 1, -1] (embL a)) := by
    rw [mo_mul]
    apply mo_congr
    rw [toMon_addE, toMon_addE, toMon_addE, toMon_addE]
    funext i
    fin_cases i <;> simp [toMon, embL, getD_smulE, List.getD_cons_zero, List.getD_cons_succ,
      List.getD_nil, -List.getD_eq_getElem?_getD] <;> ring
  rw [h1, h2, h3]
  ring

theorem psi_prod_fU (ws : List (List ℤ)) : psi (ws.map fU).prod = (ws.map fA).prod := by
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun a _ => psi_fU a)

theorem psi_d4LU : psi d4LU = d4L := by
  rw [d4LU, d4L]
  simp only [map_sub, map_add, map_mul, map_one, psi_moU, List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil, pow_zero, pow_one, mul_one, uS, tS, mo_mul]
  have e1 : mo (embL [-1, 1, 1]) = mo [-1, 0, 0, 1, 1] :=
    mo_congr (by funext i; fin_cases i <;> rfl)
  have e2 : mo (addE (embL [1]) [0, 2]) = mo [1, 2] := mo_congr (by funext i; fin_cases i <;> rfl)
  have e3 : mo (embL []) = 1 := by
    rw [mo, AddMonoidAlgebra.one_def]; congr 1; funext i; fin_cases i <;> rfl
  have e4 : mo (embL [0, 1]) = mo [0, 0, 0, 1] := mo_congr (by funext i; fin_cases i <;> rfl)
  have e5 : mo (embL [0, 0, 1]) = mo [0, 0, 0, 0, 1] := mo_congr (by funext i; fin_cases i <;> rfl)
  rw [e1, e2, e3, e4, e5, one_mul]

theorem psi_d4QU : psi d4QU = d4Q := by
  rw [d4QU, d4Q, map_mul, map_mul, psi_prod_fU, psi_d4LU, map_sub, map_one, psi_moU]
  simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, pow_one, mul_one, tS, mo_mul]
  congr 3
  exact mo_congr (by funext i; fin_cases i <;> rfl)

theorem psi_d4P0U : psi d4P0U = d4P0 := psi_prod_fU _

theorem psi_d4PthetaU : psi d4PthetaU = d4Ptheta := psi_prod_fU _

theorem psi_piSThetaU (f : LU) : psi (piSThetaU f) = piSTheta (psi f) := by
  unfold piSThetaU piSTheta
  generalize d4Word = w
  induction w generalizing f with
  | nil => rfl
  | cons i w ih => rw [List.foldl_cons, List.foldl_cons, ih, psi_demazureU]

end Algebraic

/-! ## Computable mirrors -/

/-- `1 - u a + t a²`. -/
def fUc (a : List ℤ) : UList := addP (subP oneU (monoU a [1] 1)) (monoU (smulE 2 a) [0, 1] 1)

def prodU (ps : List UList) : UList := ps.foldl mulU oneU

def d4LUc : UList :=
  subP (mulU (addP oneU (monoU [-1, 1, 1] [] 1)) (addP oneU (monoU [1] [0, 1] 1)))
    (mulU (monoU [] [1] 1) (addP (monoU [0, 1] [] 1) (monoU [0, 0, 1] [] 1)))

def d4QUc : UList :=
  mulU (mulU (subP oneU (monoU [1] [0, 1] 1)) (prodU (wtsQQZ.map fUc))) d4LUc

def d4P0Uc : UList := prodU (wtsQZ.map fUc)

def d4PthetaUc : UList := prodU (wtsThetaQZ.map fUc)

/-- Powers of a term list. -/
def powP (p : TList) : ℕ → TList
  | 0 => oneP
  | n + 1 => mulP (powP p n) p

def uSc : TList := addP (monoP [0, 1, 1] 1) (monoP [0, 1, -1] 1)

def tSc : TList := monoP [0, 2] 1

/-- The transfer of one `(q, u, t, z)` term. -/
def psiTerm (t : Tm (List ℤ × List ℕ)) : TList :=
  mulP (mulP (monoP (embL t.1.2.1) t.2) (powP uSc (t.1.2.2.getD 0 0))) (powP tSc (t.1.2.2.getD 1 0))

/-- The transfer of a term list. -/
def psiL (p : UList) : TList := normalize (p.map psiTerm).flatten

def d4Dplusc : TList := mulP (linP [0, 2, 2]) (linP [1, 2, 2])

def d4Dminusc : TList := mulP (linP [0, 2, -2]) (linP [1, 2, -2])

def d4Pplusc : TList := prodLin (wtsQZ.map fun a => addE [0, 1, 1] (embL a))

def d4Pminusc : TList := prodLin (wtsQZ.map fun a => addE [0, 1, -1] (embL a))

def d4RHSc : TList :=
  subP (mulP (mulP (mulP (mulP (linP [0, 2]) (linP [1, 2])) (linP [0, 0, 2])) d4Dplusc) d4Dminusc)
    (mulP (linP [1, 2])
      (subP (mulP d4Pplusc d4Dminusc) (mulP (mulP (monoP [0, 0, 2] 1) d4Pminusc) d4Dplusc)))

/-- The left side from a `(q, u, t, z)` list representing `π_{s_θ} Q`. -/
def d4LHSc (fu : UList) : TList := mulP (mulP (linP [0, 0, 2]) (monoP [1, 2] 1)) (psiL fu)

def piSThetaUc (p : UList) : UList := d4Word.foldl (fun acc i => demU (d4Roots.getD i []) acc) p

/-! ## Evaluation of the mirrors -/

noncomputable section EvalLemmas

theorem moU_eq (a : List ℤ) (n : List ℕ) : evalU (monoU a n 1) = moU a n := evalU_monoU a n 1

theorem evalU_fUc (a : List ℤ) : evalU (fUc a) = fU a := by
  rw [fUc, evalU_addP, evalU_subP, evalU_oneU, moU_eq, moU_eq, fU]

theorem evalU_prodU (ps : List UList) : evalU (prodU ps) = (ps.map evalU).prod := by
  rw [prodU]
  suffices h : ∀ acc : UList, evalU (ps.foldl mulU acc) = evalU acc * (ps.map evalU).prod by
    rw [h, evalU_oneU, one_mul]
  induction ps with
  | nil => intro acc; simp
  | cons p ps ih =>
      intro acc
      rw [List.foldl_cons, ih, evalU_mulU, List.map_cons, List.prod_cons, mul_assoc]

theorem evalU_prod_fUc (ws : List (List ℤ)) :
    evalU (prodU (ws.map fUc)) = (ws.map fU).prod := by
  rw [evalU_prodU]
  induction ws with
  | nil => rfl
  | cons a ws ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, ih, evalU_fUc]

theorem evalU_d4LUc : evalU d4LUc = d4LU := by
  simp only [d4LUc, evalU_subP, evalU_mulU, evalU_addP, evalU_oneU, moU_eq, d4LU]

theorem evalU_d4QUc : evalU d4QUc = d4QU := by
  rw [d4QUc, evalU_mulU, evalU_mulU, evalU_subP, evalU_oneU, moU_eq, evalU_prod_fUc,
    evalU_d4LUc, d4QU]

theorem evalU_d4P0Uc : evalU d4P0Uc = d4P0U := evalU_prod_fUc _

theorem evalU_d4PthetaUc : evalU d4PthetaUc = d4PthetaU := evalU_prod_fUc _

theorem evalU_piSThetaUc (p : UList) : evalU (piSThetaUc p) = piSThetaU (evalU p) := by
  unfold piSThetaUc piSThetaU
  generalize d4Word = w
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => rw [List.foldl_cons, List.foldl_cons, ih, evalU_demU]

theorem eval_powP (p : TList) (n : ℕ) : eval (powP p n) = eval p ^ n := by
  induction n with
  | zero => rw [powP, eval_oneP, pow_zero]
  | succ n ih => rw [powP, eval_mulP, ih, pow_succ]

theorem eval_uSc : eval uSc = uS := by rw [uSc, eval_addP, eval_monoP_one, eval_monoP_one, uS]

theorem eval_tSc : eval tSc = tS := by rw [tSc, eval_monoP_one, tS]

theorem eval_psiTerm (t : Tm (List ℤ × List ℕ)) :
    eval (psiTerm t) = psi (AddMonoidAlgebra.single (toMonU t.1.2) t.2) := by
  rw [psiTerm, eval_mulP, eval_mulP, eval_powP, eval_powP, eval_uSc, eval_tSc, eval_monoP,
    psi_single, show toMon (embL t.1.2.1) = embedZQ (toMonU t.1.2).1 by
      funext i; fin_cases i <;> rfl]
  rfl

theorem eval_psiL (p : UList) : eval (psiL p) = psi (evalU p) := by
  rw [psiL, eval, evalG_normalize, evalG_flatten, List.map_map]
  induction p with
  | nil => simp [evalU]
  | cons t p ih =>
      rw [List.map_cons, List.sum_cons, Function.comp_apply, ← eval, eval_psiTerm, ih,
        show evalU (t :: p) = AddMonoidAlgebra.single (toMonU t.1.2) t.2 + evalU p from
          evalG_cons _ _ _, map_add]

theorem eval_d4RHSc : eval d4RHSc = d4RHS := by
  have hP : eval d4Pplusc = d4Pplus := by rw [d4Pplusc, eval_prodLin, List.map_map]; rfl
  have hM : eval d4Pminusc = d4Pminus := by rw [d4Pminusc, eval_prodLin, List.map_map]; rfl
  simp only [d4RHSc, eval_subP, eval_mulP, eval_linP, eval_monoP_one, d4RHS, d4Dplusc, d4Dminusc,
    d4Dplus, d4Dminus, hP, hM]

theorem eval_d4LHSc (fu : UList) (h : evalU fu = piSThetaU d4QU) : eval (d4LHSc fu) = d4LHS := by
  rw [d4LHSc, eval_mulP, eval_mulP, eval_linP, eval_monoP_one, eval_psiL, h, psi_piSThetaU,
    psi_d4QU, d4LHS, d4F]

end EvalLemmas

end VOA.DeligneAudit.D4Finite
