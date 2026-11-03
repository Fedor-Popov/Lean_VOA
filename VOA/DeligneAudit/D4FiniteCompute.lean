/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FiniteCore

/-!
# Laurent polynomial worlds for the D₄ finite identity

* **The `(q, s, x, z)` world** `L7 = ℤ[q^±, s^±, x^±, z₁^±, …, z₄^±]`
  (`AddMonoidAlgebra ℤ (Fin 7 → ℤ)`), where the paper's identity (P) lives, with the isobaric
  Demazure operators `demazure α` acting on the `z`-exponents.
* **The `(q, u, t, z)` world** `LU = ℤ[q^±, z^±][u, t]`
  (`AddMonoidAlgebra ℤ ((Fin 5 → ℤ) × (Fin 2 → ℕ))`), with `u = s(x + x⁻¹)` and `t = s²`.  Every
  factor `f(a) = (1 - s x a)(1 - s x⁻¹ a) = 1 - u a + t a²`, so the heavy part of the computation
  (about four times smaller) happens here.
* **The transfer** `psi : LU →ₐ[ℤ] L7`, `u ↦ s x + s x⁻¹`, `t ↦ s²`, which commutes with the
  Demazure operators (`psi_demazureU`).
* Computable mirrors of both worlds (term lists, see `D4FiniteCore`) with evaluation lemmas.
-/

namespace VOA.DeligneAudit.D4Finite

open scoped BigOperators
open Gen

/-! ## The `(q, s, x, z)` world -/

/-- Exponent vectors `(q, s, x, z₁, z₂, z₃, z₄)`. -/
abbrev Mon := Fin 7 → ℤ

/-- `ℤ[q^±, s^±, x^±, z₁^±, …, z₄^±]`. -/
abbrev L7 := AddMonoidAlgebra ℤ Mon

/-- Read a list as an exponent vector (missing entries are `0`). -/
def toMon (l : List ℤ) : Mon := fun i => l.getD i 0

/-- The monomial with exponent list `l`. -/
noncomputable def mo (l : List ℤ) : L7 := AddMonoidAlgebra.single (toMon l) 1

/-- A root `α ∈ ℤ⁴` (in `z`-coordinates) as an exponent vector. -/
def rootZ (α : List ℤ) : Mon := toMon ([0, 0, 0] ++ α)

/-- `⟨μ, α⟩` on the `z`-part. -/
def pairZ (e : Mon) (α : List ℤ) : ℤ :=
  e 3 * α.getD 0 0 + e 4 * α.getD 1 0 + e 5 * α.getD 2 0 + e 6 * α.getD 3 0

/-- `e ↦ e + j α`. -/
def shZ (α : List ℤ) (j : ℤ) (e : Mon) : Mon := e + j • rootZ α

/-- The isobaric Demazure operator `π_α = (1 - z^{-α} s_α)/(1 - z^{-α})` on `L7`, monomialwise by
the `α`-string formula: `z^e ↦ Σ_{j=0}^{n} z^{e - jα}` (`n = ⟨e, α⟩ ≥ 0`),
`z^e ↦ -Σ_{j=1}^{-n-1} z^{e + jα}` (`n < 0`). -/
noncomputable def demazure (α : List ℤ) (f : L7) : L7 := demazureG (pairZ · α) (shZ α) f

/-! ### Computable mirror -/

/-- Term lists over `L7`. -/
abbrev TList := List (Tm (List ℤ))

/-- Packed key of an exponent list (for ordering only). -/
def keyOf (l : List ℤ) : ℕ :=
  (List.range 7).foldr (fun i acc => (l.getD i 0 + 64).toNat * 128 ^ i + acc) 0

def keyBias : ℕ := keyOf []

/-- Pointwise sum of exponent lists (total; the shorter list is padded by `0`). -/
def addE : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addE l m

/-- `c • l`. -/
def smulE (c : ℤ) (l : List ℤ) : List ℤ := l.map (c * ·)

/-- Pad an exponent list to length `7`. -/
def pad (l : List ℤ) : List ℤ := (List.range 7).map fun i => l.getD i 0

def mkTerm (l : List ℤ) (c : ℤ) : Tm (List ℤ) := ((keyOf l, pad l), c)

def oneP : TList := [mkTerm [] 1]

def monoP (l : List ℤ) (c : ℤ) : TList := [mkTerm l c]

/-- `1 - z^l`. -/
def linP (l : List ℤ) : TList := [mkTerm [] 1, mkTerm l (-1)]

def mulP (p q : TList) : TList := mulPG addE keyBias p q

/-- `∏ (1 - z^l)`. -/
def prodLin (ls : List (List ℤ)) : TList := ls.foldl (fun acc l => mulP acc (linP l)) oneP

def pairL (l : List ℤ) (α : List ℤ) : ℤ :=
  l.getD 3 0 * α.getD 0 0 + l.getD 4 0 * α.getD 1 0 + l.getD 5 0 * α.getD 2 0 +
    l.getD 6 0 * α.getD 3 0

def keyDelta (α : List ℤ) : ℤ :=
  α.getD 0 0 * 128 ^ 3 + α.getD 1 0 * 128 ^ 4 + α.getD 2 0 * 128 ^ 5 + α.getD 3 0 * 128 ^ 6

def demP (α : List ℤ) (p : TList) : TList :=
  demPG (pairL · α) (fun j l => addE l (smulE j ([0, 0, 0] ++ α))) (keyDelta α) p

/-! ### Correctness -/

noncomputable def eval (p : TList) : L7 := evalG toMon p

theorem toMon_addE (l m : List ℤ) : toMon (addE l m) = toMon l + toMon m := by
  induction l generalizing m with
  | nil => funext i; simp [addE, toMon]
  | cons a l ih =>
      cases m with
      | nil => funext i; simp [addE, toMon]
      | cons b m =>
          funext i
          rcases i with ⟨i, hi⟩
          cases i with
          | zero => simp [addE, toMon]
          | succ i =>
              have := congrFun (ih m) ⟨i, by omega⟩
              simpa [addE, toMon] using this

theorem toMon_smulE (c : ℤ) (l : List ℤ) : toMon (smulE c l) = c • toMon l := by
  funext i
  simp only [toMon, smulE, Pi.smul_apply, smul_eq_mul]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[(i : ℕ)]? <;> simp

theorem toMon_pad (l : List ℤ) : toMon (pad l) = toMon l := by
  funext i
  rcases i with ⟨i, hi⟩
  simp only [toMon, pad]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem eval_addP (p q : TList) : eval (addP p q) = eval p + eval q := evalG_addP toMon p q

theorem eval_subP (p q : TList) : eval (subP p q) = eval p - eval q := evalG_subP toMon p q

theorem eval_mulP (p q : TList) : eval (mulP p q) = eval p * eval q :=
  evalG_mulPG toMon addE toMon_addE keyBias p q

theorem eval_oneP : eval oneP = 1 := by
  simp only [eval, oneP, mkTerm, evalG_cons, evalG_nil, add_zero, toMon_pad]
  rfl

theorem eval_monoP (l : List ℤ) (c : ℤ) :
    eval (monoP l c) = AddMonoidAlgebra.single (toMon l) c := by
  simp only [eval, monoP, mkTerm, evalG_cons, evalG_nil, add_zero, toMon_pad]

theorem eval_monoP_one (l : List ℤ) : eval (monoP l 1) = mo l := eval_monoP l 1

theorem eval_linP (l : List ℤ) : eval (linP l) = 1 - mo l := by
  simp only [eval, linP, mkTerm, evalG_cons, evalG_nil, add_zero, toMon_pad, mo]
  rw [show AddMonoidAlgebra.single (toMon []) (1 : ℤ) = 1 from rfl, AddMonoidAlgebra.single_neg,
    sub_eq_add_neg]

theorem eval_prodLin (ls : List (List ℤ)) :
    eval (prodLin ls) = (ls.map fun l => 1 - mo l).prod := by
  rw [prodLin]
  suffices h : ∀ acc : TList, eval (ls.foldl (fun acc l => mulP acc (linP l)) acc) =
      eval acc * (ls.map fun l => 1 - mo l).prod by
    rw [h, eval_oneP, one_mul]
  induction ls with
  | nil => intro acc; simp
  | cons l ls ih =>
      intro acc
      rw [List.foldl_cons, ih, eval_mulP, eval_linP, List.map_cons, List.prod_cons, mul_assoc]

theorem eval_demP (α : List ℤ) (p : TList) : eval (demP α p) = demazure α (eval p) :=
  evalG_demPG toMon _ _ _ (pairZ · α) (shZ α) (fun _ => rfl)
    (fun j l => by rw [toMon_addE, toMon_smulE]; rfl) p

/-! ## The `(q, u, t, z)` world -/

/-- Exponents `((q, z₁, z₂, z₃, z₄), (u, t))`. -/
abbrev MonU := (Fin 5 → ℤ) × (Fin 2 → ℕ)

/-- `ℤ[q^±, z^±][u, t]`. -/
abbrev LU := AddMonoidAlgebra ℤ MonU

def toMonU (e : List ℤ × List ℕ) : MonU := (fun i => e.1.getD i 0, fun i => e.2.getD i 0)

noncomputable def moU (a : List ℤ) (n : List ℕ) : LU := AddMonoidAlgebra.single (toMonU (a, n)) 1

def rootU (α : List ℤ) : MonU := toMonU ([0] ++ α, [])

def pairZU (e : MonU) (α : List ℤ) : ℤ :=
  e.1 1 * α.getD 0 0 + e.1 2 * α.getD 1 0 + e.1 3 * α.getD 2 0 + e.1 4 * α.getD 3 0

def shU (α : List ℤ) (j : ℤ) (e : MonU) : MonU := (e.1 + j • (rootU α).1, e.2)

/-- The Demazure operator on `LU`. -/
noncomputable def demazureU (α : List ℤ) (f : LU) : LU := demazureG (pairZU · α) (shU α) f

/-- Term lists over `LU`. -/
abbrev UList := List (Tm (List ℤ × List ℕ))

def addN : List ℕ → List ℕ → List ℕ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addN l m

def addEU (e f : List ℤ × List ℕ) : List ℤ × List ℕ := (addE e.1 f.1, addN e.2 f.2)

def keyOfU (e : List ℤ × List ℕ) : ℕ :=
  (List.range 5).foldr (fun i acc => (e.1.getD i 0 + 64).toNat * 128 ^ i + acc) 0 +
    e.2.getD 0 0 * 128 ^ 5 + e.2.getD 1 0 * 128 ^ 6

def keyBiasU : ℕ := keyOfU ([], [])

def padU (e : List ℤ × List ℕ) : List ℤ × List ℕ :=
  ((List.range 5).map fun i => e.1.getD i 0, (List.range 2).map fun i => e.2.getD i 0)

def mkTermU (a : List ℤ) (n : List ℕ) (c : ℤ) : Tm (List ℤ × List ℕ) :=
  ((keyOfU (a, n), padU (a, n)), c)

def monoU (a : List ℤ) (n : List ℕ) (c : ℤ) : UList := [mkTermU a n c]

def oneU : UList := monoU [] [] 1

def mulU (p q : UList) : UList := mulPG addEU keyBiasU p q

def pairLU (e : List ℤ × List ℕ) (α : List ℤ) : ℤ :=
  e.1.getD 1 0 * α.getD 0 0 + e.1.getD 2 0 * α.getD 1 0 + e.1.getD 3 0 * α.getD 2 0 +
    e.1.getD 4 0 * α.getD 3 0

def keyDeltaU (α : List ℤ) : ℤ :=
  α.getD 0 0 * 128 ^ 1 + α.getD 1 0 * 128 ^ 2 + α.getD 2 0 * 128 ^ 3 + α.getD 3 0 * 128 ^ 4

def demU (α : List ℤ) (p : UList) : UList :=
  demPG (pairLU · α) (fun j e => (addE e.1 (smulE j ([0] ++ α)), e.2)) (keyDeltaU α) p

noncomputable def evalU (p : UList) : LU := evalG toMonU p

theorem getD_addN (l m : List ℕ) (i : ℕ) : (addN l m).getD i 0 = l.getD i 0 + m.getD i 0 := by
  induction l generalizing m i with
  | nil => simp [addN]
  | cons a l ih =>
      cases m with
      | nil => simp [addN]
      | cons b m =>
          cases i with
          | zero => simp [addN]
          | succ i => simpa [addN] using ih m i

theorem toMonU_addEU (e f : List ℤ × List ℕ) : toMonU (addEU e f) = toMonU e + toMonU f := by
  have h1 := toMon_addE e.1 f.1
  ext i
  · have := congrFun h1 ⟨i, by omega⟩
    simpa [toMonU, addEU, toMon] using this
  · change (addN e.2 f.2).getD i 0 = e.2.getD i 0 + f.2.getD i 0
    exact getD_addN _ _ _

theorem toMonU_padU (e : List ℤ × List ℕ) : toMonU (padU e) = toMonU e := by
  ext i
  · rcases i with ⟨i, hi⟩
    simp only [toMonU, padU]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  · rcases i with ⟨i, hi⟩
    simp only [toMonU, padU]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl

theorem evalU_addP (p q : UList) : evalU (addP p q) = evalU p + evalU q := evalG_addP toMonU p q

theorem evalU_subP (p q : UList) : evalU (subP p q) = evalU p - evalU q := evalG_subP toMonU p q

theorem evalU_mulU (p q : UList) : evalU (mulU p q) = evalU p * evalU q :=
  evalG_mulPG toMonU addEU toMonU_addEU keyBiasU p q

theorem evalU_monoU (a : List ℤ) (n : List ℕ) (c : ℤ) :
    evalU (monoU a n c) = AddMonoidAlgebra.single (toMonU (a, n)) c := by
  simp only [evalU, monoU, mkTermU, evalG_cons, evalG_nil, add_zero, toMonU_padU]

theorem evalU_oneU : evalU oneU = 1 := by
  rw [oneU, evalU_monoU]; rfl

theorem evalU_demU (α : List ℤ) (p : UList) : evalU (demU α p) = demazureU α (evalU p) :=
  evalG_demPG toMonU _ _ _ (pairZU · α) (shU α) (fun _ => rfl)
    (fun j e => by
      have := toMon_addE e.1 (smulE j ([0] ++ α))
      rw [toMon_smulE] at this
      ext i
      · have h := congrFun this ⟨i, by omega⟩
        simpa [toMonU, shU, rootU, toMon] using h
      · rfl) p

/-! ## The transfer `u ↦ s x + s x⁻¹`, `t ↦ s²` -/

/-- `(q, z) ↦ (q, 0, 0, z)`. -/
def embedZQ (a : Fin 5 → ℤ) : Mon := ![a 0, 0, 0, a 1, a 2, a 3, a 4]

/-- `u = s x + s x⁻¹`. -/
noncomputable def uS : L7 := mo [0, 1, 1] + mo [0, 1, -1]

/-- `t = s²`. -/
noncomputable def tS : L7 := mo [0, 2]

/-- The monoid hom behind `psi`. -/
noncomputable def psiHom : Multiplicative MonU →* L7 where
  toFun e := AddMonoidAlgebra.single (embedZQ e.toAdd.1) 1 * uS ^ (e.toAdd.2 0) * tS ^ (e.toAdd.2 1)
  map_one' := by
    simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, pow_zero, mul_one]
    rw [show embedZQ 0 = 0 by funext i; fin_cases i <;> rfl]
    rfl
  map_mul' e f := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Pi.add_apply, pow_add]
    rw [show embedZQ (e.toAdd.1 + f.toAdd.1) = embedZQ e.toAdd.1 + embedZQ f.toAdd.1 by
      funext i; fin_cases i <;> simp [embedZQ]]
    rw [← one_mul (1 : ℤ), ← AddMonoidAlgebra.single_mul_single]
    ring

/-- The transfer homomorphism `ℤ[q^±, z^±][u, t] → ℤ[q^±, s^±, x^±, z^±]`. -/
noncomputable def psi : LU →ₐ[ℤ] L7 := AddMonoidAlgebra.lift ℤ L7 MonU psiHom

theorem psi_single (e : MonU) (c : ℤ) :
    psi (AddMonoidAlgebra.single e c) =
      AddMonoidAlgebra.single (embedZQ e.1) c * uS ^ (e.2 0) * tS ^ (e.2 1) := by
  rw [psi, AddMonoidAlgebra.lift_single]
  change c • (AddMonoidAlgebra.single (embedZQ e.1) 1 * uS ^ (e.2 0) * tS ^ (e.2 1)) = _
  rw [mul_assoc, mul_assoc, ← smul_mul_assoc]
  congr 1
  simp only [zsmul_eq_mul, AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.single_mul_single,
    zero_add, mul_one, Int.cast_id]

/-- `z`-free elements: every monomial has zero `z`-exponents. -/
def ZFree (f : L7) : Prop := ∀ m ∈ f.support, m 3 = 0 ∧ m 4 = 0 ∧ m 5 = 0 ∧ m 6 = 0

theorem zfree_add {f g : L7} (hf : ZFree f) (hg : ZFree g) : ZFree (f + g) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
  · exact hf m h
  · exact hg m h

theorem zfree_mul {f g : L7} (hf : ZFree f) (hg : ZFree g) : ZFree (f * g) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_mul f g hm)
  obtain ⟨a3, a4, a5, a6⟩ := hf a ha
  obtain ⟨b3, b4, b5, b6⟩ := hg b hb
  simp [a3, a4, a5, a6, b3, b4, b5, b6]

theorem zfree_single (m : Mon) (c : ℤ) (h : m 3 = 0 ∧ m 4 = 0 ∧ m 5 = 0 ∧ m 6 = 0) :
    ZFree (AddMonoidAlgebra.single m c) := by
  classical
  intro m' hm'
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hm')]
  exact h

theorem zfree_one : ZFree (1 : L7) := zfree_single 0 1 (by simp)

theorem zfree_pow {f : L7} (hf : ZFree f) (n : ℕ) : ZFree (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact zfree_one
  | succ n ih => rw [pow_succ]; exact zfree_mul ih hf

theorem zfree_uS : ZFree uS :=
  zfree_add (zfree_single _ _ (by simp [toMon])) (zfree_single _ _ (by simp [toMon]))

theorem zfree_tS : ZFree tS := zfree_single _ _ (by simp [toMon])

theorem demazure_mul_zfree (α : List ℤ) (f h : L7) (hh : ZFree h) :
    demazure α (f * h) = demazure α f * h := by
  apply demazureG_mul_neutral
  intro m hm e
  obtain ⟨h3, h4, h5, h6⟩ := hh m hm
  refine ⟨?_, fun j => ?_⟩
  · simp [pairZ, h3, h4, h5, h6]
  · simp only [shZ]; abel

theorem embedZQ_shU (α : List ℤ) (j : ℤ) (e : MonU) :
    embedZQ (shU α j e).1 = shZ α j (embedZQ e.1) := by
  funext i
  fin_cases i <;> simp [embedZQ, shU, shZ, rootU, rootZ, toMonU, toMon]

theorem pairZ_embedZQ (α : List ℤ) (e : MonU) : pairZ (embedZQ e.1) α = pairZU e α := by
  simp [pairZ, pairZU, embedZQ]

/-- **`psi` commutes with the Demazure operators.** -/
theorem psi_demazureU (α : List ℤ) (f : LU) : psi (demazureU α f) = demazure α (psi f) := by
  rw [demazureU, demazureG_eq_sum, map_sum]
  conv_rhs => rw [← f.sum_single, Finsupp.sum, map_sum, demazure, demazureG_finset_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [psi_single, mul_assoc, ← demazure,
    demazure_mul_zfree α _ _ (zfree_mul (zfree_pow zfree_uS _) (zfree_pow zfree_tS _)),
    demazure, demazureG_single]
  unfold demMonoG
  simp only [pairZ_embedZQ]
  split_ifs
  · rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [psi_single, ← embedZQ_shU, mul_assoc]
    rfl
  · rw [map_neg, map_sum, neg_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [psi_single, ← embedZQ_shU, mul_assoc]
    rfl

end VOA.DeligneAudit.D4Finite
