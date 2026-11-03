/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Vandermonde algebra for the `n = 2` jet-ideal Poincaré lemma

Pure commutative algebra in `ℂ[x_0, …, x_{k-1}]`.

* `L = (x_0^N, …, x_{k-1}^N)`;
* `W = Σ_l x_l^N · Q_l`, where `Q_l` is the ideal of polynomials divisible by every `x_b - x_a`
  with `a < b`, `a, b ≠ l`.

`mem_W_of_mem_L` — **a polynomial in `L` divisible by every `x_b - x_a` lies in `W`.**

Proof: `f = Δ g` (`Δ` the Vandermonde product); `g` is divided (lexicographic division algorithm)
by the generators `G_i = det(points x_i, …, x_{k-1}; powers 0, …, k-2-i, m_i) / Δ(x_i, …)`, whose
leading monomial is `x_i^{N-(k-1-i)}` and with `Δ G_i ∈ W` (Laplace expansion along the last
column); the remainder `r` is a combination of monomials `x^c` with `c_i < N - (k-1-i)`, and
`Δ r ∈ L` forces `r = 0` because the leading monomial of `Δ r` has all exponents `< N`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.JetPoincareVdm

open MvPolynomial Finset
open scoped MonomialOrder

noncomputable section

variable {k : ℕ}

/-- `ℂ[x_0, …, x_{k-1}]`. -/
abbrev XP (k : ℕ) : Type := MvPolynomial (Fin k) ℂ

/-! ### Divisibility by `x_b - x_a` -/

/-- The variable substitution `x_b ↦ x_a`. -/
def subst (a b : Fin k) (i : Fin k) : Fin k := if i = b then a else i

theorem dvd_sub_rename (a b : Fin k) (p : XP k) :
    (X b - X a : XP k) ∣ p - rename (subst a b) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]; exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul, rename_X]
    have h : p * X i - rename (subst a b) p * X (subst a b i) =
        (p - rename (subst a b) p) * X i + rename (subst a b) p * (X i - X (subst a b i)) := by
      ring
    rw [h]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    unfold subst
    split_ifs with hib
    · subst hib; exact dvd_rfl
    · simp

theorem rename_subst_eq_zero_of_dvd {a b : Fin k} {p : XP k} (h : (X b - X a : XP k) ∣ p) :
    rename (subst a b) p = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [map_mul, map_sub, rename_X, rename_X]
  simp [subst]

theorem dvd_of_rename_subst_eq_zero {a b : Fin k} {p : XP k} (h : rename (subst a b) p = 0) :
    (X b - X a : XP k) ∣ p := by
  have := dvd_sub_rename a b p
  rwa [h, sub_zero] at this

/-- The product of the pair factors over a set of increasing pairs. -/
def pprod (P : Finset (Fin k × Fin k)) : XP k := ∏ q ∈ P, (X q.2 - X q.1)

theorem X_sub_X_ne_zero {a b : Fin k} (h : a ≠ b) : (X b - X a : XP k) ≠ 0 := by
  rw [sub_ne_zero]
  intro he
  exact h (X_injective he).symm

/-- **Peeling**: a polynomial divisible by each factor `x_b - x_a` (`a < b`) of a product is
divisible by the product. -/
theorem pprod_dvd {P : Finset (Fin k × Fin k)} (hP : ∀ q ∈ P, q.1 < q.2) {f : XP k}
    (hf : ∀ q ∈ P, (X q.2 - X q.1 : XP k) ∣ f) : pprod P ∣ f := by
  classical
  induction P using Finset.induction_on generalizing f with
  | empty => simp [pprod]
  | insert q P hq ih =>
    have hP' : ∀ p ∈ P, p.1 < p.2 := fun p hp => hP p (mem_insert_of_mem hp)
    obtain ⟨g, rfl⟩ := ih hP' fun p hp => hf p (mem_insert_of_mem hp)
    have hqd := hf q (mem_insert_self q P)
    have h0 := rename_subst_eq_zero_of_dvd hqd
    rw [map_mul] at h0
    have hne : rename (subst q.1 q.2) (pprod P) ≠ 0 := by
      rw [pprod, map_prod, prod_ne_zero_iff]
      intro p hp
      rw [map_sub, rename_X, rename_X]
      have hp12 := hP' p hp
      have hq12 := hP q (mem_insert_self q P)
      have hpq : p ≠ q := fun h => hq (h ▸ hp)
      apply X_sub_X_ne_zero
      intro he
      unfold subst at he
      rw [Ne, Prod.ext_iff] at hpq
      rw [Fin.lt_def] at hp12 hq12
      split_ifs at he with h1 h2 h2 <;>
        simp only [Fin.ext_iff] at h1 h2 he hpq <;> omega
    have hg : rename (subst q.1 q.2) g = 0 :=
      (mul_eq_zero.mp h0).resolve_left hne
    obtain ⟨g', rfl⟩ := dvd_of_rename_subst_eq_zero hg
    rw [pprod, prod_insert hq, ← pprod]
    exact ⟨g', by ring⟩

/-! ### Vandermonde products -/

/-- `Δ(v) = ∏_{p < q} (x_{v q} - x_{v p})`. -/
def vdm {n : ℕ} (v : Fin n → Fin k) : XP k := ∏ p : Fin n, ∏ q ∈ Ioi p, (X (v q) - X (v p))

theorem vdm_eq_det {n : ℕ} (v : Fin n → Fin k) :
    vdm v = (Matrix.vandermonde fun p => (X (v p) : XP k)).det :=
  (Matrix.det_vandermonde _).symm

/-- The increasing pairs `(v p, v q)`, `p < q`. -/
def vpairs {n : ℕ} (v : Fin n → Fin k) : Finset (Fin k × Fin k) :=
  (univ.sigma fun p : Fin n => Ioi p).image fun x => (v x.1, v x.2)

theorem mem_vpairs {n : ℕ} {v : Fin n → Fin k} {q : Fin k × Fin k} :
    q ∈ vpairs v ↔ ∃ p p' : Fin n, p < p' ∧ v p = q.1 ∧ v p' = q.2 := by
  simp only [vpairs, mem_image, mem_sigma, mem_univ, mem_Ioi, true_and]
  constructor
  · rintro ⟨⟨p, p'⟩, h, rfl⟩; exact ⟨p, p', h, rfl, rfl⟩
  · rintro ⟨p, p', h, h1, h2⟩; exact ⟨⟨p, p'⟩, h, Prod.ext h1 h2⟩

theorem vpairs_lt {n : ℕ} {v : Fin n → Fin k} (hv : StrictMono v) :
    ∀ q ∈ vpairs v, q.1 < q.2 := by
  intro q hq
  obtain ⟨p, p', h, h1, h2⟩ := mem_vpairs.mp hq
  rw [← h1, ← h2]; exact hv h

theorem vdm_eq_pprod {n : ℕ} {v : Fin n → Fin k} (hv : StrictMono v) :
    vdm v = pprod (vpairs v) := by
  rw [vdm, prod_sigma', pprod, vpairs, prod_image]
  intro x _ y _ hxy
  simp only [Prod.mk.injEq] at hxy
  exact Sigma.ext (hv.injective hxy.1) (heq_of_eq (hv.injective hxy.2))

theorem vdm_ne_zero {n : ℕ} {v : Fin n → Fin k} (hv : StrictMono v) : vdm v ≠ 0 := by
  rw [vdm]
  refine prod_ne_zero_iff.mpr fun p _ => prod_ne_zero_iff.mpr fun q hq => ?_
  exact X_sub_X_ne_zero (hv.injective.ne (ne_of_lt (mem_Ioi.mp hq)))

/-! ### Lexicographic degrees -/

/-- The lexicographic monomial order on `ℂ[x_0, …, x_{k-1}]` (`x_0` largest). -/
abbrev lexO (k : ℕ) : MonomialOrder (Fin k) := MonomialOrder.lex

theorem degree_X_sub_X {a b : Fin k} (h : a < b) :
    (lexO k).degree (X b - X a : XP k) = Finsupp.single a 1 := by
  have h1 : (X b - X a : XP k) = -(X a - X b) := by ring
  rw [h1, MonomialOrder.degree_neg, MonomialOrder.degree_sub_of_lt, MonomialOrder.degree_X]
  rw [MonomialOrder.degree_X, MonomialOrder.degree_X, MonomialOrder.lex_lt_iff]
  exact Finsupp.Lex.single_lt_iff.mpr h

/-- `δ(v) = Σ_{p < q} e_{v p}`, the lexicographic degree of `Δ(v)`. -/
def dvec {n : ℕ} (v : Fin n → Fin k) : Fin k →₀ ℕ :=
  ∑ p : Fin n, ∑ _q ∈ Ioi p, Finsupp.single (v p) 1

theorem degree_vdm {n : ℕ} {v : Fin n → Fin k} (hv : StrictMono v) :
    (lexO k).degree (vdm v) = dvec v := by
  rw [vdm, MonomialOrder.degree_prod]
  · refine sum_congr rfl fun p _ => ?_
    rw [MonomialOrder.degree_prod]
    · exact sum_congr rfl fun q hq => degree_X_sub_X (hv (mem_Ioi.mp hq))
    · intro q hq
      exact X_sub_X_ne_zero (hv.injective.ne (ne_of_lt (mem_Ioi.mp hq)))
  · intro p _
    refine prod_ne_zero_iff.mpr fun q hq => ?_
    exact X_sub_X_ne_zero (hv.injective.ne (ne_of_lt (mem_Ioi.mp hq)))

theorem dvec_apply {n : ℕ} (v : Fin n → Fin k) (j : Fin k) :
    dvec v j = ∑ p : Fin n, if v p = j then #(Ioi p) else 0 := by
  rw [dvec, Finsupp.finsetSum_apply]
  refine sum_congr rfl fun p _ => ?_
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, sum_ite_irrel, sum_const, smul_eq_mul, mul_one, mul_zero]

theorem dvec_apply_of_forall_ne {n : ℕ} {v : Fin n → Fin k} {j : Fin k}
    (h : ∀ p, v p ≠ j) : dvec v j = 0 := by
  rw [dvec_apply]
  exact sum_eq_zero fun p _ => if_neg (h p)

theorem dvec_apply_of_eq {n : ℕ} {v : Fin n → Fin k} (hv : Function.Injective v) {p0 : Fin n}
    {j : Fin k} (h : v p0 = j) : dvec v j = #(Ioi p0) := by
  rw [dvec_apply]
  have : ∀ p, (v p = j) ↔ (p = p0) := fun p => ⟨fun hp => hv (hp.trans h.symm), fun hp => hp ▸ h⟩
  simp only [this, sum_ite_eq', mem_univ, if_true]

theorem dvec_id_apply (j : Fin k) : dvec (id : Fin k → Fin k) j = k - 1 - j := by
  rw [dvec_apply_of_eq (v := id) (p0 := j) (j := j) Function.injective_id rfl, Fin.card_Ioi]

theorem dvec_le {n : ℕ} {v : Fin n → Fin k} (hv : Function.Injective v) (j : Fin k) :
    dvec v j ≤ n - 1 := by
  by_cases h : ∃ p0, v p0 = j
  · obtain ⟨p0, hp0⟩ := h
    rw [dvec_apply_of_eq hv hp0, Fin.card_Ioi]; omega
  · push Not at h
    rw [dvec_apply_of_forall_ne h]; exact Nat.zero_le _

/-! ### The ideals `L`, `Q_l`, `W` -/

/-- `L = (x_0^N, …, x_{k-1}^N)`. -/
def Lid (k N : ℕ) : Ideal (XP k) := Ideal.span (Set.range fun i : Fin k => (X i ^ N : XP k))

/-- `Q_l`: divisible by every `x_b - x_a`, `a < b`, `a, b ≠ l`. -/
def Qid (k : ℕ) (l : Fin k) : Ideal (XP k) :=
  ⨅ (a : Fin k) (b : Fin k) (_ : a < b ∧ a ≠ l ∧ b ≠ l), Ideal.span {(X b - X a : XP k)}

/-- `W = Σ_l x_l^N Q_l`. -/
def Wid (k N : ℕ) : Ideal (XP k) := ⨆ l : Fin k, Ideal.span {(X l ^ N : XP k)} * Qid k l

theorem mem_Qid {l : Fin k} {Y : XP k} :
    Y ∈ Qid k l ↔ ∀ a b : Fin k, a < b → a ≠ l → b ≠ l → (X b - X a : XP k) ∣ Y := by
  simp only [Qid, Ideal.mem_iInf, Ideal.mem_span_singleton]
  constructor
  · intro h a b h1 h2 h3; exact h a b ⟨h1, h2, h3⟩
  · intro h a b hh; exact h a b hh.1 hh.2.1 hh.2.2

theorem pow_mul_mem_Wid {N m : ℕ} (hm : N ≤ m) {l : Fin k} {Y : XP k} (hY : Y ∈ Qid k l) :
    X l ^ m * Y ∈ Wid k N := by
  have h : (X l ^ m * Y : XP k) = X l ^ N * (X l ^ (m - N) * Y) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [h]
  exact Ideal.mem_iSup_of_mem l
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_left _ _ hY))

theorem Wid_le_Lid (N : ℕ) : Wid k N ≤ Lid k N :=
  iSup_le fun l => le_trans Ideal.mul_le_right
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.subset_span ⟨l, rfl⟩)))

theorem exists_ge_of_mem_Lid {N : ℕ} {f : XP k} (hf : f ∈ Lid k N) :
    ∀ e ∈ f.support, ∃ i, N ≤ e i := by
  have hL : Lid k N = Ideal.span ((fun s => monomial s (1 : ℂ)) ''
      Set.range fun i : Fin k => Finsupp.single i N) := by
    rw [Lid, ← Set.range_comp]
    congr 1
    ext x
    simp [X_pow_eq_monomial]
  rw [hL, mem_ideal_span_monomial_image] at hf
  intro e he
  obtain ⟨si, ⟨i, rfl⟩, hle⟩ := hf e he
  exact ⟨i, by simpa using hle i⟩

/-! ### The determinant generators -/

variable {r : ℕ}

/-- Rows: the points `x_{pt p}`; columns: the powers `0, 1, …, r - 1, m`. -/
def dmat (pt : Fin (r + 1) → Fin k) (m : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) (XP k) :=
  Matrix.of fun p q => X (pt p) ^ (if q = Fin.last r then m else (q : ℕ))

/-- The alternant `det(x_{pt p}^{0}, …, x_{pt p}^{r-1}, x_{pt p}^m)`. -/
def dD (pt : Fin (r + 1) → Fin k) (m : ℕ) : XP k := (dmat pt m).det

/-- The Laplace term of the alternant. -/
def dT (pt : Fin (r + 1) → Fin k) (m : ℕ) (p : Fin (r + 1)) : XP k :=
  (-1) ^ ((p : ℕ) + r) * X (pt p) ^ m * vdm (fun p' => pt (p.succAbove p'))

/-- **Laplace expansion** along the column of the power `m`. -/
theorem dD_laplace (pt : Fin (r + 1) → Fin k) (m : ℕ) :
    dD pt m = ∑ p : Fin (r + 1), dT pt m p := by
  rw [dD, Matrix.det_succ_column _ (Fin.last r)]
  refine sum_congr rfl fun p _ => ?_
  have hsub : (dmat pt m).submatrix p.succAbove (Fin.last r).succAbove =
      Matrix.vandermonde fun p' => (X (pt (p.succAbove p')) : XP k) := by
    ext p' q'
    simp [dmat, Matrix.vandermonde_apply, Fin.succAbove_last, Fin.castSucc_ne_last]
  rw [dT, Fin.val_last, vdm_eq_det, hsub]
  simp [dmat]

theorem dD_self (pt : Fin (r + 1) → Fin k) : dD pt r = vdm pt := by
  rw [dD, vdm_eq_det]
  congr 1
  ext p q
  simp only [dmat, Matrix.of_apply, Matrix.vandermonde_apply]
  split_ifs with h
  · subst h; simp
  · rfl

theorem dvd_dD {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) (m : ℕ) {pa pb : Fin (r + 1)}
    (hab : pa < pb) : (X (pt pb) - X (pt pa) : XP k) ∣ dD pt m := by
  apply dvd_of_rename_subst_eq_zero
  rw [dD, AlgHom.map_det]
  have hne : pt pa ≠ pt pb := hpt.injective.ne (ne_of_lt hab)
  refine Matrix.det_zero_of_row_eq (ne_of_lt hab) (funext fun q => ?_)
  have h1 : subst (pt pa) (pt pb) (pt pa) = pt pa := by simp [subst, hne]
  have h2 : subst (pt pa) (pt pb) (pt pb) = pt pa := by simp [subst]
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, dmat, Matrix.of_apply, map_pow, rename_X,
    h1, h2]

theorem vdm_dvd_dD {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) (m : ℕ) :
    vdm pt ∣ dD pt m := by
  rw [vdm_eq_pprod hpt]
  refine pprod_dvd (vpairs_lt hpt) fun q hq => ?_
  obtain ⟨p, p', h, h1, h2⟩ := mem_vpairs.mp hq
  rw [← h1, ← h2]
  exact dvd_dD hpt m h

/-- The pair factors not inside the point set. -/
def Rfac (pt : Fin (r + 1) → Fin k) : XP k :=
  pprod (vpairs (id : Fin k → Fin k) \ vpairs pt)

theorem vpairs_subset {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) :
    vpairs pt ⊆ vpairs (id : Fin k → Fin k) := by
  intro q hq
  obtain ⟨p, p', h, h1, h2⟩ := mem_vpairs.mp hq
  exact mem_vpairs.mpr ⟨q.1, q.2, h1 ▸ h2 ▸ hpt h, rfl, rfl⟩

theorem vdm_id_eq {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) :
    vdm (id : Fin k → Fin k) = Rfac pt * vdm pt := by
  rw [vdm_eq_pprod strictMono_id, vdm_eq_pprod hpt, Rfac, pprod, pprod, pprod,
    prod_sdiff (vpairs_subset hpt)]

theorem Rfac_mul_vdm_mem_Qid (pt : Fin (r + 1) → Fin k) (p : Fin (r + 1)) :
    Rfac pt * vdm (fun p' => pt (p.succAbove p')) ∈ Qid k (pt p) := by
  rw [mem_Qid]
  intro a b hab ha hb
  by_cases hq : (a, b) ∈ vpairs pt
  · obtain ⟨x, y, hxy, hx, hy⟩ := mem_vpairs.mp hq
    simp only at hx hy
    have hxp : x ≠ p := fun h => ha (by rw [← hx, h])
    have hyp : y ≠ p := fun h => hb (by rw [← hy, h])
    obtain ⟨x', rfl⟩ := Fin.exists_succAbove_eq hxp
    obtain ⟨y', rfl⟩ := Fin.exists_succAbove_eq hyp
    have hlt : x' < y' := (Fin.strictMono_succAbove p).lt_iff_lt.mp hxy
    refine dvd_mul_of_dvd_right ?_ _
    rw [← hx, ← hy, vdm]
    exact dvd_trans (dvd_prod_of_mem
      (fun q => (X (pt (p.succAbove q)) - X (pt (p.succAbove x')) : XP k)) (mem_Ioi.mpr hlt))
      (dvd_prod_of_mem (fun p'' => ∏ q ∈ Ioi p'',
        (X (pt (p.succAbove q)) - X (pt (p.succAbove p'')) : XP k)) (mem_univ x'))
  · refine dvd_mul_of_dvd_left ?_ _
    have hmem : (a, b) ∈ vpairs (id : Fin k → Fin k) \ vpairs pt :=
      mem_sdiff.mpr ⟨mem_vpairs.mpr ⟨a, b, hab, rfl, rfl⟩, hq⟩
    have h := dvd_prod_of_mem (fun q : Fin k × Fin k => (X q.2 - X q.1 : XP k)) hmem
    rw [Rfac, pprod]
    exact h

/-- **`Δ · G ∈ W`** for the quotient `G = D / Δ(pt)`. -/
theorem vdm_mul_mem_Wid {N m : ℕ} (hm : N ≤ m) {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt)
    {G : XP k} (hG : dD pt m = vdm pt * G) : vdm (id : Fin k → Fin k) * G ∈ Wid k N := by
  rw [vdm_id_eq hpt, mul_assoc, ← hG, dD_laplace, mul_sum]
  refine Ideal.sum_mem _ fun p _ => ?_
  have h : Rfac pt * dT pt m p =
      X (pt p) ^ m * ((-1) ^ ((p : ℕ) + r) * (Rfac pt * vdm (fun p' => pt (p.succAbove p')))) := by
    rw [dT]; ring
  rw [h]
  exact pow_mul_mem_Wid hm (Ideal.mul_mem_left _ _ (Rfac_mul_vdm_mem_Qid pt p))

/-! ### The leading monomial of the generator -/

theorem degree_neg_one_pow_mul (n : ℕ) (Y : XP k) :
    (lexO k).degree ((-1) ^ n * Y) = (lexO k).degree Y := by
  rcases neg_one_pow_eq_or (XP k) n with h | h <;> rw [h]
  · rw [one_mul]
  · rw [neg_one_mul, MonomialOrder.degree_neg]

theorem dT_ne_zero {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) (m : ℕ) (p : Fin (r + 1)) :
    dT pt m p ≠ 0 := by
  rw [dT]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ (X_ne_zero _)))
    (vdm_ne_zero (hpt.comp (Fin.strictMono_succAbove p)))

theorem degree_dT {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) (m : ℕ) (p : Fin (r + 1)) :
    (lexO k).degree (dT pt m p) =
      Finsupp.single (pt p) m + dvec (fun p' => pt (p.succAbove p')) := by
  have hv : StrictMono fun p' => pt (p.succAbove p') := hpt.comp (Fin.strictMono_succAbove p)
  rw [dT, mul_assoc, degree_neg_one_pow_mul, MonomialOrder.degree_mul (pow_ne_zero _ (X_ne_zero _))
    (vdm_ne_zero hv), MonomialOrder.degree_pow, MonomialOrder.degree_X, degree_vdm hv,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The Laplace term of the first point dominates. -/
theorem dT_succ_lt {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) {m : ℕ} (hrm : r ≤ m)
    (p : Fin r) : (lexO k).degree (dT pt m p.succ) ≺[lexO k] (lexO k).degree (dT pt m 0) := by
  rw [MonomialOrder.lex_lt_iff, degree_dT hpt, degree_dT hpt, Finsupp.Lex.lt_iff]
  have hge : ∀ q, pt 0 ≤ pt q := fun q => hpt.monotone (Fin.zero_le q)
  refine ⟨pt 0, fun j hj => ?_, ?_⟩
  · simp only [ofLex_toLex, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    have hj' : ∀ q, pt q ≠ j := fun q => (lt_of_lt_of_le hj (hge q)).ne'
    rw [if_neg (hj' _), if_neg (hj' _), dvec_apply_of_forall_ne (fun q => hj' _),
      dvec_apply_of_forall_ne (fun q => hj' _)]
  · simp only [ofLex_toLex, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    have hne : pt p.succ ≠ pt 0 := hpt.injective.ne (Fin.succ_ne_zero p)
    rw [if_neg hne, if_true,
      dvec_apply_of_forall_ne (v := fun p' => pt ((0 : Fin (r + 1)).succAbove p'))
        (fun q h => (Fin.succAbove_ne 0 q) (hpt.injective h))]
    have := dvec_le ((hpt.comp (Fin.strictMono_succAbove p.succ)).injective) (pt 0)
    have hr : 0 < r := Fin.pos p
    simp only [Function.comp_def] at this
    omega

/-- The lexicographic degree of the alternant. -/
theorem degree_dD {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) {m : ℕ} (hrm : r ≤ m) :
    (lexO k).degree (dD pt m) = (lexO k).degree (dT pt m 0) ∧ dD pt m ≠ 0 := by
  rw [dD_laplace, Fin.sum_univ_succ]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Fin.sum_univ_zero, add_zero]
    exact ⟨rfl, dT_ne_zero hpt m 0⟩
  have hlt : (lexO k).degree (∑ p : Fin r, dT pt m p.succ) ≺[lexO k]
      (lexO k).degree (dT pt m 0) := by
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    have hpos : ⊥ < (lexO k).toSyn ((lexO k).degree (dT pt m 0)) := by
      rw [MonomialOrder.bot_eq_zero, MonomialOrder.toSyn_lt_iff_ne_zero, ne_eq,
        MonomialOrder.toSyn_eq_zero_iff]
      intro h0
      have := congrArg (fun d : Fin k →₀ ℕ => d (pt 0)) h0
      simp only [degree_dT hpt, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    exact (Finset.sup_lt_iff hpos).mpr fun p _ => dT_succ_lt hpt hrm p
  refine ⟨MonomialOrder.degree_add_of_lt hlt, fun h0 => ?_⟩
  have hlc := MonomialOrder.leadingCoeff_add_of_lt hlt
  rw [h0, MonomialOrder.leadingCoeff_zero] at hlc
  exact (MonomialOrder.leadingCoeff_ne_zero_iff.mpr (dT_ne_zero hpt m 0)) hlc.symm

/-- **The generator**: `D(pt, m) = Δ(pt) · G` with `Δ_k G ∈ W` and leading monomial
`x_{pt 0}^{m - r}`. -/
theorem exists_gen {N m : ℕ} (hm : N ≤ m) {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt)
    (hrm : r ≤ m) : ∃ G : XP k, vdm (id : Fin k → Fin k) * G ∈ Wid k N ∧ G ≠ 0 ∧
      (lexO k).degree G = Finsupp.single (pt 0) (m - r) := by
  obtain ⟨G, hG⟩ := vdm_dvd_dD hpt m
  obtain ⟨hdeg, hne⟩ := degree_dD hpt hrm
  have hG0 : G ≠ 0 := by rintro rfl; rw [mul_zero] at hG; exact hne hG
  refine ⟨G, vdm_mul_mem_Wid hm hpt hG, hG0, ?_⟩
  have h1 := hdeg
  rw [hG, MonomialOrder.degree_mul (vdm_ne_zero hpt) hG0, degree_dT hpt] at h1
  have h2 := (degree_dD hpt (le_refl r)).1
  rw [dD_self, degree_dT hpt] at h2
  rw [h2, show Finsupp.single (pt 0) m = Finsupp.single (pt 0) r + Finsupp.single (pt 0) (m - r) by
    rw [← Finsupp.single_add, Nat.add_sub_cancel' hrm]] at h1
  have h3 := add_left_cancel (by simpa only [add_assoc] using h1)
  rw [add_comm (Finsupp.single (pt 0) (m - r))] at h3
  exact add_left_cancel h3

/-! ### Division and triangularity -/

/-- The points `x_i, x_{i+1}, …, x_{k-1}`. -/
def ptI (i : Fin k) (p : Fin (k - 1 - i + 1)) : Fin k := ⟨i + p, by omega⟩

theorem ptI_strictMono (i : Fin k) : StrictMono (ptI i) := by
  intro p q h
  simp only [ptI, Fin.mk_lt_mk]
  exact Nat.add_lt_add_left h _

theorem ptI_zero (i : Fin k) : ptI i 0 = i := by
  ext; simp [ptI]

/-- The generators `G_i`, with leading monomial `x_i^{N - (k-1-i)}` and `Δ G_i ∈ W`. -/
theorem exists_gens (N : ℕ) : ∃ G : Fin k → XP k, ∀ i,
    vdm (id : Fin k → Fin k) * G i ∈ Wid k N ∧ G i ≠ 0 ∧
      (lexO k).degree (G i) = Finsupp.single i (N - (k - 1 - i)) := by
  have h : ∀ i : Fin k, ∃ G : XP k, vdm (id : Fin k → Fin k) * G ∈ Wid k N ∧ G ≠ 0 ∧
      (lexO k).degree G = Finsupp.single i (N - (k - 1 - i)) := by
    intro i
    obtain ⟨G, h1, h2, h3⟩ := exists_gen (le_max_left N (k - 1 - i)) (ptI_strictMono i)
      (le_max_right N (k - 1 - i))
    refine ⟨G, h1, h2, ?_⟩
    rw [h3, ptI_zero]
    congr 1
    omega
  choose G hG using h
  exact ⟨G, hG⟩

/-- **Triangularity**: a combination `r` of staircase monomials with `Δ r ∈ L` vanishes. -/
theorem eq_zero_of_vdm_mul_mem {N : ℕ} {r : XP k}
    (hr : ∀ c ∈ r.support, ∀ i : Fin k, c i < N - (k - 1 - i))
    (h : vdm (id : Fin k → Fin k) * r ∈ Lid k N) : r = 0 := by
  by_contra hr0
  have hne : vdm (id : Fin k → Fin k) * r ≠ 0 := mul_ne_zero (vdm_ne_zero strictMono_id) hr0
  obtain ⟨i, hi⟩ := exists_ge_of_mem_Lid h _ ((lexO k).degree_mem_support hne)
  rw [MonomialOrder.degree_mul (vdm_ne_zero strictMono_id) hr0, degree_vdm strictMono_id,
    Finsupp.coe_add, Pi.add_apply, dvec_id_apply] at hi
  have := hr _ ((lexO k).degree_mem_support hr0) i
  omega

/-- **The arrangement inclusion for `n = 2`**: a polynomial in `L` divisible by every
`x_b - x_a` lies in `W`. -/
theorem mem_Wid_of_mem_Lid {N : ℕ} {f : XP k} (hL : f ∈ Lid k N)
    (hd : ∀ a b : Fin k, a < b → (X b - X a : XP k) ∣ f) : f ∈ Wid k N := by
  -- `f = Δ g`
  obtain ⟨g, rfl⟩ : vdm (id : Fin k → Fin k) ∣ f := by
    rw [vdm_eq_pprod strictMono_id]
    exact pprod_dvd (vpairs_lt strictMono_id) fun q hq => hd q.1 q.2 (vpairs_lt strictMono_id q hq)
  obtain ⟨G, hG⟩ := exists_gens (k := k) N
  have hunit : ∀ i, IsUnit ((lexO k).leadingCoeff (G i)) := fun i =>
    IsUnit.mk0 _ (MonomialOrder.leadingCoeff_ne_zero_iff.mpr (hG i).2.1)
  obtain ⟨q, rem, hdec, -, hrem⟩ := (lexO k).div hunit g
  have hlin : vdm (id : Fin k → Fin k) * Finsupp.linearCombination (XP k) G q ∈ Wid k N := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, mul_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hG i).1
  have hrem0 : rem = 0 := by
    refine eq_zero_of_vdm_mul_mem (N := N) (fun c hc i => ?_) ?_
    · have := hrem c hc i
      rw [(hG i).2.2, Finsupp.single_le_iff] at this
      omega
    · have h1 : vdm (id : Fin k → Fin k) * rem = vdm id * g -
          vdm (id : Fin k → Fin k) * Finsupp.linearCombination (XP k) G q := by
        rw [hdec]; ring
      rw [h1]
      exact sub_mem hL (Wid_le_Lid N hlin)
  rw [hdec, hrem0, add_zero]
  exact hlin

end

end VOA.TwoSeries.JetPoincareVdm
