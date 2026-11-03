import VOA.Classification.COne.OrbOddVir
import VOA.Classification.COne.OrbZhuTower
import VOA.Modules.ZhuVermaAnArchFiltrationFinal

/-!
# OrbOdd (2): the Zhu calculus of Virasoro words

Generic, any VOA `W`, `Ω = omegaL W` (left multiplication by `[ω]`).

* `mk_L_neg`: `[L(-n) y] = (-1)ⁿ ((n-1) Ω + k) [y]` for `y ∈ W_k`, every `n ≥ 1`
  (`n = 1, 2` are `mk_L_neg_one_of_mem_grading`, `mk_L_neg_two`; `n ≥ 3` from
  `ω ∘ₘ y = (L(-m-3) + 2 L(-m-2) + L(-m-1)) y ∈ O(W)`, `Hres_mem_O`).
* Computable `ℚ`-coefficient lists `PL` for polynomials (`zp : PL → ℂ[X]`), with `zhuW`/`zhuV`
  the Zhu polynomial of a word/vector of `OrbOddVir`, and `mk_evV`:
  `[evV v] = zp (zhuV h v) (Ω) [x]` for `x ∈ W_h` and positive letters.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbOdd

open VOA VertexOperatorAlgebra Polynomial OrbZhu

/-! ## Computable polynomials -/

/-- Coefficient lists, constant term first. -/
abbrev PL := List ℚ

def paddL : PL → PL → PL
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: paddL a b

def pscaleL (c : ℚ) (a : PL) : PL := a.map (c * ·)

def pmulL : PL → PL → PL
  | [], _ => []
  | x :: a, b => paddL (pscaleL x b) (0 :: pmulL a b)

/-- Strip trailing zeros (for comparisons). -/
def ptrim (a : PL) : PL := (a.reverse.dropWhile (· = 0)).reverse

/-- The polynomial of a coefficient list. -/
def zp : PL → ℂ[X]
  | [] => 0
  | x :: a => Polynomial.C ((x : ℚ) : ℂ) + X * zp a

theorem zp_paddL : ∀ a b : PL, zp (paddL a b) = zp a + zp b
  | [], b => by simp [paddL, zp]
  | x :: a, [] => by simp [paddL, zp]
  | x :: a, y :: b => by
    simp only [paddL, zp, zp_paddL a b]; push_cast; rw [Polynomial.C_add]; ring

theorem zp_pscaleL (c : ℚ) : ∀ a : PL, zp (pscaleL c a) = Polynomial.C ((c : ℂ)) * zp a
  | [] => by simp [pscaleL, zp]
  | x :: a => by
    have := zp_pscaleL c a
    simp only [pscaleL, List.map_cons, zp] at this ⊢
    rw [this]; push_cast; rw [Polynomial.C_mul]; ring

theorem zp_pmulL : ∀ a b : PL, zp (pmulL a b) = zp a * zp b
  | [], b => by simp [pmulL, zp]
  | x :: a, b => by
    simp only [pmulL, zp_paddL, zp_pscaleL, zp, zp_pmulL a b, Rat.cast_zero, map_zero]
    ring

theorem zp_ptrim_aux : ∀ l : List ℚ, zp ((l.dropWhile (· = 0)).reverse) = zp l.reverse := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = 0
    · subst hx
      rw [List.dropWhile_cons_of_pos (by simp), ih, List.reverse_cons]
      -- zp (r ++ [0]) = zp r
      generalize l.reverse = r
      induction r with
      | nil => simp [zp]
      | cons y r ihr => simp only [List.cons_append, zp, ihr]
    · rw [List.dropWhile_cons_of_neg (by simpa using hx)]

theorem zp_ptrim (a : PL) : zp (ptrim a) = zp a := by
  unfold ptrim
  have := zp_ptrim_aux a.reverse
  rwa [List.reverse_reverse] at this

/-! ## The Zhu polynomial of a word -/

/-- `(-1)ⁿ ((n-1) X + k)`. -/
def zfac (n : ℕ) (k : ℚ) : PL := pscaleL ((-1) ^ n) [k, ((n : ℚ) - 1)]

/-- Zhu polynomial of the word `w` over a vector of weight `h`. -/
def zhuW (h : ℚ) : List ℕ → PL
  | [] => [1]
  | n :: w => pmulL (zfac n (h + (w.sum : ℚ))) (zhuW h w)

/-- Zhu polynomial of a vector. -/
def zhuV (h : ℚ) : VVec → PL
  | [] => []
  | p :: v => paddL (pscaleL p.1 (zhuW h p.2)) (zhuV h v)

/-- All letters positive. -/
def posW (w : List ℕ) : Bool := w.all (1 ≤ ·)
def posV (v : VVec) : Bool := v.all fun p => posW p.2

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

theorem aeval_omegaL_smul (P : ℂ[X]) (c : ℂ) (y : A W) :
    aeval (omegaL W) P (c • y) = c • aeval (omegaL W) P y := map_smul _ _ _

/-- `ω ∘ₘ y ∈ O(W)`: `(L(-m-3) + 2L(-m-2) + L(-m-1)) y ∈ O(W)`. -/
theorem L_three_term_mem_O (m : ℕ) (y : 𝒱) :
    W.L (-(m : ℤ) - 3) y + (2 : ℂ) • W.L (-(m : ℤ) - 2) y + W.L (-(m : ℤ) - 1) y ∈ O W := by
  have h := Hres_mem_O W (M := 2) (a := W.conformalVector) W.conformal_mem y m 0
  unfold Hres Gres at h
  simp only [add_zero, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have c1 : cbz ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 2 := by
    rw [cbz_apply_nonneg _ (by norm_num), show (((1 : ℕ) : ℤ)).toNat = 1 from rfl, gBinom]
    norm_num [Finset.prod_range_one]
  have c2 : cbz ((2 : ℕ) : ℤ) ((2 : ℕ) : ℤ) = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num), show (((2 : ℕ) : ℤ)).toNat = 2 from rfl, gBinom]
    norm_num [Finset.prod_range_succ, Finset.prod_range_one]
  have c0 : cbz ((2 : ℕ) : ℤ) ((0 : ℕ) : ℤ) = 1 := by simp
  rw [c0, c1, c2, one_smul, one_smul] at h
  have e : ∀ j : ℤ, W.smul W.conformalVector j y = W.L (j - 1) y := fun j => by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def, sub_add_cancel]
  rw [e, e, e] at h
  have h0 : ((0 : ℕ) : ℤ) - ((2 + 0 + m : ℕ) : ℤ) - 1 = -(m : ℤ) - 3 := by push_cast; ring
  have h1 : ((1 : ℕ) : ℤ) - ((2 + 0 + m : ℕ) : ℤ) - 1 = -(m : ℤ) - 2 := by push_cast; ring
  have h2 : ((2 : ℕ) : ℤ) - ((2 + 0 + m : ℕ) : ℤ) - 1 = -(m : ℤ) - 1 := by push_cast; ring
  rw [h0, h1, h2] at h
  exact h

/-- `[L(-n) y] = (-1)ⁿ ((n-1) Ω + k) [y]` for `y ∈ W_k`, `n ≥ 1`. -/
theorem mk_L_neg {k : ℤ} {y : 𝒱} (hy : y ∈ W.grading k) :
    ∀ n : ℕ, 1 ≤ n → mk W (W.L (-(n : ℤ)) y) =
      ((-1 : ℂ) ^ n) • (((n : ℂ) - 1) • omegaL W (mk W y) + (k : ℂ) • mk W y)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    rw [show (-((1 : ℕ) : ℤ)) = -1 by norm_num, ZhuW2.mk_L_neg_one_of_mem_grading W hy]
    simp
  | 2, _ => by
    rw [show (-((2 : ℕ) : ℤ)) = -2 by norm_num, mk_L_neg_two W hy]
    norm_num
  | m + 3, _ => by
    have h1 := mk_L_neg hy (m + 2) (by omega)
    have h2 := mk_L_neg hy (m + 1) (by omega)
    have hO := (mk_eq_zero_iff W).mpr (L_three_term_mem_O W m y)
    rw [map_add, map_add, map_smul] at hO
    rw [show (-((m + 2 : ℕ) : ℤ)) = -(m : ℤ) - 2 by push_cast; ring] at h1
    rw [show (-((m + 1 : ℕ) : ℤ)) = -(m : ℤ) - 1 by push_cast; ring] at h2
    rw [show (-((m + 3 : ℕ) : ℤ)) = -(m : ℤ) - 3 by push_cast; ring]
    have hA : mk W (W.L (-(m : ℤ) - 3) y) = -((2 : ℂ) • mk W (W.L (-(m : ℤ) - 2) y) +
        mk W (W.L (-(m : ℤ) - 1) y)) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact hO
    rw [hA, h1, h2]
    push_cast
    simp only [pow_succ, smul_add, smul_smul]
    module

theorem aeval_zfac (n : ℕ) (k : ℚ) (z : A W) :
    aeval (omegaL W) (zp (zfac n k)) z =
      ((-1 : ℂ) ^ n) • (((n : ℂ) - 1) • omegaL W z + (k : ℂ) • z) := by
  simp only [zfac, pscaleL, List.map_cons, List.map_nil, zp, map_add, map_mul, aeval_C,
    aeval_X, mul_zero, add_zero, LinearMap.add_apply, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one]
  push_cast
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_add, smul_smul]
  module

theorem evW_mem_grading {h : ℤ} {x : 𝒱} (hx : x ∈ W.grading h) :
    ∀ w : List ℕ, evW W x w ∈ W.grading (h + (w.sum : ℤ))
  | [] => by simpa [evW] using hx
  | n :: w => by
    have := L_mem_grading_ W (evW_mem_grading hx w) (-(n : ℤ))
    simp only [evW, List.sum_cons]
    convert this using 2; push_cast; ring

/-- The Zhu image of a word. -/
theorem mk_evW {h : ℕ} {x : 𝒱} (hx : x ∈ W.grading (h : ℤ)) :
    ∀ w : List ℕ, posW w = true →
      mk W (evW W x w) = aeval (omegaL W) (zp (zhuW (h : ℚ) w)) (mk W x)
  | [], _ => by simp [evW, zhuW, zp]
  | n :: w, hw => by
    simp only [posW, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    have ih := mk_evW hx w hw.2
    have hg := evW_mem_grading W hx w
    simp only [evW, zhuW]
    rw [mk_L_neg W hg n hw.1, zp_pmulL, map_mul, Module.End.mul_apply, ← ih, aeval_zfac]
    simp only [Int.cast_add, Int.cast_natCast, Rat.cast_add, Rat.cast_natCast]

/-- The Zhu image of a vector. -/
theorem mk_evV {h : ℕ} {x : 𝒱} (hx : x ∈ W.grading (h : ℤ)) :
    ∀ v : VVec, posV v = true →
      mk W (evV W x v) = aeval (omegaL W) (zp (zhuV (h : ℚ) v)) (mk W x)
  | [], _ => by simp [zhuV, zp]
  | p :: v, hv => by
    simp only [posV, List.all_cons, Bool.and_eq_true] at hv
    rw [evV_cons, map_add, map_smul, mk_evW W hx p.2 hv.1, mk_evV hx v hv.2]
    simp only [zhuV, zp_paddL, zp_pscaleL, map_add, map_mul, aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply]

end VOA.Classification.COne.OrbOdd
