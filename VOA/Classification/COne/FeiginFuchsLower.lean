/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.FeiginFuchsCOne
import VOA.Examples.VirasoroVermaBSAAllLevels

/-!
# I1c: the Feigin–Fuchs `c = 1` radical bound, proved

`VirC1RadicalLevelBound` (`FeiginFuchsCOne.lean`): in the Verma module `M(1, μ²)` the
contravariant radical at level `N + m` (`N = 2μ + 1`) has dimension `≤ p(m)`. Hence
`virC1DegenerateCharacters_holds : VirC1DegenerateCharacters`.

## Method (a Jantzen-type determinant comparison along one Kac curve)

Deform along the `(1, N)` curve `c(t) = 13 - 6t - 6/t`, `h₀(t) = h_{1,N}(t)`, which passes
through `(c, h) = (1, μ²)` at `t = 1`. On the curve the BSA singular vector `S(t)` exists for every
`t ≠ 0`. Choose (once, at `t = 1`) a complement `f` of the descendants `L_{-λ} S(1)` in the level
`N + m` coordinate space. Then (`curve_identity`), for every `t ≠ 0`,
`det(T(t))² · K · R(t) = β(t)^{p(m)} · det G_m(c(t), h₀(t) + N) · det D(t)`,
where `R` is the Kac product with the `(1, N)` factor removed, `β(t)` is the divided difference
of `⟨S, S⟩`, and `D(t)` is the Gram block of `f`. The orders of vanishing at `t = 1` are
`ord R = aSum μ m = aSum μ 0 · p(m) + bSum μ m` (`aSum_rel`, from `Phi_shift`) and
`ord det G_m = bSum μ m`. The same identity at `m = 0`, where the radical is the singular line
(`finrank_vermaRadicalLevel_one_sq_first`) so `D(1)` is non-degenerate, gives
`β(t) = (t - 1)^{aSum μ 0} γ(t)` with `γ` continuous, `γ(1) ≠ 0`. Cancelling `(t - 1)^{…}` and
letting `t → 1` shows `det D(1) ≠ 0`, so the radical meets the span of `f` trivially and has
dimension `≤ p(m)` (`finrank_ker_le_of_block`). Only the unconditional Kac determinant
`kac_determinant_eval` is used; the crossing curve `h_{1,N}`/`h_{N,1}` is handled because only
the *shifted* determinant and the order bookkeeping enter, never the full order at `h = μ²`.

Source: Feigin–Fuchs, *Verma modules over the Virasoro algebra* (LNM 1060, 1984); Iohara–Koga,
*Representation theory of the Virasoro algebra*, Ch. 5 (Jantzen filtration argument).
-/

open Finset

noncomputable section

namespace VOA.Classification.COne.FFLower

open VOA.InverseDS.VirasoroVerma VOA.VirasoroScreening VOA.VirModule
open scoped Classical

/-! ## PBW coordinates of homogeneous vectors -/

/-- The PBW coordinates of a vector at level `n`, read from the sorted basis. -/
def lc (c h : ℂ) (n : ℕ) (v : Verma c h) : VermaPartitions n → ℂ :=
  fun i => (vermaSortedBasis c h).repr v ⟨i.val, i.2.1⟩

theorem lc_add (c h : ℂ) (n : ℕ) (v w : Verma c h) :
    lc c h n (v + w) = lc c h n v + lc c h n w := by
  funext i; simp [lc]

theorem lc_smul (c h : ℂ) (n : ℕ) (a : ℂ) (v : Verma c h) :
    lc c h n (a • v) = a • lc c h n v := by
  funext i; simp [lc]

theorem lc_sum {α : Type*} (s : Finset α) (c h : ℂ) (n : ℕ) (f : α → Verma c h) :
    lc c h n (∑ x ∈ s, f x) = ∑ x ∈ s, lc c h n (f x) := by
  funext i; simp [lc, Finset.sum_apply]

theorem repr_negWord_partition (c h : ℂ) (n : ℕ) (w : VermaPartitions n) :
    (vermaSortedBasis c h).repr (negWord c h w.val) = Finsupp.single ⟨w.val, w.2.1⟩ 1 := by
  rw [← vermaSortedBasis_apply c h ⟨w.val, w.2.1⟩, Module.Basis.repr_self]

theorem lc_levelState (c h : ℂ) (n : ℕ) (a : VermaPartitions n → ℂ) :
    lc c h n (vermaLevelState c h n a) = a := by
  funext i
  simp only [lc, vermaLevelState, map_sum, map_smul, repr_negWord_partition,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro he
    apply hb
    have := congrArg (fun z : {w : List ℕ // SortedWord w} => z.val) he
    exact Subtype.ext (by simpa using this)
  · simp

theorem levelState_lc (c h : ℂ) (n : ℕ) (v : Verma c h) (hv : v ∈ sortedSpan c h n) :
    vermaLevelState c h n (lc c h n v) = v := by
  obtain ⟨a, rfl⟩ := exists_vermaLevelState c h n v hv
  rw [lc_levelState]

theorem vermaLevelState_add (c h : ℂ) (n : ℕ) (a b : VermaPartitions n → ℂ) :
    vermaLevelState c h n (a + b) = vermaLevelState c h n a + vermaLevelState c h n b := by
  simp [vermaLevelState, add_smul, Finset.sum_add_distrib]

theorem vermaLevelState_smul (c h : ℂ) (n : ℕ) (r : ℂ) (a : VermaPartitions n → ℂ) :
    vermaLevelState c h n (r • a) = r • vermaLevelState c h n a := by
  simp [vermaLevelState, Finset.smul_sum, mul_smul]

theorem vermaLevelState_sum {α : Type*} (s : Finset α) (c h : ℂ) (n : ℕ)
    (f : α → VermaPartitions n → ℂ) :
    vermaLevelState c h n (∑ x ∈ s, f x) = ∑ x ∈ s, vermaLevelState c h n (f x) := by
  induction s using Finset.induction_on with
  | empty => simp [vermaLevelState]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vermaLevelState_add, ih]

/-- The level-`n` assembly as a linear map. -/
def levelStateLin (c h : ℂ) (n : ℕ) : (VermaPartitions n → ℂ) →ₗ[ℂ] Verma c h where
  toFun := vermaLevelState c h n
  map_add' := vermaLevelState_add c h n
  map_smul' := vermaLevelState_smul c h n

theorem levelStateLin_injective (c h : ℂ) (n : ℕ) : Function.Injective (levelStateLin c h n) := by
  intro a b hab
  have := congrArg (lc c h n) hab
  simpa [levelStateLin, lc_levelState] using this

/-- Coordinates of an arbitrary (unsorted) creation word, computed once at `(0,0)`. -/
def wc (n : ℕ) (w : List ℕ) : VermaPartitions n → ℂ := lc 0 0 n (negWord 0 0 w)

/-- The coordinates of a creation word do not depend on `(c, h)`. -/
theorem levelState_wc (c h : ℂ) (n : ℕ) (w : List ℕ) (hw : energyHW w = n) :
    vermaLevelState c h n (wc n w) = negWord c h w := by
  have hm : negWord c h w ∈ sortedSpan c h n := hw ▸ negWord_mem_sortedSpan c h w
  have he : wc n w = lc c h n (negWord c h w) := by
    funext i
    simp only [wc, lc]
    rw [verma_negWord_coordinates_independent c h 0 0 w]
  rw [he, levelState_lc c h n _ hm]

theorem negWord_append (c h : ℂ) (a b : List ℕ) :
    negWord c h (a ++ b) = vermaDescendant c h a (negWord c h b) := by
  induction a with
  | nil => rfl
  | cons i a ih => simp [vermaDescendant, ih]

theorem energyHW_append (a b : List ℕ) : energyHW (a ++ b) = energyHW a + energyHW b := by
  simp [energyHW]

/-- Coordinates of the descendant `L_{-λ} S` at level `N + m`, for `S` with coordinates `s`. -/
def dc (N m : ℕ) (lam : VermaPartitions m) (s : VermaPartitions N → ℂ) :
    VermaPartitions (N + m) → ℂ :=
  ∑ ν : VermaPartitions N, s ν • wc (N + m) (lam.val ++ ν.val)

theorem levelState_dc (c h : ℂ) (N m : ℕ) (lam : VermaPartitions m) (s : VermaPartitions N → ℂ) :
    vermaLevelState c h (N + m) (dc N m lam s) =
      vermaDescendant c h lam.val (vermaLevelState c h N s) := by
  rw [dc, vermaLevelState_sum]
  simp only [vermaLevelState_smul]
  rw [vermaLevelState, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [levelState_wc c h _ _ (by rw [energyHW_append, lam.2.2, ν.2.2]; ring), negWord_append,
    map_smul]

/-! ## The Gram matrix as a bilinear form -/

theorem gram_dot (c h : ℂ) (n : ℕ) (a b : VermaPartitions n → ℂ) :
    a ⬝ᵥ (vermaGramMatrix c h n).mulVec b =
      vermaContravariant c h (vermaLevelState c h n a) (vermaLevelState c h n b) := by
  simp only [dotProduct, vermaGramMatrix_mulVec, vermaLevelState, map_sum, map_smul,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- Iterated positive modes, adjoint to `vermaDescendant`. -/
def posAct (c h : ℂ) : List ℕ → Verma c h → Verma c h
  | [], y => y
  | i :: w, y => posAct c h w (vermaMode c h ((i : ℤ) + 1) y)

theorem posAct_cons (c h : ℂ) (i : ℕ) (w : List ℕ) (y : Verma c h) :
    posAct c h (i :: w) y = posAct c h w (vermaMode c h ((i : ℤ) + 1) y) := rfl

theorem contravariant_descendant (c h : ℂ) (w : List ℕ) (x y : Verma c h) :
    vermaContravariant c h (vermaDescendant c h w x) y =
      vermaContravariant c h x (posAct c h w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons i w ih =>
    simp only [vermaDescendant, LinearMap.comp_apply, posAct]
    rw [vermaContravariant_adj, ← ih, show -(-(i:ℤ)-1) = (i:ℤ)+1 by ring]

/-! ## A block determinant over `ℂ[X]` -/

section Block

open Polynomial

/-- The polynomial pairing `x ⬝ G(X) y`. -/
def pairX {ι : Type*} [Fintype ι] (G : Matrix ι ι ℂ[X]) (x y : ι → ℂ) : ℂ[X] :=
  (fun i => Polynomial.C (x i)) ⬝ᵥ G.mulVec (fun i => Polynomial.C (y i))

theorem eval_pairX {ι : Type*} [Fintype ι] (G : Matrix ι ι ℂ[X]) (x y : ι → ℂ) (h0 : ℂ) :
    (pairX G x y).eval h0 = x ⬝ᵥ (G.map (eval h0)).mulVec y := by
  simp [pairX, dotProduct, Matrix.mulVec, eval_finsetSum]

/-- **Block determinant with a vanishing column block.** If the columns `b (inl k)` are in the
kernel of `G(h₀)`, then `det(T)² det G(X)` is divisible by `(X - h₀)^{|κ|}` and the quotient at
`h₀` is `det A₁ · det D`, where `A₁` is the first divided difference of the `κ`-block and `D` is
the `ρ`-block at `h₀`. -/
theorem block_det {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (e : κ ⊕ ρ ≃ ι) (G : Matrix ι ι ℂ[X]) (h0 : ℂ)
    (hsym : (G.map (eval h0)).transpose = G.map (eval h0))
    (b : κ ⊕ ρ → ι → ℂ) (hb : ∀ k, (G.map (eval h0)).mulVec (b (Sum.inl k)) = 0) :
    ∃ Q : ℂ[X], Polynomial.C ((Matrix.of fun i k => b (e.symm k) i).det ^ 2) * G.det =
        (X - Polynomial.C h0) ^ Fintype.card κ * Q ∧
      Q.eval h0 = (Matrix.of fun k k' : κ =>
          (pairX G (b (Sum.inl k)) (b (Sum.inl k')) /ₘ (X - Polynomial.C h0)).eval h0).det *
        (Matrix.of fun j j' : ρ =>
          b (Sum.inr j) ⬝ᵥ (G.map (eval h0)).mulVec (b (Sum.inr j'))).det := by
  set G0 := G.map (eval h0) with hG0
  set T : Matrix ι (κ ⊕ ρ) ℂ[X] := Matrix.of fun i k => Polynomial.C (b k i) with hT
  set Gt : Matrix (κ ⊕ ρ) (κ ⊕ ρ) ℂ[X] := T.transpose * G * T with hGt
  have hGt_apply : ∀ k k', Gt k k' = pairX G (b k) (b k') := by
    intro k k'
    simp only [hGt, hT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, pairX,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  -- the determinant of `Gt`
  set M : Matrix ι ι ℂ := Matrix.of fun i k => b (e.symm k) i with hM
  have hdet : Gt.det = Polynomial.C (M.det ^ 2) * G.det := by
    have h1 : Gt.det = (Gt.submatrix e.symm e.symm).det := (Matrix.det_submatrix_equiv_self _ _).symm
    have h2 : Gt.submatrix e.symm e.symm =
        (M.map Polynomial.C).transpose * G * M.map Polynomial.C := by
      ext i j
      simp only [hGt, hT, hM, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.of_apply, Matrix.map_apply]
    rw [h1, h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, map_pow]
    ring
  -- divisibility of the `κ` columns
  have hroot : ∀ k'' (k : κ), IsRoot (Gt k'' (Sum.inl k)) h0 := by
    intro k'' k
    rw [IsRoot, hGt_apply, eval_pairX, ← hG0, hb k, dotProduct_zero]
  set d : κ ⊕ ρ → ℂ[X] := Sum.elim (fun _ => X - Polynomial.C h0) (fun _ => 1) with hd
  set Gh : Matrix (κ ⊕ ρ) (κ ⊕ ρ) ℂ[X] := Matrix.of fun k'' =>
    Sum.elim (fun k => Gt k'' (Sum.inl k) /ₘ (X - Polynomial.C h0)) (fun j => Gt k'' (Sum.inr j)) with hGh
  have hfac : Gt = Gh * Matrix.diagonal d := by
    refine Matrix.ext fun k'' k' => ?_
    rw [Matrix.mul_diagonal]
    cases k' with
    | inl k =>
      simp only [hGh, hd, Matrix.of_apply, Sum.elim_inl]
      rw [mul_comm]
      exact ((mul_divByMonic_eq_iff_isRoot).mpr (hroot k'' k)).symm
    | inr j => simp [hGh, hd]
  refine ⟨Gh.det, ?_, ?_⟩
  · rw [← hdet, hfac, Matrix.det_mul, Matrix.det_diagonal, Fintype.prod_sum_type]
    simp [hd, Finset.prod_const, mul_comm]
  · rw [← coe_evalRingHom, RingHom.map_det]
    have hblock : (evalRingHom h0).mapMatrix Gh =
        Matrix.fromBlocks
          (Matrix.of fun k k' : κ =>
            (pairX G (b (Sum.inl k)) (b (Sum.inl k')) /ₘ (X - Polynomial.C h0)).eval h0) 0
          (Matrix.of fun (j : ρ) (k : κ) =>
            (pairX G (b (Sum.inr j)) (b (Sum.inl k)) /ₘ (X - Polynomial.C h0)).eval h0)
          (Matrix.of fun j j' : ρ => b (Sum.inr j) ⬝ᵥ G0.mulVec (b (Sum.inr j'))) := by
      ext k'' k'
      cases k'' with
      | inl k =>
        cases k' with
        | inl k' => simp [hGh, hGt_apply]
        | inr j =>
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hGh, Matrix.of_apply,
            Sum.elim_inr, hGt_apply, coe_evalRingHom, eval_pairX, ← hG0, Matrix.fromBlocks_apply₁₂,
            Matrix.zero_apply]
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hb k, zero_dotProduct]
      | inr j =>
        cases k' with
        | inl k => simp [hGh, hGt_apply]
        | inr j' => simp [hGh, hGt_apply, eval_pairX, ← hG0]
    rw [hblock, Matrix.det_fromBlocks_zero₁₂]
    rfl

end Block

/-! ## The divided difference of the descendant Gram block -/

section Deriv

open Polynomial

/-- The Gram matrix at fixed central charge `c`, as a polynomial matrix in the weight `X`. -/
def GX (c : ℂ) (n : ℕ) : Matrix (VermaPartitions n) (VermaPartitions n) ℂ[X] :=
  vermaAlgebraGramMatrix (Polynomial.C c) Polynomial.X n

theorem GX_eval (c h : ℂ) (n : ℕ) (i j : VermaPartitions n) :
    (GX c n i j).eval h = vermaGramMatrix c h n i j := by
  have he := congrArg (fun M => M i j)
    (vermaAlgebraGramMatrix_eval (Polynomial.C c) Polynomial.X (Polynomial.aeval h) n)
  have e1 : (Polynomial.aeval h) (Polynomial.C c) = c := by simp
  simp only [Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at he
  rw [e1] at he
  rw [← he, GX, coe_aeval_eq_eval]

theorem GX_map_eval (c h : ℂ) (n : ℕ) : (GX c n).map (eval h) = vermaGramMatrix c h n := by
  ext i j; exact GX_eval c h n i j

/-- Iterated positive modes on polynomial word expressions. -/
def posForm {R : Type*} [CommRing R] [Algebra ℂ R] (C' H' : R) :
    List ℕ → VermaPolynomialForm R → VermaPolynomialForm R
  | [], f => f
  | i :: w, f => posForm C' H' w (polynomialModeAction C' H' ((i : ℤ) + 1) f)

theorem posForm_eval {R : Type*} [CommRing R] [Algebra ℂ R] (C' H' : R) (ev : R →ₐ[ℂ] ℂ)
    (w : List ℕ) (f : VermaPolynomialForm R) :
    evaluatePolynomialForm C' H' ev (posForm C' H' w f) =
      posAct (ev C') (ev H') w (evaluatePolynomialForm C' H' ev f) := by
  induction w generalizing f with
  | nil => rfl
  | cons i w ih => simp only [posForm, posAct, ih, evaluate_polynomialModeAction]

/-- The word expression of `L_{-λ'} S` for `S` with coordinates `s`. -/
def formDesc {R : Type*} [CommRing R] [Algebra ℂ R] (N : ℕ) (lam' : List ℕ)
    (s : VermaPartitions N → ℂ) : VermaPolynomialForm R :=
  ∑ ν : VermaPartitions N, Finsupp.single (lam' ++ ν.val) (algebraMap ℂ R (s ν))

theorem formDesc_eval {R : Type*} [CommRing R] [Algebra ℂ R] (C' H' : R) (ev : R →ₐ[ℂ] ℂ)
    (N : ℕ) (lam' : List ℕ) (s : VermaPartitions N → ℂ) :
    evaluatePolynomialForm C' H' ev (formDesc N lam' s) =
      vermaDescendant (ev C') (ev H') lam' (vermaLevelState (ev C') (ev H') N s) := by
  rw [formDesc, vermaLevelState, map_sum]
  have hsum : ∀ (t : Finset (VermaPartitions N)),
      evaluatePolynomialForm C' H' ev
        (∑ ν ∈ t, Finsupp.single (lam' ++ ν.val) (algebraMap ℂ R (s ν))) =
      ∑ ν ∈ t, evaluatePolynomialForm C' H' ev (Finsupp.single (lam' ++ ν.val) (algebraMap ℂ R (s ν))) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [evaluatePolynomialForm]
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, evaluatePolynomialForm_add, ih]
  rw [hsum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [evaluatePolynomialForm_single, AlgHom.commutes, Algebra.algebraMap_self_apply, negWord_append,
    map_smul]

theorem posAct_mem (c h : ℂ) (w : List ℕ) (k : ℕ) (y : Verma c h)
    (hy : y ∈ sortedSpan c h (k + energyHW w)) : posAct c h w y ∈ sortedSpan c h k := by
  induction w generalizing y with
  | nil => simpa using hy
  | cons i w ih =>
    apply ih
    apply verma_mode_mem_level c h _ _ y hy
    rw [energyHW_cons]; push_cast; ring

theorem posAct_add (c h : ℂ) (w : List ℕ) (x y : Verma c h) :
    posAct c h w (x + y) = posAct c h w x + posAct c h w y := by
  induction w generalizing x y with
  | nil => rfl
  | cons i w ih => simp only [posAct, map_add, ih]

theorem posAct_smul (c h : ℂ) (w : List ℕ) (a : ℂ) (x : Verma c h) :
    posAct c h w (a • x) = a • posAct c h w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => simp only [posAct, map_smul, ih]

/-- The polynomial coordinates of `posAct λ (L_{-λ'} S)` at level `N`. -/
def vX (c : ℂ) (N : ℕ) (lam lam' : List ℕ) (s : VermaPartitions N → ℂ) (i : VermaPartitions N) :
    ℂ[X] :=
  polynomialFormCoordinate
    (posForm (Polynomial.C c) Polynomial.X lam (formDesc (R := ℂ[X]) N lam' s)) ⟨i.val, i.2.1⟩

theorem vX_eval (c h : ℂ) (N : ℕ) (lam lam' : List ℕ) (s : VermaPartitions N → ℂ)
    (i : VermaPartitions N) :
    (vX c N lam lam' s i).eval h =
      lc c h N (posAct c h lam (vermaDescendant c h lam' (vermaLevelState c h N s))) i := by
  have he := polynomialFormCoordinate_eval (Polynomial.C c) Polynomial.X (Polynomial.aeval h)
    (posForm (Polynomial.C c) Polynomial.X lam (formDesc (R := ℂ[X]) N lam' s)) ⟨i.val, i.2.1⟩
  rw [posForm_eval, formDesc_eval] at he
  have e1 : (Polynomial.aeval h) (Polynomial.C c) = c := by simp
  rw [e1, aeval_X] at he
  rw [vX, ← coe_aeval_eq_eval, he]
  rfl

theorem levelZero_eq (c h : ℂ) (x : Verma c h) (hx : x ∈ sortedSpan c h 0) :
    x = vermaContravariant c h (highestVector c h) x • highestVector c h := by
  obtain ⟨a, rfl⟩ := exists_vermaLevelState c h 0 x hx
  let w0 : VermaPartitions 0 := ⟨[], sortedWord_nil, rfl⟩
  have hu : ∀ w : VermaPartitions 0, w = w0 := fun w =>
    Subtype.ext ((verma_energy_zero_iff w.val).mp w.property.2)
  have hx : vermaLevelState c h 0 a = a w0 • highestVector c h := by
    rw [vermaLevelState, Finset.sum_eq_single w0 (fun b _ hb => absurd (hu b) hb)
      (fun h => absurd (Finset.mem_univ _) h)]
    rfl
  rw [hx, map_smul, vermaContravariant_normalized, smul_eq_mul, mul_one]

theorem posAct_singularMap (c h0 : ℂ) (N : ℕ) (S : Verma c h0)
    (hS : S ∈ sortedSpan c h0 N) (h1 : vermaMode c h0 1 S = 0) (h2 : vermaMode c h0 2 S = 0)
    (w : List ℕ) (x : Verma c (h0 + N)) :
    posAct c h0 w (vermaSingularMap c h0 N S hS h1 h2 x) =
      vermaSingularMap c h0 N S hS h1 h2 (posAct c (h0 + N) w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    rw [posAct_cons, posAct_cons, ← ih]
    congr 1
    exact (vermaSingularMap_mode c h0 N S hS h1 h2 _ x).symm

theorem gram_eq_contravariant (c h : ℂ) (m : ℕ) (lam lam' : VermaPartitions m) :
    vermaGramMatrix c h m lam lam' =
      vermaContravariant c h (negWord c h lam.val) (negWord c h lam'.val) := rfl

/-- **Singular vectors turn positive-negative words into Gram entries.** -/
theorem posAct_desc_singular (c h0 : ℂ) (N m : ℕ) (S : Verma c h0)
    (hS : S ∈ sortedSpan c h0 N) (h1 : vermaMode c h0 1 S = 0) (h2 : vermaMode c h0 2 S = 0)
    (lam lam' : VermaPartitions m) :
    posAct c h0 lam.val (vermaDescendant c h0 lam'.val S) =
      vermaGramMatrix c (h0 + N) m lam lam' • S := by
  have hdesc : vermaDescendant c h0 lam'.val S =
      vermaSingularMap c h0 N S hS h1 h2 (negWord c (h0 + N) lam'.val) :=
    (verma_universalMap_word c h0 (h0 + N) S _ lam'.val).symm
  have hmem : posAct c (h0 + N) lam.val (negWord c (h0 + N) lam'.val) ∈
      sortedSpan c (h0 + N) 0 := by
    apply posAct_mem
    rw [zero_add, lam.2.2]
    exact negWord_mem_sortedSpan_of_sorted _ _ lam'.2.1 lam'.2.2
  have hcoef : vermaContravariant c (h0 + N) (highestVector c (h0 + N))
      (posAct c (h0 + N) lam.val (negWord c (h0 + N) lam'.val)) =
      vermaGramMatrix c (h0 + N) m lam lam' := by
    rw [← contravariant_descendant, vermaDescendant_highest, gram_eq_contravariant]
  have hhw : vermaSingularMap c h0 N S hS h1 h2 (highestVector c (h0 + N)) = S :=
    universalMap_highestVector _ _ _
  rw [hdesc, posAct_singularMap, levelZero_eq _ _ _ hmem, map_smul, hcoef, hhw]

theorem lc_eq_of_levelState (c h : ℂ) (n : ℕ) (a : VermaPartitions n → ℂ) (x : Verma c h)
    (hx : vermaLevelState c h n a = x) : lc c h n x = a := by
  rw [← hx, lc_levelState]

/-- **The divided difference of the descendant block.** For a singular vector `S` at level `N`
of `M(c, h₀)` with coordinates `s`, the first divided difference at `h₀` of the Gram pairing of
`L_{-λ} S, L_{-λ'} S` is `β · ⟨λ, λ'⟩_{M(c, h₀+N)}`, where `β` is the divided difference of
`⟨S, S⟩`. -/
theorem deriv_block (c h0 : ℂ) (N m : ℕ) (hN : 0 < N) (s : VermaPartitions N → ℂ)
    (h1 : vermaMode c h0 1 (vermaLevelState c h0 N s) = 0)
    (h2 : vermaMode c h0 2 (vermaLevelState c h0 N s) = 0) (lam lam' : VermaPartitions m) :
    (pairX (GX c (N + m)) (dc N m lam s) (dc N m lam' s) /ₘ (X - Polynomial.C h0)).eval h0 =
      (pairX (GX c N) s s /ₘ (X - Polynomial.C h0)).eval h0 *
        vermaGramMatrix c (h0 + N) m lam lam' := by
  set g := vermaGramMatrix c (h0 + N) m lam lam' with hg
  set q : ℂ[X] := X - Polynomial.C h0 with hq
  have hqm : q.Monic := monic_X_sub_C h0
  set r : VermaPartitions N → ℂ[X] := fun i => ∑ j, Polynomial.C (s j) * GX c N j i with hr
  set v : VermaPartitions N → ℂ[X] := vX c N lam.val lam'.val s with hv
  set p := pairX (GX c (N + m)) (dc N m lam s) (dc N m lam' s) with hp
  set P := pairX (GX c N) s s with hP
  -- the pointwise identity `p = Σ r_i v_i`
  have hpv : p = ∑ i, r i * v i := by
    apply Polynomial.funext
    intro h
    rw [hp, eval_pairX, GX_map_eval, gram_dot, levelState_dc, levelState_dc,
      contravariant_descendant, eval_finsetSum]
    have hmem : posAct c h lam.val (vermaDescendant c h lam'.val (vermaLevelState c h N s)) ∈
        sortedSpan c h N := by
      apply posAct_mem
      rw [lam.2.2]
      have := vermaDescendant_mem_level c h lam'.val N _ (vermaLevelState_mem c h N s)
      rw [lam'.2.2] at this
      convert this using 2
    rw [← levelState_lc c h N _ hmem, ← gram_dot]
    simp only [hr, hv, eval_mul, eval_finsetSum, GX_eval, vX_eval, eval_C, dotProduct,
      Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hP' : P = ∑ i, r i * Polynomial.C (s i) := by
    simp only [hP, hr, pairX, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- `S` is in the radical at `h₀`
  have hSmem := vermaLevelState_mem c h0 N s
  have hrad := vermaContravariant_singular_radical c h0 N hN _ hSmem h1 h2
  have hker : (vermaGramMatrix c h0 N).mulVec s = 0 :=
    (vermaGramMatrix_kernel_iff_radical c h0 N s).mpr hrad
  have hr0 : ∀ i, IsRoot (r i) h0 := by
    intro i
    have := congrFun hker i
    rw [← vermaGramMatrix_symm, Matrix.mulVec, Matrix.transpose] at this
    simp only [IsRoot, hr, eval_finsetSum, eval_mul, eval_C, GX_eval]
    simpa [dotProduct, Matrix.of_apply, mul_comm] using this
  -- `v(h₀) = g • s`
  have hv0 : ∀ i, IsRoot (v i - Polynomial.C (g * s i)) h0 := by
    intro i
    rw [IsRoot, eval_sub, eval_C, hv, vX_eval,
      posAct_desc_singular c h0 N m _ hSmem h1 h2 lam lam', lc_smul, lc_levelState]
    simp [hg]
  -- factor out `q`
  set rh : VermaPartitions N → ℂ[X] := fun i => r i /ₘ q
  set uh : VermaPartitions N → ℂ[X] := fun i => (v i - Polynomial.C (g * s i)) /ₘ q
  have hr_f : ∀ i, r i = q * rh i := fun i => ((mul_divByMonic_eq_iff_isRoot).mpr (hr0 i)).symm
  have hu_f : ∀ i, v i = q * uh i + Polynomial.C (g * s i) := fun i => by
    rw [((mul_divByMonic_eq_iff_isRoot).mpr (hv0 i))]; ring
  have hProot : IsRoot P h0 := by
    rw [IsRoot, hP', eval_finsetSum]
    exact Finset.sum_eq_zero fun i _ => by rw [eval_mul, hr0 i, zero_mul]
  have hP_f : P = q * (P /ₘ q) := ((mul_divByMonic_eq_iff_isRoot).mpr hProot).symm
  have hpq : p = q * (q * ∑ i, rh i * uh i + Polynomial.C g * (P /ₘ q)) := by
    rw [hpv]
    have : ∑ i, r i * v i = q * (q * ∑ i, rh i * uh i) + Polynomial.C g * P := by
      rw [hP']
      simp only [hu_f, hr_f, Finset.mul_sum, mul_add, Finset.sum_add_distrib, Polynomial.C_mul]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => by ring
      · refine Finset.sum_congr rfl fun i _ => by ring
    have hCP : Polynomial.C g * P = q * (Polynomial.C g * (P /ₘ q)) := by
      conv_lhs => rw [hP_f]
      ring
    rw [this, hCP]; ring
  rw [hpq, mul_divByMonic_cancel_left _ hqm]
  simp [hq]
  ring

end Deriv

/-! ## The identity along the `(1, N)` curve -/

section Curve

open Polynomial

/-- The `(1, N)` label in `kacLabels (N + m)`. -/
def labOne (N m : ℕ) (hN : 0 < N) : Fin (N + m) × Fin (N + m) :=
  (⟨0, by omega⟩, ⟨N - 1, by omega⟩)

theorem labOne_mem (N m : ℕ) (hN : 0 < N) : labOne N m hN ∈ kacLabels (N + m) := by
  simp only [kacLabels, labOne, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- The Kac product with the `(1, N)` factor removed. -/
def kwpRest (t : ℂ) (N m : ℕ) (hN : 0 < N) : ℂ[X] :=
  ∏ i ∈ (kacLabels (N + m)).erase (labOne N m hN),
    (X - Polynomial.C (fusionKacWeight (i.1.val + 1) (i.2.val + 1) t)) ^
      Fintype.card (VermaPartitions (N + m - (i.1.val + 1) * (i.2.val + 1)))

theorem fusionKacWeight_one_N (N : ℕ) (t : ℂ) (ht : t ≠ 0) :
    fusionKacWeight 1 (N : ℂ) t = vermaBSAWeight N t := by
  simp only [fusionKacWeight, vermaBSAWeight]
  field_simp
  ring

theorem kwp_split (t : ℂ) (ht : t ≠ 0) (N m : ℕ) (hN : 0 < N) :
    kacWeightProduct t (N + m) =
      (X - Polynomial.C (vermaBSAWeight N t)) ^ Fintype.card (VermaPartitions m) *
        kwpRest t N m hN := by
  rw [kacWeightProduct, kwpRest, ← Finset.mul_prod_erase _ _ (labOne_mem N m hN)]
  congr 1
  have h1 : (((labOne N m hN).1.val : ℕ) : ℂ) + 1 = 1 := by simp [labOne]
  have h2 : (((labOne N m hN).2.val : ℕ) : ℂ) + 1 = N := by
    simp only [labOne]
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have h3 : N + m - ((labOne N m hN).1.val + 1) * ((labOne N m hN).2.val + 1) = m := by
    simp only [labOne]; omega
  rw [h1, h2, h3, fusionKacWeight_one_N N t ht]

theorem eval_det_poly {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ[X]) (h : ℂ) :
    M.det.eval h = (M.map (eval h)).det := by
  rw [← coe_evalRingHom, RingHom.map_det]; rfl

/-- The Kac determinant as a polynomial identity in the weight. -/
theorem det_GX (t : ℂ) (ht : t ≠ 0) (n : ℕ) :
    (GX (vermaBSACharge t) n).det =
      Polynomial.C (∏ w : VermaPartitions n, vermaDiagonalContraction w.val) *
        kacWeightProduct t n := by
  apply Polynomial.funext
  intro h
  rw [eval_det_poly, GX_map_eval, kac_determinant_eval t ht h n, eval_mul, eval_C]

/-- The coordinates of the BSA singular vector on the `(1, N)` curve. -/
def bsaS (t : ℂ) (N : ℕ) : VermaPartitions N → ℂ :=
  lc (vermaBSACharge t) (vermaBSAWeight N t) N
    (vermaBSASource (vermaBSACharge t) (vermaBSAWeight N t) t N N)

theorem levelState_bsaS (t : ℂ) (N : ℕ) :
    vermaLevelState (vermaBSACharge t) (vermaBSAWeight N t) N (bsaS t N) =
      vermaBSASource (vermaBSACharge t) (vermaBSAWeight N t) t N N :=
  levelState_lc _ _ _ _ (vermaBSASource_mem_level _ _ t N N)

/-- The divided difference `β(t)` of `⟨S, S⟩` at the curve point. -/
def betaT (t : ℂ) (N : ℕ) : ℂ :=
  (pairX (GX (vermaBSACharge t) N) (bsaS t N) (bsaS t N) /ₘ
    (X - Polynomial.C (vermaBSAWeight N t))).eval (vermaBSAWeight N t)

/-- The basis family: descendants of the singular vector, then a fixed complement. -/
def famB (t : ℂ) (N m : ℕ) {ρ : Type*} (f : ρ → VermaPartitions (N + m) → ℂ) :
    VermaPartitions m ⊕ ρ → VermaPartitions (N + m) → ℂ :=
  Sum.elim (fun lam => dc N m lam (bsaS t N)) f

/-- **The quotient-determinant identity along the curve.** For every `t ≠ 0`:
`det(T)² · K · R(t) = β(t)^{p(m)} · det G_m(c, h₀ + N) · det D(t)`. -/
theorem curve_identity (t : ℂ) (ht : t ≠ 0) (N m : ℕ) (hN : 0 < N) {ρ : Type*} [Fintype ρ]
    (e : VermaPartitions m ⊕ ρ ≃ VermaPartitions (N + m))
    (f : ρ → VermaPartitions (N + m) → ℂ) :
    (Matrix.of fun i k => famB t N m f (e.symm k) i).det ^ 2 *
        (∏ w : VermaPartitions (N + m), vermaDiagonalContraction w.val) *
        (kwpRest t N m hN).eval (vermaBSAWeight N t) =
      betaT t N ^ Fintype.card (VermaPartitions m) *
        (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight N t + N) m).det *
        (Matrix.of fun j j' : ρ => f j ⬝ᵥ
          (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight N t) (N + m)).mulVec (f j')).det := by
  set c := vermaBSACharge t with hc
  set h0 := vermaBSAWeight N t with hh0
  have hsing := vermaBSASource_one_two_all t N ht hN
  rw [← levelState_bsaS] at hsing
  have hS1 := hsing.1
  have hS2 := hsing.2
  have hrad := vermaContravariant_singular_radical c h0 N hN _ (vermaLevelState_mem c h0 N _)
    hS1 hS2
  have hb : ∀ k, ((GX c (N + m)).map (eval h0)).mulVec (famB t N m f (Sum.inl k)) = 0 := by
    intro k
    rw [GX_map_eval, famB, Sum.elim_inl, vermaGramMatrix_kernel_iff_radical, levelState_dc]
    exact vermaDescendant_radical c h0 _ _ hrad
  have hsym : ((GX c (N + m)).map (eval h0)).transpose = (GX c (N + m)).map (eval h0) := by
    rw [GX_map_eval, vermaGramMatrix_symm]
  obtain ⟨Q, hQ, hQ0⟩ := block_det e (GX c (N + m)) h0 hsym (famB t N m f) hb
  set K := ∏ w : VermaPartitions (N + m), vermaDiagonalContraction w.val with hK
  set dT := (Matrix.of fun i k => famB t N m f (e.symm k) i).det with hdT
  have hQe : Q = Polynomial.C (dT ^ 2 * K) * kwpRest t N m hN := by
    rw [det_GX t ht, kwp_split t ht N m hN] at hQ
    have hne : (X - Polynomial.C h0) ^ Fintype.card (VermaPartitions m) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero h0)
    apply mul_left_cancel₀ hne
    rw [← hQ, Polynomial.C_mul]
    ring
  have hA : (Matrix.of fun k k' : VermaPartitions m =>
      (pairX (GX c (N + m)) (famB t N m f (Sum.inl k)) (famB t N m f (Sum.inl k')) /ₘ
        (X - Polynomial.C h0)).eval h0) = betaT t N • vermaGramMatrix c (h0 + N) m := by
    ext k k'
    simp only [Matrix.of_apply, famB, Sum.elim_inl, Matrix.smul_apply, smul_eq_mul]
    exact deriv_block c h0 N m hN (bsaS t N) hS1 hS2 k k'
  rw [hA, Matrix.det_smul, GX_map_eval] at hQ0
  rw [hQe, eval_mul, eval_C] at hQ0
  simp only [famB, Sum.elim_inr] at hQ0
  rw [← hQ0]

end Curve

/-! ## Continuity in the curve parameter -/

section Cont

open Filter Topology

theorem cAt_sum {α : Type*} (s : Finset α) (F : α → ℂ → ℂ) (t0 : ℂ)
    (h : ∀ a ∈ s, ContinuousAt (F a) t0) : ContinuousAt (fun t => ∑ a ∈ s, F a t) t0 :=
  tendsto_finsetSum s h

theorem cAt_prod {α : Type*} (s : Finset α) (F : α → ℂ → ℂ) (t0 : ℂ)
    (h : ∀ a ∈ s, ContinuousAt (F a) t0) : ContinuousAt (fun t => ∏ a ∈ s, F a t) t0 :=
  tendsto_finsetProd s h

theorem lc_mode_neg (c h : ℂ) (k q n : ℕ) (hn : n = q + 1 + k) (x : Verma c h)
    (hx : x ∈ sortedSpan c h k) :
    lc c h n (vermaMode c h (-(q : ℤ) - 1) x) =
      ∑ ν : VermaPartitions k, lc c h k x ν • wc n (q :: ν.val) := by
  conv_lhs => rw [← levelState_lc c h k x hx]
  rw [vermaLevelState, map_sum, lc_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, lc_smul, ← negWord_cons,
    lc_eq_of_levelState _ _ _ _ _ (levelState_wc c h n _ (by rw [energyHW_cons, ν.2.2]; omega))]

theorem bsaSource_cont (N r : ℕ) (cf hf : ℂ → ℂ)
    (ih : ∀ j < r, ∀ i : VermaPartitions j,
      ContinuousAt (fun t => lc (cf t) (hf t) j (vermaBSAState (cf t) (hf t) t N j) i) 1)
    (i : VermaPartitions r) :
    ContinuousAt (fun t => lc (cf t) (hf t) r (vermaBSASource (cf t) (hf t) t N r) i) 1 := by
  have he : ∀ t, lc (cf t) (hf t) r (vermaBSASource (cf t) (hf t) t N r) i =
      ∑ j : Fin r, ∑ ν : VermaPartitions j,
        lc (cf t) (hf t) j (vermaBSAState (cf t) (hf t) t N j) ν * wc r ((r - 1 - j) :: ν.val) i := by
    intro t
    rw [vermaBSASource, lc_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : ((j : ℕ) : ℤ) - (r : ℤ) = -((r - 1 - j : ℕ) : ℤ) - 1 := by omega
    rw [hj, lc_mode_neg _ _ j (r - 1 - j) r (by omega) _ (vermaBSAState_mem_level _ _ t N j),
      Finset.sum_apply]
    rfl
  simp only [he]
  refine cAt_sum _ _ _ fun j _ => cAt_sum _ _ _ fun ν _ => ?_
  exact (ih j j.isLt ν).mul continuousAt_const

theorem bsaState_cont (N : ℕ) (cf hf : ℂ → ℂ) :
    ∀ r, ∀ i : VermaPartitions r,
      ContinuousAt (fun t => lc (cf t) (hf t) r (vermaBSAState (cf t) (hf t) t N r) i) 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro i
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have he : ∀ t, lc (cf t) (hf t) 0 (vermaBSAState (cf t) (hf t) t N 0) i = wc 0 [] i := by
        intro t
        rw [vermaBSAState_zero, ← negWord_nil,
          lc_eq_of_levelState _ _ _ _ _ (levelState_wc _ _ 0 [] rfl)]
      simp only [he]
      exact continuousAt_const
    · have he : ∀ t, lc (cf t) (hf t) r (vermaBSAState (cf t) (hf t) t N r) i =
          (-t / ((r : ℂ) * ((N : ℂ) - (r : ℂ)))) *
            lc (cf t) (hf t) r (vermaBSASource (cf t) (hf t) t N r) i := by
        intro t
        rw [vermaBSAState_eq_source _ _ _ N r hpos, lc_smul]
        rfl
      simp only [he]
      refine ContinuousAt.mul ?_ (bsaSource_cont N r cf hf (fun j hj => ih j hj) i)
      exact (continuousAt_id.neg).div_const _

theorem bsaS_cont (N : ℕ) (i : VermaPartitions N) : ContinuousAt (fun t => bsaS t N i) 1 :=
  bsaSource_cont N N _ _ (fun j _ => bsaState_cont N _ _ j) i

theorem continuousAt_det {ι : Type*} [Fintype ι] (M : ℂ → Matrix ι ι ℂ) (t0 : ℂ)
    (hM : ∀ i j, ContinuousAt (fun t => M t i j) t0) : ContinuousAt (fun t => (M t).det) t0 :=
  (Continuous.matrix_det continuous_id).continuousAt.comp
    (continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => hM i j)

theorem gram_cont (cf hf : ℂ → ℂ) (t0 : ℂ) (hc : ContinuousAt cf t0) (hh : ContinuousAt hf t0)
    (n : ℕ) (i j : VermaPartitions n) :
    ContinuousAt (fun t => vermaGramMatrix (cf t) (hf t) n i j) t0 := by
  have he : ∀ t, vermaGramMatrix (cf t) (hf t) n i j =
      MvPolynomial.eval (fun k : Fin 2 => if k = 0 then cf t else hf t) (vermaGramPolynomial n i j) := by
    intro t
    rw [← vermaGramPolynomial_eval]
    simp [MvPolynomial.coe_aeval_eq_eval]
  simp only [he]
  refine (MvPolynomial.continuous_eval _).continuousAt.comp (continuousAt_pi.2 fun k => ?_)
  split_ifs
  · exact hc
  · exact hh

theorem charge_cont : ContinuousAt vermaBSACharge 1 := by
  unfold vermaBSACharge
  exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).sub
    (continuousAt_const.div continuousAt_id one_ne_zero)

theorem weight_cont (N : ℕ) : ContinuousAt (vermaBSAWeight N) 1 := by
  unfold vermaBSAWeight
  exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by norm_num)).sub
    continuousAt_const

end Cont

/-! ## Orders of the Kac factors at `t = 1` -/

section KacOrders

open Filter Topology

/-- The order at `t = 1` of `h_{1,2μ+1}(t) - h_{u,v}(t)` (for `(u,v) ≠ (1, 2μ+1)`). -/
def eR (μ u v : ℕ) : ℕ := (if v = u + 2 * μ then 1 else 0) + (if u = v + 2 * μ then 1 else 0)

/-- The reduced factor of `h_{1,2μ+1}(t) - h_{u,v}(t)`. -/
def gR (μ u v : ℕ) (t : ℂ) : ℂ :=
  (if v = u + 2 * μ then (1 - (u : ℂ)) else ((1 - (u : ℂ)) * t + ((v : ℂ) - (2 * μ + 1)))) *
    (if u = v + 2 * μ then (1 + (u : ℂ)) else ((1 + (u : ℂ)) * t - ((v : ℂ) + (2 * μ + 1)))) /
      (4 * t)

theorem factorR (μ u v : ℕ) (t : ℂ) (ht : t ≠ 0) :
    vermaBSAWeight (2 * μ + 1) t - fusionKacWeight u v t = (t - 1) ^ eR μ u v * gR μ u v t := by
  have key : vermaBSAWeight (2 * μ + 1) t - fusionKacWeight u v t =
      ((1 - (u : ℂ)) * t + ((v : ℂ) - (2 * μ + 1))) *
        ((1 + (u : ℂ)) * t - ((v : ℂ) + (2 * μ + 1))) / (4 * t) := by
    simp only [vermaBSAWeight, fusionKacWeight]; push_cast; field_simp; ring
  rw [key]
  unfold eR gR
  by_cases h1 : v = u + 2 * μ <;> by_cases h2 : u = v + 2 * μ
  · simp only [if_pos h1, if_pos h2]
    obtain rfl : μ = 0 := by omega
    obtain rfl : v = u := by omega
    push_cast; ring
  · simp only [if_pos h1, if_neg h2]
    subst h1; push_cast; ring
  · simp only [if_neg h1, if_pos h2]
    subst h2; push_cast; ring
  · simp only [if_neg h1, if_neg h2]
    ring

theorem gR_cont (μ u v : ℕ) : ContinuousAt (gR μ u v) 1 := by
  unfold gR
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (continuousAt_const.mul continuousAt_id)
    (by norm_num)
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).sub continuousAt_const

theorem gR_one_ne (μ u v : ℕ) (hne : ¬ (u = 1 ∧ v = 2 * μ + 1)) : gR μ u v 1 ≠ 0 := by
  unfold gR
  refine div_ne_zero (mul_ne_zero ?_ ?_) (by norm_num)
  · split_ifs with h1
    · intro h
      have hu : (u : ℂ) = 1 := by linear_combination -h
      have hu' : u = 1 := by exact_mod_cast hu
      exact hne ⟨hu', by omega⟩
    · intro h
      have hv : (v : ℂ) = ((u + 2 * μ : ℕ) : ℂ) := by push_cast; linear_combination h
      exact h1 (by exact_mod_cast hv)
  · split_ifs with h2
    · intro h
      have : ((1 + u : ℕ) : ℂ) = 0 := by push_cast; exact h
      have := Nat.cast_eq_zero.mp this
      omega
    · intro h
      have hu : (u : ℂ) = ((v + 2 * μ : ℕ) : ℂ) := by push_cast; linear_combination h
      exact h2 (by exact_mod_cast hu)

/-- The reduced factor of `h_{1,2μ+1}(t) + (2μ+1) - h_{u,v}(t)`. -/
def gG (μ u v : ℕ) (t : ℂ) : ℂ :=
  (if u = v + 2 * (μ + 1) then (1 - (u : ℂ)) else ((1 - (u : ℂ)) * t + ((2 * μ + 1) + (v : ℂ)))) *
    (if v = u + 2 * (μ + 1) then (1 + (u : ℂ)) else ((1 + (u : ℂ)) * t + ((2 * μ + 1) - (v : ℂ)))) /
      (4 * t)

theorem factorG (μ u v : ℕ) (t : ℂ) (ht : t ≠ 0) :
    vermaBSAWeight (2 * μ + 1) t + ((2 * μ + 1 : ℕ) : ℂ) - fusionKacWeight u v t =
      (t - 1) ^ eR (μ + 1) u v * gG μ u v t := by
  have key : vermaBSAWeight (2 * μ + 1) t + ((2 * μ + 1 : ℕ) : ℂ) - fusionKacWeight u v t =
      ((1 - (u : ℂ)) * t + ((2 * μ + 1) + (v : ℂ))) *
        ((1 + (u : ℂ)) * t + ((2 * μ + 1) - (v : ℂ))) / (4 * t) := by
    simp only [vermaBSAWeight, fusionKacWeight]; push_cast; field_simp; ring
  rw [key]
  unfold eR gG
  by_cases h1 : v = u + 2 * (μ + 1) <;> by_cases h2 : u = v + 2 * (μ + 1)
  · omega
  · simp only [if_pos h1, if_neg h2]
    subst h1; push_cast; ring
  · simp only [if_neg h1, if_pos h2]
    subst h2; push_cast; ring
  · simp only [if_neg h1, if_neg h2]
    ring

theorem gG_cont (μ u v : ℕ) : ContinuousAt (gG μ u v) 1 := by
  unfold gG
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (continuousAt_const.mul continuousAt_id)
    (by norm_num)
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const

theorem gG_one_ne (μ u v : ℕ) : gG μ u v 1 ≠ 0 := by
  unfold gG
  refine div_ne_zero (mul_ne_zero ?_ ?_) (by norm_num)
  · split_ifs with h1
    · intro h
      have hu : (u : ℂ) = 1 := by linear_combination -h
      have hu' : u = 1 := by exact_mod_cast hu
      omega
    · intro h
      have hu : (u : ℂ) = ((v + 2 * (μ + 1) : ℕ) : ℂ) := by push_cast; linear_combination -h
      exact h1 (by exact_mod_cast hu)
  · split_ifs with h2
    · intro h
      have : ((1 + u : ℕ) : ℂ) = 0 := by push_cast; exact h
      have := Nat.cast_eq_zero.mp this
      omega
    · intro h
      have hv : (v : ℂ) = ((u + 2 * (μ + 1) : ℕ) : ℂ) := by push_cast; linear_combination -h
      exact h2 (by exact_mod_cast hv)

theorem prod_order {α : Type*} (s : Finset α) (F g : α → ℂ) (e k : α → ℕ) (t : ℂ)
    (hF : ∀ a ∈ s, F a = (t - 1) ^ e a * g a) :
    ∏ a ∈ s, F a ^ k a = (t - 1) ^ (∑ a ∈ s, k a * e a) * ∏ a ∈ s, g a ^ k a := by
  rw [Finset.prod_congr rfl (fun a ha => by rw [hF a ha, mul_pow, ← pow_mul]),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### The exponent bookkeeping -/

/-- Partition numbers. -/
def pp (k : ℕ) : ℕ := Fintype.card (VermaPartitions k)

theorem pp_zero : pp 0 = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨⟨[], sortedWord_nil, rfl⟩, fun w =>
    Subtype.ext ((verma_energy_zero_iff w.val).mp w.property.2)⟩

def phi (μ n u : ℕ) : ℕ :=
  if (u + 1) * (u + 1 + 2 * μ) ≤ n then pp (n - (u + 1) * (u + 1 + 2 * μ)) else 0

def Phi (μ n : ℕ) : ℕ := ∑ u ∈ Finset.range n, phi μ n u

theorem sum_kacLabels (n : ℕ) (F : ℕ → ℕ → ℕ) :
    ∑ x ∈ kacLabels n, F (x.1.val + 1) (x.2.val + 1) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if (i + 1) * (j + 1) ≤ n then F (i + 1) (j + 1) else 0 := by
  rw [kacLabels, Finset.sum_filter, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n,
    if (i + 1) * (j + 1) ≤ n then F (i + 1) (j + 1) else 0) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun j => if (i.val + 1) * (j + 1) ≤ n then
    F (i.val + 1) (j + 1) else 0) n

theorem inner_collapse (μ n i : ℕ) :
    ∑ j ∈ Finset.range n, (if (i + 1) * (j + 1) ≤ n then
      pp (n - (i + 1) * (j + 1)) * (if j + 1 = i + 1 + 2 * μ then 1 else 0) else 0) =
      phi μ n i := by
  rw [Finset.sum_eq_single (i + 2 * μ)]
  · simp only [phi, show i + 2 * μ + 1 = i + 1 + 2 * μ by ring, if_true, mul_one]
  · intro b _ hb
    simp [show b + 1 ≠ i + 1 + 2 * μ by omega]
  · intro hni
    simp only [Finset.mem_range, not_lt] at hni
    have : ¬ (i + 1) * (i + 2 * μ + 1) ≤ n := by nlinarith
    simp [this]

theorem sum_eR (μ n : ℕ) :
    ∑ x ∈ kacLabels n, pp (n - (x.1.val + 1) * (x.2.val + 1)) * eR μ (x.1.val + 1) (x.2.val + 1) =
      2 * Phi μ n := by
  rw [sum_kacLabels n (fun u v => pp (n - u * v) * eR μ u v)]
  have hsplit : ∀ i j, (if (i + 1) * (j + 1) ≤ n then pp (n - (i + 1) * (j + 1)) *
      eR μ (i + 1) (j + 1) else 0) =
      (if (i + 1) * (j + 1) ≤ n then pp (n - (i + 1) * (j + 1)) *
        (if j + 1 = i + 1 + 2 * μ then 1 else 0) else 0) +
      (if (j + 1) * (i + 1) ≤ n then pp (n - (j + 1) * (i + 1)) *
        (if i + 1 = j + 1 + 2 * μ then 1 else 0) else 0) := by
    intro i j
    rw [eR, Nat.mul_comm (j + 1) (i + 1)]
    split_ifs <;> ring
  simp only [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (if (j + 1) * (i + 1) ≤ n then pp (n - (j + 1) * (i + 1)) *
        (if i + 1 = j + 1 + 2 * μ then 1 else 0) else 0))]
  simp only [inner_collapse, Phi]
  ring

theorem Phi_range (μ n L : ℕ) (hL : n ≤ L) :
    ∑ u ∈ Finset.range L, phi μ n u = Phi μ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hL
  rw [Finset.sum_range_add, Phi]
  have : ∑ x ∈ Finset.range k, phi μ n (n + x) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    have : ¬ (n + x + 1) * (n + x + 1 + 2 * μ) ≤ n := by nlinarith
    simp [phi, this]
  rw [this, add_zero]

theorem Phi_shift (μ m : ℕ) : Phi μ (2 * μ + 1 + m) = pp m + Phi (μ + 1) m := by
  rw [Phi, show 2 * μ + 1 + m = (2 * μ + m) + 1 by ring, Finset.sum_range_succ']
  have h0 : phi μ (2 * μ + m + 1) 0 = pp m := by
    simp only [phi]
    rw [if_pos (by nlinarith)]
    congr 1; ring_nf; omega
  have hs : ∀ u, phi μ (2 * μ + m + 1) (u + 1) = phi (μ + 1) m u := by
    intro u
    have hid : (u + 1 + 1) * (u + 1 + 1 + 2 * μ) = (u + 1) * (u + 1 + 2 * (μ + 1)) + (2 * μ + 1) := by
      ring
    simp only [phi, hid]
    by_cases hc : (u + 1) * (u + 1 + 2 * (μ + 1)) ≤ m
    · rw [if_pos (by omega), if_pos hc]
      congr 1; omega
    · rw [if_neg (by omega), if_neg hc]
  simp only [hs, h0]
  rw [Phi_range (μ + 1) m (2 * μ + m) (by omega)]
  ring

/-- The exponent of `t - 1` in the Kac product with the `(1,N)` factor removed. -/
def aSum (μ m : ℕ) : ℕ :=
  ∑ x ∈ (kacLabels (2 * μ + 1 + m)).erase (labOne (2 * μ + 1) m (by omega)),
    pp (2 * μ + 1 + m - (x.1.val + 1) * (x.2.val + 1)) * eR μ (x.1.val + 1) (x.2.val + 1)

/-- The exponent of `t - 1` in the shifted Kac product at level `m`. -/
def bSum (μ m : ℕ) : ℕ :=
  ∑ x ∈ kacLabels m, pp (m - (x.1.val + 1) * (x.2.val + 1)) * eR (μ + 1) (x.1.val + 1) (x.2.val + 1)

theorem aSum_eq (μ m : ℕ) : aSum μ m = (if μ = 0 then 0 else 1) * pp m + bSum μ m := by
  have hfull := sum_eR μ (2 * μ + 1 + m)
  rw [← Finset.sum_erase_add _ _ (labOne_mem (2 * μ + 1) m (by omega))] at hfull
  have hlab : pp (2 * μ + 1 + m - ((labOne (2 * μ + 1) m (by omega)).1.val + 1) *
      ((labOne (2 * μ + 1) m (by omega)).2.val + 1)) *
      eR μ ((labOne (2 * μ + 1) m (by omega)).1.val + 1)
        ((labOne (2 * μ + 1) m (by omega)).2.val + 1) =
      pp m * (if μ = 0 then 2 else 1) := by
    simp only [labOne, eR]
    rw [show 2 * μ + 1 + m - (0 + 1) * (2 * μ + 1 - 1 + 1) = m by omega]
    congr 1
    split_ifs <;> omega
  have hb : bSum μ m = 2 * Phi (μ + 1) m := sum_eR (μ + 1) m
  rw [hlab, Phi_shift] at hfull
  rw [aSum, hb]
  split_ifs at hfull ⊢ with hμ <;> omega

theorem aSum_rel (μ m : ℕ) : aSum μ m = aSum μ 0 * pp m + bSum μ m := by
  rw [aSum_eq μ m, aSum_eq μ 0, pp_zero]
  have : bSum μ 0 = 0 := by simp [bSum, kacLabels]
  rw [this]; ring

end KacOrders

/-! ## Finite-dimensional linear algebra for the block argument -/

section LinAlg

theorem linIndep_of_det {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (e : κ ⊕ ρ ≃ ι) (b : κ ⊕ ρ → ι → ℂ) (hM : (Matrix.of fun i k => b (e.symm k) i).det ≠ 0) :
    LinearIndependent ℂ b := by
  have h := Matrix.linearIndependent_cols_of_det_ne_zero hM
  have h' : LinearIndependent ℂ (fun k => b (e.symm k)) := by
    convert h using 1
  have := h'.comp e e.injective
  simpa [Function.comp_def] using this

theorem D_mulVec {ι ρ : Type*} [Fintype ι] [Fintype ρ] (G0 : Matrix ι ι ℂ) (f : ρ → ι → ℂ)
    (a : ρ → ℂ) (j : ρ) :
    ((Matrix.of fun j j' : ρ => f j ⬝ᵥ G0.mulVec (f j')).mulVec a) j =
      f j ⬝ᵥ G0.mulVec (∑ j', a j' • f j') := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The final count.** If the complement block of a symmetric form is non-degenerate, the
kernel has dimension at most the size of the other block. -/
theorem finrank_ker_le_of_block {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (e : κ ⊕ ρ ≃ ι) (G0 : Matrix ι ι ℂ) (b : κ ⊕ ρ → ι → ℂ)
    (hM : (Matrix.of fun i k => b (e.symm k) i).det ≠ 0)
    (hD : (Matrix.of fun j j' : ρ => b (Sum.inr j) ⬝ᵥ G0.mulVec (b (Sum.inr j'))).det ≠ 0) :
    Module.finrank ℂ (LinearMap.ker G0.mulVecLin) ≤ Fintype.card κ := by
  have hb := linIndep_of_det e b hM
  have hf : LinearIndependent ℂ (fun j => b (Sum.inr j)) := hb.comp Sum.inr Sum.inr_injective
  set W := Submodule.span ℂ (Set.range fun j => b (Sum.inr j)) with hW
  have hWr : Module.finrank ℂ W = Fintype.card ρ := finrank_span_eq_card hf
  have hdis : LinearMap.ker G0.mulVecLin ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxW⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hxW
    have hx' : G0.mulVec (∑ j, a j • b (Sum.inr j)) = 0 := by
      exact hx
    have ha : (Matrix.of fun j j' : ρ => b (Sum.inr j) ⬝ᵥ G0.mulVec (b (Sum.inr j'))).mulVec a
        = 0 := by
      funext j
      rw [D_mulVec, hx', dotProduct_zero]
      rfl
    have := Matrix.eq_zero_of_mulVec_eq_zero hD ha
    subst this
    simp
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker G0.mulVecLin) W
  rw [hdis, finrank_bot, add_zero, hWr] at hsum
  have hle := Submodule.finrank_le (LinearMap.ker G0.mulVecLin ⊔ W)
  rw [Module.finrank_fintype_fun_eq_card, ← Fintype.card_congr e, Fintype.card_sum] at hle
  omega

/-- **Non-degeneracy of a complement of the radical.** -/
theorem det_block_ne_zero {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (e : κ ⊕ ρ ≃ ι) (G0 : Matrix ι ι ℂ) (hsym : G0.transpose = G0)
    (b : κ ⊕ ρ → ι → ℂ)
    (hM : (Matrix.of fun i k => b (e.symm k) i).det ≠ 0)
    (hk : ∀ k, G0.mulVec (b (Sum.inl k)) = 0)
    (hker : Module.finrank ℂ (LinearMap.ker G0.mulVecLin) ≤ Fintype.card κ) :
    (Matrix.of fun j j' : ρ => b (Sum.inr j) ⬝ᵥ G0.mulVec (b (Sum.inr j'))).det ≠ 0 := by
  have hb := linIndep_of_det e b hM
  have hl : LinearIndependent ℂ (fun k => b (Sum.inl k)) := hb.comp Sum.inl Sum.inl_injective
  set U := Submodule.span ℂ (Set.range fun k => b (Sum.inl k)) with hU
  have hUle : U ≤ LinearMap.ker G0.mulVecLin := by
    rw [hU, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hk k
  have hUeq : U = LinearMap.ker G0.mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hUle (by rw [finrank_span_eq_card hl]; exact hker)
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set x := ∑ j, a j • b (Sum.inr j) with hx
  have hGx : G0.mulVec x = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hM
    funext k
    simp only [Matrix.vecMul, Pi.zero_apply]
    have hcol : (fun i => (Matrix.of fun i k => b (e.symm k) i) i k) = b (e.symm k) := rfl
    rcases hk' : e.symm k with k' | j
    · have : G0.mulVec x ⬝ᵥ b (Sum.inl k') = 0 := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hk k',
          zero_dotProduct]
      rw [← this]
      simp only [Matrix.of_apply, hk']
    · have := congrFun ha j
      rw [D_mulVec, Pi.zero_apply, dotProduct_comm, ← hx] at this
      rw [← this]
      simp only [Matrix.of_apply, hk']
  have hxU : x ∈ U := by rw [hUeq]; simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hGx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hxU
  have hz := Fintype.linearIndependent_iff.mp hb (Sum.elim c (-a)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hc, hx, add_neg_cancel])
  apply ha0
  funext j
  have := hz (Sum.inr j)
  simpa using this

/-- Extending a linearly independent family to a basis, with a nonzero determinant. -/
theorem exists_complement {ι κ : Type} [Fintype ι] [Finite κ] (v : κ → ι → ℂ)
    (hv : LinearIndependent ℂ v) :
    ∃ (ρ : Type) (_ : Fintype ρ) (e : κ ⊕ ρ ≃ ι) (f : ρ → ι → ℂ),
      (Matrix.of fun i k => Sum.elim v f (e.symm k) i).det ≠ 0 := by
  have := Fintype.ofFinite κ
  obtain ⟨q, hq⟩ := (Submodule.span ℂ (Set.range v)).exists_isCompl
  let bq := Module.finBasis ℂ q
  let f : Fin (Module.finrank ℂ q) → ι → ℂ := fun j => (bq j : ι → ℂ)
  have hf : LinearIndependent ℂ f :=
    bq.linearIndependent.map' q.subtype (Submodule.ker_subtype q)
  have hfq : Submodule.span ℂ (Set.range f) ≤ q :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => (bq j).2)
  have hli : LinearIndependent ℂ (Sum.elim v f) :=
    hv.sum_type hf (hq.disjoint.mono_right hfq)
  have hcard : Fintype.card (κ ⊕ Fin (Module.finrank ℂ q)) = Fintype.card ι := by
    rw [Fintype.card_sum, Fintype.card_fin, ← finrank_span_eq_card hv,
      Submodule.finrank_add_eq_of_isCompl hq, Module.finrank_fintype_fun_eq_card]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨Fin (Module.finrank ℂ q), inferInstance, e, f, ?_⟩
  have hcols := hli.comp _ e.symm.injective
  have hu : IsUnit (Matrix.of fun i k => Sum.elim v f (e.symm k) i) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hu).ne_zero

end LinAlg

/-! ## The two Kac products as `(t - 1)^order × (continuous, nonzero at 1)` -/

section Orders

open Polynomial Filter Topology

/-- The reduced remaining Kac product. -/
def GRm (μ m : ℕ) (t : ℂ) : ℂ :=
  ∏ x ∈ (kacLabels (2 * μ + 1 + m)).erase (labOne (2 * μ + 1) m (by omega)),
    gR μ (x.1.val + 1) (x.2.val + 1) t ^ pp (2 * μ + 1 + m - (x.1.val + 1) * (x.2.val + 1))

/-- The reduced shifted Kac product. -/
def GBm (μ m : ℕ) (t : ℂ) : ℂ :=
  ∏ x ∈ kacLabels m, gG μ (x.1.val + 1) (x.2.val + 1) t ^ pp (m - (x.1.val + 1) * (x.2.val + 1))

theorem kwpRest_eval_order (μ m : ℕ) (t : ℂ) (ht : t ≠ 0) :
    (kwpRest t (2 * μ + 1) m (by omega)).eval (vermaBSAWeight (2 * μ + 1) t) =
      (t - 1) ^ aSum μ m * GRm μ m t := by
  have hpp : ∀ k, Fintype.card (VermaPartitions k) = pp k := fun _ => rfl
  rw [kwpRest, eval_prod, aSum, GRm]
  simp only [eval_pow, eval_sub, eval_X, eval_C, hpp]
  refine prod_order _ _ _ _ _ t (fun x _ => ?_)
  have := factorR μ (x.1.val + 1) (x.2.val + 1) t ht
  push_cast at this
  exact this

theorem gram_shift_det_order (μ m : ℕ) (t : ℂ) (ht : t ≠ 0) :
    (vermaGramMatrix (vermaBSACharge t)
        (vermaBSAWeight (2 * μ + 1) t + ((2 * μ + 1 : ℕ) : ℂ)) m).det =
      (∏ w : VermaPartitions m, vermaDiagonalContraction w.val) *
        ((t - 1) ^ bSum μ m * GBm μ m t) := by
  have hpp : ∀ k, Fintype.card (VermaPartitions k) = pp k := fun _ => rfl
  rw [kac_determinant_eval t ht, kacWeightProduct, eval_prod, bSum, GBm]
  simp only [eval_pow, eval_sub, eval_X, eval_C, hpp]
  congr 1
  refine prod_order _ _ _ _ _ t (fun x _ => ?_)
  have := factorG μ (x.1.val + 1) (x.2.val + 1) t ht
  push_cast at this ⊢
  exact this

theorem GRm_cont (μ m : ℕ) : ContinuousAt (GRm μ m) 1 := by
  unfold GRm
  exact cAt_prod _ _ _ fun x _ => (gR_cont μ _ _).pow _

theorem GBm_cont (μ m : ℕ) : ContinuousAt (GBm μ m) 1 := by
  unfold GBm
  exact cAt_prod _ _ _ fun x _ => (gG_cont μ _ _).pow _

theorem GRm_one_ne (μ m : ℕ) : GRm μ m 1 ≠ 0 := by
  unfold GRm
  refine Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ (gR_one_ne μ _ _ ?_)
  rintro ⟨h1, h2⟩
  apply (Finset.mem_erase.mp hx).1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp only [labOne, Prod.mk.injEq, Fin.mk.injEq]
  simp only at h1 h2
  omega

theorem GBm_one_ne (μ m : ℕ) : GBm μ m 1 ≠ 0 := by
  unfold GBm
  exact Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (gG_one_ne μ _ _)

theorem bSum_zero (μ : ℕ) : bSum μ 0 = 0 := by simp [bSum, kacLabels]

/-- Two functions continuous at `1` that agree on a punctured neighbourhood agree at `1`. -/
theorem eq_at_one {F1 F2 : ℂ → ℂ} (h1 : ContinuousAt F1 1) (h2 : ContinuousAt F2 1)
    (h : ∀ᶠ t in 𝓝[≠] (1 : ℂ), F1 t = F2 t) : F1 1 = F2 1 :=
  tendsto_nhds_unique (h1.tendsto.mono_left nhdsWithin_le_nhds)
    ((h2.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ ht => ht.symm))

end Orders

/-! ## Assembly: the complement block is non-degenerate at `t = 1` -/

section Main

open Filter Topology

theorem radicalLevel_eq_map (c h : ℂ) (n : ℕ) :
    vermaRadicalLevel c h n =
      (LinearMap.ker (vermaGramMatrix c h n).mulVecLin).map (levelStateLin c h n) := by
  ext x
  constructor
  · rintro ⟨hx, hr⟩
    refine ⟨lc c h n x, ?_, levelState_lc c h n x hx⟩
    show (vermaGramMatrix c h n).mulVec (lc c h n x) = 0
    rw [vermaGramMatrix_kernel_iff_radical, levelState_lc c h n x hx]
    exact hr
  · rintro ⟨a, ha, rfl⟩
    exact ⟨vermaLevelState_mem c h n a, (vermaGramMatrix_kernel_iff_radical c h n a).mp ha⟩

/-- The level-`n` radical has the dimension of the Gram kernel. -/
theorem finrank_radicalLevel_eq (c h : ℂ) (n : ℕ) :
    Module.finrank ℂ (vermaRadicalLevel c h n) =
      Module.finrank ℂ (LinearMap.ker (vermaGramMatrix c h n).mulVecLin) := by
  rw [radicalLevel_eq_map]
  exact (Submodule.equivMapOfInjective _ (levelStateLin_injective c h n) _).finrank_eq.symm

theorem famB_cont (N m : ℕ) {ρ : Type*} (f : ρ → VermaPartitions (N + m) → ℂ)
    (x : VermaPartitions m ⊕ ρ) (i : VermaPartitions (N + m)) :
    ContinuousAt (fun t => famB t N m f x i) 1 := by
  cases x with
  | inl lam =>
    simp only [famB, Sum.elim_inl, dc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact cAt_sum _ _ _ fun ν _ => (bsaS_cont N ν).mul continuousAt_const
  | inr j => exact continuousAt_const

theorem dT_cont (N m : ℕ) {ρ : Type*} [Fintype ρ]
    (e : VermaPartitions m ⊕ ρ ≃ VermaPartitions (N + m)) (f : ρ → VermaPartitions (N + m) → ℂ) :
    ContinuousAt (fun t => (Matrix.of fun i k => famB t N m f (e.symm k) i).det) 1 :=
  continuousAt_det _ 1 fun i k => famB_cont N m f (e.symm k) i

theorem detD_cont (N n : ℕ) {ρ : Type*} [Fintype ρ] (f : ρ → VermaPartitions n → ℂ) :
    ContinuousAt (fun t => (Matrix.of fun j j' : ρ => f j ⬝ᵥ
      (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight N t) n).mulVec (f j')).det) 1 := by
  refine continuousAt_det _ 1 fun j j' => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec]
  exact cAt_sum _ _ _ fun i _ => continuousAt_const.mul (cAt_sum _ _ _ fun k _ =>
    (gram_cont _ _ 1 charge_cont (weight_cont N) n i k).mul continuousAt_const)

theorem bsa_singular (t : ℂ) (ht : t ≠ 0) (N : ℕ) (hN : 0 < N) :
    vermaMode (vermaBSACharge t) (vermaBSAWeight N t) 1
        (vermaLevelState (vermaBSACharge t) (vermaBSAWeight N t) N (bsaS t N)) = 0 ∧
      vermaMode (vermaBSACharge t) (vermaBSAWeight N t) 2
        (vermaLevelState (vermaBSACharge t) (vermaBSAWeight N t) N (bsaS t N)) = 0 := by
  rw [levelState_bsaS]
  exact vermaBSASource_one_two_all t N ht hN

/-- The descendants `L_{-λ} S` of the BSA singular vector are linearly independent. -/
theorem dc_linIndep (t : ℂ) (ht : t ≠ 0) (N m : ℕ) (hN : 0 < N) :
    LinearIndependent ℂ (fun lam : VermaPartitions m => dc N m lam (bsaS t N)) := by
  set c := vermaBSACharge t with hc
  set h0 := vermaBSAWeight N t with hh0
  set S := vermaLevelState c h0 N (bsaS t N) with hS
  have hSmem : S ∈ sortedSpan c h0 N := vermaLevelState_mem c h0 N _
  have hne : S ≠ 0 := by
    rw [hS, levelState_bsaS]; exact vermaBSASource_ne_zero c h0 t N ht hN
  obtain ⟨h1, h2⟩ := bsa_singular t ht N hN
  have hbasis := ((vermaSortedBasis c (h0 + N)).linearIndependent.comp
      (fun lam : VermaPartitions m => (⟨lam.val, lam.2.1⟩ : {w : List ℕ // SortedWord w}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))).map'
    (vermaSingularMap c h0 N S hSmem h1 h2)
    (LinearMap.ker_eq_bot.mpr (vermaSingularMap_injective c h0 N S hSmem hne h1 h2))
  apply LinearIndependent.of_comp (levelStateLin c h0 (N + m))
  convert hbasis using 1
  funext lam
  simp only [Function.comp_apply, levelStateLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [levelState_dc, vermaSortedBasis_apply]
  exact (verma_universalMap_word c h0 _ S _ lam.val).symm

theorem diag_ne (n : ℕ) : (∏ w : VermaPartitions n, vermaDiagonalContraction w.val) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun w _ => vermaDiagonalContraction_ne_zero _

/-- **The Feigin–Fuchs radical bound at `c = 1`.** -/
theorem radical_bound (μ m : ℕ) :
    Module.finrank ℂ (vermaRadicalLevel 1 ((μ ^ 2 : ℕ) : ℂ) (2 * μ + 1 + m)) ≤ pp m := by
  have hN : 0 < 2 * μ + 1 := by omega
  have hc1 : vermaBSACharge 1 = 1 := vermaBSACharge_one
  have hh1 : vermaBSAWeight (2 * μ + 1) 1 = ((μ ^ 2 : ℕ) : ℂ) := by
    rw [vermaBSAWeight]; push_cast; ring
  obtain ⟨ρ, _, e, f, hM⟩ := exists_complement _ (dc_linIndep 1 one_ne_zero (2 * μ + 1) m hN)
  obtain ⟨ρ0, _, e0, f0, hM0⟩ :=
    exists_complement _ (dc_linIndep 1 one_ne_zero (2 * μ + 1) 0 hN)
  -- the level-`(2μ+1)` complement is non-degenerate at `t = 1`
  have hD0 : (Matrix.of fun j j' : ρ0 => f0 j ⬝ᵥ (vermaGramMatrix (vermaBSACharge 1)
      (vermaBSAWeight (2 * μ + 1) 1) (2 * μ + 1 + 0)).mulVec (f0 j')).det ≠ 0 := by
    have := det_block_ne_zero e0 (vermaGramMatrix (vermaBSACharge 1)
      (vermaBSAWeight (2 * μ + 1) 1) (2 * μ + 1 + 0)) (vermaGramMatrix_symm _ _ _)
      (famB 1 (2 * μ + 1) 0 f0) hM0 ?_ ?_
    · simpa [famB] using this
    · intro k
      rw [famB, Sum.elim_inl, vermaGramMatrix_kernel_iff_radical, levelState_dc]
      obtain ⟨h1, h2⟩ := bsa_singular 1 one_ne_zero _ hN
      exact vermaDescendant_radical _ _ _ _ (vermaContravariant_singular_radical _ _ _ hN _
        (vermaLevelState_mem _ _ _ _) h1 h2)
    · rw [← finrank_radicalLevel_eq, hc1, hh1, Nat.add_zero, finrank_vermaRadicalLevel_one_sq_first]
      exact le_of_eq pp_zero.symm
  -- the functions of `t`
  set dT : ℂ → ℂ := fun t => (Matrix.of fun i k => famB t (2 * μ + 1) m f (e.symm k) i).det
    with hdT
  set dT0 : ℂ → ℂ := fun t => (Matrix.of fun i k => famB t (2 * μ + 1) 0 f0 (e0.symm k) i).det
    with hdT0
  set DD : ℂ → ℂ := fun t => (Matrix.of fun j j' : ρ => f j ⬝ᵥ (vermaGramMatrix (vermaBSACharge t)
      (vermaBSAWeight (2 * μ + 1) t) (2 * μ + 1 + m)).mulVec (f j')).det with hDD
  set DD0 : ℂ → ℂ := fun t => (Matrix.of fun j j' : ρ0 => f0 j ⬝ᵥ
      (vermaGramMatrix (vermaBSACharge t)
      (vermaBSAWeight (2 * μ + 1) t) (2 * μ + 1 + 0)).mulVec (f0 j')).det with hDD0
  set K := ∏ w : VermaPartitions (2 * μ + 1 + m), vermaDiagonalContraction w.val with hK
  set K0 := ∏ w : VermaPartitions (2 * μ + 1 + 0), vermaDiagonalContraction w.val with hK0
  set Km := ∏ w : VermaPartitions m, vermaDiagonalContraction w.val with hKm
  set Kz := ∏ w : VermaPartitions 0, vermaDiagonalContraction w.val with hKz
  set Den : ℂ → ℂ := fun t => Kz * GBm μ 0 t * DD0 t with hDen
  set γ : ℂ → ℂ := fun t => dT0 t ^ 2 * K0 * GRm μ 0 t / Den t with hγ
  have hDen_cont : ContinuousAt Den 1 :=
    (continuousAt_const.mul (GBm_cont μ 0)).mul (detD_cont _ _ f0)
  have hDen1 : Den 1 ≠ 0 := mul_ne_zero (mul_ne_zero (diag_ne 0) (GBm_one_ne μ 0)) hD0
  have hγ_cont : ContinuousAt γ 1 :=
    ((((dT_cont _ _ e0 f0).pow 2).mul continuousAt_const).mul (GRm_cont μ 0)).div hDen_cont hDen1
  -- eventually: `t ≠ 0`, `t ≠ 1`, `Den t ≠ 0`
  have hev : ∀ᶠ t in 𝓝[≠] (1 : ℂ), t ≠ 0 ∧ t ≠ 1 ∧ Den t ≠ 0 := by
    have h0 : ∀ᶠ t in 𝓝 (1 : ℂ), t ≠ 0 := eventually_ne_nhds one_ne_zero
    have h2 : ∀ᶠ t in 𝓝 (1 : ℂ), Den t ≠ 0 := hDen_cont.eventually_ne hDen1
    have h1 : ∀ᶠ t in 𝓝[≠] (1 : ℂ), t ≠ 1 := eventually_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds h0, h1, nhdsWithin_le_nhds h2] with t ha hb hc
    exact ⟨ha, hb, hc⟩
  -- the two curve identities
  have hF : ∀ᶠ t in 𝓝[≠] (1 : ℂ), dT t ^ 2 * K * GRm μ m t =
      γ t ^ pp m * (Km * GBm μ m t) * DD t := by
    filter_upwards [hev] with t ⟨ht0, ht1, hDt⟩
    have I0 := curve_identity t ht0 (2 * μ + 1) 0 hN e0 f0
    rw [kwpRest_eval_order μ 0 t ht0, gram_shift_det_order μ 0 t ht0, bSum_zero,
      show Fintype.card (VermaPartitions 0) = 1 from pp_zero, pow_one, pow_zero, one_mul] at I0
    have Im := curve_identity t ht0 (2 * μ + 1) m hN e f
    rw [kwpRest_eval_order μ m t ht0, gram_shift_det_order μ m t ht0] at Im
    have hβ : betaT t (2 * μ + 1) = (t - 1) ^ aSum μ 0 * γ t := by
      simp only [hγ, hDen] at hDt ⊢
      rw [mul_div_assoc', eq_div_iff hDt]
      linear_combination -I0
    rw [hβ, aSum_rel μ m] at Im
    have hne : (t - 1) ^ aSum μ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr ht1)
    apply mul_left_cancel₀ hne
    rw [aSum_rel μ m]
    have hpp : Fintype.card (VermaPartitions m) = pp m := rfl
    rw [hpp] at Im
    linear_combination Im
  have hlim := eq_at_one (F1 := fun t => dT t ^ 2 * K * GRm μ m t)
    (F2 := fun t => γ t ^ pp m * (Km * GBm μ m t) * DD t)
    ((((dT_cont _ _ e f).pow 2).mul continuousAt_const).mul (GRm_cont μ m))
    (((hγ_cont.pow _).mul (continuousAt_const.mul (GBm_cont μ m))).mul (detD_cont _ _ f)) hF
  simp only at hlim
  have hL1 : dT 1 ^ 2 * K * GRm μ m 1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM) (diag_ne _)) (GRm_one_ne μ m)
  have hD1 : DD 1 ≠ 0 := by
    intro h0
    apply hL1
    rw [hlim, h0, mul_zero]
  have hfin := finrank_ker_le_of_block e (vermaGramMatrix (vermaBSACharge 1)
    (vermaBSAWeight (2 * μ + 1) 1) (2 * μ + 1 + m)) (famB 1 (2 * μ + 1) m f) hM
    (by simpa [famB] using hD1)
  rw [← finrank_radicalLevel_eq, hc1, hh1] at hfin
  exact hfin

end Main

end VOA.Classification.COne.FFLower

namespace VOA.Classification.COne

/-- **The `c = 1` radical bound (Feigin–Fuchs lower bound), proved.** -/
theorem virC1RadicalLevelBound_holds : VirC1RadicalLevelBound :=
  fun μ m => FFLower.radical_bound μ m

/-- **The Feigin–Fuchs `c = 1` degenerate characters**:
`η · ch L(1, μ²) = q^{μ²} - q^{(μ+1)²}` for every `μ`. -/
theorem virC1DegenerateCharacters_holds : VirC1DegenerateCharacters :=
  virC1DegenerateCharacters_of_radicalLevelBound virC1RadicalLevelBound_holds

end VOA.Classification.COne
