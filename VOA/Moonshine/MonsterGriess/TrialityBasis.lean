/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Griess/TrialityBasis.lean
  CFSG/Monster/Griess/Space.lean (`card_pairIdx`, `coe_basisA`, `bform_tensor`, `BR`, `gramDiag`,
    `sum_sym2_indicator`, `trace_basisA_mul`, `card_shortIdx'`, `finrank_S`, `finrank_A`,
    `finrank_X`, `finrank_W`, `finrank_B`, `two_mem_dyadic_inv`)
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.TrialityClasses
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Axiom's Monster port (triality basis, part 3): the orthogonal basis `tbasis` of `SpaceB`

* `TIdx = Fin 24 ⊕ (LtPair × Fin 3) ⊕ (C₀ × Fin 24 × Fin 3) ⊕ OctIdx` (`card_tIdx = 196884`);
* ⭐ `tbasis : Basis TIdx ℚ SpaceB`, an orthogonal basis (`bform_tbasis`: the Gram matrix is
  `diagonal tnorm`, `tnorm ∈ {1, 2}`) adapted to triality: the diagonal matrix units, and triples
  `(basisA s(i,j), Xlift rMinus - Xlift rPlus, Xlift rMinus + Xlift rPlus)`,
  `(Xlift rOdd, ±E₁(c)⊗e_i, ±E₀(c)⊗e_i)` permuted cyclically by the triality, and the octad
  vectors `Xlift rOctQ`;
* `span_tbasis` — its `ℤ[1/2]`-span is the dyadic lattice `BR`;
* the summary `short_vector_triality_basis`.

## Port notes
* Namespace `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess` (as in the earlier ports).
  Module-system syntax, `@[expose]` and the source's `attribute [-instance] …` line dropped.
  Bodies verbatim except as listed.
* The pieces of `CFSG/Monster/Griess/Space.lean` not ported in `GriessTrilinear.lean`
  (`card_pairIdx`, `coe_basisA`, `bform_tensor`, `BR`, `gramDiag`, `sum_sym2_indicator`,
  `trace_basisA_mul`, `card_shortIdx'`, `finrank_S/A/X/W/B`, `two_mem_dyadic_inv`) are added at
  the top, verbatim.  `card_shortIdx'` uses our `card_shortIdx` (`LatticeFamilies.lean`).
* Drift: `ite_eq_left h`/`ite_eq_right h` (absent in Mathlib v4.30) ↦ `if_pos h`/`if_neg h`.
  In `linearIndependent_tvec` the second goal `¬bform.IsOrtho (tvec x) (tvec x)` is first
  restated with `change bform (tvec x) (tvec x) ≠ 0` (Mathlib v4.30's `rw` does not see through
  `IsOrtho`); `import Mathlib.LinearAlgebra.BilinearForm.Orthogonal` added.
* The source's private `sgn_mem_dyadic` (same statement as the public
  `VOA.Moonshine.MonsterGriess.sgn_mem_dyadic` of `OctadEvenSubset.lean`) is not repeated; the
  public lemma is used.
* **Re-proved (same statement):** `card_ltPair`.  The source uses `decide +kernel`; the port
  derives it from `card_fam₁Dom` (`LatticeFamilies.lean`, `fam₁Dom = {i < j} ×ˢ univ`), so the
  count of the 276 pairs `i < j` is kernel-computed only once in the library.
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.SpinLattice Matrix Module Subgroup

/-! ### From `CFSG/Monster/Griess/Space.lean` (the pieces not ported earlier) -/

theorem card_pairIdx : Fintype.card PairIdx = 300 := by
  rw [Sym2.card, Fintype.card_fin]
  rfl

theorem coe_basisA (i j : Fin 24) :
    (basisA s(i, j) : Matrix (Fin 24) (Fin 24) ℚ) =
      if i = j then Matrix.single i i 1 else Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l
  rw [basisA_apply]
  by_cases h : s(k, l) = s(i, j)
  · rw [if_pos h]
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · split_ifs with hkl
      · subst hkl; simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hkl]
    · split_ifs with hkl
      · subst hkl; simp [Matrix.single_apply]
      · simp [Matrix.single_apply, Ne.symm hkl]
  · rw [if_neg h]
    have h' : ¬ ((k = i ∧ l = j) ∨ (k = j ∧ l = i)) := fun h'' => h (Sym2.eq_iff.2 h'')
    split_ifs with hij
    · subst hij
      simp only [Matrix.single_apply]
      split_ifs with h3
      · exact absurd (Or.inl ⟨h3.1.symm, h3.2.symm⟩) h'
      · rfl
    · simp only [Matrix.add_apply, Matrix.single_apply]
      split_ifs with h3 h4 h4
      · exact absurd (Or.inl ⟨h3.1.symm, h3.2.symm⟩) h'
      · exact absurd (Or.inl ⟨h3.1.symm, h3.2.symm⟩) h'
      · exact absurd (Or.inr ⟨h4.1.symm, h4.2.symm⟩) h'
      · exact (add_zero 0).symm

theorem bform_tensor (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    bform (0, 0, tensor q v) (0, 0, tensor q' w) = (q ⬝ᵥ q') * (v ⬝ᵥ w) := by
  rw [bform_apply, dotProduct, dotProduct, Finset.sum_mul_sum]
  simp only [Submodule.coe_zero, Matrix.zero_mul, trace_zero, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, tensor, vecMulVec_apply]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

noncomputable def BR : Submodule dyadic SpaceB := Submodule.span dyadic (Set.range basisB)

def gramDiag : BIdx → ℚ
  | Sum.inl z => if z.IsDiag then 1 else 2
  | Sum.inr _ => 1

theorem sum_sym2_indicator (i j : Fin 24) :
    (∑ k : Fin 24, ∑ l : Fin 24, if s(k, l) = s(i, j) then (1 : ℚ) else 0) =
      if i = j then 1 else 2 := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Finset.sum_boole]
  have hf : (Finset.univ.filter fun p : Fin 24 × Fin 24 => s(p.1, p.2) = s(i, j)) =
      {(i, j), (j, i)} := by
    ext ⟨k, l⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
  rw [hf]
  split_ifs with h
  · subst h
    simp
  · rw [Finset.card_pair (by simp [Prod.ext_iff, h])]
    norm_num

theorem trace_basisA_mul (z z' : PairIdx) :
    trace ((basisA z : Matrix (Fin 24) (Fin 24) ℚ) * (basisA z' : Matrix (Fin 24) (Fin 24) ℚ)) =
      if z = z' then gramDiag (Sum.inl z) else 0 := by
  simp only [trace, diag, Matrix.mul_apply, basisA_apply]
  have hswap : ∀ k l : Fin 24, s(l, k) = s(k, l) := fun k l => Sym2.eq_swap
  simp only [hswap]
  split_ifs with h
  · subst h
    have e : ∀ k l : Fin 24, ((if s(k, l) = z then (1 : ℚ) else 0) *
        (if s(k, l) = z then (1 : ℚ) else 0)) = if s(k, l) = z then 1 else 0 := by
      intro k l
      split_ifs <;> norm_num
    simp only [e]
    induction z using Sym2.ind with
    | h i j =>
      rw [sum_sym2_indicator]
      simp only [gramDiag, Sym2.mk_isDiag_iff]
  · refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    · simp
    · simp
    · simp

theorem card_shortIdx' : Fintype.card ShortIdx = 98280 := by
  rw [← Nat.card_eq_fintype_card, card_shortIdx]

theorem finrank_S : finrank ℚ (SpinIdx → ℚ) = 4096 := by
  rw [Module.finrank_fintype_fun_eq_card, card_spinIdx]

theorem finrank_A : finrank ℚ symMat = 300 := by
  rw [finrank_eq_card_basis basisA, card_pairIdx]

theorem finrank_X : finrank ℚ SpaceX = 98280 := by
  rw [Module.finrank_fintype_fun_eq_card, card_shortIdx']

theorem finrank_W : finrank ℚ SpaceW = 98304 := by
  rw [Module.finrank_matrix, card_spinIdx, Fintype.card_fin, Module.finrank_self]

theorem finrank_B : finrank ℚ SpaceB = 196884 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_A, finrank_X, finrank_W]

theorem two_mem_dyadic_inv : ((2 : ℚ))⁻¹ ∈ dyadic := by
  have := inv_two_pow_mem_dyadic 1
  simpa using this

/-! ### From `CFSG/Monster/Griess/TrialityBasis.lean` -/

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem sgn_mul_self' (t : ZMod 2) : sgn t * sgn t = 1 := by
  rcases zmod2_cases t with rfl | rfl <;> norm_num [sgn]

theorem Xlift_labelElt (l : ShortLabel) : Xlift (labelElt l) = Pi.single (labelIdx l) 1 := by
  rw [Xlift_eq (isShortCoord_labelElt l), centralCoord_labelElt, sgn_zero, one_smul]
  rfl

theorem Xlift_labelElt_dotProduct (l l' : ShortLabel) :
    Xlift (labelElt l) ⬝ᵥ Xlift (labelElt l') = if l = l' then 1 else 0 := by
  rw [Xlift_labelElt, Xlift_labelElt, single_dotProduct_single]
  simp only [labelIdx_injective.eq_iff]

abbrev AIdx : Type := Fin 24 ⊕ LtPair

abbrev XIdx : Type := (LtPair × Fin 2) ⊕ (C₀ × Fin 24) ⊕ OctIdx

abbrev WIdx : Type := C₀ × Fin 24 × Fin 2

abbrev BlockIdx : Type := AIdx ⊕ XIdx ⊕ WIdx

noncomputable instance : DecidableEq XIdx :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)

noncomputable instance : DecidableEq BlockIdx :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)

def aPair : AIdx → PairIdx
  | .inl i => s(i, i)
  | .inr p => s(p.1.1, p.1.2)

theorem aPair_injective : Function.Injective aPair := by
  rintro (i | p) (i' | p') h <;> simp only [aPair, Sym2.eq_iff] at h
  · rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.symm.trans h2) p'.2.ne
    · exact absurd (h2.symm.trans h1) p'.2.ne
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) p.2.ne
    · exact absurd (h1.trans h2.symm) p.2.ne
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact congrArg Sum.inr (ltPair_eq h1 h2)
    · have h3 : p'.1.2 < p'.1.1 := by
        rw [← h1, ← h2]
        exact p.2
      exact absurd p'.2 (lt_asymm h3)

noncomputable def xVec : XIdx → SpaceX
  | .inl (p, k) => ![Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2),
      Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2)] k
  | .inr (.inl q) => Xlift (rOdd q.1 q.2)
  | .inr (.inr o) => Xlift (rOctQ o.1 o.2)

def wEta : Fin 2 → ZMod 2 := ![1, 0]

noncomputable def wSign (c : C₀) (i : Fin 24) : Fin 2 → ℚ :=
  ![sgn (((c : C) : Fin 24 → ZMod 2) i), sgn (P ((c : C) : Fin 24 → ZMod 2))]

noncomputable def wVec : WIdx → SpaceW
  | (c, i, k) => wSign c i k • tensor (Spin.E (wEta k) c) (Pi.single i 1)

noncomputable def blockVec : BlockIdx → SpaceB
  | .inl a => (basisA (aPair a), 0, 0)
  | .inr (.inl x) => (0, xVec x, 0)
  | .inr (.inr w) => (0, 0, wVec w)

def blockNorm : BlockIdx → ℚ
  | .inl (.inr _) => 2
  | .inr (.inl (.inl _)) => 2
  | _ => 1

theorem bform_mk (a a' : symMat) (x x' : SpaceX) (w w' : SpaceW) :
    bform (a, x, w) (a', x', w') = trace ((a : Matrix (Fin 24) (Fin 24) ℚ) *
      (a' : Matrix (Fin 24) (Fin 24) ℚ)) + x ⬝ᵥ x' + ∑ j, ∑ i, w j i * w' j i := rfl

theorem trace_basisA_aPair (a a' : AIdx) :
    trace ((basisA (aPair a) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (aPair a') : Matrix (Fin 24) (Fin 24) ℚ)) =
      if a = a' then blockNorm (.inl a) else 0 := by
  rw [trace_basisA_mul]
  by_cases h : a = a'
  · subst h
    rw [if_pos rfl, if_pos rfl]
    rcases a with i | p
    · simp [gramDiag, aPair, blockNorm]
    · simp [gramDiag, aPair, blockNorm, p.2.ne]
  · rw [if_neg (aPair_injective.ne h), if_neg h]

theorem xVec_inl (p : LtPair) (k : Fin 2) :
    xVec (.inl (p, k)) = ![Xlift (labelElt (.inl p)) - Xlift (labelElt (.inr (.inl p))),
      Xlift (labelElt (.inl p)) + Xlift (labelElt (.inr (.inl p)))] k := rfl

theorem xVec_odd (q : C₀ × Fin 24) :
    xVec (.inr (.inl q)) = Xlift (labelElt (.inr (.inr (.inl q)))) := rfl

theorem xVec_oct (o : OctIdx) : xVec (.inr (.inr o)) = Xlift (labelElt (.inr (.inr (.inr o)))) :=
  rfl

theorem xVec_dotProduct (x x' : XIdx) :
    xVec x ⬝ᵥ xVec x' = if x = x' then blockNorm (.inr (.inl x)) else 0 := by
  rcases x with ⟨p, k⟩ | q | o <;> rcases x' with ⟨p', k'⟩ | q' | o'
  · rw [xVec_inl, xVec_inl]
    by_cases hp : p = p'
    · subst hp
      fin_cases k <;> fin_cases k' <;>
        simp [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
          Xlift_labelElt_dotProduct, blockNorm] <;> norm_num
    · fin_cases k <;> fin_cases k' <;>
        simp [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
          Xlift_labelElt_dotProduct, hp]
  · rw [xVec_inl, xVec_odd]
    fin_cases k <;>
      simp [sub_dotProduct, add_dotProduct, Xlift_labelElt_dotProduct]
  · rw [xVec_inl, xVec_oct]
    fin_cases k <;>
      simp [sub_dotProduct, add_dotProduct, Xlift_labelElt_dotProduct]
  · rw [xVec_odd, xVec_inl]
    fin_cases k' <;>
      simp [dotProduct_sub, dotProduct_add, Xlift_labelElt_dotProduct]
  · rw [xVec_odd, xVec_odd, Xlift_labelElt_dotProduct]
    simp [blockNorm]
  · rw [xVec_odd, xVec_oct, Xlift_labelElt_dotProduct]
    simp
  · rw [xVec_oct, xVec_inl]
    fin_cases k' <;>
      simp [dotProduct_sub, dotProduct_add, Xlift_labelElt_dotProduct]
  · rw [xVec_oct, xVec_odd, Xlift_labelElt_dotProduct]
    simp
  · rw [xVec_oct, xVec_oct, Xlift_labelElt_dotProduct]
    simp [blockNorm]

theorem wEta_injective : Function.Injective wEta := by decide

theorem wSign_mul_self (c : C₀) (i : Fin 24) (k : Fin 2) : wSign c i k * wSign c i k = 1 := by
  fin_cases k <;> exact sgn_mul_self' _

theorem wVec_eq_tensor (w : WIdx) :
    wVec w = tensor (wSign w.1 w.2.1 w.2.2 • Spin.E (wEta w.2.2) w.1) (Pi.single w.2.1 1) := by
  obtain ⟨c, i, k⟩ := w
  rw [wVec, tensor, tensor, smul_vecMulVec]

theorem bform_wVec (w w' : WIdx) :
    bform (0, 0, wVec w) (0, 0, wVec w') = if w = w' then 1 else 0 := by
  rw [wVec_eq_tensor, wVec_eq_tensor, bform_tensor, smul_dotProduct, dotProduct_smul,
    E_dotProduct_E, single_dotProduct_single]
  obtain ⟨c, i, k⟩ := w
  obtain ⟨c', i', k'⟩ := w'
  simp only [smul_eq_mul, Prod.mk.injEq, wEta_injective.eq_iff]
  by_cases hk : k = k'
  · subst hk
    by_cases hc : c = c'
    · subst hc
      by_cases hi : i = i'
      · subst hi
        simp only [and_self, ite_true, mul_one]
        rw [mul_comm]
        exact wSign_mul_self c i k
      · simp [hi]
    · simp [hc]
  · simp [hk]

theorem bform_blockVec (β β' : BlockIdx) :
    bform (blockVec β) (blockVec β') = if β = β' then blockNorm β else 0 := by
  rcases β with a | x | w <;> rcases β' with a' | x' | w'
  · rw [blockVec, blockVec, bform_mk, trace_basisA_aPair]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk, xVec_dotProduct]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_wVec]
    simp [blockNorm]

abbrev TIdx : Type := Fin 24 ⊕ (LtPair × Fin 3) ⊕ (C₀ × Fin 24 × Fin 3) ⊕ OctIdx

noncomputable instance : DecidableEq TIdx :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance))

def toBlock : TIdx → BlockIdx
  | .inl i => .inl (.inl i)
  | .inr (.inl (p, k)) => ![.inl (.inr p), .inr (.inl (.inl (p, 0))), .inr (.inl (.inl (p, 1)))] k
  | .inr (.inr (.inl (c, i, k))) =>
    ![.inr (.inl (.inr (.inl (c, i)))), .inr (.inr (c, i, 0)), .inr (.inr (c, i, 1))] k
  | .inr (.inr (.inr o)) => .inr (.inl (.inr (.inr o)))

def ofBlock : BlockIdx → TIdx
  | .inl (.inl i) => .inl i
  | .inl (.inr p) => .inr (.inl (p, 0))
  | .inr (.inl (.inl (p, k))) => .inr (.inl (p, k.succ))
  | .inr (.inl (.inr (.inl q))) => .inr (.inr (.inl (q.1, q.2, 0)))
  | .inr (.inl (.inr (.inr o))) => .inr (.inr (.inr o))
  | .inr (.inr (c, i, k)) => .inr (.inr (.inl (c, i, k.succ)))

theorem ofBlock_toBlock (x : TIdx) : ofBlock (toBlock x) = x := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o
  · rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · rfl

theorem toBlock_injective : Function.Injective toBlock :=
  Function.LeftInverse.injective ofBlock_toBlock

noncomputable def tvec (x : TIdx) : SpaceB := blockVec (toBlock x)

def tnorm : TIdx → ℚ
  | .inr (.inl _) => 2
  | _ => 1

theorem tnorm_eq (x : TIdx) : tnorm x = blockNorm (toBlock x) := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o
  · rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · rfl

theorem tnorm_ne_zero (x : TIdx) : tnorm x ≠ 0 := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o <;> norm_num [tnorm]

theorem bform_tvec (x y : TIdx) : bform (tvec x) (tvec y) = if x = y then tnorm x else 0 := by
  rw [tvec, tvec, bform_blockVec]
  simp only [toBlock_injective.eq_iff]
  rw [tnorm_eq]

theorem linearIndependent_tvec : LinearIndependent ℚ tvec := by
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := bform) ?_ ?_
  · intro x y hxy
    change bform (tvec x) (tvec y) = 0
    rw [bform_tvec, if_neg hxy]
  · intro x
    change bform (tvec x) (tvec x) ≠ 0
    rw [bform_tvec, if_pos rfl]
    exact tnorm_ne_zero x

theorem card_ltPair : Fintype.card LtPair = 276 := by
  rw [Fintype.card_subtype]
  have h := card_fam₁Dom
  unfold fam₁Dom at h
  rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_bool] at h
  omega

theorem card_octadWord : Fintype.card OctadWord = 759 := by
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ C)
      (fun x => hammingNorm x = 8)), Fintype.card_of_subtype octFin (fun _ => mem_octFin),
    card_octFin]

theorem card_evenQuot_octSupp (d : OctadWord) : Fintype.card (Octad.EvenQuot (octSupp d)) = 64 :=
  Octad.card_evenQuot (card_octSupp d)

theorem card_octIdx : Fintype.card OctIdx = 759 * 64 := by
  rw [Fintype.card_sigma, Finset.sum_congr rfl fun d _ => card_evenQuot_octSupp d,
    Finset.sum_const, Finset.card_univ, card_octadWord, smul_eq_mul]

theorem card_tIdx : Fintype.card TIdx = 196884 := by
  simp only [TIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_ltPair, card_C₀,
    card_octIdx]

theorem card_shortLabel : Fintype.card ShortLabel = 98280 := by
  simp only [ShortLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_ltPair,
    card_C₀, card_octIdx]

noncomputable def tbasis : Basis TIdx ℚ SpaceB :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_tvec (card_tIdx.trans finrank_B.symm)

theorem coe_tbasis : ⇑tbasis = tvec := coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem tbasis_apply (x : TIdx) : tbasis x = blockVec (toBlock x) := congrFun coe_tbasis x

theorem bform_tbasis (x y : TIdx) : bform (tbasis x) (tbasis y) = if x = y then tnorm x else 0 := by
  rw [coe_tbasis]
  exact bform_tvec x y

theorem tbasis_diag (i : Fin 24) : tbasis (.inl i) = (basisA s(i, i), 0, 0) := tbasis_apply _

theorem tbasis_pair_zero (p : LtPair) :
    tbasis (.inr (.inl (p, 0))) = (basisA s(p.1.1, p.1.2), 0, 0) := tbasis_apply _

theorem tbasis_pair_one (p : LtPair) :
    tbasis (.inr (.inl (p, 1))) = (0, Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2), 0) :=
  tbasis_apply _

theorem tbasis_pair_two (p : LtPair) :
    tbasis (.inr (.inl (p, 2))) = (0, Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2), 0) :=
  tbasis_apply _

theorem tbasis_odd_zero (c : C₀) (i : Fin 24) :
    tbasis (.inr (.inr (.inl (c, i, 0)))) = (0, Xlift (rOdd c i), 0) := tbasis_apply _

theorem tbasis_odd_one (c : C₀) (i : Fin 24) :
    tbasis (.inr (.inr (.inl (c, i, 1)))) =
      (0, 0, sgn (((c : C) : Fin 24 → ZMod 2) i) • tensor (Spin.E 1 c) (Pi.single i 1)) :=
  tbasis_apply _

theorem tbasis_odd_two (c : C₀) (i : Fin 24) :
    tbasis (.inr (.inr (.inl (c, i, 2)))) =
      (0, 0, sgn (P ((c : C) : Fin 24 → ZMod 2)) • tensor (Spin.E 0 c) (Pi.single i 1)) :=
  tbasis_apply _

theorem tbasis_oct (o : OctIdx) : tbasis (.inr (.inr (.inr o))) = (0, Xlift (rOctQ o.1 o.2), 0) :=
  tbasis_apply _

theorem tbasis_oct_cls {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    tbasis (.inr (.inr (.inr ⟨d, Octad.cls (octSupp d) δ⟩))) = (0, Xlift (rOct d δ), 0) := by
  rw [tbasis_oct, rOctQ_cls hδ he]

theorem basisB_mem_BR (b : BIdx) : basisB b ∈ BR := Submodule.subset_span ⟨b, rfl⟩

theorem Xlift_labelElt_mem_BR (l : ShortLabel) :
    ((0 : symMat), Xlift (labelElt l), (0 : SpaceW)) ∈ BR := by
  rw [Xlift_labelElt, ← basisB_inr_inl]
  exact basisB_mem_BR _

theorem blockVec_W (c : C₀) (i : Fin 24) (k : Fin 2) :
    blockVec (.inr (.inr (c, i, k))) = wSign c i k • basisB (.inr (.inr ((wEta k, c), i))) := by
  rw [basisB_inr_inr, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]
  rfl

theorem blockVec_pair_zero (p : LtPair) :
    blockVec (.inr (.inl (.inl (p, 0)))) =
      ((0 : symMat), Xlift (labelElt (.inl p)), (0 : SpaceW)) -
        ((0 : symMat), Xlift (labelElt (.inr (.inl p))), (0 : SpaceW)) := by
  rw [Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]
  rfl

theorem blockVec_pair_one (p : LtPair) :
    blockVec (.inr (.inl (.inl (p, 1)))) =
      ((0 : symMat), Xlift (labelElt (.inl p)), (0 : SpaceW)) +
        ((0 : symMat), Xlift (labelElt (.inr (.inl p))), (0 : SpaceW)) := by
  rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]
  rfl

theorem wSign_mem_dyadic (c : C₀) (i : Fin 24) (k : Fin 2) : wSign c i k ∈ dyadic := by
  fin_cases k <;> exact sgn_mem_dyadic _

theorem blockVec_mem_BR (β : BlockIdx) : blockVec β ∈ BR := by
  rcases β with a | (⟨p, k⟩ | q | o) | ⟨c, i, k⟩
  · rw [blockVec, ← basisB_inl]
    exact basisB_mem_BR _
  · have h₁ := Xlift_labelElt_mem_BR (.inl p)
    have h₂ := Xlift_labelElt_mem_BR (.inr (.inl p))
    fin_cases k
    · show blockVec (.inr (.inl (.inl (p, 0)))) ∈ BR
      rw [blockVec_pair_zero]
      exact BR.sub_mem h₁ h₂
    · show blockVec (.inr (.inl (.inl (p, 1)))) ∈ BR
      rw [blockVec_pair_one]
      exact BR.add_mem h₁ h₂
  · exact Xlift_labelElt_mem_BR (.inr (.inr (.inl q)))
  · exact Xlift_labelElt_mem_BR (.inr (.inr (.inr o)))
  · rw [blockVec_W]
    exact BR.smul_mem ⟨_, wSign_mem_dyadic c i k⟩ (basisB_mem_BR _)

theorem tbasis_mem_BR (x : TIdx) : tbasis x ∈ BR := by
  rw [tbasis_apply]
  exact blockVec_mem_BR _

abbrev tspan : Submodule dyadic SpaceB := Submodule.span dyadic (Set.range tbasis)

theorem tbasis_mem_tspan (x : TIdx) : tbasis x ∈ tspan := Submodule.subset_span ⟨x, rfl⟩

theorem Xlift_labelElt_mem_tspan (l : ShortLabel) :
    ((0 : symMat), Xlift (labelElt l), (0 : SpaceW)) ∈ tspan := by
  rcases l with p | p | q | o
  · have e : ((0 : symMat), Xlift (labelElt (.inl p)), (0 : SpaceW)) =
        (2 : ℚ)⁻¹ • (tbasis (.inr (.inl (p, 1))) + tbasis (.inr (.inl (p, 2)))) := by
      rw [tbasis_pair_one, tbasis_pair_two, Prod.mk_add_mk, Prod.mk_add_mk, Prod.smul_mk,
        Prod.smul_mk, add_zero, add_zero, smul_zero, smul_zero]
      congr 2
      change _ = (2 : ℚ)⁻¹ • (Xlift (labelElt (.inl p)) - Xlift (labelElt (.inr (.inl p))) +
        (Xlift (labelElt (.inl p)) + Xlift (labelElt (.inr (.inl p)))))
      rw [sub_add_add_cancel, ← two_smul ℚ, smul_smul]
      norm_num
    rw [e]
    exact tspan.smul_mem ⟨_, two_mem_dyadic_inv⟩ (tspan.add_mem (tbasis_mem_tspan _)
      (tbasis_mem_tspan _))
  · have e : ((0 : symMat), Xlift (labelElt (.inr (.inl p))), (0 : SpaceW)) =
        (2 : ℚ)⁻¹ • (tbasis (.inr (.inl (p, 2))) - tbasis (.inr (.inl (p, 1)))) := by
      rw [tbasis_pair_one, tbasis_pair_two, Prod.mk_sub_mk, Prod.mk_sub_mk, Prod.smul_mk,
        Prod.smul_mk, sub_zero, sub_zero, smul_zero, smul_zero]
      congr 2
      change _ = (2 : ℚ)⁻¹ • (Xlift (labelElt (.inl p)) + Xlift (labelElt (.inr (.inl p))) -
        (Xlift (labelElt (.inl p)) - Xlift (labelElt (.inr (.inl p)))))
      rw [add_sub_sub_cancel, ← two_smul ℚ, smul_smul]
      norm_num
    rw [e]
    exact tspan.smul_mem ⟨_, two_mem_dyadic_inv⟩ (tspan.sub_mem (tbasis_mem_tspan _)
      (tbasis_mem_tspan _))
  · have e : tbasis (.inr (.inr (.inl (q.1, q.2, 0)))) =
        ((0 : symMat), Xlift (labelElt (.inr (.inr (.inl q)))), (0 : SpaceW)) :=
      tbasis_odd_zero q.1 q.2
    rw [← e]
    exact tbasis_mem_tspan _
  · have e : tbasis (.inr (.inr (.inr o))) =
        ((0 : symMat), Xlift (labelElt (.inr (.inr (.inr o)))), (0 : SpaceW)) := tbasis_oct o
    rw [← e]
    exact tbasis_mem_tspan _

theorem basisB_mem_tspan (b : BIdx) : basisB b ∈ tspan := by
  rcases b with z | c | ⟨⟨η, c⟩, i⟩
  · induction z using Sym2.ind with
    | h i j =>
      rw [basisB_inl]
      rcases lt_trichotomy i j with h | rfl | h
      · rw [← tbasis_pair_zero ⟨(i, j), h⟩]
        exact tbasis_mem_tspan _
      · rw [← tbasis_diag]
        exact tbasis_mem_tspan _
      · rw [Sym2.eq_swap, ← tbasis_pair_zero ⟨(j, i), h⟩]
        exact tbasis_mem_tspan _
  · obtain ⟨l, rfl⟩ := labelIdx_surjective c
    rw [basisB_inr_inl, ← Xlift_labelElt]
    exact Xlift_labelElt_mem_tspan l
  · have hk : ∃ k : Fin 2, wEta k = η := by
      rcases zmod2_cases η with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    obtain ⟨k, rfl⟩ := hk
    have e2 : tbasis (.inr (.inr (.inl (c, i, k.succ)))) = blockVec (.inr (.inr (c, i, k))) := by
      rw [tbasis_apply]
      fin_cases k <;> rfl
    have e : basisB (.inr (.inr ((wEta k, c), i))) =
        wSign c i k • tbasis (.inr (.inr (.inl (c, i, k.succ)))) := by
      rw [e2, blockVec_W, smul_smul, wSign_mul_self, one_smul]
    rw [e]
    exact tspan.smul_mem ⟨_, wSign_mem_dyadic c i k⟩ (tbasis_mem_tspan _)

theorem span_tbasis : Submodule.span dyadic (Set.range tbasis) = BR := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact tbasis_mem_BR x
  · rw [BR, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact basisB_mem_tspan b

theorem short_vector_triality_basis :
    (∀ i j : Fin 24, deltaPair i j = Submodule.Quotient.mk (Pi.single i 1 + Pi.single j 1) ∧
      rMinus i j = DQ (deltaPair i j) ∧ rPlus i j = XQ ⟨ΩC, 0⟩ * DQ (deltaPair i j)) ∧
    (∀ (c : C₀) (i : Fin 24),
      mOdd c i = ((c : C) : Fin 24 → ZMod 2) i + P ((c : C) : Fin 24 → ZMod 2) ∧
      rOdd c i = XQ ⟨(c : C) + mOdd c i • ΩC, 0⟩ * DQ (Submodule.Quotient.mk (Pi.single i 1))) ∧
    (∀ (d : C) (δ : Finset (Fin 24)), nOct δ = ((δ.card / 2 : ℕ) : ZMod 2) ∧
      rOct d δ = XQ ⟨d + nOct δ • ΩC, 0⟩ * DQ (Submodule.Quotient.mk (Octad.ind δ))) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      rOct d (octSupp d \ δ) = rOct d δ ∧ rOctQ d (Octad.cls (octSupp d) δ) = rOct d δ) ∧
    (∀ p : LtPair,
      IsShort (QuotientGroup.mk (rMinus p.1.1 p.1.2)) ∧
      IsShort (QuotientGroup.mk (rPlus p.1.1 p.1.2)) ∧
      (4 : ℤ) • eℤ p.1.1 - (4 : ℤ) • eℤ p.1.2 ∈ minVecs ∧
      (4 : ℤ) • eℤ p.1.1 + (4 : ℤ) • eℤ p.1.2 ∈ minVecs ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rMinus p.1.1 p.1.2))) =
        classOf ((4 : ℤ) • eℤ p.1.1 - (4 : ℤ) • eℤ p.1.2) ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rPlus p.1.1 p.1.2))) =
        classOf ((4 : ℤ) • eℤ p.1.1 + (4 : ℤ) • eℤ p.1.2)) ∧
    (∀ (c : C₀) (i : Fin 24), IsShort (QuotientGroup.mk (rOdd c i)) ∧
      oddMin i ((c : C) : Fin 24 → ZMod 2) ∈ minVecs ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rOdd c i))) =
        classOf (oddMin i ((c : C) : Fin 24 → ZMod 2))) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      IsShort (QuotientGroup.mk (rOct d δ)) ∧
      (2 : ℤ) • liftℤ ((d : C) : Fin 24 → ZMod 2) - (4 : ℤ) • liftℤ (Octad.ind δ) ∈ minVecs ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rOct d δ))) =
        classOf ((2 : ℤ) • liftℤ ((d : C) : Fin 24 → ZMod 2) - (4 : ℤ) • liftℤ (Octad.ind δ))) ∧
    (∀ p : LtPair, labelElt (.inl p) = rMinus p.1.1 p.1.2 ∧
      labelElt (.inr (.inl p)) = rPlus p.1.1 p.1.2) ∧
    (∀ q : C₀ × Fin 24, labelElt (.inr (.inr (.inl q))) = rOdd q.1 q.2) ∧
    (∀ o : OctIdx, labelElt (.inr (.inr (.inr o))) = rOctQ o.1 o.2) ∧
    (∀ l l' : ShortLabel,
      (QuotientGroup.mk (labelElt l) : Q ⧸ center Q) = QuotientGroup.mk (labelElt l') ↔ l = l') ∧
    (∀ c : Q ⧸ center Q, IsShort c ↔ ∃ l : ShortLabel, QuotientGroup.mk (labelElt l) = c) ∧
    (∀ (d d' : OctadWord) (δ δ' : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      δ' ⊆ octSupp d' → Even δ'.card →
      ((QuotientGroup.mk (rOct d δ) : Q ⧸ center Q) = QuotientGroup.mk (rOct d' δ') ↔
        d = d' ∧ (δ' = δ ∨ δ' = octSupp d \ δ))) ∧
    Function.Bijective labelIdx ∧ (∀ l : ShortLabel, (labelIdx l).1 = coordOf (labelElt l)) ∧
    Fintype.card LtPair = 276 ∧ Fintype.card (C₀ × Fin 24) = 49152 ∧
    Fintype.card OctadWord = 759 ∧
    (∀ d : OctadWord, Fintype.card (Octad.EvenQuot (octSupp d)) = 64) ∧
    Fintype.card ShortLabel = 98280 ∧ Nat.card ShortIdx = 98280 ∧
    (∀ i : Fin 24, tbasis (.inl i) = (basisA s(i, i), 0, 0) ∧
      (basisA s(i, i) : Matrix (Fin 24) (Fin 24) ℚ) = Matrix.single i i 1) ∧
    (∀ p : LtPair, tbasis (.inr (.inl (p, 0))) = (basisA s(p.1.1, p.1.2), 0, 0) ∧
      (basisA s(p.1.1, p.1.2) : Matrix (Fin 24) (Fin 24) ℚ) =
        Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1 ∧
      tbasis (.inr (.inl (p, 1))) =
        (0, Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2), 0) ∧
      tbasis (.inr (.inl (p, 2))) =
        (0, Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2), 0)) ∧
    (∀ (c : C₀) (i : Fin 24), tbasis (.inr (.inr (.inl (c, i, 0)))) = (0, Xlift (rOdd c i), 0) ∧
      tbasis (.inr (.inr (.inl (c, i, 1)))) =
        (0, 0, sgn (((c : C) : Fin 24 → ZMod 2) i) • tensor (Spin.E 1 c) (Pi.single i 1)) ∧
      tbasis (.inr (.inr (.inl (c, i, 2)))) =
        (0, 0, sgn (P ((c : C) : Fin 24 → ZMod 2)) • tensor (Spin.E 0 c) (Pi.single i 1))) ∧
    (∀ o : OctIdx, tbasis (.inr (.inr (.inr o))) = (0, Xlift (rOctQ o.1 o.2), 0)) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      tbasis (.inr (.inr (.inr ⟨d, Octad.cls (octSupp d) δ⟩))) = (0, Xlift (rOct d δ), 0)) ∧
    (∀ x y : TIdx, bform (tbasis x) (tbasis y) = if x = y then tnorm x else 0) ∧
    (∀ q : LtPair × Fin 3, tnorm (.inr (.inl q)) = 2) ∧ (∀ i : Fin 24, tnorm (.inl i) = 1) ∧
    (∀ q : (C₀ × Fin 24 × Fin 3) ⊕ OctIdx, tnorm (.inr (.inr q)) = 1) ∧
    Fintype.card TIdx = 196884 ∧
    Submodule.span dyadic (Set.range tbasis) = BR := by
  refine ⟨fun i j => ⟨rfl, rfl, rfl⟩, fun c i => ⟨rfl, rfl⟩, fun d δ => ⟨rfl, rfl⟩,
    fun d δ hδ he => ⟨rOct_compl d.2 hδ he, rOctQ_cls hδ he⟩, fun p => ?_, fun c i => ?_,
    fun d δ hδ he => ?_, fun p => ⟨rfl, rfl⟩, fun q => rfl, fun o => rfl, mk_labelElt_eq_iff,
    fun c => ⟨exists_labelElt_of_isShort, fun ⟨l, hl⟩ => (congrArg IsShort hl).mp
      (isShort_labelElt l)⟩, fun d d' δ δ' hδ he hδ' he' => mk_rOct_eq_iff hδ he hδ' he',
    labelIdx_bijective, fun l => rfl, card_ltPair, ?_, card_octadWord, card_evenQuot_octSupp,
    card_shortLabel, card_shortIdx, fun i => ⟨tbasis_diag i, ?_⟩, fun p => ⟨tbasis_pair_zero p, ?_,
      tbasis_pair_one p, tbasis_pair_two p⟩,
    fun c i => ⟨tbasis_odd_zero c i, tbasis_odd_one c i, tbasis_odd_two c i⟩, tbasis_oct,
    fun d δ hδ he => tbasis_oct_cls hδ he, bform_tbasis, fun q => rfl, fun i => rfl,
    fun q => by rcases q with q | q <;> rfl, card_tIdx, span_tbasis⟩
  · exact ⟨isShort_labelElt (.inl p), isShort_labelElt (.inr (.inl p)), vMinus_mem p.2,
      vPlus_mem p.2, (toAdd_phi_mk _).trans (phi0_coordOf_rMinus p.2),
      (toAdd_phi_mk _).trans (phi0_coordOf_rPlus p.2)⟩
  · exact ⟨isShort_labelElt (.inr (.inr (.inl (c, i)))), oddMin_mem c i,
      (toAdd_phi_mk _).trans (phi0_coordOf_rOdd c i)⟩
  · refine ⟨?_, vOct_mem (d : C).2 d.2 hδ he, (toAdd_phi_mk _).trans (phi0_coordOf_rOct d.2 hδ he)⟩
    rw [← rOctQ_cls hδ he]
    exact isShort_labelElt (.inr (.inr (.inr ⟨d, Octad.cls (octSupp d) δ⟩)))
  · rw [Fintype.card_prod, card_C₀, Fintype.card_fin]
  · rw [coe_basisA, if_pos rfl]
  · rw [coe_basisA, if_neg p.2.ne]

end VOA.Moonshine.MonsterGriess
