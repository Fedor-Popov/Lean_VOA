/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetProductReduce

/-!
# The jet-ring lower bound `dim A_{r,N} ≥ [q^{N-r}] Σ_k [2r,k]_q / (q)_r`

For each charge `k ≤ 2r` (with `l = 2r - k`) the generating polynomials `Apol λ w` form a square
matrix (rows: multisets `λ` of `k` indices `≤ l`; columns: generator words `w` of charge `k`).
At the distinct points `t_i = i + 1` it is the matrix of the local products of
`JetProductLocal`, hence invertible (`local_indep`); so its determinant is a nonzero polynomial.

The functionals `Λ_{k,λ,α} = [u_λ v_0^l] ∘ E_α` (with `E_α` realizing `e^α`) are then linearly
independent on the weight-`N` piece of `A_r`: a relation would give a vector of symmetric
polynomials `y_λ = Σ_α c_{k,λ,α} e^α` killed by the matrix.

* `block_indep` — the vector-matrix statement for one charge;
* `card_jetIndex_le_finrank` — `#{(k, λ, α)} ≤ dim (jetDeg r N)`.

Everything is proved outright.
-/

namespace VOA.JetProduct

open MvPolynomial VOA.SymbolModel
open scoped BigOperators

noncomputable section

/-! ### Charges -/

/-- The `u`-degree of a generator. -/
def gdeg (g : Fin 4) : ℕ := tdeg (gtype g)

theorem gdeg_add_vcount (g : Fin 4) : gdeg g + vcount g = 2 := by
  fin_cases g <;> rfl

theorem sum_vcount {r : ℕ} (w : Fin r → Fin 4) :
    ∑ i, vcount (w i) = 2 * r - ∑ i, gdeg (w i) := by
  have h : ∑ i, gdeg (w i) + ∑ i, vcount (w i) = 2 * r := by
    rw [← Finset.sum_add_distrib]
    simp only [gdeg_add_vcount, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    ring
  omega

theorem gtype_injective : Function.Injective gtype := by decide

/-- The inverse of `gtype`. -/
def gtinv (x : Fin 4) : Fin 4 := ![2, 1, 3, 0] x

theorem gtinv_gtype (g : Fin 4) : gtinv (gtype g) = g := by fin_cases g <;> rfl

/-! ### The local independence at the standard points -/

/-- The standard distinct points `t_i = i + 1`. -/
def tStd {r : ℕ} (i : Fin r) : ℂ := (i : ℂ) + 1

theorem tStd_injective {r : ℕ} : Function.Injective (tStd (r := r)) := by
  intro i j h
  simp only [tStd, add_left_inj, Nat.cast_inj] at h
  exact Fin.ext h

/-- The standard configuration of `r` multiplicity-two points. -/
def stdConf (r : ℕ) : List Pt := List.ofFn fun i : Fin r => stdPt (tStd i)

theorem good_stdConf (r : ℕ) : Good (stdConf r) := by
  refine ⟨?_, ?_⟩
  · rw [stdConf, List.pairwise_ofFn]
    intro i j hij
    exact fun h => (ne_of_lt hij) (tStd_injective h)
  · intro p hp
    rw [stdConf, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact ⟨one_ne_zero, one_ne_zero⟩

theorem totalMult_allTwo : ∀ P : List Pt, (∀ p ∈ P, p.two = true) →
    totalMult P = 2 * P.length
  | [], _ => rfl
  | p :: P, h => by
    rw [totalMult_cons, totalMult_allTwo P (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      Pt.mult, if_pos (h p List.mem_cons_self), List.length_cons]
    ring

theorem mem_validSet_allTwo : ∀ (P : List Pt), (∀ p ∈ P, p.two = true) →
    ∀ (k : ℕ) (g : List (Fin 4)),
      g ∈ validSet P k ↔ g.length = P.length ∧ (g.map tdeg).sum = k
  | [], _, k, g => by
    simp only [validSet, List.length_nil]
    split_ifs with hk
    · subst hk
      constructor
      · intro h; rw [Finset.mem_singleton] at h; subst h; simp
      · rintro ⟨h1, -⟩; rw [List.length_eq_zero_iff] at h1; subst h1; simp
    · constructor
      · intro h; simp at h
      · rintro ⟨h1, h2⟩
        rw [List.length_eq_zero_iff] at h1; subst h1
        simp at h2; omega
  | p :: P, hP, k, g => by
    rw [mem_validSet_cons]
    have ih := mem_validSet_allTwo P (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    constructor
    · rintro ⟨x, g', rfl, -, hx, hg'⟩
      rw [ih] at hg'
      refine ⟨by simp [hg'.1], ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    · rintro ⟨h1, h2⟩
      obtain ⟨x, g', rfl⟩ : ∃ x g', g = x :: g' := by
        cases g with
        | nil => simp at h1
        | cons x g' => exact ⟨x, g', rfl⟩
      simp only [List.map_cons, List.sum_cons, List.length_cons, add_left_inj] at h1 h2
      refine ⟨x, g', rfl, Or.inl (hP p List.mem_cons_self), by omega, ?_⟩
      rw [ih]
      exact ⟨h1, by omega⟩

/-- The column words of charge `k`. -/
def colSet (r k : ℕ) : Finset (Fin r → Fin 4) :=
  Finset.univ.filter fun w => ∑ i, gdeg (w i) = k

/-- The type list of a word. -/
def typeList {r : ℕ} (w : Fin r → Fin 4) : List (Fin 4) := List.ofFn fun i => gtype (w i)

theorem typeList_injective {r : ℕ} : Function.Injective (typeList (r := r)) := by
  intro w w' h
  have := List.ofFn_injective h
  funext i
  exact gtype_injective (congrFun this i)

theorem gtype_gtinv (x : Fin 4) : gtype (gtinv x) = x := by fin_cases x <;> rfl

/-- The word of a type list. -/
def wOf (r : ℕ) (g : List (Fin 4)) : Fin r → Fin 4 := fun i => gtinv (g.getD i 0)

theorem wOf_typeList {r : ℕ} (w : Fin r → Fin 4) : wOf r (typeList w) = w := by
  funext i
  simp [wOf, typeList, gtinv_gtype]

theorem typeList_wOf {r : ℕ} (g : List (Fin 4)) (hg : g.length = r) :
    typeList (wOf r g) = g := by
  apply List.ext_getElem (by simp [typeList, hg])
  intro n h1 h2
  simp only [typeList, List.getElem_ofFn, wOf, gtype_gtinv]
  rw [List.getD_eq_getElem _ _ h2]

theorem stdConf_two (r : ℕ) : ∀ p ∈ stdConf r, p.two = true := by
  intro p hp; rw [stdConf, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; rfl

theorem length_stdConf (r : ℕ) : (stdConf r).length = r := by simp [stdConf]

theorem sum_tdeg_typeList {r : ℕ} (w : Fin r → Fin 4) :
    ((typeList w).map tdeg).sum = ∑ i, gdeg (w i) := by
  rw [typeList, List.map_ofFn, List.sum_ofFn]
  rfl

theorem validSet_stdConf (r k : ℕ) :
    validSet (stdConf r) k = (colSet r k).image typeList := by
  ext g
  rw [mem_validSet_allTwo _ (stdConf_two r), length_stdConf, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨wOf r g, ?_, typeList_wOf g h1⟩
    rw [colSet, Finset.mem_filter, ← sum_tdeg_typeList, typeList_wOf g h1]
    exact ⟨Finset.mem_univ _, h2⟩
  · rintro ⟨w, hw, rfl⟩
    rw [colSet, Finset.mem_filter] at hw
    exact ⟨by simp [typeList], by rw [sum_tdeg_typeList]; exact hw.2⟩

/-- **Local independence at the standard points**: the products of local forms indexed by the
words of charge `k` are linearly independent. -/
theorem std_local_indep (r k : ℕ) (y : (Fin r → Fin 4) → ℂ)
    (h : ∑ w ∈ colSet r k, y w • ∏ i, locG (2 * r - k) (tStd i) (w i) = 0) :
    ∀ w ∈ colSet r k, y w = 0 := by
  have hrel : ∑ g ∈ validSet (stdConf r) k, (fun g => y (wOf r g)) g •
      F (totalMult (stdConf r) - k) (stdConf r) g = 0 := by
    rw [validSet_stdConf, Finset.sum_image (fun a _ b _ hab => typeList_injective hab),
      totalMult_allTwo _ (stdConf_two r), length_stdConf]
    rw [← h]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only
    rw [wOf_typeList, prod_locG_eq_F]
    rfl
  intro w hw
  have := local_indep _ (stdConf r) rfl (good_stdConf r) k _ hrel (typeList w)
    (by rw [validSet_stdConf]; exact Finset.mem_image_of_mem _ hw)
  simpa [wOf_typeList] using this

/-! ### Homogeneity and support of the local products -/

theorem ev_isHomogeneous (l : ℕ) (t : ℂ) : (ev l t).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem evd_isHomogeneous (l : ℕ) (t : ℂ) : (evd l t).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem locG_isHomogeneous (l : ℕ) (t : ℂ) (g : Fin 4) :
    (locG l t g).IsHomogeneous (gdeg g) := by
  fin_cases g
  · simpa [locG, gdeg, gtype, tdeg] using (ev_isHomogeneous l t).pow 2
  · simpa [locG, gdeg, gtype, tdeg] using ev_isHomogeneous l t
  · simpa [locG, gdeg, gtype, tdeg] using isHomogeneous_one ℕ ℂ
  · simpa [locG, gdeg, gtype, tdeg] using evd_isHomogeneous l t

theorem prod_locG_isHomogeneous {r : ℕ} (l : ℕ) (t : Fin r → ℂ) (w : Fin r → Fin 4) :
    (∏ i, locG l (t i) (w i)).IsHomogeneous (∑ i, gdeg (w i)) :=
  IsHomogeneous.prod _ _ _ fun i _ => locG_isHomogeneous l (t i) (w i)

theorem ev_mem_supported (l : ℕ) (t : ℂ) : ev l t ∈ supported ℂ (Set.Iic l) :=
  Subalgebra.sum_mem _ fun _ hj => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (X_mem_supported.mpr (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))))

theorem evd_mem_supported (l : ℕ) (t : ℂ) : evd l t ∈ supported ℂ (Set.Iic l) :=
  Subalgebra.sum_mem _ fun _ hj => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (X_mem_supported.mpr (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))))

theorem locG_mem_supported (l : ℕ) (t : ℂ) (g : Fin 4) :
    locG l t g ∈ supported ℂ (Set.Iic l) := by
  fin_cases g
  · exact Subalgebra.pow_mem _ (ev_mem_supported l t) 2
  · exact ev_mem_supported l t
  · exact Subalgebra.one_mem _
  · exact evd_mem_supported l t

/-! ### The square blocks -/

/-- Row indices: multisets of `k` indices `≤ 2r - k`. -/
abbrev Rows (r k : ℕ) : Type := Sym (Fin (2 * r - k + 1)) k

/-- The multiset of a row index. -/
def msOf {r k : ℕ} (s : Rows r k) : Multiset ℕ := (s : Multiset (Fin (2 * r - k + 1))).map Fin.val

theorem msOf_le {r k : ℕ} (s : Rows r k) : ∀ j ∈ msOf s, j ≤ 2 * r - k := by
  intro j hj
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hj
  exact Nat.lt_succ_iff.mp x.2

theorem card_rows (r k : ℕ) (hk : k ≤ 2 * r) : Fintype.card (Rows r k) = (2 * r).choose k := by
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  congr 1
  omega

/-- Column indices: words of charge `k`. -/
abbrev Cols (r k : ℕ) : Type := {w : Fin r → Fin 4 // ∑ i, gdeg (w i) = k}

theorem card_cols (r k : ℕ) : Fintype.card (Cols r k) = (2 * r).choose k := by
  classical
  have hgen : (∑ w : Fin r → Fin 4, (Polynomial.X : Polynomial ℕ) ^ (∑ i, gdeg (w i))) =
      (1 + Polynomial.X) ^ (2 * r) := by
    have h1 : ∀ w : Fin r → Fin 4, (Polynomial.X : Polynomial ℕ) ^ (∑ i, gdeg (w i)) =
        ∏ i, Polynomial.X ^ gdeg (w i) := fun w => (Finset.prod_pow_eq_pow_sum _ _ _).symm
    simp only [h1]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ)
      (fun _ g => (Polynomial.X : Polynomial ℕ) ^ gdeg g), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, pow_mul]
    congr 1
    rw [Fin.sum_univ_four]
    simp [gdeg, gtype, tdeg]
    ring
  have hc := congrArg (fun p => Polynomial.coeff p k) hgen
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Polynomial.coeff_one_add_X_pow,
    Nat.cast_id] at hc
  rw [← hc, Finset.sum_boole, Fintype.card_subtype]
  simp only [Nat.cast_id]
  congr 1
  ext w
  simp [eq_comm]

/-- A monomial in the support of a charge-`k` local product comes from a row index. -/
theorem exists_row_of_coeff {r k : ℕ} (_hk : k ≤ 2 * r) (Q : UPoly)
    (hQ : Q.IsHomogeneous k) (hS : Q ∈ supported ℂ (Set.Iic (2 * r - k)))
    (d : ℕ →₀ ℕ) (hd : coeff d Q ≠ 0) : ∃ s : Rows r k, Multiset.toFinsupp (msOf s) = d := by
  have hdeg : d.degree = k := by
    have := hQ hd
    rwa [Finsupp.degree_eq_weight_one]
  have hsupp : ∀ j ∈ d.support, j ≤ 2 * r - k := by
    intro j hj
    have hv : j ∈ Q.vars := (mem_vars_iff_mem_support j).mpr ⟨d, mem_support_iff.mpr hd, hj⟩
    exact Set.mem_Iic.mp ((mem_supported.mp hS) hv)
  have hmem : ∀ j ∈ Finsupp.toMultiset d, j < 2 * r - k + 1 := by
    intro j hj
    rw [Finsupp.mem_toMultiset] at hj
    exact Nat.lt_succ_iff.mpr (hsupp j hj)
  refine ⟨⟨(Finsupp.toMultiset d).pmap (fun j hj => (⟨j, hj⟩ : Fin (2 * r - k + 1))) hmem, ?_⟩, ?_⟩
  · rw [Multiset.card_pmap, Finsupp.card_toMultiset, ← hdeg, Finsupp.degree]
    rfl
  · rw [Multiset.toFinsupp_eq_iff, msOf]
    simp only [Sym.coe_mk, Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']

theorem eval_Apol_col {r k : ℕ} (s : Rows r k) (w : Cols r k) (_hk : k ≤ 2 * r) :
    eval tStd (Apol (msOf s) (2 * r - k) w.1) =
      coeff (Multiset.toFinsupp (msOf s)) (∏ i, locG (2 * r - k) (tStd i) (w.1 i)) := by
  rw [eval_Apol _ _ (msOf_le s), if_pos]
  rw [sum_vcount, w.2]

open Matrix in
/-- **The block matrix is nondegenerate**: a vector of polynomials killed by the charge-`k`
block of generating polynomials is zero. -/
theorem block_indep (r k : ℕ) (hk : k ≤ 2 * r) (y : Rows r k → MvPolynomial (Fin r) ℂ)
    (h : ∀ w : Cols r k, ∑ s, y s * Apol (msOf s) (2 * r - k) w.1 = 0) : y = 0 := by
  classical
  let e : Rows r k ≃ Cols r k := Fintype.equivOfCardEq (by rw [card_rows r k hk, card_cols])
  let M : Matrix (Rows r k) (Rows r k) (MvPolynomial (Fin r) ℂ) :=
    fun s s' => Apol (msOf s) (2 * r - k) (e s').1
  have hM : y ᵥ* M = 0 := by
    funext s'
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    exact h (e s')
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 : (M.map (eval tStd)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
    apply hc
    -- the local product combination vanishes
    set Q : UPoly := ∑ s', c s' • ∏ i, locG (2 * r - k) (tStd i) ((e s').1 i) with hQdef
    have hcoeffQ : ∀ s : Rows r k, coeff (Multiset.toFinsupp (msOf s)) Q = 0 := by
      intro s
      have := congrFun hMc s
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this
      rw [hQdef, coeff_sum]
      rw [← this]
      apply Finset.sum_congr rfl
      intro s' _
      rw [coeff_smul, eval_Apol_col s (e s') hk, smul_eq_mul, mul_comm]
    have hhom : Q.IsHomogeneous k := by
      apply IsHomogeneous.sum
      intro s' _
      have := prod_locG_isHomogeneous (2 * r - k) tStd (e s').1
      rw [(e s').2] at this
      rw [smul_eq_C_mul]
      exact this.C_mul _
    have hsupp : Q ∈ supported ℂ (Set.Iic (2 * r - k)) :=
      Subalgebra.sum_mem _ fun s' _ => Subalgebra.smul_mem _
        (Subalgebra.prod_mem _ fun i _ => locG_mem_supported _ _ _) _
    have hQ0 : Q = 0 := by
      ext d
      rw [coeff_zero]
      by_contra hd
      obtain ⟨s, hs⟩ := exists_row_of_coeff hk Q hhom hsupp d hd
      exact hd (hs ▸ hcoeffQ s)
    let y' : (Fin r → Fin 4) → ℂ := fun w =>
      if hw : ∑ i, gdeg (w i) = k then c (e.symm ⟨w, hw⟩) else 0
    have hrel : ∑ w ∈ colSet r k, y' w • ∏ i, locG (2 * r - k) (tStd i) (w i) = 0 := by
      rw [Finset.sum_subtype (colSet r k) (p := fun w => ∑ i, gdeg (w i) = k)
        (fun w => by simp [colSet])]
      rw [← hQ0, hQdef, ← Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro s' _
      simp only [y', dif_pos (e s').2, Subtype.coe_eta, Equiv.symm_apply_apply]
    funext s'
    have := std_local_indep r k y' hrel (e s').1 (by simp [colSet, (e s').2])
    simpa [y', dif_pos (e s').2] using this
  by_contra hy
  exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨y, hy, hM⟩)


end

end VOA.JetProduct
