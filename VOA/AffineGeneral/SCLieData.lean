/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SCLie
import VOA.AffineGeneral.LieData
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# `LieData` for a structure-constant algebra from a sparse form table

For a checked table `T` (`SCLie.Alg N T hc`) and a sparse symmetric matrix `Gm` (entries `(i, j, g)`), `formG`
is the bilinear form `κ(x, y) = Σ g · xᵢ yⱼ`.

* `formG_symm_of`: symmetry from a Boolean check on `Gm`;
* `skew_of_basis_check`: `ad b_a` is `κ`-skew (`κ(⁅a,y⁆,z) + κ(y,⁅a,z⁆) = 0`) from a Boolean check over basis `y`;
* `skew_of_bracket`: skewness passes from `a`, `b` to `c` when `⁅b_a, b_b⁆ = κ b_c` (Leibniz);
* `isInvariant_of_skew`: skewness for every basis vector gives `κ.IsInvariant`;
* `lieDataOf`: `LieData` with explicit dual vectors `(1/Dⱼ) · vec dⱼ` and the Casimir `2h`, both from checks.

All the checks are finite computations on sparse lists, decided by kernel reduction for a concrete algebra.
-/

namespace VOA.AffineGeneral.SCLie

noncomputable section

variable {N : ℕ} {T : Table} (hc : Checks N T)

/-- `Σ g · coef l₁ i · coef l₂ j` over a sparse matrix. -/
def formV (Gm : List (ℕ × ℕ × ℤ)) (l₁ l₂ : List (ℕ × ℤ)) : ℤ :=
  (Gm.map fun t => t.2.2 * coef l₁ t.1 * coef l₂ t.2.1).sum

/-- All indices of `Gm` are `< N`. -/
def gInRange (N : ℕ) (Gm : List (ℕ × ℕ × ℤ)) : Bool := Gm.all fun t => t.1 < N && t.2.1 < N

/-! ## Quadratic singular-vector checks (used in `SCSingular`) -/

/-- The weight-one vector of `J^x_1 t` (as a sparse vector). -/
def q1Vec {N : ℕ} (T : Table) (Gm : List (ℕ × ℕ × ℤ)) (k : ℤ) (tz : List (ℤ × Fin N × Fin N)) (x : ℕ) :
    List (ℕ × ℤ) :=
  tz.flatMap fun t => scale t.1 ((t.2.1.val, k * formV Gm [(x, 1)] [(t.2.2.val, 1)]) ::
    (t.2.2.val, k * formV Gm [(x, 1)] [(t.2.1.val, 1)]) :: brL T (entry T x t.2.1.val) [(t.2.2.val, 1)])

/-- All weight-one coefficients vanish. -/
def q1OK {N : ℕ} (T : Table) (Gm : List (ℕ × ℕ × ℤ)) (k : ℤ) (tz : List (ℤ × Fin N × Fin N)) : Bool :=
  (List.range N).all fun x => (tz.all fun t => inRange N (entry T x t.2.1.val)) &&
    (List.range N).all fun g => coef (q1Vec T Gm k tz x) g == 0

/-- All vacuum coefficients vanish. -/
def q2OK {N : ℕ} (T : Table) (Gm : List (ℕ × ℕ × ℤ)) (k : ℤ) (tz : List (ℤ × Fin N × Fin N)) : Bool :=
  (List.range N).all fun x =>
    (tz.map fun t => t.1 * (k * formV Gm (entry T x t.2.1.val) [(t.2.2.val, 1)])).sum == 0

/-- The complex terms of `tz`. -/
def termsC {N : ℕ} (tz : List (ℤ × Fin N × Fin N)) : List (ℂ × Fin N × Fin N) :=
  tz.map fun t => ((t.1 : ℂ), t.2)

/-- One term `g · xᵢ yⱼ` of a sparse form. -/
def formTerm (t : ℕ × ℕ × ℤ) : LinearMap.BilinForm ℂ (Alg N T hc) :=
  if h : t.1 < N ∧ t.2.1 < N then
    (t.2.2 : ℂ) • (LinearMap.mul ℂ ℂ).compl₁₂ (coordL hc ⟨t.1, h.1⟩) (coordL hc ⟨t.2.1, h.2⟩)
  else 0

/-- The bilinear form of a sparse matrix. -/
def formG (Gm : List (ℕ × ℕ × ℤ)) : LinearMap.BilinForm ℂ (Alg N T hc) := (Gm.map (formTerm hc)).sum

theorem formG_apply (Gm : List (ℕ × ℕ × ℤ)) (x y : Alg N T hc) :
    formG hc Gm x y = (Gm.map fun t => formTerm hc t x y).sum := by
  induction Gm with
  | nil => simp [formG]
  | cons t l ih => simp [formG, ih] at ih ⊢

theorem formG_vec (Gm : List (ℕ × ℕ × ℤ)) (hG : gInRange N Gm = true) (l₁ l₂ : List (ℕ × ℤ)) :
    formG hc Gm (vec hc l₁) (vec hc l₂) = (formV Gm l₁ l₂ : ℂ) := by
  rw [formG_apply, formV, Int.cast_list_sum, List.map_map]
  congr 1; apply List.map_congr_left; intro t ht
  have h := List.all_eq_true.mp hG t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [formTerm, dif_pos h, Function.comp_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', coordL_apply, smul_eq_mul]
  push_cast
  simp only [vec]
  ring

/-! ## Boolean checks -/

/-- Symmetry of the form on basis vectors. -/
def symmOK (N : ℕ) (Gm : List (ℕ × ℕ × ℤ)) : Bool :=
  (List.range N).all fun i => (List.range N).all fun j =>
    formV Gm [(i, 1)] [(j, 1)] == formV Gm [(j, 1)] [(i, 1)]

/-- `ad b_a` is skew on basis vectors. -/
def skewOK (T : Table) (N : ℕ) (Gm : List (ℕ × ℕ × ℤ)) (a : ℕ) : Bool :=
  (List.range N).all fun y => (List.range N).all fun z =>
    formV Gm (entry T a y) [(z, 1)] + formV Gm [(y, 1)] (entry T a z) == 0

/-- Symmetry of a sparse matrix: its transpose is a permutation of it. -/
def symmPerm (Gm : List (ℕ × ℕ × ℤ)) : Bool := (Gm.map fun t => (t.2.1, t.1, t.2.2)).isPerm Gm

/-- The column `z` of a sparse matrix, as `(row, value)` pairs. -/
def col (Gm : List (ℕ × ℕ × ℤ)) (z : ℕ) : List (ℕ × ℤ) :=
  (Gm.filter fun t => t.2.1 == z).map fun t => (t.1, t.2.2)

/-- `Σ g · l_w` over a column. -/
def colV (c l : List (ℕ × ℤ)) : ℤ := (c.map fun p => p.2 * coef l p.1).sum

/-- `ad b_a` is skew, using a precomputed column table `gc` (cheap in the kernel). -/
def skewOK2 (T : Table) (N : ℕ) (gc : List (List (ℕ × ℤ))) (a : ℕ) : Bool :=
  (List.range N).all fun y => (List.range N).all fun z =>
    colV (gc.getD z []) (entry T a y) + colV (gc.getD y []) (entry T a z) == 0

theorem formV_single_right (Gm : List (ℕ × ℕ × ℤ)) (l : List (ℕ × ℤ)) (z : ℕ) :
    formV Gm l [(z, 1)] = colV (col Gm z) l := by
  induction Gm with
  | nil => rfl
  | cons t Gm ih =>
    simp only [formV, col, colV, List.map_cons, List.sum_cons, List.filter_cons] at ih ⊢
    rw [ih]
    by_cases h : t.2.1 = z
    · simp [h, coef]
    · simp [h, coef, Ne.symm h]

theorem formV_comm (Gm : List (ℕ × ℕ × ℤ)) (h : symmPerm Gm = true) (l₁ l₂ : List (ℕ × ℤ)) :
    formV Gm l₁ l₂ = formV Gm l₂ l₁ := by
  have hp : (Gm.map fun t => (t.2.1, t.1, t.2.2)).Perm Gm := List.isPerm_iff.mp h
  rw [formV, formV, ← (hp.map (fun t => t.2.2 * coef l₂ t.1 * coef l₁ t.2.1)).sum_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp]
  ring

theorem skewOK_of_2 (T : Table) (N : ℕ) (Gm : List (ℕ × ℕ × ℤ)) (hs : symmPerm Gm = true)
    (gc : List (List (ℕ × ℤ))) (hgc : gc = (List.range N).map (col Gm)) (a : ℕ)
    (h : skewOK2 T N gc a = true) : skewOK T N Gm a = true := by
  have hget : ∀ z < N, gc.getD z [] = col Gm z := by
    intro z hz; subst hgc; simp [List.getD_eq_getElem?_getD, hz]
  simp only [skewOK, skewOK2, List.all_eq_true, List.mem_range, beq_iff_eq] at h ⊢
  intro y hy z hz
  rw [formV_comm Gm hs [(y, 1)], formV_single_right, formV_single_right, ← hget z hz, ← hget y hy]
  exact h y hy z hz

/-! ## Symmetry and skewness -/

variable (Gm : List (ℕ × ℕ × ℤ)) (hG : gInRange N Gm = true)
include hG

theorem formG_basis (i j : Fin N) :
    formG hc Gm (basis hc i) (basis hc j) = (formV Gm [((i : ℕ), 1)] [((j : ℕ), 1)] : ℂ) := by
  rw [basis_eq_vec, basis_eq_vec, formG_vec hc Gm hG]

theorem formG_symm (h : symmOK N Gm = true) (x y : Alg N T hc) : formG hc Gm x y = formG hc Gm y x := by
  have : formG hc Gm = (formG hc Gm).flip := by
    refine LinearMap.ext_basis (basis hc) (basis hc) fun i j => ?_
    rw [LinearMap.BilinForm.flip_apply, formG_basis hc Gm hG, formG_basis hc Gm hG]
    have := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr i.2)) j (List.mem_range.mpr j.2)
    simp only [beq_iff_eq] at this
    rw [this]
  exact congrArg (fun F : LinearMap.BilinForm ℂ (Alg N T hc) => F x y) this

/-- `ad a` is `κ`-skew. -/
def Skew (a : Alg N T hc) : Prop :=
  ∀ y z : Alg N T hc, formG hc Gm ⁅a, y⁆ z + formG hc Gm y ⁅a, z⁆ = 0

omit hG in
theorem skew_smul {a : Alg N T hc} (h : Skew hc Gm a) (c : ℂ) : Skew hc Gm (c • a) := by
  intro y z
  rw [smul_lie, smul_lie, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add,
    h y z, mul_zero]

omit hG in
theorem skew_add {a b : Alg N T hc} (ha : Skew hc Gm a) (hb : Skew hc Gm b) : Skew hc Gm (a + b) := by
  intro y z
  rw [add_lie, add_lie, map_add, LinearMap.add_apply, map_add]
  linear_combination ha y z + hb y z

theorem skew_basis_of_check (a : Fin N) (h : skewOK T N Gm a = true) : Skew hc Gm (basis hc a) := by
  -- the bilinear map `(y, z) ↦ κ(⁅a,y⁆, z) + κ(y, ⁅a,z⁆)` vanishes on the basis
  have hb : (formG hc Gm).compl₁₂ (B hc (basis hc a)) LinearMap.id
      + (formG hc Gm).compl₂ (B hc (basis hc a)) = 0 := by
    refine LinearMap.ext_basis (basis hc) (basis hc) fun y z => ?_
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearMap.compl₂_apply,
      LinearMap.zero_apply]
    have hy := List.all_eq_true.mp (List.all_eq_true.mp h y (List.mem_range.mpr y.2)) z
      (List.mem_range.mpr z.2)
    simp only [beq_iff_eq] at hy
    have e1 : B hc (basis hc a) (basis hc y) = vec hc (entry T a y) := by
      rw [← lie_def, basis_eq_vec, basis_eq_vec,
        lie_vec hc (by simp [inRange]) (by simp [inRange])]
      funext k
      simp [vec, brL, coef_flatMap, coef_scale]
    have e2 : B hc (basis hc a) (basis hc z) = vec hc (entry T a z) := by
      rw [← lie_def, basis_eq_vec, basis_eq_vec,
        lie_vec hc (by simp [inRange]) (by simp [inRange])]
      funext k
      simp [vec, brL, coef_flatMap, coef_scale]
    rw [e1, e2, basis_eq_vec, basis_eq_vec, formG_vec hc Gm hG, formG_vec hc Gm hG]
    exact_mod_cast hy
  intro y z
  have := congrArg (fun F : LinearMap.BilinForm ℂ (Alg N T hc) => F y z) hb
  simpa [lie_def] using this

omit hG in
/-- **Skewness passes along a bracket** (Leibniz). -/
theorem skew_lie {a b : Alg N T hc} (ha : Skew hc Gm a) (hb : Skew hc Gm b) : Skew hc Gm ⁅a, b⁆ := by
  intro y z
  have l1 : ⁅⁅a, b⁆, y⁆ = ⁅a, ⁅b, y⁆⁆ - ⁅b, ⁅a, y⁆⁆ := by rw [leibniz_lie]; abel
  have l2 : ⁅⁅a, b⁆, z⁆ = ⁅a, ⁅b, z⁆⁆ - ⁅b, ⁅a, z⁆⁆ := by rw [leibniz_lie]; abel
  rw [l1, l2, map_sub, LinearMap.sub_apply, map_sub]
  have h1 := ha ⁅b, y⁆ z
  have h2 := hb ⁅a, y⁆ z
  have h3 := ha y ⁅b, z⁆
  have h4 := hb y ⁅a, z⁆
  linear_combination h1 - h2 + h3 - h4

omit hG in
theorem formTerm_swap (t : ℕ × ℕ × ℤ) (x y : Alg N T hc) :
    formTerm hc (t.2.1, t.1, t.2.2) x y = formTerm hc t y x := by
  unfold formTerm
  by_cases h : t.1 < N ∧ t.2.1 < N
  · rw [dif_pos ⟨h.2, h.1⟩, dif_pos h]
    simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', smul_eq_mul]
    ring
  · rw [dif_neg (fun h' => h ⟨h'.2, h'.1⟩), dif_neg h]; simp

omit hG in
theorem formG_symm' (h : symmPerm Gm = true) (x y : Alg N T hc) : formG hc Gm x y = formG hc Gm y x := by
  have hp : (Gm.map fun t => (t.2.1, t.1, t.2.2)).Perm Gm := List.isPerm_iff.mp h
  rw [formG_apply, formG_apply, ← (hp.map (fun t => formTerm hc t x y)).sum_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  exact formTerm_swap hc t x y

/-- Skewness for every basis vector gives `κ.IsInvariant` (with symmetry). -/
theorem isInvariant_of_skew (hs : symmPerm Gm = true) (hsk : ∀ c : Fin N, Skew hc Gm (basis hc c)) :
    (formG hc Gm).IsInvariant := by
  have hall : ∀ a : Alg N T hc, Skew hc Gm a := by
    intro a
    have ha : a ∈ Submodule.span ℂ (Set.range (basis hc)) := by rw [(basis hc).span_eq]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact hsk c
    | zero => intro y z; simp
    | add x y _ _ hx hy => exact skew_add hc Gm hx hy
    | smul c x _ hx => exact skew_smul hc Gm hx c
  refine ⟨formG_symm' hc Gm hs, fun x y z => ?_⟩
  have h := hall y x z
  rw [← lie_skew, map_neg, LinearMap.neg_apply] at h
  linear_combination -h


omit hG in
/-- A single-term table entry gives `⁅b_a, b_b⁆ = κ b_c`. -/
theorem lie_basis_of_entry {a b c : Fin N} {κ : ℤ} (h : entry T a b = [((c : ℕ), κ)]) :
    ⁅basis hc a, basis hc b⁆ = (κ : ℂ) • basis hc c := by
  rw [basis_eq_vec, basis_eq_vec, lie_vec hc (by simp [inRange]) (by simp [inRange]), basis_eq_vec]
  funext k
  change (coef (brL T [((a : ℕ), 1)] [((b : ℕ), 1)]) k : ℂ) = (κ : ℂ) * (coef [((c : ℕ), 1)] k : ℂ)
  simp [brL, coef_flatMap, coef_scale, h, coef_cons]

omit hG in
/-- Skewness along a single-term bracket. -/
theorem skew_of_entry {a b c : Fin N} {κ : ℤ} (hκ : κ ≠ 0) (h : entry T a b = [((c : ℕ), κ)])
    (ha : Skew hc Gm (basis hc a)) (hb : Skew hc Gm (basis hc b)) : Skew hc Gm (basis hc c) := by
  have e := lie_basis_of_entry hc h
  have : basis hc c = ((κ : ℂ))⁻¹ • ⁅basis hc a, basis hc b⁆ := by
    rw [e, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hκ), one_smul]
  rw [this]
  exact skew_smul hc Gm (skew_lie hc Gm ha hb) _


/-! ## Dual family, Casimir, `LieData` -/

omit hG in
/-- The dual vectors `(1/Dⱼ) · vec dⱼ`. -/
def dualV (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) (j : Fin N) : Alg N T hc := ((D j : ℂ)⁻¹) • vec hc (dl j)

/-- `κ(bᵢ, vec dⱼ) = δᵢⱼ Dⱼ`, `Dⱼ ≠ 0`, indices in range. -/
def pairOK (N : ℕ) (Gm : List (ℕ × ℕ × ℤ)) (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) : Bool :=
  (List.range N).all fun j => decide (D j ≠ 0) && inRange N (dl j) &&
    (List.range N).all fun i => formV Gm [(i, 1)] (dl j) == if i = j then D j else 0

/-- Pairing checks for the dual vectors `lo ≤ j < hi`. -/
def pairChunk (N : ℕ) (Gm : List (ℕ × ℕ × ℤ)) (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun j => decide (D j ≠ 0) && inRange N (dl j) &&
    (List.range N).all fun i => formV Gm [(i, 1)] (dl j) == if i = j then D j else 0

omit hG in
theorem pairOK_of_chunks (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ)
    (h : ∀ j, j < N → ∃ lo hi, lo ≤ j ∧ j < hi ∧ pairChunk N Gm dl D lo hi = true) : pairOK N Gm dl D = true := by
  unfold pairOK
  refine List.all_eq_true.mpr fun j hj => ?_
  obtain ⟨lo, hi, h1, h2, hc'⟩ := h j (List.mem_range.mp hj)
  unfold pairChunk at hc'
  exact List.all_eq_true.mp hc' j (List.mem_range'_1.mpr ⟨h1, by omega⟩)
theorem pair_of_check (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) (h : pairOK N Gm dl D = true) (i j : Fin N) :
    formG hc Gm (basis hc i) (dualV hc dl D j) = if i = j then 1 else 0 := by
  have hj := List.all_eq_true.mp h j (List.mem_range.mpr j.2)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  obtain ⟨⟨hD, _⟩, hi⟩ := hj
  have hij := List.all_eq_true.mp hi i (List.mem_range.mpr i.2)
  simp only [beq_iff_eq] at hij
  rw [dualV, map_smul, basis_eq_vec, formG_vec hc Gm hG, hij, smul_eq_mul]
  by_cases e : i = j
  · subst e; simp [hD]
  · have : (i : ℕ) ≠ j := fun h' => e (Fin.ext h')
    simp [e, this]

omit hG in
/-- The Casimir check at a basis vector `x`: `Σᵢ (L/Dᵢ)·⁅bᵢ, ⁅vec dᵢ, bₓ⁆⁆ = c·L·bₓ`. -/
def casOK (T : Table) (N : ℕ) (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) (L c : ℤ) (x : ℕ) : Bool :=
  (List.finRange N).all (fun i => decide ((D i : ℤ) ∣ L) && inRange N (brL T (dl i) [(x, 1)])) &&
    zeroL ((List.finRange N).flatMap (fun i : Fin N => scale (L / D (i : ℕ)) (brL T [((i : ℕ), 1)]
      (brL T (dl (i : ℕ)) [(x, 1)]))) ++
      scale (-(c * L)) [(x, 1)])

omit hG in
theorem vec_append' (l₁ l₂ : List (ℕ × ℤ)) : vec hc (l₁ ++ l₂) = vec hc l₁ + vec hc l₂ := by
  funext k
  change (coef (l₁ ++ l₂) k : ℂ) = (coef l₁ k : ℂ) + (coef l₂ k : ℂ)
  rw [coef_append]; push_cast; rfl

omit hG in
theorem vec_scale' (c : ℤ) (l : List (ℕ × ℤ)) : vec hc (scale c l) = (c : ℂ) • vec hc l := by
  funext k
  change (coef (scale c l) k : ℂ) = (c : ℂ) * (coef l k : ℂ)
  rw [coef_scale]; push_cast; rfl

omit hG in
theorem vec_flatMap_finRange (g : Fin N → List (ℕ × ℤ)) :
    vec hc ((List.finRange N).flatMap g) = ∑ i, vec hc (g i) := by
  rw [Fin.sum_univ_def]
  induction (List.finRange N) with
  | nil => funext k; change (coef [] k : ℂ) = 0; simp
  | cons a l ih => rw [List.flatMap_cons, vec_append', ih, List.map_cons, List.sum_cons]

theorem casimir_basis (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) (hp : pairOK N Gm dl D = true) (L c : ℤ)
    (hL : L ≠ 0) (x : Fin N) (h : casOK T N dl D L c x = true) :
    ∑ i, ⁅basis hc i, ⁅dualV hc dl D i, basis hc x⁆⁆ = (c : ℂ) • basis hc x := by
  simp only [casOK, Bool.and_eq_true] at h
  obtain ⟨hdiv, hz⟩ := h
  have hterm : ∀ i : Fin N, ⁅basis hc i, ⁅dualV hc dl D i, basis hc x⁆⁆
      = (L : ℂ)⁻¹ • vec hc (scale (L / D i) (brL T [((i : ℕ), 1)] (brL T (dl i) [((x : ℕ), 1)]))) := by
    intro i
    have hi := List.all_eq_true.mp hdiv i (List.mem_finRange i)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    have hpj := List.all_eq_true.mp hp i (List.mem_range.mpr i.2)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpj
    rw [dualV, smul_lie, basis_eq_vec hc x, lie_vec hc hpj.1.2 (by simp [inRange]), lie_smul, basis_eq_vec hc i,
      lie_vec hc (by simp [inRange]) hi.2, vec_scale', smul_smul]
    congr 1
    obtain ⟨q, hq⟩ := hi.1
    have hD0 : D i ≠ 0 := hpj.1.1
    have hD : (D i : ℂ) ≠ 0 := by exact_mod_cast hD0
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    have hq0 : q ≠ 0 := by rintro rfl; apply hL; rw [hq, mul_zero]
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    rw [hq, Int.mul_ediv_cancel_left _ hD0]
    push_cast
    field_simp
  simp only [hterm, ← Finset.smul_sum]
  rw [← vec_flatMap_finRange hc (fun i : Fin N => scale (L / D i) (brL T [((i : ℕ), 1)] (brL T (dl i) [((x : ℕ), 1)]))),
    vec_eq_of_zeroL hc (c * L) hz, ← basis_eq_vec, smul_smul]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  congr 1
  push_cast
  field_simp

/-- **`LieData` from sparse tables.** -/
def lieDataOf (hs : symmPerm Gm = true) (hsk : ∀ c : Fin N, Skew hc Gm (basis hc c))
    (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) (hp : pairOK N Gm dl D = true) (L c : ℤ) (hL : L ≠ 0)
    (hcas : ∀ x : Fin N, casOK T N dl D L c x = true) : LieData (formG hc Gm) (Fin N) where
  invariant := isInvariant_of_skew hc Gm hG hs hsk
  basis := basis hc
  dual := dualV hc dl D
  pair := pair_of_check hc Gm hG dl D hp
  h := (c : ℂ) / 2
  casimir x := by
    have hlin : (∑ i, (B hc (basis hc i)).comp (B hc (dualV hc dl D i))) = (c : ℂ) • LinearMap.id := by
      refine (basis hc).ext fun x => ?_
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      have := casimir_basis hc Gm hG dl D hp L c hL x (hcas x)
      simpa [lie_def] using this
    have := congrArg (fun F : Alg N T hc →ₗ[ℂ] Alg N T hc => F x) hlin
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at this
    rw [show 2 * ((c : ℂ) / 2) = c by ring]
    simpa [lie_def] using this


end

end VOA.AffineGeneral.SCLie

