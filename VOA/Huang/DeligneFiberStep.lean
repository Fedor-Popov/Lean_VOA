/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberCrux

/-!
# Deligne's fiber functor — the Gram–Schmidt step

Given a lax braided `G` (with `ε 1 ≠ 0` and countable ranks) carrying an orthonormal `m`-family on
`X`, `m < n = symDim X`, the quotient `G' = H ⧸ (q - 1)` of the free extension
`H = A ⊗ Sym(Xᘁ ⊞ X)` by the pivot `q = ⟨f', P e'⟩` carries the orthonormal `(m+1)`-family
`(e_1, …, e_m, P e')`, `(f_1, …, f_m, f' P)`, still with `ε 1 ≠ 0` and countable ranks.

* the grading of `tensorG` (`homSub`) and `not_unit_of_homogeneous`: a homogeneous element `q`
  of degree `2` that is not nilpotent makes `q - 1` a non-unit (the inverse would be `-Σ q^j`);
* `pivotIdeal` (the ideal `(q - 1)`) and the quotient `stepG`;
* `gram_schmidt_step`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal Cardinal
open scoped TensorProduct DirectSum

universe v u

section Grading

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] (B : GCMon C)

local notation "H" => tensorG G B

/-- The homogeneous elements of degree `d`. -/
def homSub (Y : C) (d : ℕ) : Submodule ℂ (tsum G B Y) := LinearMap.range (tlof G B Y d)

/-- The degree-`d` component. -/
def compH (Y : C) (d : ℕ) : tsum G B Y →ₗ[ℂ] tcomp G B Y d := DirectSum.component ℂ ℕ (tcomp G B Y) d

theorem lof_mem_homSub {Y : C} (d : ℕ) (x : tcomp G B Y d) : tlof G B Y d x ∈ homSub G B Y d := ⟨x, rfl⟩

theorem homSub_cast {Y : C} {d d' : ℕ} (h : d = d') {x : (H).obj Y} (hx : x ∈ homSub G B Y d) :
    x ∈ homSub G B Y d' := by
  subst h; exact hx

theorem homSub_map {Y Y' : C} (f : Y ⟶ Y') {d : ℕ} {x : (H).obj Y} (hx : x ∈ homSub G B Y d) :
    ((H).map f).hom x ∈ homSub G B Y' d := by
  obtain ⟨z, rfl⟩ := hx
  erw [tensorG_map_lof]
  exact lof_mem_homSub G B d _

theorem homSub_μ {Y Z : C} {a b : ℕ} {x : (H).obj Y} {y : (H).obj Z} (hx : x ∈ homSub G B Y a)
    (hy : y ∈ homSub G B Z b) : (μ (H) Y Z).hom (x ⊗ₜ y) ∈ homSub G B (Y ⊗ Z) (a + b) := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  erw [tensorG_μ_lof]
  exact lof_mem_homSub G B _ _

theorem homSub_act {Y : C} {a b : ℕ} {r : (H).obj (𝟙_ C)} {y : (H).obj Y} (hr : r ∈ homSub G B (𝟙_ C) a)
    (hy : y ∈ homSub G B Y b) : act (H) r y ∈ homSub G B Y (a + b) :=
  homSub_map G B _ (homSub_μ G B hr hy)

theorem homSub_pairG [RightRigidCategory C] {X : C} {a b : ℕ} {g : (H).obj Xᘁ} {x : (H).obj X}
    (hg : g ∈ homSub G B Xᘁ a) (hx : x ∈ homSub G B X b) : pairG (H) g x ∈ homSub G B (𝟙_ C) (a + b) :=
  homSub_map G B _ (homSub_μ G B hg hx)

theorem compH_lof {Y : C} (d d' : ℕ) (x : tcomp G B Y d') :
    compH G B Y d (tlof G B Y d' x) = if h : d' = d then Eq.recOn h x else 0 :=
  DirectSum.component.of ℂ d d' x

theorem compH_eq_zero {Y : C} {d d' : ℕ} {x : (H).obj Y} (hx : x ∈ homSub G B Y d') (h : d' ≠ d) :
    compH G B Y d x = 0 := by
  obtain ⟨z, rfl⟩ := hx
  erw [compH_lof, dif_neg h]

theorem eq_lof_compH {Y : C} {d : ℕ} {x : (H).obj Y} (hx : x ∈ homSub G B Y d) :
    tlof G B Y d (compH G B Y d x) = x := by
  obtain ⟨z, rfl⟩ := hx
  erw [compH_lof, dif_pos rfl]

theorem exists_compH_eq_zero {Y : C} (y : (H).obj Y) : ∃ N, ∀ d, N ≤ d → compH G B Y d y = 0 := by
  classical
  refine ⟨(DFinsupp.support y).sup id + 1, fun d hd => ?_⟩
  change (show tsum G B Y from y) d = 0
  by_contra hne
  have hmem : d ∈ DFinsupp.support y := DFinsupp.mem_support_iff.2 hne
  have := Finset.le_sup (f := id) hmem
  simp at this
  omega

theorem act_neg_right' {Y : C} (r : (H).obj (𝟙_ C)) (y : (H).obj Y) : act (H) r (-y) = -act (H) r y := by
  simp [act, TensorProduct.tmul_neg]

/-- **`q - 1` is not a unit** when `q` is homogeneous of degree `2` and not nilpotent: if
`q y - y = 1` then `y_{2j} = -q^j` for all `j`, against the finite support of `y`. -/
theorem not_unit_of_homogeneous {q : (H).obj (𝟙_ C)} (hq : q ∈ homSub G B (𝟙_ C) 2)
    (hnil : ∀ k, pw G q k ≠ 0) (y : (H).obj (𝟙_ C)) : act (H) q y - y ≠ (ε (H)).hom 1 := by
  intro h
  let Lq : tsum G B (𝟙_ C) →ₗ[ℂ] tsum G B (𝟙_ C) := actLin (H) q
  have hLq : ∀ z, Lq z = act (H) q z := fun z => rfl
  have hε : (ε (H)).hom 1 ∈ homSub G B (𝟙_ C) 0 := lof_mem_homSub G B 0 _
  have hpw : ∀ k, pw G q k ∈ homSub G B (𝟙_ C) (2 * k) := by
    intro k
    induction k with
    | zero => exact hε
    | succ k ih => exact homSub_cast G B (by ring) (homSub_act G B hq ih)
  have hgen : ∀ (d' : ℕ) (w : tcomp G B (𝟙_ C) d'), Lq (tlof G B (𝟙_ C) d' w) ∈ homSub G B (𝟙_ C) (2 + d') :=
    fun d' w => homSub_act G B hq (lof_mem_homSub G B d' w)
  have hL : ∀ (z : tsum G B (𝟙_ C)) (d : ℕ),
      compH G B (𝟙_ C) (d + 2) (Lq z) = compH G B (𝟙_ C) (d + 2) (Lq (tlof G B (𝟙_ C) d (compH G B (𝟙_ C) d z))) := by
    intro z d
    induction z using DirectSum.induction_on with
    | zero => simp
    | of d' w =>
      rw [← DirectSum.lof_eq_of ℂ]
      change compH G B (𝟙_ C) (d + 2) (Lq (tlof G B (𝟙_ C) d' w)) =
        compH G B (𝟙_ C) (d + 2) (Lq (tlof G B (𝟙_ C) d (compH G B (𝟙_ C) d (tlof G B (𝟙_ C) d' w))))
      by_cases hd : d' = d
      · subst hd
        rw [compH_lof, dif_pos rfl]
      · rw [compH_lof, dif_neg hd, map_zero, map_zero, map_zero]
        exact compH_eq_zero G B (hgen d' w) (by omega)
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add, map_add, map_add]
  have hL0 : ∀ (z : tsum G B (𝟙_ C)), compH G B (𝟙_ C) 0 (Lq z) = 0 := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of d' w =>
      rw [← DirectSum.lof_eq_of ℂ]
      exact compH_eq_zero G B (hgen d' w) (by omega)
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  let yT : tsum G B (𝟙_ C) := y
  let e0 : tcomp G B (𝟙_ C) 0 := (G.map (B.ι0 (𝟙_ C))).hom ((ε G).hom 1)
  let pT : ℕ → tsum G B (𝟙_ C) := fun j => pw G q j
  have h' : Lq yT - yT = tlof G B (𝟙_ C) 0 e0 := h
  have hpT0 : pT 0 = tlof G B (𝟙_ C) 0 e0 := rfl
  have hpTs : ∀ j, Lq (pT j) = pT (j + 1) := fun j => rfl
  have hclaim : ∀ j, tlof G B (𝟙_ C) (2 * j) (compH G B (𝟙_ C) (2 * j) yT) = -pT j := by
    intro j
    induction j with
    | zero =>
      have h0 := congrArg (compH G B (𝟙_ C) 0) h'
      rw [map_sub, hL0, zero_sub, compH_lof, dif_pos rfl] at h0
      have h00 : -(compH G B (𝟙_ C) 0 yT) = e0 := h0
      have : compH G B (𝟙_ C) (2 * 0) yT = -e0 := by
        show compH G B (𝟙_ C) 0 yT = -e0
        rw [← h00, neg_neg]
      rw [this, map_neg, hpT0]
    | succ j ih =>
      have h1 := congrArg (compH G B (𝟙_ C) (2 * j + 2)) h'
      rw [map_sub, compH_lof, dif_neg (by omega), sub_eq_zero, hL, ih] at h1
      simp only [map_neg, hpTs] at h1
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, ← h1, map_neg]
      congr 1
      exact eq_lof_compH G B (homSub_cast G B (by ring) (hpw (j + 1)))
  obtain ⟨N, hN⟩ := exists_compH_eq_zero G B yT
  have := hclaim N
  rw [hN (2 * N) (by omega), map_zero, eq_comm, neg_eq_zero] at this
  exact hnil N this

end Grading

section StepMain

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  [HasKernels C] [HasBinaryBiproducts C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] [G.Linear ℂ] (X : C)

local notation "SB" => symGCMon (Xᘁ ⊞ X)
local notation "HH" => tensorG G (symGCMon (Xᘁ ⊞ X))

theorem ev'_hom : ev' G X ∈ homSub G (SB) X 1 := ⟨_, rfl⟩

theorem fv'_hom : fv' G X ∈ homSub G (SB) Xᘁ 1 := ⟨_, rfl⟩

theorem EE_hom {m : ℕ} (e : Fin m → G.obj X) (j : Fin m) : EE G X e j ∈ homSub G (SB) X 0 := ⟨_, rfl⟩

theorem FF_hom {m : ℕ} (f : Fin m → G.obj Xᘁ) (j : Fin m) : FF G X f j ∈ homSub G (SB) Xᘁ 0 := ⟨_, rfl⟩

theorem Pv_hom {m : ℕ} (e : Fin m → G.obj X) (f : Fin m → G.obj Xᘁ) :
    Pv (HH) (EE G X e) (FF G X f) (ev' G X) ∈ homSub G (SB) X 1 := by
  refine Submodule.sub_mem _ (ev'_hom G X) (Submodule.sum_mem _ fun j _ => ?_)
  have h1 := homSub_pairG G (SB) (FF_hom G X f j) (ev'_hom G X)
  have h2 := homSub_act G (SB) h1 (EE_hom G X e j)
  exact homSub_cast G (SB) (show 0 + 1 + 0 = 1 from rfl) h2

theorem qq_homogeneous {m : ℕ} (e : Fin m → G.obj X) (f : Fin m → G.obj Xᘁ) :
    qq G X e f ∈ homSub G (SB) (𝟙_ C) 2 := by
  rw [qq]
  exact homSub_cast G (SB) (show 1 + 1 = 2 from rfl) (homSub_pairG G (SB) (fv'_hom G X) (Pv_hom G X e f))

/-- The ideal `(q - 1)` (range of the action of `q - 1`). -/
def pivotIdeal (q : (HH).obj (𝟙_ C)) : LaxIdeal (HH) where
  I Y := LinearMap.range (actLin (HH) (q - (ε (HH)).hom 1) : (HH).obj Y →ₗ[ℂ] (HH).obj Y)
  map_mem {Y Y'} f y hy := by
    obtain ⟨z, rfl⟩ := hy
    exact ⟨((HH).map f).hom z, (act_natural (HH) f _ z).symm⟩
  mul_mem_left Y Z y z hz := by
    obtain ⟨w, rfl⟩ := hz
    exact ⟨(μ (HH) Y Z).hom (y ⊗ₜ w), (μ_act_right (HH) _ y w).symm⟩
  mul_mem_right Y Z y z hy := by
    obtain ⟨w, rfl⟩ := hy
    exact ⟨(μ (HH) Y Z).hom (w ⊗ₜ z), (μ_act_left (HH) _ w z).symm⟩

/-- **The Gram–Schmidt step.**  An orthonormal `m`-family (`m < n = symDim X`) over a lax braided
`G` with `ε 1 ≠ 0` and countable ranks extends to an orthonormal `(m+1)`-family over
`G' = (A ⊗ Sym(Xᘁ ⊞ X)) ⧸ (q - 1)`, again with `ε 1 ≠ 0` and countable ranks. -/
theorem gram_schmidt_step {n m : ℕ} (htr : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (n : ℂ) • 𝟙 (𝟙_ C))
    (hmn : m < n) (hne : (ε G).hom 1 ≠ 0) (hrank : ∀ Y, Module.rank ℂ (G.obj Y) ≤ ℵ₀)
    (e : Fin m → G.obj X) (f : Fin m → G.obj Xᘁ)
    (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0) :
    ∃ (G' : C ⥤ ModuleCat.{0} ℂ) (_ : G'.LaxBraided) (_ : G'.Additive) (_ : G'.Linear ℂ)
      (e' : Fin (m + 1) → G'.obj X) (f' : Fin (m + 1) → G'.obj Xᘁ),
      (ε G').hom 1 ≠ 0 ∧ (∀ Y, Module.rank ℂ (G'.obj Y) ≤ ℵ₀) ∧
      ∀ i j, pairG G' (f' i) (e' j) = if i = j then (ε G').hom 1 else 0 := by
  set q := qq G X e f with hqdef
  set J := pivotIdeal G X q with hJ
  have horthH := orthoH G X e f horth
  let mkX : (HH).obj X → J.quot.obj X := fun x => (Submodule.Quotient.mk x : (HH).obj X ⧸ J.I X)
  let mkD : (HH).obj Xᘁ → J.quot.obj Xᘁ := fun g => (Submodule.Quotient.mk g : (HH).obj Xᘁ ⧸ J.I Xᘁ)
  let mk1 : (HH).obj (𝟙_ C) → J.quot.obj (𝟙_ C) := fun r => (Submodule.Quotient.mk r : (HH).obj (𝟙_ C) ⧸ J.I (𝟙_ C))
  have hpair : ∀ (g : (HH).obj Xᘁ) (x : (HH).obj X), pairG J.quot (mkD g) (mkX x) = mk1 (pairG (HH) g x) :=
    fun g x => rfl
  have hε1 : (ε J.quot).hom 1 = mk1 ((ε (HH)).hom 1) := rfl
  have hq1 : mk1 q = mk1 ((ε (HH)).hom 1) := by
    refine (Submodule.Quotient.eq _).2 ⟨(ε (HH)).hom 1, ?_⟩
    rw [actLin_apply, act_unit_right]
  have h0 : mk1 0 = 0 := rfl
  refine ⟨J.quot, inferInstance, inferInstance, inferInstance,
    Fin.snoc (fun j => mkX (EE G X e j)) (mkX (Pv (HH) (EE G X e) (FF G X f) (ev' G X))),
    Fin.snoc (fun j => mkD (FF G X f j)) (mkD (Pc (HH) (EE G X e) (FF G X f) (fv' G X))), ?_, ?_, ?_⟩
  · intro hz
    have hz' : (Submodule.Quotient.mk ((ε (HH)).hom 1) : (HH).obj (𝟙_ C) ⧸ J.I (𝟙_ C)) = 0 := hz
    rw [Submodule.Quotient.mk_eq_zero] at hz'
    obtain ⟨y, hy⟩ := hz'
    apply not_unit_of_homogeneous G (SB) (qq_homogeneous G X e f) (pw_ne_zero G X e f htr hmn horth hne) y
    rw [← hy, actLin_apply, act_sub_left, act_unit]
  · intro Y
    exact (rank_quotient_le _).trans (rank_tensorG_le G (SB) (fun k => hrank _))
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, if_true]
      rw [hpair, pairG_Pc_Pv (HH) _ _ horthH]
      change mk1 q = _
      rw [hq1, hε1]
    · simp only [Fin.snoc_last, Fin.snoc_castSucc, if_neg (Fin.castSucc_ne_last j).symm]
      rw [hpair, pairG_Pc_E (HH) _ _ horthH, h0]
    · simp only [Fin.snoc_last, Fin.snoc_castSucc, if_neg (Fin.castSucc_ne_last i)]
      rw [hpair, pairG_Pv (HH) _ _ horthH, h0]
    · simp only [Fin.snoc_castSucc, Fin.castSucc_inj]
      rw [hpair, horthH]
      split_ifs
      · exact hε1.symm
      · exact h0

end StepMain

end VOA.Huang.TensorCat.DeligneFiber
