/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelKoszul
import VOA.Examples.ConcreteGoodGrading

/-!
# The leading Koszul bicomplex is the antighost-count block decomposition of `Q⁻`

`GrLeadKoszulData C n r` (`SymbolModelKoszul`) asks for an *arbitrary* `LeadingBicomplex` and a
`LeadModel` identifying it with the leading complex of `C` at `(2r, 0)`. On the actual relative
complex the bicomplex is not extra data: the antighost number (number of `b` creation modes)
splits every bigraded piece, and the two components of `Q⁻` on these blocks are `d_K` (lowering
the antighost number by one) and `d_CE` (preserving it). This file proves that, for **any**
Kähler complex carrying such a block decomposition,

* the bicomplex `KoszulBlocks.bicomplex` whose four diagonals are the actual blocks and whose six
  components are the block components of the actual `Q⁻` satisfies every relation of
  `(d_K + d_CE)² = 0` (`rel_YZ`, `rel_YY`, `rel_KK`, `rel_XG`, `rel_CC` all derived from
  `Q⁻² = 0`), once Koszul exactness of the actual `d_K` rows is given (`KExact`);
* `KoszulBlocks.leadModel` — the `LeadModel` identifying `C.deg a` with the product
  totalization is **proved** (projections onto the blocks), with no further input;
* `KoszulBlocks.toGrLeadKoszulData` — `GrLeadKoszulData C n r` follows from the blocks, Koszul
  exactness, and the two *symbol maps* `π₀`, `π₁` (`KoszulSymbolMaps`): `π₀` on the block of
  antighost number `0` at `(2r, 0)` with kernel exactly `d_K`-boundaries, `π₁` on the block of
  antighost number `0` at `(2r + 1, 1)` with kernel exactly `d_K`-boundaries, intertwining
  `d_CE` with the diagonal positive-mode action.

Index convention of the blocks: `((2R, gh), q)`, `q` the antighost number. The hypotheses of
`KoszulBlocks` are: internal direct sum, refinement of `C.deg`, no negative antighost or ghost
counts (`q ≥ 0`, `gh + q ≥ 0`), and the *shape* of the total differential: `D` changes the
antighost number by `0` or `-1`.

Everything here is proved outright from the listed hypotheses.
-/

namespace VOA.KoszulConcrete

open VOA.GradedUnitaryCohomology VOA.LeadingKoszul VOA.ConcreteHodge
open scoped DirectSum

noncomputable section

/-! ### The bigrading of a Kähler complex is internal -/

section Deg

variable {K : Type*} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)

theorem P_iSup_right {ι : Sort*} (S : ι → Submodule ℂ K) (x : K)
    (h : ∀ i, ∀ y ∈ S i, C.P x y = 0) : ∀ y ∈ iSup S, C.P x y = 0 := by
  intro y hy
  refine Submodule.iSup_induction S (motive := fun y => C.P x y = 0) hy h
    (SesqForm.zero_right _ x) ?_
  intro y y' h1 h2
  rw [C.P.add_right, h1, h2, add_zero]

/-- The bigraded pieces of a Kähler complex are independent (orthogonality + positivity). -/
theorem deg_iSupIndep : iSupIndep C.deg := by
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply C.eq_zero_of_self
  refine P_iSup_right C _ x (fun b y hy => ?_) x hx'
  refine P_iSup_right C _ x (fun hb z hz => ?_) y hy
  exact C.orth a b (Ne.symm hb) x hx z hz

/-- The bigrading of a Kähler complex is an internal direct sum. -/
theorem deg_isInternal : DirectSum.IsInternal C.deg :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (deg_iSupIndep C) C.span

end Deg

/-! ### Antighost-count blocks -/

/-- **Antighost-count blocks of a Kähler complex.** `blk ((2R, gh), q)` is the part of
`C.deg (2R, gh)` with `q` antighost (`b`) creation modes. -/
structure KoszulBlocks {K : Type*} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K) where
  blk : (ℤ × ℤ) × ℤ → Submodule ℂ K
  indep : iSupIndep blk
  span : iSup blk = ⊤
  le_deg : ∀ a q, blk (a, q) ≤ C.deg a
  /-- No negative antighost number. -/
  neg : ∀ a q, q < 0 → blk (a, q) = ⊥
  /-- No negative ghost (`c`) number: `#c = gh + #b ≥ 0`. -/
  cneg : ∀ a q, a.2 + q < 0 → blk (a, q) = ⊥
  /-- **Shape of the total differential**: it changes the antighost number by `0` or `-1`. -/
  shape : ∀ i, ∀ x ∈ blk i, C.D x ∈ ⨆ (j : (ℤ × ℤ) × ℤ) (_ : j.2 = i.2 ∨ j.2 + 1 = i.2), blk j

namespace KoszulBlocks

variable {K : Type*} [AddCommGroup K] [Module ℂ K] {C : KahlerComplex K} (B : KoszulBlocks C)

/-- The blocks form an internal direct sum. -/
theorem internal : DirectSum.IsInternal B.blk :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top B.indep B.span

/-- The projection onto a block. -/
abbrev pr (i : (ℤ × ℤ) × ℤ) : K →ₗ[ℂ] K := iproj B.internal i

theorem pr_mem (i : (ℤ × ℤ) × ℤ) (x : K) : B.pr i x ∈ B.blk i := iproj_mem _ i x

theorem pr_of_mem {i : (ℤ × ℤ) × ℤ} {x : K} (hx : x ∈ B.blk i) : B.pr i x = x :=
  iproj_of_mem_same _ hx

theorem pr_of_mem_ne {i j : (ℤ × ℤ) × ℤ} (h : j ≠ i) {x : K} (hx : x ∈ B.blk j) :
    B.pr i x = 0 :=
  iproj_of_mem_ne _ h hx

theorem pr_pr_ne {i j : (ℤ × ℤ) × ℤ} (h : j ≠ i) (x : K) : B.pr i (B.pr j x) = 0 :=
  B.pr_of_mem_ne h (B.pr_mem j x)

theorem eq_zero_of_pr {x : K} (h : ∀ i, B.pr i x = 0) : x = 0 := by
  obtain ⟨s, hs⟩ := sum_iproj B.internal x
  rw [← hs]
  exact Finset.sum_eq_zero fun i _ => h i

theorem pr_eq_zero_of_bot {i : (ℤ × ℤ) × ℤ} (h : B.blk i = ⊥) (x : K) : B.pr i x = 0 := by
  have := B.pr_mem i x
  rwa [h, Submodule.mem_bot] at this

/-- A vector of `C.deg b` has no component in a block of another bidegree. -/
theorem pr_deg_ne {b : ℤ × ℤ} {x : K} (hx : x ∈ C.deg b) {i : (ℤ × ℤ) × ℤ} (hi : i.1 ≠ b) :
    B.pr i x = 0 :=
  iproj_eq_zero_of_weight B.internal (deg_isInternal C) Prod.fst
    (fun i => B.le_deg i.1 i.2) hx hi

/-- Components of `D x` outside the two admissible antighost numbers vanish. -/
theorem pr_D_eq_zero {i : (ℤ × ℤ) × ℤ} {x : K} (hx : x ∈ B.blk i) {j : (ℤ × ℤ) × ℤ}
    (h1 : j.2 ≠ i.2) (h2 : j.2 + 1 ≠ i.2) : B.pr j (C.D x) = 0 := by
  have hD := B.shape i x hx
  refine Submodule.iSup_induction _ (motive := fun y => B.pr j y = 0) hD ?_ (map_zero _)
    (fun y y' hy hy' => by beta_reduce at hy hy' ⊢; rw [map_add, hy, hy', add_zero])
  intro j' y hy
  refine Submodule.iSup_induction _ (motive := fun y => B.pr j y = 0) hy ?_ (map_zero _)
    (fun y y' hy hy' => by beta_reduce at hy hy' ⊢; rw [map_add, hy, hy', add_zero])
  intro hj' z hz
  refine B.pr_of_mem_ne ?_ hz
  rintro rfl
  rcases hj' with h | h
  · exact h1 h
  · exact h2 h

/-- On a block of bidegree `a`, the `(a + shQm)`-components of `Q⁻` and of `D` agree. -/
theorem pr_Qm_eq_pr_D {a : ℤ × ℤ} {x : K} (hx : x ∈ C.deg a) (q : ℤ) :
    B.pr (a + shQm, q) (C.Qm x) = B.pr (a + shQm, q) (C.D x) := by
  have hS : B.pr (a + shQm, q) (C.Sm x) = 0 :=
    B.pr_deg_ne (C.Sm_deg a x hx) (by
      intro h
      have := congrArg Prod.fst h
      simp only [Prod.fst_add] at this
      omega)
  change _ = B.pr (a + shQm, q) ((C.Qm + C.Sm) x)
  rw [LinearMap.add_apply, map_add, hS, add_zero]

/-- **Components of `Q⁻` on a block.** Only the two antighost numbers `q` and `q - 1` of the
bidegree `a + shQm` occur. -/
theorem pr_Qm_eq_zero {a : ℤ × ℤ} {q : ℤ} {x : K} (hx : x ∈ B.blk (a, q)) {j : (ℤ × ℤ) × ℤ}
    (h : j.1 ≠ a + shQm ∨ (j.2 ≠ q ∧ j.2 + 1 ≠ q)) : B.pr j (C.Qm x) = 0 := by
  have hxa := B.le_deg a q hx
  rcases h with h | ⟨h1, h2⟩
  · exact B.pr_deg_ne (C.Qm_deg a x hxa) h
  · by_cases hj : j.1 = a + shQm
    · obtain ⟨j1, j2⟩ := j
      simp only at hj
      subst hj
      rw [B.pr_Qm_eq_pr_D hxa]
      exact B.pr_D_eq_zero hx h1 h2
    · exact B.pr_deg_ne (C.Qm_deg a x hxa) hj

/-- **`Q⁻` on a block is the sum of its two block components.** -/
theorem Qm_split {a b : ℤ × ℤ} (hb : b = a + shQm) {q : ℤ} {x : K} (hx : x ∈ B.blk (a, q)) :
    C.Qm x = B.pr (b, q) (C.Qm x) + B.pr (b, q - 1) (C.Qm x) := by
  subst hb
  have hne : ((a + shQm, q - 1) : (ℤ × ℤ) × ℤ) ≠ (a + shQm, q) := by
    intro h; have := congrArg Prod.snd h; simp at this
  rw [← sub_eq_zero, sub_add_eq_sub_sub]
  refine B.eq_zero_of_pr fun j => ?_
  rw [map_sub, map_sub]
  by_cases h1 : j = (a + shQm, q)
  · subst h1
    rw [B.pr_of_mem (B.pr_mem _ _), B.pr_pr_ne hne, sub_self, sub_zero]
  · by_cases h2 : j = (a + shQm, q - 1)
    · subst h2
      rw [B.pr_of_mem (B.pr_mem _ _), B.pr_pr_ne (Ne.symm hne), sub_zero, sub_self]
    · rw [B.pr_pr_ne (Ne.symm h1), B.pr_pr_ne (Ne.symm h2), sub_zero, sub_zero]
      refine B.pr_Qm_eq_zero hx ?_
      by_cases hj : j.1 = a + shQm
      · right
        obtain ⟨j1, j2⟩ := j
        simp only at hj
        subst hj
        refine ⟨fun e => h1 (by simp only at e; rw [e]), fun e => h2 ?_⟩
        rw [show j2 = q - 1 by omega]
      · left; exact hj

/-- **Components of `Q⁻` on a whole bigraded piece**: the `q`-component of `Q⁻ x` only sees the
`q` and `q + 1` components of `x`. -/
theorem pr_Qm_deg {a b : ℤ × ℤ} (hb : b = a + shQm) {x : K} (hx : x ∈ C.deg a) (q : ℤ) :
    B.pr (b, q) (C.Qm x) =
      B.pr (b, q) (C.Qm (B.pr (a, q) x)) + B.pr (b, q) (C.Qm (B.pr (a, q + 1) x)) := by
  set z := x - B.pr (a, q) x - B.pr (a, q + 1) x with hz
  have hne : ((a, q + 1) : (ℤ × ℤ) × ℤ) ≠ (a, q) := by
    intro h; have := congrArg Prod.snd h; simp at this
  have hzj : ∀ j, j = (a, q) ∨ j = (a, q + 1) ∨ j.1 ≠ a → B.pr j z = 0 := by
    intro j hj
    rw [hz, map_sub, map_sub]
    rcases hj with rfl | rfl | hj
    · rw [B.pr_of_mem (B.pr_mem _ _), B.pr_pr_ne hne, sub_self, sub_zero]
    · rw [B.pr_of_mem (B.pr_mem _ _), B.pr_pr_ne (Ne.symm hne), sub_zero, sub_self]
    · rw [B.pr_deg_ne hx hj, B.pr_deg_ne (B.le_deg _ _ (B.pr_mem _ _)) hj,
        B.pr_deg_ne (B.le_deg _ _ (B.pr_mem _ _)) hj, sub_zero, sub_zero]
  have hQz : B.pr (b, q) (C.Qm z) = 0 := by
    obtain ⟨s, hs⟩ := sum_iproj B.internal z
    rw [← hs, map_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = (a, q) ∨ j = (a, q + 1) ∨ j.1 ≠ a
    · change B.pr (b, q) (C.Qm (B.pr j z)) = 0
      rw [hzj j hj, map_zero, map_zero]
    · push Not at hj
      obtain ⟨h1, h2, h3⟩ := hj
      obtain ⟨j1, j2⟩ := j
      simp only at h3
      subst h3
      refine B.pr_Qm_eq_zero (B.pr_mem _ z) (j := (b, q)) (Or.inr ⟨?_, ?_⟩)
      · intro e; exact h1 (by simp only at e; rw [e])
      · intro e; exact h2 (by simp only at e; rw [← e])
  have hx' : x = z + B.pr (a, q) x + B.pr (a, q + 1) x := by rw [hz]; abel
  conv_lhs => rw [hx']
  rw [map_add, map_add, map_add, map_add, hQz, zero_add]

/-! ### The bicomplex of block components -/

/-- The block component `blk (a, q) → blk (b, q')` of `Q⁻`. -/
def comp (a b : ℤ × ℤ) (q q' : ℤ) : B.blk (a, q) →ₗ[ℂ] B.blk (b, q') :=
  (B.pr (b, q') ∘ₗ C.Qm ∘ₗ (B.blk (a, q)).subtype).codRestrict _ fun _ => B.pr_mem _ _

@[simp] theorem comp_coe (a b : ℤ × ℤ) (q q' : ℤ) (x : B.blk (a, q)) :
    (B.comp a b q q' x : K) = B.pr (b, q') (C.Qm x) := rfl

variable (a : ℤ × ℤ)

/-- The four diagonals: `X p = blk (a, p)`. -/
abbrev XB (p : ℕ) : Type _ := B.blk (a, (p : ℤ))
/-- `Y p = blk (a - shQm, p + 1)`. -/
abbrev YB (p : ℕ) : Type _ := B.blk (a - shQm, ((p + 1 : ℕ) : ℤ))
/-- `Z p = blk (a + shQm, p)`. -/
abbrev ZB (p : ℕ) : Type _ := B.blk (a + shQm, (p : ℤ))
/-- `G p = blk (a + shQm + shQm, p)`. -/
abbrev GB (p : ℕ) : Type _ := B.blk (a + shQm + shQm, (p : ℤ))

theorem a_sub_add : a - shQm + shQm = a := by abel

/-- **Koszul exactness of the actual `d_K` at the bidegree `a`, antighost number `p + 1`**: a
`d_K`-cycle is a `d_K`-boundary from the bidegree `b = a - shQm` below. -/
def KExactAt (b a : ℤ × ℤ) (p : ℕ) : Prop :=
  ∀ x : B.blk (a, ((p + 1 : ℕ) : ℤ)), B.comp a (a + shQm) _ (p : ℤ) x = 0 →
    ∃ y : B.blk (b, ((p + 1 + 1 : ℕ) : ℤ)), B.comp b a _ ((p + 1 : ℕ) : ℤ) y = x

/-- Koszul exactness in positive antighost number, at ghost numbers `0` and `+1` above `a`. -/
def KExact : Prop := ∀ p : ℕ, B.KExactAt (a - shQm) a p ∧ B.KExactAt a (a + shQm) p

theorem cast_succ_sub_one (p : ℕ) : ((p + 1 : ℕ) : ℤ) - 1 = (p : ℤ) := by push_cast; ring

/-- `Q⁻²` on a block, through its two components. -/
theorem pr_Qm_Qm_split {a' b : ℤ × ℤ} (hb : b = a' + shQm) (c : ℤ × ℤ) {q : ℤ} {x : K}
    (hx : x ∈ B.blk (a', q)) (q' : ℤ) :
    B.pr (c, q') (C.Qm (B.pr (b, q) (C.Qm x))) + B.pr (c, q') (C.Qm (B.pr (b, q - 1) (C.Qm x)))
      = 0 := by
  rw [← map_add, ← map_add, ← B.Qm_split hb hx, C.Qm_sq, map_zero]

/-- **The bicomplex of block components of `Q⁻`**, Koszul exactness supplied by `hK`. -/
def bicomplex (hK : B.KExact a) :
    LeadingBicomplex ℂ (B.XB a) (B.YB a) (B.ZB a) (B.GB a) where
  dKY p := B.comp (a - shQm) a _ _
  dCEY p := B.comp (a - shQm) a _ _
  dKX p := B.comp a (a + shQm) _ _
  dCEX p := B.comp a (a + shQm) _ _
  dKZ p := B.comp (a + shQm) (a + shQm + shQm) _ _
  dCEZ p := B.comp (a + shQm) (a + shQm + shQm) _ _
  rel_YZ p y := by
    apply Subtype.ext
    simp only [comp_coe, Submodule.coe_add, Submodule.coe_zero]
    have h := B.pr_Qm_Qm_split (a_sub_add a).symm (a + shQm) y.2 (p : ℤ)
    rw [cast_succ_sub_one] at h
    rw [add_comm]; exact h
  rel_YY p y := by
    apply Subtype.ext
    simp only [comp_coe, Submodule.coe_zero]
    have h := B.pr_Qm_Qm_split (a_sub_add a).symm (a + shQm) y.2 (((p + 1 : ℕ) : ℤ))
    rw [cast_succ_sub_one] at h
    have h0 : B.pr (a + shQm, ((p + 1 : ℕ) : ℤ)) (C.Qm (B.pr (a, (p : ℤ)) (C.Qm y))) = 0 :=
      B.pr_Qm_eq_zero (B.pr_mem _ _) (Or.inr ⟨by push_cast; omega, by push_cast; omega⟩)
    rw [h0, add_zero] at h
    exact h
  rel_KK p y := by
    apply Subtype.ext
    simp only [comp_coe, Submodule.coe_zero]
    have h := B.pr_Qm_Qm_split (a_sub_add a).symm (a + shQm) y.2 (p : ℤ)
    rw [cast_succ_sub_one] at h
    have h0 : B.pr (a + shQm, (p : ℤ)) (C.Qm (B.pr (a, ((p + 1 + 1 : ℕ) : ℤ)) (C.Qm y))) = 0 :=
      B.pr_Qm_eq_zero (B.pr_mem _ _) (Or.inr ⟨by push_cast; omega, by push_cast; omega⟩)
    rw [h0, zero_add] at h
    exact h
  rel_XG p x := by
    apply Subtype.ext
    simp only [comp_coe, Submodule.coe_add, Submodule.coe_zero]
    have h := B.pr_Qm_Qm_split rfl (a + shQm + shQm) x.2 (p : ℤ)
    rw [cast_succ_sub_one] at h
    exact h
  rel_CC p x := by
    apply Subtype.ext
    simp only [comp_coe, Submodule.coe_zero]
    have h := B.pr_Qm_Qm_split rfl (a + shQm + shQm) x.2 (p : ℤ)
    have h0 : B.pr (a + shQm + shQm, (p : ℤ))
        (C.Qm (B.pr (a + shQm, (p : ℤ) - 1) (C.Qm x))) = 0 :=
      B.pr_Qm_eq_zero (B.pr_mem _ _) (Or.inr ⟨by omega, by omega⟩)
    rw [h0, add_zero] at h
    exact h
  exact_X p x hx := (hK p).1 x hx
  exact_Z p z hz := (hK p).2 z hz

/-! ### The `LeadModel` -/

/-- The block components of a vector of `C.deg b`, as a product. -/
def toPi (b : ℤ × ℤ) (s : ℕ → ℤ) : C.deg b →ₗ[ℂ] (∀ p : ℕ, B.blk (b, s p)) :=
  LinearMap.pi fun p =>
    (B.pr (b, s p) ∘ₗ (C.deg b).subtype).codRestrict _ fun _ => B.pr_mem _ _

@[simp] theorem toPi_coe (b : ℤ × ℤ) (s : ℕ → ℤ) (x : C.deg b) (p : ℕ) :
    (B.toPi b s x p : K) = B.pr (b, s p) x := rfl

/-- If every block of bidegree `b` not listed by `s` vanishes, `toPi` is injective. -/
theorem toPi_injective (b : ℤ × ℤ) (s : ℕ → ℤ)
    (hs : ∀ q, (∀ p, s p ≠ q) → B.blk (b, q) = ⊥) : Function.Injective (B.toPi b s) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  refine B.eq_zero_of_pr fun j => ?_
  obtain ⟨j1, j2⟩ := j
  by_cases hj : j1 = b
  · subst hj
    by_cases hq : ∃ p, s p = j2
    · obtain ⟨p, rfl⟩ := hq
      have := congrArg (fun f => (f p : K)) hx
      simpa using this
    · push Not at hq
      exact B.pr_eq_zero_of_bot (hs j2 hq) _
  · exact B.pr_deg_ne x.2 hj

/-- If moreover `s` is injective and only finitely many blocks of bidegree `b` are nonzero,
`toPi` is surjective. -/
theorem toPi_surjective [FiniteDimensional ℂ K] (b : ℤ × ℤ) (s : ℕ → ℤ)
    (hinj : Function.Injective s) : Function.Surjective (B.toPi b s) := by
  classical
  intro f
  have hfin : {i | B.blk i ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep B.internal.submodule_iSupIndep
  set T : Set ℕ := {p | B.blk (b, s p) ≠ ⊥} with hT
  have hTfin : T.Finite :=
    (hfin.preimage (f := fun p => (b, s p)) (by
      intro p _ p' _ h
      exact hinj (congrArg Prod.snd h)))
  set x : K := ∑ p ∈ hTfin.toFinset, (f p : K) with hx
  have hxmem : x ∈ C.deg b :=
    Submodule.sum_mem _ fun p _ => B.le_deg b _ (f p).2
  refine ⟨⟨x, hxmem⟩, ?_⟩
  funext p
  apply Subtype.ext
  rw [toPi_coe]
  change B.pr (b, s p) x = _
  rw [hx, map_sum]
  by_cases hp : p ∈ hTfin.toFinset
  · rw [Finset.sum_eq_single p]
    · exact B.pr_of_mem (f p).2
    · intro p' _ hp'
      exact B.pr_of_mem_ne (fun e => hp' (hinj (congrArg Prod.snd e))) (f p').2
    · intro h; exact absurd hp h
  · have hbot : B.blk (b, s p) = ⊥ := by
      by_contra h
      exact hp (hTfin.mem_toFinset.mpr h)
    have hf : (f p : K) = 0 := by
      have h1 : (f p : K) ∈ B.blk (b, s p) := (f p).2
      have h2 : B.blk (b, s p) ≤ ⊥ := hbot.le
      exact (Submodule.mem_bot ℂ).mp (h2 h1)
    rw [hf]
    refine Finset.sum_eq_zero fun p' hp' => ?_
    have hne : p' ≠ p := fun e => hp (e ▸ hp')
    exact B.pr_of_mem_ne (fun e => hne (hinj (congrArg Prod.snd e))) (f p').2

section LM

variable [FiniteDimensional ℂ K]

/-- **The `LeadModel` of the block bicomplex: proved.** -/
def leadModel (hK : B.KExact a) (ha : a.2 = 0) : LeadModel C (B.bicomplex a hK) a where
  eX := LinearEquiv.ofBijective (B.toPi a fun p => (p : ℤ))
    ⟨B.toPi_injective a _ (fun q hq => B.neg a q (by
        by_contra h; push Not at h
        exact hq q.toNat (Int.toNat_of_nonneg h))),
      B.toPi_surjective a _ (fun p p' h => by exact_mod_cast h)⟩
  eY := LinearEquiv.ofBijective (B.toPi (a - shQm) fun p => ((p + 1 : ℕ) : ℤ))
    ⟨B.toPi_injective (a - shQm) _ (fun q hq => by
        rcases lt_trichotomy q 0 with h | rfl | h
        · exact B.neg _ q h
        · exact B.cneg _ 0 (by simp [ha])
        · exfalso
          apply hq (q - 1).toNat
          push_cast
          omega),
      B.toPi_surjective (a - shQm) _ (fun p p' h => by
        have : ((p + 1 : ℕ) : ℤ) = ((p' + 1 : ℕ) : ℤ) := h
        omega)⟩
  eZ := B.toPi (a + shQm) fun p => (p : ℤ)
  eZ_inj := B.toPi_injective (a + shQm) _ (fun q hq => B.neg _ q (by
    by_contra h; push Not at h
    exact hq q.toNat (Int.toNat_of_nonneg h)))
  hQX x h := by
    funext p
    apply Subtype.ext
    simp only [toPi_coe, LeadingBicomplex.D0_apply, Submodule.coe_add,
      LinearEquiv.ofBijective_apply]
    change B.pr (a + shQm, (p : ℤ)) (C.Qm x) =
      B.pr (a + shQm, (p : ℤ)) (C.Qm (B.pr (a, (p : ℤ)) x)) +
        B.pr (a + shQm, (p : ℤ)) (C.Qm (B.pr (a, ((p + 1 : ℕ) : ℤ)) x))
    rw [B.pr_Qm_deg rfl x.2]
    push_cast; rfl
  hQY y h := by
    funext p
    apply Subtype.ext
    rcases p with _ | p
    · simp only [LinearEquiv.ofBijective_apply, toPi_coe, LeadingBicomplex.Dm_zero]
      change B.pr (a, ((0 : ℕ) : ℤ)) (C.Qm y) =
        B.pr (a, ((0 : ℕ) : ℤ)) (C.Qm (B.pr (a - shQm, ((0 + 1 : ℕ) : ℤ)) y))
      rw [B.pr_Qm_deg (a_sub_add a).symm y.2]
      have h0 : B.pr (a - shQm, ((0 : ℕ) : ℤ)) (y : K) = 0 :=
        B.pr_eq_zero_of_bot (B.cneg _ _ (by simp [ha])) _
      rw [h0, map_zero, map_zero, zero_add]
      rfl
    · simp only [LinearEquiv.ofBijective_apply, toPi_coe, LeadingBicomplex.Dm_succ,
        Submodule.coe_add]
      change B.pr (a, ((p + 1 : ℕ) : ℤ)) (C.Qm y) =
        B.pr (a, ((p + 1 : ℕ) : ℤ)) (C.Qm (B.pr (a - shQm, ((p + 1 + 1 : ℕ) : ℤ)) y)) +
          B.pr (a, ((p + 1 : ℕ) : ℤ)) (C.Qm (B.pr (a - shQm, ((p + 1 : ℕ) : ℤ)) y))
      rw [B.pr_Qm_deg (a_sub_add a).symm y.2, add_comm]
      push_cast; rfl

end LM

/-! ### Koszul `H₀` through symbol maps -/

/-- **Symbol maps on the two Koszul rows** of the block bicomplex at `a`: `π₀` on the
antighost-free block of `a`, with kernel exactly the `d_K`-boundaries; `π₁` on the antighost-free
block of `a + shQm` into `κ → M`, with kernel exactly the `d_K`-boundaries; and `π₁ ∘ d_CE`
equal to the family `ρ k ∘ π₀`. -/
structure KoszulSymbolMaps (M : Type*) [AddCommGroup M] [Module ℂ M] {κ : Type*}
    (ρ : κ → M →ₗ[ℂ] M) where
  π0 : B.blk (a, ((0 : ℕ) : ℤ)) →ₗ[ℂ] M
  ker_π0 : LinearMap.ker π0 = LinearMap.range (B.comp (a - shQm) a ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ))
  π1 : B.blk (a + shQm, ((0 : ℕ) : ℤ)) →ₗ[ℂ] (κ → M)
  ker_π1 : LinearMap.ker π1 = LinearMap.range (B.comp a (a + shQm) ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ))
  intertwine : ∀ x k, π1 (B.comp a (a + shQm) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) x) k = ρ k (π0 x)

variable {a}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {κ : Type*} {ρ : κ → M →ₗ[ℂ] M}

/-- Koszul `H₀` of row `0` is the range of `π₀`. -/
def KoszulSymbolMaps.e0 (hK : B.KExact a) (S : B.KoszulSymbolMaps a M ρ) :
    (B.bicomplex a hK).KH0 ≃ₗ[ℂ] LinearMap.range S.π0 :=
  (Submodule.quotEquivOfEq _ _ S.ker_π0.symm).trans S.π0.quotKerEquivRange

theorem KoszulSymbolMaps.e0_mk (hK : B.KExact a) (S : B.KoszulSymbolMaps a M ρ)
    (x : B.blk (a, ((0 : ℕ) : ℤ))) :
    (S.e0 B hK (Submodule.Quotient.mk x) : M) = S.π0 x := rfl

/-- Koszul `H₀` of row `1` embeds through `π₁`. -/
def KoszulSymbolMaps.e1 (hK : B.KExact a) (S : B.KoszulSymbolMaps a M ρ) :
    (B.bicomplex a hK).KH1 →ₗ[ℂ] (κ → M) :=
  (LinearMap.range (B.comp a (a + shQm) ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ))).liftQ S.π1
    S.ker_π1.ge

theorem KoszulSymbolMaps.e1_injective (hK : B.KExact a) (S : B.KoszulSymbolMaps a M ρ) :
    Function.Injective (S.e1 B hK) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ S.ker_π1.le

theorem KoszulSymbolMaps.intertwine_dbar (hK : B.KExact a) (S : B.KoszulSymbolMaps a M ρ)
    (v : (B.bicomplex a hK).KH0) (k : κ) :
    S.e1 B hK ((B.bicomplex a hK).dbar v) k = ρ k ((S.e0 B hK v : M)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [LeadingBicomplex.dbar_mk, S.e0_mk]
  exact S.intertwine x k

/-- **`H⁰(Q⁻)` at `a` is the joint kernel of `ρ` on the range of `π₀`**, from the blocks,
Koszul exactness and the symbol maps. -/
def leadCohomEquivJointKer [FiniteDimensional ℂ K] (hK : B.KExact a) (ha : a.2 = 0)
    (S : B.KoszulSymbolMaps a M ρ) :
    C.leadCohom a ≃ₗ[ℂ] VOA.SymbolModel.jointKer
      (fun k => ρ k ∘ₗ (LinearMap.range S.π0).subtype) :=
  VOA.SymbolModel.leadCohomEquivJointKer (B.leadModel a hK ha) (S.e0 B hK) (S.e1 B hK)
    (S.e1_injective B hK) _ (fun v k => S.intertwine_dbar B hK v k)

end KoszulBlocks

/-! ### Specialization: the concrete Koszul data -/

section Concrete

open VOA.SymbolModel VOA.InvariantSymbol VOA.CyclicEval Sl2CosetConcrete
open scoped TensorProduct

variable {K : Type} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K] {C : KahlerComplex K}

/-- **`GrLeadKoszulData` from the antighost-count blocks.** The bicomplex and the `LeadModel`
are the actual block components of `Q⁻` (proved); only Koszul exactness `hK` and the symbol maps
`S` (with weight condition `hw`) are inputs. -/
def grLeadKoszulData_of_blocks (n : ℤ) (r : ℕ) (B : KoszulBlocks C)
    (hK : B.KExact (2 * (r : ℤ), 0))
    (S : B.KoszulSymbolMaps (2 * (r : ℤ), 0) (GrA r ⊗[ℂ] BSpace) (grDiag r))
    (hw : ∀ x, S.π0 x ∈ tensorWeight (grDeg r) bWeight n) : GrLeadKoszulData C n r where
  X := B.XB (2 * (r : ℤ), 0)
  Y := B.YB (2 * (r : ℤ), 0)
  Z := B.ZB (2 * (r : ℤ), 0)
  G := B.GB (2 * (r : ℤ), 0)
  Bc := B.bicomplex _ hK
  LM := B.leadModel _ hK rfl
  N0 := LinearMap.range S.π0
  e0 := S.e0 B hK
  j := (LinearMap.range S.π0).subtype
  j_injective := Subtype.val_injective
  j_weight y := by
    obtain ⟨x, hx⟩ := y.2
    rw [Submodule.subtype_apply, ← hx]
    exact hw x
  e1 := S.e1 B hK
  e1_injective := S.e1_injective B hK
  intertwine v k := S.intertwine_dbar B hK v k

end Concrete

end

end VOA.KoszulConcrete
