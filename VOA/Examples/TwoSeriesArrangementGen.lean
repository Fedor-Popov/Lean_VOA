/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArrangementSym

/-!
# Block-Vandermonde alternant generators of `W_n`

The `n = 2` proof (`JetPoincareVdm`) writes every element of `I_2 ∩ L` through the alternants
`dD pt m = det(x_{pt p}^0, …, x_{pt p}^{r-1}, x_{pt p}^m)` (`m ≥ N`) times the complementary pair
factors, and shows those products lie in `W` by Laplace expansion along the `m`-column.  The same
mechanism works for every `n` with **block** Vandermonde products: for a labelling
`c : Fin k → Fin (n - 1)` of the points by `n - 1` blocks and a strictly increasing point list
`pt` inside one block,

  `G(c, pt, m) = blockProd c pt · dD pt m`,

where `blockProd c pt` is the product of `x_b - x_a` over the pairs `a < b` in a common block that
are not both in `pt`.  Laplace expansion gives `G = Σ_p ± x_{pt p}^m · blockProd · Δ(pt \ pt p)`,
and each cofactor vanishes on every `n`-fold diagonal avoiding `pt p` (pigeonhole: `n` points in
`n - 1` blocks share a block).

* `vanishOn_of_dvd` — divisibility by `x_b - x_a` with `a ≠ b` in `S` gives `VanishOn S`;
* `mul_mem_Wn` — `W_n` is an ideal;
* `mul_dD_mem_Wn` — **the Laplace step**: `C · dD pt m ∈ W_n` (`m ≥ N`) as soon as every
  cofactor `C · Δ(pt \ pt p)` vanishes on the `n`-fold diagonals avoiding `pt p`;
* `blockProd_mul_dD_mem_Wn` — the block generators lie in `W_n`;
* `GenInclusion n` — `I_n ∩ L ⊆ (block generators)` (an ideal-generation statement; numerically an
  **equality**, with suffix point lists already sufficing — numerical evidence, not a proof);
* `arrangementInclusion_of_genInclusion` — **`GenInclusion n → ArrangementInclusion n`**, and
  `symArrangementInclusion_of_genInclusion`;
* `genInclusion_two` — **`GenInclusion 2`** (the `JetPoincareVdm` division argument, with one
  block, lands in the ideal of the block generators), so the input is the correct generalization.

Everything is proved outright; `GenInclusion n` (`n ≥ 3`) is an open named input, alternative to
(and stronger than) `ArrangementInclusion n`.
-/

namespace VOA.TwoSeries.ArrangementGen

open MvPolynomial Finset JetPoincareVdm JetPoincareArr

noncomputable section

variable {k : ℕ}

/-! ### Vanishing and the ideal property of `W_n` -/

theorem vanishOn_mul_left {S : Finset (Fin k)} {Y : XP k} (g : XP k) (hY : VanishOn S Y) :
    VanishOn S (g * Y) := by
  intro s₀ hs₀
  rw [map_mul, hY s₀ hs₀, mul_zero]

/-- Divisibility by a pair factor inside `S` forces vanishing on the diagonal of `S`. -/
theorem vanishOn_of_dvd {S : Finset (Fin k)} {a b : Fin k} (ha : a ∈ S) (hb : b ∈ S)
    {Y : XP k} (h : (X b - X a : XP k) ∣ Y) : VanishOn S Y := by
  obtain ⟨u, rfl⟩ := h
  intro s₀ _
  rw [map_mul, map_sub, rename_X, rename_X]
  simp [collapseTo, ha, hb]

/-- `W_n` is closed under multiplication by polynomials. -/
theorem mul_mem_Wn {N n : ℕ} (g : XP k) {w : XP k} (hw : w ∈ Wn k N n) : g * w ∈ Wn k N n := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, Y, hY, rfl⟩ := hx
    refine Submodule.subset_span ⟨l, g * Y, fun S hS hlS => vanishOn_mul_left g (hY S hS hlS), ?_⟩
    ring
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-! ### The Laplace step -/

variable {r : ℕ}

/-- **The Laplace step.** If every cofactor `C · Δ(pt \ pt p)` vanishes on the `n`-fold
diagonals avoiding `pt p`, then `C · dD pt m ∈ W_n` for `m ≥ N`. -/
theorem mul_dD_mem_Wn {n N m : ℕ} (hm : N ≤ m) (pt : Fin (r + 1) → Fin k) (C : XP k)
    (hC : ∀ p : Fin (r + 1), ∀ S : Finset (Fin k), #S = n → pt p ∉ S →
      VanishOn S (C * vdm (fun p' => pt (p.succAbove p')))) :
    C * dD pt m ∈ Wn k N n := by
  rw [dD_laplace, mul_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  refine Submodule.subset_span ⟨pt p, X (pt p) ^ (m - N) * ((-1) ^ ((p : ℕ) + r) *
    (C * vdm (fun p' => pt (p.succAbove p')))), fun S hS hpS => ?_, ?_⟩
  · exact vanishOn_mul_left _ (vanishOn_mul_left _ (hC p S hS hpS))
  · rw [dT]
    have h : (X (pt p) ^ m : XP k) = X (pt p) ^ N * X (pt p) ^ (m - N) := by
      rw [← pow_add, Nat.add_sub_cancel' hm]
    rw [h]; ring

/-! ### Block generators -/

/-- The pair factors `x_b - x_a` (`a < b`, same block) that are not both in the point list. -/
def blockPairs {M : ℕ} (c : Fin k → Fin M) (pt : Fin (r + 1) → Fin k) : Finset (Fin k × Fin k) :=
  univ.filter fun q => q.1 < q.2 ∧ c q.1 = c q.2 ∧ ¬ (q.1 ∈ univ.image pt ∧ q.2 ∈ univ.image pt)

/-- The complementary block-Vandermonde factor. -/
def blockProd {M : ℕ} (c : Fin k → Fin M) (pt : Fin (r + 1) → Fin k) : XP k :=
  pprod (blockPairs c pt)

theorem dvd_vdm_succAbove (pt : Fin (r + 1) → Fin k) (p : Fin (r + 1))
    {x y : Fin (r + 1)} (hxy : x < y) (hxp : x ≠ p) (hyp : y ≠ p) :
    (X (pt y) - X (pt x) : XP k) ∣ vdm (fun p' => pt (p.succAbove p')) := by
  obtain ⟨x', rfl⟩ := Fin.exists_succAbove_eq hxp
  obtain ⟨y', rfl⟩ := Fin.exists_succAbove_eq hyp
  have hlt : x' < y' := (Fin.strictMono_succAbove p).lt_iff_lt.mp hxy
  rw [vdm]
  exact dvd_trans (dvd_prod_of_mem
    (fun q => (X (pt (p.succAbove q)) - X (pt (p.succAbove x')) : XP k)) (mem_Ioi.mpr hlt))
    (dvd_prod_of_mem (fun p'' => ∏ q ∈ Ioi p'',
      (X (pt (p.succAbove q)) - X (pt (p.succAbove p'')) : XP k)) (mem_univ x'))

/-- The cofactors of the block generators vanish on the `n`-fold diagonals avoiding the expanded
point (pigeonhole over the `n - 1` blocks). -/
theorem blockProd_cofactor_vanish {n : ℕ} (hn : 2 ≤ n) (c : Fin k → Fin (n - 1))
    {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) (p : Fin (r + 1)) (S : Finset (Fin k))
    (hS : #S = n) (hpS : pt p ∉ S) :
    VanishOn S (blockProd c pt * vdm (fun p' => pt (p.succAbove p'))) := by
  have hlt : (univ : Finset (Fin (n - 1))).card < S.card := by
    rw [card_univ, Fintype.card_fin, hS]; omega
  obtain ⟨a, ha, b, hb, hab, hcab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun x _ => mem_univ (c x))
  -- order the pair
  wlog hlt' : a < b generalizing a b
  · exact this b hb a ha hab.symm hcab.symm (lt_of_le_of_ne (not_lt.mp hlt') hab.symm)
  by_cases hboth : a ∈ univ.image pt ∧ b ∈ univ.image pt
  · obtain ⟨x, -, hx⟩ := mem_image.mp hboth.1
    obtain ⟨y, -, hy⟩ := mem_image.mp hboth.2
    have hxy : x < y := hpt.lt_iff_lt.mp (hx ▸ hy ▸ hlt')
    have hxp : x ≠ p := fun h => hpS (h ▸ hx ▸ ha)
    have hyp : y ≠ p := fun h => hpS (h ▸ hy ▸ hb)
    have hd := dvd_vdm_succAbove pt p hxy hxp hyp
    rw [hx, hy] at hd
    exact vanishOn_of_dvd ha hb (dvd_mul_of_dvd_right hd _)
  · have hmem : (a, b) ∈ blockPairs c pt := by
      simp only [blockPairs, mem_filter, mem_univ, true_and]
      exact ⟨hlt', hcab, hboth⟩
    refine vanishOn_of_dvd ha hb (dvd_mul_of_dvd_left ?_ _)
    have hd : (X (a, b).2 - X (a, b).1 : XP k) ∣ ∏ q ∈ blockPairs c pt, (X q.2 - X q.1 : XP k) :=
      Finset.dvd_prod_of_mem (fun q : Fin k × Fin k => (X q.2 - X q.1 : XP k)) hmem
    exact hd

/-- **The block generators lie in `W_n`.** -/
theorem blockProd_mul_dD_mem_Wn {n N m : ℕ} (hn : 2 ≤ n) (hm : N ≤ m) (c : Fin k → Fin (n - 1))
    {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) :
    blockProd c pt * dD pt m ∈ Wn k N n :=
  mul_dD_mem_Wn hm pt _ fun p S hS hpS => blockProd_cofactor_vanish hn c hpt p S hS hpS

/-- The block generators: a labelling `c` by `n - 1` blocks, a strictly increasing point list
inside one block, and a power `m ≥ N`. -/
def genSet (n k N : ℕ) : Set (XP k) :=
  {g | ∃ (c : Fin k → Fin (n - 1)) (r : ℕ) (pt : Fin (r + 1) → Fin k) (m : ℕ),
    StrictMono pt ∧ (∀ p, c (pt p) = c (pt 0)) ∧ N ≤ m ∧ g = blockProd c pt * dD pt m}

/-- **The generation input**: every polynomial in `L` vanishing on the `n`-fold diagonals lies in
the ideal generated by the block generators. -/
def GenInclusion (n : ℕ) : Prop :=
  ∀ (k N : ℕ) (f : XP k), f ∈ Lid k N → (∀ S : Finset (Fin k), #S = n → VanishOn S f) →
    f ∈ Ideal.span (genSet n k N)

theorem span_genSet_le_Wn {n N : ℕ} (hn : 2 ≤ n) {f : XP k} (hf : f ∈ Ideal.span (genSet n k N)) :
    f ∈ Wn k N n := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, r, pt, m, hpt, -, hm, rfl⟩ := hx
    exact blockProd_mul_dD_mem_Wn hn hm c hpt
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_eq_mul]; exact mul_mem_Wn a hx

/-- **The generation input implies the arrangement inclusion.** -/
theorem arrangementInclusion_of_genInclusion {n : ℕ} (hn : 2 ≤ n) (h : GenInclusion n) :
    ArrangementInclusion n :=
  fun k N f _ hL hV => span_genSet_le_Wn hn (h k N f hL hV)

/-- … hence the narrowed input of the endpoint. -/
theorem symArrangementInclusion_of_genInclusion {n : ℕ} (hn : 2 ≤ n) (h : GenInclusion n) :
    ArrangementSym.SymArrangementInclusion n :=
  ArrangementSym.symArrangementInclusion_of_arrangementInclusion
    (arrangementInclusion_of_genInclusion hn h)

theorem Wn_le_Lid {n N : ℕ} {w : XP k} (hw : w ∈ Wn k N n) : w ∈ Lid k N := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, Y, -, rfl⟩ := hx
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨l, rfl⟩)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_of_tower_mem _ c hx

/-! ### `n = 2`: the generation input holds -/

theorem blockPairs_const {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt) :
    blockPairs (fun _ => (0 : Fin 1)) pt = vpairs (id : Fin k → Fin k) \ vpairs pt := by
  ext q
  rw [blockPairs, mem_filter, mem_sdiff, mem_vpairs, mem_vpairs]
  constructor
  · rintro ⟨-, hlt, -, hnot⟩
    refine ⟨⟨q.1, q.2, hlt, rfl, rfl⟩, ?_⟩
    rintro ⟨x, y, -, hx, hy⟩
    exact hnot ⟨mem_image.mpr ⟨x, mem_univ _, hx⟩, mem_image.mpr ⟨y, mem_univ _, hy⟩⟩
  · rintro ⟨⟨a, b, hab, ha, hb⟩, hnot⟩
    refine ⟨mem_univ _, ?_, rfl, ?_⟩
    · rw [← ha, ← hb]; exact hab
    · rintro ⟨h1, h2⟩
      obtain ⟨x, -, hx⟩ := mem_image.mp h1
      obtain ⟨y, -, hy⟩ := mem_image.mp h2
      refine hnot ⟨x, y, hpt.lt_iff_lt.mp ?_, hx, hy⟩
      rw [hx, hy, ← ha, ← hb]; exact hab

theorem vdm_mul_mem_span_genSet_two {N m : ℕ} (hm : N ≤ m) {pt : Fin (r + 1) → Fin k}
    (hpt : StrictMono pt) {G : XP k} (hG : dD pt m = vdm pt * G) :
    vdm (id : Fin k → Fin k) * G ∈ Ideal.span (genSet 2 k N) := by
  refine Ideal.subset_span ⟨fun _ => 0, r, pt, m, hpt, fun _ => rfl, hm, ?_⟩
  rw [blockProd, blockPairs_const hpt, ← Rfac, vdm_id_eq hpt, hG]
  ring

/-- The generator of `JetPoincareVdm.exists_gen`, with the alternant identity exposed. -/
theorem exists_gen_span {N m : ℕ} (hm : N ≤ m) {pt : Fin (r + 1) → Fin k} (hpt : StrictMono pt)
    (hrm : r ≤ m) : ∃ G : XP k, vdm (id : Fin k → Fin k) * G ∈ Ideal.span (genSet 2 k N) ∧
      G ≠ 0 ∧ (lexO k).degree G = Finsupp.single (pt 0) (m - r) := by
  obtain ⟨G, hG⟩ := vdm_dvd_dD hpt m
  obtain ⟨hdeg, hne⟩ := degree_dD hpt hrm
  have hG0 : G ≠ 0 := by rintro rfl; rw [mul_zero] at hG; exact hne hG
  refine ⟨G, vdm_mul_mem_span_genSet_two hm hpt hG, hG0, ?_⟩
  have h1 := hdeg
  rw [hG, MonomialOrder.degree_mul (vdm_ne_zero hpt) hG0, degree_dT hpt] at h1
  have h2 := (degree_dD hpt (le_refl r)).1
  rw [dD_self, degree_dT hpt] at h2
  rw [h2, show Finsupp.single (pt 0) m = Finsupp.single (pt 0) r + Finsupp.single (pt 0) (m - r) by
    rw [← Finsupp.single_add, Nat.add_sub_cancel' hrm]] at h1
  have h3 := add_left_cancel (by simpa only [add_assoc] using h1)
  rw [add_comm (Finsupp.single (pt 0) (m - r))] at h3
  exact add_left_cancel h3

theorem exists_gens_span (N : ℕ) : ∃ G : Fin k → XP k, ∀ i,
    vdm (id : Fin k → Fin k) * G i ∈ Ideal.span (genSet 2 k N) ∧ G i ≠ 0 ∧
      (lexO k).degree (G i) = Finsupp.single i (N - (k - 1 - i)) := by
  have h : ∀ i : Fin k, ∃ G : XP k, vdm (id : Fin k → Fin k) * G ∈ Ideal.span (genSet 2 k N) ∧
      G ≠ 0 ∧ (lexO k).degree G = Finsupp.single i (N - (k - 1 - i)) := by
    intro i
    obtain ⟨G, h1, h2, h3⟩ := exists_gen_span (le_max_left N (k - 1 - i)) (ptI_strictMono i)
      (le_max_right N (k - 1 - i))
    refine ⟨G, h1, h2, ?_⟩
    rw [h3, ptI_zero]
    congr 1
    omega
  choose G hG using h
  exact ⟨G, hG⟩

/-- **`GenInclusion 2`**: the `n = 2` argument of `JetPoincareVdm` lands in the ideal of the
block generators (one block, where `blockProd = Rfac`). -/
theorem genInclusion_two : GenInclusion 2 := by
  intro k N f hL hV
  have hd : ∀ a b : Fin k, a < b → (X b - X a : XP k) ∣ f := by
    intro a b hab
    have := hV {a, b} (card_pair (ne_of_lt hab)) a (mem_insert_self _ _)
    rw [collapseTo_pair (ne_of_lt hab)] at this
    exact dvd_of_rename_subst_eq_zero this
  obtain ⟨g, rfl⟩ : vdm (id : Fin k → Fin k) ∣ f := by
    rw [vdm_eq_pprod strictMono_id]
    exact pprod_dvd (vpairs_lt strictMono_id) fun q hq => hd q.1 q.2 (vpairs_lt strictMono_id q hq)
  obtain ⟨G, hG⟩ := exists_gens_span (k := k) N
  have hunit : ∀ i, IsUnit ((lexO k).leadingCoeff (G i)) := fun i =>
    IsUnit.mk0 _ (MonomialOrder.leadingCoeff_ne_zero_iff.mpr (hG i).2.1)
  obtain ⟨q, rem, hdec, -, hrem⟩ := (lexO k).div hunit g
  have hlin : vdm (id : Fin k → Fin k) * Finsupp.linearCombination (XP k) G q ∈
      Ideal.span (genSet 2 k N) := by
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
      exact sub_mem hL (Wn_le_Lid (n := 2) (span_genSet_le_Wn (le_refl 2) hlin))
  rw [hdec, hrem0, add_zero]
  exact hlin

end

end VOA.TwoSeries.ArrangementGen
