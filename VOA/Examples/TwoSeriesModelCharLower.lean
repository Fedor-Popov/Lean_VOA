/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharEval
import VOA.Examples.TwoSeriesModelCharFermionic

/-!
# The colour-`≤ 1` fermionic lower bound for the model `S_{n,r}`, every `n ≥ 2`

For a shape `(m, s)` (`m` blocks of colour `0`, `s` of colour `1`, `r = m + 2s` letters) the
functionals

  `Λ_{k,λ,γ,β} = [u_λ v_0^l] ∘ E_{(γ,0)} ∘ Φ_{ψbar(vdm_s · e^β)}`

(`LamB`) are linearly independent on the weight-`N` part of `S_{n,r}`; the different shapes with
the same `r` are jointly independent because a functional of `T`-degree `s` vanishes on block
products of `T`-degree `> s` (`tIndex_indep`).  Counting them:

* `card_bIndex` — `#(shape (m,s), weight N) = [q^N] q^{(m+s) + s² + s} H_{2(m+s)} / ((q)_m (q)_s)`;
* `card_tIndex_le_finrank` — `#(all shapes with r letters) ≤ dim S_{n,r,N}`;
* `fermSeries_two_le_model` — **`[q^N] fermSeries 2 ≤ Σ_{r ≤ N} dim S_{n,r,N}` for every
  `n ≥ 2`** (the Chern–Tran–Wakhare colour profiles with colours `0, 1` only).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct VOA.QSeries
open VOA.AffineVOA.CorrectedR (Generator)
open VOA.AdamovicSymbol (wordWt letterWt)
open scoped BigOperators

noncomputable section

/-! ### Finite dimensionality of the model pieces -/

instance generator_finite : Finite Generator := by
  refine Finite.of_injective (fun g : Generator => match g with
    | .current a => (some a : Option (Fin 3))
    | .sugawara => none) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

theorem letterWt_pos (l : Generator × ℕ) : (l.2 : ℤ) + 1 ≤ letterWt l := by
  obtain ⟨g, k⟩ := l
  cases g <;> simp [letterWt]

theorem le_wordWt (w : List (Generator × ℕ)) (l : Generator × ℕ) (hl : l ∈ w) :
    (l.2 : ℤ) + 1 ≤ wordWt w := by
  induction w with
  | nil => simp at hl
  | cons x w ih =>
    have hx := letterWt_pos x
    have hw : 0 ≤ wordWt w := by
      clear ih hl
      induction w with
      | nil => simp [wordWt]
      | cons y w ihw =>
        have := letterWt_pos y
        simp only [wordWt, List.map_cons, List.sum_cons] at ihw ⊢
        omega
    rcases List.mem_cons.mp hl with rfl | h
    · simp only [wordWt, List.map_cons, List.sum_cons] at hw ⊢; omega
    · have := ih h
      have hx0 : 0 ≤ letterWt x := by have := letterWt_pos x; omega
      simp only [wordWt, List.map_cons, List.sum_cons] at this ⊢; omega

theorem words_finite (r : ℕ) (d : ℤ) :
    {w : List (Generator × ℕ) | w.length = r ∧ wordWt w = d}.Finite := by
  classical
  set S : Set (Generator × ℕ) := {l | l.2 < d.toNat + 1}
  have hS : S.Finite := (Set.finite_univ.prod (Set.finite_Iio (d.toNat + 1))).subset
    (fun l hl => ⟨Set.mem_univ _, hl⟩)
  haveI := hS.to_subtype
  have hfin := (List.finite_length_eq S r).image (List.map Subtype.val)
  refine hfin.subset ?_
  rintro w ⟨hw, hwt⟩
  have hmem : ∀ l ∈ w, l ∈ S := by
    intro l hl
    have := le_wordWt w l hl
    rw [hwt] at this
    show l.2 < d.toNat + 1
    omega
  refine ⟨w.pmap (fun l hl => (⟨l, hl⟩ : S)) hmem, by simp [hw], ?_⟩
  simp [List.map_pmap]

instance modelDeg_finiteDimensional' (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)
    (r : ℕ) (d : ℤ) : FiniteDimensional ℂ (modelDeg R t r d) := by
  have : {Q | ∃ w : List (Generator × ℕ), w.length = r ∧ wordWt w = d ∧ mword R t w = Q} =
      (fun w => mword R t w) '' {w | w.length = r ∧ wordWt w = d} := by
    ext Q; simp [and_assoc]
  rw [modelDeg, this]
  exact FiniteDimensional.span_of_finite ℂ ((words_finite r d).image _)

/-! ### Weights -/

theorem awt_append {m s : ℕ} (γ : Fin m → ℕ) :
    awt (Fin.append γ (fun _ : Fin s => 0)) = awt γ := by
  rw [awt, awt, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem sum_bwt_col (m s : ℕ) (g : Fin (m + s) → Fin 4) :
    ∑ i, bwt (col m s i) (g i) = (((m + s) + 2 * s + jcount g : ℕ) : ℤ) := by
  have h1 : ∑ i, bwt (col m s i) (g i) =
      ∑ i : Fin (m + s), (1 : ℤ) + 2 * ∑ i, ((col m s i : ℕ) : ℤ) + ∑ i, (jflag (g i) : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [bwt, jflag]
  rw [h1]
  have h2 : ∑ i, ((col m s i : ℕ) : ℤ) = s := by exact_mod_cast sum_col' m s
  rw [h2, jcount]
  push_cast
  simp

/-! ### The functionals of a shape -/

/-- The index of a shape `(m, s)`: a charge, a row, and exponents `γ` (colour-zero count) and
`β` (colour-one count). -/
abbrev BIdx (m s : ℕ) : Type :=
  Σ k : Fin (2 * (m + s) + 1), Rows (m + s) k × (Fin m → ℕ) × (Fin s → ℕ)

/-- The indices of conformal weight `N`. -/
def bIndex (m s N : ℕ) : Finset (BIdx m s) :=
  Finset.univ.sigma fun _ => (Finset.univ ×ˢ ((Fintype.piFinset fun _ => Finset.range (N + 1)) ×ˢ
    (Fintype.piFinset fun _ => Finset.range (N + 1)))).filter
      fun p => (msOf p.1).sum + awt p.2.1 + awt p.2.2 + s * s + s + (m + s) = N

/-- The functional of an index. -/
def LamB (n : ℕ) (hn : 2 ≤ n) {m s : ℕ} (i : BIdx m s) : MPoly (Rn n) →ₗ[ℂ] ℂ :=
  Lam (msOf i.2.1) (2 * (m + s) - i.1) (Fin.append i.2.2.1 (fun _ : Fin s => 0)) ∘ₗ
    VOA.TwoSeries.StrictModel.Φ (Rn n)
      (ψbar hn (fsF s i.2.2.2) (fsF_symm s i.2.2.2) (fsF_div s i.2.2.2))

theorem ψbar_comp_mk {n : ℕ} (hn : 2 ≤ n) {s : ℕ} (F : MvPolynomial (Fin s) ℂ) (hF : Symm F)
    (hd : DivX01 F) :
    ψbar hn F hF hd ∘ₗ (Ideal.Quotient.mkₐ ℂ (jetIdealT n)).toLinearMap = ψF F :=
  LinearMap.ext fun p => ψbar_mk hn F hF hd p

/-- The functional of a shape on a pushed-forward block product. -/
theorem LamB_push {n : ℕ} (hn : 2 ≤ n) {m s : ℕ} (i : BIdx m s) (g : Fin (m + s) → Fin 4)
    (a : Fin (m + s) → ℕ) :
    LamB n hn i (pushN n (pblk TPoly X (col m s) g a)) =
      coeff (toF a) (rename (Fin.natAdd m) (fsF s i.2.2.2) *
        (esymmPow (Fin.append i.2.2.1 (fun _ : Fin s => 0)) *
          Apol (msOf i.2.1) (2 * (m + s) - i.1) g)) := by
  rw [LamB, LinearMap.comp_apply, Φ_pushN, ψbar_comp_mk]
  exact lam_ψF_pblk (fsF_symm s _) _ _ (msOf_le i.2.1) _ g a

theorem pblk_lowM {m s : ℕ} (g : Fin (m + s) → Fin 4) (a : Fin (m + s) → ℕ) :
    LowM s (pblk TPoly X (col m s) g a) := by
  have h := (prod_sub_lowM (fun i => (col m s i : ℕ)) (fun i => lowC (col m s i) (g i) (a i))
    (fun i => PowerSeries.coeff (a i) (blk TPoly X (col m s i) (g i)))
    (fun i => lowC_lowM _ _ _) (fun i => blk_coeff_sub_lowM _ _ _)).2
  rwa [sum_col'] at h

/-- A functional of `T`-degree `s` vanishes on block products of `T`-degree `s' > s`. -/
theorem LamB_push_lower {n : ℕ} (hn : 2 ≤ n) {m s m' s' : ℕ} (hs : s < s') (i : BIdx m s)
    (g : Fin (m' + s') → Fin 4) (a : Fin (m' + s') → ℕ) :
    LamB n hn i (pushN n (pblk TPoly X (col m' s') g a)) = 0 := by
  rw [LamB, LinearMap.comp_apply, Φ_pushN, ψbar_comp_mk,
    Φ_ψF_eq_zero _ ((pblk_lowM g a).mono hs), map_zero]

/-- Homogeneity: a coefficient vanishes off the matching degree. -/
theorem coeff_fs_mul_eq_zero {m s : ℕ} (β : Fin s → ℕ) (α : Fin (m + s) → ℕ) (ms : Multiset ℕ)
    (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l) (g : Fin (m + s) → Fin 4) (d : Fin (m + s) →₀ ℕ)
    (hd : ∑ i, d i + jcount g ≠ (s * s - s + awt β) + awt α + ms.sum) :
    coeff d (rename (Fin.natAdd m) (fsF s β) * (esymmPow α * Apol ms l g)) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  by_contra hne
  have h1 : p.1.degree = s * s - s + awt β := by
    have := ((fsF_isHomogeneous s β).rename_isHomogeneous) (left_ne_zero_of_mul hne)
    rwa [Finsupp.degree_eq_weight_one]
  have h2 : ∑ i, p.2 i + jcount g = awt α + ms.sum := by
    by_contra h
    exact (right_ne_zero_of_mul hne) (coeff_esymmPow_mul_Apol_eq_zero ms l hms α g p.2 h)
  apply hd
  have hsum : ∑ i, d i = p.1.degree + ∑ i, p.2 i := by
    rw [← hp, Finsupp.degree_eq_sum]
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  omega

/-- The exponents completing `(k, λ)` to weight `N`. -/
def fibB (m s N : ℕ) {k : ℕ} (ro : Rows (m + s) k) : Finset ((Fin m → ℕ) × (Fin s → ℕ)) :=
  ((Fintype.piFinset fun _ => Finset.range (N + 1)) ×ˢ
    (Fintype.piFinset fun _ => Finset.range (N + 1))).filter
      fun p => (msOf ro).sum + awt p.1 + awt p.2 + s * s + s + (m + s) = N

theorem sum_bIndex {M : Type*} [AddCommMonoid M] {m s N : ℕ} (f : BIdx m s → M) :
    ∑ i ∈ bIndex m s N, f i =
      ∑ k : Fin (2 * (m + s) + 1), ∑ ro : Rows (m + s) k, ∑ p ∈ fibB m s N ro, f ⟨k, (ro, p)⟩ := by
  rw [bIndex, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro ro _
  rw [fibB, Finset.sum_filter]

/-- **Independence of the functionals of one shape** on the pushed-forward block products of
that shape. -/
theorem bIndex_indep {n : ℕ} (hn : 2 ≤ n) {m s N : ℕ} (κ : BIdx m s → ℂ)
    (h : ∀ (g : Fin (m + s) → Fin 4) (a : Fin (m + s) → ℕ),
      ∑ i, a i + jcount g + (m + s) + 2 * s = N →
        ∑ i ∈ bIndex m s N, κ i * LamB n hn i (pushN n (pblk TPoly X (col m s) g a)) = 0) :
    ∀ i ∈ bIndex m s N, κ i = 0 := by
  classical
  rintro ⟨k0, ro0, p0⟩ hi
  have hk0 : (k0 : ℕ) ≤ 2 * (m + s) := Nat.lt_succ_iff.mp k0.2
  let y : Rows (m + s) k0 → MvPolynomial (Fin (m + s)) ℂ := fun ro =>
    ∑ p ∈ fibB m s N ro, κ ⟨k0, (ro, p)⟩ •
      (rename (Fin.natAdd m) (fsF s p.2) * esymmPow (Fin.append p.1 (fun _ : Fin s => 0)))
  have hy : ∀ w : Cols (m + s) k0,
      ∑ ro, y ro * Apol (msOf ro) (2 * (m + s) - k0) w.1 = 0 := by
    intro w
    ext d
    rw [coeff_zero, coeff_sum]
    simp only [y, Finset.sum_mul, coeff_sum, smul_mul_assoc, coeff_smul, smul_eq_mul, mul_assoc]
    by_cases hW : ∑ i, d i + jcount w.1 + (m + s) + 2 * s = N
    · have htot := h w.1 d hW
      rw [sum_bIndex, Finset.sum_eq_single k0] at htot
      · rw [← htot]
        apply Finset.sum_congr rfl
        intro ro _
        apply Finset.sum_congr rfl
        intro p _
        rw [LamB_push, toF_coe]
      · intro k _ hk
        apply Finset.sum_eq_zero
        intro ro _
        apply Finset.sum_eq_zero
        intro p _
        rw [LamB_push, Apol_eq_zero _ _ (msOf_le ro) _ (vcount_ne_of_ne k0 k hk w), mul_zero,
          mul_zero, coeff_zero, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ _) hk
    · apply Finset.sum_eq_zero
      intro ro _
      apply Finset.sum_eq_zero
      intro p hp
      rw [coeff_fs_mul_eq_zero p.2 _ (msOf ro) _ (msOf_le ro) w.1 d ?_, mul_zero]
      rw [awt_append]
      have hpw := (Finset.mem_filter.mp hp).2
      have hss : s ≤ s * s := Nat.le_mul_self s
      omega
  have hy0 := block_indep (m + s) k0 hk0 y hy
  have hs0 : ∑ p ∈ fibB m s N ro0, κ ⟨k0, (ro0, p)⟩ •
      (rename (Fin.natAdd m) (vdm s) *
        (esymmPow (Fin.append p.1 (fun _ : Fin s => 0)) *
          rename (Fin.natAdd m) (esymmPow p.2))) = 0 := by
    have := congrFun hy0 ro0
    simp only [y, Pi.zero_apply] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro p _
    rw [fsF, map_mul]
    congr 1
    ring
  have hs0' : rename (Fin.natAdd m) (vdm s) * ∑ p ∈ fibB m s N ro0, κ ⟨k0, (ro0, p)⟩ •
      (esymmPow (Fin.append p.1 (fun _ : Fin s => 0)) * rename (Fin.natAdd m) (esymmPow p.2)) =
        0 := by
    rw [← hs0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [mul_smul_comm]
  have hV : rename (Fin.natAdd m) (vdm s) ≠ 0 := by
    intro h0
    exact vdm_ne_zero s (rename_injective _ (Fin.natAdd_injective s m) (by rw [h0, map_zero]))
  have hs1 := (mul_eq_zero.mp hs0').resolve_left hV
  have hp0 : p0 ∈ fibB m s N ro0 := by
    rw [bIndex, Finset.mem_sigma] at hi
    obtain ⟨-, hi⟩ := hi
    rw [Finset.mem_filter, Finset.mem_product] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.2, hi.2⟩
  exact (linearIndependent_iff'.mp (linearIndependent_mixed (m := m) (s := s))) _
    (fun p => κ ⟨k0, (ro0, p)⟩) hs1 p0 hp0

/-! ### All shapes with `r` letters -/

/-- The index over all shapes `(r - 2s, s)` with `2s ≤ r`. -/
abbrev TIdx (r : ℕ) : Type := Σ s : Fin (r / 2 + 1), BIdx (r - 2 * s) s

/-- The indices of conformal weight `N`. -/
def tIndex (r N : ℕ) : Finset (TIdx r) :=
  Finset.univ.sigma fun s => bIndex (r - 2 * s) s N

theorem two_mul_le_of_fin {r : ℕ} (s : Fin (r / 2 + 1)) : 2 * (s : ℕ) ≤ r := by
  have := s.2
  have : (s : ℕ) ≤ r / 2 := Nat.lt_succ_iff.mp this
  omega

/-- The pushed-forward block products of a shape lie in the weight-`N` model piece. -/
theorem push_pblk_mem {n r m s N : ℕ} (hr : m + 2 * s = r) (g : Fin (m + s) → Fin 4)
    (a : Fin (m + s) → ℕ) (hW : ∑ i, a i + jcount g + (m + s) + 2 * s = N) :
    pushN n (pblk TPoly X (col m s) g a) ∈ modelDeg (Rn n) (tn n) r (N : ℤ) := by
  apply map_modelDeg
  have h := pblk_mem TPoly X (col m s) g a
  rw [sum_col, hr, Finset.sum_add_distrib, sum_bwt_col] at h
  convert h using 2
  rw [← hW]
  push_cast
  ring

/-- **Joint independence of the functionals of all shapes with `r` letters** on the
weight-`N` part of `S_{n,r}`. -/
theorem tIndex_indep {n : ℕ} (hn : 2 ≤ n) (r N : ℕ) (κ : TIdx r → ℂ)
    (h : ∀ x ∈ modelDeg (Rn n) (tn n) r (N : ℤ), ∑ i ∈ tIndex r N, κ i * LamB n hn i.2 x = 0) :
    ∀ i ∈ tIndex r N, κ i = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0, hκ0⟩ := hne
  set bad := (tIndex r N).filter (fun i => κ i ≠ 0)
  obtain ⟨i1, hi1, hmax⟩ := bad.exists_max_image (fun i => (i.1 : ℕ))
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, hκ0⟩⟩
  obtain ⟨s0, j1⟩ := i1
  have hi1' := Finset.mem_filter.mp hi1
  have hj1 : j1 ∈ bIndex (r - 2 * s0) s0 N := (Finset.mem_sigma.mp hi1'.1).2
  have h2 := two_mul_le_of_fin s0
  have key := bIndex_indep hn (m := r - 2 * s0) (s := s0) (N := N)
    (fun j => κ ⟨s0, j⟩) (fun g a hW => by
      have hx := push_pblk_mem (n := n) (by omega : r - 2 * s0 + 2 * (s0 : ℕ) = r) g a hW
      have hsum := h _ hx
      rw [tIndex, Finset.sum_sigma, Finset.sum_eq_single s0] at hsum
      · exact hsum
      · intro s _ hs
        apply Finset.sum_eq_zero
        intro j hj
        rcases lt_or_gt_of_ne (fun h' : (s : ℕ) = s0 => hs (Fin.ext h')) with hlt | hgt
        · rw [LamB_push_lower hn hlt, mul_zero]
        · have : κ ⟨s, j⟩ = 0 := by
            by_contra hκ
            have := hmax ⟨s, j⟩ (Finset.mem_filter.mpr
              ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hj⟩, hκ⟩)
            exact absurd this (not_le.mpr hgt)
          rw [this, zero_mul]
      · intro hs; exact absurd (Finset.mem_univ _) hs)
  exact hi1'.2 (key j1 hj1)

/-- **The per-`r` lower bound**: `#tIndex r N ≤ dim S_{n,r,N}`. -/
theorem card_tIndex_le_finrank {n : ℕ} (hn : 2 ≤ n) (r N : ℕ) :
    (tIndex r N).card ≤ Module.finrank ℂ (modelDeg (Rn n) (tn n) r (N : ℤ)) := by
  classical
  set V := modelDeg (Rn n) (tn n) r (N : ℤ)
  let f : tIndex r N → Module.Dual ℂ V := fun i => LamB n hn i.1.2 ∘ₗ V.subtype
  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro S g hg i hi
    let c : TIdx r → ℂ := fun j => if h : j ∈ tIndex r N then
      (if (⟨j, h⟩ : tIndex r N) ∈ S then g ⟨j, h⟩ else 0) else 0
    have hc : ∀ x ∈ V, ∑ j ∈ tIndex r N, c j * LamB n hn j.2 x = 0 := by
      intro x hx
      have h1 := congrArg (fun φ : Module.Dual ℂ V => φ ⟨x, hx⟩) hg
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply, f, LinearMap.comp_apply, Submodule.subtype_apply] at h1
      rw [← h1, ← Finset.sum_coe_sort (tIndex r N)]
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · apply Finset.sum_congr rfl
        intro j hj
        simp [c, hj]
      · intro j _ hj
        simp [c, hj]
    have := tIndex_indep hn r N c hc i.1 i.2
    simpa [c, hi] using this
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_coe, Subspace.dual_finrank_eq] at this

/-! ### Counting -/

theorem card_pairs (m s e B : ℕ) (hB : e ≤ B) :
    ((((Fintype.piFinset fun _ : Fin m => Finset.range (B + 1)) ×ˢ
      (Fintype.piFinset fun _ : Fin s => Finset.range (B + 1))).filter
        fun p => awt p.1 + awt p.2 = e).card : ℚ) =
      PowerSeries.coeff e ((reciprocalQFactorial m : PowerSeries ℚ) * reciprocalQFactorial s) := by
  classical
  set A := (Fintype.piFinset fun _ : Fin m => Finset.range (B + 1))
  set Bs := (Fintype.piFinset fun _ : Fin s => Finset.range (B + 1))
  rw [PowerSeries.coeff_mul]
  have hc : ∀ x ∈ Finset.antidiagonal e,
      PowerSeries.coeff x.1 (reciprocalQFactorial m : PowerSeries ℚ) *
        PowerSeries.coeff x.2 (reciprocalQFactorial s : PowerSeries ℚ) =
      ∑ γ ∈ A, ∑ β ∈ Bs, (if awt γ = x.1 then (1 : ℚ) else 0) *
        (if awt β = x.2 then (1 : ℚ) else 0) := by
    intro x hx
    have hx' := Finset.mem_antidiagonal.mp hx
    rw [coeff_reciprocalQFactorial_eq_card m x.1 B (by omega),
      coeff_reciprocalQFactorial_eq_card s x.2 B (by omega), Finset.card_filter,
      Finset.card_filter]
    push_cast
    rw [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hc, Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  by_cases he : awt γ + awt β = e
  · rw [Finset.sum_eq_single (awt γ, awt β)]
    · simp [he]
    · intro x _ hne
      split_ifs with h1 h2 <;> try simp
      exact absurd (Prod.ext h1.symm h2.symm) hne
    · intro hn
      exact absurd (Finset.mem_antidiagonal.mpr he) hn
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro x hx
    have hx' := Finset.mem_antidiagonal.mp hx
    split_ifs with h1 h2 <;> try simp
    exact absurd (by rw [h1, h2]; exact hx') he

/-- The weighted count of one shape. -/
theorem card_bIndex (m s N : ℕ) :
    ((bIndex m s N).card : ℚ) = PowerSeries.coeff N
      (PowerSeries.X ^ ((m + s) + s * s + s) *
        (∑ k ∈ Finset.range (2 * (m + s) + 1), gaussian PowerSeries.X (2 * (m + s)) k) *
          ((reciprocalQFactorial m : PowerSeries ℚ) * reciprocalQFactorial s)) := by
  classical
  rw [Finset.card_eq_sum_ones, sum_bIndex, sum_gaussian_eq]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [cntG, Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro ro _
  rw [Finset.sum_const, nsmul_one, ← pow_add, PowerSeries.coeff_X_pow_mul',
    symSum_eq_msOf]
  split_ifs with hle
  · rw [← card_pairs m s _ N (by omega), fibB]
    congr 2
    ext p
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · rw [fibB, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    omega

theorem bIndex_eq_empty {m s N : ℕ} (h : N < m + 2 * s) : bIndex m s N = ∅ := by
  rw [bIndex, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨k, ro, p⟩ hi
  rw [Finset.mem_sigma, Finset.mem_filter] at hi
  have := hi.2.2
  have : s ≤ s * s := Nat.le_mul_self s
  omega

theorem coeff_fermSeries_two (N : ℕ) :
    PowerSeries.coeff N (fermSeries 2) = ∑ Nb ∈ Finset.range (N + 1),
      ∑ s ∈ Finset.range (Nb + 1), ((bIndex (Nb - s) s N).card : ℚ) := by
  rw [fermSeries, coeff_indexBounded_sum _ (coeff_fermTerm_eq_zero 2) N N le_rfl, map_sum]
  apply Finset.sum_congr rfl
  intro Nb _
  rw [fermTerm, bet, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsNb : s ≤ Nb := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [card_bIndex, bet_one, show Nb - s + s = Nb by omega]
  congr 1
  rw [pow_add, pow_add]
  ring

theorem reindex_inner (N s c : ℕ) (hc : c ≤ 2 * s) (F : ℕ → ℕ → ℚ)
    (hF : ∀ m, N < m + 2 * s → F m s = 0) :
    ∑ r ∈ (Finset.range (N + 1)).filter (fun r => c ≤ r), F (r - c) s =
      ∑ m ∈ Finset.range (N + 1), F m s := by
  conv_rhs => rw [← Finset.sum_filter_of_ne (p := fun m => m + c ≤ N) (fun m _ hm => by
    by_contra h; exact hm (hF m (by omega)))]
  refine Finset.sum_nbij' (fun r => r - c) (fun m => m + c) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
    omega
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    show r - c + c = r
    omega
  · intro m _
    show m + c - c = m
    omega
  · intro r _; rfl

theorem reindex_shapes (N : ℕ) (F : ℕ → ℕ → ℚ) (hF : ∀ m s, N < m + 2 * s → F m s = 0) :
    ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (r / 2 + 1), F (r - 2 * s) s =
      ∑ Nb ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (Nb + 1), F (Nb - s) s := by
  have hL : ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (r / 2 + 1), F (r - 2 * s) s =
      ∑ s ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1), F m s := by
    rw [Finset.sum_comm' (t' := Finset.range (N + 1))
      (s' := fun s => (Finset.range (N + 1)).filter (fun r => 2 * s ≤ r))]
    · apply Finset.sum_congr rfl
      intro s _
      exact reindex_inner N s (2 * s) le_rfl F (fun m h => hF m s h)
    · intro r s
      simp only [Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; omega
      · rintro ⟨⟨h1, h2⟩, h3⟩; omega
  have hR : ∑ Nb ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (Nb + 1), F (Nb - s) s =
      ∑ s ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1), F m s := by
    rw [Finset.sum_comm' (t' := Finset.range (N + 1))
      (s' := fun s => (Finset.range (N + 1)).filter (fun Nb => s ≤ Nb))]
    · apply Finset.sum_congr rfl
      intro s _
      exact reindex_inner N s s (by omega) F (fun m h => hF m s h)
    · intro r s
      simp only [Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; omega
      · rintro ⟨⟨h1, h2⟩, h3⟩; omega
  rw [hL, hR]

/-- **The colour-`≤ 1` fermionic lower bound, for every `n ≥ 2`**:
`[q^N] fermSeries 2 ≤ Σ_{r ≤ N} dim S_{n,r,N}`. -/
theorem fermSeries_two_le_model {n : ℕ} (hn : 2 ≤ n) (N : ℕ) :
    PowerSeries.coeff N (fermSeries 2) ≤
      ∑ r ∈ Finset.range (N + 1), (Module.finrank ℂ (modelDeg (Rn n) (tn n) r (N : ℤ)) : ℚ) := by
  rw [coeff_fermSeries_two, ← reindex_shapes N (fun m s => ((bIndex m s N).card : ℚ))
    (fun m s h => by show ((bIndex m s N).card : ℚ) = 0; rw [bIndex_eq_empty h]; simp)]
  apply Finset.sum_le_sum
  intro r _
  have h := card_tIndex_le_finrank hn r N
  rw [tIndex, Finset.card_sigma] at h
  have h' : ∑ s ∈ Finset.range (r / 2 + 1), ((bIndex (r - 2 * s) s N).card : ℚ) =
      ((∑ s : Fin (r / 2 + 1), (bIndex (r - 2 * s) s N).card : ℕ) : ℚ) := by
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun s => ((bIndex (r - 2 * s) s N).card : ℚ))]
  rw [h']
  exact_mod_cast h

end

end VOA.TwoSeries.ModelChar
