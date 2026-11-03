/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterAGIdentity
import VOA.Examples.TwoSeriesJetRing

/-!
# The leading-symbol map `L(c_{2,2m+3}) → R_{m+1}` (PBW-length symbol theorem for `M(2, 2m+3)`)

**Scope.**  This file proves a PBW-length leading-symbol statement into the
*presented* ring `R_{m+1}`; it does not mention Li's filtration, `V/C₂`, or the canonical map.
Intrinsic Li classical freeness of `M(2, 2m+3)` is
`VOA.VirasoroClassicalFreeness.classicallyFree` (`VirasoroMinimalClassicalFreeness.lean`), which
uses `virSymbol_twoSeries` below as its injectivity input.

Let `c = c_{2,2m+3}` and `R_{m+1} = ℂ[T_j]/(jets of T^{m+1})`.  The **leading symbol** of a
Virasoro creation word of length `b` is the monomial `T_{j₁} ⋯ T_{j_b}` (entry `j` standing for
`L_{-j-2}`).  This file proves that the symbol is well defined on the simple quotient: for every
`b` there is a `ℂ`-linear map `σ_b : V(c,0) → R_{m+1}` that

1. kills the maximal ideal,
2. kills every creation word of length `< b`,
3. sends every creation word of length `b` (in any order) to the product of its jets.

Combined with the Li-filtration bridge of `VirasoroMinimalClassicalFreeness.lean` this yields
`gr^{Li} L(c_{2,2m+3}) ≅ J_∞(ℂ[T]/(T^{m+1}))` (classical freeness); on its own it is the
length-filtration symbol statement.  The proof is the squeeze:

* `pair_mem_pairGood` — **simultaneous straightening**: every pair
  `(L-word w, T-monomial of w)` lies in the span of the pairs of Gordon-good sorted words of the
  same length, modulo `(lower length + maximal ideal) × 0`.  The rewriting steps are the jet
  relations of the singular vector in `V(c,0)` (`HasJetRelations`) and, in parallel, the jet
  relations `Σ_{e₁+⋯+e_{m+1} = k} T_{e₁} ⋯ T_{e_{m+1}} = 0` of `R_{m+1}`;
* the Gordon-good words form a basis of `L(c)` (proved: Gordon spanning + the Rocha-Caridi /
  Andrews–Gordon character, `gFamily_linearIndependent`), so `σ_b` can be **defined** on that
  basis (`Θ`), and the straightening shows that it has property 3 on every word;
* `virSymbol_of` — the generic statement (any `c`, `n`, `R`, `t` with the two families of jet
  relations and the Gordon lower bound);
* `virSymbol_twoSeries` — **for every `m`, `VirSymbol c_{2,2m+3} R_{m+1}`**, outright.

Everything is proved outright; no input is added.
-/

namespace VOA.TwoSeries.DSSlice

open VOA.VirModule VOA.VirGoodFil VOA.VirSimple VOA.LeeYangCharacter VOA.TwoSeriesCharacter
open MvPolynomial
open scoped BigOperators

noncomputable section

/-! ## §1  Length filtration and the symbol property -/

section Defs

variable (c : ℂ)

/-- Creation words of length `≤ b` (any order, any weight). -/
def vLen (b : ℕ) : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ {x | ∃ w : List ℕ, w.length ≤ b ∧ negWordVir c w = x}

/-- Creation words of length `< b` (any order, any weight). -/
def vBelow (b : ℕ) : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ {x | ∃ w : List ℕ, w.length < b ∧ negWordVir c w = x}

theorem negWordVir_mem_vLen {w : List ℕ} {b : ℕ} (h : w.length ≤ b) : negWordVir c w ∈ vLen c b :=
  Submodule.subset_span ⟨w, h, rfl⟩

theorem negWordVir_mem_vBelow {w : List ℕ} {b : ℕ} (h : w.length < b) :
    negWordVir c w ∈ vBelow c b :=
  Submodule.subset_span ⟨w, h, rfl⟩

theorem vLen_le_vBelow (b : ℕ) : vLen c b ≤ vBelow c (b + 1) :=
  Submodule.span_mono fun _ ⟨w, hw, hx⟩ => ⟨w, by omega, hx⟩

theorem vLen_mono {a b : ℕ} (h : a ≤ b) : vLen c a ≤ vLen c b :=
  Submodule.span_mono fun _ ⟨w, hw, hx⟩ => ⟨w, hw.trans h, hx⟩

theorem virFil_le_vBelow {p b : ℕ} (h : p < b) (N : ℤ) : virFil c p N ≤ vBelow c b := by
  rw [virFil, Submodule.span_le]
  rintro _ ⟨w, -, -, hl, rfl⟩
  exact negWordVir_mem_vBelow c (by omega)

variable (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)

/-- **The Virasoro symbol property** (PBW-length leading symbol; the injectivity input to
classical freeness, see `VirasoroClassicalFreeness.classicallyFree`): a family of `ℂ`-linear maps
`σ_b : V(c,0) → R` killing the maximal ideal and the creation words of length `< b`, and sending
every creation word of length `b` to the product of its jets `t_{j₁} ⋯ t_{j_b}`. -/
def VirSymbol : Prop :=
  ∃ σ : ℕ → (VirUniv c →ₗ[ℂ] R),
    (∀ b, ∀ v ∈ maxIdealVir c, σ b v = 0) ∧
    (∀ b, ∀ v ∈ vBelow c b, σ b v = 0) ∧
    (∀ w : List ℕ, σ w.length (negWordVir c w) = (w.map t).prod)

end Defs

/-! ## §2  Simultaneous straightening -/

section Straighten

variable (c : ℂ) (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R) (n : ℕ)

/-- Pairs (word, monomial) of Gordon-good sorted words of length `ℓ`, plus
`(lower length + maximal ideal) × 0`. -/
def pairGood (ℓ : ℕ) : Submodule ℂ (VirUniv c × R) :=
  Submodule.span ℂ {x | ∃ u : List ℕ, SortedWord u ∧ GordonGood n u ∧ u.length = ℓ ∧
      (negWordVir c u, (u.map t).prod) = x} ⊔ (vBelow c ℓ ⊔ maxIdealVir c).prod ⊥

theorem lower_mem_pairGood {ℓ : ℕ} {y : VirUniv c} (hy : y ∈ vBelow c ℓ ⊔ maxIdealVir c) :
    (y, (0 : R)) ∈ pairGood c R t n ℓ :=
  Submodule.mem_sup_right (Submodule.mem_prod.mpr ⟨hy, Submodule.zero_mem _⟩)

omit [Algebra ℂ R] in
theorem prod_map_perm {w w' : List ℕ} (h : w.Perm w') : (w.map t).prod = (w'.map t).prod :=
  (h.map t).prod_eq

theorem sortDesc_pair_sub (w : List ℕ) (hw : 0 < w.length) :
    (negWordVir c w, (w.map t).prod) - (negWordVir c (sortDesc w), ((sortDesc w).map t).prod) ∈
      pairGood c R t n w.length := by
  rw [Prod.mk_sub_mk, prod_map_perm R t (sortDesc_perm w), sub_self]
  apply lower_mem_pairGood
  exact Submodule.mem_sup_left (virFil_le_vBelow c (p := w.length - 1) (by omega) _
    (negWordVir_sub_sortDesc_mem c w))

/-- **Simultaneous straightening of sorted words.** -/
theorem sorted_pair_mem_pairGood (hJ : HasJetRelations c n)
    (hjet : ∀ k, ∑ e ∈ comps (n + 1) k, (e.map t).prod = 0) :
    ∀ u : List ℕ, SortedWord u →
      (negWordVir c u, (u.map t).prod) ∈ pairGood c R t n u.length := by
  classical
  obtain ⟨α, hα, hrel⟩ := hJ
  suffices H : ∀ s : ℕ, ∀ u : List ℕ, SortedWord u → energyVir u ^ 2 - sqSum u = s →
      (negWordVir c u, (u.map t).prod) ∈ pairGood c R t n u.length by
    intro u hu
    exact H _ u hu rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro u hu hs
  by_cases hg : GordonGood n u
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, hg, rfl, rfl⟩)
  obtain ⟨l₁, W, l₂, b, rfl, hWl, hWb⟩ := exists_window hu hg
  set u := l₁ ++ W ++ l₂ with hu_def
  set r := l₁ ++ l₂ with hr
  set ℓ := u.length with hℓ
  set k := W.sum with hk
  have hperm : (r ++ W).Perm u := by
    rw [hr, hu_def, List.append_assoc, List.append_assoc]
    exact List.perm_append_comm.append_left l₁
  have hlenr : r.length + (n + 1) = ℓ := by
    have h1 := hperm.length_eq
    simp only [List.length_append] at h1
    rw [hℓ, ← h1, hWl]
  set P := pairGood c R t n ℓ with hP
  obtain ⟨σ, hσ, hlead⟩ := hrel k
  have h1 : (applyWord c r σ, (0 : R)) ∈ P :=
    lower_mem_pairGood c R t n (Submodule.mem_sup_right (applyWord_mem_maxIdealVir c r hσ))
  have h2 : (applyWord c r (σ - α • jetSum c (n + 1) k), (0 : R)) ∈ P := by
    apply lower_mem_pairGood
    exact Submodule.mem_sup_left (virFil_le_vBelow c (p := n + r.length) (by omega) _
      (applyWord_mem_virFil c r hlead))
  have hJsum : applyWord c r (jetSum c (n + 1) k) =
      ∑ e ∈ comps (n + 1) k, negWordVir c (r ++ e) := by
    rw [jetSum_eq_sum, map_sum]
    simp only [negWordVir_append]
  have hRsum : ∑ e ∈ comps (n + 1) k, ((r ++ e).map t).prod = 0 := by
    simp only [List.map_append, List.prod_append]
    rw [← Finset.mul_sum, hjet k, mul_zero]
  have hterm : ∀ e ∈ comps (n + 1) k,
      (negWordVir c (r ++ e), ((r ++ e).map t).prod) -
        (if e.Perm W then (1 : ℂ) else 0) • (negWordVir c u, (u.map t).prod) ∈ P := by
    intro e he
    obtain ⟨hel, hes⟩ := (mem_comps _ _ e).mp he
    set w := r ++ e with hw
    have hwl : w.length = ℓ := by rw [hw, List.length_append, hel, hlenr]
    have hdiff := sortDesc_pair_sub c R t n w (by omega)
    rw [hwl] at hdiff
    by_cases hpe : e.Perm W
    · rw [if_pos hpe, one_smul]
      have hwu : sortDesc w = u := by
        have hpw : w.Perm u := (List.Perm.append_left r hpe).trans hperm
        exact List.Perm.eq_of_pairwise (fun x y _ _ h1 h2 => le_antisymm h2 h1)
          (sortDesc_sorted w) hu ((sortDesc_perm w).trans hpw)
      rwa [hwu] at hdiff
    · rw [if_neg hpe, zero_smul, sub_zero]
      have hsq : sqSum u < sqSum (sortDesc w) := by
        have e1 : sqSum (sortDesc w) = sqSum r + sqSum e :=
          (sqSum_perm (sortDesc_perm w)).trans (sqSum_append r e)
        have e2 : sqSum u = sqSum r + sqSum W := (sqSum_perm hperm).symm.trans (sqSum_append r W)
        have := sqSum_lt_of_not_perm hWb (by rw [hel, hWl]) hes hpe
        omega
      have hEw : energyVir (sortDesc w) = energyVir u := by
        rw [energyVir_sortDesc, ← energyVir_perm hperm, energyVir_eq_sum, energyVir_eq_sum]
        simp only [hw, List.sum_append, List.length_append]
        rw [hel, hes, hWl]
      have hbound := sqSum_le (sortDesc w)
      rw [hEw] at hbound
      have hmem := ihs (energyVir (sortDesc w) ^ 2 - sqSum (sortDesc w))
        (by rw [← hs, hEw]; omega) (sortDesc w) (sortDesc_sorted w) rfl
      rw [length_sortDesc, hwl] at hmem
      have := Submodule.add_mem _ hdiff hmem
      simpa using this
  have hsum := Submodule.sum_mem P hterm
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_boole] at hsum
  set m : ℂ := (((comps (n + 1) k).filter (fun e => e.Perm W)).card : ℂ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Nat.cast_ne_zero]
    apply Finset.card_ne_zero_of_mem (a := W)
    rw [Finset.mem_filter, mem_comps]
    exact ⟨⟨hWl, rfl⟩, List.Perm.refl W⟩
  have hpairsum : ∑ e ∈ comps (n + 1) k, (negWordVir c (r ++ e), ((r ++ e).map t).prod) =
      (applyWord c r (jetSum c (n + 1) k), (0 : R)) := by
    ext
    · rw [Prod.fst_sum, hJsum]
    · rw [Prod.snd_sum, hRsum]
  rw [hpairsum] at hsum
  have hcomb : (α * m) • (negWordVir c u, (u.map t).prod) =
      (applyWord c r σ, (0 : R)) - (applyWord c r (σ - α • jetSum c (n + 1) k), (0 : R)) -
        α • ((applyWord c r (jetSum c (n + 1) k), (0 : R)) -
          m • (negWordVir c u, (u.map t).prod)) := by
    rw [map_sub, map_smul, mul_smul]
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst]; module
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_zero, sub_zero, zero_sub, smul_sub,
        neg_neg]
  have hαm : α * m ≠ 0 := mul_ne_zero hα hm0
  have h5 : (α * m) • (negWordVir c u, (u.map t).prod) ∈ P := by
    rw [hcomb]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ hsum)
  have := Submodule.smul_mem _ (α * m)⁻¹ h5
  rwa [smul_smul, inv_mul_cancel₀ hαm, one_smul] at this

/-- **Simultaneous straightening of all words.** -/
theorem pair_mem_pairGood (hJ : HasJetRelations c n)
    (hjet : ∀ k, ∑ e ∈ comps (n + 1) k, (e.map t).prod = 0) (w : List ℕ) :
    (negWordVir c w, (w.map t).prod) ∈ pairGood c R t n w.length := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0]
    exact sorted_pair_mem_pairGood c R t n hJ hjet [] (List.Pairwise.nil)
  · have h := sorted_pair_mem_pairGood c R t n hJ hjet (sortDesc w) (sortDesc_sorted w)
    rw [length_sortDesc] at h
    have := Submodule.add_mem _ (sortDesc_pair_sub c R t n w hpos) h
    simpa using this

end Straighten

/-! ## §3  The symbol functional, defined on the Gordon basis -/

section Theta

variable (c : ℂ) (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R) (n : ℕ)
variable (hJ : HasJetRelations c n) (hlow : GordonLowerBound c n)
include hJ

theorem span_gFamily_eq (N : ℕ) :
    Submodule.span ℂ (Set.range (gFamily c n N N)) = (virasoroSimple c).grading (N : ℤ) := by
  rw [← goodFil_eq_span_gFamily c n hJ, goodFil_top']

include hlow

/-- The coordinate assignment on the Gordon basis of weight `N`. -/
def thetaN (ℓ N : ℕ) : (virasoroSimple c).grading (N : ℤ) →ₗ[ℂ] R :=
  ((Module.Basis.span (gFamily_linearIndependent c n hJ hlow N)).constr ℂ
      (fun u => if u.1.length = ℓ then (u.1.map t).prod else 0)).comp
    (LinearEquiv.ofEq _ _ (span_gFamily_eq c n hJ N).symm).toLinearMap

theorem thetaN_congr (ℓ : ℕ) {M N : ℕ} (h : M = N) (y : (virasoroSimple c).grading (M : ℤ))
    (x : VirUniv c ⧸ maxIdealVir c) (hx' : x ∈ (virasoroSimple c).grading (N : ℤ))
    (hyx : (y : VirUniv c ⧸ maxIdealVir c) = x) :
    thetaN c R t n hJ hlow ℓ M y = thetaN c R t n hJ hlow ℓ N ⟨x, hx'⟩ := by
  subst h; congr 1; exact Subtype.ext hyx

theorem thetaN_gWord (ℓ N : ℕ) (u : gordonWordsLe n N N)
    (hx : gWord c u.1 ∈ (virasoroSimple c).grading (N : ℤ)) :
    thetaN c R t n hJ hlow ℓ N ⟨gWord c u.1, hx⟩ =
      if u.1.length = ℓ then (u.1.map t).prod else 0 := by
  have hb : (LinearEquiv.ofEq _ _ (span_gFamily_eq c n hJ N).symm) ⟨gWord c u.1, hx⟩ =
      Module.Basis.span (gFamily_linearIndependent c n hJ hlow N) u := by
    rw [Module.Basis.span_apply]; rfl
  simp only [thetaN, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [hb, Module.Basis.constr_basis]

/-- The coordinate assignment on the weight-`N` piece, for integer `N`. -/
def thetaZ (ℓ : ℕ) (N : ℤ) : (virasoroSimple c).grading N →ₗ[ℂ] R :=
  if h : 0 ≤ N then
    (thetaN c R t n hJ hlow ℓ N.toNat).comp
      (LinearEquiv.ofEq _ _ (by rw [Int.toNat_of_nonneg h])).toLinearMap
  else 0

/-- The symbol on `L(c)`: the coordinates on the Gordon basis, summed over the weights. -/
def theta (ℓ : ℕ) : (VirUniv c ⧸ maxIdealVir c) →ₗ[ℂ] R :=
  (DFinsupp.lsum ℕ (thetaZ c R t n hJ hlow ℓ)).comp
    ((virasoroSimple c).isInternal.submodule_iSupIndep.linearEquiv
      (virasoroSimple c).isInternal.submodule_iSup_eq_top).symm.toLinearMap

theorem theta_of_mem (ℓ : ℕ) {N : ℤ} {x : VirUniv c ⧸ maxIdealVir c}
    (hx : x ∈ (virasoroSimple c).grading N) :
    theta c R t n hJ hlow ℓ x = thetaZ c R t n hJ hlow ℓ N ⟨x, hx⟩ := by
  simp only [theta, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [iSupIndep.linearEquiv_symm_apply _ _ hx, DFinsupp.lsum_single]

omit hlow in
theorem gWord_mem_grading {N : ℕ} (u : gordonWordsLe n N N) :
    gWord c u.1 ∈ (virasoroSimple c).grading (N : ℤ) := by
  rw [← span_gFamily_eq c n hJ N]
  exact Submodule.subset_span ⟨u, rfl⟩

theorem theta_gWord (ℓ N : ℕ) (u : gordonWordsLe n N N) :
    theta c R t n hJ hlow ℓ (gWord c u.1) = if u.1.length = ℓ then (u.1.map t).prod else 0 := by
  rw [theta_of_mem c R t n hJ hlow ℓ (gWord_mem_grading c n hJ u), thetaZ,
    dif_pos (Int.natCast_nonneg N)]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [thetaN_congr c R t n hJ hlow ℓ (Int.toNat_natCast N) _ _ (gWord_mem_grading c n hJ u) rfl,
    thetaN_gWord]

/-- The symbol on the universal module. -/
def Theta (ℓ : ℕ) : VirUniv c →ₗ[ℂ] R :=
  (theta c R t n hJ hlow ℓ).comp (maxIdealVir c).mkQ

theorem Theta_maxIdeal (ℓ : ℕ) {v : VirUniv c} (hv : v ∈ maxIdealVir c) :
    Theta c R t n hJ hlow ℓ v = 0 := by
  simp only [Theta, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero _).mpr hv, map_zero]

theorem Theta_good {u : List ℕ} (hs : SortedWord u) (hg : GordonGood n u) :
    Theta c R t n hJ hlow u.length (negWordVir c u) = (u.map t).prod := by
  have hu : u ∈ gordonWordsLe n (energyVir u) (energyVir u) :=
    mem_gordonWordsLe.mpr ⟨hs, hg, rfl, length_le_energyVir u⟩
  have := theta_gWord c R t n hJ hlow u.length (energyVir u) ⟨u, hu⟩
  rw [if_pos rfl] at this
  exact this

theorem Theta_vBelow (ℓ : ℕ) {v : VirUniv c} (hv : v ∈ vBelow c ℓ) :
    Theta c R t n hJ hlow ℓ v = 0 := by
  have hle : vBelow c ℓ ≤ LinearMap.ker (Theta c R t n hJ hlow ℓ) := by
    rw [vBelow, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hmem : (maxIdealVir c).mkQ (negWordVir c w) ∈ goodFil c w.length (energyVir w : ℤ) :=
      Submodule.mem_map_of_mem (negWordVir_mem_virFil_length c w)
    rw [goodFil_eq_span_gFamily c n hJ] at hmem
    have hle2 : Submodule.span ℂ (Set.range (gFamily c n (energyVir w) w.length)) ≤
        LinearMap.ker (theta c R t n hJ hlow ℓ) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨u, hu⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hu' : u ∈ gordonWordsLe n (energyVir w) (energyVir w) :=
        gordonWordsLe_subset n _ _ hu
      have hl := (mem_gordonWordsLe.mp hu).2.2.2
      have := theta_gWord c R t n hJ hlow ℓ (energyVir w) ⟨u, hu'⟩
      rw [if_neg (by simp only; omega)] at this
      exact this
    exact hle2 hmem
  exact hle hv

/-- **The pair module lies on the graph of `Θ_ℓ`.** -/
theorem Theta_pairGood (ℓ : ℕ) {x : VirUniv c × R} (hx : x ∈ pairGood c R t n ℓ) :
    Theta c R t n hJ hlow ℓ x.1 = x.2 := by
  let Δ : (VirUniv c × R) →ₗ[ℂ] R :=
    (Theta c R t n hJ hlow ℓ).comp (LinearMap.fst ℂ _ _) - LinearMap.snd ℂ _ _
  have hle : pairGood c R t n ℓ ≤ LinearMap.ker Δ := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨u, hs, hg, hl, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      simp only [Δ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply]
      rw [← hl, Theta_good c R t n hJ hlow hs hg, sub_self]
    · rintro ⟨y, z⟩ hyz
      obtain ⟨hy, hz⟩ := Submodule.mem_prod.mp hyz
      change z ∈ (⊥ : Submodule ℂ R) at hz
      rw [Submodule.mem_bot] at hz
      subst hz
      rw [LinearMap.mem_ker]
      simp only [Δ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, sub_zero]
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, Theta_vBelow c R t n hJ hlow ℓ hy1, Theta_maxIdeal c R t n hJ hlow ℓ hy2,
        add_zero]
  have h := hle hx
  rw [LinearMap.mem_ker] at h
  simp only [Δ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply] at h
  exact sub_eq_zero.mp h

/-- **The leading-symbol property from the two families of jet relations and the Gordon lower
bound.** -/
theorem virSymbol_of (hjet : ∀ k, ∑ e ∈ comps (n + 1) k, (e.map t).prod = 0) :
    VirSymbol c R t :=
  ⟨Theta c R t n hJ hlow, fun b _ hv => Theta_maxIdeal c R t n hJ hlow b hv,
    fun b _ hv => Theta_vBelow c R t n hJ hlow b hv,
    fun w => Theta_pairGood c R t n hJ hlow w.length (pair_mem_pairGood c R t n hJ hjet w)⟩

end Theta

/-! ## §4  The jet relations of `R_{m+1}` and the two-series specialisation -/

open VOA.TwoSeries.StrictModel

/-- `[s^k] T(s)^m = Σ_{e₁+⋯+e_m = k} T_{e₁} ⋯ T_{e_m}`. -/
theorem coeff_tSer_pow : ∀ (m k : ℕ),
    PowerSeries.coeff k (tSer ^ m) = ∑ e ∈ comps m k, (e.map (X : ℕ → TPoly)).prod
  | 0, k => by
      by_cases hk : k = 0
      · subst hk; simp [comps]
      · simp [comps, hk, PowerSeries.coeff_one]
  | m + 1, k => by
      rw [pow_succ', PowerSeries.coeff_mul, comps, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [coeff_tSer_pow m p.2, Finset.mul_sum, Finset.sum_map]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp [tSer, PowerSeries.coeff_mk]
      · intro p hp q hq hpq
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hx'
        obtain ⟨e, -, rfl⟩ := hx
        obtain ⟨e', -, he⟩ := hx'
        have h1 : q.1 = p.1 := (List.cons.inj he).1
        have hp' := Finset.mem_antidiagonal.mp (Finset.mem_coe.mp hp)
        have hq' := Finset.mem_antidiagonal.mp (Finset.mem_coe.mp hq)
        exact hpq (Prod.ext h1.symm (by omega))

/-- The jet relations of `R_{m+1}`. -/
theorem jet_rel_Rn (m k : ℕ) : ∑ e ∈ comps (m + 1) k, (e.map (tn (m + 1))).prod = 0 := by
  have h : Ideal.Quotient.mk (jetIdealT (m + 1)) (PowerSeries.coeff k (tSer ^ (m + 1))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
  rw [coeff_tSer_pow, map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_list_prod, List.map_map]
  rfl

/-- **Leading symbol of `M(2, 2m+3)`**: the leading-symbol maps
`L(c_{2,2m+3}) → R_{m+1} = ℂ[T_j]/(jets of T^{m+1})` exist, for every `m`.  Proved outright.
The intrinsic Li classical-freeness theorem built on it is
`VOA.VirasoroClassicalFreeness.classicallyFree`. -/
theorem virSymbol_twoSeries (m : ℕ) :
    VirSymbol (twoSeriesLevels m).c (Rn (m + 1)) (tn (m + 1)) :=
  virSymbol_of _ _ _ m (twoSeries_hasJetRelations_all m) (gordonLowerBound_twoSeries m)
    (jet_rel_Rn m)

end

end VOA.TwoSeries.DSSlice
