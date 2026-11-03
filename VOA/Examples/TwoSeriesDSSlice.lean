/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesDSVirSymbol
import VOA.Examples.TwoSeriesCharacterGU
import VOA.Examples.TwoSeriesStrictEndpoint
import VOA.Examples.TwoSeriesDetectFunctional
import VOA.Examples.TwoSeriesPoincareZero

/-!
# Detection from the Drinfeld–Sokolov slice map

The detection input `TwoSeriesModelDetects n` (equivalently, the evaluation-functional family
`TwoSeriesEvalFunctionals n`) is reduced here to a statement about one **Drinfeld–Sokolov-type
map** `W : V^{k_n}(sl₂) → Vir^c` into the *universal* Virasoro vacuum module at the
Drinfeld–Sokolov central charge `c = c_{2,2n+1}`, plus the leading-symbol (PBW-length) maps of
`M(2, 2n+1)`, which are proved (`TwoSeriesDSVirSymbol.virSymbol_twoSeries`; the intrinsic Li
classical-freeness theorem is `VirasoroClassicalFreeness.classicallyFree`).

## The slice map

Let `b₋ = span(f, h)` and `χ` the character of `t⁻¹b₋[t⁻¹]` with `χ(f_{-1}) = -1` and `χ = 0` on
all other modes.  The quotient `X = V^k / Σ (x - χ(x)) V^k` (`x ∈ t⁻¹b₋[t⁻¹]`) is, by PBW, the
space `ℂ[e_{-1}, e_{-2}, …]|0⟩`; the creation Sugawara modes act on it, and
`L_{-n₁} ⋯ L_{-n_b}|0⟩ ↦ [L^{sug}_{-n₁} ⋯ L^{sug}_{-n_b}|0⟩]` is a linear isomorphism
`Vir^c → X` (triangular: `L_{-j-2}` has leading term a nonzero multiple of `e_{-j-1}`).  The
**slice map** is `W = (that isomorphism)⁻¹ ∘ (V^k → X)`, made `ℤ`-graded by `a = -(charge)/2`
(the power of the Rees parameter carried by `f_{-1} ↦ -1`).  It is the quantum version of
"restrict to the Kostant slice `f + ℂe`", i.e. of evaluating the model symbols at the base point
`(u, v) = (0, 1)`.

`DSSliceMap c L` records the properties of such a map that the reduction uses — all of them
statements about the *universal* objects `V^k(sl₂)` and `Vir^c` (exact Whittaker relations for the
`f`-modes; filtration by `2·#e + #h + #T`; the `e`, `h` letters strictly lower; the Sugawara
letter acting as `L_{-m-2}` up to lower terms).  `SliceArakawa S` is the one statement about
the simple quotients: **`W` maps the maximal ideal of `V^k` into the maximal ideal of `Vir^c`**,
i.e. `W` descends to `L_k(sl₂) → L(c)`.  This is the slice form of Arakawa's theorem
`H_DS(L_k(sl₂)) ≅ L(c_k)`.

## Results

* `evalFunctional_of_dsSlice` — `DSSliceMap` + `SliceArakawa` + `VirSymbol` give the
  evaluation functional at every filtration index (`Λ_r = Σ_a σ_{r-a} ∘ W_a`);
* `modelDetects_of_dsSlice`;
* `twoSeriesModelDetects_of_dsSlice` — at the boundary level, with the leading-symbol maps of
  `M(2, 2n+1)` **proved** (`virSymbol_twoSeries`): `TwoSeriesModelDetects (m+1)` from a slice map
  and its Arakawa
  property only;
* `twoSeries_gradedUnitary_of_dsSlice` — **Affine GU ⇒ GU of `M(2, 2n+3)`**,
  `#print axioms`-clean, conditional on `hA`, the slice map `S`, `SliceArakawa S` and the
  jet-ideal Poincaré input `JetPoincareCoreT0 n`.

Numerical evidence (exact linear algebra mod `p = 1000003`, not a proof; the scripts are
not in the repository).  For the slice map constructed as above at `k_n = -2 + 2/(2n+1)`:
`Vir^c → X` is invertible (DS weights `≤ 17`); the image of the maximal ideal of `V^{k_n}` lies
in the maximal ideal of `Vir^{c_{2,2n+1}}` for `n = 2` and `n = 3` at all affine weights `≤ 10`
and all charges, and for charge `≤ 0` it is all of it; with the central charge replaced by
`c_{2,2n+3}` the inclusion fails.  The universal fields `filtered` / `current_lower` hold on all
2187 corrected words of weight `≤ 6` with nonzero image (`n = 2, 3`), and fail if every bound
is lowered by one; `f_one`, `f_high`, `sugawara` hold exactly by construction.

Everything here is proved; `DSSliceMap` and `SliceArakawa` are stated, never assumed globally.
-/

namespace VOA.TwoSeries.DSSlice

open MvPolynomial VOA.SymbolModel VOA.AdamovicSymbol
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR
open VOA.VirModule VOA.VirGoodFil VOA.VirSimple VOA.LeeYangCharacter
open VOA.TwoSeries.StrictModel
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete
open scoped BigOperators

noncomputable section

/-! ## §1  Integer-indexed length filtration and symbols -/

section Symbols

variable (c : ℂ)

/-- Creation words of length `≤ b`, with `⊥` for negative `b`. -/
def vLenZ (b : ℤ) : Submodule ℂ (VirUniv c) := if 0 ≤ b then vLen c b.toNat else ⊥

theorem vLenZ_mono {a b : ℤ} (h : a ≤ b) : vLenZ c a ≤ vLenZ c b := by
  unfold vLenZ
  split_ifs with ha hb hb
  · exact vLen_mono c (by omega)
  · omega
  · exact bot_le
  · exact le_rfl

variable {R : Type} [CommRing R] [Algebra ℂ R] {t : ℕ → R}

/-- Integer-indexed symbol maps (`0` for negative index). -/
def sigmaZ (σ : ℕ → (VirUniv c →ₗ[ℂ] R)) (b : ℤ) : VirUniv c →ₗ[ℂ] R :=
  if 0 ≤ b then σ b.toNat else 0

variable {c}

theorem sigmaZ_maxIdeal {σ : ℕ → (VirUniv c →ₗ[ℂ] R)}
    (hI : ∀ b, ∀ v ∈ maxIdealVir c, σ b v = 0) (b : ℤ) {v : VirUniv c}
    (hv : v ∈ maxIdealVir c) : sigmaZ c σ b v = 0 := by
  unfold sigmaZ; split_ifs
  · exact hI _ v hv
  · rfl

theorem sigmaZ_lower {σ : ℕ → (VirUniv c →ₗ[ℂ] R)}
    (hlow : ∀ b, ∀ v ∈ vBelow c b, σ b v = 0) (b : ℤ) {v : VirUniv c}
    (hv : v ∈ vLenZ c (b - 1)) : sigmaZ c σ b v = 0 := by
  by_cases hb : 1 ≤ b
  · have h0 : (0 : ℤ) ≤ b - 1 := by omega
    rw [vLenZ, if_pos h0] at hv
    rw [sigmaZ, if_pos (by omega : (0 : ℤ) ≤ b)]
    apply hlow
    have := vLen_le_vBelow c _ hv
    rwa [show (b - 1).toNat + 1 = b.toNat by omega] at this
  · rw [vLenZ, if_neg (by omega : ¬ (0 : ℤ) ≤ b - 1), Submodule.mem_bot] at hv
    rw [hv, map_zero]

theorem sigma_Lop {σ : ℕ → (VirUniv c →ₗ[ℂ] R)}
    (hlow : ∀ b, ∀ v ∈ vBelow c b, σ b v = 0)
    (hword : ∀ w : List ℕ, σ w.length (negWordVir c w) = (w.map t).prod)
    (m B : ℕ) {v : VirUniv c} (hv : v ∈ vLen c B) :
    σ (B + 1) (Lop c (-(m : ℤ) - 2) v) = t m * σ B v := by
  have hle : vLen c B ≤ LinearMap.ker
      ((σ (B + 1)).comp (Lop c (-(m : ℤ) - 2)) - (t m) • σ B) := by
    rw [vLen, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, sub_eq_zero, ← negWordVir_cons]
    rcases hw.lt_or_eq with hlt | heq
    · rw [hlow _ _ (negWordVir_mem_vBelow c (by simp; omega)),
        hlow _ _ (negWordVir_mem_vBelow c hlt), smul_zero]
    · have h1 := hword (m :: w)
      have h2 := hword w
      simp only [List.length_cons, List.map_cons, List.prod_cons] at h1
      rw [heq] at h1 h2
      rw [h1, h2, smul_eq_mul]
  have h := hle hv
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    sub_eq_zero, smul_eq_mul] at h
  exact h

theorem sigmaZ_Lop {σ : ℕ → (VirUniv c →ₗ[ℂ] R)}
    (hlow : ∀ b, ∀ v ∈ vBelow c b, σ b v = 0)
    (hword : ∀ w : List ℕ, σ w.length (negWordVir c w) = (w.map t).prod)
    (m : ℕ) (b : ℤ) {v : VirUniv c} (hv : v ∈ vLenZ c b) :
    sigmaZ c σ (b + 1) (Lop c (-(m : ℤ) - 2) v) = t m * sigmaZ c σ b v := by
  by_cases hb : 0 ≤ b
  · rw [vLenZ, if_pos hb] at hv
    rw [sigmaZ, sigmaZ, if_pos hb, if_pos (by omega : (0 : ℤ) ≤ b + 1),
      show (b + 1).toNat = b.toNat + 1 by omega]
    exact sigma_Lop hlow hword m _ hv
  · rw [vLenZ, if_neg hb, Submodule.mem_bot] at hv
    rw [hv, map_zero, map_zero, map_zero, mul_zero]

end Symbols

/-! ## §2  The slice map and its Arakawa property -/

section Slice

variable (c : ℂ) (L : CosetLevels)

/-- **A Drinfeld–Sokolov slice map** `V^{kA}(sl₂) → Vir^c`, graded by the power `a` of the Rees
parameter (`a = #f - #e` on words).  All fields are statements about the universal objects:

* `vacuum` — `W |0⟩ = |0⟩` in degree `0`;
* `f_one`, `f_high` — the exact Whittaker relations `W ∘ f_{-1} = -s·W`, `W ∘ f_{-j} = 0`
  (`j ≥ 2`);
* `filtered` — a corrected word of length `ℓ` has degree-`a` part of Virasoro length `≤ ℓ - a`
  (`= 2#e + #h + #T`);
* `current_lower` — for words beginning with an `e`- or `h`-letter that bound drops by one;
* `sugawara` — the Sugawara letter `T_{(m)}` acts as `L_{-m-2}`, up to that lower piece. -/
structure DSSliceMap where
  /-- The map, with its Rees-parameter grading. -/
  W : WakModule L.kA →ₗ[ℂ] (ℤ →₀ VirUniv c)
  vacuum : W (correctedWordState L.kA L.aNoncritical []) = Finsupp.single 0 (vacVec c)
  f_one : ∀ (y : WakModule L.kA) (a : ℤ), W (J L.kA 1 (-1) y) a = -(W y (a - 1))
  f_high : ∀ (j : ℕ) (y : WakModule L.kA), W (J L.kA 1 (-(j : ℤ) - 2) y) = 0
  filtered : ∀ (w : List (Generator × ℕ)) (a : ℤ),
    W (correctedWordState L.kA L.aNoncritical w) a ∈ vLenZ c ((w.length : ℤ) - a)
  current_lower : ∀ (b : Fin 3), b ≠ 1 → ∀ (m : ℕ) (w : List (Generator × ℕ)) (a : ℤ),
    W (correctedWordState L.kA L.aNoncritical ((Generator.current b, m) :: w)) a ∈
      vLenZ c ((w.length : ℤ) - a)
  sugawara : ∀ (m : ℕ) (w : List (Generator × ℕ)) (a : ℤ),
    W (correctedWordState L.kA L.aNoncritical ((Generator.sugawara, m) :: w)) a -
      Lop c (-(m : ℤ) - 2) (W (correctedWordState L.kA L.aNoncritical w) a) ∈
        vLenZ c ((w.length : ℤ) - a)

variable {c L}

/-- **The slice form of Arakawa's theorem** (input): the slice map sends the maximal ideal of
`V^{kA}(sl₂)` into the maximal ideal of `Vir^c`, i.e. it descends to `L_{kA}(sl₂) → L(c)`. -/
def SliceArakawa (S : DSSliceMap c L) : Prop :=
  ∀ y ∈ ImaxL L, ∀ a : ℤ, S.W y a ∈ maxIdealVir c

variable {R : Type} [CommRing R] [Algebra ℂ R] {t : ℕ → R}

/-- The functional `Λ_r = Σ_a σ_{r-a} ∘ W_a`. -/
def lam (S : DSSliceMap c L) (σ : ℕ → (VirUniv c →ₗ[ℂ] R)) (r : ℤ) :
    WakModule L.kA →ₗ[ℂ] R :=
  (Finsupp.lsum ℕ fun a => sigmaZ c σ (r - a)).comp S.W

theorem lam_apply (S : DSSliceMap c L) (σ : ℕ → (VirUniv c →ₗ[ℂ] R)) (r : ℤ)
    (y : WakModule L.kA) :
    lam S σ r y = (S.W y).sum fun a v => sigmaZ c σ (r - a) v := by
  simp [lam]

theorem lam_eq_sum (S : DSSliceMap c L) (σ : ℕ → (VirUniv c →ₗ[ℂ] R)) (r : ℤ)
    (y : WakModule L.kA) {s : Finset ℤ} (hs : (S.W y).support ⊆ s) :
    lam S σ r y = ∑ a ∈ s, sigmaZ c σ (r - a) (S.W y a) := by
  rw [lam_apply, Finsupp.sum_of_support_subset _ hs]
  intro a _; exact map_zero _

theorem lam_eq_zero (S : DSSliceMap c L) (σ : ℕ → (VirUniv c →ₗ[ℂ] R)) (r : ℤ)
    (y : WakModule L.kA) (h : ∀ a, sigmaZ c σ (r - a) (S.W y a) = 0) : lam S σ r y = 0 := by
  rw [lam_eq_sum S σ r y subset_rfl]
  exact Finset.sum_eq_zero fun a _ => h a

theorem lam_f_one (S : DSSliceMap c L) (σ : ℕ → (VirUniv c →ₗ[ℂ] R)) (r : ℤ)
    (y : WakModule L.kA) : lam S σ (r + 1) (J L.kA 1 (-1) y) = -lam S σ r y := by
  classical
  have hsupp : (S.W (J L.kA 1 (-1) y)).support ⊆ (S.W y).support.image (· + 1) := by
    intro a ha
    rw [Finsupp.mem_support_iff, S.f_one, neg_ne_zero] at ha
    rw [Finset.mem_image]
    exact ⟨a - 1, Finsupp.mem_support_iff.mpr ha, by ring⟩
  rw [lam_eq_sum S σ _ _ hsupp, Finset.sum_image (fun x _ y _ h => by simpa using h),
    lam_eq_sum S σ r y subset_rfl, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [S.f_one, map_neg, show r + 1 - (a + 1) = r - a by ring, show a + 1 - 1 = a by ring]

theorem lam_f_high (S : DSSliceMap c L) (σ : ℕ → (VirUniv c →ₗ[ℂ] R)) (r : ℤ) (j : ℕ)
    (y : WakModule L.kA) : lam S σ r (J L.kA 1 (-(j : ℤ) - 2) y) = 0 := by
  change (Finsupp.lsum ℕ fun a => sigmaZ c σ (r - a)) (S.W _) = 0
  rw [S.f_high, map_zero]

theorem lam_maxIdeal (S : DSSliceMap c L) (hS : SliceArakawa S) {σ : ℕ → (VirUniv c →ₗ[ℂ] R)}
    (hI : ∀ b, ∀ v ∈ maxIdealVir c, σ b v = 0) (r : ℤ) {y : WakModule L.kA}
    (hy : y ∈ ImaxL L) : lam S σ r y = 0 :=
  lam_eq_zero S σ r y fun a => sigmaZ_maxIdeal hI _ (hS y hy a)

theorem lam_lower (S : DSSliceMap c L) {σ : ℕ → (VirUniv c →ₗ[ℂ] R)}
    (hlow : ∀ b, ∀ v ∈ vBelow c b, σ b v = 0) (r : ℕ) {y : WakModule L.kA}
    (hy : y ∈ lowerP L.kA L.aNoncritical r) : lam S σ r y = 0 := by
  cases r with
  | zero =>
    change y ∈ (⊥ : Submodule ℂ (WakModule L.kA)) at hy
    rw [Submodule.mem_bot] at hy; rw [hy, map_zero]
  | succ q =>
    change y ∈ correctedAffineRPiece L.kA L.aNoncritical q at hy
    have hle : correctedAffineRPiece L.kA L.aNoncritical q ≤
        LinearMap.ker (lam S σ ((q + 1 : ℕ) : ℤ)) := by
      rw [correctedAffineRPiece, Submodule.span_le]
      rintro _ ⟨⟨w, hw⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      refine lam_eq_zero S σ _ _ fun a => sigmaZ_lower hlow _ ?_
      refine vLenZ_mono c ?_ (S.filtered w a)
      push_cast; omega
    exact hle hy

theorem evR_mletter_current_ne (b : Fin 3) (hb : b ≠ 1) (m : ℕ) :
    evR R (mletter R t (Generator.current b, m)) = 0 := by
  change evR R (ι R (letterSym (Generator.current b, m))) = 0
  rw [evR_ι, Desc.evalBase_letterSym, if_neg, map_zero]
  intro h
  exact hb (by simpa using (Prod.mk.inj h).1)

theorem evR_mletter_sugawara (m : ℕ) :
    evR R (mletter R t (Generator.sugawara, m)) = t m := by
  change evR R (ι R (letterSym (Generator.sugawara, m)) + MvPolynomial.C (t m)) = t m
  rw [map_add, evR_ι, Desc.evalBase_letterSym, if_neg (by simp), map_zero, zero_add,
    ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

/-- **Word values.** -/
theorem lam_word (S : DSSliceMap c L) {σ : ℕ → (VirUniv c →ₗ[ℂ] R)}
    (hlow : ∀ b, ∀ v ∈ vBelow c b, σ b v = 0)
    (hword : ∀ w : List ℕ, σ w.length (negWordVir c w) = (w.map t).prod) :
    ∀ w : List (Generator × ℕ),
      lam S σ w.length (correctedWordState L.kA L.aNoncritical w) = evR R (mword R t w) := by
  classical
  intro w
  induction w with
  | nil =>
    rw [lam_apply, S.vacuum, Finsupp.sum_single_index (by simp)]
    simp only [List.length_nil, Nat.cast_zero, sub_zero, sigmaZ, le_refl, if_true,
      Int.toNat_zero, mword_nil, map_one]
    have := hword []
    simpa using this
  | cons l w ih =>
    obtain ⟨g, m⟩ := l
    cases g with
    | current b =>
      rw [correctedWordState_cons', letterOp_current, mword_cons, map_mul, List.length_cons]
      by_cases hb : b = 1
      · subst hb
        rw [evR_mletter_f]
        rcases m with _ | m
        · simp only [Nat.cast_zero, neg_zero, zero_sub, if_true]
          push_cast
          rw [lam_f_one, ih]; ring
        · rw [show (-((m + 1 : ℕ) : ℤ) - 1) = -(m : ℤ) - 2 by push_cast; ring]
          push_cast
          rw [lam_f_high]
          simp
      · rw [evR_mletter_current_ne b hb, zero_mul]
        refine lam_eq_zero S σ _ _ fun a => sigmaZ_lower hlow _ ?_
        have h := S.current_lower b hb m w a
        rw [correctedWordState_cons', letterOp_current] at h
        refine vLenZ_mono c ?_ h
        push_cast; omega
    | sugawara =>
      rw [mword_cons, map_mul, evR_mletter_sugawara, ← ih, List.length_cons]
      set y := correctedWordState L.kA L.aNoncritical ((Generator.sugawara, m) :: w) with hy
      set z := correctedWordState L.kA L.aNoncritical w with hz
      have hs1 : (S.W y).support ⊆ (S.W y).support ∪ (S.W z).support := Finset.subset_union_left
      have hs2 : (S.W z).support ⊆ (S.W y).support ∪ (S.W z).support :=
        Finset.subset_union_right
      rw [lam_eq_sum S σ _ y hs1, lam_eq_sum S σ _ z hs2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hδ : sigmaZ c σ (((w.length + 1 : ℕ) : ℤ) - a)
          (S.W y a - Lop c (-(m : ℤ) - 2) (S.W z a)) = 0 :=
        sigmaZ_lower hlow _ (vLenZ_mono c (by push_cast; omega) (S.sugawara m w a))
      rw [← add_sub_cancel (Lop c (-(m : ℤ) - 2) (S.W z a)) (S.W y a), map_add, hδ, add_zero]
      have h := sigmaZ_Lop hlow hword m _ (S.filtered w a)
      rw [show ((w.length : ℤ) - a + 1) = (((w.length + 1 : ℕ) : ℤ) - a) by push_cast; ring] at h
      exact h

/-- **The evaluation functionals from the slice map**, at every filtration index. -/
theorem evalFunctional_of_dsSlice (S : DSSliceMap c L) (hS : SliceArakawa S)
    (hσ : VirSymbol c R t) (r : ℕ) : EvalFunctional L R t r := by
  obtain ⟨σ, hI, hlow, hword⟩ := hσ
  exact ⟨lam S σ r, fun y hy => lam_maxIdeal S hS hI r hy, fun y hy => lam_lower S hlow r hy,
    fun w hw => hw ▸ lam_word S hlow hword w⟩

/-- Detection from the slice map. -/
theorem modelDetects_of_dsSlice (S : DSSliceMap c L) (hS : SliceArakawa S)
    (hσ : VirSymbol c R t) : ModelDetects L R t :=
  modelDetects_iff_evalFunctional.mpr (evalFunctional_of_dsSlice S hS hσ)

/-- The slice functionals also form a coinvariant (Drinfeld–Sokolov-shaped) family. -/
theorem coinvEvalFamily_of_dsSlice (S : DSSliceMap c L) (hS : SliceArakawa S)
    (hσ : VirSymbol c R t) : CoinvEvalFamily L R t := by
  obtain ⟨σ, hI, hlow, hword⟩ := hσ
  refine ⟨fun r => lam S σ r, fun r y hy => lam_maxIdeal S hS hI r hy,
    fun r y hy => lam_lower S hlow r hy, fun r y => ?_, fun r j y => ?_,
    fun w _ => lam_word S hlow hword w⟩
  · push_cast; exact lam_f_one S σ r y
  · exact lam_f_high S σ _ j y

end Slice

/-! ## §3  The boundary level -/

/-- **Detection at the boundary index `m+1` from the slice map**: the leading-symbol maps of
`M(2, 2m+3)` are proved (`virSymbol_twoSeries`), so only the slice map into `Vir^{c_{2,2m+3}}`
and its Arakawa property remain. -/
theorem twoSeriesModelDetects_of_dsSlice (m : ℕ)
    (S : DSSliceMap (twoSeriesLevels m).c (twoSeriesLevels (m + 1))) (hS : SliceArakawa S) :
    TwoSeriesModelDetects (m + 1) :=
  modelDetects_of_dsSlice S hS (virSymbol_twoSeries m)

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`** (`n = m + 1 ≥ 1`), `#print axioms`-clean, conditional
on `hA`, a Drinfeld–Sokolov slice map `S : V^{k_n}(sl₂) → Vir^{c_{2,2n+1}}` with its Arakawa
property, and the jet-ideal Poincaré input `JetPoincareCoreT0 n`. -/
theorem twoSeries_gradedUnitary_of_dsSlice (m : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels (m + 1)))
      (affineRealStructure (twoSeriesLevels (m + 1))) (affineFlag (twoSeriesLevels (m + 1))))
    (S : DSSliceMap (twoSeriesLevels m).c (twoSeriesLevels (m + 1))) (hS : SliceArakawa S)
    (h : PoincareZero.JetPoincareCoreT0 (m + 1)) :
    VirGradedUnitary (twoSeriesLevels (m + 1)).c (targetRealStructure (twoSeriesLevels (m + 1))) :=
  twoSeries_gradedUnitary_of_strictModel_jetPoincareCoreT0 (m + 1) (by omega) hA
    (twoSeriesModelDetects_of_dsSlice m S hS) h

end

end VOA.TwoSeries.DSSlice
