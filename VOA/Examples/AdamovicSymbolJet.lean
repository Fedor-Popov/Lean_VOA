/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetStrictEndpoint

/-!
# The Adamović leading-symbol images of corrected generators, on the jet ring

The corrected filtration of `L_{-4/3}(sl₂)` is spanned by *corrected words*
`g¹_{(-n₁-1)} ⋯ gʳ_{(-n_r-1)} |0⟩` in the currents `e, f, h` and the Sugawara vector `T`
(`AffineVOA.CorrectedR.correctedWordState`). The filtered Adamović leading-symbol map sends

  `e ↦ X = u²,  f ↦ -Z = -v²,  h ↦ -2Y = -2uv,  T ↦ -J = -(u'v - uv')`,

a letter `(g, n)` to the `s^n` coefficient of the image series, and a word to the product.

* `curSer`, `letterSym`, `wordSym` — these images;
* `jetDer_letterSym_current` — the nonnegative mode derivations act on current letters by the
  `sl₂` structure constants: `D_{(a,m)} (b, n) = Σ_c f^{ab}_c (c, n - m)` (`0` if `m > n`);
* `jetDer_letterSym_sugawara` — and on stress letters by `D_{(a,m)} (T, n) = m (a, n + 1 - m)`
  (`0` if `m > n + 1`), the symbol of `[J^a_m, L_{-n-2}] = m J^a_{m-n-2}`;
* `wordSym_mem_jetImage`, `wordSym_isWeightedHomogeneous` — a length-`r` word lands in
  `A_r`, in jet weight `Σ (letter weights)`;
* `jetImage_le_span_wordSym` — `A_r` is spanned by the symbols of length-`r` words.

Everything is proved outright.
-/

namespace VOA.SymbolModel

open MvPolynomial
open VOA.AffineVOA.CorrectedR (Generator)
open VOA.AffineVOA (fabc)
open scoped Pointwise

noncomputable section

/-! ### The images -/

/-- The image series of the currents: `e ↦ X`, `f ↦ -Z`, `h ↦ -2Y`. -/
def curSer : Fin 3 → JetSer
  | 0 => xSer
  | 1 => -zSer
  | 2 => -(ySer + ySer)

/-- The symbol of a corrected letter `(g, n)`: the `s^n` coefficient of the image series
(`T ↦ -J`). -/
def letterSym : Generator × ℕ → JetPoly
  | (.current a, n) => PowerSeries.coeff n (curSer a)
  | (.sugawara, n) => PowerSeries.coeff n (-jSer)

/-- The symbol of a corrected word: the product of its letter symbols. -/
def wordSym (w : List (Generator × ℕ)) : JetPoly := (w.map letterSym).prod

@[simp] theorem wordSym_nil : wordSym [] = 1 := rfl

@[simp] theorem wordSym_cons (l : Generator × ℕ) (w : List (Generator × ℕ)) :
    wordSym (l :: w) = letterSym l * wordSym w := by
  simp [wordSym]

/-! ### Series identities -/

theorem coeff_sX_pow_mul (m n : ℕ) (F : JetSer) :
    PowerSeries.coeff n (sX ^ m * F) = if m ≤ n then PowerSeries.coeff (n - m) F else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']

theorem jetDer_coeff (k : Fin 3 × ℕ) (n : ℕ) (F : JetSer) :
    jetDer k (PowerSeries.coeff n F) = PowerSeries.coeff n (serD (jetDer k).toLinearMap F) := by
  rw [coeff_serD]; rfl

theorem coeff_curSer_one (n : ℕ) : PowerSeries.coeff n (curSer 1) = letterSym (.current 1, n) :=
  rfl

/-- The current-image series as a function of the colour. -/
theorem serD_curSer (a b : Fin 3) (m : ℕ) : ∃ G : JetSer,
    serD (jetDer (a, m)).toLinearMap (curSer b) = sX ^ m * G ∧
      ∀ j, PowerSeries.coeff j G = ∑ c, fabc a b c • letterSym (.current c, j) := by
  match a, b with
  | 0, 0 =>
    refine ⟨0, ?_, fun j => ?_⟩
    · change serD _ xSer = _
      rw [serD_xSer, serD_e_u]; ring
    · simp [fabc]
  | 0, 1 =>
    refine ⟨-(ySer + ySer), ?_, fun j => ?_⟩
    · change serD _ (-zSer) = _
      rw [serD_neg, serD_zSer, serD_e_v, ySer]; ring
    · simp [fabc, Fin.sum_univ_three, letterSym, curSer]
  | 0, 2 =>
    refine ⟨-(xSer + xSer), ?_, fun j => ?_⟩
    · change serD _ (-(ySer + ySer)) = _
      rw [serD_neg, serD_add, serD_ySer, serD_e_u, serD_e_v]; rw [xSer]; ring
    · simp [fabc, Fin.sum_univ_three, letterSym, curSer]; module
  | 1, 0 =>
    refine ⟨ySer + ySer, ?_, fun j => ?_⟩
    · change serD _ xSer = _
      rw [serD_xSer, serD_f_u]; rw [ySer]; ring
    · simp [fabc, Fin.sum_univ_three, letterSym, curSer]
  | 1, 1 =>
    refine ⟨0, ?_, fun j => ?_⟩
    · change serD _ (-zSer) = _
      rw [serD_neg, serD_zSer, serD_f_v]; ring
    · simp [fabc]
  | 1, 2 =>
    refine ⟨-(zSer + zSer), ?_, fun j => ?_⟩
    · change serD _ (-(ySer + ySer)) = _
      rw [serD_neg, serD_add, serD_ySer, serD_f_u, serD_f_v]; rw [zSer]; ring
    · simp [fabc, Fin.sum_univ_three, letterSym, curSer]; module
  | 2, 0 =>
    refine ⟨xSer + xSer, ?_, fun j => ?_⟩
    · change serD _ xSer = _
      rw [serD_xSer, serD_h_u]; rw [xSer]; ring
    · simp [fabc, Fin.sum_univ_three, letterSym, curSer]; module
  | 2, 1 =>
    refine ⟨zSer + zSer, ?_, fun j => ?_⟩
    · change serD _ (-zSer) = _
      rw [serD_neg, serD_zSer, serD_h_v]; rw [zSer]; ring
    · simp [fabc, Fin.sum_univ_three, letterSym, curSer]; module
  | 2, 2 =>
    refine ⟨0, ?_, fun j => ?_⟩
    · change serD _ (-(ySer + ySer)) = _
      rw [serD_neg, serD_add, serD_ySer, serD_h_u, serD_h_v]; ring
    · simp [fabc]

/-- **Current letters**: `D_{(a,m)} (b, n) = Σ_c f^{ab}_c (c, n - m)`, and `0` if `m > n`. -/
theorem jetDer_letterSym_current (a b : Fin 3) (m n : ℕ) :
    jetDer (a, m) (letterSym (.current b, n)) =
      if m ≤ n then ∑ c, fabc a b c • letterSym (.current c, n - m) else 0 := by
  obtain ⟨G, hG, hc⟩ := serD_curSer a b m
  change jetDer (a, m) (PowerSeries.coeff n (curSer b)) = _
  rw [jetDer_coeff, hG, coeff_sX_pow_mul]
  split_ifs
  · exact hc _
  · rfl

/-- The stress image series under the mode derivations: `D_{(a,m)} (-J) = (s^m)' · (image of a)`. -/
theorem serD_negJ (a : Fin 3) (m : ℕ) :
    serD (jetDer (a, m)).toLinearMap (-jSer) = dS (sX ^ m) * curSer a := by
  match a with
  | 0 =>
    change _ = _ * xSer
    rw [serD_neg, serD_jSer, serD_e_u, serD_e_v, map_zero, Derivation.leibniz, xSer,
      smul_eq_mul, smul_eq_mul]
    ring
  | 1 =>
    change _ = _ * -zSer
    rw [serD_neg, serD_jSer, serD_f_u, serD_f_v, map_zero, Derivation.leibniz, zSer,
      smul_eq_mul, smul_eq_mul]
    ring
  | 2 =>
    change _ = _ * -(ySer + ySer)
    rw [serD_neg, serD_jSer, serD_h_u, serD_h_v, map_neg, Derivation.leibniz,
      Derivation.leibniz, ySer, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

/-- **Stress letters**: `D_{(a,m)} (T, n) = m (a, n + 1 - m)`, and `0` if `m > n + 1`. -/
theorem jetDer_letterSym_sugawara (a : Fin 3) (m n : ℕ) :
    jetDer (a, m) (letterSym (.sugawara, n)) =
      if m ≤ n + 1 then (m : ℂ) • letterSym (.current a, n + 1 - m) else 0 := by
  change jetDer (a, m) (PowerSeries.coeff n (-jSer)) = _
  rw [jetDer_coeff, serD_negJ, dS_X_pow, smul_mul_assoc, map_nsmul]
  cases m with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel, coeff_sX_pow_mul]
    by_cases h : m ≤ n
    · rw [if_pos h, if_pos (by omega), Nat.add_sub_add_right, ← Nat.cast_smul_eq_nsmul ℂ]
      rfl
    · rw [if_neg h, if_neg (by omega), smul_zero]

/-! ### Jet weights -/

/-- A series whose `s^i` coefficient has jet weight `i + δ`. -/
def SerWH (F : JetSer) (δ : ℤ) : Prop :=
  ∀ i : ℕ, PowerSeries.coeff i F ∈ weightedHomogeneousSubmodule ℂ jetWt ((i : ℤ) + δ)

theorem serWH_colSer (b : Fin 2) : SerWH (colSer b) 0 := fun i => by
  rw [colSer, PowerSeries.coeff_mk, add_zero, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_X ℂ jetWt (b, i)

theorem serWH_add {F G : JetSer} {δ : ℤ} (hF : SerWH F δ) (hG : SerWH G δ) :
    SerWH (F + G) δ := fun i => by rw [map_add]; exact add_mem (hF i) (hG i)

theorem serWH_neg {F : JetSer} {δ : ℤ} (hF : SerWH F δ) : SerWH (-F) δ := fun i => by
  rw [map_neg]; exact neg_mem (hF i)

theorem serWH_sub {F G : JetSer} {δ : ℤ} (hF : SerWH F δ) (hG : SerWH G δ) :
    SerWH (F - G) δ := fun i => by rw [map_sub]; exact sub_mem (hF i) (hG i)

theorem serWH_mul {F G : JetSer} {δ ε : ℤ} (hF : SerWH F δ) (hG : SerWH G ε) :
    SerWH (F * G) (δ + ε) := fun i => by
  rw [PowerSeries.coeff_mul]
  refine Submodule.sum_mem _ fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have h := (hF p.1).mul (hG p.2)
  rw [mem_weightedHomogeneousSubmodule]
  convert h using 1
  rw [← hp]; push_cast; ring

theorem serWH_dS {F : JetSer} {δ : ℤ} (hF : SerWH F δ) : SerWH (dS F) (δ + 1) := fun i => by
  rw [PowerSeries.coeff_derivative]
  have h := hF (i + 1)
  rw [show ((i : ℤ) + (δ + 1)) = ((i + 1 : ℕ) : ℤ) + δ by push_cast; ring]
  rw [show (PowerSeries.coeff (i + 1) F * ((i : JetPoly) + 1)) =
    ((i : ℂ) + 1) • PowerSeries.coeff (i + 1) F by
      rw [MvPolynomial.smul_eq_C_mul, mul_comm]; congr 1; simp]
  exact Submodule.smul_mem _ _ h

theorem serWH_curSer (a : Fin 3) : SerWH (curSer a) 0 := by
  have hX : SerWH xSer 0 := by
    simpa using serWH_mul (serWH_colSer 0) (serWH_colSer 0)
  have hY : SerWH ySer 0 := by
    simpa using serWH_mul (serWH_colSer 0) (serWH_colSer 1)
  have hZ : SerWH zSer 0 := by
    simpa using serWH_mul (serWH_colSer 1) (serWH_colSer 1)
  match a with
  | 0 => exact hX
  | 1 => exact serWH_neg hZ
  | 2 => exact serWH_neg (serWH_add hY hY)

theorem serWH_negJ : SerWH (-jSer) 1 := by
  refine serWH_neg (serWH_sub ?_ ?_)
  · simpa using serWH_mul (serWH_dS (serWH_colSer 0)) (serWH_colSer 1)
  · simpa using serWH_mul (serWH_colSer 0) (serWH_dS (serWH_colSer 1))

/-- The jet weight of a corrected letter: `n` for a current, `n + 1` for the stress tensor. -/
def letterJetWt : Generator × ℕ → ℤ
  | (.current _, n) => n
  | (.sugawara, n) => n + 1

/-- The jet weight of a corrected word. -/
def wordJetWt (w : List (Generator × ℕ)) : ℤ := (w.map letterJetWt).sum

theorem letterSym_mem_weighted (l : Generator × ℕ) :
    letterSym l ∈ weightedHomogeneousSubmodule ℂ jetWt (letterJetWt l) := by
  obtain ⟨g, n⟩ := l
  cases g with
  | current a => simpa [letterJetWt] using serWH_curSer a n
  | sugawara => exact serWH_negJ n

/-- A word symbol is weighted homogeneous of the word's jet weight. -/
theorem wordSym_mem_weighted (w : List (Generator × ℕ)) :
    wordSym w ∈ weightedHomogeneousSubmodule ℂ jetWt (wordJetWt w) := by
  induction w with
  | nil =>
    rw [wordSym_nil, mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one ℂ jetWt
  | cons l w ih =>
    rw [wordSym_cons, mem_weightedHomogeneousSubmodule]
    have h := (letterSym_mem_weighted l).mul ih
    simpa [wordJetWt] using h

/-! ### The polynomial image -/

theorem letterSym_mem_genSpan (l : Generator × ℕ) : letterSym l ∈ genSpan := by
  have hg : ∀ g n, genCoeff g n ∈ genSpan := fun g n => Submodule.subset_span ⟨(g, n), rfl⟩
  obtain ⟨g, n⟩ := l
  cases g with
  | current a =>
    match a with
    | 0 => exact hg 0 n
    | 1 =>
      change PowerSeries.coeff n (-zSer) ∈ genSpan
      rw [map_neg]; exact neg_mem (hg 2 n)
    | 2 =>
      change PowerSeries.coeff n (-(ySer + ySer)) ∈ genSpan
      rw [map_neg, map_add]; exact neg_mem (add_mem (hg 1 n) (hg 1 n))
  | sugawara =>
    change PowerSeries.coeff n (-jSer) ∈ genSpan
    rw [map_neg]; exact neg_mem (hg 3 n)

/-- A length-`r` word symbol lies in `A_r`. -/
theorem wordSym_mem_jetImage (w : List (Generator × ℕ)) : wordSym w ∈ jetImage w.length := by
  induction w with
  | nil =>
    rw [wordSym_nil, jetImage, List.length_nil, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | cons l w ih =>
    rw [wordSym_cons, jetImage, List.length_cons, pow_succ']
    exact Submodule.mul_mem_mul (letterSym_mem_genSpan l) ih

/-- The generator coefficients are multiples of letter symbols. -/
theorem genCoeff_eq_smul_letterSym (g : Fin 4) (n : ℕ) :
    ∃ (c : ℂ) (l : Generator × ℕ), genCoeff g n = c • letterSym l := by
  match g with
  | 0 => exact ⟨1, (.current 0, n), by rw [one_smul]; rfl⟩
  | 1 =>
    refine ⟨-(1 / 2), (.current 2, n), ?_⟩
    change PowerSeries.coeff n ySer = _ • PowerSeries.coeff n (-(ySer + ySer))
    rw [map_neg, map_add]; module
  | 2 =>
    refine ⟨-1, (.current 1, n), ?_⟩
    change PowerSeries.coeff n zSer = _ • PowerSeries.coeff n (-zSer)
    rw [map_neg]; module
  | 3 =>
    refine ⟨-1, (.sugawara, n), ?_⟩
    change PowerSeries.coeff n jSer = _ • PowerSeries.coeff n (-jSer)
    rw [map_neg]; module

/-- The symbols of the length-`r` words. -/
def wordSymSet (r : ℕ) : Set JetPoly :=
  {Q | ∃ w : List (Generator × ℕ), w.length = r ∧ wordSym w = Q}

/-- **`A_r` is spanned by the symbols of length-`r` words.** -/
theorem jetImage_le_span_wordSym (r : ℕ) : jetImage r ≤ Submodule.span ℂ (wordSymSet r) := by
  induction r with
  | zero =>
    rw [jetImage, pow_zero, Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨[], rfl, rfl⟩
  | succ r ih =>
    rw [jetImage, pow_succ']
    calc genSpan * genSpan ^ r ≤ genSpan * Submodule.span ℂ (wordSymSet r) :=
          mul_le_mul' le_rfl ih
      _ = Submodule.span ℂ ((Set.range fun p : Fin 4 × ℕ => genCoeff p.1 p.2) * wordSymSet r) :=
          Submodule.span_mul_span _ _ _
      _ ≤ Submodule.span ℂ (wordSymSet (r + 1)) := by
          rw [Submodule.span_le]
          rintro _ ⟨_, ⟨⟨g, n⟩, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
          obtain ⟨c, l, hc⟩ := genCoeff_eq_smul_letterSym g n
          simp only
          rw [hc, smul_mul_assoc, ← wordSym_cons]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l :: w, by simp [hw], rfl⟩)

end

end VOA.SymbolModel
