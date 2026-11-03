/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetFermionicIdentity

/-!
# Well-definedness of the Adamović word symbols, by cyclicity of the jet ring

This file proves `WordSymbolDescends r` for **every** `r`, with no free-field realization.

The argument works on the universal algebra `V = V^k(sl₂)` (any noncritical level `k` with
`k ∉ ℕ`) and any VOA ideal `I` that avoids conformal weight `0`, e.g. the maximal graded ideal.
Let `symMod r ⊆ V × ℂ[u_j, v_j]` be the span of the pairs `(|w⟩, wordSym w)`, `|w| = r`, plus
`F_{r-1} V × 0` (`AdamovicSymbolWords`).

1. **A functional detecting `f_{-1}^r|0⟩`.** Put `E = e_1`. For `(y, Q) ∈ symMod r`,

     `E^r y ≡ (-1)^r c_r · ev(Q) · |0⟩   (mod ⨆_{n ≠ 0} V_n)`,

   where `ev` is evaluation at the base point `(u, v) = (0, 1)` and
   `c_r = ∏_{i < r} (i+1)(k-i)` (`symMod_le_detect`). On a word, `ev(wordSym w)` is `(-1)^r` for
   `w = f_{-1}^r` and `0` otherwise; `E^r f_{-1}^r |0⟩ = c_r |0⟩` is the `sl₂`-triple
   `(e_1, h_0 + k, f_{-1})` computation (`e1_pow_fPow`); every other word is sent off weight `0`
   or into the weight-`0` space with nonzero `h_0`-charge, where it vanishes (`V_0 = ℂ|0⟩`).
2. **Detection on the ideal.** If moreover `y ∈ I`, then `E^r y ∈ I ⊆ ⨆_{n≠0} V_n`, hence
   `ev(Q) = 0` (`evalBase_eq_zero_of_mem`).
3. **Cyclicity.** `symMod r` is stable under the pair operators `(J^a_μ, D_{(a,μ)})`
   (`J_word_mem_symMod`) and `I` under `J^a_μ`; so every `ev(D_{l} Q)` vanishes, and
   `jet_cyclic` gives `Q = 0` (`symbol_eq_zero_of_mem`).
4. **Descent.** Therefore the image of `symMod r` in `L × ℂ[u_j, v_j]` is the graph of a linear
   map on `F_r L`, which is `WordSymbolDescends r` (`wordSymbolDescends`).

* `symbol_eq_zero_of_mem` — the symbol relation is single-valued modulo `I` (generic `k`);
* `wordSymbolDescends : ∀ r, WordSymbolDescends r` — proved outright at `k = -4/3`;
* `leeYang_gradedUnitary_of_affine` — **Affine GU ⇒ Lee–Yang GU**, conditional only on `hA`.
-/

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.ConcreteHodge VOA.LeeYangTransferAssembly Sl2CosetConcrete
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR VOA.VertexOperatorAlgebra
open AffineSl2GeneralRigidity MvPolynomial

noncomputable section

namespace Desc

/-! ### The `h_0`-charge of corrected words -/

/-- The `h_0`-charge of a current: `e ↦ 2`, `f ↦ -2`, `h ↦ 0`. -/
def curCharge : Fin 3 → ℤ := ![2, -2, 0]

/-- The `h_0`-charge of a corrected letter (`T` has charge `0`). -/
def letterCharge : Generator × ℕ → ℤ
  | (.current a, _) => curCharge a
  | (.sugawara, _) => 0

/-- The `h_0`-charge of a corrected word. -/
def wordCharge (w : List (Generator × ℕ)) : ℤ := (w.map letterCharge).sum

@[simp] theorem wordCharge_nil : wordCharge [] = 0 := rfl

@[simp] theorem wordCharge_cons (l : Generator × ℕ) (w : List (Generator × ℕ)) :
    wordCharge (l :: w) = letterCharge l + wordCharge w := by
  simp [wordCharge]

@[simp] theorem wordWt_nil : wordWt [] = 0 := rfl

@[simp] theorem wordWt_cons (l : Generator × ℕ) (w : List (Generator × ℕ)) :
    wordWt (l :: w) = letterWt l + wordWt w := by
  simp [wordWt]

/-- Weight plus charge of a word is at least minus its length, with equality only for
`f_{-1}^r|0⟩`. -/
theorem wt_add_charge (w : List (Generator × ℕ)) :
    -(w.length : ℤ) ≤ wordWt w + wordCharge w ∧
      (wordWt w + wordCharge w = -(w.length : ℤ) →
        w = List.replicate w.length (Generator.current 1, 0)) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨g, n⟩ := l
    simp only [wordWt_cons, wordCharge_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      List.replicate_succ, List.cons.injEq]
    cases g with
    | current a =>
      fin_cases a <;> simp only [letterWt, letterCharge, curCharge] <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
        refine ⟨by omega, fun h => ?_⟩
      · omega
      · refine ⟨?_, ih2 (by omega)⟩
        have : n = 0 := by omega
        subst this; rfl
      · omega
    | sugawara =>
      simp only [letterWt, letterCharge]
      exact ⟨by omega, fun h => by omega⟩

/-! ### Commutators with `h_0` -/

section Generic

variable (k : ℂ) (hk : k + 2 ≠ 0)

theorem h0_J (b : Fin 3) (m : ℤ) (x : WakModule k) :
    J k 2 0 (J k b m x) = J k b m (J k 2 0 x) + (curCharge b : ℂ) • J k b m x := by
  have h := LinearMap.congr_fun (current_comm k 2 b 0 m) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, Int.cast_zero, zero_mul, zero_smul, ite_self, add_zero] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  fin_cases b <;> simp [fabc, Fin.sum_univ_three, curCharge] <;> abel

theorem h0_word (w : List (Generator × ℕ)) :
    J k 2 0 (correctedWordState k hk w) = (wordCharge w : ℂ) • correctedWordState k hk w := by
  induction w with
  | nil =>
    rw [correctedWordState_nil, closed_vacuum, J_vacuum_nonneg k 2 le_rfl, wordCharge_nil,
      Int.cast_zero, zero_smul]
  | cons l w ih =>
    obtain ⟨g, n⟩ := l
    rw [correctedWordState_cons', wordCharge_cons, Int.cast_add]
    cases g with
    | current b =>
      rw [letterOp_current, h0_J, ih, map_smul]
      simp only [letterCharge]
      rw [add_smul]; abel
    | sugawara =>
      rw [letterOp_sugawara]
      have h := Vir.Lcomm_J_apply k hk (-(n : ℤ) - 2) 2 0 (correctedWordState k hk w)
      rw [neg_zero, Int.cast_zero, zero_smul, add_zero] at h
      rw [show J k 2 0 (mode (YA k hk (omegaA k)) ((-(n : ℤ) - 2) + 1)
          (correctedWordState k hk w)) =
          mode (YA k hk (omegaA k)) ((-(n : ℤ) - 2) + 1) (J k 2 0 (correctedWordState k hk w))
          from h.symm, ih, map_smul]
      simp [letterCharge]

/-- `e_1` raises the `h_0`-charge by two. -/
theorem h0_e1_pow (r : ℕ) {z : WakModule k} {c : ℂ} (hz : J k 2 0 z = c • z) :
    J k 2 0 ((J k 0 1 ^ r) z) = (c + 2 * r) • (J k 0 1 ^ r) z := by
  induction r with
  | zero => simpa using hz
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, h0_J, ih, map_smul]
    simp only [curCharge, Matrix.cons_val_zero]
    push_cast
    rw [← add_smul]; congr 1; ring

theorem e1_pow_mem_grading (r : ℕ) {n : ℤ} {z : WakModule k} (hz : z ∈ gradingZA k n) :
    (J k 0 1 ^ r) z ∈ gradingZA k (n - r) := by
  induction r with
  | zero => simpa using hz
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := J_mem_gradingZA k 0 1 _ ih
    convert h using 2
    push_cast; ring

/-- The nonzero-weight part `⨆_{n ≠ 0} V_n`. -/
def offZero : Submodule ℂ (WakModule k) :=
  ⨆ (n : ℤ) (_ : n ≠ 0), (affineSl2VOA_closed k hk).grading n

theorem mem_offZero {n : ℤ} (hn : n ≠ 0) {z : WakModule k}
    (hz : z ∈ (affineSl2VOA_closed k hk).grading n) : z ∈ offZero k hk :=
  (le_iSup₂ (f := fun (m : ℤ) (_ : m ≠ 0) => (affineSl2VOA_closed k hk).grading m) n hn) hz

/-- A weight-zero vector of nonzero `h_0`-charge vanishes (`V_0 = ℂ|0⟩`). -/
theorem eq_zero_of_grading_zero {z : WakModule k} {c : ℂ} (hc : c ≠ 0)
    (hz0 : z ∈ (affineSl2VOA_closed k hk).grading 0) (hz : J k 2 0 z = c • z) : z = 0 := by
  rw [(affineSl2VOA_closed k hk).vacuum_grade, Submodule.mem_span_singleton] at hz0
  obtain ⟨t, rfl⟩ := hz0
  rw [map_smul, closed_vacuum, J_vacuum_nonneg k 2 le_rfl, smul_zero] at hz
  exact (smul_eq_zero.mp hz.symm).resolve_left hc

/-- `e_1^r` sends every word other than `f_{-1}^r|0⟩` (of length `≤ r`) off weight zero. -/
theorem e1_pow_word_mem_offZero (r : ℕ) (w : List (Generator × ℕ)) (hw : w.length ≤ r)
    (hne : w ≠ List.replicate r (Generator.current 1, 0)) :
    (J k 0 1 ^ r) (correctedWordState k hk w) ∈ offZero k hk := by
  have hgr : (J k 0 1 ^ r) (correctedWordState k hk w) ∈
      (affineSl2VOA_closed k hk).grading (wordWt w - r) :=
    e1_pow_mem_grading k r (correctedWordState_mem_grading k hk w)
  by_cases hwt : wordWt w - r = 0
  · have hch : (wordCharge w : ℂ) + 2 * r ≠ 0 := by
      obtain ⟨h1, h2⟩ := wt_add_charge w
      intro h
      have h' : wordCharge w + 2 * (r : ℤ) = 0 := by exact_mod_cast h
      have hlen : (w.length : ℤ) = r := by omega
      apply hne
      have := h2 (by omega)
      rw [this, show w.length = r by exact_mod_cast hlen]
    rw [hwt] at hgr
    rw [eq_zero_of_grading_zero k hk hch hgr (h0_e1_pow k r (h0_word k hk w))]
    exact Submodule.zero_mem _
  · exact mem_offZero k hk hwt hgr

/-! ### The `sl₂`-triple `(e_1, h_0 + k, f_{-1})` on the vacuum -/

/-- `c_r = ∏_{i < r} (i+1)(k-i)`. -/
def cf (r : ℕ) : ℂ := ∏ i ∈ Finset.range r, (((i : ℂ) + 1) * (k - i))

theorem e1_f (x : WakModule k) :
    J k 0 1 (J k 1 (-1) x) = J k 1 (-1) (J k 0 1 x) + J k 2 0 x + k • x := by
  have h := LinearMap.congr_fun (current_comm k 0 1 1 (-1)) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  simp [fabc, Fin.sum_univ_three, kappa]
  abel

theorem h0_fPow (m : ℕ) :
    J k 2 0 ((J k 1 (-1) ^ m) (vacuumA k)) = (-(2 * m : ℂ)) • (J k 1 (-1) ^ m) (vacuumA k) := by
  induction m with
  | zero => simp [J_vacuum_nonneg k 2 le_rfl]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, h0_J, ih, map_smul]
    simp only [curCharge]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← add_smul]; congr 1; push_cast; ring

theorem e1_fPow_succ (m : ℕ) :
    J k 0 1 ((J k 1 (-1) ^ (m + 1)) (vacuumA k)) =
      (((m : ℂ) + 1) * (k - m)) • (J k 1 (-1) ^ m) (vacuumA k) := by
  induction m with
  | zero =>
    simp [e1_f, J_vacuum_nonneg k 0 (by norm_num : (0 : ℤ) ≤ 1), J_vacuum_nonneg k 2 le_rfl]
  | succ m ih =>
    have hF : J k 1 (-1) ((J k 1 (-1) ^ m) (vacuumA k)) = (J k 1 (-1) ^ (m + 1)) (vacuumA k) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [pow_succ' _ (m + 1), Module.End.mul_apply, e1_f, ih, map_smul, h0_fPow, hF,
      ← add_smul, ← add_smul]
    congr 1
    push_cast; ring

theorem e1_pow_fPow (m : ℕ) :
    (J k 0 1 ^ m) ((J k 1 (-1) ^ m) (vacuumA k)) = cf k m • vacuumA k := by
  induction m with
  | zero => simp [cf]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, e1_fPow_succ, map_smul, ih, smul_smul, cf, cf,
      Finset.prod_range_succ, mul_comm]

theorem cf_ne_zero (hkN : ∀ i : ℕ, k ≠ i) (r : ℕ) : cf k r ≠ 0 := by
  rw [cf, Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero ?_ (sub_ne_zero.mpr (hkN i))
  exact_mod_cast Nat.succ_ne_zero i

theorem correctedWordState_fPow (m : ℕ) :
    correctedWordState k hk (List.replicate m (Generator.current 1, 0)) =
      (J k 1 (-1) ^ m) (vacuumA k) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, correctedWordState_cons', letterOp_current, ih, pow_succ',
      Module.End.mul_apply]
    norm_num

/-! ### Evaluation of the word symbols at the base point -/

/-- `evalBase` as a ring hom. -/
abbrev evalBaseR : JetPoly →+* ℂ := evalBase

theorem evalBase_coeff (f : JetSer) (n : ℕ) :
    evalBase (PowerSeries.coeff n f) = PowerSeries.coeff n (PowerSeries.map evalBaseR f) := by
  rw [PowerSeries.coeff_map]; rfl

theorem map_evalBase_colSer_zero : PowerSeries.map evalBaseR (colSer 0) = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk]
  simp [evalBase, baseVal]

theorem map_evalBase_colSer_one : PowerSeries.map evalBaseR (colSer 1) = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  simp [evalBase, baseVal]

theorem map_evalBase_dS (f : JetSer) :
    PowerSeries.map evalBaseR (dS f) = PowerSeries.derivative ℂ (PowerSeries.map evalBaseR f) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

theorem evalBase_letterSym (l : Generator × ℕ) :
    evalBase (letterSym l) = if l = (Generator.current 1, 0) then -1 else 0 := by
  obtain ⟨g, n⟩ := l
  cases g with
  | current a =>
    change evalBase (PowerSeries.coeff n (curSer a)) = _
    rw [evalBase_coeff]
    fin_cases a
    · simp [curSer, xSer, map_evalBase_colSer_zero]
    · simp only [curSer, zSer, map_neg, map_mul, map_evalBase_colSer_one, mul_one,
        PowerSeries.coeff_one]
      by_cases hn : n = 0 <;> simp [hn]
    · simp [curSer, ySer, map_evalBase_colSer_zero]
  | sugawara =>
    change evalBase (PowerSeries.coeff n (-jSer)) = _
    rw [evalBase_coeff]
    simp [jSer, map_evalBase_dS, map_evalBase_colSer_zero, map_evalBase_colSer_one]

theorem evalBase_wordSym (w : List (Generator × ℕ)) :
    evalBase (wordSym w) =
      if w = List.replicate w.length (Generator.current 1, 0) then (-1) ^ w.length else 0 := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [wordSym_cons, map_mul, ih, evalBase_letterSym]
    simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
    by_cases hl : l = (Generator.current 1, 0)
    · simp only [hl, true_and, if_true]
      split_ifs <;> ring
    · simp [hl]

/-! ### The detecting functional -/

/-- `(y, Q) ↦ e_1^r y - (-1)^r c_r ev(Q) |0⟩`. -/
def detect (r : ℕ) : (WakModule k × JetPoly) →ₗ[ℂ] WakModule k :=
  (J k 0 1 ^ r) ∘ₗ LinearMap.fst ℂ _ _ -
    (LinearMap.smulRight evalBase.toLinearMap (((-1) ^ r * cf k r) • vacuumA k)) ∘ₗ
      LinearMap.snd ℂ _ _

theorem detect_apply (r : ℕ) (p : WakModule k × JetPoly) :
    detect k r p = (J k 0 1 ^ r) p.1 - evalBase p.2 • (((-1) ^ r * cf k r) • vacuumA k) := rfl

theorem lowerP_le_detect (r : ℕ) {y : WakModule k} (hy : y ∈ lowerP k hk r) :
    (J k 0 1 ^ r) y ∈ offZero k hk := by
  cases r with
  | zero =>
    rw [lowerP, Submodule.mem_bot] at hy
    rw [hy, map_zero]; exact Submodule.zero_mem _
  | succ q =>
    change y ∈ correctedAffineRPiece k hk q at hy
    rw [correctedAffineRPiece] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨w, hw⟩, rfl⟩ := hx
      refine e1_pow_word_mem_offZero k hk (q + 1) w (by omega) ?_
      intro h
      have := congrArg List.length h
      simp at this; omega
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- On `symMod r`, `e_1^r y ≡ (-1)^r c_r ev(Q) |0⟩` modulo the nonzero weights. -/
theorem symMod_le_detect (r : ℕ) :
    symMod k hk r ≤ (offZero k hk).comap (detect k r) := by
  refine sup_le ?_ ?_
  · rw [symPairs, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, detect_apply]
    dsimp only
    rw [evalBase_wordSym]
    by_cases hf : w = List.replicate w.length (Generator.current 1, 0)
    · rw [if_pos hf, hf, correctedWordState_fPow, List.length_replicate, hw, e1_pow_fPow,
        smul_smul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
        one_pow, one_mul, sub_self]
      exact Submodule.zero_mem _
    · rw [if_neg hf, zero_smul, sub_zero]
      refine e1_pow_word_mem_offZero k hk r w hw.le ?_
      intro h; apply hf; rw [hw]; exact h
  · rintro ⟨y, p⟩ ⟨hy, hp⟩
    change p ∈ (⊥ : Submodule ℂ JetPoly) at hp
    rw [Submodule.mem_bot] at hp
    subst hp
    rw [Submodule.mem_comap, detect_apply]
    dsimp only
    rw [map_zero, zero_smul, sub_zero]
    exact lowerP_le_detect k hk r hy

/-! ### The ideal -/

variable {k hk} {I : Submodule ℂ (WakModule k)}

theorem J_mem_ideal (hI : (affineSl2VOA_closed k hk).IsIdeal I) (a : Fin 3) (m : ℤ)
    {y : WakModule k} (hy : y ∈ I) : J k a m y ∈ I := by
  rw [← smul_currentState_eq_J k hk a m y]
  exact hI _ _ _ hy

theorem e1_pow_mem_ideal (hI : (affineSl2VOA_closed k hk).IsIdeal I) (r : ℕ)
    {y : WakModule k} (hy : y ∈ I) : (J k 0 1 ^ r) y ∈ I := by
  induction r with
  | zero => simpa using hy
  | succ r ih => rw [pow_succ', Module.End.mul_apply]; exact J_mem_ideal hI 0 1 ih

/-- **Detection**: on `symMod r`, membership of `y` in an ideal avoiding weight zero forces
`ev(Q) = 0`. -/
theorem evalBase_eq_zero_of_mem (hkN : ∀ i : ℕ, k ≠ i)
    (hI : (affineSl2VOA_closed k hk).IsIdeal I) (hIN : I ≤ offZero k hk) (r : ℕ)
    {y : WakModule k} {Q : JetPoly} (hyQ : (y, Q) ∈ symMod k hk r) (hy : y ∈ I) :
    evalBase Q = 0 := by
  have h1 : detect k r (y, Q) ∈ offZero k hk := symMod_le_detect k hk r hyQ
  have h2 : (J k 0 1 ^ r) y ∈ offZero k hk := hIN (e1_pow_mem_ideal hI r hy)
  rw [detect_apply] at h1
  have h3 : evalBase Q • (((-1) ^ r * cf k r) • vacuumA k) ∈ offZero k hk := by
    have := sub_mem h2 h1
    simpa using this
  have h4 : evalBase Q • (((-1) ^ r * cf k r) • vacuumA k) ∈
      (affineSl2VOA_closed k hk).grading 0 :=
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (affineSl2VOA_closed k hk).vacuum_mem)
  have hd : Disjoint ((affineSl2VOA_closed k hk).grading 0) (offZero k hk) :=
    iSupIndep_def.mp (affineSl2VOA_closed k hk).isInternal.submodule_iSupIndep 0
  have h5 := Submodule.disjoint_def.mp hd _ h4 h3
  rw [smul_smul] at h5
  have hvac : vacuumA k ≠ 0 := closed_vacuum_ne_zero k hk
  have hc : (-1 : ℂ) ^ r * cf k r ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (cf_ne_zero k hkN r)
  have := (smul_eq_zero.mp h5).resolve_right hvac
  exact (mul_eq_zero.mp this).resolve_right hc

/-! ### Cyclicity -/

theorem symMod_J (a : Fin 3) (μ : ℕ) (r : ℕ) {y : WakModule k} {Q : JetPoly}
    (hyQ : (y, Q) ∈ symMod k hk r) : (J k a μ y, jetDer (a, μ) Q) ∈ symMod k hk r := by
  let P : (WakModule k × JetPoly) →ₗ[ℂ] (WakModule k × JetPoly) :=
    LinearMap.prodMap (J k a μ) (jetDer (a, μ)).toLinearMap
  have hle : symMod k hk r ≤ (symMod k hk r).comap P := by
    refine sup_le ?_ ?_
    · rw [symPairs, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := J_word_mem_symMod k hk a μ w
      rw [hw] at h
      exact h
    · rintro ⟨z, p⟩ ⟨hz, hp⟩
      change p ∈ (⊥ : Submodule ℂ JetPoly) at hp
      rw [Submodule.mem_bot] at hp
      subst hp
      rw [Submodule.mem_comap]
      change (J k a μ z, jetDer (a, μ) 0) ∈ symMod k hk r
      rw [map_zero]
      exact lower_mem_symMod k hk (J_nonneg_lowerP k hk a (by positivity) hz)
  exact hle hyQ

/-- The mode word `J_{l}` on the universal algebra. -/
def jWord (l : List (Fin 3 × ℕ)) : Module.End ℂ (WakModule k) :=
  (l.map fun q => J k q.1 q.2).prod

theorem symMod_word (l : List (Fin 3 × ℕ)) (r : ℕ) {y : WakModule k} {Q : JetPoly}
    (hyQ : (y, Q) ∈ symMod k hk r) :
    (jWord (k := k) l y, VOA.CyclicEval.word jetRho l Q) ∈ symMod k hk r := by
  induction l with
  | nil => simpa [jWord, VOA.CyclicEval.word] using hyQ
  | cons q l ih =>
    have h := symMod_J (hk := hk) q.1 q.2 r ih
    simpa [jWord, VOA.CyclicEval.word, Module.End.mul_apply] using h

theorem jWord_mem (hI : (affineSl2VOA_closed k hk).IsIdeal I) (l : List (Fin 3 × ℕ))
    {y : WakModule k} (hy : y ∈ I) : jWord (k := k) l y ∈ I := by
  induction l with
  | nil => simpa [jWord] using hy
  | cons q l ih =>
    simp only [jWord, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    exact J_mem_ideal hI q.1 q.2 ih

/-- **The symbol relation is single-valued modulo the ideal**: if `(y, Q) ∈ symMod r` and
`y ∈ I` (an ideal avoiding weight zero), then `Q = 0`. -/
theorem symbol_eq_zero_of_mem (hkN : ∀ i : ℕ, k ≠ i)
    (hI : (affineSl2VOA_closed k hk).IsIdeal I) (hIN : I ≤ offZero k hk) (r : ℕ)
    {y : WakModule k} {Q : JetPoly} (hyQ : (y, Q) ∈ symMod k hk r) (hy : y ∈ I) : Q = 0 :=
  jet_cyclic Q fun l =>
    evalBase_eq_zero_of_mem hkN hI hIN r (symMod_word l r hyQ) (jWord_mem hI l hy)

end Generic

/-! ### Specialization to `L_{-4/3}(sl₂)` -/

theorem aLevel_ne_nat (i : ℕ) : ALevel ≠ (i : ℂ) := by
  intro h
  have h' : ALevel = ((-4 / 3 : ℝ) : ℂ) := by
    simp only [ALevel, AffineSl2BoundarySingularFamily.level,
      AffineSl2BoundarySingularFamily.denominator]
    push_cast; norm_num
  rw [h', show ((i : ℂ)) = ((i : ℝ) : ℂ) by push_cast; rfl] at h
  have := Complex.ofReal_injective h
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

theorem imax_isIdeal : (affineSl2VOA_closed ALevel aNoncritical).IsIdeal Imax :=
  QuotVOA.maxGradedIdeal_isIdeal _

theorem imax_le_offZero : Imax ≤ offZero ALevel aNoncritical :=
  QuotVOA.le_iSup_ne_zero (QuotVOA.maxGradedIdeal_isGradedIdeal _)
    (QuotVOA.vacuum_not_mem_maxGradedIdeal _ (closed_vacuum_ne_zero _ _))

/-- The symbol relation, pushed to the simple quotient. -/
def graphL (r : ℕ) : Submodule ℂ (ASpace × JetPoly) :=
  (symMod ALevel aNoncritical r).map (LinearMap.prodMap Imax.mkQ LinearMap.id)

theorem graphL_single (r : ℕ) : ∀ (x : ASpace × JetPoly), x ∈ graphL r → x.1 = 0 → x.2 = 0 := by
  rintro _ ⟨⟨y, Q⟩, hyQ, rfl⟩ h0
  simp only [LinearMap.prodMap_apply, LinearMap.id_apply] at h0 ⊢
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  exact symbol_eq_zero_of_mem aLevel_ne_nat imax_isIdeal imax_le_offZero r hyQ h0

theorem aFil_le_domain (r : ℕ) : aFil r ≤ (graphL r).map (LinearMap.fst ℂ _ _) := by
  rw [aFil_eq_map, UP, correctedAffineRPiece, Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  rcases hw.lt_or_eq with hlt | heq
  · refine ⟨(Imax.mkQ (correctedWordState ALevel aNoncritical w), 0),
      ⟨(correctedWordState ALevel aNoncritical w, 0), lower_mem_symMod _ _
        (word_mem_lowerP _ _ w hlt), rfl⟩, rfl⟩
  · refine ⟨(Imax.mkQ (correctedWordState ALevel aNoncritical w), wordSym w),
      ⟨(correctedWordState ALevel aNoncritical w, wordSym w), ?_, rfl⟩, rfl⟩
    have h := word_mem_symMod ALevel aNoncritical w
    rwa [heq] at h

theorem graphL_apply_eq (r : ℕ) {x : ASpace} (hx : x ∈ (graphL r).map (LinearMap.fst ℂ _ _))
    {Q : JetPoly} (hxQ : (x, Q) ∈ graphL r) : (graphL r).toLinearPMap ⟨x, hx⟩ = Q := by
  have h1 := Submodule.mem_graph_toLinearPMap (graphL_single r) ⟨x, hx⟩
  have h2 := sub_mem h1 hxQ
  have h3 := graphL_single r _ h2 (by simp)
  simpa [sub_eq_zero] using h3

/-- **`WordSymbolDescends r` for every `r`, proved outright.** -/
def wordSymbolDescends (r : ℕ) : WordSymbolDescends r where
  σ := (graphL r).toLinearPMap.toFun ∘ₗ Submodule.inclusion (aFil_le_domain r)
  lower x hx := by
    change (graphL r).toLinearPMap ⟨(x : ASpace), aFil_le_domain r x.2⟩ = 0
    apply graphL_apply_eq
    cases r with
    | zero =>
      change (x : ASpace) ∈ (⊥ : Submodule ℂ ASpace) at hx
      rw [Submodule.mem_bot] at hx
      rw [hx]; exact Submodule.zero_mem _
    | succ q =>
      change (x : ASpace) ∈ aFil q at hx
      rw [aFil_eq_map] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      refine ⟨(z, 0), lower_mem_symMod _ _ hz, ?_⟩
      simp [hzx]
  word w hw := by
    change (graphL r).toLinearPMap ⟨_, aFil_le_domain r (wordClass w hw.le).2⟩ = wordSym w
    apply graphL_apply_eq
    refine ⟨(correctedWordState ALevel aNoncritical w, wordSym w), ?_, rfl⟩
    have h := word_mem_symMod ALevel aNoncritical w
    rwa [hw] at h

end Desc

/-- **Affine GU ⇒ Lee–Yang GU**, conditional only on `hA`: the word-symbol descent is
proved (`Desc.wordSymbolDescends`). -/
theorem leeYang_gradedUnitary_of_affine
    (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_wordSymbols_jet hA fun r => Desc.wordSymbolDescends (r + 2)

end

end VOA.AdamovicSymbol
