/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.AdamovicSymbolJet

/-!
# The nonnegative current modes on corrected words, modulo lower corrected degree

On the universal affine VOA `V^k(sl₂)` (any noncritical level), pair each corrected word state
with its Adamović symbol: `(w ↦ (|w⟩, wordSym w))`. Let `symMod q ⊆ V^k × ℂ[u_j, v_j]` be the span
of the pairs of length-`q` words, plus `F_{q-1} × 0`.

* `prepend_symMod` — prepending a letter maps `symMod q` into `symMod (q+1)`;
* `J_word_mem_symMod` — **the commutator calculus**: for every word `w` and nonnegative mode
  `J^a_μ`, the pair `(J^a_μ |w⟩, D_{(a,μ)} (wordSym w))` lies in `symMod |w|`. That is,
  modulo lower corrected degree, `J^a_μ` acts on corrected words exactly as the jet derivation
  `D_{(a,μ)}` acts on their symbols. The induction uses the affine commutator
  `[J^a_μ, J^b_{-n-1}] = Σ_c f^{ab}_c J^c_{μ-n-1} + central`, Virasoro–current covariance
  `[J^a_μ, L_{-n-2}] = μ J^a_{μ-n-2}`, and the letter formulas of `AdamovicSymbolJet`.

Everything is proved outright, at every noncritical level.
-/

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.ConcreteHodge
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR
open VOA.VertexOperatorAlgebra

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- `F_{q-1}` of the universal corrected filtration (`F_{-1} = 0`). -/
def lowerP : ℕ → Submodule ℂ (WakModule k)
  | 0 => ⊥
  | q + 1 => correctedAffineRPiece k hk q

/-- The span of the (state, symbol) pairs of length-`q` words. -/
def symPairs (q : ℕ) : Submodule ℂ (WakModule k × JetPoly) :=
  Submodule.span ℂ
    {x | ∃ w : List (Generator × ℕ), w.length = q ∧ (correctedWordState k hk w, wordSym w) = x}

/-- Pairs of length-`q` words, modulo `F_{q-1} × 0`. -/
def symMod (q : ℕ) : Submodule ℂ (WakModule k × JetPoly) :=
  symPairs k hk q ⊔ (lowerP k hk q).prod ⊥

theorem word_mem_symMod (w : List (Generator × ℕ)) :
    (correctedWordState k hk w, wordSym w) ∈ symMod k hk w.length :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨w, rfl, rfl⟩)

theorem lower_mem_symMod {q : ℕ} {y : WakModule k} (hy : y ∈ lowerP k hk q) :
    (y, (0 : JetPoly)) ∈ symMod k hk q :=
  Submodule.mem_sup_right ⟨hy, Submodule.zero_mem _⟩

/-- The creation operator of a letter. -/
def letterOp (l : Generator × ℕ) : Module.End ℂ (WakModule k) :=
  mode ((affineSl2VOA_closed k hk).Y (generatorState k hk l.1)) (-(l.2 : ℤ) - 1)

theorem correctedWordState_cons' (l : Generator × ℕ) (w : List (Generator × ℕ)) :
    correctedWordState k hk (l :: w) = letterOp k hk l (correctedWordState k hk w) := rfl

theorem generatorState_mem_piece_one (g : Generator) :
    generatorState k hk g ∈ correctedAffineRPiece k hk 1 := by
  cases g with
  | current a => exact currentState_mem_piece_one k hk a
  | sugawara => exact conformalVector_mem_piece_one k hk

theorem letterOp_lowerP (l : Generator × ℕ) {q : ℕ} {y : WakModule k}
    (hy : y ∈ lowerP k hk q) : letterOp k hk l y ∈ lowerP k hk (q + 1) := by
  cases q with
  | zero =>
    rw [lowerP, Submodule.mem_bot] at hy
    rw [hy, map_zero]; exact Submodule.zero_mem _
  | succ q =>
    have h := mode_piece_mem_piece_add k hk (generatorState_mem_piece_one k hk l.1) hy
      (-(l.2 : ℤ) - 1)
    rw [add_comm] at h
    exact h

/-- Prepending a letter, on pairs. -/
def prepend (l : Generator × ℕ) : (WakModule k × JetPoly) →ₗ[ℂ] (WakModule k × JetPoly) :=
  LinearMap.prodMap (letterOp k hk l) (LinearMap.mulLeft ℂ (letterSym l))

/-- Prepending a letter maps `symMod q` into `symMod (q+1)`. -/
theorem prepend_symMod (l : Generator × ℕ) {q : ℕ} {x : WakModule k × JetPoly}
    (hx : x ∈ symMod k hk q) : prepend k hk l x ∈ symMod k hk (q + 1) := by
  have hle : symMod k hk q ≤ (symMod k hk (q + 1)).comap (prepend k hk l) := by
    refine sup_le ?_ ?_
    · rw [symPairs, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := word_mem_symMod k hk (l :: w)
      rw [List.length_cons, hw, wordSym_cons, correctedWordState_cons'] at h
      exact h
    · rintro ⟨y, p⟩ ⟨hy, hp⟩
      change p ∈ (⊥ : Submodule ℂ JetPoly) at hp
      rw [Submodule.mem_bot] at hp
      subst hp
      rw [Submodule.mem_comap]
      change (letterOp k hk l y, letterSym l * 0) ∈ symMod k hk (q + 1)
      rw [mul_zero]
      exact lower_mem_symMod k hk (letterOp_lowerP k hk l hy)
  exact hle hx

theorem J_nonneg_lowerP (a : Fin 3) {μ : ℤ} (hμ : 0 ≤ μ) {q : ℕ} {y : WakModule k}
    (hy : y ∈ lowerP k hk q) : J k a μ y ∈ lowerP k hk q := by
  cases q with
  | zero =>
    rw [lowerP, Submodule.mem_bot] at hy
    rw [hy, map_zero]; exact Submodule.zero_mem _
  | succ q => exact correctedPiece_J_nonneg k hk a hμ hy

/-! ### The commutator calculus -/

theorem letterOp_current (b : Fin 3) (n : ℕ) (x : WakModule k) :
    letterOp k hk (.current b, n) x = J k b (-(n : ℤ) - 1) x :=
  smul_currentState_eq_J k hk b _ x

theorem letterOp_sugawara (n : ℕ) (x : WakModule k) :
    letterOp k hk (.sugawara, n) x = mode (YA k hk (omegaA k)) ((-(n : ℤ) - 2) + 1) x := by
  rw [show (-(n : ℤ) - 2) + 1 = -(n : ℤ) - 1 by ring]
  rfl

/-- **The commutator calculus on corrected words.** -/
theorem J_word_mem_symMod (a : Fin 3) (μ : ℕ) :
    ∀ w : List (Generator × ℕ),
      (J k a μ (correctedWordState k hk w), jetDer (a, μ) (wordSym w)) ∈ symMod k hk w.length
  | [] => by
      rw [correctedWordState_nil, closed_vacuum, J_vacuum_nonneg k a (by positivity),
        wordSym_nil, Derivation.map_one_eq_zero]
      exact Submodule.zero_mem _
  | (.current b, n) :: rest => by
      have ih := J_word_mem_symMod a μ rest
      set x := correctedWordState k hk rest with hx
      have hxP : x ∈ correctedAffineRPiece k hk rest.length :=
        correctedWordState_mem_piece k hk rest le_rfl
      rw [correctedWordState_cons', letterOp_current, wordSym_cons, Derivation.leibniz,
        smul_eq_mul, smul_eq_mul]
      have hcomm := LinearMap.congr_fun (current_comm k a b μ (-(n : ℤ) - 1)) x
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at hcomm
      rw [sub_eq_iff_eq_add] at hcomm
      rw [hcomm, List.length_cons]
      have hP := prepend_symMod k hk (.current b, n) ih
      suffices hA : (∑ c, fabc a b c • J k c (↑μ + (-↑n - 1)) x +
            (if (μ : ℤ) + (-↑n - 1) = 0 then (((μ : ℤ) : ℂ) * k * kappa a b) • LinearMap.id
              else 0) x, wordSym rest * jetDer (a, μ) (letterSym (Generator.current b, n))) ∈
            symMod k hk (rest.length + 1) by
        convert Submodule.add_mem _ hA hP using 1
        refine Prod.ext ?_ ?_
        · simp only [prepend, LinearMap.prodMap_apply, letterOp_current, Prod.fst_add]
          rfl
        · simp only [prepend, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, Prod.snd_add]
          abel
      rw [jetDer_letterSym_current]
      by_cases hμn : μ ≤ n
      · -- `μ ≤ n`: the commutator is a sum of length-`|w|` words
        rw [if_pos hμn, if_neg (by omega), LinearMap.zero_apply, add_zero, Finset.mul_sum]
        rw [show (∑ c, fabc a b c • J k c (↑μ + (-↑n - 1)) x,
            ∑ c, wordSym rest * fabc a b c • letterSym (Generator.current c, n - μ)) =
            ∑ c, fabc a b c • (correctedWordState k hk ((.current c, n - μ) :: rest),
              wordSym ((.current c, n - μ) :: rest)) by
          rw [Prod.ext_iff]
          simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd]
          refine ⟨Finset.sum_congr rfl fun c _ => ?_, Finset.sum_congr rfl fun c _ => ?_⟩
          · rw [correctedWordState_cons', letterOp_current]
            congr 2
            push_cast [hμn]; ring_nf
          · rw [wordSym_cons, mul_smul_comm, mul_comm]]
        refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
        have h := word_mem_symMod k hk ((.current c, n - μ) :: rest)
        rwa [List.length_cons] at h
      · -- `μ > n`: everything is in lower degree
        rw [if_neg hμn, mul_zero]
        refine lower_mem_symMod k hk (Submodule.add_mem _ (Submodule.sum_mem _ fun c _ =>
          Submodule.smul_mem _ _ (correctedPiece_J_nonneg k hk c (by omega) hxP)) ?_)
        split_ifs
        · rw [LinearMap.smul_apply, LinearMap.id_apply]
          exact Submodule.smul_mem _ _ hxP
        · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
  | (.sugawara, n) :: rest => by
      have ih := J_word_mem_symMod a μ rest
      set x := correctedWordState k hk rest with hx
      have hxP : x ∈ correctedAffineRPiece k hk rest.length :=
        correctedWordState_mem_piece k hk rest le_rfl
      rw [correctedWordState_cons', wordSym_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      have hcomm := Vir.Lcomm_J_apply k hk (-(n : ℤ) - 2) a μ x
      have hJ : J k a μ (letterOp k hk (.sugawara, n) x) =
          letterOp k hk (.sugawara, n) (J k a μ x)
            + ((μ : ℤ) : ℂ) • J k a ((-(n : ℤ) - 2) + μ) x := by
        rw [letterOp_sugawara, letterOp_sugawara, hcomm, Int.cast_neg, neg_smul]; abel
      rw [hJ, List.length_cons]
      have hP := prepend_symMod k hk (.sugawara, n) ih
      suffices hA : (((μ : ℤ) : ℂ) • J k a ((-(n : ℤ) - 2) + μ) x,
            wordSym rest * jetDer (a, μ) (letterSym (Generator.sugawara, n))) ∈
            symMod k hk (rest.length + 1) by
        convert Submodule.add_mem _ hA hP using 1
        refine Prod.ext ?_ ?_
        · simp only [prepend, LinearMap.prodMap_apply, Prod.fst_add]
          abel
        · simp only [prepend, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, Prod.snd_add]
          abel
      rw [jetDer_letterSym_sugawara]
      split_ifs with hμn
      · rw [show (((μ : ℤ) : ℂ) • J k a ((-(n : ℤ) - 2) + μ) x,
            wordSym rest * (μ : ℂ) • letterSym (Generator.current a, n + 1 - μ)) =
            (μ : ℂ) • (correctedWordState k hk ((.current a, n + 1 - μ) :: rest),
              wordSym ((.current a, n + 1 - μ) :: rest)) by
          rw [Prod.ext_iff]
          simp only [Prod.smul_fst, Prod.smul_snd]
          refine ⟨?_, ?_⟩
          · rw [correctedWordState_cons', letterOp_current, Int.cast_natCast]
            congr 2
            push_cast [hμn]; ring_nf
          · rw [wordSym_cons, mul_smul_comm, mul_comm]]
        refine Submodule.smul_mem _ _ ?_
        have h := word_mem_symMod k hk ((.current a, n + 1 - μ) :: rest)
        rwa [List.length_cons] at h
      · rw [mul_zero]
        exact lower_mem_symMod k hk (Submodule.smul_mem _ _
          (correctedPiece_J_nonneg k hk a (by omega) hxP))

end

end VOA.AdamovicSymbol
