/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictRing
import VOA.Examples.AdamovicDescCyclic

/-!
# The model symbol calculus on corrected words, at every level

On the universal affine VOA `V^k(sl₂)` (any noncritical level), pair each corrected word state
with its **model** symbol `mword R t w ∈ R[u_j, v_j]` (`TwoSeriesStrictRing`).  Let
`symModM R t k hk r ⊆ V^k × R[u_j, v_j]` be the span of the pairs of length-`r` words, plus
`F_{r-1} × 0`.

* `J_word_mem_symModM` — **the commutator calculus**: modulo lower corrected degree, `J^a_μ`
  (`μ ≥ 0`) acts on corrected words exactly as the model derivation `D_{(a,μ)}` acts on their
  model symbols.  The proof is the level-one proof, with the letter formulas
  `mder_mletter_current` / `mder_mletter_sugawara` (the `t`-terms are inert).
* `symModM_word` — stability under words in the nonnegative modes;
* `symbol_eq_zero_of_detect` — **well-definedness from detection, at any level and for any
  ideal**: if, for every pair `(y, Q) ∈ symModM r` with `y ∈ I`, the `R`-valued base-point
  evaluation `evR Q` vanishes, then every such pair has `Q = 0`.  (Cyclicity over `R`,
  `m_cyclic`, plus stability.)
* `modelImage R t r`, `modelDeg R t r d` — the span of the length-`r` model word symbols, and
  its part of conformal weight `d`; `snd_mem_modelImage`, `mder_mem_modelImage`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.ConcreteHodge
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR
open VOA.VertexOperatorAlgebra VOA.AdamovicSymbol

noncomputable section

variable (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)

/-! ### The model word symbols span the model -/

/-- The span of the model symbols of the length-`r` words. -/
def modelImage (r : ℕ) : Submodule ℂ (MPoly R) :=
  Submodule.span ℂ {Q | ∃ w : List (Generator × ℕ), w.length = r ∧ mword R t w = Q}

/-- The span of the model symbols of the length-`r` words of conformal weight `d`. -/
def modelDeg (r : ℕ) (d : ℤ) : Submodule ℂ (MPoly R) :=
  Submodule.span ℂ
    {Q | ∃ w : List (Generator × ℕ), w.length = r ∧ wordWt w = d ∧ mword R t w = Q}

theorem mword_mem_modelImage (w : List (Generator × ℕ)) : mword R t w ∈ modelImage R t w.length :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

theorem mword_mem_modelDeg (w : List (Generator × ℕ)) :
    mword R t w ∈ modelDeg R t w.length (wordWt w) :=
  Submodule.subset_span ⟨w, rfl, rfl, rfl⟩

theorem modelDeg_le (r : ℕ) (d : ℤ) : modelDeg R t r d ≤ modelImage R t r := by
  rw [modelDeg, Submodule.span_le]
  rintro _ ⟨w, hw, -, rfl⟩
  exact Submodule.subset_span ⟨w, hw, rfl⟩

/-! ### The pair module -/

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The span of the (state, model symbol) pairs of length-`r` words. -/
def symPairsM (r : ℕ) : Submodule ℂ (WakModule k × MPoly R) :=
  Submodule.span ℂ
    {x | ∃ w : List (Generator × ℕ), w.length = r ∧ (correctedWordState k hk w, mword R t w) = x}

/-- Pairs of length-`r` words, modulo `F_{r-1} × 0`. -/
def symModM (r : ℕ) : Submodule ℂ (WakModule k × MPoly R) :=
  symPairsM R t k hk r ⊔ (lowerP k hk r).prod ⊥

theorem word_mem_symModM (w : List (Generator × ℕ)) :
    (correctedWordState k hk w, mword R t w) ∈ symModM R t k hk w.length :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨w, rfl, rfl⟩)

theorem lower_mem_symModM {r : ℕ} {y : WakModule k} (hy : y ∈ lowerP k hk r) :
    (y, (0 : MPoly R)) ∈ symModM R t k hk r :=
  Submodule.mem_sup_right ⟨hy, Submodule.zero_mem _⟩

/-- The second component of a pair lies in the model image. -/
theorem snd_mem_modelImage {r : ℕ} {x : WakModule k × MPoly R} (hx : x ∈ symModM R t k hk r) :
    x.2 ∈ modelImage R t r := by
  have hle : symModM R t k hk r ≤
      (modelImage R t r).comap (LinearMap.snd ℂ (WakModule k) (MPoly R)) := by
    refine sup_le ?_ ?_
    · rw [symPairsM, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.snd_apply]
      exact hw ▸ mword_mem_modelImage R t w
    · rintro ⟨y, p⟩ ⟨-, hp⟩
      change p ∈ (⊥ : Submodule ℂ (MPoly R)) at hp
      rw [Submodule.mem_bot] at hp
      subst hp
      change (0 : MPoly R) ∈ modelImage R t r
      exact Submodule.zero_mem _
  exact hle hx

/-- Prepending a letter, on pairs. -/
def prependM (l : Generator × ℕ) : (WakModule k × MPoly R) →ₗ[ℂ] (WakModule k × MPoly R) :=
  LinearMap.prodMap (letterOp k hk l) (LinearMap.mulLeft ℂ (mletter R t l))

theorem prependM_symModM (l : Generator × ℕ) {r : ℕ} {x : WakModule k × MPoly R}
    (hx : x ∈ symModM R t k hk r) : prependM R t k hk l x ∈ symModM R t k hk (r + 1) := by
  have hle : symModM R t k hk r ≤ (symModM R t k hk (r + 1)).comap (prependM R t k hk l) := by
    refine sup_le ?_ ?_
    · rw [symPairsM, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := word_mem_symModM R t k hk (l :: w)
      rw [List.length_cons, hw, mword_cons, correctedWordState_cons'] at h
      exact h
    · rintro ⟨y, p⟩ ⟨hy, hp⟩
      change p ∈ (⊥ : Submodule ℂ (MPoly R)) at hp
      rw [Submodule.mem_bot] at hp
      subst hp
      rw [Submodule.mem_comap]
      change (letterOp k hk l y, mletter R t l * 0) ∈ symModM R t k hk (r + 1)
      rw [mul_zero]
      exact lower_mem_symModM R t k hk (letterOp_lowerP k hk l hy)
  exact hle hx

/-- **The commutator calculus on corrected words, in the model.** -/
theorem J_word_mem_symModM (a : Fin 3) (μ : ℕ) :
    ∀ w : List (Generator × ℕ),
      (J k a μ (correctedWordState k hk w), mder R (a, μ) (mword R t w)) ∈
        symModM R t k hk w.length
  | [] => by
      rw [correctedWordState_nil, closed_vacuum, J_vacuum_nonneg k a (by positivity),
        mword_nil, Derivation.map_one_eq_zero]
      exact Submodule.zero_mem _
  | (.current b, n) :: rest => by
      have ih := J_word_mem_symModM a μ rest
      set x := correctedWordState k hk rest with hx
      have hxP : x ∈ correctedAffineRPiece k hk rest.length :=
        correctedWordState_mem_piece k hk rest le_rfl
      rw [correctedWordState_cons', letterOp_current, mword_cons, Derivation.leibniz,
        smul_eq_mul, smul_eq_mul]
      have hcomm := LinearMap.congr_fun (current_comm k a b μ (-(n : ℤ) - 1)) x
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at hcomm
      rw [sub_eq_iff_eq_add] at hcomm
      rw [hcomm, List.length_cons]
      have hP := prependM_symModM R t k hk (.current b, n) ih
      suffices hA : (∑ c, fabc a b c • J k c (↑μ + (-↑n - 1)) x +
            (if (μ : ℤ) + (-↑n - 1) = 0 then (((μ : ℤ) : ℂ) * k * kappa a b) • LinearMap.id
              else 0) x, mword R t rest * mder R (a, μ) (mletter R t (Generator.current b, n))) ∈
            symModM R t k hk (rest.length + 1) by
        convert Submodule.add_mem _ hA hP using 1
        refine Prod.ext ?_ ?_
        · simp only [prependM, LinearMap.prodMap_apply, letterOp_current, Prod.fst_add]
          rfl
        · simp only [prependM, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, Prod.snd_add]
          abel
      rw [mder_mletter_current]
      by_cases hμn : μ ≤ n
      · rw [if_pos hμn, if_neg (by omega), LinearMap.zero_apply, add_zero, Finset.mul_sum]
        rw [show (∑ c, fabc a b c • J k c (↑μ + (-↑n - 1)) x,
            ∑ c, mword R t rest * fabc a b c • mletter R t (Generator.current c, n - μ)) =
            ∑ c, fabc a b c • (correctedWordState k hk ((.current c, n - μ) :: rest),
              mword R t ((.current c, n - μ) :: rest)) by
          rw [Prod.ext_iff]
          simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd]
          refine ⟨Finset.sum_congr rfl fun c _ => ?_, Finset.sum_congr rfl fun c _ => ?_⟩
          · rw [correctedWordState_cons', letterOp_current]
            congr 2
            push_cast [hμn]; ring_nf
          · rw [mword_cons, mul_smul_comm, mul_comm]]
        refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
        have h := word_mem_symModM R t k hk ((.current c, n - μ) :: rest)
        rwa [List.length_cons] at h
      · rw [if_neg hμn, mul_zero]
        refine lower_mem_symModM R t k hk (Submodule.add_mem _ (Submodule.sum_mem _ fun c _ =>
          Submodule.smul_mem _ _ (correctedPiece_J_nonneg k hk c (by omega) hxP)) ?_)
        split_ifs
        · rw [LinearMap.smul_apply, LinearMap.id_apply]
          exact Submodule.smul_mem _ _ hxP
        · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
  | (.sugawara, n) :: rest => by
      have ih := J_word_mem_symModM a μ rest
      set x := correctedWordState k hk rest with hx
      have hxP : x ∈ correctedAffineRPiece k hk rest.length :=
        correctedWordState_mem_piece k hk rest le_rfl
      rw [correctedWordState_cons', mword_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      have hcomm := Vir.Lcomm_J_apply k hk (-(n : ℤ) - 2) a μ x
      have hJ : J k a μ (letterOp k hk (.sugawara, n) x) =
          letterOp k hk (.sugawara, n) (J k a μ x)
            + ((μ : ℤ) : ℂ) • J k a ((-(n : ℤ) - 2) + μ) x := by
        rw [letterOp_sugawara, letterOp_sugawara, hcomm, Int.cast_neg, neg_smul]; abel
      rw [hJ, List.length_cons]
      have hP := prependM_symModM R t k hk (.sugawara, n) ih
      suffices hA : (((μ : ℤ) : ℂ) • J k a ((-(n : ℤ) - 2) + μ) x,
            mword R t rest * mder R (a, μ) (mletter R t (Generator.sugawara, n))) ∈
            symModM R t k hk (rest.length + 1) by
        convert Submodule.add_mem _ hA hP using 1
        refine Prod.ext ?_ ?_
        · simp only [prependM, LinearMap.prodMap_apply, Prod.fst_add]
          abel
        · simp only [prependM, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, Prod.snd_add]
          abel
      rw [mder_mletter_sugawara]
      split_ifs with hμn
      · rw [show (((μ : ℤ) : ℂ) • J k a ((-(n : ℤ) - 2) + μ) x,
            mword R t rest * (μ : ℂ) • mletter R t (Generator.current a, n + 1 - μ)) =
            (μ : ℂ) • (correctedWordState k hk ((.current a, n + 1 - μ) :: rest),
              mword R t ((.current a, n + 1 - μ) :: rest)) by
          rw [Prod.ext_iff]
          simp only [Prod.smul_fst, Prod.smul_snd]
          refine ⟨?_, ?_⟩
          · rw [correctedWordState_cons', letterOp_current, Int.cast_natCast]
            congr 2
            push_cast [hμn]; ring_nf
          · rw [mword_cons, mul_smul_comm, mul_comm]]
        refine Submodule.smul_mem _ _ ?_
        have h := word_mem_symModM R t k hk ((.current a, n + 1 - μ) :: rest)
        rwa [List.length_cons] at h
      · rw [mul_zero]
        exact lower_mem_symModM R t k hk (Submodule.smul_mem _ _
          (correctedPiece_J_nonneg k hk a (by omega) hxP))

theorem symModM_J (a : Fin 3) (μ : ℕ) (r : ℕ) {y : WakModule k} {Q : MPoly R}
    (hyQ : (y, Q) ∈ symModM R t k hk r) :
    (J k a μ y, mder R (a, μ) Q) ∈ symModM R t k hk r := by
  let P : (WakModule k × MPoly R) →ₗ[ℂ] (WakModule k × MPoly R) :=
    LinearMap.prodMap (J k a μ) (mρ R (a, μ))
  have hle : symModM R t k hk r ≤ (symModM R t k hk r).comap P := by
    refine sup_le ?_ ?_
    · rw [symPairsM, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := J_word_mem_symModM R t k hk a μ w
      rw [hw] at h
      exact h
    · rintro ⟨z, p⟩ ⟨hz, hp⟩
      change p ∈ (⊥ : Submodule ℂ (MPoly R)) at hp
      rw [Submodule.mem_bot] at hp
      subst hp
      rw [Submodule.mem_comap]
      change (J k a μ z, mder R (a, μ) 0) ∈ symModM R t k hk r
      rw [map_zero]
      exact lower_mem_symModM R t k hk (J_nonneg_lowerP k hk a (by positivity) hz)
  exact hle hyQ

/-- Stability of the pair module under words in the nonnegative modes. -/
theorem symModM_word (l : List (Fin 3 × ℕ)) (r : ℕ) {y : WakModule k} {Q : MPoly R}
    (hyQ : (y, Q) ∈ symModM R t k hk r) :
    (Desc.jWord (k := k) l y, VOA.CyclicEval.word (mρ R) l Q) ∈ symModM R t k hk r := by
  induction l with
  | nil => simpa [Desc.jWord, VOA.CyclicEval.word] using hyQ
  | cons q l ih =>
    have h := symModM_J R t k hk q.1 q.2 r ih
    simpa [Desc.jWord, VOA.CyclicEval.word, Module.End.mul_apply] using h

/-- The model derivations preserve the model image. -/
theorem mder_mem_modelImage (kk : Fin 3 × ℕ) (r : ℕ) {Q : MPoly R} (hQ : Q ∈ modelImage R t r) :
    mder R kk Q ∈ modelImage R t r := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have h := J_word_mem_symModM R t 0 (by norm_num) kk.1 kk.2 w
    rw [hw] at h
    exact snd_mem_modelImage R t 0 (by norm_num) h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [show mder R kk (c • x) = c • mder R kk x from (mρ R kk).map_smul c x]
    exact Submodule.smul_mem _ _ hx

/-! ### Well-definedness from detection -/

/-- **Detection by the `R`-valued base-point evaluation**: for every pair `(y, Q)` of the pair
module with `y ∈ I`, the base-point evaluation of `Q` (with values in `R`) vanishes. -/
def Detects (I : Submodule ℂ (WakModule k)) (r : ℕ) : Prop :=
  ∀ (y : WakModule k) (Q : MPoly R), (y, Q) ∈ symModM R t k hk r → y ∈ I → evR R Q = 0

/-- **Well-definedness from detection**: at any noncritical level and for any VOA ideal,
detection forces every pair with first component in the ideal to have zero symbol. -/
theorem symbol_eq_zero_of_detect {I : Submodule ℂ (WakModule k)}
    (hI : (affineSl2VOA_closed k hk).IsIdeal I) (r : ℕ) (hdet : Detects R t k hk I r)
    {y : WakModule k} {Q : MPoly R} (hyQ : (y, Q) ∈ symModM R t k hk r) (hy : y ∈ I) :
    Q = 0 :=
  m_cyclic R Q fun l => hdet _ _ (symModM_word R t k hk l r hyQ) (Desc.jWord_mem hI l hy)

end

end VOA.TwoSeries.StrictModel
