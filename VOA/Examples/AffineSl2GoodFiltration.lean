/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2Strong
import VOA.Core.GoodFiltration
import VOA.Core.GoodFiltrationQuotient
import VOA.Core.LinearFiltration
import VOA.Modules.FiniteGenerationProof

/-!
# The corrected affine `R`-filtration on the universal affine `sl2` VOA

The corrected filtration used in the affine graded-unitarity programme assigns cost one both to
each current and to the Sugawara conformal vector.  The latter is essential: although the
Sugawara vector is quadratic in currents, its corrected `R`-degree is one.

This file implements the resulting order-theoretic filtration on the universal affine VOA
`V^k(sl2)` at noncritical level.  A word is formed from current states and the conformal vector,
with arbitrary creation-mode depth; its filtration degree is the number of generators, not the
sum of their conformal weights or derivative orders.

What is proved here:

* the word spans form an increasing and exhaustive `LinearFiltration`;
* intersecting with conformal-weight spaces gives a `GradedFlag`;
* the vacuum is in degree zero, every current and every current derivative is in degree one,
  and the Sugawara vector and its global descendants are in degree one;
* the weight-one, degree-one piece is the entire weight-one space, and corrected degree two
  exhausts the weight-two space;
* arbitrary modes add corrected degrees, so the flag is a `GoodFiltration`, and this good
  filtration descends to every graded VOA quotient;
* finite-dimensional filtered-character equality implies strictness for any proposed embedding,
  by the generic criterion in `Core.LinearFiltration`.

What is deliberately not claimed:

* the induced flag on an arbitrary affine VOA quotient is constructed below, but it is not
  identified with an independently characterized intrinsic filtration on the quotient; and
* no inverse-DS embedding is constructed here, and no inverse-DS strictness statement is asserted.
-/

namespace VOA
namespace AffineVOA
namespace CorrectedR

open VOA.VertexOperatorAlgebra
open VOA.AffineVOA.Inst

noncomputable section

/-- The two kinds of cost-one generator in the corrected affine filtration. -/
inductive Generator
  | current (a : Fin 3)
  | sugawara
  deriving DecidableEq

/-- The state represented by a corrected generator. -/
def generatorState (k : ℂ) (hk : k + 2 ≠ 0) : Generator → WakModule k
  | .current a => currentState k a
  | .sugawara => (affineSl2VOA_closed k hk).conformalVector

/-- A corrected affine creation word.  The natural number on each letter records creation-mode
depth; derivatives have cost zero, so only the list length contributes to the filtration. -/
def correctedWordState (k : ℂ) (hk : k + 2 ≠ 0) :
    List (Generator × ℕ) → WakModule k
  | [] => (affineSl2VOA_closed k hk).vacuum
  | gr :: rest =>
      (affineSl2VOA_closed k hk).smul (generatorState k hk gr.1)
        (-(gr.2 : ℤ) - 1) (correctedWordState k hk rest)

@[simp] theorem correctedWordState_nil (k : ℂ) (hk : k + 2 ≠ 0) :
    correctedWordState k hk [] = (affineSl2VOA_closed k hk).vacuum := rfl

theorem correctedWordState_cons (k : ℂ) (hk : k + 2 ≠ 0)
    (gr : Generator × ℕ) (rest : List (Generator × ℕ)) :
    correctedWordState k hk (gr :: rest) =
      (affineSl2VOA_closed k hk).smul (generatorState k hk gr.1)
        (-(gr.2 : ℤ) - 1) (correctedWordState k hk rest) := rfl

/-- The span of corrected words containing at most `p` cost-one generators. -/
def correctedAffineRPiece (k : ℂ) (hk : k + 2 ≠ 0) (p : ℕ) :
    Submodule ℂ (WakModule k) :=
  Submodule.span ℂ (Set.range (fun w : {w : List (Generator × ℕ) // w.length ≤ p} =>
    correctedWordState k hk w.1))

/-- The corrected affine `R`-filtration before restriction to conformal weight. -/
def correctedAffineRFiltration (k : ℂ) (hk : k + 2 ≠ 0) :
    LinearFiltration ℕ ℂ (WakModule k) where
  piece := correctedAffineRPiece k hk
  mono' := by
    intro p q hpq
    rw [correctedAffineRPiece, correctedAffineRPiece, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span ⟨⟨w.1, w.2.trans hpq⟩, rfl⟩

@[simp] theorem correctedAffineRFiltration_piece (k : ℂ) (hk : k + 2 ≠ 0) (p : ℕ) :
    (correctedAffineRFiltration k hk).piece p = correctedAffineRPiece k hk p := rfl

/-- Every corrected word belongs to the piece indexed by its length. -/
theorem correctedWordState_mem_piece (k : ℂ) (hk : k + 2 ≠ 0)
    (w : List (Generator × ℕ)) {p : ℕ} (hw : w.length ≤ p) :
    correctedWordState k hk w ∈ (correctedAffineRFiltration k hk).piece p :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

/-- Explicit monotonicity of the corrected affine pieces. -/
theorem correctedAffineRPiece_mono (k : ℂ) (hk : k + 2 ≠ 0) {p q : ℕ} (hpq : p ≤ q) :
    correctedAffineRPiece k hk p ≤ correctedAffineRPiece k hk q :=
  (correctedAffineRFiltration k hk).mono hpq

/-- Current-only affine words embed into corrected words by tagging every letter as a current. -/
def liftCurrentWord : List (Fin 3 × ℕ) → List (Generator × ℕ) :=
  List.map (fun an => (Generator.current an.1, an.2))

@[simp] theorem length_liftCurrentWord (w : List (Fin 3 × ℕ)) :
    (liftCurrentWord w).length = w.length := by simp [liftCurrentWord]

@[simp] theorem liftCurrentWord_cons (an : Fin 3 × ℕ) (rest : List (Fin 3 × ℕ)) :
    liftCurrentWord (an :: rest) = (Generator.current an.1, an.2) :: liftCurrentWord rest := rfl

/-- The corrected-word interpretation of a current-only word is the existing affine word state. -/
theorem correctedWordState_liftCurrentWord (k : ℂ) (hk : k + 2 ≠ 0)
    (w : List (Fin 3 × ℕ)) :
    correctedWordState k hk (liftCurrentWord w) = wordStateA k w := by
  induction w with
  | nil => rfl
  | cons an rest ih =>
      rw [liftCurrentWord_cons, correctedWordState_cons,
        generatorState, ih, wordStateA_cons, smul_currentState_eq_J]

/-- The corrected filtration is exhaustive.  This uses only the already proved fact that
current-only creation words span the universal affine vacuum module. -/
theorem iSup_correctedAffineRFiltration_piece (k : ℂ) (hk : k + 2 ≠ 0) :
    (⨆ p : ℕ, (correctedAffineRFiltration k hk).piece p) = ⊤ := by
  rw [eq_top_iff, ← wordStateA_span k, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  rw [← correctedWordState_liftCurrentWord k hk w]
  exact Submodule.mem_iSup_of_mem w.length
    (correctedWordState_mem_piece k hk (liftCurrentWord w) (by simp))

/-- Degree zero is exactly the vacuum line. -/
theorem correctedAffineRPiece_zero (k : ℂ) (hk : k + 2 ≠ 0) :
    correctedAffineRPiece k hk 0 = ℂ ∙ (affineSl2VOA_closed k hk).vacuum := by
  apply le_antisymm
  · rw [correctedAffineRPiece, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨w, hw⟩ := w
    have hw0 : w = [] := by simpa using hw
    subst w
    simp
  · rw [Submodule.span_le]
    rintro _ rfl
    exact correctedWordState_mem_piece k hk [] (by simp)

/-! ## Cost-one generators and their creation towers -/

/-- Every current creation mode has corrected degree at most one, independently of derivative
order. -/
theorem currentCreation_mem_piece_one (k : ℂ) (hk : k + 2 ≠ 0) (a : Fin 3) (r : ℕ) :
    J k a (-(r : ℤ) - 1) (vacuumA k) ∈ correctedAffineRPiece k hk 1 := by
  have h := correctedWordState_mem_piece k hk [(Generator.current a, r)]
    (p := 1) (by simp)
  simpa [correctedWordState, generatorState, smul_currentState_eq_J] using h

/-- In particular, every current state has corrected degree one. -/
theorem currentState_mem_piece_one (k : ℂ) (hk : k + 2 ≠ 0) (a : Fin 3) :
    currentState k a ∈ correctedAffineRPiece k hk 1 := by
  simpa [currentState_def] using currentCreation_mem_piece_one k hk a 0

/-- Every Sugawara creation mode has corrected degree at most one.  In Virasoro notation these
are the states `L_{-r-2} vacuum`. -/
theorem sugawaraCreation_mem_piece_one (k : ℂ) (hk : k + 2 ≠ 0) (r : ℕ) :
    (affineSl2VOA_closed k hk).L (-(r : ℤ) - 2)
        (affineSl2VOA_closed k hk).vacuum ∈ correctedAffineRPiece k hk 1 := by
  have h := correctedWordState_mem_piece k hk [(Generator.sugawara, r)]
    (p := 1) (by simp)
  rw [VertexOperatorAlgebra.L_def]
  change mode ((affineSl2VOA_closed k hk).Y
      (affineSl2VOA_closed k hk).conformalVector) (-(r : ℤ) - 2 + 1)
        (affineSl2VOA_closed k hk).vacuum ∈ correctedAffineRPiece k hk 1
  rw [show (-(r : ℤ) - 2 + 1 : ℤ) = -(r : ℤ) - 1 by ring]
  simpa [correctedWordState, generatorState, PreVertexAlgebra.smul_def] using h

/-- The Sugawara conformal vector itself has corrected degree one, rather than its naive current
word length two. -/
theorem conformalVector_mem_piece_one (k : ℂ) (hk : k + 2 ≠ 0) :
    (affineSl2VOA_closed k hk).conformalVector ∈ correctedAffineRPiece k hk 1 := by
  have hω : (affineSl2VOA_closed k hk).conformalVector =
      (affineSl2VOA_closed k hk).L (-2) (affineSl2VOA_closed k hk).vacuum := by
    rw [VertexOperatorAlgebra.L_def, show (-2 + 1 : ℤ) = -1 by ring,
      ← PreVertexAlgebra.smul_def, (affineSl2VOA_closed k hk).smul_vacuum_neg_one]
  rw [hω]
  simpa using sugawaraCreation_mem_piece_one k hk 0

/-! ## Mode closure of corrected words -/

/-- Prepending a creation mode of either corrected generator raises corrected degree by one. -/
private theorem generatorCreation_mem_piece_succ (k : ℂ) (hk : k + 2 ≠ 0)
    (gr : Generator) (r p : ℕ) {v : WakModule k}
    (hv : v ∈ correctedAffineRPiece k hk p) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk gr)
      (-(r : ℤ) - 1) v ∈ correctedAffineRPiece k hk (p + 1) := by
  rw [correctedAffineRPiece] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨⟨(gr, r) :: w.1, by simpa using w.2⟩, rfl⟩
  | zero => rw [PreVertexAlgebra.smul_zero_right]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [PreVertexAlgebra.smul_add_right]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [PreVertexAlgebra.smul_smul_right]
      exact Submodule.smul_mem _ c ihx

/-- A mode of the Sugawara generator is the correspondingly shifted Virasoro mode. -/
private theorem sugawaraMode_eq_L (k : ℂ) (hk : k + 2 ≠ 0)
    (m : ℤ) (v : WakModule k) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk .sugawara) m v =
      (affineSl2VOA_closed k hk).L (m - 1) v := by
  change mode ((affineSl2VOA_closed k hk).Y
      (affineSl2VOA_closed k hk).conformalVector) m v =
    mode ((affineSl2VOA_closed k hk).Y
      (affineSl2VOA_closed k hk).conformalVector) (m - 1 + 1) v
  rw [show m - 1 + 1 = m by ring]

/-- Current-current commutation keeps a generator mode applied to a corrected word within the
next corrected piece. -/
private theorem currentMode_currentCons_mem_piece (k : ℂ) (hk : k + 2 ≠ 0)
    (a b : Fin 3) (m : ℤ) (r : ℕ) (rest : List (Generator × ℕ))
    (ih : ∀ (gr : Generator) (j : ℤ),
      (affineSl2VOA_closed k hk).smul (generatorState k hk gr) j
        (correctedWordState k hk rest) ∈ correctedAffineRPiece k hk (rest.length + 1)) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk (.current a)) m
        (correctedWordState k hk ((.current b, r) :: rest)) ∈
      correctedAffineRPiece k hk (rest.length + 2) := by
  have hcomm := smul_currentState_comm k hk a b m (-(r : ℤ) - 1)
    (correctedWordState k hk rest)
  rw [sub_eq_iff_eq_add] at hcomm
  simp only [generatorState, correctedWordState, smul_currentState_eq_J] at hcomm ⊢
  rw [hcomm]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · refine Submodule.sum_mem _ fun c _ => ?_
      apply correctedAffineRPiece_mono k hk (show rest.length + 1 ≤ rest.length + 2 by omega)
      exact Submodule.smul_mem _ _ (by
        simpa [generatorState, smul_currentState_eq_J] using
          ih (.current c) (m + (-(r : ℤ) - 1)))
    · split_ifs with hzero
      · exact Submodule.smul_mem _ _
          (correctedWordState_mem_piece k hk rest (p := rest.length + 2) (by omega))
      · exact Submodule.zero_mem _
  · have hinner := ih (.current a) m
    simpa [generatorState, smul_currentState_eq_J, add_assoc] using
      generatorCreation_mem_piece_succ k hk (.current b) r (rest.length + 1) hinner

/-- Virasoro-current covariance gives the mixed Sugawara-current step. -/
private theorem sugawaraMode_currentCons_mem_piece (k : ℂ) (hk : k + 2 ≠ 0)
    (b : Fin 3) (m : ℤ) (r : ℕ) (rest : List (Generator × ℕ))
    (ih : ∀ (gr : Generator) (j : ℤ),
      (affineSl2VOA_closed k hk).smul (generatorState k hk gr) j
        (correctedWordState k hk rest) ∈ correctedAffineRPiece k hk (rest.length + 1)) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk .sugawara) m
        (correctedWordState k hk ((.current b, r) :: rest)) ∈
      correctedAffineRPiece k hk (rest.length + 2) := by
  have hcomm := Vir.Lcomm_J_apply k hk (m - 1) b (-(r : ℤ) - 1)
    (correctedWordState k hk rest)
  rw [show m - 1 + 1 = m by ring] at hcomm
  simp only [generatorState, correctedWordState]
  rw [smul_currentState_eq_J]
  rw [closed_smul, closed_conformalVector]
  rw [hcomm]
  apply Submodule.add_mem
  · have hinner := ih .sugawara m
    have hcreate :=
      generatorCreation_mem_piece_succ k hk (.current b) r (rest.length + 1) hinner
    simp only [generatorState] at hcreate
    rw [smul_currentState_eq_J] at hcreate
    simpa only [closed_smul, closed_conformalVector, add_assoc] using hcreate
  · apply correctedAffineRPiece_mono k hk (show rest.length + 1 ≤ rest.length + 2 by omega)
    exact Submodule.smul_mem _ _ (by
      simpa [generatorState, smul_currentState_eq_J] using
        ih (.current b) ((m - 1) + (-(r : ℤ) - 1)))

/-- Virasoro-current covariance, rearranged, gives the mixed current-Sugawara step. -/
private theorem currentMode_sugawaraCons_mem_piece (k : ℂ) (hk : k + 2 ≠ 0)
    (a : Fin 3) (m : ℤ) (r : ℕ) (rest : List (Generator × ℕ))
    (ih : ∀ (gr : Generator) (j : ℤ),
      (affineSl2VOA_closed k hk).smul (generatorState k hk gr) j
        (correctedWordState k hk rest) ∈ correctedAffineRPiece k hk (rest.length + 1)) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk (.current a)) m
        (correctedWordState k hk ((.sugawara, r) :: rest)) ∈
      correctedAffineRPiece k hk (rest.length + 2) := by
  let n : ℤ := -(r : ℤ) - 1
  have hcomm := Vir.Lcomm_J_apply k hk (n - 1) a m
    (correctedWordState k hk rest)
  rw [show n - 1 + 1 = n by ring] at hcomm
  have hrearr :
      J k a m (mode (YA k hk (omegaA k)) n (correctedWordState k hk rest)) =
        mode (YA k hk (omegaA k)) n
            (J k a m (correctedWordState k hk rest)) -
          ((-m : ℤ) : ℂ) • J k a ((n - 1) + m) (correctedWordState k hk rest) := by
    rw [eq_sub_iff_add_eq]
    exact hcomm.symm
  simp only [generatorState, correctedWordState]
  rw [smul_currentState_eq_J]
  rw [closed_smul, closed_conformalVector]
  rw [hrearr]
  apply Submodule.sub_mem
  · have hinner := ih (.current a) m
    have hcreate :=
      generatorCreation_mem_piece_succ k hk .sugawara r (rest.length + 1) hinner
    simp only [generatorState] at hcreate
    rw [smul_currentState_eq_J] at hcreate
    simpa only [closed_smul, closed_conformalVector, add_assoc, n] using hcreate
  · apply correctedAffineRPiece_mono k hk (show rest.length + 1 ≤ rest.length + 2 by omega)
    exact Submodule.smul_mem _ _ (by
      simpa [generatorState, smul_currentState_eq_J] using
        ih (.current a) ((n - 1) + m))

/-- The VOA Virasoro relation gives the Sugawara-Sugawara step. -/
private theorem sugawaraMode_sugawaraCons_mem_piece (k : ℂ) (hk : k + 2 ≠ 0)
    (m : ℤ) (r : ℕ) (rest : List (Generator × ℕ))
    (ih : ∀ (gr : Generator) (j : ℤ),
      (affineSl2VOA_closed k hk).smul (generatorState k hk gr) j
        (correctedWordState k hk rest) ∈ correctedAffineRPiece k hk (rest.length + 1)) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk .sugawara) m
        (correctedWordState k hk ((.sugawara, r) :: rest)) ∈
      correctedAffineRPiece k hk (rest.length + 2) := by
  let W := affineSl2VOA_closed k hk
  let A : ℤ := m - 1
  let B : ℤ := (-(r : ℤ) - 1) - 1
  have hvir := W.L_virasoro A B
  rw [LieRing.of_associative_ring_bracket] at hvir
  have happ := congrArg (fun T : Module.End ℂ (WakModule k) =>
    T (correctedWordState k hk rest)) hvir
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply] at happ
  rw [sub_eq_iff_eq_add] at happ
  simp only [correctedWordState]
  rw [sugawaraMode_eq_L, sugawaraMode_eq_L]
  change W.L A (W.L B (correctedWordState k hk rest)) ∈ _
  rw [happ]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply correctedAffineRPiece_mono k hk (show rest.length + 1 ≤ rest.length + 2 by omega)
      exact Submodule.smul_mem _ _ (by
        have hinner := ih .sugawara (A + B + 1)
        rw [sugawaraMode_eq_L] at hinner
        simpa only [show A + B + 1 - 1 = A + B by ring] using hinner)
    · split_ifs
      · exact Submodule.smul_mem _ _
          (correctedWordState_mem_piece k hk rest (p := rest.length + 2) (by omega))
      · exact Submodule.zero_mem _
  · have hinner := ih .sugawara m
    rw [sugawaraMode_eq_L] at hinner
    have hcreate :=
      generatorCreation_mem_piece_succ k hk .sugawara r (rest.length + 1) hinner
    rw [sugawaraMode_eq_L] at hcreate
    simpa only [add_assoc, A, B] using hcreate

/-- Any mode of a corrected generator raises the corrected length bound of a word by at most one.
The four induction steps are respectively the affine current relation, the two orientations of
Virasoro-current covariance, and the Virasoro relation. -/
private theorem generatorMode_word_mem_piece_succ (k : ℂ) (hk : k + 2 ≠ 0) :
    ∀ (w : List (Generator × ℕ)) (gr : Generator) (m : ℤ),
      (affineSl2VOA_closed k hk).smul (generatorState k hk gr) m
          (correctedWordState k hk w) ∈ correctedAffineRPiece k hk (w.length + 1)
  | [], gr, m => by
      by_cases hm : 0 ≤ m
      · simp only [correctedWordState]
        rw [(affineSl2VOA_closed k hk).toPreVertexAlgebra.smul_vacuum_nonneg _ hm]
        exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = -(r : ℤ) - 1 :=
          ⟨(-m - 1).toNat, by omega⟩
        rw [hr]
        simpa only [correctedWordState, List.length_cons, List.length_nil,
          zero_add] using
          correctedWordState_mem_piece k hk [(gr, r)] (p := 1) (by simp)
  | ((headGr, r) :: rest), gr, m => by
      have ih := fun gr' j => generatorMode_word_mem_piece_succ k hk rest gr' j
      cases gr with
      | current a =>
          cases headGr with
          | current b =>
              simpa only [List.length_cons, Nat.add_assoc] using
                currentMode_currentCons_mem_piece k hk a b m r rest ih
          | sugawara =>
              simpa only [List.length_cons, Nat.add_assoc] using
                currentMode_sugawaraCons_mem_piece k hk a m r rest ih
      | sugawara =>
          cases headGr with
          | current b =>
              simpa only [List.length_cons, Nat.add_assoc] using
                sugawaraMode_currentCons_mem_piece k hk b m r rest ih
          | sugawara =>
              simpa only [List.length_cons, Nat.add_assoc] using
                sugawaraMode_sugawaraCons_mem_piece k hk m r rest ih

/-- A generator mode maps corrected degree `q` into corrected degree `q+1`. -/
private theorem generatorMode_piece_mem_piece_succ (k : ℂ) (hk : k + 2 ≠ 0)
    (gr : Generator) (m : ℤ) (q : ℕ) {v : WakModule k}
    (hv : v ∈ correctedAffineRPiece k hk q) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk gr) m v ∈
      correctedAffineRPiece k hk (q + 1) := by
  rw [correctedAffineRPiece] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      apply correctedAffineRPiece_mono k hk
        (show w.1.length + 1 ≤ q + 1 by omega)
      exact generatorMode_word_mem_piece_succ k hk w.1 gr m
  | zero =>
      rw [PreVertexAlgebra.smul_zero_right]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [PreVertexAlgebra.smul_add_right]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [PreVertexAlgebra.smul_smul_right]
      exact Submodule.smul_mem _ c ihx

/-- The all-integer iterate formula propagates generator closure to arbitrary corrected words. -/
private theorem wordMode_piece_mem_piece_add (k : ℂ) (hk : k + 2 ≠ 0) :
    ∀ (w : List (Generator × ℕ)) (q : ℕ) {v : WakModule k},
      v ∈ correctedAffineRPiece k hk q → ∀ m : ℤ,
        (affineSl2VOA_closed k hk).smul (correctedWordState k hk w) m v ∈
          correctedAffineRPiece k hk (w.length + q)
  | [], q, v, hv, m => by
      simp only [correctedWordState]
      rw [PreVertexAlgebra.smul_vacuum_left]
      split_ifs
      · simpa using hv
      · exact Submodule.zero_mem _
  | ((gr, r) :: rest), q, v, hv, m => by
      let W := affineSl2VOA_closed k hk
      let ell : ℤ := -(r : ℤ) - 1
      rw [correctedWordState_cons]
      rw [W.mode_iterate (generatorState k hk gr)
        (correctedWordState k hk rest) ell m v]
      apply QuotVOA.finsum_mem_submodule
      intro i
      apply Submodule.smul_mem
      apply Submodule.sub_mem
      · simpa only [W, List.length_cons, Nat.add_assoc, Nat.add_comm q 1] using
          generatorMode_piece_mem_piece_succ k hk gr (ell - i)
            (rest.length + q) (wordMode_piece_mem_piece_add k hk rest q hv (m + i))
      · apply Submodule.smul_mem
        simpa only [W, List.length_cons, Nat.add_assoc, Nat.add_comm q 1] using
          wordMode_piece_mem_piece_add k hk rest (q + 1)
            (generatorMode_piece_mem_piece_succ k hk gr i q hv) (ell + m - i)

/-- Arbitrary modes of elements in corrected degrees `p` and `q` have corrected degree at most
`p+q`.  This is the ungraded core of good-filtration compatibility. -/
theorem mode_piece_mem_piece_add (k : ℂ) (hk : k + 2 ≠ 0)
    {p q : ℕ} {u v : WakModule k}
    (hu : u ∈ correctedAffineRPiece k hk p)
    (hv : v ∈ correctedAffineRPiece k hk q) (m : ℤ) :
    (affineSl2VOA_closed k hk).smul u m v ∈ correctedAffineRPiece k hk (p + q) := by
  rw [correctedAffineRPiece] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      apply correctedAffineRPiece_mono k hk
        (show w.1.length + q ≤ p + q by omega)
      exact wordMode_piece_mem_piece_add k hk w.1 q hv m
  | zero =>
      rw [PreVertexAlgebra.smul_zero_left]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [PreVertexAlgebra.smul_add_left]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [PreVertexAlgebra.smul_smul_left]
      exact Submodule.smul_mem _ c ihx

/-! ## Restriction to conformal weight and the graded flag -/

/-- The corrected degree-`p`, conformal-weight-`n` piece. -/
def correctedAffineRWeightPiece (k : ℂ) (hk : k + 2 ≠ 0) (p : ℕ) (n : ℤ) :
    Submodule ℂ (WakModule k) :=
  correctedAffineRPiece k hk p ⊓ (affineSl2VOA_closed k hk).grading n

/-- Current derivatives lie in corrected degree one and their expected conformal weight. -/
theorem currentCreation_mem_weightPiece_one (k : ℂ) (hk : k + 2 ≠ 0)
    (a : Fin 3) (r : ℕ) :
    J k a (-(r : ℤ) - 1) (vacuumA k) ∈
      correctedAffineRWeightPiece k hk 1 (r + 1 : ℕ) := by
  refine ⟨currentCreation_mem_piece_one k hk a r, ?_⟩
  have h := (affineSl2VOA_closed k hk).grading_mode
    (currentState k a) (currentState_mem_grading k hk a)
    (affineSl2VOA_closed k hk).vacuum
    (affineSl2VOA_closed k hk).vacuum_mem_grading_zero (-(r : ℤ) - 1)
  change (affineSl2VOA_closed k hk).smul (currentState k a) (-(r : ℤ) - 1)
      (affineSl2VOA_closed k hk).vacuum ∈ _ at h
  rw [smul_currentState_eq_J] at h
  rw [closed_vacuum] at h
  have hi : (1 + 0 - (-(r : ℤ) - 1) - 1 : ℤ) = ((r + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hi] at h
  exact h

/-- Sugawara descendants lie in corrected degree one and weight `r+2`. -/
theorem sugawaraCreation_mem_weightPiece_one (k : ℂ) (hk : k + 2 ≠ 0) (r : ℕ) :
    (affineSl2VOA_closed k hk).L (-(r : ℤ) - 2)
        (affineSl2VOA_closed k hk).vacuum ∈
      correctedAffineRWeightPiece k hk 1 (r + 2 : ℕ) := by
  refine ⟨sugawaraCreation_mem_piece_one k hk r, ?_⟩
  have h := (affineSl2VOA_closed k hk).grading_mode
    (affineSl2VOA_closed k hk).conformalVector
    (affineSl2VOA_closed k hk).conformalVector_mem_grading_two
    (affineSl2VOA_closed k hk).vacuum
    (affineSl2VOA_closed k hk).vacuum_mem_grading_zero (-(r : ℤ) - 1)
  have hi : (2 + 0 - (-(r : ℤ) - 1) - 1 : ℤ) = ((r + 2 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hi] at h
  rw [VertexOperatorAlgebra.L_def]
  change mode ((affineSl2VOA_closed k hk).Y
      (affineSl2VOA_closed k hk).conformalVector) (-(r : ℤ) - 2 + 1)
        (affineSl2VOA_closed k hk).vacuum ∈ _
  rw [show (-(r : ℤ) - 2 + 1 : ℤ) = -(r : ℤ) - 1 by ring]
  exact h

/-- The degree-zero part has no positive-weight vectors. -/
theorem correctedAffineRWeightPiece_zero_of_pos (k : ℂ) (hk : k + 2 ≠ 0)
    (n : ℤ) (hn : 0 < n) : correctedAffineRWeightPiece k hk 0 n = ⊥ := by
  rw [correctedAffineRWeightPiece, correctedAffineRPiece_zero]
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx0 : x ∈ (affineSl2VOA_closed k hk).grading 0 := by
    rw [(affineSl2VOA_closed k hk).vacuum_grade]
    exact hx.1
  have hd : Disjoint ((affineSl2VOA_closed k hk).grading 0)
      ((affineSl2VOA_closed k hk).grading n) :=
    (affineSl2VOA_closed k hk).isInternal.submodule_iSupIndep.pairwiseDisjoint (by omega)
  exact Submodule.disjoint_def.mp hd x hx0 hx.2

/-- At weight zero, corrected degree zero is the whole weight space. -/
theorem correctedAffineRWeightPiece_zero_zero (k : ℂ) (hk : k + 2 ≠ 0) :
    correctedAffineRWeightPiece k hk 0 0 = (affineSl2VOA_closed k hk).grading 0 := by
  rw [correctedAffineRWeightPiece, correctedAffineRPiece_zero,
    (affineSl2VOA_closed k hk).vacuum_grade, inf_idem]

/-- The degree-one piece is already the whole weight-one space. -/
theorem correctedAffineRWeightPiece_one_one (k : ℂ) (hk : k + 2 ≠ 0) :
    correctedAffineRWeightPiece k hk 1 1 = (affineSl2VOA_closed k hk).grading 1 := by
  apply le_antisymm
  · exact inf_le_right
  · intro v hv
    have hv' : v ∈ gradingZA k 1 := by
      simpa only [closed_grading] using hv
    have hvH : v ∈ HSpan k 1 := gradingZA_le_hspan k 1 hv'
    have hH : HSpan k 1 ≤ correctedAffineRPiece k hk 1 := by
      rw [HSpan, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨a, rfl⟩ := Strong.wordDegA_one w hw
      simpa [wordStateA_cons, wordStateA_nil, currentState_def] using
        currentState_mem_piece_one k hk a
    exact ⟨hH hvH, hv⟩

/-! ### The exact corrected flag at conformal weight two -/

/-- The expected corrected-degree-one subspace at conformal weight two: the span of the three
current derivatives and the Sugawara conformal vector. -/
def correctedAffineRWeightTwoDegreeOneSpan (k : ℂ) (hk : k + 2 ≠ 0) :
    Submodule ℂ (WakModule k) :=
  Submodule.span ℂ
    (Set.range (fun a : Fin 3 => J k a (-2) (vacuumA k)) ∪
      {(affineSl2VOA_closed k hk).conformalVector})

/-- Every current derivative belongs to the explicit weight-two, corrected-degree-one span. -/
theorem currentDerivative_mem_weightTwoDegreeOneSpan (k : ℂ) (hk : k + 2 ≠ 0)
    (a : Fin 3) :
    J k a (-2) (vacuumA k) ∈ correctedAffineRWeightTwoDegreeOneSpan k hk :=
  Submodule.subset_span (Set.mem_union_left _ ⟨a, rfl⟩)

/-- The conformal vector belongs to the explicit weight-two, corrected-degree-one span. -/
theorem conformalVector_mem_weightTwoDegreeOneSpan (k : ℂ) (hk : k + 2 ≠ 0) :
    (affineSl2VOA_closed k hk).conformalVector ∈
      correctedAffineRWeightTwoDegreeOneSpan k hk :=
  Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _))

/-- The four displayed generators have corrected degree one and conformal weight two. -/
theorem weightTwoDegreeOneSpan_le_weightPiece (k : ℂ) (hk : k + 2 ≠ 0) :
    correctedAffineRWeightTwoDegreeOneSpan k hk ≤ correctedAffineRWeightPiece k hk 1 2 := by
  rw [correctedAffineRWeightTwoDegreeOneSpan, Submodule.span_le]
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨a, rfl⟩ := hx
    simpa only [show (-(1 : ℤ) - 1) = -2 by norm_num,
      show (((1 + 1 : ℕ) : ℤ)) = 2 by norm_num] using
      currentCreation_mem_weightPiece_one k hk a 1
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨conformalVector_mem_piece_one k hk,
      (affineSl2VOA_closed k hk).conformalVector_mem_grading_two⟩

/-- The weight-two projection of a corrected word of length at most one is one of the four
displayed generators, or zero. -/
private theorem piHom_two_word_length_one_mem_span (k : ℂ) (hk : k + 2 ≠ 0)
    (w : List (Generator × ℕ)) (hw : w.length ≤ 1) :
    piHom (affineSl2VOA_closed k hk) 2 (correctedWordState k hk w) ∈
      correctedAffineRWeightTwoDegreeOneSpan k hk := by
  cases w with
  | nil =>
    rw [correctedWordState_nil,
      piHom_of_mem_ne (affineSl2VOA_closed k hk) (by norm_num : (0 : ℤ) ≠ 2)
        (affineSl2VOA_closed k hk).vacuum_mem_grading_zero]
    exact Submodule.zero_mem _
  | cons head rest =>
    have hrest : rest = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_cons] at hw
      omega
    subst rest
    rcases head with ⟨gr, r⟩
    cases gr with
    | current a =>
        simp only [correctedWordState, generatorState, smul_currentState_eq_J,
          closed_vacuum]
        by_cases hr : r = 1
        · subst r
          have hgrade : J k a (-((1 : ℕ) : ℤ) - 1) (vacuumA k) ∈
              (affineSl2VOA_closed k hk).grading 2 := by
            simpa using (currentCreation_mem_weightPiece_one k hk a 1).2
          rw [piHom_of_mem (affineSl2VOA_closed k hk) hgrade]
          simpa only [show (-(1 : ℤ) - 1) = -2 by norm_num] using
            currentDerivative_mem_weightTwoDegreeOneSpan k hk a
        · have hgrade := (currentCreation_mem_weightPiece_one k hk a r).2
          have hne : ((r + 1 : ℕ) : ℤ) ≠ 2 := by
            intro h
            have : r = 1 := by omega
            exact hr this
          rw [piHom_of_mem_ne (affineSl2VOA_closed k hk) hne hgrade]
          exact Submodule.zero_mem _
    | sugawara =>
        by_cases hr : r = 0
        · subst r
          have hstate : correctedWordState k hk [(Generator.sugawara, 0)] =
              (affineSl2VOA_closed k hk).conformalVector := by
            simpa only [correctedWordState, generatorState] using
              (affineSl2VOA_closed k hk).smul_vacuum_neg_one
                (affineSl2VOA_closed k hk).conformalVector
          rw [hstate, piHom_of_mem (affineSl2VOA_closed k hk)
            (affineSl2VOA_closed k hk).conformalVector_mem_grading_two]
          exact conformalVector_mem_weightTwoDegreeOneSpan k hk
        · have hgrade := (sugawaraCreation_mem_weightPiece_one k hk r).2
          have hne : ((r + 2 : ℕ) : ℤ) ≠ 2 := by
            intro h
            have : r = 0 := by omega
            exact hr this
          have hstate : correctedWordState k hk [(Generator.sugawara, r)] =
              (affineSl2VOA_closed k hk).L (-(r : ℤ) - 2)
                (affineSl2VOA_closed k hk).vacuum := by
            rw [correctedWordState, generatorState, VertexOperatorAlgebra.L_def]
            change (affineSl2VOA_closed k hk).smul
                (affineSl2VOA_closed k hk).conformalVector (-(r : ℤ) - 1)
                (affineSl2VOA_closed k hk).vacuum =
              (affineSl2VOA_closed k hk).smul
                (affineSl2VOA_closed k hk).conformalVector (-(r : ℤ) - 2 + 1)
                (affineSl2VOA_closed k hk).vacuum
            rw [show (-(r : ℤ) - 2 + 1 : ℤ) = -(r : ℤ) - 1 by ring]
          rw [hstate, piHom_of_mem_ne (affineSl2VOA_closed k hk) hne hgrade]
          exact Submodule.zero_mem _

/-- Homogeneous projection maps the whole corrected degree-one piece into the explicit
four-generator weight-two span. -/
private theorem piHom_two_piece_one_mem_span (k : ℂ) (hk : k + 2 ≠ 0)
    {v : WakModule k} (hv : v ∈ correctedAffineRPiece k hk 1) :
    piHom (affineSl2VOA_closed k hk) 2 v ∈
      correctedAffineRWeightTwoDegreeOneSpan k hk := by
  rw [correctedAffineRPiece] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact piHom_two_word_length_one_mem_span k hk w.1 w.2
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx => rw [map_smul]; exact Submodule.smul_mem _ c ihx

/-- The exact corrected-degree-one subspace at conformal weight two consists of the three
current derivatives together with the Sugawara vector. -/
theorem correctedAffineRWeightPiece_one_two (k : ℂ) (hk : k + 2 ≠ 0) :
    correctedAffineRWeightPiece k hk 1 2 =
      correctedAffineRWeightTwoDegreeOneSpan k hk := by
  apply le_antisymm
  · intro v hv
    rw [← piHom_of_mem (affineSl2VOA_closed k hk) hv.2]
    exact piHom_two_piece_one_mem_span k hk hv.1
  · exact weightTwoDegreeOneSpan_le_weightPiece k hk

/-- The number of letters in a current creation word is bounded by its conformal weight. -/
private theorem currentWord_length_le_weight : ∀ w : List (Fin 3 × ℕ),
    (w.length : ℤ) ≤ wordDegA w
  | [] => by simp
  | ai :: rest => by
      rw [wordDegA_cons]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      have ih := currentWord_length_le_weight rest
      have hn : (0 : ℤ) ≤ ai.2 := Int.natCast_nonneg _
      omega

/-- At conformal weight two, corrected degree two already exhausts the full homogeneous space.
This follows directly from current-word spanning: every weight-two current word has at most two
letters.  The finer description of the degree-one subspace is not asserted here. -/
theorem correctedAffineRWeightPiece_two_two (k : ℂ) (hk : k + 2 ≠ 0) :
    correctedAffineRWeightPiece k hk 2 2 = (affineSl2VOA_closed k hk).grading 2 := by
  apply le_antisymm
  · exact inf_le_right
  · intro v hv
    have hv' : v ∈ gradingZA k 2 := by
      simpa only [closed_grading] using hv
    have hvH : v ∈ HSpan k 2 := gradingZA_le_hspan k 2 hv'
    have hH : HSpan k 2 ≤ correctedAffineRPiece k hk 2 := by
      rw [HSpan, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [← correctedWordState_liftCurrentWord k hk w]
      apply correctedWordState_mem_piece
      rw [length_liftCurrentWord]
      have hlen := currentWord_length_le_weight w
      omega
    exact ⟨hH hvH, hv⟩

/-- The corrected affine graded flag. -/
def correctedAffineRFlag (k : ℂ) (hk : k + 2 ≠ 0) :
    GradedFlag (affineSl2VOA_closed k hk) where
  piece := correctedAffineRWeightPiece k hk
  le_grading := fun _ _ => inf_le_right
  mono := by
    intro p q n hpq
    exact inf_le_inf_right _ (correctedAffineRPiece_mono k hk hpq)
  bot := correctedAffineRWeightPiece_zero_of_pos k hk
  vacuum_zero := (correctedAffineRWeightPiece_zero_zero k hk).trans
    (affineSl2VOA_closed k hk).vacuum_grade
  exhaustive := by
    intro n
    apply le_antisymm
    · exact iSup_le fun _ => inf_le_right
    · intro x hx
      have hall : x ∈ ⨆ p : ℕ, (correctedAffineRFiltration k hk).piece p := by
        rw [iSup_correctedAffineRFiltration_piece k hk]
        trivial
      obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _
        ((correctedAffineRFiltration k hk).mono'.directed_le)).mp hall
      exact Submodule.mem_iSup_of_mem p ⟨hp, hx⟩

/-- The local VOA condition saying that arbitrary modes of two corrected word spans add word
costs.  No inverse-DS statement is part of this predicate. -/
def ModeCompatibilityStatement (k : ℂ) (hk : k + 2 ≠ 0) : Prop :=
  (correctedAffineRFlag k hk).ModeCompatible

/-- The corrected affine flag is mode-compatible.  The proof combines current-current,
Virasoro-current, and Virasoro commutators with the all-integer iterate formula. -/
theorem correctedAffineRFlag_modeCompatible (k : ℂ) (hk : k + 2 ≠ 0) :
    ModeCompatibilityStatement k hk := by
  intro p q m n j u v hu hv
  refine ⟨mode_piece_mem_piece_add k hk hu.1 hv.1 j, ?_⟩
  exact (affineSl2VOA_closed k hk).grading_mode u hu.2 v hv.2 j

/-- The corrected affine filtration, unconditionally packaged as a good filtration. -/
def correctedAffineGoodFiltration (k : ℂ) (hk : k + 2 ≠ 0) :
    GoodFiltration (affineSl2VOA_closed k hk) where
  toGradedFlag := correctedAffineRFlag k hk
  mode_mem := correctedAffineRFlag_modeCompatible k hk

/-! ## Induced filtrations on affine VOA quotients -/

/-- The corrected affine flag induced on a VOA quotient.  Its degree-`p`, weight-`n` piece is
the image of the corresponding universal affine piece under the quotient map.

This is an induced filtration only.  It does not identify the quotient ideal, prove that this
flag agrees with any independently specified intrinsic filtration on the quotient, or compute an
associated graded algebra. -/
noncomputable def correctedAffineRQuotientFlag (k : ℂ) (hk : k + 2 ≠ 0)
    (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I) :
    GradedFlag (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) :=
  (correctedAffineRFlag k hk).quotient I hI hgr

@[simp] theorem correctedAffineRQuotientFlag_piece (k : ℂ) (hk : k + 2 ≠ 0)
    (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I)
    (p : ℕ) (n : ℤ) :
    (correctedAffineRQuotientFlag k hk I hI hgr).piece p n =
      (correctedAffineRWeightPiece k hk p n).map I.mkQ := rfl

/-- Mode compatibility of the corrected affine flag descends to every graded VOA quotient. -/
theorem correctedAffineRQuotientFlag_modeCompatible (k : ℂ) (hk : k + 2 ≠ 0)
    (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I) :
    (correctedAffineRQuotientFlag k hk I hI hgr).ModeCompatible :=
  (correctedAffineRFlag k hk).quotient_modeCompatible I hI hgr
    (correctedAffineRFlag_modeCompatible k hk)

/-- The induced good filtration on any graded affine VOA quotient. -/
noncomputable def correctedAffineRQuotientGoodFiltration (k : ℂ) (hk : k + 2 ≠ 0)
    (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I) :
    GoodFiltration (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) :=
  (correctedAffineGoodFiltration k hk).quotient I hI hgr

/-! ## Conditional finite-dimensional strictness interface -/

/-- Character-form strictness criterion specialized to the corrected affine filtration.

For actual VOAs this should normally be applied after restricting to a fixed conformal weight
(and, in the free-field target, a fixed charge sector), so the displayed intersections are finite
dimensional.  The theorem is conditional and asserts neither an inverse-DS embedding nor the
required filtered-character equality. -/
theorem strictFilteredAlong_of_filtered_of_finrank_eq
    {I Ambient : Type*} [Preorder I]
    [AddCommGroup Ambient] [Module ℂ Ambient]
    (k : ℂ) (hk : k + 2 ≠ 0)
    (G : LinearFiltration I ℂ Ambient) (phi : ℕ → I)
    (iota : WakModule k →ₗ[ℂ] Ambient) (hiota : Function.Injective iota)
    (hfiltered : (correctedAffineRFiltration k hk).IsFilteredAlong G phi iota)
    (hfinite : ∀ p, FiniteDimensional ℂ ↥(LinearMap.range iota ⊓ G.piece (phi p)))
    (hfinrank : ∀ p, Module.finrank ℂ ((correctedAffineRFiltration k hk).piece p) =
      Module.finrank ℂ ↥(LinearMap.range iota ⊓ G.piece (phi p))) :
    (correctedAffineRFiltration k hk).IsStrictFilteredAlong G phi iota :=
  hfiltered.isStrictFilteredAlong_of_finrank_eq_range_inf hiota hfinite hfinrank

end

end CorrectedR
end AffineVOA
end VOA
