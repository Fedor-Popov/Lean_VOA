/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2Presentation
import VOA.Filtered.AffineCurrentLi
import VOA.Foundations.PBWBasis
import Mathlib.Algebra.Order.Group.Multiset

/-!
# The universal affine `sl₂` `C₂` symbol map and its exact PBW input

This file isolates the basis theorem needed for injectivity of the universal symbol map
`Sym(sl₂) -> A₂(V^k(sl₂))`.  The source monomial of exponent `mu` is represented by the
ordered word of `(-1)`-current modes in affine colour order `(e,f,h)`.  Thus injectivity is
equivalent to linear independence of those ordered depth-zero words modulo `O₂`.

The exact minimal condition is that the depth-zero PBW sector be disjoint from `O₂`.  A full
`PBWBasis` supplies independence of the representatives before quotienting.  The second half of
this file proves, by an explicit adjacent-swap argument, that ordinary affine PBW also supplies
the required filtered triangularity.  Thus no classical-freeness hypothesis enters the proof;
the remaining named input is precisely the ordinary affine PBW basis theorem itself.
-/

namespace VOA

open VertexOperatorAlgebra
open VOA.AffineVOA
open VOA.AffineVOA.Inst
open VOA.AffineVOA.CurrentLi
open VOA.QuasiLisseSl2
open VOA.Sl2Pres
open VOA.Sl2Symbol

namespace AffineSl2UniversalC2PBW

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

private abbrev W : VertexOperatorAlgebra (WakModule k) := affineSl2VOA_closed k hk

/-- The coordinate-to-current permutation `(e,h,f) -> (e,f,h)`. -/
def symbolToCurrentColor : Equiv.Perm (Fin 3) := Equiv.swap 1 2

@[simp] theorem symbolToCurrentColor_zero : symbolToCurrentColor 0 = 0 := by decide
@[simp] theorem symbolToCurrentColor_one : symbolToCurrentColor 1 = 2 := by decide
@[simp] theorem symbolToCurrentColor_two : symbolToCurrentColor 2 = 1 := by decide

/-- Embed a symbol colour as the depth-zero affine PBW letter of the corresponding current. -/
def purePBWLetterEmbedding : Fin 3 ↪ (Fin 3 ×ₗ ℕ) where
  toFun i := toLex (symbolToCurrentColor i, 0)
  inj' := by
    intro i j hij
    apply symbolToCurrentColor.injective
    exact congrArg (fun q => (ofLex q).1) hij

/-- Extend a three-variable monomial exponent by zero to the full affine PBW alphabet. -/
def purePBWIndex (mu : Fin 3 →₀ ℕ) : (Fin 3 ×ₗ ℕ) →₀ ℕ :=
  Finsupp.embDomain purePBWLetterEmbedding mu

theorem purePBWIndex_injective : Function.Injective purePBWIndex :=
  Finsupp.embDomain_injective purePBWLetterEmbedding

/-- Full PBW exponents containing at least one positive-depth letter. -/
def positiveDepthPBWIndices : Set ((Fin 3 ×ₗ ℕ) →₀ ℕ) :=
  {mu | ∃ a : Fin 3, ∃ n : ℕ, 0 < n ∧ mu (toLex (a, n)) ≠ 0}

/-- A depth-zero exponent vanishes at every positive-depth PBW letter. -/
theorem purePBWIndex_apply_positiveDepth (mu : Fin 3 →₀ ℕ) (a : Fin 3) (n : ℕ)
    (hn : 0 < n) : purePBWIndex mu (toLex (a, n)) = 0 := by
  rw [purePBWIndex, Finsupp.embDomain_apply]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    have hdepth := congrArg (fun q => (ofLex q).2) hi
    change (0 : ℕ) = n at hdepth
    omega
  · rfl

/-- The embedded depth-zero exponents and the positive-depth exponents are disjoint. -/
theorem range_purePBWIndex_disjoint_positiveDepth :
    Disjoint (Set.range purePBWIndex) positiveDepthPBWIndices := by
  rw [Set.disjoint_left]
  rintro _ ⟨mu, rfl⟩ ⟨a, n, hn, hne⟩
  exact hne (purePBWIndex_apply_positiveDepth mu a n hn)

private abbrev q0 : Fin 3 ×ₗ ℕ := toLex (0, 0)
private abbrev q1 : Fin 3 ×ₗ ℕ := toLex (1, 0)
private abbrev q2 : Fin 3 ×ₗ ℕ := toLex (2, 0)

private theorem supportSort_q0_q1 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (Finsupp.single q0 x + Finsupp.single q1 y).support.sort (fun a b => a ≤ b) =
      [q0, q1] := by
  have hs : (Finsupp.single q0 x + Finsupp.single q1 y).support = {q0, q1} := by
    rw [Finsupp.support_add_eq (by simp [hx, hy])]
    simp [hx, hy]
  rw [hs]
  rw [Finset.sort_insert]
  · rw [Finset.sort_singleton]
  · intro b hb
    simp only [Finset.mem_singleton] at hb
    subst b
    rw [Prod.Lex.toLex_le_toLex]
    exact Or.inl (by decide)
  · simp [q0, q1]

private theorem supportSort_q0_q2 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (Finsupp.single q0 x + Finsupp.single q2 y).support.sort (fun a b => a ≤ b) =
      [q0, q2] := by
  have hs : (Finsupp.single q0 x + Finsupp.single q2 y).support = {q0, q2} := by
    rw [Finsupp.support_add_eq (by simp [hx, hy])]
    simp [hx, hy]
  rw [hs]
  rw [Finset.sort_insert]
  · rw [Finset.sort_singleton]
  · intro b hb
    simp only [Finset.mem_singleton] at hb
    subst b
    rw [Prod.Lex.toLex_le_toLex]
    exact Or.inl (by decide)
  · simp [q0, q2]

private theorem supportSort_q2_q1 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (Finsupp.single q2 x + Finsupp.single q1 y).support.sort (fun a b => a ≤ b) =
      [q1, q2] := by
  have hs : (Finsupp.single q2 x + Finsupp.single q1 y).support = {q2, q1} := by
    rw [Finsupp.support_add_eq (by simp [hx, hy])]
    simp [hx, hy]
  rw [hs]
  rw [show ({q2, q1} : Finset _) = {q1, q2} by ext q; simp [or_comm]]
  rw [Finset.sort_insert]
  · rw [Finset.sort_singleton]
  · intro b hb
    simp only [Finset.mem_singleton] at hb
    subst b
    rw [Prod.Lex.toLex_le_toLex]
    exact Or.inl (by decide)
  · simp [q1, q2]

private theorem supportSort_q0_q2_q1 {x y z : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (Finsupp.single q0 x + Finsupp.single q2 y + Finsupp.single q1 z).support.sort
        (fun a b => a ≤ b) = [q0, q1, q2] := by
  have hs :
      (Finsupp.single q0 x + Finsupp.single q2 y + Finsupp.single q1 z).support =
        {q0, q2, q1} := by
    rw [Finsupp.support_add_eq (by
      rw [Finsupp.support_add_eq (by simp [hx, hy])]
      simp [hx, hy, hz])]
    rw [Finsupp.support_add_eq (by simp [hx, hy])]
    simp [hx, hy, hz]
  rw [hs]
  rw [Finset.sort_insert]
  · rw [show ({q2, q1} : Finset _) = {q1, q2} by ext q; simp [or_comm]]
    rw [Finset.sort_insert]
    · rw [Finset.sort_singleton]
    · intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      rw [Prod.Lex.toLex_le_toLex]
      exact Or.inl (by decide)
    · simp [q1, q2]
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl <;> rw [Prod.Lex.toLex_le_toLex] <;>
      exact Or.inl (by decide)
  · simp [q0, q1, q2]

/-- The ordered depth-zero current word attached to an `(e,h,f)` exponent vector.  The list is
written in affine PBW colour order `(e,f,h)`, hence the transposition of entries `1` and `2`. -/
def pureCurrentWord (mu : Fin 3 →₀ ℕ) : List (Fin 3 × ℕ) :=
  List.replicate (mu 0) (colE, 0) ++
    List.replicate (mu 2) (colF, 0) ++
      List.replicate (mu 1) (colH, 0)

/-- The same word with Chevalley basis vectors in place of colour labels. -/
def pureLieWord (mu : Fin 3 →₀ ℕ) : List (Sl2 × ℕ) :=
  (pureCurrentWord mu).map fun an => (basis an.1, an.2)

/-- The ordered `(-1)`-current state representing one polynomial monomial. -/
def pureCurrentState (mu : Fin 3 →₀ ℕ) : WakModule k :=
  wordStateA k (pureCurrentWord mu)

/-- The depth-zero current span is disjoint from the span of positive-depth current words.  This
is the precise filtered-triangularity target used below. -/
def PureCurrentLiSeparated : Prop :=
  Disjoint (Submodule.span ℂ (Set.range (pureCurrentState k))) (currentWordPiece k 1)

/-- The full PBW word attached to a depth-zero exponent is the explicit `(e,f,h)` word. -/
theorem pbwWord_purePBWIndex (mu : Fin 3 →₀ ℕ) :
    pbwWord (Pi.basisFun ℂ (Fin 3)) (purePBWIndex mu) = pureLieWord mu := by
  classical
  have hmu : mu = Finsupp.single 0 (mu 0) + Finsupp.single 1 (mu 1) +
      Finsupp.single 2 (mu 2) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  by_cases h0 : mu 0 = 0 <;> by_cases h1 : mu 1 = 0 <;> by_cases h2 : mu 2 = 0
  all_goals
    rw [hmu]
    simp [pbwWord, purePBWIndex, purePBWLetterEmbedding,
      pureLieWord, pureCurrentWord, h0, h1, h2, Pi.basisFun_apply, basis,
      supportSort_q0_q1, supportSort_q0_q2, supportSort_q2_q1, supportSort_q0_q2_q1]

/-- Replacing every colour in a current word by its Chevalley basis vector turns the affine
`negWord` construction into `wordStateA` definitionally. -/
theorem negWord_map_basis_eq_wordStateA :
    ∀ l : List (Fin 3 × ℕ),
      AffineLie.negWord kappaForm kappaForm_isInvariant k
          (l.map fun an => (basis an.1, an.2)) = wordStateA k l
  | [] => by simp [AffineLie.negWord_nil, wordStateA_nil, vacuumA]
  | (a, n) :: l => by
      rw [List.map_cons, AffineLie.negWord_cons, wordStateA_cons,
        negWord_map_basis_eq_wordStateA l]
      rfl

/-- The depth-zero current representatives are a subfamily of the full affine PBW family. -/
theorem pureCurrentState_eq_pbwMonomial (mu : Fin 3 →₀ ℕ) :
    pureCurrentState k mu =
      AffineLie.negWord kappaForm kappaForm_isInvariant k
        (pbwWord (Pi.basisFun ℂ (Fin 3)) (purePBWIndex mu)) := by
  rw [pbwWord_purePBWIndex, pureLieWord, negWord_map_basis_eq_wordStateA]
  rfl

/-- A full affine PBW basis proves linear independence of the depth-zero representatives before
passing to `C₂`. -/
theorem pureCurrentState_linearIndependent_of_PBWBasis
    (hPBW : PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k) :
    LinearIndependent ℂ (pureCurrentState k) := by
  have h := (PBWBasis.linearIndependent hPBW).comp purePBWIndex purePBWIndex_injective
  have heq :
      ((fun mu => AffineLie.negWord kappaForm kappaForm_isInvariant k
        (pbwWord (Pi.basisFun ℂ (Fin 3)) mu)) ∘ purePBWIndex) = pureCurrentState k := by
    funext mu
    exact (pureCurrentState_eq_pbwMonomial k mu).symm
  rw [heq] at h
  exact h

/-- The filtered PBW containment: every current word of positive total derivative depth is a
linear combination of ordered PBW monomials containing a positive-depth letter.  It is defined
here as an intermediate interface and proved from ordinary `PBWBasis` below. -/
def PositiveDepthPBWSpanning
    (B : Module.Basis (((Fin 3) ×ₗ ℕ) →₀ ℕ) ℂ (WakModule k)) : Prop :=
  currentWordPiece k 1 ≤
    Submodule.span ℂ (B '' positiveDepthPBWIndices)

/-- A PBW basis whose straightening respects positive derivative depth.  Unlike bare
`PBWBasis`, this package contains exactly the filtration compatibility needed for `C₂`.
-/
def FilteredPBWBasis : Prop :=
  ∃ B : Module.Basis (((Fin 3) ×ₗ ℕ) →₀ ℕ) ℂ (WakModule k),
    (∀ mu, B mu = AffineLie.negWord kappaForm kappaForm_isInvariant k
      (pbwWord (Pi.basisFun ℂ (Fin 3)) mu)) ∧ PositiveDepthPBWSpanning k B

/-- A filtered PBW basis implies the abstract depth-zero/positive-depth separation. -/
theorem pureCurrentLiSeparated_of_filteredPBW
    (B : Module.Basis (((Fin 3) ×ₗ ℕ) →₀ ℕ) ℂ (WakModule k))
    (hB : ∀ mu, B mu = AffineLie.negWord kappaForm kappaForm_isInvariant k
      (pbwWord (Pi.basisFun ℂ (Fin 3)) mu))
    (hspan : PositiveDepthPBWSpanning k B) : PureCurrentLiSeparated k := by
  have hpure : Submodule.span ℂ (Set.range (pureCurrentState k)) ≤
      Submodule.span ℂ (B '' Set.range purePBWIndex) := by
    rw [Submodule.span_le]
    rintro _ ⟨mu, rfl⟩
    apply Submodule.subset_span
    refine ⟨purePBWIndex mu, ⟨mu, rfl⟩, ?_⟩
    rw [hB]
    exact (pureCurrentState_eq_pbwMonomial k mu).symm
  have hdisjoint :
      Disjoint (Submodule.span ℂ (B '' Set.range purePBWIndex))
        (Submodule.span ℂ (B '' positiveDepthPBWIndices)) :=
    B.linearIndependent.disjoint_span_image range_purePBWIndex_disjoint_positiveDepth
  exact Disjoint.mono hpure hspan hdisjoint

/-- Bundled filtered PBW data gives the separation in one step. -/
theorem pureCurrentLiSeparated_of_FilteredPBWBasis
    (hPBW : FilteredPBWBasis k) : PureCurrentLiSeparated k := by
  obtain ⟨B, hB, hspan⟩ := hPBW
  exact pureCurrentLiSeparated_of_filteredPBW k B hB hspan

/-- The class of an arbitrary depth-zero current word is the product of its current classes. -/
theorem mk₂_wordStateA_eq_prod_of_depth_zero :
    ∀ l : List (Fin 3 × ℕ),
      (∀ an ∈ l, an.2 = 0) →
      mk₂ (W k hk) (wordStateA k l) =
        (l.map fun an => mk₂ (W k hk) (currentState k an.1)).prod
  | [], _ => by
      rw [wordStateA_nil, show vacuumA k = (W k hk).vacuum from rfl, ← A₂_one_eq]
      rfl
  | (a, n) :: l, hl => by
      have hn : n = 0 := hl (a, n) (by simp)
      have htail : ∀ an ∈ l, an.2 = 0 := by
        intro an han
        exact hl an (by simp [han])
      subst n
      rw [wordStateA_cons, show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num]
      rw [Sl2Pres.mk₂_J_neg_one k hk]
      rw [mk₂_wordStateA_eq_prod_of_depth_zero l htail]
      rfl

/-- The PBW representative of a monomial has exactly the expected commutative `C₂` class. -/
theorem mk₂_pureCurrentState (mu : Fin 3 →₀ ℕ) :
    mk₂ (W k hk) (pureCurrentState k mu) =
      eCl k hk ^ mu 0 * fCl k hk ^ mu 2 * hCl k hk ^ mu 1 := by
  rw [pureCurrentState, mk₂_wordStateA_eq_prod_of_depth_zero k hk]
  · simp [pureCurrentWord, eCl, fCl, hCl]
    ring
  · intro an han
    simp only [pureCurrentWord, List.mem_append, List.mem_replicate] at han
    rcases han with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> rfl

/-- Evaluating a source monomial under the universal symbol map gives the class of its ordered
depth-zero PBW representative. -/
theorem symbolAlg_monomial (mu : Fin 3 →₀ ℕ) :
    symbolAlg k hk (MvPolynomial.monomial mu 1) =
      mk₂ (W k hk) (pureCurrentState k mu) := by
  rw [mk₂_pureCurrentState]
  simp only [symbolAlg, MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial,
    map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_three]
    change eCl k hk ^ mu 0 * hCl k hk ^ mu 1 * fCl k hk ^ mu 2 = _
    ring
  · simp

/-- The exact depth-zero PBW statement needed for the universal `C₂` presentation: ordered
`(-1)`-current monomials remain linearly independent after quotienting by `O₂`. -/
def PureCurrentC2Independent : Prop :=
  LinearIndependent ℂ fun mu : Fin 3 →₀ ℕ =>
    mk₂ (W k hk) (pureCurrentState k mu)

/-- Exact PBW separation at `C₂`: no nonzero linear combination of depth-zero ordered current
monomials belongs to `O₂`. -/
def PureCurrentO2Separated : Prop :=
  Disjoint (Submodule.span ℂ (Set.range (pureCurrentState k))) (O₂ (W k hk))

/-- Positive-depth PBW separation implies `O₂` separation, using the proved strict description
of the affine Li filtration. -/
theorem pureCurrentO2Separated_of_liSeparated
    (hsep : PureCurrentLiSeparated k) : PureCurrentO2Separated k hk := by
  rw [PureCurrentLiSeparated, Submodule.disjoint_def] at hsep
  rw [PureCurrentO2Separated, Submodule.disjoint_def]
  intro x hx hO2
  apply hsep x hx
  rw [← liFiltration_eq_currentWordPiece k hk 1]
  exact O₂_le_liFiltration_one (W k hk) hO2

/-- Independence of the depth-zero classes forces exact separation from `O₂`. -/
theorem pureCurrentO2Separated_of_c2Independent
    (hclass : PureCurrentC2Independent k hk) : PureCurrentO2Separated k hk := by
  rw [PureCurrentO2Separated, Submodule.disjoint_def]
  intro x hx hO2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  change Finsupp.linearCombination ℂ (pureCurrentState k) c = x at hc
  have hzero : Finsupp.linearCombination ℂ
      (fun mu : Fin 3 →₀ ℕ => mk₂ (W k hk) (pureCurrentState k mu)) c = 0 := by
    change Finsupp.linearCombination ℂ
      ((mk₂ (W k hk)) ∘ pureCurrentState k) c = 0
    rw [← LinearMap.map_finsupp_linearCombination (mk₂ (W k hk)), hc]
    exact (mk₂_eq_zero_iff (W k hk)).mpr hO2
  have hc0 : c = 0 := hclass.finsuppLinearCombination_injective (by
    rw [hzero]
    exact (map_zero _).symm)
  rw [← hc, hc0]
  exact map_zero _

/-- If the depth-zero representatives are independent before quotienting and their span is
disjoint from `O₂`, then their `C₂` classes remain independent. -/
theorem pureCurrentC2Independent_of_o2Separated
    (hli : LinearIndependent ℂ (pureCurrentState k))
    (hsep : PureCurrentO2Separated k hk) : PureCurrentC2Independent k hk := by
  let f : WakModule k →ₗ[ℂ] A₂ (W k hk) := mk₂ (W k hk)
  have hker : LinearMap.ker f = O₂ (W k hk) := by
    ext x
    change f x = 0 ↔ x ∈ O₂ (W k hk)
    exact mk₂_eq_zero_iff (W k hk)
  have hd : Disjoint (Submodule.span ℂ (Set.range (pureCurrentState k)))
      (LinearMap.ker f) := by simpa [hker] using hsep
  exact (f.linearIndependent_iff_of_disjoint hd).mpr hli

/-- With independence of the representatives before quotienting, `C₂` independence is exactly
the statement that their span misses `O₂`. -/
theorem pureCurrentC2Independent_iff_o2Separated
    (hli : LinearIndependent ℂ (pureCurrentState k)) :
    PureCurrentC2Independent k hk ↔ PureCurrentO2Separated k hk :=
  ⟨pureCurrentO2Separated_of_c2Independent k hk,
    pureCurrentC2Independent_of_o2Separated k hk hli⟩

/-- A full affine PBW basis plus filtered triangular separation proves independence of the
depth-zero classes.  This is the clean non-circular input route to universal-symbol injectivity.
-/
theorem pureCurrentC2Independent_of_PBWBasis_of_liSeparated
    (hPBW : PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k)
    (hsep : PureCurrentLiSeparated k) : PureCurrentC2Independent k hk := by
  apply pureCurrentC2Independent_of_o2Separated k hk
    (pureCurrentState_linearIndependent_of_PBWBasis k hPBW)
  exact pureCurrentO2Separated_of_liSeparated k hk hsep

/-- Linear independence of the depth-zero current classes implies injectivity of the universal
symbol map. -/
theorem symbolAlg_injective_of_pureCurrentC2Independent
    (h : PureCurrentC2Independent k hk) :
    Function.Injective (symbolAlg k hk) := by
  let b := MvPolynomial.basisMonomials (Fin 3) ℂ
  have himages : LinearIndependent ℂ fun mu : Fin 3 →₀ ℕ =>
      symbolAlg k hk (b mu) := by
    simpa only [b, MvPolynomial.coe_basisMonomials,
      symbolAlg_monomial k hk] using h
  have hmap : (symbolAlg k hk).toLinearMap =
      b.constr ℂ (fun mu => symbolAlg k hk (b mu)) := by
    apply b.ext
    intro mu
    simp
  change Function.Injective (symbolAlg k hk).toLinearMap
  rw [hmap]
  exact b.injective_constr_of_linearIndependent himages

/-- Conversely, injectivity of the universal symbol map forces linear independence of the
ordered depth-zero current classes.  Thus the named condition above is exact, not merely
sufficient. -/
theorem pureCurrentC2Independent_of_symbolAlg_injective
    (h : Function.Injective (symbolAlg k hk)) :
    PureCurrentC2Independent k hk := by
  have hb := (MvPolynomial.basisMonomials (Fin 3) ℂ).linearIndependent
  have himage : LinearIndependent ℂ fun mu : Fin 3 →₀ ℕ =>
      symbolAlg k hk ((MvPolynomial.basisMonomials (Fin 3) ℂ) mu) :=
    hb.map' (symbolAlg k hk).toLinearMap (LinearMap.ker_eq_bot.mpr h)
  simpa only [MvPolynomial.coe_basisMonomials, symbolAlg_monomial k hk] using himage

/-- Exact reformulation of universal-symbol injectivity as depth-zero PBW independence modulo
`O₂`. -/
theorem symbolAlg_injective_iff_pureCurrentC2Independent :
    Function.Injective (symbolAlg k hk) ↔ PureCurrentC2Independent k hk :=
  ⟨pureCurrentC2Independent_of_symbolAlg_injective k hk,
    symbolAlg_injective_of_pureCurrentC2Independent k hk⟩

/-- Intermediate route to injectivity from affine PBW and explicit depth-zero/Li separation.
The separation hypothesis is discharged from the same ordinary PBW input below. -/
theorem symbolAlg_injective_of_PBWBasis_of_liSeparated
    (hPBW : PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k)
    (hsep : PureCurrentLiSeparated k) : Function.Injective (symbolAlg k hk) :=
  symbolAlg_injective_of_pureCurrentC2Independent k hk
    (pureCurrentC2Independent_of_PBWBasis_of_liSeparated k hk hPBW hsep)

/-- A filtered affine PBW basis proves universal-symbol injectivity directly. -/
theorem symbolAlg_injective_of_FilteredPBWBasis
    (hPBW : FilteredPBWBasis k) : Function.Injective (symbolAlg k hk) := by
  obtain ⟨B, hB, hspan⟩ := hPBW
  exact symbolAlg_injective_of_PBWBasis_of_liSeparated k hk ⟨B, hB⟩
    (pureCurrentLiSeparated_of_filteredPBW k B hB hspan)

/-! ## Ordinary PBW already supplies the filtered triangularity

The remainder of the file proves the positive-depth spanning clause by explicit affine
straightening.  The measure is `(word length, inversion count)`: swapping an inverted adjacent
pair decreases the second coordinate, while its commutator term has one fewer letter.  For two
negative modes the central term vanishes, and the bracket letter has depth `r+s+1`; hence no
commutator can lose the property of having positive total derivative depth.
-/

private abbrev PBWLetter := Fin 3 ×ₗ ℕ

/-- Interpret a lexicographically ordered affine PBW letter as a current letter. -/
private def currentLetter (q : PBWLetter) : Fin 3 × ℕ := ofLex q

@[simp] private theorem currentLetter_toLex (q : Fin 3 × ℕ) :
    currentLetter (toLex q) = q := ofLex_toLex q

/-- Interpret a list of affine PBW letters as a current creation word. -/
private def lexWordState (l : List PBWLetter) : WakModule k :=
  wordStateA k (l.map currentLetter)

/-- The total derivative depth of a list of affine PBW letters. -/
private def lexWordLevel (l : List PBWLetter) : ℕ :=
  (l.map fun q => (ofLex q).2).sum

/-- The canonical ordered list attached to a PBW exponent. -/
private def exponentWord (mu : PBWLetter →₀ ℕ) : List PBWLetter :=
  (mu.support.sort (fun a b => a ≤ b)).flatMap fun q => List.replicate (mu q) q

@[simp] private theorem lexWordState_nil : lexWordState k [] = vacuumA k := rfl

private theorem lexWordState_cons (q : PBWLetter) (l : List PBWLetter) :
    lexWordState k (q :: l) =
      J k (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) (lexWordState k l) := by
  simp [lexWordState, currentLetter, wordStateA_cons]

private theorem pbwWord_eq_map_exponentWord (mu : PBWLetter →₀ ℕ) :
    pbwWord (Pi.basisFun ℂ (Fin 3)) mu =
      (exponentWord mu).map (fun q => (basis (ofLex q).1, (ofLex q).2)) := by
  simp [pbwWord, exponentWord, List.map_flatMap, Pi.basisFun_apply, basis]

private theorem exponentWord_toMultiset (mu : PBWLetter →₀ ℕ) :
    (exponentWord mu : Multiset PBWLetter) = Finsupp.toMultiset mu := by
  classical
  rw [exponentWord, Finsupp.toMultiset_apply, Finsupp.sum]
  have hcoe : ∀ l : List PBWLetter,
      ((l.flatMap fun q => List.replicate (mu q) q : List PBWLetter) : Multiset PBWLetter) =
        (l.map fun q => mu q • ({q} : Multiset PBWLetter)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons q l ih =>
        change (List.replicate (mu q) q : Multiset PBWLetter) +
            (List.flatMap (fun q => List.replicate (mu q) q) l : Multiset PBWLetter) = _
        rw [Multiset.coe_replicate, ih]
        simp [Multiset.nsmul_singleton]
  rw [hcoe]
  have hs := congrArg Multiset.sum (congrArg (Multiset.map fun q : PBWLetter =>
      mu q • ({q} : Multiset PBWLetter))
    (mu.support.sort_eq (fun a b => a ≤ b)))
  exact hs

private theorem exponentWord_pairwise (mu : PBWLetter →₀ ℕ) :
    (exponentWord mu).Pairwise (fun a b => a ≤ b) := by
  classical
  have haux : ∀ l : List PBWLetter, l.Pairwise (fun a b => a ≤ b) →
      (l.flatMap fun q => List.replicate (mu q) q).Pairwise (fun a b => a ≤ b) := by
    intro l hl
    induction l with
    | nil => simp
    | cons q l ih =>
        rw [List.pairwise_cons] at hl
        simp only [List.flatMap_cons]
        rw [List.pairwise_append]
        refine ⟨List.pairwise_replicate_of_refl, ih hl.2, ?_⟩
        intro a ha b hb
        have ha' : a = q := List.eq_of_mem_replicate ha
        subst a
        simp only [List.mem_flatMap] at hb
        obtain ⟨r, hr, hbr⟩ := hb
        have hbr' : b = r := List.eq_of_mem_replicate hbr
        subst b
        exact hl.1 r hr
  exact haux _ (Finset.pairwise_sort _ _)

/-- A sorted list is the canonical exponent word of its multiplicity function. -/
private theorem eq_exponentWord_toFinsupp (l : List PBWLetter)
    (hl : l.Pairwise (fun a b => a ≤ b)) :
    l = exponentWord (Multiset.toFinsupp (l : Multiset PBWLetter)) := by
  classical
  have hcoe : (l : Multiset PBWLetter) =
      (exponentWord (Multiset.toFinsupp (l : Multiset PBWLetter)) : Multiset PBWLetter) := by
    rw [exponentWord_toMultiset, Multiset.toFinsupp_toMultiset]
  exact (Multiset.coe_eq_coe.mp hcoe).eq_of_pairwise' hl
    (exponentWord_pairwise (Multiset.toFinsupp (l : Multiset PBWLetter)))

/-- Positive total derivative depth is witnessed by one positive-depth letter. -/
private theorem exists_positiveDepth_of_lexWordLevel_pos :
    ∀ l : List PBWLetter, 0 < lexWordLevel l →
      ∃ q ∈ l, 0 < (ofLex q).2
  | [], h => by simp [lexWordLevel] at h
  | q :: l, h => by
      simp only [lexWordLevel, List.map_cons, List.sum_cons] at h
      by_cases hq : 0 < (ofLex q).2
      · exact ⟨q, by simp, hq⟩
      · have ht : 0 < lexWordLevel l := by
          simp only [lexWordLevel]
          omega
        obtain ⟨r, hr, hrd⟩ := exists_positiveDepth_of_lexWordLevel_pos l ht
        exact ⟨r, by simp [hr], hrd⟩

private theorem toFinsupp_mem_positiveDepthPBWIndices (l : List PBWLetter)
    (hl : 0 < lexWordLevel l) :
    Multiset.toFinsupp (l : Multiset PBWLetter) ∈ positiveDepthPBWIndices := by
  obtain ⟨q, hq, hqd⟩ := exists_positiveDepth_of_lexWordLevel_pos l hl
  refine ⟨(ofLex q).1, (ofLex q).2, hqd, ?_⟩
  rw [Multiset.toFinsupp_apply]
  exact Multiset.count_ne_zero.mpr (by simpa using hq)

private theorem basis_eq_lexWordState_exponentWord
    (B : Module.Basis (PBWLetter →₀ ℕ) ℂ (WakModule k))
    (hB : ∀ mu, B mu = AffineLie.negWord kappaForm kappaForm_isInvariant k
      (pbwWord (Pi.basisFun ℂ (Fin 3)) mu)) (mu : PBWLetter →₀ ℕ) :
    B mu = lexWordState k (exponentWord mu) := by
  rw [hB, pbwWord_eq_map_exponentWord]
  change AffineLie.negWord kappaForm kappaForm_isInvariant k
      ((exponentWord mu).map (fun q => (basis (ofLex q).1, (ofLex q).2))) =
    wordStateA k ((exponentWord mu).map currentLetter)
  simpa only [currentLetter, List.map_map, Function.comp_apply] using
    negWord_map_basis_eq_wordStateA k ((exponentWord mu).map currentLetter)

/-- A sorted positive-depth current word is one of the positive-depth PBW basis vectors. -/
private theorem sorted_lexWordState_mem_positiveSpan
    (B : Module.Basis (PBWLetter →₀ ℕ) ℂ (WakModule k))
    (hB : ∀ mu, B mu = AffineLie.negWord kappaForm kappaForm_isInvariant k
      (pbwWord (Pi.basisFun ℂ (Fin 3)) mu))
    (l : List PBWLetter) (hsort : l.Pairwise (fun a b => a ≤ b))
    (hlevel : 0 < lexWordLevel l) :
    lexWordState k l ∈ Submodule.span ℂ (B '' positiveDepthPBWIndices) := by
  let mu : PBWLetter →₀ ℕ := Multiset.toFinsupp (l : Multiset PBWLetter)
  have hl : l = exponentWord mu := eq_exponentWord_toFinsupp l hsort
  have hmu : mu ∈ positiveDepthPBWIndices :=
    toFinsupp_mem_positiveDepthPBWIndices l hlevel
  apply Submodule.subset_span
  refine ⟨mu, hmu, ?_⟩
  rw [basis_eq_lexWordState_exponentWord k B hB, ← hl]

/-- Number of inverted pairs in a list.  The recursive form is convenient for proving that an
adjacent transposition decreases it. -/
private def inversionCount : List PBWLetter → ℕ
  | [] => 0
  | q :: l => (l.filter fun r => r < q).length + inversionCount l

private theorem inversionCount_swap (pre post : List PBWLetter) (a b : PBWLetter)
    (hba : b < a) :
    inversionCount (pre ++ b :: a :: post) < inversionCount (pre ++ a :: b :: post) := by
  induction pre with
  | nil =>
      have hab : ¬a < b := not_lt_of_ge hba.le
      simp only [List.nil_append, inversionCount, List.filter_cons]
      simp [hba, hab]
      omega
  | cons q pre ih =>
      simp only [List.cons_append, inversionCount, List.filter_append, List.length_append,
        List.filter_cons]
      split_ifs <;> simp only [List.length_cons] at ih ⊢ <;> omega

/-- A non-sorted list in a linear order contains an adjacent inverted pair. -/
private theorem exists_adjacent_inversion_of_not_pairwise :
    ∀ l : List PBWLetter, ¬l.Pairwise (fun a b => a ≤ b) →
      ∃ (pre : List PBWLetter) (a b : PBWLetter) (post : List PBWLetter),
        b < a ∧ l = pre ++ a :: b :: post
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: b :: l, h => by
      by_cases hab : a ≤ b
      · have ht : ¬(b :: l).Pairwise (fun x y => x ≤ y) := by
          intro ht
          exact h ((List.pairwise_cons_cons_iff_of_trans).mpr ⟨hab, ht⟩)
        obtain ⟨pre, c, d, post, hdc, heq⟩ :=
          exists_adjacent_inversion_of_not_pairwise (b :: l) ht
        exact ⟨a :: pre, c, d, post, hdc, by simp [heq]⟩
      · exact ⟨[], a, b, l, lt_of_not_ge hab, rfl⟩

private theorem lexWordLevel_swap (pre post : List PBWLetter) (a b : PBWLetter) :
    lexWordLevel (pre ++ b :: a :: post) = lexWordLevel (pre ++ a :: b :: post) := by
  simp [lexWordLevel, List.sum_append]
  omega

private theorem lexWordLevel_bracket (pre post : List PBWLetter) (a b : PBWLetter)
    (c : Fin 3) :
    lexWordLevel (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post) =
      lexWordLevel (pre ++ a :: b :: post) + 1 := by
  simp [lexWordLevel, List.sum_append]
  omega

/-- Swapping two adjacent negative current modes produces the usual bracket term.  The central
term is absent because the sum of two strictly negative mode indices cannot vanish. -/
private theorem lexWordState_adjacent_swap
    (pre post : List PBWLetter) (a b : PBWLetter) :
    lexWordState k (pre ++ a :: b :: post) =
      lexWordState k (pre ++ b :: a :: post) +
        ∑ c : Fin 3, fabc (ofLex a).1 (ofLex b).1 c •
          lexWordState k
            (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post) := by
  induction pre with
  | nil =>
      simp only [List.nil_append]
      have h := congrArg (fun T : Module.End ℂ (WakModule k) => T (lexWordState k post))
        (current_comm k (ofLex a).1 (ofLex b).1
          (-((ofLex a).2 : ℤ) - 1) (-((ofLex b).2 : ℤ) - 1))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [sub_eq_iff_eq_add] at h
      have hnz : -((ofLex a).2 : ℤ) - 1 + (-((ofLex b).2 : ℤ) - 1) ≠ 0 := by
        omega
      rw [if_neg hnz] at h
      simp only [LinearMap.zero_apply, add_zero] at h
      have hm : -((ofLex a).2 : ℤ) - 1 + (-((ofLex b).2 : ℤ) - 1) =
          (-(((ofLex a).2 + (ofLex b).2 + 1 : ℕ) : ℤ) - 1) := by
        omega
      rw [hm] at h
      rw [add_comm (∑ c : Fin 3, fabc (ofLex a).1 (ofLex b).1 c •
        J k c (-↑((ofLex a).2 + (ofLex b).2 + 1) - 1) (lexWordState k post))] at h
      simpa only [lexWordState_cons, ofLex_toLex] using h
  | cons q pre ih =>
      simp only [List.cons_append, lexWordState_cons]
      rw [ih, map_add, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      rw [map_smul]

/-- Affine PBW straightening preserves positive total derivative depth.  This is the exact
filtered-triangularity theorem not packaged as a field of the bare `PBWBasis` interface. -/
private theorem lexWordState_mem_positiveSpan_of_level
    (B : Module.Basis (PBWLetter →₀ ℕ) ℂ (WakModule k))
    (hB : ∀ mu, B mu = AffineLie.negWord kappaForm kappaForm_isInvariant k
      (pbwWord (Pi.basisFun ℂ (Fin 3)) mu))
    (l : List PBWLetter) (hlevel : 0 < lexWordLevel l) :
    lexWordState k l ∈ Submodule.span ℂ (B '' positiveDepthPBWIndices) := by
  by_cases hsort : l.Pairwise (fun a b => a ≤ b)
  · exact sorted_lexWordState_mem_positiveSpan k B hB l hsort hlevel
  · obtain ⟨pre, a, b, post, hba, heq⟩ :=
      exists_adjacent_inversion_of_not_pairwise l hsort
    subst l
    have hswapLevel : 0 < lexWordLevel (pre ++ b :: a :: post) := by
      rw [lexWordLevel_swap pre post a b]
      exact hlevel
    have hswap := lexWordState_mem_positiveSpan_of_level B hB
      (pre ++ b :: a :: post) hswapLevel
    have hbracket : ∀ c : Fin 3,
        lexWordState k
            (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post) ∈
          Submodule.span ℂ (B '' positiveDepthPBWIndices) := by
      intro c
      apply lexWordState_mem_positiveSpan_of_level B hB
      rw [lexWordLevel_bracket pre post a b c]
      omega
    rw [lexWordState_adjacent_swap k]
    exact Submodule.add_mem _ hswap (Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (hbracket c))
termination_by (l.length, inversionCount l)
decreasing_by
  · rw [heq]
    rw [show (pre ++ b :: a :: post).length = (pre ++ a :: b :: post).length by simp]
    apply Prod.Lex.right
    exact inversionCount_swap pre post a b hba
  · rw [heq]
    apply Prod.Lex.left
    simp

/-! ## Ordinary PBW reduced to one explicit independence statement

The straightening argument above also proves the spanning half of ordinary affine PBW without
assuming a basis.  Consequently the named `PBWBasis` input is equivalent, in this concrete
`sl₂` vacuum module, to linear independence of the displayed ordered creation family.  This
pins the remaining library gap to the independence half of PBW; no hidden completeness condition
remains.
-/

/-- The ordered affine creation state indexed by its multiplicity function. -/
def orderedCreationState (mu : PBWLetter →₀ ℕ) : WakModule k :=
  AffineLie.negWord kappaForm kappaForm_isInvariant k
    (pbwWord (Pi.basisFun ℂ (Fin 3)) mu)

private theorem orderedCreationState_eq_lexWordState (mu : PBWLetter →₀ ℕ) :
    orderedCreationState k mu = lexWordState k (exponentWord mu) := by
  rw [orderedCreationState, pbwWord_eq_map_exponentWord]
  change AffineLie.negWord kappaForm kappaForm_isInvariant k
      ((exponentWord mu).map (fun q => (basis (ofLex q).1, (ofLex q).2))) =
    wordStateA k ((exponentWord mu).map currentLetter)
  simpa only [currentLetter, List.map_map, Function.comp_apply] using
    negWord_map_basis_eq_wordStateA k ((exponentWord mu).map currentLetter)

/-- Every basis-coloured negative-current word is in the span of ordered creation states. -/
private theorem lexWordState_mem_orderedCreationSpan
    (l : List PBWLetter) :
    lexWordState k l ∈ Submodule.span ℂ (Set.range (orderedCreationState k)) := by
  by_cases hsort : l.Pairwise (fun a b => a ≤ b)
  · let mu : PBWLetter →₀ ℕ := Multiset.toFinsupp (l : Multiset PBWLetter)
    have hl : l = exponentWord mu := eq_exponentWord_toFinsupp l hsort
    apply Submodule.subset_span
    refine ⟨mu, ?_⟩
    rw [orderedCreationState_eq_lexWordState k, ← hl]
  · obtain ⟨pre, a, b, post, hba, heq⟩ :=
      exists_adjacent_inversion_of_not_pairwise l hsort
    subst l
    have hswap := lexWordState_mem_orderedCreationSpan (pre ++ b :: a :: post)
    have hbracket : ∀ c : Fin 3,
        lexWordState k
            (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post) ∈
          Submodule.span ℂ (Set.range (orderedCreationState k)) := by
      intro c
      exact lexWordState_mem_orderedCreationSpan
        (pre ++ toLex (c, (ofLex a).2 + (ofLex b).2 + 1) :: post)
    rw [lexWordState_adjacent_swap k]
    exact Submodule.add_mem _ hswap (Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (hbracket c))
termination_by (l.length, inversionCount l)
decreasing_by
  · rw [heq]
    rw [show (pre ++ b :: a :: post).length = (pre ++ a :: b :: post).length by simp]
    apply Prod.Lex.right
    exact inversionCount_swap pre post a b hba
  · rw [heq]
    apply Prod.Lex.left
    simp

/-- The ordered creation states span the universal affine `sl₂` vacuum module.  This is the
spanning half of affine PBW, proved from current commutators and the already established spanning
by arbitrary basis-coloured words. -/
theorem orderedCreationState_span_eq_top :
    Submodule.span ℂ (Set.range (orderedCreationState k)) = ⊤ := by
  rw [eq_top_iff, ← wordStateA_span k, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have h := lexWordState_mem_orderedCreationSpan (k := k) (l.map toLex)
  have hl : (l.map toLex).map currentLetter = l := by
    rw [List.map_map]
    have hfun : (currentLetter ∘ fun q : Fin 3 × ℕ => toLex q) = id := by
      funext q
      exact currentLetter_toLex q
    simpa only [List.map_map, List.map_id_fun] using
      congrArg (fun f : (Fin 3 × ℕ) → (Fin 3 × ℕ) => l.map f) hfun
  rwa [lexWordState, hl] at h

/-- In the concrete affine `sl₂` vacuum module, the named ordinary `PBWBasis` package is
equivalent to linear independence of the explicit ordered creation family.  The spanning half is
the theorem `orderedCreationState_span_eq_top`; the right side is therefore the exact remaining
PBW input. -/
theorem pbwBasis_iff_orderedCreationState_linearIndependent :
    PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k ↔
      LinearIndependent ℂ (orderedCreationState k) := by
  constructor
  · intro hPBW
    simpa only [orderedCreationState] using PBWBasis.linearIndependent hPBW
  · intro hli
    let B : Module.Basis (PBWLetter →₀ ℕ) ℂ (WakModule k) :=
      Module.Basis.mk hli (orderedCreationState_span_eq_top k).ge
    refine ⟨B, fun mu => ?_⟩
    rw [show B mu = orderedCreationState k mu from Module.Basis.mk_apply hli _ mu]
    rfl

/-- **Filtered affine PBW straightening.**  Every positive-depth current word is a linear
combination of ordered PBW monomials containing a positive-depth letter.  This uses the affine
commutator and ordinary PBW basis data, but no `C₂` presentation or classical freeness. -/
theorem positiveDepthPBWSpanning_of_basis
    (B : Module.Basis (PBWLetter →₀ ℕ) ℂ (WakModule k))
    (hB : ∀ mu, B mu = AffineLie.negWord kappaForm kappaForm_isInvariant k
      (pbwWord (Pi.basisFun ℂ (Fin 3)) mu)) :
    PositiveDepthPBWSpanning k B := by
  rw [PositiveDepthPBWSpanning, currentWordPiece, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  have hlevel : 0 < lexWordLevel (w.map toLex) := by
    simpa only [lexWordLevel, List.map_map, Function.comp_apply, ofLex_toLex,
      currentWordLevel, pairsLevel] using hw
  have h := lexWordState_mem_positiveSpan_of_level k B hB (w.map toLex) hlevel
  have hwmap : (w.map toLex).map currentLetter = w := by
    rw [List.map_map]
    have hfun : (currentLetter ∘ fun q : Fin 3 × ℕ => toLex q) = id := by
      funext q
      exact currentLetter_toLex q
    simpa only [List.map_map, List.map_id_fun] using
      congrArg (fun f : (Fin 3 × ℕ) → (Fin 3 × ℕ) => w.map f) hfun
  rwa [lexWordState, hwmap] at h

/-- Ordinary affine PBW is automatically compatible with the positive-depth Li filtration. -/
theorem filteredPBWBasis_of_PBWBasis
    (hPBW : PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k) :
    FilteredPBWBasis k := by
  obtain ⟨B, hB⟩ := hPBW
  exact ⟨B, hB, positiveDepthPBWSpanning_of_basis k B hB⟩

/-- The filtered package adds no mathematical hypothesis: for affine `sl₂` it is equivalent
to the ordinary PBW basis theorem. -/
theorem filteredPBWBasis_iff_PBWBasis :
    FilteredPBWBasis k ↔
      PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k := by
  constructor
  · rintro ⟨B, hB, _⟩
    exact ⟨B, hB⟩
  · exact filteredPBWBasis_of_PBWBasis k

/-- Ordinary affine PBW separates the depth-zero current sector from positive Li depth. -/
theorem pureCurrentLiSeparated_of_PBWBasis
    (hPBW : PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k) :
    PureCurrentLiSeparated k :=
  pureCurrentLiSeparated_of_FilteredPBWBasis k (filteredPBWBasis_of_PBWBasis k hPBW)

/-- **Universal affine `sl₂` `C₂` presentation from ordinary PBW.**  The canonical polynomial
symbol map is injective at every noncritical level.  Surjectivity was already proved in
`AffineSl2Presentation`. -/
theorem symbolAlg_injective_of_PBWBasis
    (hPBW : PBWBasis kappaForm kappaForm_isInvariant (Pi.basisFun ℂ (Fin 3)) k) :
    Function.Injective (symbolAlg k hk) :=
  symbolAlg_injective_of_PBWBasis_of_liSeparated k hk hPBW
    (pureCurrentLiSeparated_of_PBWBasis k hPBW)


/-! ## All-depth filtered PBW straightening -/

/-- Total derivative depth of an ordered affine PBW monomial. -/
def orderedCreationDepth (mu : (Fin 3 ×ₗ ℕ) →₀ ℕ) : ℕ :=
  lexWordLevel (exponentWord mu)

private theorem lexWordState_mem_depthSpan
    (p : ℕ) (l : List PBWLetter) (hlevel : p ≤ lexWordLevel l) :
    lexWordState k l ∈ Submodule.span ℂ
      (orderedCreationState k '' {mu | p ≤ orderedCreationDepth mu}) := by
  by_cases hsort : l.Pairwise (fun a b => a ≤ b)
  · let mu : PBWLetter →₀ ℕ := Multiset.toFinsupp (l : Multiset PBWLetter)
    have hl : l = exponentWord mu := eq_exponentWord_toFinsupp l hsort
    apply Submodule.subset_span
    refine ⟨mu, ?_, ?_⟩
    · change p ≤ lexWordLevel (exponentWord mu)
      rwa [← hl]
    · rw [orderedCreationState_eq_lexWordState, ← hl]
  · obtain ⟨pre,a,b,post,hba,heq⟩ := exists_adjacent_inversion_of_not_pairwise l hsort
    subst l
    have hswapLevel : p ≤ lexWordLevel (pre ++ b :: a :: post) := by
      rw [lexWordLevel_swap]
      exact hlevel
    have hswap := lexWordState_mem_depthSpan p (pre ++ b :: a :: post) hswapLevel
    have hbracket : ∀ c : Fin 3,
        lexWordState k (pre ++ toLex (c,(ofLex a).2+(ofLex b).2+1) :: post) ∈
          Submodule.span ℂ (orderedCreationState k '' {mu | p ≤ orderedCreationDepth mu}) := by
      intro c
      apply lexWordState_mem_depthSpan p
      rw [lexWordLevel_bracket]
      omega
    rw [lexWordState_adjacent_swap k]
    exact Submodule.add_mem _ hswap (Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (hbracket c))
termination_by (l.length,inversionCount l)
decreasing_by
  · rw [heq]
    rw [show (pre ++ b :: a :: post).length = (pre ++ a :: b :: post).length by simp]
    apply Prod.Lex.right
    exact inversionCount_swap pre post a b hba
  · rw [heq]
    apply Prod.Lex.left
    simp

/-- The entire Li current-word filtration is the ordered PBW span above each depth threshold.
This is proved by affine commutators, without adding a filtered-PBW assumption. -/
theorem currentWordPiece_eq_orderedDepthSpan (p : ℕ) :
    currentWordPiece k p = Submodule.span ℂ
      (orderedCreationState k '' {mu | p ≤ orderedCreationDepth mu}) := by
  apply le_antisymm
  · rw [currentWordPiece, Submodule.span_le]
    rintro _ ⟨w,hw,rfl⟩
    have hlevel : p ≤ lexWordLevel (w.map toLex) := by
      simpa only [lexWordLevel,List.map_map,Function.comp_apply,ofLex_toLex,
        currentWordLevel,pairsLevel] using hw
    have h := lexWordState_mem_depthSpan k p (w.map toLex) hlevel
    have hwmap : (w.map toLex).map currentLetter = w := by
      simp only [List.map_map]
      have heq : (currentLetter ∘ fun q : Fin 3 × ℕ => toLex q) = id := by
        funext q
        exact currentLetter_toLex q
      rw [heq,List.map_id]
    rwa [lexWordState,hwmap] at h
  · apply Submodule.span_le.mpr
    rintro _ ⟨mu,hmu,rfl⟩
    rw [orderedCreationState_eq_lexWordState,lexWordState]
    apply wordStateA_mem_currentWordPiece
    simpa only [orderedCreationDepth,lexWordLevel,currentWordLevel,pairsLevel,
      List.map_map,Function.comp_apply,currentLetter] using hmu

/-- All-depth Li filtration equality for the universal affine sl2 VOA. -/
theorem liFiltration_eq_orderedDepthSpan (p : ℕ) :
    liFiltration (affineSl2VOA_closed k hk) p = Submodule.span ℂ
      (orderedCreationState k '' {mu | p ≤ orderedCreationDepth mu}) := by
  rw [liFiltration_eq_currentWordPiece k hk p, currentWordPiece_eq_orderedDepthSpan]

end
end AffineSl2UniversalC2PBW
end VOA

section AxiomAudit
#print axioms VOA.AffineSl2UniversalC2PBW.symbolAlg_monomial
#print axioms VOA.AffineSl2UniversalC2PBW.pureCurrentState_linearIndependent_of_PBWBasis
#print axioms VOA.AffineSl2UniversalC2PBW.symbolAlg_injective_of_pureCurrentC2Independent
#print axioms VOA.AffineSl2UniversalC2PBW.symbolAlg_injective_iff_pureCurrentC2Independent
#print axioms VOA.AffineSl2UniversalC2PBW.symbolAlg_injective_of_PBWBasis_of_liSeparated
#print axioms VOA.AffineSl2UniversalC2PBW.symbolAlg_injective_of_FilteredPBWBasis
#print axioms VOA.AffineSl2UniversalC2PBW.positiveDepthPBWSpanning_of_basis
#print axioms VOA.AffineSl2UniversalC2PBW.orderedCreationState_span_eq_top
#print axioms VOA.AffineSl2UniversalC2PBW.pbwBasis_iff_orderedCreationState_linearIndependent
#print axioms VOA.AffineSl2UniversalC2PBW.filteredPBWBasis_of_PBWBasis
#print axioms VOA.AffineSl2UniversalC2PBW.filteredPBWBasis_iff_PBWBasis
#print axioms VOA.AffineSl2UniversalC2PBW.symbolAlg_injective_of_PBWBasis
end AxiomAudit
