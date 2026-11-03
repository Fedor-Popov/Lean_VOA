/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2JointGram

/-!
# Opposite-charge indexing of the affine Gram determinant

Swapping the e and f multiplicities preserves PBW energy and negates Cartan
charge. This gives a concrete bijection between opposite joint index sets,
so the actual bilinear Gram block becomes a square polynomial matrix without
an unspecified dimension comparison or a choice of matching columns.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineSl2PBWWakimotoReduction Sl2NonLisse

/-- An additive statistic of a coloured creation word expands as the sum of
multiplicities times the statistic of each PBW letter. -/
theorem orderedPBW_statistic (f : Fin 3 × ℕ → ℤ) (mu : CurrentIndex) :
    ((orderedPBWColorWord mu).map f).sum =
      mu.sum (fun q a => (a:ℤ) * f (ofLex q)) := by
  classical
  have hf (l : List (Fin 3 ×ₗ ℕ)) :
      ((l.flatMap (fun q => List.replicate (mu q) ((ofLex q).1,(ofLex q).2))).map f).sum =
        (l.map (fun q => (mu q:ℤ) * f (ofLex q))).sum := by
    induction l with
    | nil => rfl
    | cons q l ih => simp [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_replicate, List.sum_replicate, ih]
  rw [orderedPBWColorWord, hf, ← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  simp only [Finset.sort_toFinset]
  rfl

/-- The energy statistic is the sum of depth-plus-one over all letters. -/
theorem wordDegA_eq_sum (w : List (Fin 3 × ℕ)) :
    wordDegA w = (w.map (fun q => (q.2:ℤ)+1)).sum := by
  induction w with
  | nil => rfl
  | cons q w ih => simp only [wordDegA_cons, List.map_cons, List.sum_cons, ih]

/-- The Cartan statistic is the sum of colour charges over all letters. -/
theorem wordCharge_eq_sum (w : List (Fin 3 × ℕ)) :
    wordCharge w = (w.map (fun q => colourCharge q.1)).sum := by
  induction w with
  | nil => rfl
  | cons q w ih => simp only [wordCharge_cons, List.map_cons, List.sum_cons, ih]

/-- Energy in fixed PBW coordinates is independent of ordering the letters. -/
theorem currentEnergy_sum (mu : CurrentIndex) :
    currentEnergy mu = mu.sum (fun q a => (a:ℤ) * ((ofLex q).2+1)) := by
  rw [currentEnergy, wordDegA_eq_sum, orderedPBW_statistic]

/-- Cartan charge in fixed PBW coordinates is the signed colour count. -/
theorem currentCharge_sum (mu : CurrentIndex) :
    currentCharge mu = mu.sum (fun q a => (a:ℤ) * colourCharge (ofLex q).1) := by
  rw [currentCharge, wordCharge_eq_sum, orderedPBW_statistic]

/-- Interchange e and f while keeping the h colour and the negative depth. -/
noncomputable def flipCurrentLetter (q : Fin 3 ×ₗ ℕ) : Fin 3 ×ₗ ℕ :=
  toLex (Equiv.swap (0:Fin 3) 1 (ofLex q).1, (ofLex q).2)

/-- Swapping the two colours twice restores the original PBW letter. -/
theorem flipCurrentLetter_involutive : Function.Involutive flipCurrentLetter := by
  intro q
  simp [flipCurrentLetter]

/-- Relabel all multiplicities by the colour swap. Repeated labels are handled
by finite-support pushforward, although the swap is in fact a bijection. -/
noncomputable def flipCurrentIndex (mu : CurrentIndex) : CurrentIndex :=
  Finsupp.mapDomain flipCurrentLetter mu

/-- The multiplicity swap is an involution. -/
theorem flipCurrentIndex_involutive : Function.Involutive flipCurrentIndex := by
  intro mu
  simp only [flipCurrentIndex, ← Finsupp.mapDomain_comp]
  have he : flipCurrentLetter ∘ flipCurrentLetter = id :=
    funext flipCurrentLetter_involutive
  rw [he, Finsupp.mapDomain_id]

/-- Colour swapping leaves every negative depth and hence total energy unchanged. -/
theorem currentEnergy_flip (mu : CurrentIndex) :
    currentEnergy (flipCurrentIndex mu) = currentEnergy mu := by
  rw [currentEnergy_sum, currentEnergy_sum, flipCurrentIndex]
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · intro q; simp
  · intro q a b; push_cast; ring

/-- Swapping e and f negates their charges, while h remains neutral. -/
theorem colourCharge_swap (a : Fin 3) :
    colourCharge (Equiv.swap (0:Fin 3) 1 a) = -colourCharge a := by
  fin_cases a <;> norm_num [colourCharge, Equiv.swap_apply_def]

/-- The PBW multiplicity swap reverses the actual horizontal charge. -/
theorem currentCharge_flip (mu : CurrentIndex) :
    currentCharge (flipCurrentIndex mu) = -currentCharge mu := by
  rw [currentCharge_sum, currentCharge_sum, flipCurrentIndex]
  rw [Finsupp.sum_mapDomain_index]
  · simp only [flipCurrentLetter, ofLex_toLex, colourCharge_swap, mul_neg,
      Finsupp.sum, Finset.sum_neg_distrib]
  · intro q; simp
  · intro q a b; push_cast; ring

/-- A concrete bijection between the two opposite Cartan PBW index sets at
the same energy. This proves the equality of block sizes at every level. -/
noncomputable def jointChargeEquiv (n h : ℤ) : JointIndex n h ≃ JointIndex n (-h) where
  toFun i := ⟨flipCurrentIndex i.val, by simp only [currentEnergy_flip,
    currentCharge_flip, i.property.1, i.property.2, and_self]⟩
  invFun i := ⟨flipCurrentIndex i.val, by simp only [currentEnergy_flip,
    currentCharge_flip, i.property.1, i.property.2, neg_neg, and_self]⟩
  left_inv i := Subtype.ext (flipCurrentIndex_involutive _)
  right_inv i := Subtype.ext (flipCurrentIndex_involutive _)

/-- Opposite joint spaces have the same exact finite dimension. -/
theorem jointIndex_card_neg (n h : ℤ) :
    Fintype.card (JointIndex n h) = Fintype.card (JointIndex n (-h)) :=
  Fintype.card_congr (jointChargeEquiv n h)

/-- The actual opposite-charge Gram block as a square polynomial matrix,
using the explicit colour-swap bijection for its columns. -/
noncomputable def jointGramSquare (n h : ℤ) :
    Matrix (JointIndex n h) (JointIndex n h) (Polynomial ℂ) :=
  fun i j => jointGramPolynomial n h i (jointChargeEquiv n h j)

/-- The ordinary determinant of the actual joint Gram block. Its zero and
simple-root properties at admissible levels are not asserted by this definition. -/
noncomputable def jointDeterminant (n h : ℤ) : Polynomial ℂ := by
  classical
  exact (jointGramSquare n h).det

/-- A zero of the actual joint determinant yields a nonzero universal PBW
combination that vanishes in the simple quotient. This extracts an ordinary
relation from a proved root; it does not assert such a root exists. -/
theorem jointDeterminant_root_relation (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)
    (n h : ℤ) (hz : (jointDeterminant n h).eval k = 0) :
    ∃ r : JointIndex n h → ℂ,
      (∑ i, r i • currentPBWBasis k hk i.val) ≠ 0 ∧
      (∑ i, r i • currentWord k hk (jointWord n h i) (simple k hk).vacuum) = 0 := by
  classical
  have hm : ((Polynomial.evalRingHom k).mapMatrix (jointGramSquare n h)).det = 0 := by
    rw [← RingHom.map_det]
    exact hz
  obtain ⟨r,hrne,hr⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hm
  refine ⟨r, ?_, jointGram_row_relation k hk hk0 n h r ?_⟩
  · intro he
    have hc := Fintype.linearIndependent_iff.mp (jointWords_linearIndependent k hk n h) r he
    exact hrne (funext hc)
  · intro j
    obtain ⟨i,rfl⟩ := (jointChargeEquiv n h).surjective j
    have hh := congrFun hr i
    simpa only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
      jointGramSquare, Pi.zero_apply] using hh

end VOA.AffineSl2GeneralRigidity
