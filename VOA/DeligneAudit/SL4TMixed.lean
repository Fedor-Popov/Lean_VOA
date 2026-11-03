import VOA.DeligneAudit.SL4TCore

/-!
# Mixed multiplicity rings and the boundary part of Lemma Q

The five alphabets use one fixed polynomial ring. Killing the elementary tails
leaves exactly the generators in the paper; the complete and relative relations
are the finite windows (H) and (F), without replacing them by stronger tail ideals.
Integer parameters preserve invalid states when a zero length is decremented.

The four b-state ideals and parameter changes are defined here. The invalid-state
direction of Lemma Q is proved. The valid-state isomorphisms and the transport of
the characteristic polynomial remain to be proved.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

structure MixedParams where
  A : ℤ
  B : ℤ
  d1 : ℤ
  d2 : ℤ
  d3 : ℤ
  e1 : ℤ
  e2 : ℤ
  deriving DecidableEq

def mixedP (q : MixedParams) : ℤ := q.d1 + q.B - q.d2
def mixedQ (q : MixedParams) : ℤ := q.d2 + q.A - q.d3
def mixedWeight (q : MixedParams) : ℤ := q.e1 + mixedQ q - q.e2

def MixedValid (q : MixedParams) : Prop :=
  0 ≤ q.A ∧ 0 ≤ q.B ∧ 0 ≤ q.d1 ∧ q.d1 ≤ q.A ∧ 0 ≤ q.d2 ∧ q.d2 ≤ q.B ∧
    0 ≤ q.d3 ∧ q.d3 ≤ q.A ∧ 0 ≤ q.e1 ∧ q.e1 ≤ mixedP q ∧
      0 ≤ q.e2 ∧ q.e2 ≤ mixedQ q

abbrev MixedPoly := MvPolynomial (Fin 5 × ℕ) ℂ

/-- Alphabet order: x1, x2, x3, g1, g2. -/
def mixedAlphabet (i : Fin 5) : SymPoly →ₐ[ℂ] MixedPoly :=
  MvPolynomial.rename (fun j => (i, j))

def mixedE (i : Fin 5) (j : ℕ) : MixedPoly := mixedAlphabet i (elementary j)
def mixedH (i : Fin 5) (j : ℕ) : MixedPoly := mixedAlphabet i (complete j)

/-- Coefficient convolution, used for the unsigned elementary series E(s). -/
def mixedConv (f g : ℕ → MixedPoly) (n : ℕ) : MixedPoly :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

def mixedU : ℕ → MixedPoly := mixedConv (mixedE 0) (fun j => (-1) ^ j * mixedH 1 j)
def mixedV : ℕ → MixedPoly := mixedConv (mixedE 1) (fun j => (-1) ^ j * mixedH 2 j)
def mixedG1prime : ℕ → MixedPoly := mixedConv mixedU (fun j => (-1) ^ j * mixedH 3 j)
def mixedG2prime : ℕ → MixedPoly := mixedConv mixedV (fun j => (-1) ^ j * mixedH 4 j)

theorem mixed_series_zero :
    (∀ i, mixedE i 0 = 1) ∧ (∀ i, mixedH i 0 = 1) ∧
      mixedU 0 = 1 ∧ mixedV 0 = 1 ∧ mixedG1prime 0 = 1 ∧ mixedG2prime 0 = 1 := by
  simp [mixedE, mixedH, mixedU, mixedV, mixedG1prime, mixedG2prime, mixedConv]

def mixedLengths (q : MixedParams) : Fin 5 → ℕ :=
  ![q.d1.toNat, q.d2.toNat, q.d3.toNat, q.e1.toNat, q.e2.toNat]

/-- Exactly the generator tails and the five finite relation windows of §2.1. -/
def mixedRelations (q : MixedParams) : Set MixedPoly := {f |
  (∃ i j, mixedLengths q i < j ∧ mixedE i j = f) ∨
  (∃ j, (q.A - q.d1).toNat < j ∧ j ≤ q.A.toNat ∧ mixedH 0 j = f) ∨
  (∃ j, (q.B - q.d2).toNat < j ∧ j ≤ q.B.toNat ∧ mixedH 1 j = f) ∨
  (∃ j, (q.A - q.d3).toNat < j ∧ j ≤ q.A.toNat ∧ mixedH 2 j = f) ∨
  (∃ j, (mixedP q - q.e1).toNat < j ∧ j ≤ (mixedP q).toNat ∧ mixedG1prime j = f) ∨
  (∃ j, (mixedQ q - q.e2).toNat < j ∧ j ≤ (mixedQ q).toNat ∧ mixedG2prime j = f)}

def mixedIdeal (q : MixedParams) : Ideal MixedPoly := by
  classical
  exact if MixedValid q then Ideal.span (mixedRelations q) else ⊤

/-- The ring R(A,B;d1,d2,d3,e1,e2), with the zero ring for invalid tuples. -/
abbrev MixedRing (q : MixedParams) := MixedPoly ⧸ mixedIdeal q

theorem mixedRelation_zero (q : MixedParams) (hq : MixedValid q)
    (f : MixedPoly) (hf : f ∈ mixedRelations q) :
    Ideal.Quotient.mk (mixedIdeal q) f = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [mixedIdeal, if_pos hq]
  exact Ideal.subset_span hf

theorem mixedRing_invalid (q : MixedParams) (hq : ¬ MixedValid q) :
    Subsingleton (MixedRing q) := by
  apply Ideal.Quotient.subsingleton_iff.mpr
  rw [mixedIdeal, if_neg hq]

/-- The b-site order is s1, d1, s2, d2. -/
inductive MixedBState
  | s1 | d1 | s2 | d2
  deriving DecidableEq

def mixedBNext (q : MixedParams) : MixedBState → MixedParams
  | .s1 => {q with B := q.B - 1}
  | .d1 => {q with B := q.B - 1, e1 := q.e1 - 1}
  | .s2 => {q with B := q.B - 1, d2 := q.d2 - 1, e2 := q.e2 - 1}
  | .d2 => {q with B := q.B - 1, d2 := q.d2 - 1}

def mixedBZeroRoots : MixedBState → ℕ
  | .s1 | .s2 => 0
  | .d1 | .d2 => 1

def mixedBPair (q : MixedParams) : MixedBState → MixedPoly × MixedPoly
  | .s1 => (mixedH 1 (q.B - q.d2).toNat, mixedG1prime (mixedP q - q.e1).toNat)
  | .d1 => (mixedH 1 (q.B - q.d2).toNat, mixedE 3 q.e1.toNat)
  | .s2 => (mixedE 1 q.d2.toNat, mixedE 4 q.e2.toNat)
  | .d2 => (mixedE 1 q.d2.toNat, mixedG2prime (mixedQ q - q.e2).toNat)

def mixedBStateIdeal (q : MixedParams) (s : MixedBState) : Ideal (MixedRing q) :=
  Ideal.span {Ideal.Quotient.mk (mixedIdeal q) (mixedBPair q s).1,
    Ideal.Quotient.mk (mixedIdeal q) (mixedBPair q s).2}

theorem mixedBNext_sites (q : MixedParams) (s : MixedBState) :
    (mixedBNext q s).A + (mixedBNext q s).B = q.A + q.B - 1 := by
  cases s <;> simp [mixedBNext] <;> omega

theorem mixedBNext_weight (q : MixedParams) (s : MixedBState) :
    mixedWeight q = mixedWeight (mixedBNext q s) + (mixedBZeroRoots s : ℤ) := by
  cases s <;> simp [mixedWeight, mixedQ, mixedBNext, mixedBZeroRoots] <;> omega

def mixedBBoundary (q : MixedParams) : MixedBState → Prop
  | .s1 => q.d2 = q.B ∨ q.e1 = mixedP q
  | .d1 => q.d2 = q.B ∨ q.e1 = 0
  | .s2 => q.d2 = 0 ∨ q.e2 = 0
  | .d2 => q.d2 = 0 ∨ q.e2 = mixedQ q

/-- Exact boundary conditions, with no natural subtraction of parameter lengths. -/
theorem mixedBNext_invalid_iff (q : MixedParams) (hq : MixedValid q) (hB : 1 ≤ q.B)
    (s : MixedBState) : ¬ MixedValid (mixedBNext q s) ↔ mixedBBoundary q s := by
  cases s <;>
    simp only [MixedValid, mixedP, mixedQ, mixedBNext, mixedBBoundary] at * <;> omega

theorem mixedBPair_one_of_invalid (q : MixedParams) (hq : MixedValid q) (hB : 1 ≤ q.B)
    (s : MixedBState) (hs : ¬ MixedValid (mixedBNext q s)) :
    (mixedBPair q s).1 = 1 ∨ (mixedBPair q s).2 = 1 := by
  have hb := (mixedBNext_invalid_iff q hq hB s).mp hs
  obtain ⟨he, hh, _, _, hg1, hg2⟩ := mixed_series_zero
  cases s with
  | s1 =>
      rcases hb with h | h
      · exact Or.inl (by simp [mixedBPair, h, hh])
      · exact Or.inr (by simp [mixedBPair, h, hg1])
  | d1 =>
      rcases hb with h | h
      · exact Or.inl (by simp [mixedBPair, h, hh])
      · exact Or.inr (by simp [mixedBPair, h, he])
  | s2 =>
      rcases hb with h | h
      · exact Or.inl (by simp [mixedBPair, h, he])
      · exact Or.inr (by simp [mixedBPair, h, he])
  | d2 =>
      rcases hb with h | h
      · exact Or.inl (by simp [mixedBPair, h, he])
      · exact Or.inr (by simp [mixedBPair, h, hg2])

/-- The four invalid-state ideals are the whole ring, as in Lemma Q. -/
theorem mixedBStateIdeal_eq_top_of_invalid (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) (s : MixedBState) (hs : ¬ MixedValid (mixedBNext q s)) :
    mixedBStateIdeal q s = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  rcases mixedBPair_one_of_invalid q hq hB s hs with h | h <;> simp [h]

/-- The invalid-state direction of Lemma Q, uniformly for all four b-site states. -/
theorem mixedBState_invalid (q : MixedParams) (hq : MixedValid q) (hB : 1 ≤ q.B)
    (s : MixedBState) (hs : ¬ MixedValid (mixedBNext q s)) :
    Subsingleton (MixedRing q ⧸ mixedBStateIdeal q s) :=
  Ideal.Quotient.subsingleton_iff.mpr (mixedBStateIdeal_eq_top_of_invalid q hq hB s hs)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixed_series_zero
#print axioms VOA.DeligneAudit.SL4T.mixedRelation_zero
#print axioms VOA.DeligneAudit.SL4T.mixedRing_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_sites
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_weight
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_invalid_iff
#print axioms VOA.DeligneAudit.SL4T.mixedBPair_one_of_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedBStateIdeal_eq_top_of_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedBState_invalid
