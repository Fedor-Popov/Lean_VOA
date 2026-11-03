import VOA.DeligneAudit.SL4TTwoAlphabet

/-! # Simultaneous boundary quotients in the two alphabets -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- `true` removes a root; `false` removes a complementary root. -/
def boundaryIndex (d : ℕ) (cutE : Bool) : ℕ := if cutE then d - 1 else d

def boundaryPoly (M d : ℕ) (cutE : Bool) : SymPoly :=
  if cutE then elementary d else complete (M - d)

def BoundaryAllowed (M d : ℕ) (cutE : Bool) : Prop :=
  if cutE then 0 < d else d < M

theorem grassIdeal_boundary (M d : ℕ) (cutE : Bool) (hd : d ≤ M)
    (hc : BoundaryAllowed M d cutE) :
    grassIdeal (boundaryIndex d cutE) (M - 1 - boundaryIndex d cutE) =
      grassIdeal d (M - d) ⊔ Ideal.span {boundaryPoly M d cutE} := by
  cases cutE with
  | false =>
      simp only [boundaryIndex, boundaryPoly, BoundaryAllowed, Bool.false_eq_true,
        if_false] at *
      have hw : M - d = (M - 1 - d) + 1 := by omega
      rw [hw]
      exact grassIdeal_peel_h d (M - 1 - d)
  | true =>
      simp only [boundaryIndex, boundaryPoly, BoundaryAllowed, if_true] at *
      rw [show M - 1 - (d - 1) = M - d by omega]
      simpa only [Nat.sub_add_cancel (show 1 ≤ d by omega)] using
        grassIdeal_peel_e (d - 1) (M - d)

/-- The two new relations in the fixed ambient polynomial ring. -/
def biBoundaryRel (M a b : ℕ) (cutL cutR : Bool) : Ideal BiSymPoly :=
  Ideal.span {alphabetIn false (boundaryPoly M a cutL)} ⊔
    Ideal.span {alphabetIn true (boundaryPoly M b cutR)}

/-- The corresponding ideal of `S_M(a,b)`. -/
def boundaryIdeal (M a b : ℕ) (cutL cutR : Bool) : Ideal (S M a b) :=
  (biBoundaryRel M a b cutL cutR).map
    (Ideal.Quotient.mkₐ ℂ (biGrassIdeal a (M - a) b (M - b)))

theorem boundaryIdeal_eq (M a b : ℕ) (cutL cutR : Bool) :
    boundaryIdeal M a b cutL cutR =
      Ideal.span {if cutL then leftE M a b a else leftH M a b (M - a)} ⊔
        Ideal.span {if cutR then rightE M a b b else rightH M a b (M - b)} := by
  cases cutL <;> cases cutR <;>
    simp [boundaryIdeal, biBoundaryRel, boundaryPoly, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, leftE, rightE, leftH, rightH, eClass, hClass,
      biLeft_mk, biRight_mk, Ideal.Quotient.mkₐ_eq_mk]

theorem biGrassIdeal_boundary (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) :
    biGrassIdeal (boundaryIndex a cutL) (M - 1 - boundaryIndex a cutL)
        (boundaryIndex b cutR) (M - 1 - boundaryIndex b cutR) =
      biGrassIdeal a (M - a) b (M - b) ⊔ biBoundaryRel M a b cutL cutR := by
  simp only [biGrassIdeal, grassIdeal_boundary M a cutL ha hL,
    grassIdeal_boundary M b cutR hb hR, Ideal.map_sup, Ideal.map_span,
    Set.image_singleton, biBoundaryRel]
  ac_rfl

/-- All four boundary identifications, with exactly their valid index ranges. -/
def S_boundary_quot (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) :
    (S M a b ⧸ boundaryIdeal M a b cutL cutR) ≃ₐ[ℂ]
      S (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ ℂ (biGrassIdeal a (M - a) b (M - b))
    (biBoundaryRel M a b cutL cutR)).trans
      (Ideal.quotientEquivAlgOfEq ℂ (biGrassIdeal_boundary M a b cutL cutR ha hb hL hR).symm)

theorem S_boundary_quot_mk (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (p : BiSymPoly) :
    S_boundary_quot M a b cutL cutR ha hb hL hR
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ p)) = Ideal.Quotient.mk _ p := by
  exact Ideal.quotientEquivAlgOfEq_mk ℂ
    (biGrassIdeal_boundary M a b cutL cutR ha hb hL hR).symm p

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.grassIdeal_boundary
#print axioms VOA.DeligneAudit.SL4T.boundaryIdeal_eq
#print axioms VOA.DeligneAudit.SL4T.biGrassIdeal_boundary
#print axioms VOA.DeligneAudit.SL4T.S_boundary_quot
#print axioms VOA.DeligneAudit.SL4T.S_boundary_quot_mk
