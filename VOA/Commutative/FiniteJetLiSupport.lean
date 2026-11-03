/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FiniteWeightedJet

/-!
# Support of finite jet Li bidegrees

For generators of positive conformal weight, a jet monomial of Li/conformal bidegree `(p,N)`
can occur only when `p <= N`.  This elementary support statement lets a one-variable character
identity be used in the Li-degree Hilbert squeeze: at conformal weight `N`, only the finite window
`p = 0, ..., N` contributes.
-/

namespace VOA.FiniteJet

universe uR uSigma

variable {R : Type uR} {sigma : Type uSigma} [CommRing R]

/-- Positive generator weights force Li degree to be at most conformal weight for every
nonzero jet monomial. -/
theorem liDegree_le_conformalWeight_of_weight_eq
    (baseWeight : sigma -> Nat) (m p N : Nat) (d : JetVar sigma m →₀ Nat)
    (hd : Finsupp.weight (jetLiBidegree baseWeight m) d = (p, N)) :
    p <= N := by
  have hfst := congrArg Prod.fst hd
  have hsnd := congrArg Prod.snd hd
  simp only [Finsupp.weight_apply, Finsupp.sum, jetLiBidegree,
    Prod.fst_sum, Prod.snd_sum] at hfst hsnd
  rw [<- hfst, <- hsnd]
  apply Finset.sum_le_sum
  intro v hv
  apply Nat.mul_le_mul_left
  exact Nat.le_add_left v.order (baseWeight v.generator)

/-- If `N < p`, the exact jet-polynomial bidegree `(p,N)` is zero. -/
theorem jetLiBidegreePiece_eq_bot_of_conformalWeight_lt_liDegree
    (baseWeight : sigma -> Nat) (m p N : Nat) (hNp : N < p) :
    JetLiBidegreePiece R baseWeight m p N = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_bot]
    apply MvPolynomial.ext
    intro d
    by_contra hcoeff
    exact (Nat.not_le_of_gt hNp)
      (liDegree_le_conformalWeight_of_weight_eq baseWeight m p N d (hf hcoeff))
  · exact bot_le

/-- The presented image of an impossible Li bidegree is zero as well. -/
theorem presentedJetLiBidegreeImage_eq_bot_of_conformalWeight_lt_liDegree
    (baseWeight : sigma -> Nat) (m p N : Nat) (hNp : N < p)
    (I : Ideal (MvPolynomial sigma R)) :
    PresentedJetLiBidegreeImage (R := R) baseWeight m p N I = ⊥ := by
  rw [PresentedJetLiBidegreeImage,
    jetLiBidegreePiece_eq_bot_of_conformalWeight_lt_liDegree
      baseWeight m p N hNp]
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [Submodule.mem_bot]
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, map_zero]
  · exact bot_le

end VOA.FiniteJet

section AxiomAudit
#print axioms VOA.FiniteJet.liDegree_le_conformalWeight_of_weight_eq
#print axioms VOA.FiniteJet.jetLiBidegreePiece_eq_bot_of_conformalWeight_lt_liDegree
#print axioms VOA.FiniteJet.presentedJetLiBidegreeImage_eq_bot_of_conformalWeight_lt_liDegree
end AxiomAudit
