/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.DeligneAudit.A2Relations
import VOA.DeligneAudit.A2Instance

/-!
# The A₂ geometric carrier embedding

For the explicit A₂ ideal `A2.I2ns = (V(θ) ⊂ Sym² sl₃)`, this file

* writes each relation `A2.relationPoly a` as `quadraticRelation (A2.relationMatrix a)` for an
  explicit, sparse coefficient matrix (`A2.relationPoly_eq_quadraticRelation`), so that
  `A2.I2ns = quadraticIdeal A2.relationMatrix` (`A2.I2ns_eq_quadraticIdeal`);
* defines the literal A₂ current carrier `A2.Carrier p N` (symmetric `sl₃^{⊗(N-p)}`-valued
  polynomials of degree `p` satisfying the eight quadratic collision equations);
* proves **`A2.geometricCarrierEmbedding`**: `GeometricCarrierEmbedding .A2 W P A2.Carrier` for
  every presentation `P` with `P.ideal = A2.I2ns` (any VOA `W`; in particular
  `A2.W = L_{-3/2}(sl₃)`);
* states the A₂ endgame: classical freeness from `CurrentJetSurjectivity` and the single named
  residual `QuadraticCarrierUpperBound A2.relationMatrix W` (`A2.classicallyFree_of_upperBound`).

No representation-theoretic input enters the embedding.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial
open VOA.QuadraticJetCoefficientPairing
open VOA.DeligneHigherRankConditionalCapstone
open VOA.DeligneAudit.CarrierEmbedding

noncomputable section

/-- The coefficient matrix with the listed entries `(x, y, c)` (all others zero). -/
def entryMatrix {σ : Type*} [DecidableEq σ] (L : List (σ × σ × ℂ)) : σ × σ → ℂ :=
  fun xy => (L.map fun t => if (t.1, t.2.1) = xy then t.2.2 else 0).sum

theorem quadraticRelation_entryMatrix {σ : Type*} [Fintype σ] [DecidableEq σ]
    (L : List (σ × σ × ℂ)) :
    quadraticRelation (entryMatrix L) = (L.map fun t => t.2.2 • (X t.1 * X t.2.1)).sum := by
  induction L with
  | nil => simp [quadraticRelation, entryMatrix]
  | cons t L ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    unfold quadraticRelation entryMatrix
    simp only [List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib, ite_smul,
      zero_smul]
    congr 1
    rw [Finset.sum_ite_eq]
    simp

/-- The nonzero entries of the eight relations, read off `A2.relationPoly`. -/
def relationEntries : Fin 8 → List (Fin 8 × Fin 8 × ℂ) :=
  ![[(0, 6, 1), (0, 7, 2), (2, 4, 3)],
    [(1, 6, -2), (1, 7, -1), (2, 3, 3)],
    [(2, 6, 1), (2, 7, -1), (0, 1, 3)],
    [(3, 6, 1), (3, 7, 2), (1, 5, 3)],
    [(4, 6, -2), (4, 7, -1), (0, 5, 3)],
    [(5, 6, 1), (5, 7, -1), (3, 4, 3)],
    [(6, 6, 1), (6, 7, 2), (2, 5, 3), (1, 4, -3)],
    [(7, 7, -1), (6, 7, -2), (2, 5, -3), (0, 3, 3)]]

/-- The explicit coefficient matrices of the A₂ relations. -/
def relationMatrix (a : Fin 8) : Fin 8 × Fin 8 → ℂ := entryMatrix (relationEntries a)

theorem relationPoly_eq_quadraticRelation (a : Fin 8) :
    relationPoly a = quadraticRelation (relationMatrix a) := by
  rw [relationMatrix, quadraticRelation_entryMatrix]
  fin_cases a <;>
    simp [relationPoly, relationEntries, q, MvPolynomial.smul_eq_C_mul, map_neg, map_ofNat] <;> ring

/-- **`I₂ⁿˢ` is the quadratic ideal of the explicit matrices.** -/
theorem I2ns_eq_quadraticIdeal : I2ns = quadraticIdeal relationMatrix := by
  rw [I2ns, quadraticIdeal]
  congr 2
  funext a
  exact relationPoly_eq_quadraticRelation a

/-- The literal A₂ current carrier in Li/conformal bidegree `(p, N)`. -/
abbrev Carrier (p N : ℕ) : Type := CarrierEmbedding.Carrier relationMatrix p N

/-- On the diagonal range the A₂ carrier is linearly equivalent to the restricted dual of the
presented jet bidegree of `Sym sl₃ / I₂ⁿˢ`. -/
def dualEquivCarrier {p N : ℕ} (h : p ≤ N) :
    Module.Dual ℂ
        (FiniteJet.PresentedJetLiBidegreeImage (R := ℂ) (fun _ : Fin 8 => 1) p p N I2ns) ≃ₗ[ℂ]
      Carrier p N := by
  rw [I2ns_eq_quadraticIdeal]
  exact CarrierEmbedding.dualEquivCarrier relationMatrix h

/-- **The A₂ geometric carrier embedding.**  For every VOA `W` and every current presentation
whose ideal is `I₂ⁿˢ`, the literal carrier receives the capstone's injective restricted-dual
maps. -/
def geometricCarrierEmbedding {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} (P : CurrentC2Presentation .A2 W) (hP : P.ideal = I2ns) :
    GeometricCarrierEmbedding .A2 W P Carrier :=
  geometricCarrierEmbedding_of_quadraticIdeal P relationMatrix (hP.trans I2ns_eq_quadraticIdeal)

/-- **A₂ endgame.**  For any presentation by `I₂ⁿˢ`, classical freeness and exactness of the
presentation follow from current-jet surjectivity and the named carrier upper bound
`Hilb Jet(Sym sl₃/I₂ⁿˢ) ≤ ch V`. -/
theorem classicallyFree_of_upperBound {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} (P : CurrentC2Presentation .A2 W) (hP : P.ideal = I2ns)
    (hsurj : CurrentJetSurjectivity .A2 W P)
    (hbound : QuadraticCarrierUpperBound relationMatrix W) :
    CaseClassicallyFree .A2 W P ∧
      RingHom.ker
          (MvPolynomial.aeval fun i =>
            liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom =
        P.ideal :=
  caseClassicallyFree_of_quadraticCarrierUpperBound P relationMatrix
    (hP.trans I2ns_eq_quadraticIdeal) hsurj hbound

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms quadraticRelation_entryMatrix
#print axioms relationPoly_eq_quadraticRelation
#print axioms I2ns_eq_quadraticIdeal
#print axioms dualEquivCarrier
#print axioms geometricCarrierEmbedding
#print axioms classicallyFree_of_upperBound
end AxiomAudit
