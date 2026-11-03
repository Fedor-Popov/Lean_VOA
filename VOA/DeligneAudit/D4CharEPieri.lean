import VOA.DeligneAudit.D4CharPieriCoefficient

/-!
# Lemma E: e-Pieri for all ranks and dominant integer highest weights

The Gaussian boundary calculation used integer powers of a unit. To remove that temporary
restriction, prove the identity at the polynomial variable via the injective map to Laurent
polynomials, and then evaluate the polynomial variable at an arbitrary ring element.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

/-- The Laurent variable is a unit, even when the coefficient ring has zero divisors. -/
def pieriLaurentUnit (R : Type*) [CommRing R] : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

/-- The unit-parameter identity descends to an ordinary polynomial identity. -/
theorem ePieri_polynomial (u : ℕ → (Polynomial R)ˣ) :
    EPieri (Polynomial.X : Polynomial R) u := by
  intro N lam hlam r
  apply Polynomial.toLaurent_injective
  rw [map_mul, pieriElementary_map, gtEval_map, pieriRHS_map]
  have h := ePieri_unit (pieriLaurentUnit R)
    (fun i => Units.map (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) (u i))
    N lam hlam r
  simpa only [Polynomial.toLaurent_X, pieriLaurentUnit] using h

/-- Full e-Pieri: arbitrary coefficient ring, arbitrary q, every rank, weight, and degree. -/
theorem ePieri (q : R) (u : ℕ → Rˣ) : EPieri q u := by
  intro N lam hlam r
  let C : R →+* Polynomial R := Polynomial.C
  let ev : Polynomial R →+* R := Polynomial.evalRingHom q
  have hu : (fun i => Units.map ev.toMonoidHom (Units.map C.toMonoidHom (u i))) = u := by
    funext i
    apply Units.ext
    simp [C, ev]
  have h := ePieri_polynomial (fun i => Units.map C.toMonoidHom (u i)) N lam hlam r
  have he := congrArg ev h
  rw [map_mul, pieriElementary_map, gtEval_map, pieriRHS_map] at he
  change pieriElementary
      (fun i => Units.map ev.toMonoidHom (Units.map C.toMonoidHom (u i))) N r *
      gtEval (ev Polynomial.X)
        (fun i => Units.map ev.toMonoidHom (Units.map C.toMonoidHom (u i))) N lam =
      pieriRHS (ev Polynomial.X)
        (fun i => Units.map ev.toMonoidHom (Units.map C.toMonoidHom (u i))) N lam r at he
  rw [hu] at he
  simpa [ev] using he

/-- The Laurent polynomials `gtP` satisfy Lemma E in every rank. -/
theorem gtP_ePieri (N : ℕ) (lam : Fin N → ℤ) (hlam : Antitone lam) (r : ℕ) :
    pieriElementary gtVariable N r * gtP N lam =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        pieriCoeff (AddMonoidAlgebra.single 0 Polynomial.X : GTLaurent) lam S *
          gtP N (pieriWeight lam S) := by
  exact ePieri (AddMonoidAlgebra.single 0 Polynomial.X : GTLaurent) gtVariable N lam hlam r

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.ePieri_polynomial
#print axioms VOA.DeligneAudit.D4Char.ePieri
#print axioms VOA.DeligneAudit.D4Char.gtP_ePieri
