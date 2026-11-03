/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FourTriangular
import VOA.DeligneAudit.A2CharacterStarChain

/-!
# `FourTriangular` for the A₂ star chain

Discharges residual 3 of `VOA/DeligneAudit/A2CharacterStarChain.lean`,

  `∑_{v ≥ 0} (2v+1) q^v/(1-q^{2v+1}) = (q)_∞⁴ ∏_{r ≥ 1} (1+q^r)⁸`,

from `VOA.QSeries.JTP.lambertS_eq` (Legendre's four-triangular-numbers theorem, proved in
`VOA/Commutative/FourTriangular.lean` from Gauss's product for `φ` and Jacobi's cube identity).
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.QSeries VOA.QSeries.JTP

theorem geomInv_eq_geomInvSeries (m : ℕ) : geomInv m = (geomInvSeries m : PowerSeries ℤ) := rfl

/-- `fermionInf = ∏_{k ≥ 0} (1 + q^{k+1})⁸` as an `infProd`. -/
theorem fermionInf_eq_infProd :
    fermionInf = infProd fun k => (1 + (X : PowerSeries ℤ) ^ (k + 1)) ^ 8 := by
  ext N
  rw [fermionInf, coeff_mk, ← coeff_fermionProd_self, infProd, coeff_mk]
  rfl

/-- **Residual 3 of the star chain, discharged.** -/
theorem fourTriangular : FourTriangular :=
  ⟨by rw [fermionInf_eq_infProd, ← lambertS_eq]; rfl⟩

/-- The star identity rests only on `StarReduction` and `ShiftedMehler`. -/
theorem starIdentity_of_reduction_mehler (hR : StarReduction) (hM : ShiftedMehler) :
    StarIdentity :=
  starIdentity_of_chain hR hM fourTriangular

/-- The character side, likewise. -/
theorem demazureCharacterBound_of_reduction_mehler (hR : StarReduction) (hM : ShiftedMehler)
    (hkw : KacWakimotoLowerBound) : DemazureCharacterBound :=
  demazureCharacterBound_of_chain hR hM fourTriangular hkw

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.QSeries.JTP.thetaPhi_eq
#print axioms VOA.QSeries.JTP.rescale_thetaPhi_eq
#print axioms VOA.QSeries.JTP.eulerOp_oddPlus_wronskian
#print axioms VOA.QSeries.JTP.wronskian_eq
#print axioms VOA.QSeries.JTP.zetaSeries_eq
#print axioms VOA.QSeries.JTP.jacobi_cube_int
#print axioms VOA.QSeries.JTP.lambertS_eq
#print axioms VOA.DeligneAudit.A2.fourTriangular
#print axioms VOA.DeligneAudit.A2.starIdentity_of_reduction_mehler
#print axioms VOA.DeligneAudit.A2.demazureCharacterBound_of_reduction_mehler
end AxiomAudit
