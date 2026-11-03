import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCommute

/-! Exact five-term cubic polar; the lower tail is kept explicitly for the
subsequent completion problem. No projected polynomial is differentiated. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable (K : Type*) [CommRing K]

def cubicPolarFormula : P8 K :=
  12 * MvPolynomial.X 0 * MvPolynomial.X 4 * MvPolynomial.X 7 +
  12 * MvPolynomial.X 0 * MvPolynomial.X 5 * MvPolynomial.X 6 +
  12 * MvPolynomial.X 4 * MvPolynomial.X 6 * MvPolynomial.X 1 +
  12 * MvPolynomial.X 4 * MvPolynomial.X 2 * MvPolynomial.X 5 +
  6 * MvPolynomial.X 4^2 * MvPolynomial.X 3

theorem cubic_polar_formula : orbit K 3 1 1 2 = cubicPolarFormula K := by
  have h10 : d1 K (MvPolynomial.X 0) = MvPolynomial.X 1 := MvPolynomial.mkDerivation_X K _ _
  have h20 : d2 K (MvPolynomial.X 0) = MvPolynomial.X 2 := MvPolynomial.mkDerivation_X K _ _
  have h21 : d2 K (MvPolynomial.X 1) = MvPolynomial.X 3 := MvPolynomial.mkDerivation_X K _ _
  have h30 : d3 K (MvPolynomial.X 0) = MvPolynomial.X 4 := MvPolynomial.mkDerivation_X K _ _
  have h31 : d3 K (MvPolynomial.X 1) = MvPolynomial.X 5 := MvPolynomial.mkDerivation_X K _ _
  have h32 : d3 K (MvPolynomial.X 2) = MvPolynomial.X 6 := MvPolynomial.mkDerivation_X K _ _
  have h33 : d3 K (MvPolynomial.X 3) = MvPolynomial.X 7 := MvPolynomial.mkDerivation_X K _ _
  have h34 : d3 K (MvPolynomial.X 4) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h35 : d3 K (MvPolynomial.X 5) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h36 : d3 K (MvPolynomial.X 6) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h37 : d3 K (MvPolynomial.X 7) = 0 := MvPolynomial.mkDerivation_X K _ _
  have hc23 : d2 K (3 : P8 K) = 0 := Derivation.map_natCast _ 3
  have hc33 : d3 K (3 : P8 K) = 0 := Derivation.map_natCast _ 3
  have hc36 : d3 K (6 : P8 K) = 0 := Derivation.map_natCast _ 6
  have h1 : d1 K (MvPolynomial.X 0^3) =
      (3 : P8 K) * MvPolynomial.X 0^2 * MvPolynomial.X 1 := by
    rw [show (3:ℕ) = 2+1 from rfl,deriv_pow_succ,h10]
    norm_num
  have h2 : d2 K ((3 : P8 K) * MvPolynomial.X 0^2 * MvPolynomial.X 1) =
      6 * MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 1 +
      3 * MvPolynomial.X 0^2 * MvPolynomial.X 3 := by
    simp only [Derivation.leibniz,Derivation.leibniz_pow,
      smul_eq_mul,nsmul_eq_mul,h20,h21,hc23]
    ring
  simp only [orbit,Function.iterate_succ_apply',Function.iterate_zero_apply]
  rw [h1,h2]
  simp only [map_add,Derivation.leibniz,Derivation.map_natCast,Derivation.leibniz_pow,
    smul_eq_mul,nsmul_eq_mul,h30,h31,h32,h33,h34,h35,h36,h37,hc33,hc36,
    mul_zero,zero_add,add_zero,cubicPolarFormula]
  ring

end
#print axioms cubic_polar_formula
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
