import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCommute

/-! Exact twelve-term whole quartic polar. This retains every color tail;
no reduced head, rank or normal-form completeness is asserted. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable (K : Type*) [CommRing K]

def quarticPolarFormula : P8 K :=
  48 * MvPolynomial.X 0^2 * MvPolynomial.X 7^2 +
  48 * MvPolynomial.X 1^2 * MvPolynomial.X 6^2 +
  48 * MvPolynomial.X 2^2 * MvPolynomial.X 5^2 +
  48 * MvPolynomial.X 3^2 * MvPolynomial.X 4^2 +
  192 * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 6 * MvPolynomial.X 7 +
  192 * MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 5 * MvPolynomial.X 7 +
  192 * MvPolynomial.X 0 * MvPolynomial.X 3 * MvPolynomial.X 4 * MvPolynomial.X 7 +
  192 * MvPolynomial.X 0 * MvPolynomial.X 3 * MvPolynomial.X 5 * MvPolynomial.X 6 +
  192 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 4 * MvPolynomial.X 7 +
  192 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 5 * MvPolynomial.X 6 +
  192 * MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4 * MvPolynomial.X 6 +
  192 * MvPolynomial.X 2 * MvPolynomial.X 3 * MvPolynomial.X 4 * MvPolynomial.X 5

/-- Fixed small algebra identity over every commutative ring. -/
theorem quartic_polar_formula : orbit K 4 2 2 2 = quarticPolarFormula K := by
  have h10 : d1 K (MvPolynomial.X 0) = MvPolynomial.X 1 := MvPolynomial.mkDerivation_X K _ _
  have h11 : d1 K (MvPolynomial.X 1) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h20 : d2 K (MvPolynomial.X 0) = MvPolynomial.X 2 := MvPolynomial.mkDerivation_X K _ _
  have h21 : d2 K (MvPolynomial.X 1) = MvPolynomial.X 3 := MvPolynomial.mkDerivation_X K _ _
  have h22 : d2 K (MvPolynomial.X 2) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h23 : d2 K (MvPolynomial.X 3) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h30 : d3 K (MvPolynomial.X 0) = MvPolynomial.X 4 := MvPolynomial.mkDerivation_X K _ _
  have h31 : d3 K (MvPolynomial.X 1) = MvPolynomial.X 5 := MvPolynomial.mkDerivation_X K _ _
  have h32 : d3 K (MvPolynomial.X 2) = MvPolynomial.X 6 := MvPolynomial.mkDerivation_X K _ _
  have h33 : d3 K (MvPolynomial.X 3) = MvPolynomial.X 7 := MvPolynomial.mkDerivation_X K _ _
  have h34 : d3 K (MvPolynomial.X 4) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h35 : d3 K (MvPolynomial.X 5) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h36 : d3 K (MvPolynomial.X 6) = 0 := MvPolynomial.mkDerivation_X K _ _
  have h37 : d3 K (MvPolynomial.X 7) = 0 := MvPolynomial.mkDerivation_X K _ _
  have hc212 : d2 K (12 : P8 K) = 0 := Derivation.map_natCast _ 12
  have hc324 : d3 K (24 : P8 K) = 0 := Derivation.map_natCast _ 24
  have hc396 : d3 K (96 : P8 K) = 0 := Derivation.map_natCast _ 96
  have h1 : d1 K (d1 K (MvPolynomial.X 0^4)) =
      (12 : P8 K) * MvPolynomial.X 0^2 * MvPolynomial.X 1^2 := by
    simp only [Derivation.leibniz_pow,Derivation.leibniz,
      Derivation.map_natCast,smul_eq_mul,nsmul_eq_mul,h10,h11]
    ring
  have h2 : d2 K (d2 K ((12 : P8 K) * MvPolynomial.X 0^2 * MvPolynomial.X 1^2)) =
      24 * MvPolynomial.X 1^2 * MvPolynomial.X 2^2 +
      96 * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 +
      24 * MvPolynomial.X 0^2 * MvPolynomial.X 3^2 := by
    simp only [Derivation.leibniz_pow,Derivation.leibniz,map_add,map_zero,
      Derivation.map_natCast,smul_eq_mul,nsmul_eq_mul,h20,h21,h22,h23,hc212]
    ring
  simp only [orbit,Function.iterate_succ_apply',Function.iterate_zero_apply]
  rw [h1,h2]
  simp only [map_add,Derivation.leibniz,Derivation.map_natCast,Derivation.leibniz_pow,
    smul_eq_mul,nsmul_eq_mul,h30,h31,h32,h33,h34,h35,h36,h37,hc324,hc396,
    mul_zero,zero_add,add_zero,quarticPolarFormula]
  ring

end
#print axioms quartic_polar_formula
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
