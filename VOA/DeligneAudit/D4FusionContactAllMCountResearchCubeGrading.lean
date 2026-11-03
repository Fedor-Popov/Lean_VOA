import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeOrbit
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeEnergy
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Every monomial of the whole cube orbit has the prescribed length and
three marginals. The proof uses weighted homogeneous polynomials over Z. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable (K : Type*) [CommRing K]

/-- The coordinate formula for any derivation of the eight-variable ring. -/
theorem deriv_eq_sum (D : Derivation K (P8 K) (P8 K)) :
    D = ∑ i : Fin 8, D (MvPolynomial.X i) • MvPolynomial.pderiv i := by
  apply MvPolynomial.derivation_ext
  intro j
  change D (MvPolynomial.X j) = (Derivation.coeFnAddMonoidHom
    (∑ i : Fin 8, D (MvPolynomial.X i) • MvPolynomial.pderiv i)) (MvPolynomial.X j)
  rw [map_sum,Finset.sum_apply]
  simp [Derivation.smul_apply,smul_eq_mul,MvPolynomial.pderiv_X,Pi.single_apply]

theorem deriv_apply_eq_sum (D : Derivation K (P8 K) (P8 K)) (p : P8 K) :
    D p = ∑ i : Fin 8, D (MvPolynomial.X i) * MvPolynomial.pderiv i p := by
  conv_lhs => rw [deriv_eq_sum K D]
  change (Derivation.coeFnAddMonoidHom
    (∑ i : Fin 8, D (MvPolynomial.X i) • MvPolynomial.pderiv i)) p = _
  rw [map_sum,Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply,Derivation.smul_apply,smul_eq_mul]

/-- A variable-wise weight shift gives the same shift on every whole polynomial. -/
theorem deriv_weight_shift (D : Derivation K (P8 K) (P8 K))
    (w : Fin 8 → ℤ) (δ : ℤ)
    (hX : ∀ i, (D (MvPolynomial.X i)).IsWeightedHomogeneous w (w i + δ))
    {p : P8 K} {n : ℤ} (hp : p.IsWeightedHomogeneous w n) :
    (D p).IsWeightedHomogeneous w (n + δ) := by
  rw [deriv_apply_eq_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i _
  have hd : (MvPolynomial.pderiv i p).IsWeightedHomogeneous w (n - w i) :=
    hp.pderiv (by omega)
  convert (hX i).mul hd using 1; omega

theorem iterate_weight_shift (D : Derivation K (P8 K) (P8 K))
    (w : Fin 8 → ℤ) (δ : ℤ)
    (hX : ∀ i, (D (MvPolynomial.X i)).IsWeightedHomogeneous w (w i + δ))
    {p : P8 K} {n : ℤ} (hp : p.IsWeightedHomogeneous w n) (k : ℕ) :
    (((D : P8 K → P8 K)^[k]) p).IsWeightedHomogeneous w (n + (k : ℤ) * δ) := by
  induction k with
  | zero => simpa only [Function.iterate_zero_apply,Nat.cast_zero,zero_mul,add_zero] using hp
  | succ k ih =>
      have hh := deriv_weight_shift K D w δ hX ih
      rw [Function.iterate_succ_apply']
      convert hh using 1; push_cast; ring

def cubeWeight : Fin 4 → Fin 8 → ℤ :=
  ![![1,1,1,1,1,1,1,1],![0,1,0,1,0,1,0,1],
    ![0,0,1,1,0,0,1,1],![0,0,0,0,1,1,1,1]]

def shift1 : Fin 4 → ℤ := ![0,1,0,0]
def shift2 : Fin 4 → ℤ := ![0,0,1,0]
def shift3 : Fin 4 → ℤ := ![0,0,0,1]

def grade (r a b c : ℕ) : Fin 4 → ℤ := ![(r:ℤ),(a:ℤ),(b:ℤ),(c:ℤ)]

theorem d1_weight_image (j : Fin 4) (i : Fin 8) :
    (d1 K (MvPolynomial.X i)).IsWeightedHomogeneous (cubeWeight j)
      (cubeWeight j i+shift1 j) := by
  fin_cases j <;> fin_cases i <;> simp only [d1,MvPolynomial.mkDerivation_X]
  all_goals first
    | exact MvPolynomial.isWeightedHomogeneous_zero K _ _
    | exact MvPolynomial.isWeightedHomogeneous_X K _ _

theorem d2_weight_image (j : Fin 4) (i : Fin 8) :
    (d2 K (MvPolynomial.X i)).IsWeightedHomogeneous (cubeWeight j)
      (cubeWeight j i+shift2 j) := by
  fin_cases j <;> fin_cases i <;> simp only [d2,MvPolynomial.mkDerivation_X]
  all_goals first
    | exact MvPolynomial.isWeightedHomogeneous_zero K _ _
    | exact MvPolynomial.isWeightedHomogeneous_X K _ _

theorem d3_weight_image (j : Fin 4) (i : Fin 8) :
    (d3 K (MvPolynomial.X i)).IsWeightedHomogeneous (cubeWeight j)
      (cubeWeight j i+shift3 j) := by
  fin_cases j <;> fin_cases i <;> simp only [d3,MvPolynomial.mkDerivation_X]
  all_goals first
    | exact MvPolynomial.isWeightedHomogeneous_zero K _ _
    | exact MvPolynomial.isWeightedHomogeneous_X K _ _

/-- This support statement holds at every order, including zero whole orbits. -/
theorem orbit_weighted (r a b c : ℕ) (j : Fin 4) :
    (orbit K r a b c).IsWeightedHomogeneous (cubeWeight j) (grade r a b c j) := by
  have hx : ((MvPolynomial.X 0 : P8 K)^r).IsWeightedHomogeneous
      (cubeWeight j) ((r:ℤ)*cubeWeight j 0) := by
    have hh := (MvPolynomial.isWeightedHomogeneous_X K (cubeWeight j) (0 : Fin 8)).pow r
    rw [nsmul_eq_mul] at hh
    exact hh
  have h1 := iterate_weight_shift K (d1 K) (cubeWeight j) (shift1 j)
    (d1_weight_image K j) hx a
  have h2 := iterate_weight_shift K (d2 K) (cubeWeight j) (shift2 j)
    (d2_weight_image K j) h1 b
  have h3 := iterate_weight_shift K (d3 K) (cubeWeight j) (shift3 j)
    (d3_weight_image K j) h2 c
  have he : ((r:ℤ)*cubeWeight j 0+(a:ℤ)*shift1 j)+(b:ℤ)*shift2 j+
      (c:ℤ)*shift3 j = grade r a b c j := by
    fin_cases j
    · change (r:ℤ)*1+(a:ℤ)*0+(b:ℤ)*0+(c:ℤ)*0=(r:ℤ)
      ring
    · change (r:ℤ)*0+(a:ℤ)*1+(b:ℤ)*0+(c:ℤ)*0=(a:ℤ)
      ring
    · change (r:ℤ)*0+(a:ℤ)*0+(b:ℤ)*1+(c:ℤ)*0=(b:ℤ)
      ring
    · change (r:ℤ)*0+(a:ℤ)*0+(b:ℤ)*0+(c:ℤ)*1=(c:ℤ)
      ring
  rw [he] at h3
  exact h3

end
#print axioms chain_projection_formula
#print axioms orbit_weighted
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
