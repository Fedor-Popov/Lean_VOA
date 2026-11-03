import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeMaps

/-! The nested-chain part of every whole normalized cube orbit is exactly
one monomial, with a nonzero falling-factorial coefficient. No ideal or
quotient presentation, dimension or normal-completeness premise occurs. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable (K : Type*) [CommRing K]

def orbit (r a b c : ℕ) : P8 K :=
  ((d3 K : P8 K → P8 K)^[c])
    (((d2 K : P8 K → P8 K)^[b])
      (((d1 K : P8 K → P8 K)^[a]) ((MvPolynomial.X 0 : P8 K)^r)))

def towerCoeff (r a b c : ℕ) : ℕ :=
  r.descFactorial a * a.descFactorial b * b.descFactorial c

theorem embed_first_two (r a b : ℕ) :
    smallEmbed K (((d2small K : P4 K → P4 K)^[b])
      (((d1small K : P4 K → P4 K)^[a]) ((MvPolynomial.X 0 : P4 K)^r))) =
    ((d2 K : P8 K → P8 K)^[b])
      (((d1 K : P8 K → P8 K)^[a]) ((MvPolynomial.X 0 : P8 K)^r)) := by
  rw [map_iterate_deriv (smallEmbed K) (d2small K) (d2 K) (embed_d2 K),
    map_iterate_deriv (smallEmbed K) (d1small K) (d1 K) (embed_d1 K)]
  simp only [smallEmbed,map_pow,MvPolynomial.rename_X,smallIndex]
  rfl

/-- The intermediate projection is justified on the invariant small subring. -/
theorem project_orbit_reduction (r a b c : ℕ) :
    chainProj K (orbit K r a b c) =
      ((e3 K : P4 K → P4 K)^[c])
        (((e2 K : P4 K → P4 K)^[b])
          (chainProjSmall K (((d1small K : P4 K → P4 K)^[a])
            ((MvPolynomial.X 0 : P4 K)^r)))) := by
  rw [orbit,map_iterate_deriv (chainProj K) (d3 K) (e3 K) (project_d3 K)]
  rw [← embed_first_two K r a b,project_embed_apply]
  rw [map_iterate_deriv (chainProjSmall K) (d2small K) (e2 K) (project_d2 K)]

theorem first_projection (r a : ℕ) (ha : a ≤ r) :
    chainProjSmall K (((d1small K : P4 K → P4 K)^[a])
      ((MvPolynomial.X 0 : P4 K)^r)) =
      (r.descFactorial a : P4 K) * MvPolynomial.X 0^(r-a) * MvPolynomial.X 1^a := by
  rw [iterate_deriv_power_of_le (d1small K) (MvPolynomial.X 0) (MvPolynomial.X 1)
    (by simp [d1small]) (by simp [d1small]) r a ha]
  simp [chainProjSmall]

/-- The exact uniform coefficient of the unique nested-chain monomial. -/
theorem chain_projection_formula (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    chainProj K (orbit K r a b c) =
      (towerCoeff r a b c : P4 K) *
        MvPolynomial.X 0^(r-a) * MvPolynomial.X 1^(a-b) *
        MvPolynomial.X 2^(b-c) * MvPolynomial.X 3^c := by
  rw [project_orbit_reduction,first_projection K r a ha]
  let c0 : P4 K := (r.descFactorial a : P4 K) * MvPolynomial.X 0^(r-a)
  have hz0 : e2 K c0 = 0 := by
    simp [c0,Derivation.leibniz,Derivation.leibniz_pow,e2]
  change ((e3 K : P4 K → P4 K)^[c])
    (((e2 K : P4 K → P4 K)^[b]) (c0 * MvPolynomial.X 1^a)) = _
  rw [iterate_const_mul (e2 K) c0 hz0,
    iterate_deriv_power_of_le (e2 K) (MvPolynomial.X 1) (MvPolynomial.X 2)
      (by simp [e2]) (by simp [e2]) a b hb]
  let c1 : P4 K := c0 * (a.descFactorial b : P4 K) * MvPolynomial.X 1^(a-b)
  have hgroup : c0 * ((a.descFactorial b : P4 K) * MvPolynomial.X 1^(a-b) *
      MvPolynomial.X 2^b) = c1 * MvPolynomial.X 2^b := by dsimp [c1]; ring
  rw [hgroup]
  have hz1 : e3 K c1 = 0 := by
    simp [c1,c0,Derivation.leibniz,Derivation.leibniz_pow,e3]
  rw [iterate_const_mul (e3 K) c1 hz1,
    iterate_deriv_power_of_le (e3 K) (MvPolynomial.X 2) (MvPolynomial.X 3)
      (by simp [e3]) (by simp [e3]) b c hc]
  simp only [towerCoeff,Nat.cast_mul]
  dsimp only [c1,c0]
  ring

theorem towerCoeff_pos (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) : 0 < towerCoeff r a b c :=
  Nat.mul_pos (Nat.mul_pos (Nat.descFactorial_pos.mpr ha)
    (Nat.descFactorial_pos.mpr hb)) (Nat.descFactorial_pos.mpr hc)

/-- In characteristic zero the projected whole orbit is nonzero at every order. -/
theorem chain_projection_ne_zero [CharZero K] (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    chainProj K (orbit K r a b c) ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.aeval (fun _ : Fin 4 => (1:K)))
    (chain_projection_formula K r a b c ha hb hc)
  rw [hz,map_zero] at he
  simp only [map_mul,map_natCast,map_pow,MvPolynomial.aeval_X,one_pow,mul_one] at he
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (towerCoeff_pos r a b c ha hb hc))) he.symm

/-- This is why the second lowering must be handled on the smaller subring. -/
theorem full_second_projection_obstruction :
    chainProj K (d2 K (MvPolynomial.X 5)) = MvPolynomial.X 3 ∧
      e2 K (chainProj K (MvPolynomial.X 5)) = 0 := by
  simp [chainProj,d2,e2]

end
#print axioms chain_projection_formula
#print axioms chain_projection_ne_zero
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
