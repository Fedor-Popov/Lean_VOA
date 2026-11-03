import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCommute

/-! A static cube lowering increments exactly its own polar index.
Only whole-polynomial commutation is used. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable (K : Type*) [CommRing K]

def polarZeroStep (d : Fin 3) (r a b c : ℕ) : P8 K :=
  if d = 0 then orbit K r (a + 1) b c
  else if d = 1 then orbit K r a (b + 1) c
  else orbit K r a b (c + 1)

private theorem orderLower_orbit_first (r a b c : ℕ) :
    orderLower K 0 (orbit K r a b c) = orbit K r (a + 1) b c := by
  change orderLower K 0
      (((orderLower K 2 : P8 K → P8 K)^[c])
        (((orderLower K 1 : P8 K → P8 K)^[b])
          (((orderLower K 0 : P8 K → P8 K)^[a]) (MvPolynomial.X 0 ^ r)))) =
    ((orderLower K 2 : P8 K → P8 K)^[c])
      (((orderLower K 1 : P8 K → P8 K)^[b])
        (((orderLower K 0 : P8 K → P8 K)^[a + 1]) (MvPolynomial.X 0 ^ r)))
  rw [(orderLower_commute K 0 2).iterate_right c,
    (orderLower_commute K 0 1).iterate_right b,Function.iterate_succ_apply']

private theorem orderLower_orbit_second (r a b c : ℕ) :
    orderLower K 1 (orbit K r a b c) = orbit K r a (b + 1) c := by
  change orderLower K 1
      (((orderLower K 2 : P8 K → P8 K)^[c])
        (((orderLower K 1 : P8 K → P8 K)^[b])
          (((orderLower K 0 : P8 K → P8 K)^[a]) (MvPolynomial.X 0 ^ r)))) =
    ((orderLower K 2 : P8 K → P8 K)^[c])
      (((orderLower K 1 : P8 K → P8 K)^[b + 1])
        (((orderLower K 0 : P8 K → P8 K)^[a]) (MvPolynomial.X 0 ^ r)))
  rw [(orderLower_commute K 1 2).iterate_right c,Function.iterate_succ_apply']

private theorem orderLower_orbit_third (r a b c : ℕ) :
    orderLower K 2 (orbit K r a b c) = orbit K r a b (c + 1) := by
  change orderLower K 2
      (((orderLower K 2 : P8 K → P8 K)^[c])
        (((orderLower K 1 : P8 K → P8 K)^[b])
          (((orderLower K 0 : P8 K → P8 K)^[a]) (MvPolynomial.X 0 ^ r)))) =
    ((orderLower K 2 : P8 K → P8 K)^[c + 1])
      (((orderLower K 1 : P8 K → P8 K)^[b])
        (((orderLower K 0 : P8 K → P8 K)^[a]) (MvPolynomial.X 0 ^ r)))
  rw [Function.iterate_succ_apply']

theorem orderLower_orbit_step (d : Fin 3) (r a b c : ℕ) :
    orderLower K d (orbit K r a b c) = polarZeroStep K d r a b c := by
  fin_cases d
  · exact orderLower_orbit_first K r a b c
  · exact orderLower_orbit_second K r a b c
  · exact orderLower_orbit_third K r a b c

end
#print axioms orderLower_orbit_step
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
