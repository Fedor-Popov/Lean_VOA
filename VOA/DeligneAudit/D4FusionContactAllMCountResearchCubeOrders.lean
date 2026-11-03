import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeLeading

/-! The six coordinate orders preserve cube lowering and the explicit strict
color weight. This acts on whole polynomials, before current coefficients. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

def orderColor : Fin 6 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7],
    ![0,1,4,5,2,3,6,7],
    ![0,2,1,3,4,6,5,7],
    ![0,2,4,6,1,3,5,7],
    ![0,4,1,5,2,6,3,7],
    ![0,4,2,6,1,5,3,7]]
def orderDirection : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2],
    ![0,2,1],
    ![1,0,2],
    ![1,2,0],
    ![2,0,1],
    ![2,1,0]]

theorem orderColor_injective : ∀ o : Fin 6, Function.Injective (orderColor o) := by
  decide +kernel

theorem orderColor_zero : ∀ o : Fin 6, orderColor o 0 = 0 := by decide +kernel

def cubeEnergy : Fin 8 → ℕ := ![0,1,1,4,1,4,4,9]

theorem orderColor_energy : ∀ (o : Fin 6) (i : Fin 8),
    cubeEnergy (orderColor o i) = cubeEnergy i := by decide +kernel

theorem cubeEnergy_weight (d : Fin 8 →₀ ℕ) :
    Finsupp.weight cubeEnergy d = energy d := by
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_eight,
    cubeEnergy,energy,mul_comm,add_assoc]

theorem orderColor_weight (o : Fin 6) (d : Fin 8 →₀ ℕ) :
    energy (d.mapDomain (orderColor o)) = energy d := by
  rw [← cubeEnergy_weight,← cubeEnergy_weight,Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun i (n : ℕ) => n • cubeEnergy i)
    (fun _ => zero_nsmul _) (fun _ _ _ => add_nsmul _ _ _)]
  simp only [orderColor_energy,Finsupp.weight_apply]

variable (K : Type*) [CommRing K]

def orderRename (o : Fin 6) : P8 K →ₐ[K] P8 K := MvPolynomial.rename (orderColor o)
def orderLower : Fin 3 → Derivation K (P8 K) (P8 K) := ![d1 K,d2 K,d3 K]

def orderNext : Fin 3 → Fin 8 → Option (Fin 8) :=
  ![![some 1,none,some 3,none,some 5,none,some 7,none],
    ![some 2,some 3,none,none,some 6,some 7,none,none],
    ![some 4,some 5,some 6,some 7,none,none,none,none]]

theorem orderColor_next : ∀ (o : Fin 6) (d : Fin 3) (i : Fin 8),
    Option.map (orderColor o) (orderNext d i) =
      orderNext (orderDirection o d) (orderColor o i) := by decide +kernel

theorem orderLower_X (d : Fin 3) (i : Fin 8) :
    orderLower K d (MvPolynomial.X i) =
      match orderNext d i with
      | none => 0
      | some j => MvPolynomial.X j := by
  fin_cases d <;> fin_cases i <;>
    change MvPolynomial.mkDerivation K _ (MvPolynomial.X _) = _ <;>
    rw [MvPolynomial.mkDerivation_X] <;> rfl

theorem orderRename_lower_X (o : Fin 6) (d : Fin 3) (i : Fin 8) :
    orderRename K o (orderLower K d (MvPolynomial.X i)) =
      orderLower K (orderDirection o d) (orderRename K o (MvPolynomial.X i)) := by
  rw [orderLower_X]
  change orderRename K o _ = orderLower K (orderDirection o d)
    (MvPolynomial.rename (orderColor o) (MvPolynomial.X i))
  rw [MvPolynomial.rename_X,orderLower_X,← orderColor_next]
  cases ht : orderNext d i <;> simp [orderRename]

theorem orderRename_lower (o : Fin 6) (d : Fin 3) (p : P8 K) :
    orderRename K o (orderLower K d p) =
      orderLower K (orderDirection o d) (orderRename K o p) :=
  map_derivation (orderRename K o) (orderLower K d)
    (orderLower K (orderDirection o d)) (orderRename_lower_X K o d) p

theorem orderRename_orbit (o : Fin 6) (r a b c : ℕ) :
    orderRename K o (orbit K r a b c) =
      ((orderLower K (orderDirection o 2) : _ → _)^[c])
        (((orderLower K (orderDirection o 1) : _ → _)^[b])
          (((orderLower K (orderDirection o 0) : _ → _)^[a]) (MvPolynomial.X 0^r))) := by
  rw [orbit,map_iterate_deriv (orderRename K o) (d3 K) _
    (fun p => orderRename_lower K o 2 p)]
  rw [map_iterate_deriv (orderRename K o) (d2 K) _
    (fun p => orderRename_lower K o 1 p)]
  rw [map_iterate_deriv (orderRename K o) (d1 K) _
    (fun p => orderRename_lower K o 0 p)]
  simp only [orderRename,map_pow,MvPolynomial.rename_X,orderColor_zero]

theorem orderRename_low (o : Fin 6) (L : ℕ) (p : P8 K) (hp : p ∈ colorLow K L) :
    orderRename K o p ∈ colorLow K L := by
  classical
  change (↑p.support : Set (Fin 8 →₀ ℕ)) ⊆ {d | energy d < L} at hp
  change (↑(MvPolynomial.rename (orderColor o) p).support : Set (Fin 8 →₀ ℕ)) ⊆
    {d | energy d < L}
  rw [MvPolynomial.support_rename_of_injective (orderColor_injective o)]
  intro e he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
  change energy (d.mapDomain (orderColor o)) < L
  rw [orderColor_weight]
  exact hp hd

/-- Every coordinate order has a genuine strict color-filtration reduction. -/
theorem order_orbit_sub_chainTerm_mem (o : Fin 6) (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    orderRename K o (orbit K r a b c) - orderRename K o (chainTerm K r a b c) ∈
      colorLow K (a+3*b+5*c) := by
  simpa only [map_sub] using orderRename_low K o (a+3*b+5*c)
    (orbit K r a b c-chainTerm K r a b c) (orbit_sub_chainTerm_mem K r a b c ha hb hc)

end
#print axioms orderRename_lower
#print axioms order_orbit_sub_chainTerm_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
