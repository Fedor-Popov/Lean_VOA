import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeGrading
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.BigOperators.Fin

/-! The projected-chain remainder is supported in strictly lower color weight. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

/-- The actual bit-mask indices of the nested chain. -/
def chainIndex : Fin 4 → Fin 8 := ![0,1,3,7]

theorem chainIndex_injective : Function.Injective chainIndex := by decide +kernel

theorem chainIndex_range (i : Fin 8) :
    i ∈ Set.range chainIndex ↔ i=0 ∨ i=1 ∨ i=3 ∨ i=7 := by
  fin_cases i <;> decide +kernel

theorem chainIndex_not_range (i : Fin 8) :
    i ∉ Set.range chainIndex ↔ i=2 ∨ i=4 ∨ i=5 ∨ i=6 := by
  fin_cases i <;> decide +kernel

variable (K : Type*) [CommRing K]

theorem chainProj_index_X (j : Fin 4) :
    chainProj K (MvPolynomial.X (chainIndex j)) = MvPolynomial.X j := by
  fin_cases j <;> simp [chainProj,chainIndex]

theorem chainProj_eq_killCompl :
    chainProj K = MvPolynomial.killCompl (R := K) chainIndex_injective := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i ∈ Set.range chainIndex
  · obtain ⟨j,rfl⟩ := hi
    rw [chainProj_index_X]
    simpa only [MvPolynomial.rename_X] using
      (MvPolynomial.killCompl_rename_app (R := K) chainIndex_injective
        (MvPolynomial.X j)).symm
  · have hz : chainProj K (MvPolynomial.X i) = 0 := by
      rcases (chainIndex_not_range i).mp hi with rfl | rfl | rfl | rfl <;>
        simp [chainProj]
    rw [hz]
    simp only [MvPolynomial.killCompl,MvPolynomial.aeval_X,dif_neg hi]

def chainEmbed : P4 K →ₐ[K] P8 K := MvPolynomial.rename chainIndex

def remainder (p : P8 K) : P8 K := p - chainEmbed K (chainProj K p)

/-- No nested-chain coefficient survives in this whole-polynomial remainder. -/
theorem remainder_coeff_zero (p : P8 K) (d : Fin 8 →₀ ℕ)
    (hs : (d.support : Set (Fin 8)) ⊆ Set.range chainIndex) :
    MvPolynomial.coeff d (remainder K p) = 0 := by
  let e := d.comapDomain chainIndex chainIndex_injective.injOn
  have he : e.mapDomain chainIndex = d := d.mapDomain_comapDomain chainIndex chainIndex_injective hs
  rw [remainder,chainEmbed,chainProj_eq_killCompl,← he,MvPolynomial.coeff_sub,
    MvPolynomial.coeff_rename_mapDomain chainIndex chainIndex_injective,
    MvPolynomial.coeff_killCompl]
  exact sub_self _

/-- Subtraction of the chain part cannot introduce any new monomial. -/
theorem remainder_coeff_source (p : P8 K) (d : Fin 8 →₀ ℕ)
    (hd : MvPolynomial.coeff d (remainder K p) ≠ 0) : MvPolynomial.coeff d p ≠ 0 := by
  intro hp
  have hs : (chainEmbed K (chainProj K p)).support ⊆ p.support := by
    rw [chainEmbed,chainProj_eq_killCompl]
    exact MvPolynomial.support_rename_killCompl_subset chainIndex_injective
  have hz : MvPolynomial.coeff d (chainEmbed K (chainProj K p)) = 0 := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp (hs (MvPolynomial.mem_support_iff.mpr hn))) hp
  apply hd
  rw [remainder,MvPolynomial.coeff_sub,hp,hz,sub_self]

/-- Conversion from the four weighted degrees to ordinary exponent counts. -/
theorem weights_counts (d : Fin 8 →₀ ℕ) :
    Finsupp.weight (cubeWeight 0) d = (length d : ℤ) ∧
    Finsupp.weight (cubeWeight 1) d = (first d : ℤ) ∧
    Finsupp.weight (cubeWeight 2) d = (second d : ℤ) ∧
    Finsupp.weight (cubeWeight 3) d = (third d : ℤ) := by
  classical
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_eight,
    cubeWeight,length,first,second,third,add_assoc]

theorem orbit_support_data (r a b c : ℕ) (d : Fin 8 →₀ ℕ)
    (hd : MvPolynomial.coeff d (orbit K r a b c) ≠ 0) :
    length d = r ∧ first d = a ∧ second d = b ∧ third d = c := by
  obtain ⟨h0,h1,h2,h3⟩ := weights_counts d
  have e0 := orbit_weighted K r a b c (0:Fin 4) hd
  have e1 := orbit_weighted K r a b c (1:Fin 4) hd
  have e2 := orbit_weighted K r a b c (2:Fin 4) hd
  have e3 := orbit_weighted K r a b c (3:Fin 4) hd
  rw [h0] at e0
  rw [h1] at e1
  rw [h2] at e2
  rw [h3] at e3
  change (length d : ℤ) = (r:ℤ) at e0
  change (first d : ℤ) = (a:ℤ) at e1
  change (second d : ℤ) = (b:ℤ) at e2
  change (third d : ℤ) = (c:ℤ) at e3
  exact ⟨Int.ofNat.inj e0,Int.ofNat.inj e1,Int.ofNat.inj e2,Int.ofNat.inj e3⟩

/-- The exact remainder of the whole orbit has strictly lower color weight. -/
theorem orbit_remainder_energy (r a b c : ℕ) (d : Fin 8 →₀ ℕ)
    (hd : MvPolynomial.coeff d (remainder K (orbit K r a b c)) ≠ 0) :
    energy d < a + 3 * b + 5 * c := by
  have hp := remainder_coeff_source K (orbit K r a b c) d hd
  obtain ⟨hr,ha,hb,hc⟩ := orbit_support_data K r a b c d hp
  have hdef := energy_deficit d
  rw [ha,hb,hc] at hdef
  have hn : ¬ (d.support : Set (Fin 8)) ⊆ Set.range chainIndex :=
    fun hs => hd (remainder_coeff_zero K (orbit K r a b c) d hs)
  obtain ⟨i,hi,hn⟩ := Set.not_subset.mp hn
  have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  rcases (chainIndex_not_range i).mp hn with rfl | rfl | rfl | rfl <;> omega

end
#print axioms chain_projection_ne_zero
#print axioms orbit_remainder_energy
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
