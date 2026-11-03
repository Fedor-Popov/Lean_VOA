import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrentFiltered
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeOrders

/-! Six actual D4 whole-current chain reductions. Coordinate permutation is
performed on the whole polynomial source; coefficients and strict color
remainders are transferred only afterwards. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4
noncomputable section

theorem currentMap_order_orbit (m : ℕ) (o : Fin 6) (r a b c : ℕ) :
    currentMap m (orderRename ℂ o (orbit ℂ r a b c)) =
      ((seriesDerivation (g0Deriv m (cubeDirection (orderDirection o 2)) 0) : _ → _)^[c])
        (((seriesDerivation (g0Deriv m (cubeDirection (orderDirection o 1)) 0) : _ → _)^[b])
          (((seriesDerivation (g0Deriv m (cubeDirection (orderDirection o 0)) 0) : _ → _)^[a])
            (AllM.current m 0 ^ r))) := by
  rw [orderRename_orbit]
  rw [map_iterate_deriv (currentMap m) (orderLower ℂ (orderDirection o 2)) _
    (fun p => currentMap_lower m (orderDirection o 2) p)]
  rw [map_iterate_deriv (currentMap m) (orderLower ℂ (orderDirection o 1)) _
    (fun p => currentMap_lower m (orderDirection o 1) p)]
  rw [map_iterate_deriv (currentMap m) (orderLower ℂ (orderDirection o 0)) _
    (fun p => currentMap_lower m (orderDirection o 0) p)]
  simp [currentMap_X,actualCurrent,cubeSign,cubeColor]

theorem order_orbit_coefficient_mem (m : ℕ) (o : Fin 6) (r a b c s : ℕ)
    (hr : 1 ≤ r) (hs : m < r + s) :
    PowerSeries.coeff s (currentMap m (orderRename ℂ o (orbit ℂ r a b c))) ∈
      AllM.candidateIdeal m := by
  rw [currentMap_order_orbit,coeff_current_iterate,coeff_current_iterate,coeff_current_iterate]
  apply AllMNormal.iterate_g0_mem m (cubeDirection (orderDirection o 2)) c
  apply AllMNormal.iterate_g0_mem m (cubeDirection (orderDirection o 1)) b
  apply AllMNormal.iterate_g0_mem m (cubeDirection (orderDirection o 0)) a
  exact AllM.seed_mem_candidate m ⟨(false,r,s),⟨hr,hs⟩⟩

def orderChainCurrentProduct (m : ℕ) (o : Fin 6) (r a b c : ℕ) :
    PowerSeries (MvPolynomial (Vars m) ℂ) :=
  actualCurrent m 0^(r-a) * actualCurrent m (orderColor o 1)^(a-b) *
    actualCurrent m (orderColor o 3)^(b-c) * actualCurrent m (orderColor o 7)^c

theorem currentMap_order_chainTerm (m : ℕ) (o : Fin 6) (r a b c : ℕ) :
    currentMap m (orderRename ℂ o (chainTerm ℂ r a b c)) =
      (towerCoeff r a b c : ℂ) • orderChainCurrentProduct m o r a b c := by
  simp only [chainTerm,orderRename,map_mul,map_pow,map_natCast,MvPolynomial.rename_X,
    orderColor_zero,currentMap_X,orderChainCurrentProduct,Algebra.smul_def,map_natCast]
  simp only [mul_assoc]

theorem order_chainTerm_coefficient_mem (m : ℕ) (o : Fin 6) (r a b c s : ℕ)
    (hr : 1 ≤ r) (hs : m < r + s) (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    PowerSeries.coeff s (currentMap m (orderRename ℂ o (chainTerm ℂ r a b c))) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) := by
  have hsource : PowerSeries.coeff s (currentMap m (orderRename ℂ o (orbit ℂ r a b c))) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) :=
    Submodule.mem_sup_left (order_orbit_coefficient_mem m o r a b c s hr hs)
  have hlow := current_coefficient_low m s (a+3*b+5*c) _
    (order_orbit_sub_chainTerm_mem ℂ o r a b c ha hb hc)
  rw [map_sub,map_sub] at hlow
  exact by
    simpa only [sub_sub_cancel] using Submodule.sub_mem _ hsource (Submodule.mem_sup_right hlow)

theorem order_chain_coefficient_mem (m : ℕ) (o : Fin 6) (r a b c s : ℕ)
    (hr : 1 ≤ r) (hs : m < r + s) (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    PowerSeries.coeff s (orderChainCurrentProduct m o r a b c) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) := by
  have h := order_chainTerm_coefficient_mem m o r a b c s hr hs ha hb hc
  rw [currentMap_order_chainTerm,PowerSeries.coeff_smul] at h
  have hn : (towerCoeff r a b c : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (towerCoeff_pos r a b c ha hb hc))
  exact (Submodule.smul_mem_iff _ hn).mp h

def rawOrderChainCurrentProduct (m : ℕ) (o : Fin 6) (r a b c : ℕ) :
    PowerSeries (MvPolynomial (Vars m) ℂ) :=
  AllM.current m 0^(r-a) * AllM.current m (cubeColor (orderColor o 1))^(a-b) *
    AllM.current m (cubeColor (orderColor o 3))^(b-c) *
    AllM.current m (cubeColor (orderColor o 7))^c

def orderChainPhase (o : Fin 6) (a b c : ℕ) : ℂ :=
  (cubeSign (orderColor o 7):ℂ)^c *
    ((cubeSign (orderColor o 3):ℂ)^(b-c) * (cubeSign (orderColor o 1):ℂ)^(a-b))

theorem cubeSign_ne_zero : ∀ i : Fin 8, cubeSign i ≠ 0 := by decide +kernel

theorem orderChainPhase_ne_zero (o : Fin 6) (a b c : ℕ) : orderChainPhase o a b c ≠ 0 := by
  have hh (i : Fin 8) : (cubeSign i:ℂ) ≠ 0 := by exact_mod_cast cubeSign_ne_zero i
  exact mul_ne_zero (pow_ne_zero _ (hh _))
    (mul_ne_zero (pow_ne_zero _ (hh _)) (pow_ne_zero _ (hh _)))

theorem orderChainCurrentProduct_eq_raw (m : ℕ) (o : Fin 6) (r a b c : ℕ) :
    orderChainCurrentProduct m o r a b c =
      orderChainPhase o a b c • rawOrderChainCurrentProduct m o r a b c := by
  have h0 : actualCurrent m 0 = AllM.current m 0 := by simp [actualCurrent,cubeSign,cubeColor]
  unfold orderChainCurrentProduct
  rw [h0]
  simp only [actualCurrent,rawOrderChainCurrentProduct,
    orderChainPhase,smul_pow,smul_mul_assoc,mul_smul_comm,smul_smul,mul_assoc]

/-- All six original-color chain coefficients admit actual source reductions
modulo strictly lower explicit color weight, uniformly in every mode cutoff. -/
theorem raw_order_chain_coefficient_mem (m : ℕ) (o : Fin 6) (r a b c s : ℕ)
    (hr : 1 ≤ r) (hs : m < r + s) (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    PowerSeries.coeff s (rawOrderChainCurrentProduct m o r a b c) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (a+3*b+5*c) := by
  have h := order_chain_coefficient_mem m o r a b c s hr hs ha hb hc
  rw [orderChainCurrentProduct_eq_raw,PowerSeries.coeff_smul] at h
  exact (Submodule.smul_mem_iff _ (orderChainPhase_ne_zero o a b c)).mp h

/-- Every whole coefficient on each maximal Boolean chain reduces strictly
in the actual color filtration. The four exponents are independent. -/
theorem raw_order_chain_counts_mem (m : ℕ) (o : Fin 6) (u v w z s : ℕ)
    (hr : 1 ≤ u + v + w + z) (hs : m < u + v + w + z + s) :
    PowerSeries.coeff s
      (AllM.current m 0^u * AllM.current m (cubeColor (orderColor o 1))^v *
        AllM.current m (cubeColor (orderColor o 3))^w *
        AllM.current m (cubeColor (orderColor o 7))^z) ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m (v+4*w+9*z) := by
  have h := raw_order_chain_coefficient_mem m o (u + v + w + z) (v+w+z) (w+z) z s
    hr hs (by omega) (by omega) (by omega)
  have h0 : u+v+w+z-(v+w+z) = u := by omega
  have h1 : v+w+z-(w+z) = v := by omega
  have h2 : w+z-z = w := by omega
  have he : v+w+z+3*(w+z)+5*z = v+4*w+9*z := by omega
  simpa only [rawOrderChainCurrentProduct,h0,h1,h2,he] using h

/-- Transfer to every actual D4 local-Weyl source. The only model premise is
its original defining relation, not a presentation or dimension statement. -/
theorem raw_order_chain_counts_mem_ann
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {R : CurrentModule D4sector.f V} {x : V} {m : ℕ}
    (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R x m)
    (o : Fin 6) (u v w z s : ℕ)
    (hr : 1 ≤ u + v + w + z) (hs : m < u + v + w + z + s) :
    PowerSeries.coeff s
      (AllM.current m 0^u * AllM.current m (cubeColor (orderColor o 1))^v *
        AllM.current m (cubeColor (orderColor o 3))^w *
        AllM.current m (cubeColor (orderColor o 7))^z) ∈
      (annIdeal R x (modeLetter m)).restrictScalars ℂ ⊔ currentColorLow m (v+4*w+9*z) := by
  have hi : (AllM.candidateIdeal m).restrictScalars ℂ ≤
      (annIdeal R x (modeLetter m)).restrictScalars ℂ :=
    AllM.source_candidateIdeal_le_ann hm h
  exact (sup_le_sup_right hi _) (raw_order_chain_counts_mem m o u v w z s hr hs)

end
#print axioms order_orbit_coefficient_mem
#print axioms order_chain_coefficient_mem
#print axioms raw_order_chain_coefficient_mem
#print axioms raw_order_chain_counts_mem
#print axioms raw_order_chain_counts_mem_ann
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
