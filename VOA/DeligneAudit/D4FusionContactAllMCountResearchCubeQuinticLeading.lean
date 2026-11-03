import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrentOrders
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCommute
import VOA.DeligneAudit.D4FusionContactAllMNormalQuintic

/-! The selected actual quintic source has an explicit uniform leading color
part. Whole current coefficients and all lower tails are retained. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4
noncomputable section

theorem currentColorLow_mul {m L n : ℕ} {p q : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ currentColorLow m L)
    (hq : q.IsWeightedHomogeneous (currentColorWeight m) n) :
    q*p ∈ currentColorLow m (L+n) := by
  classical
  change (↑p.support : Set (Vars m →₀ ℕ)) ⊆
    {d | Finsupp.weight (currentColorWeight m) d < L} at hp
  change (↑(q*p).support : Set (Vars m →₀ ℕ)) ⊆
    {d | Finsupp.weight (currentColorWeight m) d < L+n}
  intro d hd
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul q p hd)
  change Finsupp.weight (currentColorWeight m) (u+v) < L+n
  rw [map_add,hq (MvPolynomial.mem_support_iff.mp hu)]
  have hh := hp hv
  change Finsupp.weight (currentColorWeight m) v < L at hh
  omega

def cubicPolarHead (m s : ℕ) : MvPolynomial (Vars m) ℂ :=
  (12:ℂ) • PowerSeries.coeff s (AllM.current m 0 * AllM.current m 3 * AllM.current m 7)

def quinticHead (m : ℕ) : MvPolynomial (Vars m) ℂ :=
  (modeX m 1 0 * modeX m 2 (m-1)) * cubicPolarHead m (m-2)

theorem cubic_polar_current_coeff (m s : ℕ) :
    PowerSeries.coeff s (currentMap m (orbit ℂ 3 1 1 2)) =
      g0Deriv m 9 0 (g0Deriv m 9 0 (g0Deriv m 8 0
        (g0Deriv m 7 0 (AllMNormal.cubic m s)))) := by
  rw [currentMap_orbit,coeff_current_iterate,coeff_current_iterate,coeff_current_iterate]
  rfl

theorem cubic_head_current_coeff (m s : ℕ) :
    PowerSeries.coeff s (currentMap m
      ((12 : P8 ℂ) * MvPolynomial.X 0 * MvPolynomial.X 4 * MvPolynomial.X 7)) =
      cubicPolarHead m s := by
  have hh : currentMap m
      ((12 : P8 ℂ) * MvPolynomial.X 0 * MvPolynomial.X 4 * MvPolynomial.X 7) =
      (12:ℂ) • (AllM.current m 0 * AllM.current m 3 * AllM.current m 7) := by
    simp only [map_mul,map_ofNat,currentMap_X,actualCurrent]
    simp only [show cubeSign 0 = 1 from rfl,show cubeSign 4 = -1 from rfl,
      show cubeSign 7 = -1 from rfl,show cubeColor 0 = 0 from rfl,
      show cubeColor 4 = 3 from rfl,show cubeColor 7 = 7 from rfl,
      Int.cast_one,Int.cast_neg,Algebra.smul_def,map_ofNat,map_one,map_neg]
    ring
  rw [hh,PowerSeries.coeff_smul]
  rfl

/-- Actual cubic polar coefficients have precisely the proved cube color head. -/
theorem cubicPolar_sub_head_mem (m s : ℕ) :
    g0Deriv m 9 0 (g0Deriv m 9 0 (g0Deriv m 8 0
      (g0Deriv m 7 0 (AllMNormal.cubic m s)))) - cubicPolarHead m s ∈
      currentColorLow m 10 := by
  have h := current_coefficient_low m s 10 _ (cubic_polar_sub_head_mem ℂ)
  rw [map_sub,map_sub,cubic_polar_current_coeff,cubic_head_current_coeff] at h
  exact h

theorem quintic_multiplier_weighted (m : ℕ) :
    (modeX m 1 0 * modeX m 2 (m-1)).IsWeightedHomogeneous (currentColorWeight m) 2 := by
  have h1 := actualMode_weighted m 0 1
  have h2 := actualMode_weighted m (m-1) 2
  have h := h1.mul h2
  simpa [actualMode,cubeSign,cubeColor,sourceEnergy] using h

/-- Uniform leading color part of the actual whole quintic row. -/
theorem quinticLowRow_sub_head_mem (m : ℕ) :
    AllMNormal.quinticLowRow m - quinticHead m ∈ currentColorLow m 12 := by
  have h := currentColorLow_mul (cubicPolar_sub_head_mem m (m-2))
    (quintic_multiplier_weighted m)
  change (modeX m 1 0 * modeX m 2 (m-1)) *
    (AllMNormal.lowCubicPolar m - cubicPolarHead m (m-2)) ∈ currentColorLow m 12 at h
  simpa only [mul_sub,AllMNormal.quinticLowRow,quinticHead] using h

theorem quinticHead_mem_candidate_sup_low (m : ℕ) :
    quinticHead m ∈ (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m 12 := by
  have hsource : AllMNormal.quinticLowRow m ∈
      (AllM.candidateIdeal m).restrictScalars ℂ ⊔ currentColorLow m 12 :=
    Submodule.mem_sup_left (AllMNormal.quinticLowRow_mem m)
  simpa only [sub_sub_cancel] using Submodule.sub_mem _ hsource
    (Submodule.mem_sup_right (quinticLowRow_sub_head_mem m))

theorem quinticHead_mem_ann_sup_low
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {R : CurrentModule D4sector.f V} {x : V} {m : ℕ}
    (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R x m) :
    quinticHead m ∈ (annIdeal R x (modeLetter m)).restrictScalars ℂ ⊔ currentColorLow m 12 := by
  have hi : (AllM.candidateIdeal m).restrictScalars ℂ ≤
      (annIdeal R x (modeLetter m)).restrictScalars ℂ := AllM.source_candidateIdeal_le_ann hm h
  exact (sup_le_sup_right hi _) (quinticHead_mem_candidate_sup_low m)

end
#print axioms cubicPolar_sub_head_mem
#print axioms quinticLowRow_sub_head_mem
#print axioms quinticHead_mem_candidate_sup_low
#print axioms quinticHead_mem_ann_sup_low
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
