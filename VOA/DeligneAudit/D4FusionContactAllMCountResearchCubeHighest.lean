import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrentModes

/-! Whole highest-color coefficient rows and their Cartan shifts are actual
D4 source rows. This proves soundness, not completeness or a dimension count. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

abbrev TopPoly (m : ℕ) := MvPolynomial (Fin m) ℂ

def topModeX (m r : ℕ) : TopPoly m :=
  if hr : r < m then MvPolynomial.X ⟨r,hr⟩ else 0

def topShift (m k : ℕ) : Derivation ℂ (TopPoly m) (TopPoly m) :=
  MvPolynomial.mkDerivation ℂ (fun i => topModeX m (k+i.val))

def topMap (m : ℕ) : TopPoly m →ₐ[ℂ] MvPolynomial (Vars m) ℂ :=
  MvPolynomial.aeval (fun i => modeX m 0 i.val)

theorem topMap_X (m : ℕ) (i : Fin m) :
    topMap m (MvPolynomial.X i) = modeX m 0 i.val := MvPolynomial.aeval_X _ _

theorem topMap_modeX (m r : ℕ) : topMap m (topModeX m r) = modeX m 0 r := by
  by_cases hr : r < m
  · simp only [topModeX,dif_pos hr,topMap_X]
  · simp only [topModeX,modeX,dif_neg hr,map_zero]

/-- The actual highest-color Cartan coefficient is -2, not an assumed unit. -/
theorem topMap_shift (m k : ℕ) (p : TopPoly m) :
    topMap m (topShift m k p) = (-1/2:ℂ) • g0Deriv m 1 k (topMap m p) := by
  have h := map_derivation_to (topMap m) (topShift m k)
    ((-1/2:ℂ) • g0Deriv m 1 k) (fun i => ?_) p
  · simpa only [Derivation.smul_apply] using h
  · rw [show topShift m k (MvPolynomial.X i) = topModeX m (k+i.val) from
      MvPolynomial.mkDerivation_X ℂ _ _,topMap_modeX,topMap_X,
      Derivation.smul_apply,AllMNormal.cartan_modeX,smul_smul]
    norm_num [AllMNormal.cartanCoeff]

theorem topMap_shift_mem (m k : ℕ) (p : TopPoly m)
    (hp : topMap m p ∈ AllM.candidateIdeal m) :
    topMap m (topShift m k p) ∈ AllM.candidateIdeal m := by
  rw [topMap_shift]
  exact ((AllM.candidateIdeal m).restrictScalars ℂ).smul_mem _ (AllMNormal.g0_closed m k 1 hp)

def topCurrent (m : ℕ) : PowerSeries (TopPoly m) := PowerSeries.mk (topModeX m)

theorem topCurrent_map (m : ℕ) :
    PowerSeries.map (topMap m).toRingHom (topCurrent m) = AllM.current m 0 := by
  apply PowerSeries.ext
  intro s
  simp only [PowerSeries.coeff_map,topCurrent,AllM.current,PowerSeries.coeff_mk]
  change topMap m (topModeX m s) = modeX m 0 s
  exact topMap_modeX m s

/-- The exact original admissible whole U-power coefficient, at every order. -/
theorem topMap_seed (m r s : ℕ) :
    topMap m (PowerSeries.coeff s (topCurrent m^r)) =
      PowerSeries.coeff s (AllM.current m 0^r) := by
  change (topMap m).toRingHom (PowerSeries.coeff s (topCurrent m^r)) = _
  rw [← PowerSeries.coeff_map,map_pow,topCurrent_map]

theorem topMap_seed_mem (m r s : ℕ) (hr : 1 ≤ r) (hs : m < r + s) :
    topMap m (PowerSeries.coeff s (topCurrent m^r)) ∈ AllM.candidateIdeal m := by
  rw [topMap_seed]
  exact AllM.seed_mem_candidate m ⟨(false,r,s),⟨hr,hs⟩⟩

end
#print axioms topMap_shift
#print axioms topMap_shift_mem
#print axioms topMap_seed_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
