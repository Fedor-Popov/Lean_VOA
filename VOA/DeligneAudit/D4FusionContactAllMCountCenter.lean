import VOA.DeligneAudit.D4FusionContactAllMNormalIdeal

/-! The actual all-A-deleted quotient of the fixed all-m polynomial ideal. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount

noncomputable section

abbrev CenterRing (m : ℕ) := MvPolynomial (Fin m) ℂ

def centerProjection (m : ℕ) : MvPolynomial (Vars m) ℂ →ₐ[ℂ] CenterRing m :=
  MvPolynomial.aeval (fun x => if x.1 = 8 then MvPolynomial.X x.2 else 0)

def centerSection (m : ℕ) : CenterRing m →ₐ[ℂ] MvPolynomial (Vars m) ℂ :=
  MvPolynomial.rename (fun i => ((8 : Fin 9), i))

theorem centerProjection_section (m : ℕ) (p : CenterRing m) :
    centerProjection m (centerSection m p) = p := by
  have he : (centerProjection m).comp (centerSection m) = AlgHom.id ℂ (CenterRing m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [centerProjection, centerSection]
  exact congrArg (fun f : CenterRing m →ₐ[ℂ] CenterRing m => f p) he

theorem centerProjection_surjective (m : ℕ) : Function.Surjective (centerProjection m) :=
  fun p => ⟨centerSection m p, centerProjection_section m p⟩

def centerIdeal (m : ℕ) : Ideal (CenterRing m) :=
  Ideal.map (centerProjection m).toRingHom (AllM.candidateIdeal m)

abbrev CenterModel (m : ℕ) := CenterRing m ⧸ centerIdeal m

def centerMode (m r : ℕ) : CenterRing m :=
  if hr : r < m then MvPolynomial.X ⟨r, hr⟩ else 0

def centerCurrent (m : ℕ) : PowerSeries (CenterRing m) := PowerSeries.mk (centerMode m)

theorem centerMode_high (m r : ℕ) (hr : m ≤ r) : centerMode m r = 0 := dif_neg (by omega)

theorem centerProjection_mode (m r : ℕ) :
    centerProjection m (modeX m 8 r) = centerMode m r := by
  by_cases hr : r < m <;> simp [modeX, centerProjection, centerMode, hr]

theorem map_centerCurrent (m : ℕ) :
    PowerSeries.map (centerProjection m).toRingHom (AllM.current m 8) = centerCurrent m := by
  apply PowerSeries.ext
  intro r
  simp only [PowerSeries.coeff_map, AllM.current, PowerSeries.coeff_mk, centerCurrent]
  exact centerProjection_mode m r

/-- Only the original whole center coefficient seed is used. Extra
relations in the image ideal may shrink this actual quotient further. -/
theorem center_coefficient_mem (m r s : ℕ) (hr : 1 ≤ r) (hs : 2 * m < r + s) :
    PowerSeries.coeff s (centerCurrent m ^ r) ∈ centerIdeal m := by
  have hp : PowerSeries.coeff s (AllM.current m 8 ^ r) ∈ AllM.candidateIdeal m :=
    AllM.seed_mem_candidate m ⟨(true, r, s), ⟨hr, hs⟩⟩
  have hh := Ideal.mem_map_of_mem (centerProjection m).toRingHom hp
  rw [← PowerSeries.coeff_map, map_pow, map_centerCurrent] at hh
  exact hh

def sourceCenterMap (m : ℕ) : AllM.Model m →ₗ[ℂ] CenterModel m :=
  ((AllM.modelIdeal m).restrictScalars ℂ).liftQ
    (((Ideal.Quotient.mkₐ ℂ (centerIdeal m)).comp (centerProjection m)).toLinearMap) (by
      intro p hp
      change Ideal.Quotient.mk (centerIdeal m) (centerProjection m p) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change p ∈ AllM.modelIdeal m at hp
      rw [AllMNormal.modelIdeal_eq_candidate] at hp
      exact Ideal.mem_map_of_mem (centerProjection m).toRingHom hp)

theorem sourceCenterMap_mk (m : ℕ) (p : MvPolynomial (Vars m) ℂ) :
    sourceCenterMap m (((AllM.modelIdeal m).restrictScalars ℂ).mkQ p) =
      Ideal.Quotient.mk (centerIdeal m) (centerProjection m p) := rfl

theorem sourceCenterMap_surjective (m : ℕ) : Function.Surjective (sourceCenterMap m) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨((AllM.modelIdeal m).restrictScalars ℂ).mkQ (centerSection m p), ?_⟩
  rw [sourceCenterMap_mk, centerProjection_section]

theorem sourceCenterMap_A (m : ℕ) (i : Fin 8) (k : Fin m) :
    sourceCenterMap m (((AllM.modelIdeal m).restrictScalars ℂ).mkQ
      (MvPolynomial.X (i.castSucc, k))) = 0 := by
  rw [sourceCenterMap_mk]
  have hi : i.castSucc ≠ (8 : Fin 9) := Fin.castSucc_ne_last i
  simp [centerProjection, hi]

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount.center_coefficient_mem
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount.sourceCenterMap_surjective
