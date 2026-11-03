import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterContactCoverage
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticSourceReduction

/-! original U-source words are literal highest-color Cube words. Every U
source of power at most three lies in the literal quadratic/cubic polar ideal
J; every quartic U source is congruent modulo J to a multiple of one static
quartic polar. No matching budget is used: these hold for every U source. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
open Cube (quadraticCubicPolarIdeal)
noncomputable section

/-- The axis of a negative-current letter; inverse to `negative` on category one. -/
def toAxis (x : Fin 18 × ℕ) : Fin 3 × ℕ := (⟨min (x.1.val - 7) 2,by omega⟩,x.2)

theorem cubeDirection_val : ∀ d : Fin 3, (Cube.cubeDirection d).val = 7 + d.val := by decide

theorem castAdd_cubeDirection_toAxis (x : Fin 18 × ℕ) (hx : category x.1 = 1) :
    Fin.castAdd 8 (Cube.cubeDirection (toAxis x).1) = x.1 := by
  have h := (category_one_iff x.1).mp hx
  apply Fin.ext
  rw [Fin.val_castAdd,cubeDirection_val]
  simp only [toAxis]
  omega

/-- A negative letter is the actual lower g0 derivation of its axis. -/
theorem negative_deriv_eq (m : ℕ) (x : Fin 18 × ℕ) (hx : category x.1 = 1) (p : Ring ℂ m) :
    deriv ℂ m x.1 x.2 p = g0Deriv m (Cube.cubeDirection (toAxis x).1) (toAxis x).2 p := by
  rw [← deriv_g0,castAdd_cubeDirection_toAxis x hx]
  rfl

/-- Whole negative words are literal Cube negative-mode words. -/
theorem negative_word_eq (m : ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 1)
    (p : Ring ℂ m) :
    wordOp (representation ℂ m) l p = Cube.negativeModeWord m (l.map toAxis) p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change deriv ℂ m x.1 x.2 (wordOp (representation ℂ m) l p) = _
      rw [ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)),
        negative_deriv_eq m x (hl x List.mem_cons_self)]
      rfl

theorem monoMap_zero_eq_topMap (m : ℕ) (p : MonoRing ℂ m) :
    monoMap ℂ m 0 p = Cube.topMap m p := rfl

theorem shiftWord_eq_topShiftWord (m : ℕ) (ks : List ℕ) (p : MonoRing ℂ m) :
    shiftWord m ks p = Cube.topShiftWord m ks p := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      change monoShift ℂ m k (shiftWord m ks p) = Cube.topShift m k (Cube.topShiftWord m ks p)
      rw [ih]
      rfl

theorem monoSeed_eq_top (m : ℕ) (j : AllM.SeedIndex m) :
    monoSeed m j = PowerSeries.coeff j.val.2.2 (Cube.topCurrent m ^ j.val.2.1) := rfl

theorem u_outer_negative (m : ℕ) (i : OrbitSourceIndex m) (hb : i.seed.val.1 = false) :
    ∀ x ∈ i.outer, category x.1 = 1 := by
  intro x hx
  simpa only [branchCategory,hb,Bool.false_eq_true,if_false] using i.branch x hx

/-- BRIDGE: every original U source is a Cube negative word on a top shift word. -/
theorem u_orbitSourcePoly_eq (m : ℕ) (i : OrbitSourceIndex m) (hb : i.seed.val.1 = false) :
    orbitSourcePoly m i = Cube.negativeModeWord m (i.outer.map toAxis)
      (Cube.topMap m (Cube.topShiftWord m i.shifts
        (PowerSeries.coeff i.seed.val.2.2 (Cube.topCurrent m ^ i.seed.val.2.1)))) := by
  rw [orbitSourcePoly,sourceWord,negative_word_eq m i.outer (u_outer_negative m i hb)]
  have hc : sourceColor i.seed.val.1 = 0 := by simp [sourceColor,hb]
  rw [hc,monoMap_zero_eq_topMap,shiftWord_eq_topShiftWord,monoSeed_eq_top]

theorem u_seed_threshold (m : ℕ) (i : OrbitSourceIndex m) (hb : i.seed.val.1 = false) :
    m < i.seed.val.2.1 + i.seed.val.2.2 := by
  simpa only [AllM.seedThreshold,hb,Bool.false_eq_true,if_false] using i.seed.property.2

/-- Every U source of power at most three lies in J (power one vanishes). -/
theorem u_low_source_mem_polarIdeal (m : ℕ) (i : OrbitSourceIndex m)
    (hb : i.seed.val.1 = false) (hr : i.seed.val.2.1 ≤ 3) :
    orbitSourcePoly m i ∈ quadraticCubicPolarIdeal m := by
  have hth := u_seed_threshold m i hb
  have h1 := i.seed.property.1
  rw [u_orbitSourcePoly_eq m i hb]
  apply Cube.negativeModeWord_mem_polarIdeal
  apply Cube.topMap_topQuadraticCubicIdeal_mem
  apply Cube.topShiftWord_mem_topIdeal
  rcases (show i.seed.val.2.1 = 1 ∨ i.seed.val.2.1 = 2 ∨ i.seed.val.2.1 = 3 by omega) with h | h
  · rw [← monoSeed_eq_top m i.seed,monoSeed_linear_zero m i.seed h]
    exact zero_mem _
  · exact Cube.topQuadraticCubic_coeff_mem m _ _ h hth

/-- Axis counts of the negative word of a U source. -/
def uAxisCount {m : ℕ} (i : OrbitSourceIndex m) (d : Fin 3) : ℕ :=
  Cube.negativeModeAxisCount d (i.outer.map toAxis)

/-- The static quartic polar of a U source, at its original summed current mode. -/
def uQuarticStatic (m : ℕ) (i : OrbitSourceIndex m) : Ring ℂ m :=
  PowerSeries.coeff (i.seed.val.2.2 + i.shifts.sum + (i.outer.map Prod.snd).sum)
    (Cube.currentMap m (Cube.orbit ℂ 4 (uAxisCount i 0) (uAxisCount i 1) (uAxisCount i 2)))

theorem toAxis_modes (l : List (Fin 18 × ℕ)) :
    ((l.map toAxis).map Prod.snd).sum = (l.map Prod.snd).sum := by
  rw [List.map_map]
  rfl

/-- Every quartic U source is 4^(number of shifts) times its static polar, modulo J. -/
theorem u_quartic_source_sub_static_mem (m : ℕ) (i : OrbitSourceIndex m)
    (hb : i.seed.val.1 = false) (hr : i.seed.val.2.1 = 4) :
    orbitSourcePoly m i - (4 ^ i.shifts.length) • uQuarticStatic m i ∈
      quadraticCubicPolarIdeal m := by
  have hth := u_seed_threshold m i hb
  rw [hr] at hth
  have h := Cube.quartic_shift_negativeModeWord_static_mem_polarIdeal m i.seed.val.2.2
    i.shifts (i.outer.map toAxis) hth
  rw [toAxis_modes] at h
  rw [u_orbitSourcePoly_eq m i hb,hr]
  exact h

theorem uQuarticStatic_mem_candidate (m : ℕ) (i : OrbitSourceIndex m)
    (hb : i.seed.val.1 = false) (hr : i.seed.val.2.1 = 4) :
    uQuarticStatic m i ∈ AllM.candidateIdeal m := by
  have hth := u_seed_threshold m i hb
  unfold uQuarticStatic
  exact Cube.current_orbit_coeff_mem m 4 _ _ _ _ (by norm_num) (by omega)

/-- MAIN (power at most three): such U rows lie in J. No slice hypothesis is needed. -/
theorem u_low_row_mem_polarIdeal (m : ℕ) (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ))
    (hb : q.1.seed.val.1 = false) (hr : q.1.seed.val.2.1 ≤ 3) :
    MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈ quadraticCubicPolarIdeal m :=
  Ideal.mul_mem_left _ _ (u_low_source_mem_polarIdeal m q.1 hb hr)

/-- MAIN (power four): a quartic U row is a static quartic row modulo J. -/
theorem u_quartic_row_sub_static_mem (m : ℕ)
    (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ))
    (hb : q.1.seed.val.1 = false) (hr : q.1.seed.val.2.1 = 4) :
    MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 -
      (4 ^ q.1.shifts.length) • (MvPolynomial.monomial q.2 (1 : ℂ) * uQuarticStatic m q.1) ∈
      quadraticCubicPolarIdeal m := by
  rw [← mul_smul_comm,← mul_sub]
  exact Ideal.mul_mem_left _ _ (u_quartic_source_sub_static_mem m q.1 hb hr)

/-- The original quintic U-source rows of the quintic slice. -/
def quinticU5Rows (m : ℕ) : Set (Ring ℂ m) :=
  (fun q => MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1) ''
    {q | q ∈ boundedColorComponentPairs m 5 (2 * m - 3) (fun _ => 2) ∧
      q.1.seed.val.1 = false ∧ q.1.seed.val.2.1 = 5}

/-- The static quartic rows replacing the matching quartic U-source rows. -/
def quinticStaticQuarticRows (m : ℕ) : Set (Ring ℂ m) :=
  (fun q => MvPolynomial.monomial q.2 (1 : ℂ) * uQuarticStatic m q.1) ''
    {q | q ∈ boundedColorComponentPairs m 5 (2 * m - 3) (fun _ => 2) ∧
      q.1.seed.val.1 = false ∧ q.1.seed.val.2.1 = 4}

/-- MAIN: modulo J the candidate quintic slice is spanned by the quintic U rows
and the static quartic rows (m >= 2, inherited from the C-branch coverage). -/
theorem candidate_quintic_slice_eq_U5_static_sup_polar (m : ℕ) (hm : 2 ≤ m) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) =
    (Submodule.span ℂ (quinticU5Rows m) ⊔ Submodule.span ℂ (quinticStaticQuarticRows m) ⊔
      (quadraticCubicPolarIdeal m).restrictScalars ℂ) ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) := by
  have hslice := candidate_quintic_color_component_eq_finite_span m
  apply le_antisymm
  · rw [candidate_quintic_slice_eq_U_sup_polar m hm]
    apply inf_le_inf_right
    apply sup_le _ le_sup_right
    apply Submodule.span_le.mpr
    rintro p ⟨q,⟨hq,hb⟩,rfl⟩
    have h1 := q.1.seed.property.1
    have h5 := matching_source_power_le m 5 (2 * m - 3) q.1 q.2 hq.1.2.2
    rcases (show q.1.seed.val.2.1 ≤ 3 ∨ q.1.seed.val.2.1 = 4 ∨ q.1.seed.val.2.1 = 5 by omega)
      with hr | hr | hr
    · exact Submodule.mem_sup_right (u_low_row_mem_polarIdeal m q hb hr)
    · have hd := u_quartic_row_sub_static_mem m q hb hr
      have hs : MvPolynomial.monomial q.2 (1 : ℂ) * uQuarticStatic m q.1 ∈
          Submodule.span ℂ (quinticStaticQuarticRows m) :=
        Submodule.subset_span ⟨q,⟨hq,hb,hr⟩,rfl⟩
      change MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈ _
      rw [← sub_add_cancel
        (MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1)
        ((4 ^ q.1.shifts.length) • (MvPolynomial.monomial q.2 (1 : ℂ) * uQuarticStatic m q.1))]
      exact Submodule.add_mem _ (Submodule.mem_sup_right hd)
        (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_of_tower_mem _ _ hs)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.subset_span ⟨q,⟨hq,hb,hr⟩,rfl⟩))
  · intro p hp
    refine ⟨?_,hp.2⟩
    have hU : Submodule.span ℂ (quinticU5Rows m) ≤
        (AllM.candidateIdeal m).restrictScalars ℂ := by
      apply Submodule.span_le.mpr
      rintro p ⟨q,hq,rfl⟩
      have hrow : MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈
          Submodule.span ℂ (finiteColorComponentRows m 5 (2 * m - 3) (fun _ => 2)) :=
        Submodule.subset_span ⟨q,hq.1,rfl⟩
      rw [← hslice] at hrow
      exact hrow.1
    have hS : Submodule.span ℂ (quinticStaticQuarticRows m) ≤
        (AllM.candidateIdeal m).restrictScalars ℂ := by
      apply Submodule.span_le.mpr
      rintro p ⟨q,hq,rfl⟩
      exact Ideal.mul_mem_left _ _ (uQuarticStatic_mem_candidate m q.1 hq.2.1 hq.2.2)
    have hJ : (quadraticCubicPolarIdeal m).restrictScalars ℂ ≤
        (AllM.candidateIdeal m).restrictScalars ℂ :=
      fun x hx => Cube.quadraticCubicPolarIdeal_le_candidate m hx
    exact (sup_le (sup_le hU hS) hJ) hp.1

end
#print axioms u_orbitSourcePoly_eq
#print axioms u_low_row_mem_polarIdeal
#print axioms u_quartic_row_sub_static_mem
#print axioms candidate_quintic_slice_eq_U5_static_sup_polar
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
