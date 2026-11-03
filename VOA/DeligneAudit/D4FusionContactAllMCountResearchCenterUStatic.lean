import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterUBridge

/-! Intrinsic shapes of the U rows of the quintic slice. A matching quartic U
row has one linear multiplier X_(c,k) with c not the center color, and its
static polar has current mode 2m-3-k and axis counts 2 - bit_d(c). So, modulo
J, the candidate quintic slice is spanned by the quintic U rows and the 8m
static rows `staticQuarticRow m x`, x.1 ≠ 8. A matching quintic U row has the
constant multiplier, axis counts (2,2,2) and summed mode 2m-3. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
open Cube (quadraticCubicPolarIdeal)
noncomputable section

theorem toAxis_eq_iff (x : Fin 18 × ℕ) (d : Fin 3) (hx : category x.1 = 1) :
    (toAxis x).1 = d ↔ x.1 = negative d := by
  have h := (category_one_iff x.1).mp hx
  have hd := d.isLt
  rw [Fin.ext_iff,Fin.ext_iff]
  simp only [toAxis,negative]
  omega

/-- The bit grade of a negative word is its literal axis count. -/
theorem axis_wordGrade_eq (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 1)
    (d : Fin 3) :
    wordGrade (axisIncrement d) 0 l = (Cube.negativeModeAxisCount d (l.map toAxis) : ℤ) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hx := hl x List.mem_cons_self
      have hw : wordGrade (axisIncrement d) 0 (x :: l) =
          axisIncrement d x.1 + 0 * x.2 + wordGrade (axisIncrement d) 0 l := by
        simp only [wordGrade,List.map_cons,List.sum_cons]
      rw [hw,ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)),zero_mul,add_zero]
      simp only [List.map_cons,Cube.negativeModeAxisCount,Nat.cast_add,axisIncrement]
      by_cases h : x.1 = negative d
      · rw [if_pos h,if_pos ((toAxis_eq_iff x d hx).mpr h)]
        rfl
      · rw [if_neg h,if_neg (fun h' => h ((toAxis_eq_iff x d hx).mp h'))]
        rfl

theorem componentWeight_zero (m : ℕ) (x : Fin 9 × Fin m) : componentWeight m x 0 = 1 := by
  simp [componentWeight,modeWeight]

/-- A multiplier of PBW weight one is a single variable. -/
theorem pbw_one_single (m : ℕ) (e : (Fin 9 × Fin m) →₀ ℕ)
    (h : Finsupp.weight (componentWeight m) e 0 = 1) : ∃ x, e = Finsupp.single x 1 := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨x,hx⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hx0 := Finsupp.mem_support_iff.mp hx
  have hsplit := Finsupp.single_add_erase x e
  have hw : Finsupp.weight (componentWeight m) e 0 =
      (e x : ℤ) + Finsupp.weight (componentWeight m) (e.erase x) 0 := by
    conv_lhs => rw [← hsplit]
    rw [map_add,Finsupp.weight_single,Pi.add_apply,Pi.smul_apply,componentWeight_zero,
      nsmul_eq_mul,mul_one]
  have hr := component_monomial_weight_nonneg m (e.erase x) 0
  have hz : Finsupp.weight (componentWeight m) (e.erase x) 0 = 0 := by omega
  have he : e.erase x = 0 := by
    ext y
    have hy := component_term_le_weight m (e.erase x) 0 y
    rw [componentWeight_zero,mul_one,hz] at hy
    simp only [Finsupp.coe_zero,Pi.zero_apply]
    omega
  have hex : e x = 1 := by omega
  refine ⟨x,?_⟩
  rw [← hsplit,he,add_zero,hex]

/-- Axis counts of the static quartic polar attached to a multiplier color. -/
def staticAxis (c : Fin 9) (d : Fin 3) : ℕ := 2 - (bitWeight d c).toNat

/-- The static quartic row of one linear multiplier X_(c,k). -/
def staticQuarticRow (m : ℕ) (x : Fin 9 × Fin m) : Ring ℂ m :=
  MvPolynomial.monomial (Finsupp.single x 1) (1 : ℂ) *
    PowerSeries.coeff (2 * m - 3 - x.2.val) (Cube.currentMap m
      (Cube.orbit ℂ 4 (staticAxis x.1 0) (staticAxis x.1 1) (staticAxis x.1 2)))

/-- The 8m intrinsic static quartic rows: non-center multiplier colors. -/
def quinticStaticRows (m : ℕ) : Set (Ring ℂ m) := staticQuarticRow m '' {x | x.1 ≠ 8}

theorem staticQuarticRow_mem_candidate (m : ℕ) (x : Fin 9 × Fin m) :
    staticQuarticRow m x ∈ AllM.candidateIdeal m := by
  have hx := x.2.isLt
  exact Ideal.mul_mem_left _ _
    (Cube.current_orbit_coeff_mem m 4 _ _ _ _ (by norm_num) (by omega))

/-- The intrinsic static rows span at most 8m dimensions. -/
theorem finrank_span_quinticStaticRows_le (m : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (quinticStaticRows m)) ≤ 8 * m := by
  classical
  have he : quinticStaticRows m =
      ((Finset.univ.filter (fun x : Fin 9 × Fin m => x.1 ≠ 8)).image (staticQuarticRow m) :
        Set (Ring ℂ m)) := by
    ext p
    simp [quinticStaticRows]
  have hf : Finset.univ.filter (fun x : Fin 9 × Fin m => x.1 ≠ 8) =
      Finset.univ.filter (fun c : Fin 9 => c ≠ 8) ×ˢ (Finset.univ : Finset (Fin m)) := by
    ext x
    simp
  have h8 : (Finset.univ.filter (fun c : Fin 9 => c ≠ 8)).card = 8 := by decide
  rw [he]
  refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
  rw [hf,Finset.card_product,h8,Finset.card_univ,Fintype.card_fin]

/-- The six matching equations of a U row, read off exactly. -/
theorem u_matching_equations (m : ℕ) (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ))
    (hq : q ∈ boundedColorComponentPairs m 5 (2 * m - 3) (fun _ => 2))
    (hb : q.1.seed.val.1 = false) :
    Finsupp.weight (componentWeight m) q.2 0 + (q.1.seed.val.2.1 : ℤ) = 5 ∧
      Finsupp.weight (componentWeight m) q.2 1 +
        ((q.1.seed.val.2.2 + q.1.shifts.sum + (q.1.outer.map Prod.snd).sum : ℕ) : ℤ) =
          ((2 * m - 3 : ℕ) : ℤ) ∧
      Finsupp.weight (componentWeight m) q.2 2 = 0 ∧
      ∀ d : Fin 3, Finsupp.weight (modeWeight m (bitWeight d) 0) q.2 +
        (uAxisCount q.1 d : ℤ) = 2 := by
  obtain ⟨⟨-,-,hmatch⟩,hcolor⟩ := hq
  refine ⟨congrFun hmatch 0,congrFun hmatch 1,?_,?_⟩
  · have h2 := congrFun hmatch 2
    change Finsupp.weight (componentWeight m) q.2 2 +
      (if q.1.seed.val.1 then (q.1.seed.val.2.1 : ℤ) - q.1.outer.length else 0) = 0 at h2
    simpa only [hb,Bool.false_eq_true,if_false,add_zero] using h2
  · intro d
    have hc := congrFun hcolor (Fin.natAdd 3 d)
    rw [Pi.add_apply,weight_coord] at hc
    have hsrc : orbitSourceColorDegree m q.1 (Fin.natAdd 3 d) = orbitSourceBitDegree m q.1 d := by
      fin_cases d <;> rfl
    have hcw : (fun x => colorComponentWeight m x (Fin.natAdd 3 d)) =
        modeWeight m (bitWeight d) 0 := by
      funext x
      fin_cases d <;> rfl
    have htg : pureAColorTargetDegree 5 (2 * m - 3) (fun _ => 2) (Fin.natAdd 3 d) = 2 := by
      fin_cases d <;> rfl
    rw [hsrc,hcw,htg,orbitSourceBitDegree,hb,
      axis_wordGrade_eq q.1.outer (u_outer_negative m q.1 hb)] at hc
    simpa only [Bool.false_eq_true,if_false] using hc

/-- Every matching static quartic row is one of the 8m intrinsic static rows. -/
theorem quinticStaticQuarticRows_subset (m : ℕ) :
    quinticStaticQuarticRows m ⊆ quinticStaticRows m := by
  rintro p ⟨q,⟨hq,hb,hr⟩,rfl⟩
  obtain ⟨h0,h1,h2,hbit⟩ := u_matching_equations m q hq hb
  rw [hr] at h0
  obtain ⟨x,hx⟩ := pbw_one_single m q.2 (by omega)
  have hwx : ∀ j, Finsupp.weight (componentWeight m) q.2 j = componentWeight m x j := by
    intro j
    rw [hx,Finsupp.weight_single,one_smul]
  have hbx : ∀ d : Fin 3, Finsupp.weight (modeWeight m (bitWeight d) 0) q.2 =
      bitWeight d x.1 := by
    intro d
    rw [hx,Finsupp.weight_single,one_smul]
    simp [modeWeight]
  rw [hwx] at h1 h2
  have hc : cWeight x.1 = 0 := by simpa [componentWeight,modeWeight] using h2
  have hk : componentWeight m x 1 = x.2.val := by simp [componentWeight,modeWeight]
  rw [hk] at h1
  refine ⟨x,fun h8 => by simp [h8,cWeight] at hc,?_⟩
  have hs : q.1.seed.val.2.2 + q.1.shifts.sum + (q.1.outer.map Prod.snd).sum =
      2 * m - 3 - x.2.val := by omega
  have ha : ∀ d : Fin 3, uAxisCount q.1 d = staticAxis x.1 d := by
    intro d
    have h := hbit d
    rw [hbx] at h
    have hn := bitWeight_nonneg d x.1
    have hl := bitWeight_le_one d x.1
    simp only [staticAxis]
    omega
  simp only [staticQuarticRow,uQuarticStatic,hx,hs,ha]

/-- Every matching quintic U row: constant multiplier, axis counts two, mode 2m-3. -/
theorem quinticU5_row_shape (m : ℕ) (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ))
    (hq : q ∈ boundedColorComponentPairs m 5 (2 * m - 3) (fun _ => 2))
    (hb : q.1.seed.val.1 = false) (hr : q.1.seed.val.2.1 = 5) :
    q.2 = 0 ∧ q.1.seed.val.2.2 + q.1.shifts.sum + (q.1.outer.map Prod.snd).sum = 2 * m - 3 ∧
      ∀ d : Fin 3, uAxisCount q.1 d = 2 := by
  have he := matching_fifth_source_multiplier_zero m (2 * m - 3) q.1 q.2 hr hq.1.2.2
  obtain ⟨-,h1,-,hbit⟩ := u_matching_equations m q hq hb
  rw [he] at h1 hbit
  simp only [map_zero,Pi.zero_apply,zero_add] at h1 hbit
  refine ⟨he,by omega,fun d => by have := hbit d; omega⟩

/-- MAIN: modulo J the candidate quintic slice is spanned by the quintic U rows
and the 8m intrinsic static quartic rows (m >= 2, from the C-branch coverage). -/
theorem candidate_quintic_slice_eq_U5_staticRows_sup_polar (m : ℕ) (hm : 2 ≤ m) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) =
    (Submodule.span ℂ (quinticU5Rows m) ⊔ Submodule.span ℂ (quinticStaticRows m) ⊔
      (quadraticCubicPolarIdeal m).restrictScalars ℂ) ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) := by
  apply le_antisymm
  · rw [candidate_quintic_slice_eq_U5_static_sup_polar m hm]
    exact inf_le_inf_right _ (sup_le_sup_right
      (sup_le_sup_left (Submodule.span_mono (quinticStaticQuarticRows_subset m)) _) _)
  · intro p hp
    refine ⟨?_,hp.2⟩
    have hU : Submodule.span ℂ (quinticU5Rows m) ≤
        (AllM.candidateIdeal m).restrictScalars ℂ := by
      apply Submodule.span_le.mpr
      rintro p ⟨q,hq,rfl⟩
      have hrow : MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈
          Submodule.span ℂ (finiteColorComponentRows m 5 (2 * m - 3) (fun _ => 2)) :=
        Submodule.subset_span ⟨q,hq.1,rfl⟩
      rw [← candidate_quintic_color_component_eq_finite_span m] at hrow
      exact hrow.1
    have hS : Submodule.span ℂ (quinticStaticRows m) ≤
        (AllM.candidateIdeal m).restrictScalars ℂ := by
      apply Submodule.span_le.mpr
      rintro p ⟨x,-,rfl⟩
      exact staticQuarticRow_mem_candidate m x
    have hJ : (quadraticCubicPolarIdeal m).restrictScalars ℂ ≤
        (AllM.candidateIdeal m).restrictScalars ℂ :=
      fun x hx => Cube.quadraticCubicPolarIdeal_le_candidate m hx
    exact (sup_le (sup_le hU hS) hJ) hp.1

end
#print axioms pbw_one_single
#print axioms quinticStaticQuarticRows_subset
#print axioms finrank_span_quinticStaticRows_le
#print axioms quinticU5_row_shape
#print axioms candidate_quintic_slice_eq_U5_staticRows_sup_polar
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
