import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterContactShapes
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterQuinticBounds
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleColorComponentFinite

/-! original C-contact coverage in the quintic slice. For m >= 2, every
original C-source row of the exact finite span of the candidate ideal's
PBW-5 / current-(2m-3) / C-degree-0 / bit-(2,2,2) component lies in the
literal quadratic/cubic polar ideal J. The proof reads the actual matching
budgets, prunes Euler shifts, identifies the outer word with contacts, and
applies the three proved source shapes. The U-source rows, reduced
completion and the sharp count are separate. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
open Cube (quadraticCubicPolarIdeal)
open Cube.CenterStaticPolar (QuinticShape QuarticShape bitCount)
noncomputable section

theorem bitWeight_castSucc : ∀ (d : Fin 3) (e : Fin 8),
    bitWeight d e.castSucc = (((cubeIndex e).val / 2 ^ d.val % 2 : ℕ) : ℤ) := by decide

theorem bitWeight_nonneg : ∀ (d : Fin 3) (i : Fin 9), 0 ≤ bitWeight d i := by decide

/-- The letter of a contact operator; inverse to `contactOp` on contacts. -/
def toContact (x : Fin 18 × ℕ) : Fin 8 × ℕ := (⟨x.1.val - 10,by omega⟩,x.2)

theorem contactOp_toContact (x : Fin 18 × ℕ) (hx : category x.1 = 0) :
    contactOp (toContact x) = x := by
  have h := (category_zero_iff x.1).mp hx
  apply Prod.ext
  · apply Fin.ext
    simp only [contactOp,toContact,Fin.natAdd_mk]
    omega
  · rfl

theorem outer_eq_contacts (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 0) :
    (l.map toContact).map contactOp = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left (fun x hx => contactOp_toContact x (hl x hx))

theorem contact_bit_degree (l : List (Fin 8 × ℕ)) (d : Fin 3) :
    wordGrade (contactBitIncrement d) 0 (l.map contactOp) =
      (bitCount (contactWord l) d.val : ℤ) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hx : contactBitIncrement d (contactOp x).1 =
          (((cubeIndex x.1).val / 2 ^ d.val % 2 : ℕ) : ℤ) := by
        change bitWeight d (target (Fin.natAdd 10 x.1) 8) = _
        rw [actual_contact_target,bitWeight_castSucc]
      have hw : wordGrade (contactBitIncrement d) 0 ((x :: l).map contactOp) =
          contactBitIncrement d (contactOp x).1 + 0 * (contactOp x).2 +
            wordGrade (contactBitIncrement d) 0 (l.map contactOp) := by
        simp only [wordGrade,List.map_cons,List.sum_cons]
      rw [hw,hx,ih,zero_mul,add_zero]
      simp only [contactWord,bitCount,List.map_cons,List.sum_cons,Nat.cast_add]

theorem weight_coord {m : ℕ} {ι : Type*} (w : Fin 9 × Fin m → ι → ℤ)
    (e : (Fin 9 × Fin m) →₀ ℕ) (j : ι) :
    Finsupp.weight w e j = Finsupp.weight (fun x => w x j) e := by
  simp only [Finsupp.weight_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply]

/-- A multiplier's bit weight is nonnegative and at most its PBW degree. -/
theorem bit_weight_bounds (m : ℕ) (e : (Fin 9 × Fin m) →₀ ℕ) (d : Fin 3) :
    0 ≤ Finsupp.weight (modeWeight m (bitWeight d) 0) e ∧
      Finsupp.weight (modeWeight m (bitWeight d) 0) e ≤
        Finsupp.weight (modeWeight m (fun _ => 1) 0) e := by
  simp only [Finsupp.weight_apply,Finsupp.sum,modeWeight,zero_mul,add_zero]
  constructor
  · exact Finset.sum_nonneg (fun x _ => mul_nonneg (Nat.cast_nonneg _) (bitWeight_nonneg d x.1))
  · exact Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (bitWeight_le_one d x.1) (Nat.cast_nonneg _))

theorem list_nonzero_sum_le_one (L : List ℕ) (h0 : ∀ k ∈ L, k ≠ 0) (h : L.sum ≤ 1) :
    L = [] ∨ L = [1] := by
  match L, h0, h with
  | [], _, _ => exact Or.inl rfl
  | [a], h0, h =>
      have ha := h0 a List.mem_cons_self
      simp only [List.sum_cons,List.sum_nil] at h
      exact Or.inr (by rw [show a = 1 by omega])
  | a :: b :: L, h0, h =>
      have ha := h0 a List.mem_cons_self
      have hb := h0 b (List.mem_cons_of_mem a List.mem_cons_self)
      simp only [List.sum_cons] at h
      omega

theorem sum_filter_ne_zero (L : List ℕ) : (L.filter (· ≠ 0)).sum = L.sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      by_cases ha : a = 0
      · subst ha
        simpa [List.filter_cons] using ih
      · simpa [List.filter_cons,ha] using ih

theorem all_zero_of_sum_zero (l : List (Fin 8 × ℕ)) (h : (l.map Prod.snd).sum = 0) :
    ∀ x ∈ l, x.2 = 0 := by
  intro x hx
  have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := Prod.snd) hx)
  omega

/-- MAIN: every original C-source row of the quintic slice lies in J (m >= 2). -/
theorem center_row_mem_polarIdeal (m : ℕ) (hm : 2 ≤ m)
    (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ))
    (hq : q ∈ boundedColorComponentPairs m 5 (2 * m - 3) (fun _ => 2))
    (hb : q.1.seed.val.1 = true) :
    MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈ quadraticCubicPolarIdeal m := by
  obtain ⟨⟨-,-,hmatch⟩,hcolor⟩ := hq
  obtain ⟨i,e⟩ := q
  simp only at hb hmatch hcolor ⊢
  by_cases hne : MvPolynomial.monomial e (1 : ℂ) * orbitSourcePoly m i = 0
  · rw [hne]
    exact zero_mem _
  apply Ideal.mul_mem_left
  -- the actual matching budgets
  have hr := matching_center_quintic_power_cases m hm i e hb hmatch
  have hlen := (matching_c_contacts_exact m 5 (2 * m - 3) i e hb hmatch hne).1
  have hbud := matching_center_quintic_mode_budget m hm i e hb hmatch
  have hth : 2 * m < i.seed.val.2.1 + i.seed.val.2.2 := by
    simpa only [AllM.seedThreshold,hb,if_true] using i.seed.property.2
  have h0 := congrFun hmatch 0
  have h1 := congrFun hmatch 1
  change Finsupp.weight (componentWeight m) e 0 + (i.seed.val.2.1 : ℤ) = 5 at h0
  change Finsupp.weight (componentWeight m) e 1 +
    ((i.seed.val.2.2 + i.shifts.sum + (i.outer.map Prod.snd).sum : ℕ) : ℤ) =
      ((2 * m - 3 : ℕ) : ℤ) at h1
  have hw1 := component_monomial_weight_nonneg m e 1
  -- the outer word consists of contacts
  have hcat : ∀ x ∈ i.outer, category x.1 = 0 := by
    intro x hx
    simpa only [branchCategory,hb,if_true] using i.branch x hx
  set l := i.outer.map toContact with hl
  have houter : i.outer = l.map contactOp := (outer_eq_contacts i.outer hcat).symm
  have hlenl : l.length = i.seed.val.2.1 := by rw [hl,List.length_map,hlen]
  have hmodes : (l.map Prod.snd).sum = (i.outer.map Prod.snd).sum := by
    rw [hl,List.map_map]
    rfl
  -- exact bit counts of the contact word
  have hbits : ∀ d : Fin 3, Finsupp.weight (modeWeight m (bitWeight d) 0) e +
      (bitCount (contactWord l) d.val : ℤ) = 2 := by
    intro d
    have hc := congrFun hcolor (Fin.natAdd 3 d)
    rw [Pi.add_apply,weight_coord] at hc
    have hsrc : orbitSourceColorDegree m i (Fin.natAdd 3 d) = orbitSourceBitDegree m i d := by
      fin_cases d <;> rfl
    have hcw : (fun x => colorComponentWeight m x (Fin.natAdd 3 d)) =
        modeWeight m (bitWeight d) 0 := by
      funext x
      fin_cases d <;> rfl
    have htg : pureAColorTargetDegree 5 (2 * m - 3) (fun _ => 2) (Fin.natAdd 3 d) = 2 := by
      fin_cases d <;> rfl
    rw [hsrc,hcw,htg,orbitSourceBitDegree,if_pos hb,houter,contact_bit_degree] at hc
    exact hc
  have hpbw : Finsupp.weight (modeWeight m (fun _ => 1) 0) e =
      Finsupp.weight (componentWeight m) e 0 := by
    rw [weight_coord]
    rfl
  -- the source word, up to a nonzero Euler scalar
  obtain ⟨z,hz⟩ := shiftWord_seed_prune_zero m i.seed i.shifts
  have hsrc : orbitSourcePoly m i = z • wordOp (representation ℂ m) (l.map contactOp)
      (monoMap ℂ m 8 (shiftWord m (i.shifts.filter (· ≠ 0)) (monoSeed m i.seed))) := by
    rw [orbitSourcePoly,sourceWord,hz,map_smul,← wordOp_smul,← houter]
    simp only [sourceColor,hb,if_true]
  rw [hsrc]
  apply Submodule.smul_of_tower_mem
  have hF := list_nonzero_sum_le_one (i.shifts.filter (· ≠ 0))
    (fun k hk => by simpa using (List.mem_filter.mp hk).2)
    (by rw [sum_filter_ne_zero]; omega)
  rcases hr with hr | hr
  · -- r = 4: static seed, static contacts, one A multiplier
    have hst := matching_center_quartic_static_budget m hm i e hb hr hmatch
    have hF0 : i.shifts.filter (· ≠ 0) = [] := by
      rcases hF with h | h
      · exact h
      · have := sum_filter_ne_zero i.shifts
        rw [h] at this
        simp at this
        omega
    rw [hF0]
    change wordOp (representation ℂ m) (l.map contactOp)
      (monoMap ℂ m 8
        (PowerSeries.coeff i.seed.val.2.2 (monoCurrent ℂ m ^ i.seed.val.2.1))) ∈ _
    rw [monoMap_seed,hst.1,hr]
    apply static_contacts_mem m 4 l (all_zero_of_sum_zero l (by rw [hmodes]; exact hst.2.2))
      (by rw [hlenl,hr])
    refine Or.inr ⟨rfl,?_,?_⟩
    · simp only [contactWord,List.length_map]
      rw [hlenl,hr]
    · have hb0 := hbits 0
      have hb1 := hbits 1
      have hb2 := hbits 2
      have k0 := bit_weight_bounds m e 0
      have k1 := bit_weight_bounds m e 1
      have k2 := bit_weight_bounds m e 2
      rw [hr] at h0
      simp only [Fin.val_zero,Fin.val_one,Fin.val_two] at hb0 hb1 hb2
      refine ⟨by omega,by omega,by omega⟩
  · -- r = 5: constant multiplier
    have he0 := matching_fifth_source_multiplier_zero m (2 * m - 3) i e hr hmatch
    subst he0
    have hq5 : QuinticShape (contactWord l) := by
      have hb0 := hbits 0
      have hb1 := hbits 1
      have hb2 := hbits 2
      simp only [map_zero,zero_add,Fin.val_zero,Fin.val_one,Fin.val_two] at hb0 hb1 hb2
      refine ⟨?_,by omega,by omega,by omega⟩
      simp only [contactWord,List.length_map]
      rw [hlenl,hr]
    simp only [map_zero,Pi.zero_apply,zero_add] at h1
    rcases hF with hF | hF
    · rw [hF]
      change wordOp (representation ℂ m) (l.map contactOp)
        (monoMap ℂ m 8
          (PowerSeries.coeff i.seed.val.2.2 (monoCurrent ℂ m ^ i.seed.val.2.1))) ∈ _
      rw [monoMap_seed,hr]
      by_cases hz0 : (l.map Prod.snd).sum = 0
      · -- (S0): s = T
        have hs : i.seed.val.2.2 = 2 * m - 3 := by
          have := sum_filter_ne_zero i.shifts
          rw [hF] at this
          simp at this
          omega
        rw [hs]
        exact static_contacts_mem m 5 l (all_zero_of_sum_zero l hz0) (by rw [hlenl,hr])
          (Or.inl ⟨rfl,hq5⟩)
      · -- (SD): one mode-one contact, s = T - 1
        have hs : i.seed.val.2.2 = 2 * m - 3 - 1 := by
          have := sum_filter_ne_zero i.shifts
          rw [hF] at this
          simp at this
          omega
        rw [hs]
        obtain ⟨x,hx,hx0⟩ : ∃ x ∈ l, x.2 ≠ 0 := by
          by_contra hcon
          apply hz0
          apply List.sum_eq_zero
          intro k hk
          obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hk
          by_contra hy0
          exact hcon ⟨y,hy,hy0⟩
        have hperm := List.perm_cons_erase hx
        have hsum := (hperm.map Prod.snd).sum_eq
        simp only [List.map_cons,List.sum_cons] at hsum
        have hx1 : x.2 = 1 := by omega
        have hrest : ∀ y ∈ l.erase x, y.2 = 0 := all_zero_of_sum_zero _ (by omega)
        have h := wordOp_contacts_center_pow m 5 (2 * m - 3 - 1) l 1 (contactKilled_one m)
        rw [mul_one] at h
        rw [h,hlenl,hr,Nat.sub_self,pow_zero,one_mul,mul_one,map_nsmul,
          contactProduct_perm m hperm]
        exact nsmul_mem (single_contact_shift_mem m hm x hx1 _ hrest
          (quinticShape_perm (contactWord_perm hperm) hq5)) _
    · -- (SC): one mode-one seed shift, s = T - 1, static contacts
      have hshift : i.shifts.sum = 1 := by
        have := sum_filter_ne_zero i.shifts
        rw [hF] at this
        simpa using this.symm
      have hz0 : (l.map Prod.snd).sum = 0 := by omega
      have hs : i.seed.val.2.2 = 2 * m - 3 - 1 := by omega
      rw [hF]
      change wordOp (representation ℂ m) (l.map contactOp)
        (monoMap ℂ m 8 (monoShift ℂ m 1
          (PowerSeries.coeff i.seed.val.2.2 (monoCurrent ℂ m ^ i.seed.val.2.1)))) ∈ _
      rw [hs,hr]
      exact shift_seed_contacts_mem m hm l (all_zero_of_sum_zero l hz0) (by rw [hlenl,hr]) hq5

/-- The original U-source rows of the quintic slice. -/
def quinticURows (m : ℕ) : Set (Ring ℂ m) :=
  (fun q => MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1) ''
    {q | q ∈ boundedColorComponentPairs m 5 (2 * m - 3) (fun _ => 2) ∧ q.1.seed.val.1 = false}

/-- The C branch is redundant modulo J: the candidate quintic slice is the
slice of the span of the U-source rows together with J (m >= 2). -/
theorem candidate_quintic_slice_eq_U_sup_polar (m : ℕ) (hm : 2 ≤ m) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) =
    (Submodule.span ℂ (quinticURows m) ⊔ (quadraticCubicPolarIdeal m).restrictScalars ℂ) ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) := by
  have hslice := candidate_quintic_color_component_eq_finite_span m
  apply le_antisymm
  · intro p hp
    refine ⟨?_,hp.2⟩
    rw [hslice] at hp
    refine (Submodule.span_le.mpr ?_) hp
    rintro p ⟨q,hq,rfl⟩
    cases hb : q.1.seed.val.1 with
    | false => exact Submodule.mem_sup_left (Submodule.subset_span ⟨q,⟨hq,hb⟩,rfl⟩)
    | true => exact Submodule.mem_sup_right (center_row_mem_polarIdeal m hm q hq hb)
  · intro p hp
    refine ⟨?_,hp.2⟩
    have hU : Submodule.span ℂ (quinticURows m) ≤
        (AllM.candidateIdeal m).restrictScalars ℂ := by
      apply Submodule.span_le.mpr
      rintro p ⟨q,hq,rfl⟩
      have hrow : MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈
          Submodule.span ℂ (finiteColorComponentRows m 5 (2 * m - 3) (fun _ => 2)) :=
        Submodule.subset_span ⟨q,hq.1,rfl⟩
      rw [← hslice] at hrow
      exact hrow.1
    have hJ : (quadraticCubicPolarIdeal m).restrictScalars ℂ ≤
        (AllM.candidateIdeal m).restrictScalars ℂ :=
      fun x hx => Cube.quadraticCubicPolarIdeal_le_candidate m hx
    exact (sup_le hU hJ) hp.1

end
#print axioms center_row_mem_polarIdeal
#print axioms candidate_quintic_slice_eq_U_sup_polar
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
