import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleSourceGrades

/-! Source-power bounds for whole current words, before any projection. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

theorem monoMap_shift_graded (m : ℕ) (b : Bool) (k : ℕ) (w : Fin 9 → ℤ) (t : ℤ)
    {p : MonoRing ℂ m} {n : ℤ}
    (hp : (monoMap ℂ m (sourceColor b) p).IsWeightedHomogeneous (modeWeight m w t) n) :
    (monoMap ℂ m (sourceColor b) (monoShift ℂ m k p)).IsWeightedHomogeneous
      (modeWeight m w t) (n + t*k) := by
  have hr : ∀ i, coeff (1 : Fin 18) i = 0 ∨ w (target 1 i) = w i + 0 := by
    intro i
    rcases cartan_color_rule (1 : Fin 4) i with hz | ht
    · exact Or.inl hz
    · exact Or.inr (by change w (target (cartan 1) i) = w i + 0; rw [ht,add_zero])
  have hh := deriv_graded ℂ m w t 0 1 k hr hp
  change (deriv ℂ m (cartan 1) k (monoMap ℂ m (sourceColor b) p)).IsWeightedHomogeneous
    (modeWeight m w t) (n + 0 + t*k) at hh
  rw [cartan_mono ℂ m (1 : Fin 4) b k p] at hh
  have hn : (coeff 1 (sourceColor b) : ℂ) ≠ 0 := by
    exact_mod_cast source_cartan_nonzero b
  rw [← Int.cast_smul_eq_zsmul ℂ] at hh
  have hc := (Submodule.smul_mem_iff
    (MvPolynomial.weightedHomogeneousSubmodule ℂ (modeWeight m w t) (n + 0 + t*k)) hn).mp hh
  simpa only [add_zero] using hc

/-- Every arbitrary plain-shift word has its exact whole-source multidegree. -/
theorem shifted_seed_graded (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ)
    (w : Fin 9 → ℤ) (t : ℤ) :
    (monoMap ℂ m (sourceColor j.val.1) (shiftWord m modes (monoSeed m j))).IsWeightedHomogeneous
      (modeWeight m w t)
      ((j.val.2.1 : ℤ)*w (sourceColor j.val.1) + t*(j.val.2.2 + modes.sum)) := by
  induction modes with
  | nil =>
      simp only [shiftWord,List.sum_nil,monoSeed,monoMap_seed]
      exact color_seed_graded ℂ m w t _ _ _
  | cons k modes ih =>
      have hh := monoMap_shift_graded m j.val.1 k w t ih
      change (monoMap ℂ m (sourceColor j.val.1)
        (monoShift ℂ m k (shiftWord m modes (monoSeed m j)))).IsWeightedHomogeneous _ _
      convert hh using 1
      simp only [List.sum_cons,Nat.cast_add]
      ring

def sourceWord (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ) (l : List (Fin 18 × ℕ)) : Ring ℂ m :=
  wordOp (representation ℂ m) l
    (monoMap ℂ m (sourceColor j.val.1) (shiftWord m modes (monoSeed m j)))

theorem sourceWord_pbw (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ) (l : List (Fin 18 × ℕ)) :
    (sourceWord m j modes l).IsWeightedHomogeneous (modeWeight m (fun _ => 1) 0) j.val.2.1 := by
  apply word_pbw_graded
  simpa only [zero_mul,add_zero,mul_one] using shifted_seed_graded m j modes (fun _ => 1) 0

theorem sourceWord_current (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ)
    (l : List (Fin 18 × ℕ)) :
    (sourceWord m j modes l).IsWeightedHomogeneous (modeWeight m (fun _ => 0) 1)
      ((j.val.2.2 + modes.sum + (l.map Prod.snd).sum : ℕ) : ℤ) := by
  have hp := shifted_seed_graded m j modes (fun _ => 0) 1
  simp only [mul_zero,one_mul,zero_add] at hp
  have hh := word_current_graded ℂ m l hp
  simpa only [Nat.cast_add] using hh

theorem category_zero_iff : ∀ a : Fin 18, category a = 0 ↔ 10 ≤ a.val := by decide +kernel

theorem c_sourceWord_degree (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = true)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 0) :
    (sourceWord m j modes l).IsWeightedHomogeneous (modeWeight m cWeight 0)
      ((j.val.2.1 : ℤ) - l.length) := by
  have hp := shifted_seed_graded m j modes cWeight 0
  have hcolor : cWeight (sourceColor j.val.1) = 1 := by rw [hj]; rfl
  simp only [hcolor,mul_one,zero_mul,add_zero] at hp
  have hh := word_graded ℂ m cWeight 0 (fun _ => -1) l (fun x hx i => ?_) hp
  · convert hh using 1
    simp [wordGrade,sub_eq_add_neg]
  · rcases contact_c_rule x.1 i ((category_zero_iff x.1).mp (hl x hx)) with hz | hw
    · exact Or.inl hz
    · exact Or.inr (by simpa only [sub_eq_add_neg] using hw)

/-- More contacts than original C factors kill the entire source. -/
theorem c_sourceWord_too_many_contacts (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = true)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 0)
    (hlen : j.val.2.1 < l.length) : sourceWord m j modes l = 0 := by
  apply graded_negative_zero (fun x => ?_) (c_sourceWord_degree m j hj modes l hl)
  · exact sub_neg.mpr (by exact_mod_cast hlen)
  · change 0 ≤ cWeight x.1 + 0*x.2.val
    simpa only [zero_mul,add_zero] using cWeight_nonneg x.1

theorem u_sourceWord_axis_degree (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = false)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 1) (d : Fin 3) :
    (sourceWord m j modes l).IsWeightedHomogeneous (modeWeight m (bitWeight d) 0)
      (wordGrade (axisIncrement d) 0 l) := by
  have hp := shifted_seed_graded m j modes (bitWeight d) 0
  have hcolor : bitWeight d (sourceColor j.val.1) = 0 := by
    rw [hj]; fin_cases d <;> rfl
  simp only [hcolor,mul_zero,zero_mul,add_zero] at hp
  have hh := word_graded ℂ m (bitWeight d) 0 (axisIncrement d) l
    (fun x hx i => negative_bit_rule x.1 d i ((category_one_iff x.1).mp (hl x hx))) hp
  simpa only [zero_add] using hh

/-- Each negative-root direction is individually bounded by the original U power. -/
theorem u_sourceWord_too_many_axis (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = false)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 1) (d : Fin 3)
    (hlen : (j.val.2.1 : ℤ) < wordGrade (axisIncrement d) 0 l) : sourceWord m j modes l = 0 := by
  by_contra hne
  have hh := graded_compare (fun x => ?_)
    (u_sourceWord_axis_degree m j hj modes l hl d) (sourceWord_pbw m j modes l) hne
  · omega
  · change bitWeight d x.1 + 0*x.2.val ≤ 1 + 0*x.2.val
    simpa only [zero_mul,add_zero] using bitWeight_le_one d x.1

/-- A C source contributes to C degree zero only after exactly r contacts. -/
theorem c_sourceWord_component_zero (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = true)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 0)
    (hlen : l.length ≠ j.val.2.1) :
    MvPolynomial.weightedHomogeneousComponent (modeWeight m cWeight 0) 0
      (sourceWord m j modes l) = 0 := by
  apply (c_sourceWord_degree m j hj modes l hl).weightedHomogeneousComponent_ne
  intro he
  have hh : (j.val.2.1 : ℤ) = l.length := by omega
  exact hlen (by exact_mod_cast hh.symm)

/-- Admissible degree-one seed coefficients already vanish by truncation. -/
theorem monoSeed_linear_zero (m : ℕ) (j : AllM.SeedIndex m) (hr : j.val.2.1 = 1) :
    monoSeed m j = 0 := by
  have ht := j.property.2
  have hm : m ≤ AllM.seedThreshold m j.val.1 := by
    unfold AllM.seedThreshold
    split_ifs <;> omega
  have hs : ¬ j.val.2.2 < m := by rw [hr] at ht; omega
  simp only [monoSeed,hr,pow_one,monoCurrent,PowerSeries.coeff_mk,monoMode,dif_neg hs]

end
#print axioms monoSeed_linear_zero
#print axioms c_sourceWord_component_zero
#print axioms sourceWord_pbw
#print axioms sourceWord_current
#print axioms c_sourceWord_too_many_contacts
#print axioms u_sourceWord_too_many_axis
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
