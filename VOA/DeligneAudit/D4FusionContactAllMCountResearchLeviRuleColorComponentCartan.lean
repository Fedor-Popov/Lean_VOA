import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleColorComponent

/-! The numerical block's physical Cartan weights are derived from the
original D4 Cartan-arrow table, rather than assumed as a coordinate match. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- The three physical Cartan directions, in cube-bit order. -/
def physicalCartan : Fin 3 → Fin 4 := ![3,2,0]

def physicalCartanG (d : Fin 3) : Fin 10 :=
  ⟨(physicalCartan d).val,by have hh := (physicalCartan d).isLt; omega⟩

def physicalColorWeight (d : Fin 3) (i : Fin 9) : ℤ := coeff (cartan (physicalCartan d)) i

/-- Exact original Cartan table: A degree minus twice the corresponding bit degree. -/
theorem physicalColorWeight_table : ∀ (d : Fin 3) (i : Fin 9),
    physicalColorWeight d i = 1-cWeight i-2*bitWeight d i := by decide +kernel

theorem physicalColorWeight_a_table : ∀ (d : Fin 3) (i : Fin 8),
    physicalColorWeight d i.castSucc = 1-2*bitWeight d i.castSucc := by decide +kernel

/-- This weight is the action of the original Cartan derivation on every mode. -/
theorem actual_physicalCartan_mode (m : ℕ) (d : Fin 3) (i : Fin 9) (s : ℕ) :
    g0Deriv m (physicalCartanG d) 0 (mode ℂ m i s) =
      physicalColorWeight d i • mode ℂ m i s := by
  rw [← deriv_g0]
  have he : Fin.castAdd 8 (physicalCartanG d) = cartan (physicalCartan d) := Fin.ext rfl
  rw [he,deriv_mode,zero_add]
  change coeff (cartan (physicalCartan d)) i •
      mode ℂ m (target (cartan (physicalCartan d)) i) s =
    coeff (cartan (physicalCartan d)) i • mode ℂ m i s
  rcases cartan_color_rule (physicalCartan d) i with hz | ht
  · simp only [hz,zero_zsmul]
  · rw [ht]

theorem actual_physicalCartan_a_mode (m : ℕ) (d : Fin 3) (i : Fin 8) (s : ℕ) :
    g0Deriv m (physicalCartanG d) 0 (mode ℂ m i.castSucc s) =
      (1-2*bitWeight d i.castSucc) • mode ℂ m i.castSucc s := by
  rw [actual_physicalCartan_mode,physicalColorWeight_a_table]

/-- The same exact relation holds on every monomial, including C factors. -/
theorem physical_monomial_weight (m : ℕ) (d : Fin 3) (e : Fin 9 × Fin m →₀ ℕ) :
    Finsupp.weight (modeWeight m (physicalColorWeight d) 0) e =
      Finsupp.weight (modeWeight m (fun _ => 1) 0) e-
      Finsupp.weight (modeWeight m cWeight 0) e-
      2*Finsupp.weight (modeWeight m (bitWeight d) 0) e := by
  have hx : ∀ x : Fin 9 × Fin m,
      (e x : ℤ)*physicalColorWeight d x.1 =
        (e x : ℤ)-(e x : ℤ)*cWeight x.1-2*((e x : ℤ)*bitWeight d x.1) := by
    intro x
    rw [physicalColorWeight_table]
    ring
  simp only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,
    modeWeight,zero_mul,add_zero,mul_one]
  simp_rw [hx]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]

/-- On pure-A quintics, physical weights(1,1,1) mean exactly bit degrees(2,2,2). -/
theorem quintic_bit_physical_iff (m : ℕ) (p : Ring ℂ m)
    (hp : p.IsWeightedHomogeneous (modeWeight m (fun _ => 1) 0) 5)
    (hc : p.IsWeightedHomogeneous (modeWeight m cWeight 0) 0) :
    (∀ d : Fin 3, p.IsWeightedHomogeneous (modeWeight m (bitWeight d) 0) 2) ↔
      ∀ d : Fin 3, p.IsWeightedHomogeneous (modeWeight m (physicalColorWeight d) 0) 1 := by
  constructor
  · intro hb d e he
    rw [physical_monomial_weight,hp he,hc he,hb d he]
    norm_num
  · intro hphys d e he
    have hh := physical_monomial_weight m d e
    rw [hp he,hc he,hphys d he] at hh
    omega

/-- The six-coordinate slice is precisely the original physical-weight quintic block. -/
theorem quintic_color_component_iff (m : ℕ) (p : Ring ℂ m) :
    p.IsWeightedHomogeneous (colorComponentWeight m) (quinticColorDegree m) ↔
      p.IsWeightedHomogeneous (modeWeight m (fun _ => 1) 0) 5 ∧
      p.IsWeightedHomogeneous (modeWeight m (fun _ => 0) 1) ((2*m-3 : ℕ) : ℤ) ∧
      p.IsWeightedHomogeneous (modeWeight m cWeight 0) 0 ∧
      ∀ d : Fin 3, p.IsWeightedHomogeneous (modeWeight m (physicalColorWeight d) 0) 1 := by
  constructor
  · intro h
    have hs := (weighted_pi_iff _ _ _).mp h
    have hp : p.IsWeightedHomogeneous (modeWeight m (fun _ => 1) 0) 5 := hs 0
    have hc : p.IsWeightedHomogeneous (modeWeight m cWeight 0) 0 := hs 2
    refine ⟨hp,hs 1,hc,(quintic_bit_physical_iff m p hp hc).mp ?_⟩
    intro d
    fin_cases d
    · exact hs 3
    · exact hs 4
    · exact hs 5
  · rintro ⟨hp,ht,hc,hphys⟩
    have hb := (quintic_bit_physical_iff m p hp hc).mpr hphys
    apply (weighted_pi_iff _ _ _).mpr
    intro j
    fin_cases j
    · exact hp
    · exact ht
    · exact hc
    · exact hb 0
    · exact hb 1
    · exact hb 2

end
#print axioms physicalColorWeight_table
#print axioms actual_physicalCartan_a_mode
#print axioms physical_monomial_weight
#print axioms quintic_color_component_iff
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
