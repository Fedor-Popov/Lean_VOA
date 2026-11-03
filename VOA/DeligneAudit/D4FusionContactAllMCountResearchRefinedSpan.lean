import VOA.DeligneAudit.D4FusionContactAllMCountResearchNearest

/-! # Exact leading and lower-energy spaces for the refined current family -/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

abbrev RefinedLowWord := {l : List (Vars m) // l.length = 4 ∧
  currentDegree l = b.lower.val+3*b.top.val-1 ∧
  currentEnergy l < b.lower.val^2+(b.top.val-1)^2+2*b.top.val^2}

def refinedLowSpan : Submodule ℂ (MvPolynomial (Vars m) ℂ) :=
  Submodule.span ℂ (Set.range fun l : RefinedLowWord b => polyWord l.val)

/-- The four actual modes are p,q-1,q,q. Colors remain arbitrary. -/
def refinedLeadingSpan : Submodule ℂ (MvPolynomial (Vars m) ℂ) :=
  Submodule.span ℂ (Set.range fun x : Fin 9 × Fin 9 × Fin 9 × Fin 9 =>
    modeX m x.1 b.lower.val * modeX m x.2.1 (b.top.val-1) *
      modeX m x.2.2.1 b.top.val * modeX m x.2.2.2 b.top.val)

abbrev RefinedSpace := refinedLeadingSpan b ⊔ refinedLowSpan b

theorem low_endpoint_middle_product_mem (i j : Fin 9) (z : MiddlePair b) :
    modeX m i (b.top.val-1) * modeX m j b.top.val *
      (MvPolynomial.X z.left * MvPolynomial.X z.right) ∈ refinedLowSpan b := by
  have htop := b.top.isLt
  have hlt := b.lt
  have hq : 0 < b.top.val := by omega
  have hpred : b.top.val-1 < m := by omega
  let l : List (Vars m) := [(i,⟨b.top.val-1,hpred⟩),(j,b.top),z.left,z.right]
  have hl : l.length = 4 ∧ currentDegree l = b.lower.val+3*b.top.val-1 ∧
      currentEnergy l < b.lower.val^2+(b.top.val-1)^2+2*b.top.val^2 := by
    refine ⟨rfl,?_,?_⟩
    · simp only [currentDegree,l,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have := z.mode_sum
      omega
    · simp only [currentEnergy,l,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have := middle_energy b z
      omega
  have hh := (Submodule.subset_span (R := ℂ)
    (s := Set.range fun w : RefinedLowWord b => polyWord w.val) ⟨⟨l,hl⟩,rfl⟩)
  simpa only [refinedLowSpan,l,polyWord,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,mul_one,mul_assoc,modeX,dif_pos hpred,dif_pos htop] using hh

theorem low_endpoint_middle_mem (i j : Fin 9) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ middleSpan b) :
    modeX m i (b.top.val-1) * modeX m j b.top.val * p ∈ refinedLowSpan b := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨z,rfl⟩ := hp
      exact low_endpoint_middle_product_mem b i j z
  | zero => simp only [mul_zero]; exact (refinedLowSpan b).zero_mem
  | add p q _ _ ihp ihq =>
      simpa only [mul_add] using (refinedLowSpan b).add_mem ihp ihq
  | smul a p _ ih =>
      simpa only [mul_smul_comm] using (refinedLowSpan b).smul_mem a ih

theorem leading_endpoint_nearest_product_mem (i j k l : Fin 9) :
    modeX m i b.lower.val * modeX m j b.top.val *
      (modeX m k b.top.val * modeX m l (b.top.val-1)) ∈ refinedLeadingSpan b := by
  have hh := (Submodule.subset_span (R := ℂ)
    (s := Set.range fun x : Fin 9 × Fin 9 × Fin 9 × Fin 9 =>
      modeX m x.1 b.lower.val * modeX m x.2.1 (b.top.val-1) *
        modeX m x.2.2.1 b.top.val * modeX m x.2.2.2 b.top.val) ⟨(i,l,j,k),rfl⟩)
  convert hh using 1; ring

theorem leading_endpoint_nearest_mem (i j : Fin 9) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ nearestTopSpan b) :
    modeX m i b.lower.val * modeX m j b.top.val * p ∈ refinedLeadingSpan b := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨⟨k,l⟩,rfl⟩ := hp
      exact leading_endpoint_nearest_product_mem b i j k l
  | zero => simp only [mul_zero]; exact (refinedLeadingSpan b).zero_mem
  | add p q _ _ ihp ihq =>
      simpa only [mul_add] using (refinedLeadingSpan b).add_mem ihp ihq
  | smul a p _ ih =>
      simpa only [mul_smul_comm] using (refinedLeadingSpan b).smul_mem a ih

/-- Literal endpoint modes have no high-mode or quotient assumption. -/
theorem h0Deriv_lower_mode (i : Fin 9) :
    g0Deriv m 0 (refinementMode b).val (modeX m i b.lower.val) =
      (h0Weight i : ℂ) • modeX m i (b.top.val-1) := by
  rw [h0Deriv_modeX]
  congr 2
  have := b.lt
  change b.top.val-b.lower.val-1+b.lower.val = b.top.val-1
  omega

theorem h0Deriv_top_mode_zero (ha : b.lower.val + 1 < b.top.val) (i : Fin 9) :
    g0Deriv m 0 (refinementMode b).val (modeX m i b.top.val) = 0 := by
  rw [h0Deriv_modeX]
  have hh : ¬ (refinementMode b).val+b.top.val < m := by
    have := b.last
    change ¬ b.top.val-b.lower.val-1+b.top.val < m
    omega
  simp only [modeX,dif_neg hh,smul_zero]

/-- Leibniz gives precisely a leading piece and a strict lower-energy piece. -/
theorem h0Deriv_polar_middle_mem (ha : b.lower.val + 1 < b.top.val)
    (i j : Fin 9) {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ middleSpan b) :
    g0Deriv m 0 (refinementMode b).val
      (modeX m i b.lower.val * modeX m j b.top.val * p) ∈ RefinedSpace b := by
  rw [(g0Deriv m 0 (refinementMode b).val).leibniz,
    (g0Deriv m 0 (refinementMode b).val).leibniz,
    h0Deriv_lower_mode,h0Deriv_top_mode_zero b ha]
  simp only [smul_eq_mul,mul_zero,zero_add]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (leading_endpoint_nearest_mem b i j
      (h0Deriv_middle_nearest b hp))
  · have hh := (refinedLowSpan b).smul_mem (h0Weight i : ℂ)
      (low_endpoint_middle_mem b i j hp)
    apply Submodule.mem_sup_right
    simpa only [mul_smul_comm,smul_mul_assoc,mul_assoc,mul_comm,mul_left_comm] using hh

end

#print axioms h0Deriv_polar_middle_mem

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
