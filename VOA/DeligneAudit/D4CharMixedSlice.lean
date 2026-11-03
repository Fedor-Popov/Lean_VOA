import VOA.DeligneAudit.D4CharMixedWeight

/-! Finite homogeneous slices of the four-degree mixed GT sum, with integer boundaries. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtMixedFiveRow_sum (a b c d : ℤ) :
    (∑ i, gtMixedFiveRow a b c d i) = a + b - c - d := by
  simp [gtMixedFiveRow, Fin.sum_univ_succ]
  ring

theorem gtMixedWeight_shape (q : R) (h : PochhammerUnits q) (r : ℕ) (s t v : ℤ)
    (lam : Fin 5 → ℤ) (hn : gtMixedWeight q h r t v lam ≠ 0)
    (hd : (∑ i, lam i) = r + s - t - v) :
    (lam 1).toNat ≤ min r s.toNat ∧ (-lam 3).toNat ≤ min t.toNat v.toNat ∧
      lam = gtMixedFiveRow (r + s.toNat - (lam 1).toNat : ℕ) (lam 1).toNat
        (t.toNat + v.toNat - (-lam 3).toNat : ℕ) (-lam 3).toNat := by
  have he := gtMixedWeight_sum q h r t v lam hn
  have hp := gtMixedWeight_nonneg q h r s t v lam hn hd
  obtain ⟨hb, hbr, hra, hz, h₀, h₁, h₂, h₃, ht⟩ :=
    gtMixedWeight_support q h r t v lam hn
  refine ⟨by omega, by omega, ?_⟩
  ext i
  fin_cases i
  · change lam 0 = (r + s.toNat - (lam 1).toNat : ℕ)
    omega
  · change lam 1 = ((lam 1).toNat : ℤ)
    omega
  · change lam 2 = 0
    exact hz
  · change lam 3 = -((-lam 3).toNat : ℤ)
    omega
  · change lam 4 = -(t.toNat + v.toNat - (-lam 3).toNat : ℕ)
    omega

/-- A finite row container; the coefficient function imposes all degree conditions. -/
def gtMixedSliceRows (r : ℕ) (s t v : ℤ) : Finset (Fin 5 → ℤ) :=
  ((Finset.range (min r s.toNat + 1)).product
    (Finset.range (min t.toNat v.toNat + 1))).image fun p =>
      gtMixedFiveRow (r + s.toNat - p.1 : ℕ) p.1
        (t.toNat + v.toNat - p.2 : ℕ) p.2

/-- The mixed coefficient as a finite free linear combination of GL_5 rows. -/
def gtMixedSlice (q : R) (h : PochhammerUnits q) (r : ℕ) (s t v : ℤ) :
    (Fin 5 → ℤ) →₀ R :=
  Finsupp.onFinset (gtMixedSliceRows r s t v)
    (fun lam => if (∑ i, lam i) = r + s - t - v then gtMixedWeight q h r t v lam else 0)
    (by
      intro lam hn
      dsimp only at hn
      split_ifs at hn with hd
      · obtain ⟨hb, hd', he⟩ := gtMixedWeight_shape q h r s t v lam hn hd
        apply Finset.mem_image.mpr
        exact ⟨⟨(lam 1).toNat, (-lam 3).toNat⟩,
          Finset.mem_product.mpr ⟨by simpa using hb, by simpa using hd'⟩, he.symm⟩
      · exact (hn rfl).elim)

@[simp] theorem gtMixedSlice_apply (q : R) (h : PochhammerUnits q) (r : ℕ)
    (s t v : ℤ) (lam : Fin 5 → ℤ) :
    gtMixedSlice q h r s t v lam =
      if (∑ i, lam i) = r + s - t - v then gtMixedWeight q h r t v lam else 0 := rfl

theorem gtMixedSlice_mem_support (q : R) (h : PochhammerUnits q) (r : ℕ)
    (s t v : ℤ) (lam : Fin 5 → ℤ) :
    lam ∈ (gtMixedSlice q h r s t v).support ↔
      (∑ i, lam i) = r + s - t - v ∧ gtMixedWeight q h r t v lam ≠ 0 := by
  rw [Finsupp.mem_support_iff, gtMixedSlice_apply]
  split_ifs <;> simp_all

theorem gtMixedSlice_dominant (q : R) (h : PochhammerUnits q) (r : ℕ)
    (s t v : ℤ) (lam : Fin 5 → ℤ) (hm : lam ∈ (gtMixedSlice q h r s t v).support) :
    Antitone lam :=
  gtMixedWeight_dominant q h r t v lam ((gtMixedSlice_mem_support q h r s t v lam).mp hm).2

/-- All negative series degrees vanish, without truncating any valid row. -/
theorem gtMixedSlice_zero (q : R) (h : PochhammerUnits q) (r : ℕ) (s t v : ℤ)
    (hn : ¬(0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ v)) : gtMixedSlice q h r s t v = 0 := by
  ext lam
  rw [Finsupp.zero_apply, gtMixedSlice_apply]
  split_ifs with hd
  · by_contra he
    exact hn (gtMixedWeight_nonneg q h r s t v lam he hd)
  · rfl

theorem gtMixedSlice_nat_sub (q : R) (h : PochhammerUnits q)
    (r s t v i j k : ℕ) :
    gtMixedSlice q h r ((s : ℤ) - i) ((t : ℤ) - j) ((v : ℤ) - k) =
      if i ≤ s ∧ j ≤ t ∧ k ≤ v then
        gtMixedSlice q h r (s - i : ℕ) (t - j : ℕ) (v - k : ℕ) else 0 := by
  split_ifs with hd
  · rw [Int.natCast_sub hd.1, Int.natCast_sub hd.2.1, Int.natCast_sub hd.2.2]
  · exact gtMixedSlice_zero q h r _ _ _ (by omega)

theorem gtMixedFiveRow_parts_injective (a c : ℕ) :
    Function.Injective (fun p : ℕ × ℕ =>
      gtMixedFiveRow (a - p.1 : ℕ) p.1 (c - p.2 : ℕ) p.2) := by
  intro p p' he
  have h₁ := congrFun he 1
  have h₃ := congrFun he 3
  change (p.1 : ℤ) = p'.1 at h₁
  change -(p.2 : ℤ) = -p'.2 at h₃
  apply Prod.ext <;> omega

theorem gtTwoWeight_nat (q : R) (h : PochhammerUnits q) (r s b : ℕ)
    (hb : b ≤ min r s) :
    gtTwoWeight q h r (r + s - b : ℕ) b = gtTwoQCoefficient q h r s b := by
  have he : ((r + s - b : ℕ) : ℤ) - r = ((s - b : ℕ) : ℤ) := by omega
  have hr : ((r - b : ℕ) : ℤ) = (r : ℤ) - b := by omega
  simp only [gtTwoWeight, gtTwoQCoefficient, he, hr]
  ring

theorem gtMixedWeight_row (q : R) (h : PochhammerUnits q) (r s t v b d : ℕ)
    (hb : b ≤ min r s) (hd : d ≤ min t v) :
    gtMixedWeight q h r t v
      (gtMixedFiveRow (r + s - b : ℕ) b (t + v - d : ℕ) d) =
        gtTwoQCoefficient q h r s b * gtTwoQCoefficient q h t v d := by
  have he : ((t + v - d : ℕ) : ℤ) + d = (t : ℤ) + v := by omega
  change gtTwoWeight q h r (r + s - b : ℕ) b *
    (if (0 : ℤ) = 0 then gtTwoCoeff q h t v (-(-(t + v - d : ℕ) : ℤ))
      (-(-(d : ℤ))) else 0) = _
  simp only [neg_neg, ↓reduceIte, gtTwoCoeff, he, gtTwoWeight_nat q h r s b hb,
    gtTwoWeight_nat q h t v d hd]

/-- Evaluating the finite slice recovers the original mixed-Cauchy coefficient exactly. -/
theorem gtMixedSlice_eval (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) :
    Finsupp.linearCombination R (gtEval q u 5) (gtMixedSlice q h r s t v) =
      gtMixedFiveCoeff q h u r s t v := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    _ = ∑ lam ∈ gtMixedSliceRows r s t v,
        gtMixedSlice q h r s t v lam • gtEval q u 5 lam := by
      apply Finset.sum_subset Finsupp.support_onFinset_subset
      intro lam _ hn
      change lam ∉ (gtMixedSlice q h r s t v).support at hn
      rw [Finsupp.notMem_support_iff.mp hn, zero_smul]
    _ = _ := by
      rw [gtMixedSliceRows]
      simp only [Int.toNat_natCast]
      rw [Finset.sum_image (fun _ _ _ _ he => gtMixedFiveRow_parts_injective _ _ he)]
      simp only [Finset.product_eq_sprod, Finset.sum_product]
      rw [gtMixedFiveCoeff]
      apply Finset.sum_congr rfl
      intro b hb
      have hb : b ≤ min r s := by simpa using hb
      apply Finset.sum_congr rfl
      intro d hd
      have hd : d ≤ min t v := by simpa using hd
      have ht : (∑ i, gtMixedFiveRow (r + s - b : ℕ) b (t + v - d : ℕ) d i) =
          (r : ℤ) + s - t - v := by
        rw [gtMixedFiveRow_sum]
        omega
      rw [gtMixedSlice_apply, if_pos ht, gtMixedWeight_row q h r s t v b d hb hd]
      rfl

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRow_sum
#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_shape
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_mem_support
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_dominant
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_zero
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_nat_sub
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRow_parts_injective
#print axioms VOA.DeligneAudit.D4Char.gtTwoWeight_nat
#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_row
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_eval
