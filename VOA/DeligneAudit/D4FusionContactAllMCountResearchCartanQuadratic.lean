import VOA.DeligneAudit.D4FusionContactAllMCountResearchWheelEnergy

/-! # Exact Cartan-current isolation in a whole quadratic coefficient

The diagonal finite table is reused symbolically. This is a coefficient
identity for the actual current derivation, not a split seed assumption.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)
open BoundaryPair

noncomputable section

def h0Weight : Fin 9 → ℤ := ![1,1,1,-1,1,-1,-1,-1,0]

private theorem h0_sparse : ∀ i j : Fin 9,
    sparse (rootImages 0 i) j = if j=i then h0Weight i else 0 := by
  decide +kernel

theorem h0_contact (i j : Fin 9) :
    contactF (zeroIndex 0) (radIndex i) (radIndex j) =
      if j=i then (h0Weight i : ℂ) else 0 := by
  change (fZ br (zeroIndex 0) (radIndex i) (radIndex j) : ℂ) = _
  rw [show zeroIndex 0 = derivRoot 0 from rfl,root_images_Z,h0_sparse]
  split_ifs <;> simp

theorem h0Deriv_modeX (m : ℕ) (k r : ℕ) (i : Fin 9) :
    g0Deriv m 0 k (modeX m i r) = (h0Weight i : ℂ) • modeX m i (k+r) := by
  by_cases hr : r < m
  · rw [modeX,dif_pos hr]
    simp [g0Deriv,g0Image,h0_contact]
  · have hh : ¬ k+r < m := by omega
    simp only [modeX,dif_neg hr,dif_neg hh,map_zero,smul_zero]

theorem h0Deriv_simple_modeX (m k r : ℕ) :
    g0Deriv m 0 k (modeX m 0 r) = modeX m 0 (k+r) := by
  rw [h0Deriv_modeX]
  norm_num [h0Weight]

variable {m : ℕ} (b : BoundaryPair m)

/-- Only two ordered pairs survive the positive Cartan shift. -/
theorem shifted_quadratic_sum :
    (∑ x ∈ Finset.antidiagonal (b.lower.val+b.top.val),
      modeX m 0 (b.top.val-b.lower.val-1+x.1) * modeX m 0 x.2) =
      2 • (modeX m 0 (b.top.val-1) * modeX m 0 b.top.val) := by
  let S := Finset.antidiagonal (b.lower.val+b.top.val)
  let f := fun x : ℕ × ℕ =>
    modeX m 0 (b.top.val-b.lower.val-1+x.1) * modeX m 0 x.2
  have hlt := b.lt
  have hlast := b.last
  have hq : 0 < b.top.val := by omega
  have h0 : (b.lower.val,b.top.val) ∈ S := by simp [S]
  have h1 : (b.lower.val+1,b.top.val-1) ∈ S.erase (b.lower.val,b.top.val) := by
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have := congrArg Prod.fst he
      omega
    · simp only [S,Finset.mem_antidiagonal]
      omega
  have hs0 := Finset.add_sum_erase S f h0
  have hs1 := Finset.add_sum_erase (S.erase (b.lower.val,b.top.val)) f h1
  have hzero : ∑ x ∈ (S.erase (b.lower.val,b.top.val)).erase
      (b.lower.val+1,b.top.val-1), f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_erase,S,Finset.mem_antidiagonal] at hx
    have hn0 : ¬ (x.1=b.lower.val ∧ x.2=b.top.val) := by
      intro he
      exact hx.2.1 (Prod.ext he.1 he.2)
    have hn1 : ¬ (x.1=b.lower.val+1 ∧ x.2=b.top.val-1) := by
      intro he
      exact hx.1 (Prod.ext he.1 he.2)
    by_cases hi : b.top.val-b.lower.val-1+x.1 < m
    · have hj : ¬ x.2 < m := by omega
      simp only [f,modeX,dif_neg hj,mul_zero]
    · simp only [f,modeX,dif_neg hi,zero_mul]
  change (∑ x ∈ S, f x) = _
  rw [← hs0,← hs1,hzero,add_zero]
  have ha : b.top.val-b.lower.val-1+b.lower.val = b.top.val-1 := by omega
  have hb : b.top.val-b.lower.val-1+(b.lower.val+1) = b.top.val := by omega
  simp only [f,ha,hb,two_smul]
  rw [mul_comm (modeX m 0 b.top.val)]

/-- Differentiating the whole grouped source coefficient isolates one
adjacent top-mode product with its exact factor two. -/
theorem h0Deriv_groupedSeed :
    g0Deriv m 0 (b.top.val-b.lower.val-1) (groupedSeed b) =
      2 • (modeX m 0 (b.top.val-1) * modeX m 0 b.top.val) := by
  let k := b.top.val-b.lower.val-1
  let S := Finset.antidiagonal (b.lower.val+b.top.val)
  let f := fun x : ℕ × ℕ => modeX m 0 (k+x.1) * modeX m 0 x.2
  have hs : (∑ x ∈ S, modeX m 0 x.1 * modeX m 0 (k+x.2)) = ∑ x ∈ S, f x := by
    have he := (Finset.Nat.sum_antidiagonal_swap
      (f := fun x : ℕ × ℕ => modeX m 0 x.1 * modeX m 0 (k+x.2))
      (n := b.lower.val+b.top.val))
    simpa only [S,f,Prod.swap,mul_comm] using he.symm
  rw [groupedSeed_whole,Derivation.map_smul]
  simp only [pow_two,PowerSeries.coeff_mul,Polynomial.AllM.current,
    PowerSeries.coeff_mk,map_sum,Derivation.leibniz,h0Deriv_simple_modeX,smul_eq_mul]
  change (1/2:ℂ) • (∑ x ∈ S,
    (modeX m 0 x.1 * modeX m 0 (k+x.2) + modeX m 0 x.2 * modeX m 0 (k+x.1))) = _
  rw [Finset.sum_add_distrib,hs]
  have he : (∑ x ∈ S, modeX m 0 x.2 * modeX m 0 (k+x.1)) = ∑ x ∈ S, f x := by
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  rw [he]
  have hcancel : (1/2:ℂ) • ((∑ x ∈ S, f x)+(∑ x ∈ S, f x)) = ∑ x ∈ S, f x := by
    module
  rw [hcancel]
  exact shifted_quadratic_sum b

/-- The mode of the diagonal-index Cartan family. -/
def refinementMode : Fin m :=
  ⟨b.top.val-b.lower.val-1,by have := b.top.isLt; omega⟩

/-- Actual adjacent top-mode quadratic relation derived from the whole seed. -/
theorem adjacent_top_product_mem_candidate :
    modeX m 0 (b.top.val-1) * modeX m 0 b.top.val ∈
      Polynomial.AllM.candidateIdeal m := by
  have hh := Polynomial.AllM.candidateIdeal_deriv m (.inl (0,refinementMode b))
    (groupedSeed_mem b)
  change g0Deriv m 0 (b.top.val-b.lower.val-1) (groupedSeed b) ∈ _ at hh
  rw [h0Deriv_groupedSeed] at hh
  have hc := ((Polynomial.AllM.candidateIdeal m).restrictScalars ℂ).smul_mem (1/2:ℂ) hh
  have he : (1/2:ℂ) • (2 •
      (modeX m 0 (b.top.val-1) * modeX m 0 b.top.val)) =
      modeX m 0 (b.top.val-1) * modeX m 0 b.top.val := by module
  rwa [he] at hc

/-- The finite-probe diagonal-index family, retaining all source corrections.
Its fixed leading polynomial and global coverage remain separate obligations. -/
def refinedWheel : MvPolynomial (Vars m) ℂ :=
  if b.lower.val + 1 = b.top.val then MvPolynomial.rename b.embed endpointWheel
  else g0Deriv m 0 (refinementMode b).val (currentWheel b)

theorem refinedWheel_mem_candidate : refinedWheel b ∈ Polynomial.AllM.candidateIdeal m := by
  by_cases ha : b.lower.val + 1 = b.top.val
  · rw [refinedWheel,if_pos ha]
    exact adjacent_endpointWheel_mem_candidate b ha
  · rw [refinedWheel,if_neg ha]
    exact Polynomial.AllM.candidateIdeal_deriv m (.inl (0,refinementMode b))
      (currentWheel_mem_candidate b)

end

#print axioms h0Deriv_groupedSeed
#print axioms adjacent_top_product_mem_candidate
#print axioms refinedWheel_mem_candidate

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
