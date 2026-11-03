import VOA.Classification.COne.PlusSplitTwistedCandidates

/-! Explicit candidate values on the homogeneous Zhu spanning family.
Negative-one conformal iterates have shifted factorial values, not powers.
No independence or descent of the proposed values is assumed. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuFiniteTests
open PlusUnitary PlusZhuNormalForms PlusCharacterTable

/-- Scalar recurrence for negative-one conformal iterates of a weight-d state. -/
def iterateValue (h d : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (h + d + 2 * n) * iterateValue h d n

variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance valuesRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance valuesAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) :=
  instAlgebraA _

theorem omegaIter_mem_grading {d : ℤ} {v : ↥(PlusC2.VP m hm)}
    (hv : v ∈ (V2mPlus m hm).grading d) (n : ℕ) :
    omegaIter m hm v n ∈ (V2mPlus m hm).grading (d + 2 * n) := by
  induction n with
  | zero => simpa [omegaIter] using hv
  | succ n ih =>
    have h := (V2mPlus m hm).smul_mem_grading (V2mPlus m hm).conformal_mem ih (-1)
    convert h using 1
    congr 1
    push_cast
    ring

/-- The actual Zhu product differs from the negative-one product by weight. -/
theorem omega_mul_mk {d : ℤ} {v : ↥(PlusC2.VP m hm)}
    (hv : v ∈ (V2mPlus m hm).grading d) :
    generator m hm 0 * VOA.mk (V2mPlus m hm) v =
      VOA.mk (V2mPlus m hm) ((V2mPlus m hm).smul
        (V2mPlus m hm).conformalVector (-1) v) - (d : ℂ) • VOA.mk (V2mPlus m hm) v := by
  have hprod : zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector v =
      (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1) v +
      (2 : ℂ) • (V2mPlus m hm).L (-1) v + (V2mPlus m hm).L 0 v := by
    rw [zhuMul_homogeneous' _ (V2mPlus m hm).conformal_mem]
    simp only [show (2 : ℤ).toNat + 1 = 3 from rfl, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    have hb1 : cbz 2 1 = 2 := by
      simpa using cbz_natCast_eq_choose (show 1 ≤ 2 by omega)
    have hb2 : cbz 2 2 = 1 := by
      simpa using cbz_natCast_eq_choose (show 2 ≤ 2 by omega)
    norm_num [hb1, hb2, cbz_zero]
    rfl
  have ht := zhuLgen_mem_O (V2mPlus m hm) v
  rw [(V2mPlus m hm).L_zero_grading v hv] at ht
  have ht' := (Submodule.Quotient.mk_eq_zero _).mpr ht
  change VOA.mk (V2mPlus m hm) (_ + _) = 0 at ht'
  rw [map_add, map_smul] at ht'
  have htrans := eq_neg_of_add_eq_zero_left ht'
  change VOA.mk (V2mPlus m hm) (V2mPlus m hm).conformalVector * _ = _
  rw [← mk_zhuMul, hprod, map_add, map_add, map_smul,
    (V2mPlus m hm).L_zero_grading v hv, map_smul, htrans]
  module

theorem character_omegaIter (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    {d : ℤ} {v : ↥(PlusC2.VP m hm)} (hv : v ∈ (V2mPlus m hm).grading d) (n : ℕ) :
    χ (VOA.mk (V2mPlus m hm) (omegaIter m hm v n)) =
      iterateValue (χ (generator m hm 0)) d n * χ (VOA.mk (V2mPlus m hm) v) := by
  induction n with
  | zero => simp [omegaIter, iterateValue]
  | succ n ih =>
    have h := congrArg χ (omega_mul_mk m hm (omegaIter_mem_grading m hm hv n))
    simp only [map_mul, map_sub, map_smul, smul_eq_mul] at h
    change _ = χ (VOA.mk (V2mPlus m hm) (omegaIter m hm v (n + 1))) - _ at h
    rw [ih] at h
    simp only [iterateValue]
    push_cast at h
    linear_combination -h

/-- Forced proposed values on all m+7 spanning states, with E normalized
by the actual identity EP = 2*y0. This is a vector of scalars, not a functional
on the quotient. -/
def candidateValues (i : Fin 4) : Index m → ℂ
  | .inl (.inl j) => iterateValue (twistedRow m i 0) 0 j.val
  | .inl (.inr j) => iterateValue (twistedRow m i 0) 4 j.val * twistedRow m i 1
  | .inr j => iterateValue (twistedRow m i 0) m j.val * (twistedRow m i 2 / 2)

theorem character_spanningClass (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (i : Fin 4) (hχ : HasValues m hm (twistedLabel m i) χ) (j : Index m) :
    χ (spanningClass m hm j) = candidateValues m i j := by
  have h0 : χ (generator m hm 0) = twistedRow m i 0 := hχ.1
  have h1 : χ (VOA.mk (V2mPlus m hm) (WP m hm)) = twistedRow m i 1 := hχ.2.1
  have hy : y0 m hm = (1/2 : ℂ) • EP m hm := by
    rw [EP_eq_y0, smul_smul]
    norm_num
  have h2 : χ (VOA.mk (V2mPlus m hm) (y0 m hm)) = twistedRow m i 2 / 2 := by
    rw [hy, map_smul, map_smul]
    change (1/2 : ℂ) * χ (generator m hm 2) = _
    have he : χ (generator m hm 2) = twistedRow m i 2 := hχ.2.2
    rw [he]
    ring
  rcases j with (j | j) | j
  · have h := character_omegaIter m hm χ (V2mPlus m hm).vacuum_mem_grading_zero j.val
    have hunit : χ (VOA.mk (V2mPlus m hm) (V2mPlus m hm).vacuum) = 1 := map_one χ
    simpa [spanningClass, spanningState, candidateValues, h0, hunit] using h
  · simpa [spanningClass, spanningState, candidateValues, h0, h1] using
      character_omegaIter m hm χ (WP_mem_grading m hm) j.val
  · have hv : y0 m hm ∈ (V2mPlus m hm).grading m := by
      rw [hy]
      exact Submodule.smul_mem _ _ (EP_mem_grading m hm)
    simpa [spanningClass, spanningState, candidateValues, h0, h2] using
      character_omegaIter m hm χ hv j.val

/-- The actual spanning theorem implies uniqueness, but does not imply
existence, of a linear functional with these proposed values. -/
theorem linearMap_eq_of_spanning_values (hm2 : 2 ≤ m)
    (f g : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ)
    (h : ∀ j : Index m, f (spanningClass m hm j) = g (spanningClass m hm j)) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range (spanningClass m hm)) := by
    rw [spanningClass_span m hm hm2]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

end VOA.Classification.COne.PlusZhuFiniteTests
