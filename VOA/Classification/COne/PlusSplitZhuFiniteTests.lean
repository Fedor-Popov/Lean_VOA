import VOA.Classification.COne.PlusSplitSessionNine

/-! A concrete finite spanning family for the genuine Zhu quotient, and a
finite test for a linear functional to be a character. No character existence
is inferred from the C₂ dimension upper bound. -/
set_option maxSynthPendingDepth 3
noncomputable section

namespace VOA.Classification.COne.PlusZhuFiniteTests
open PlusUnitary VOA.TripletNilp

section Algebra
variable {K R I J : Type*} [Field K] [Ring R] [Algebra K R]

/-- Multiplicativity in the left generator slots suffices. -/
theorem map_mul_of_generators (g : I → R)
    (hg : Algebra.adjoin K (Set.range g) = ⊤) (f : R →ₗ[K] K)
    (h1 : f 1 = 1) (hf : ∀ i x, f (g i * x) = f (g i) * f x) :
    ∀ x y, f (x * y) = f x * f y := by
  intro x
  have hx : x ∈ Algebra.adjoin K (Set.range g) := by rw [hg]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hf i
  | algebraMap c =>
      intro y
      simp [Algebra.algebraMap_eq_smul_one, h1]
  | add x z _ _ hx hz =>
      intro y
      simp only [add_mul, map_add, hx, hz]
  | mul x z _ _ hx hz =>
      intro y
      rw [mul_assoc, hx, hz, hx, mul_assoc]

/-- Only generator-times-spanning-vector entries need checking. -/
theorem generator_test_of_span (g : I → R) (b : J → R)
    (hb : Submodule.span K (Set.range b) = ⊤) (f : R →ₗ[K] K)
    (hf : ∀ i j, f (g i * b j) = f (g i) * f (b j)) :
    ∀ i x, f (g i * x) = f (g i) * f x := by
  intro i x
  have hx : x ∈ Submodule.span K (Set.range b) := by rw [hb]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hf i j
  | zero => simp
  | add x y _ _ hx hy => simp [mul_add, hx, hy]
  | smul c x _ hx => simp [hx, mul_left_comm]

/-- This constructs a character of the actual algebra, not of a proposed
presentation with an unverified relation ideal. -/
def characterOfFiniteTests (g : I → R)
    (hg : Algebra.adjoin K (Set.range g) = ⊤) (b : J → R)
    (hb : Submodule.span K (Set.range b) = ⊤) (f : R →ₗ[K] K)
    (h1 : f 1 = 1) (hf : ∀ i j, f (g i * b j) = f (g i) * f (b j)) :
    R →ₐ[K] K where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add
  map_one' := h1
  map_mul' := map_mul_of_generators g hg f h1 (generator_test_of_span g b hb f hf)
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one, h1]

end Algebra

variable (m : ℕ) (hm : 1 ≤ m)

/-- Repeated negative-one conformal products, before taking either quotient. -/
def omegaIter (v : ↥(PlusC2.VP m hm)) : ℕ → ↥(PlusC2.VP m hm)
  | 0 => v
  | n + 1 => (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1)
      (omegaIter v n)

theorem omegaIter_homogeneous {v : ↥(PlusC2.VP m hm)} (hv : IsHomog (V2mPlus m hm) v)
    (n : ℕ) : IsHomog (V2mPlus m hm) (omegaIter m hm v n) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨_, (V2mPlus m hm).smul_mem_grading
        (V2mPlus m hm).conformal_mem hk (-1)⟩

theorem mk₂_omegaIter (v : ↥(PlusC2.VP m hm)) (n : ℕ) :
    mk₂ (V2mPlus m hm) (omegaIter m hm v n) =
      PlusC2Sharp.o m hm ^ n * mk₂ (V2mPlus m hm) v := by
  induction n with
  | zero => simp [omegaIter]
  | succ n ih =>
      rw [omegaIter, mk₂_smul_neg_one, ih, pow_succ']
      exact (mul_assoc _ _ _).symm

abbrev Index (m : ℕ) := (Fin (m + 1) ⊕ Fin 3) ⊕ Fin 3

/-- Homogeneous representatives of the C₂ spanning list. -/
def spanningState : Index m → ↥(PlusC2.VP m hm)
  | .inl (.inl i) => omegaIter m hm (V2mPlus m hm).vacuum i.val
  | .inl (.inr i) => omegaIter m hm (WP m hm) i.val
  | .inr i => omegaIter m hm (y0 m hm) i.val

theorem spanningState_homogeneous (i : Index m) :
    IsHomog (V2mPlus m hm) (spanningState m hm i) := by
  rcases i with (i | i) | i
  · exact omegaIter_homogeneous m hm ⟨0, (V2mPlus m hm).vacuum_mem_grading_zero⟩ _
  · exact omegaIter_homogeneous m hm ⟨4, WP_mem_grading m hm⟩ _
  · have he : y0 m hm = (1 / 2 : ℂ) • EP m hm := by
      rw [EP_eq_y0, smul_smul]
      norm_num
    apply omegaIter_homogeneous m hm
    refine ⟨m, ?_⟩
    rw [he]
    exact Submodule.smul_mem _ _ (EP_mem_grading m hm)

theorem mk₂_spanningState (i : Index m) :
    mk₂ (V2mPlus m hm) (spanningState m hm i) = PlusC2Sharp.spanningList m hm i := by
  rcases i with (i | i) | i
  · simpa [spanningState, PlusC2Sharp.spanningList, PlusC2Sharp.neutralList, ← A₂_one_eq]
      using mk₂_omegaIter m hm (V2mPlus m hm).vacuum i.val
  · exact mk₂_omegaIter m hm (WP m hm) i.val
  · exact mk₂_omegaIter m hm (y0 m hm) i.val

def spanningClass (i : Index m) : VOA.A (V2mPlus m hm) :=
  VOA.mk (V2mPlus m hm) (spanningState m hm i)

/-- The same m+7 homogeneous representatives span the actual Zhu quotient.
They are negative-one products; no equality with Zhu monomials is assumed. -/
theorem spanningClass_span (hm2 : 2 ≤ m) :
    Submodule.span ℂ (Set.range (spanningClass m hm)) = ⊤ := by
  have hc2 : (Submodule.span ℂ (Set.range (spanningState m hm))).map
      (O₂ (V2mPlus m hm)).mkQ = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp']
    change Submodule.span ℂ (Set.range (fun i => mk₂ _ (spanningState m hm i))) = ⊤
    simp only [mk₂_spanningState]
    exact PlusC2Sharp.spanningList_span_all m hm hm2
  have hstates : (⊤ : Submodule ℂ ↥(PlusC2.VP m hm)) =
      Submodule.span ℂ (Set.range (spanningState m hm)) ⊔ O₂ (V2mPlus m hm) := by
    have h := congrArg (Submodule.comap (O₂ (V2mPlus m hm)).mkQ) hc2
    simpa only [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] using h.symm
  have hO := span_sup_O_eq_top (V2mPlus m hm) (Set.range (spanningState m hm))
    (by rintro _ ⟨i, rfl⟩; exact spanningState_homogeneous m hm i) hstates
  have hker : (O (V2mPlus m hm)).map (O (V2mPlus m hm)).mkQ = ⊥ := by
    exact Submodule.mkQ_map_self _
  have hmap := congrArg (Submodule.map (O (V2mPlus m hm)).mkQ) hO
  simpa only [Submodule.map_top, Submodule.range_mkQ, Submodule.map_sup,
    Submodule.map_span, hker, sup_bot_eq, ← Set.range_comp'] using hmap.symm

end VOA.Classification.COne.PlusZhuFiniteTests
