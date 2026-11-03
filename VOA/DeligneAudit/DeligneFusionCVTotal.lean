import VOA.DeligneAudit.DeligneFusionCVBaseFundamental
import VOA.DeligneAudit.DeligneFusionCVBaseOneUniv
import VOA.DeligneAudit.DeligneFusionCVGrade

/-!
# Actual universal CV dimension bounds from two explicit base families

All recurrence steps used below are the proved maps between actual universal
CV modules. The two remaining hypotheses are independent sharp rectangular
KR base bounds and a residual one-adjoint, level-three base bound. They are
definitions of propositions, not axioms or established instances. In
particular this file does not assert unconditional A₂ classical freeness.
-/

namespace VOA.DeligneAudit.A2.CVUniv

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

/-- The three epsilon parameters needed by the actual recurrences. -/
def SmallEpsilon (ε : Weight) : Prop := ε = (0, 0) ∨ ε = (1, 0) ∨ ε = (0, 1)

/-- The expected product of the fundamental, rectangular and adjoint counts. -/
def cvCount (ε ν ϱ : Weight) (j : ℕ) : ℕ :=
  3 ^ (ε.1 + ε.2) * 6 ^ (ν.1 + ν.2) * 10 ^ (ϱ.1 + ϱ.2) * 8 ^ j

/-- An actual ambient finiteness and dimension statement, not a formal count. -/
def CVBound (ε ν ϱ : Weight) (j : ℕ) : Prop :=
  FiniteDimensional ℂ (CVMod ε ν ϱ j) ∧
    Module.finrank ℂ (CVMod ε ν ϱ j) ≤ cvCount ε ν ϱ j

/-- UNPROVED sharp rectangular KR base family: the actual zero-adjoint
universal modules are finite-dimensional with the published product bound.
This is an explicit mathematical input, not a Lean axiom. -/
def SharpRectangularBases : Prop :=
  ∀ (ε ν ϱ : Weight), SmallEpsilon ε → CVBound ε ν ϱ 0

/-- UNPROVED residual level-three base family, after removing every part two.
This is an explicit mathematical input, not an established instance or axiom. -/
def ResidualTheta3Bound : Prop :=
  ∀ ϱ : Weight, FiniteDimensional ℂ (CVMod (0, 0) (0, 0) ϱ 1) ∧
    Module.finrank ℂ (CVMod (0, 0) (0, 0) ϱ 1) ≤ 8 * 10 ^ (ϱ.1 + ϱ.2)

private theorem cvCount_swap (ε ν ϱ : Weight) (j : ℕ) :
    cvCount (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j = cvCount ε ν ϱ j := by
  simp only [cvCount, Nat.add_comm]

/-- Actual finiteness and bounds transport through the proved Dynkin equivalence. -/
theorem CVBound.swap {ε ν ϱ : Weight} {j : ℕ} (h : CVBound ε ν ϱ j) :
    CVBound (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j := by
  refine ⟨@cvSwap_finiteDimensional ε ν ϱ j h.1, ?_⟩
  calc
    Module.finrank ℂ (CVMod (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) =
        Module.finrank ℂ (CVMod ε ν ϱ j) := (cvSwap_finrank ε ν ϱ j).symm
    _ ≤ cvCount ε ν ϱ j := h.2
    _ = _ := (cvCount_swap ε ν ϱ j).symm

private theorem cvCount_zero_step (ν ϱ : Weight) (k : ℕ) :
    cvCount (0, 0) (ν + (1, 1)) ϱ k +
      cvCount (0, 1) (ν + (0, 1)) ϱ k +
      cvCount (0, 0) ν (ϱ + (1, 0)) k = cvCount (0, 0) ν ϱ (k + 2) := by
  simp [cvCount, Prod.fst_add, Prod.snd_add, pow_add]
  <;> ring

private theorem cvCount_fundamental_step (ν ϱ : Weight) (k : ℕ) :
    cvCount (1, 0) (ν + (1, 1)) ϱ k +
      cvCount (0, 0) (ν + (0, 1)) ϱ (k + 1) +
      cvCount (0, 0) (ν + (2, 0)) ϱ k = cvCount (1, 0) ν ϱ (k + 2) := by
  simp [cvCount, Prod.fst_add, Prod.snd_add, pow_add]
  <;> ring

private theorem cvCount_second_fundamental_step (ν ϱ : Weight) (k : ℕ) :
    cvCount (0, 1) (ν + (1, 1)) ϱ k +
      cvCount (0, 0) (ν + (1, 0)) ϱ (k + 1) +
      cvCount (0, 0) (ν + (0, 2)) ϱ k = cvCount (0, 1) ν ϱ (k + 2) := by
  simp [cvCount, Prod.fst_add, Prod.snd_add, pow_add]
  <;> ring

private theorem cvCount_fundamental_one (ν ϱ : Weight) :
    cvCount (0, 1) (ν + (1, 0)) ϱ 0 + cvCount (0, 0) (ν + (0, 1)) ϱ 0 =
      cvCount (1, 0) ν ϱ 1 := by
  simp [cvCount, Prod.fst_add, Prod.snd_add, pow_add]
  <;> ring

/-- The actual one-adjoint fundamental bound follows from rectangular bases,
using the proved one-generator quotient and kernel maps. -/
theorem cvUniv_fundamental_one_of_bases (hR : SharpRectangularBases) (ν ϱ : Weight) :
    CVBound (1, 0) ν ϱ 1 := by
  obtain ⟨hT, bT⟩ := hR (0, 1) (ν + (1, 0)) ϱ (Or.inr (Or.inr rfl))
  obtain ⟨hA, bA⟩ := hR (0, 0) (ν + (0, 1)) ϱ (Or.inl rfl)
  obtain ⟨hs, bs⟩ := @CVBaseFundamental.dimension_step ν ϱ hT hA
  refine ⟨hs, bs.trans ?_⟩
  exact (Nat.add_le_add bT bA).trans_eq (cvCount_fundamental_one ν ϱ)

/-- The second one-adjoint fundamental bound is the actual Dynkin image. -/
theorem cvUniv_second_fundamental_one_of_bases (hR : SharpRectangularBases)
    (ν ϱ : Weight) : CVBound (0, 1) ν ϱ 1 :=
  (cvUniv_fundamental_one_of_bases hR (ν.2, ν.1) (ϱ.2, ϱ.1)).swap

/-- The actual zero-epsilon inductive step, with proved source maps and no
assumed dimension recurrence. -/
theorem cvBound_zero_step {ν ϱ : Weight} {k : ℕ}
    (hT : CVBound (0, 0) (ν + (1, 1)) ϱ k)
    (hA : CVBound (0, 1) (ν + (0, 1)) ϱ k)
    (hB : CVBound (0, 0) ν (ϱ + (1, 0)) k) : CVBound (0, 0) ν ϱ (k + 2) := by
  obtain ⟨hs, bs⟩ := @cvUniv_zero_dimension_step ν ϱ k hT.1 hA.1 hB.1
  refine ⟨hs, bs.trans ?_⟩
  exact (Nat.add_le_add (Nat.add_le_add hT.2 hA.2) hB.2).trans_eq
    (cvCount_zero_step ν ϱ k)

/-- The actual first-fundamental inductive step. -/
theorem cvBound_fundamental_step {ν ϱ : Weight} {k : ℕ}
    (hT : CVBound (1, 0) (ν + (1, 1)) ϱ k)
    (hA : CVBound (0, 0) (ν + (0, 1)) ϱ (k + 1))
    (hB : CVBound (0, 0) (ν + (2, 0)) ϱ k) : CVBound (1, 0) ν ϱ (k + 2) := by
  obtain ⟨hs, bs⟩ := @cvUniv_fundamental_dimension_step ν ϱ k hT.1 hA.1 hB.1
  refine ⟨hs, bs.trans ?_⟩
  exact (Nat.add_le_add (Nat.add_le_add hT.2 hA.2) hB.2).trans_eq
    (cvCount_fundamental_step ν ϱ k)

/-- The actual second-fundamental inductive step. -/
theorem cvBound_second_fundamental_step {ν ϱ : Weight} {k : ℕ}
    (hT : CVBound (0, 1) (ν + (1, 1)) ϱ k)
    (hA : CVBound (0, 0) (ν + (1, 0)) ϱ (k + 1))
    (hB : CVBound (0, 0) (ν + (0, 2)) ϱ k) : CVBound (0, 1) ν ϱ (k + 2) := by
  obtain ⟨hs, bs⟩ := @cvUniv_second_fundamental_dimension_step ν ϱ k hT.1 hA.1 hB.1
  refine ⟨hs, bs.trans ?_⟩
  exact (Nat.add_le_add (Nat.add_le_add hT.2 hA.2) hB.2).trans_eq
    (cvCount_second_fundamental_step ν ϱ k)

private theorem cvCount_zero_one (ν ϱ : Weight) (hν : 0 < ν.1) :
    cvCount (0, 1) (ν - (1, 0)) (ϱ + (1, 0)) 0 +
      cvCount (1, 0) (ν - (1, 0) + (0, 1)) ϱ 0 = cvCount (0, 0) ν ϱ 1 := by
  rcases ν with ⟨a, b⟩
  cases a with
  | zero => simp only [Nat.lt_irrefl] at hν
  | succ a =>
      simp [cvCount, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Nat.succ_eq_add_one, pow_add]
      <;> ring

/-- With a part two on the first root, the actual one-adjoint maps reduce
the bound to the two rectangular bases; their count factors are 30 and 18. -/
theorem cvUniv_zero_one_of_first (hR : SharpRectangularBases)
    (ν ϱ : Weight) (hν : 0 < ν.1) : CVBound (0, 0) ν ϱ 1 := by
  obtain ⟨hT, bT⟩ := hR (0, 1) (ν - (1, 0)) (ϱ + (1, 0))
    (Or.inr (Or.inr rfl))
  obtain ⟨hA, bA⟩ := hR (1, 0) (ν - (1, 0) + (0, 1)) ϱ
    (Or.inr (Or.inl rfl))
  obtain ⟨hs, bs⟩ := @CVBaseOne.dimension_step ν ϱ hν hT hA
  refine ⟨hs, bs.trans ?_⟩
  exact (Nat.add_le_add bT bA).trans_eq (cvCount_zero_one ν ϱ hν)

/-- Every zero-epsilon one-adjoint bound reduces to rectangular bases or
the explicit residual level-three family. -/
theorem cvUniv_zero_one_of_bases (hR : SharpRectangularBases)
    (hΘ : ResidualTheta3Bound) (ν ϱ : Weight) : CVBound (0, 0) ν ϱ 1 := by
  by_cases hν : 0 < ν.1
  · exact cvUniv_zero_one_of_first hR ν ϱ hν
  · by_cases hν' : 0 < ν.2
    · exact (cvUniv_zero_one_of_first hR (ν.2, ν.1) (ϱ.2, ϱ.1) hν').swap
    · have hz : ν = (0, 0) := Prod.ext (by omega) (by omega)
      subst ν
      refine ⟨(hΘ ϱ).1, ?_⟩
      simpa only [cvCount, Nat.zero_add, pow_zero, one_mul, pow_one, Nat.mul_comm]
        using (hΘ ϱ).2

private theorem cvUniv_bound_all_of_one (hR : SharpRectangularBases)
    (hOne : ∀ ν ϱ : Weight, CVBound (0, 0) ν ϱ 1) :
    ∀ (j : ℕ) (ε ν ϱ : Weight), SmallEpsilon ε → CVBound ε ν ϱ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro ε ν ϱ hε
      cases j with
      | zero => exact hR ε ν ϱ hε
      | succ j =>
          cases j with
          | zero =>
              rcases hε with rfl | rfl | rfl
              · exact hOne ν ϱ
              · exact cvUniv_fundamental_one_of_bases hR ν ϱ
              · exact cvUniv_second_fundamental_one_of_bases hR ν ϱ
          | succ k =>
              rcases hε with rfl | rfl | rfl
              · exact cvBound_zero_step
                  (ih k (by omega) (0, 0) (ν + (1, 1)) ϱ (Or.inl rfl))
                  (ih k (by omega) (0, 1) (ν + (0, 1)) ϱ (Or.inr (Or.inr rfl)))
                  (ih k (by omega) (0, 0) ν (ϱ + (1, 0)) (Or.inl rfl))
              · exact cvBound_fundamental_step
                  (ih k (by omega) (1, 0) (ν + (1, 1)) ϱ (Or.inr (Or.inl rfl)))
                  (ih (k + 1) (by omega) (0, 0) (ν + (0, 1)) ϱ (Or.inl rfl))
                  (ih k (by omega) (0, 0) (ν + (2, 0)) ϱ (Or.inl rfl))
              · exact cvBound_second_fundamental_step
                  (ih k (by omega) (0, 1) (ν + (1, 1)) ϱ (Or.inr (Or.inr rfl)))
                  (ih (k + 1) (by omega) (0, 0) (ν + (1, 0)) ϱ (Or.inl rfl))
                  (ih k (by omega) (0, 0) (ν + (0, 2)) ϱ (Or.inl rfl))

/-- All actual auxiliary universal modules in the three epsilon families
satisfy the sharp product bound, conditional on precisely the two unproved
base families. All recurrences in this strong induction are proved maps. -/
theorem cvUniv_bound_all_of_bases (hR : SharpRectangularBases)
    (hΘ : ResidualTheta3Bound) (j : ℕ) (ε ν ϱ : Weight) (hε : SmallEpsilon ε) :
    CVBound ε ν ϱ j :=
  cvUniv_bound_all_of_one hR (cvUniv_zero_one_of_bases hR hΘ) j ε ν ϱ hε

/-- At weight zero every nonempty current word vanishes, so the only possible
graded piece has dimension at most one. This needs no character-chain import. -/
private theorem fusion_zero_total {V : Type} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule bracketTable V) (w : V) (hW : LocalWeylRel R w 0) (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤ 1 := by
  classical
  have hkill : ∀ (c : Fin 8) (r : ℕ), R.op c r w = 0 := by
    intro c r
    rcases (show c.val < 3 ∨ (3 ≤ c.val ∧ c.val < 6) ∨ 6 ≤ c.val by omega) with
      hc | hc | hc
    · exact hW.raising c hc r
    · simpa only [Nat.zero_add] using
        f_trunc_up hc.1 hc.2 (hW.fusion c hc.1 hc.2)
          (fun k hk => hW.cartan_pos 6 (by decide) k hk) r
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simpa using hW.cartan_zero c hc
      · exact hW.cartan_pos c hc r hr
  have hword : ∀ l : List (UnivG.Ltr 8), wordOp R l w = if l = [] then w else 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
        change R.op x.1 x.2 (wordOp R l w) = 0
        rw [ih]
        split_ifs
        · exact hkill x.1 x.2
        · exact map_zero _
  have hspan : cycDeg R w 0 ≤ ℂ ∙ w := by
    rw [cycDeg, Submodule.span_le]
    rintro _ ⟨l, _, rfl⟩
    rw [hword]
    split_ifs
    · exact Submodule.mem_span_singleton_self w
    · exact Submodule.zero_mem _
  have hpos : ∀ d : ℕ, d ≠ 0 → cycDeg R w d = ⊥ := by
    intro d hd
    apply bot_unique
    rw [cycDeg, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    have hn : l ≠ [] := by
      intro he
      subst l
      exact hd hl.symm
    rw [hword, if_neg hn]
    exact Submodule.zero_mem _
  have hb : ∀ d : ℕ, Module.finrank ℂ (cycDeg R w d) ≤ if d = 0 then 1 else 0 := by
    intro d
    by_cases hd : d = 0
    · subst d
      rw [if_pos rfl]
      haveI : FiniteDimensional ℂ (cycDeg R w 0) :=
        Submodule.finiteDimensional_of_le hspan
      exact (Submodule.finrank_mono hspan).trans (by
        simpa using finrank_span_le_card ({w} : Set V))
    · rw [if_neg hd, hpos d hd]
      simp
  calc
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤
        ∑ d ∈ Finset.range B, if d = 0 then 1 else 0 :=
      Finset.sum_le_sum fun d _ => hb d
    _ ≤ 1 := by
      simp only [Finset.sum_ite_eq', Finset.mem_range]
      split_ifs <;> omega

/-- The transfer sums dimensions in the graded universal source before mapping
to an arbitrary model. No independence of the target's pieces is assumed. -/
private theorem fusionTotalDim_of_cvZero_bounds
    (hC : ∀ N : ℕ, 0 < N → CVBound (0, 0) (0, 0) (0, 0) N) : FusionTotalDim := by
  intro m V _ _ R w hW B
  have hM := (mabRel_zero_iff R w m).mpr hW
  by_cases hm : m = 0
  · subst m
    exact fusion_zero_total R w hW B
  · obtain ⟨hFD, hdim⟩ := hC m (by omega)
    haveI := hFD
    have hc := mabRel_zero_cv3 hM (by omega)
    calc
      (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤
          ∑ d ∈ Finset.range B, Module.finrank ℂ
            (cycDeg (cvUnivRep (0, 0) (0, 0) (0, 0) m)
              (cv_wU (0, 0) (0, 0) (0, 0) m) d) :=
        Finset.sum_le_sum fun d _ => by
          rw [← map_cycDeg hc d]
          exact Submodule.finrank_map_le _ _
      _ ≤ Module.finrank ℂ (CVMod (0, 0) (0, 0) (0, 0) m) :=
        sum_finrank_cycDeg_le (0, 0) (0, 0) (0, 0) m (Finset.range B)
      _ ≤ 8 ^ m := by simpa only [cvCount, Nat.zero_add, pow_zero, one_mul] using hdim

/-- The headline total-dimension input follows from precisely the two explicit
unproved base families, via actual universal recurrences and separated degrees.
This theorem does not discharge either base family. -/
theorem fusionTotalDim_of_cvBases (hR : SharpRectangularBases)
    (hΘ : ResidualTheta3Bound) : FusionTotalDim :=
  fusionTotalDim_of_cvZero_bounds fun N _ =>
    cvUniv_bound_all_of_bases hR hΘ N (0, 0) (0, 0) (0, 0) (Or.inl rfl)

end

end VOA.DeligneAudit.A2.CVUniv

#print axioms VOA.DeligneAudit.A2.CVUniv.cvUniv_fundamental_one_of_bases
#print axioms VOA.DeligneAudit.A2.CVUniv.cvBound_zero_step
#print axioms VOA.DeligneAudit.A2.CVUniv.cvBound_fundamental_step
#print axioms VOA.DeligneAudit.A2.CVUniv.cvUniv_zero_one_of_bases
#print axioms VOA.DeligneAudit.A2.CVUniv.cvUniv_bound_all_of_bases
#print axioms VOA.DeligneAudit.A2.CVUniv.fusionTotalDim_of_cvBases
