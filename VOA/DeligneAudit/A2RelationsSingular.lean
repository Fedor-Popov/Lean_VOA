/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CurrentJetSurjectivity
import VOA.DeligneAudit.A2Relations
import VOA.Core.BorcherdsIdentity

/-!
# Perše's weight-two singular vector of `V^{-3/2}(sl₃)` dies in `L_{-3/2}(sl₃)`

* §1 (any noncritical level `k`): the *Dong-type upgrade* for the universal affine `sl₃` VOA,
  ported from `VOA/Examples/AffineSl2Strong.lean`: a vector killed by every strictly positive
  current mode (`SingP3`) is killed by every non-weight-raising mode of every state; weight-one
  states are quasi-primary.  Hence a nonzero homogeneous `SingP3` vector of positive weight is
  strongly singular, and every homogeneous `SingP3` vector of positive weight lies in the maximal
  graded ideal (`mem_maxIdeal_of_SingP3`; the zero vector trivially).
* §2 (`k = -3/2`): the explicit vector `singVec` (certificate `cert_A2.json`, translated to
  `generator` coordinates, see `A2Relations.lean`), its weight, and `SingP3`.  The positive
  modes `x(1)`, `x(2)` are computed outright from the affine commutator; `x(m)`, `m ≥ 3`, vanish
  by weight.  Hence `singVec ∈ maxIdeal` and its image in `simpleVOA (-3/2)` is zero.
-/

namespace VOA.DeligneAudit.A2

open VOA.AffineSl3
open Module (End)

noncomputable section

/-! ## §1  Strong singularity from the currents, for `V^k(sl₃)` -/

section Strong

variable (k : ℂ) (hk : k + 3 ≠ 0)

theorem smulU_currentState (a : Fin 8) (m : ℤ) (v : Vacuum k) :
    (affineSl3VOA k hk).smul (currentState k (generator a)) m v = J k a m v := by
  change mode (YA k hk (currentState k (generator a))) m v = _
  rw [mode_YA_currentState]
  rfl

theorem wordDegA_nonneg' : ∀ l : List (Fin 8 × ℕ), 0 ≤ wordDegA l
  | [] => le_rfl
  | (ai :: L) => by
      rw [wordDegA_cons]
      have h := wordDegA_nonneg' L
      have : (0 : ℤ) ≤ (ai.2 : ℤ) := Int.natCast_nonneg _
      omega

/-- Generator-singularity: every strictly positive current mode kills `t`. -/
def SingP3 (t : Vacuum k) : Prop := ∀ (a : Fin 8) (i : ℤ), 1 ≤ i → J k a i t = 0

variable {k} in
/-- `SingP3` is stable under the zero modes (the central term is absent since `i + 0 ≠ 0`). -/
theorem SingP3.zeroMode {t : Vacuum k} (ht : SingP3 k t) (a : Fin 8) : SingP3 k (J k a 0 t) := by
  intro b i hi
  have hcomm := LinearMap.congr_fun (current_comm k b a i 0) t
  rw [if_neg (by omega : ¬ (i + (0 : ℤ) = 0))] at hcomm
  simp only [LinearMap.sub_apply, Module.End.mul_apply, add_zero,
    LinearMap.sum_apply, LinearMap.smul_apply] at hcomm
  rw [ht b i hi, map_zero, sub_zero] at hcomm
  rw [hcomm]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [ht c i hi, smul_zero]

/-- The Dong-type induction over creation words. -/
theorem word_ann3 (l : List (Fin 8 × ℕ)) :
    ∀ (t : Vacuum k), SingP3 k t → ∀ N : ℤ, wordDegA l ≤ N →
      (affineSl3VOA k hk).smul (wordStateA k l) N t = 0 := by
  induction l with
  | nil =>
      intro t _ N hN
      rw [wordDegA_nil] at hN
      rw [wordStateA_nil]
      change (affineSl3VOA k hk).smul (affineSl3VOA k hk).vacuum N t = 0
      rw [PreVertexAlgebra.smul_vacuum_left, if_neg (by omega)]
  | cons ai rest ih =>
      obtain ⟨a, n⟩ := ai
      intro t ht N hN
      rw [wordDegA_cons] at hN
      have hdn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
      rw [wordStateA_cons]
      change (affineSl3VOA k hk).smul (J k a (-(n : ℤ) - 1) (wordStateA k rest)) N t = 0
      rw [← smulU_currentState k hk a (-(n : ℤ) - 1) (wordStateA k rest),
        VertexOperatorAlgebra.mode_iterate]
      have hterm : ∀ i : ℕ,
          (((-1 : ℂ) ^ i * gBinom (-(n : ℤ) - 1) i) •
            ((affineSl3VOA k hk).smul (currentState k (generator a)) (-(n : ℤ) - 1 - (i : ℤ))
                ((affineSl3VOA k hk).smul (wordStateA k rest) (N + (i : ℤ)) t)
              - ((-1 : ℂ) ^ (-(n : ℤ) - 1)) •
                (affineSl3VOA k hk).smul (wordStateA k rest)
                  ((-(n : ℤ) - 1) + N - (i : ℤ))
                  ((affineSl3VOA k hk).smul (currentState k (generator a)) (i : ℤ) t)))
          = 0 := by
        intro i
        have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
        have h1 : (affineSl3VOA k hk).smul (wordStateA k rest) (N + (i : ℤ)) t = 0 :=
          ih t ht (N + (i : ℤ)) (by omega)
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · have h2 : (affineSl3VOA k hk).smul (wordStateA k rest)
              ((-(n : ℤ) - 1) + N - ((0 : ℕ) : ℤ)) (J k a 0 t) = 0 :=
            ih _ (ht.zeroMode a) _ (by push_cast; omega)
          simp only [smulU_currentState, Nat.cast_zero, sub_zero, add_zero] at h1 h2 ⊢
          rw [h1, h2]
          simp
        · have h2 : (affineSl3VOA k hk).smul (currentState k (generator a)) (i : ℤ) t = 0 := by
            rw [smulU_currentState]
            exact ht a (i : ℤ) (by exact_mod_cast hipos)
          rw [h1, h2]
          simp
      rw [finsum_congr hterm, finsum_zero]

theorem hspan_ann3 {t : Vacuum k} (ht : SingP3 k t) (m : ℤ) :
    ∀ u ∈ HSpan k m, ∀ N : ℤ, m ≤ N → (affineSl3VOA k hk).smul u N t = 0 := by
  intro u hu
  rw [HSpan] at hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      intro N hN
      exact word_ann3 k hk l t ht N (by rw [hl]; exact hN)
  | zero => intro N _; simp
  | add x y _ _ ihx ihy =>
      intro N hN
      rw [PreVertexAlgebra.smul_add_left, ihx N hN, ihy N hN, add_zero]
  | smul c x _ ihx =>
      intro N hN
      rw [PreVertexAlgebra.smul_smul_left, ihx N hN, smul_zero]

/-- **Strong-generation upgrade for `V^k(sl₃)`**: positive current singularity implies that
every non-weight-raising mode of every homogeneous state kills `t`. -/
theorem strongly_singular_of_SingP3 {t : Vacuum k} (ht : SingP3 k t)
    {m : ℤ} {u : Vacuum k} (hu : u ∈ (affineSl3VOA k hk).grading m) :
    ∀ N : ℤ, m ≤ N → (affineSl3VOA k hk).smul u N t = 0 :=
  hspan_ann3 k hk ht m u (gradingZA_le_hspan k m hu)

/-- **Weight-one states of `V^k(sl₃)` are quasi-primary**: `L₁ v = 0` on `V₁`. -/
theorem affineSl3_qp :
    ∀ v, v ∈ (affineSl3VOA k hk).grading 1 → (affineSl3VOA k hk).L 1 v = 0 := by
  intro v hv
  change v ∈ gradingZA k 1 at hv
  rw [grading_one_eq_range] at hv
  obtain ⟨x, rfl⟩ := hv
  have hL : (affineSl3VOA k hk).L 1 = mode (YA k hk (omegaA k)) 2 := by
    rw [VertexOperatorAlgebra.L_def]
    norm_num
    rfl
  rw [hL, ← reconstruct x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul, map_smul, currentState_generator, current_primary k hk c, smul_zero]

/-- A nonzero homogeneous `SingP3` vector of positive weight is strongly singular. -/
theorem isStronglySingular_of_SingP3 {t : Vacuum k} (ht : SingP3 k t) (hne : t ≠ 0)
    {w : ℤ} (hw : 0 < w) (hmem : t ∈ gradingZA k w) :
    SingVec.IsStronglySingularOfWeight (affineSl3VOA k hk) w t where
  ne_zero := hne
  weight_pos := hw
  homogeneous := hmem
  annihilated := fun _ _ hu n hn => strongly_singular_of_SingP3 k hk ht hu n hn

/-- **Every homogeneous `SingP3` vector of positive weight lies in the maximal ideal** (the zero
vector trivially, a nonzero one by strong singularity). -/
theorem mem_maxIdeal_of_SingP3 {t : Vacuum k} (ht : SingP3 k t)
    {w : ℤ} (hw : 0 < w) (hmem : t ∈ gradingZA k w) : t ∈ maxIdeal k hk := by
  by_cases h0 : t = 0
  · rw [h0]; exact Submodule.zero_mem _
  · exact SimpleQuot.mem_maxGradedIdeal_of_stronglySingular (vacuumA_ne_zero k)
      (affineSl3_qp k hk) (isStronglySingular_of_SingP3 k hk ht h0 hw hmem)

end Strong

/-! ## §2  The singular vector at `k = -3/2` -/

/-- One commutator step, oriented to move a nonnegative mode past a creation mode. -/
theorem J_J_comm (k : ℂ) (a b : Fin 8) {m n : ℤ} (_hm : 0 ≤ m) (_hn : n < 0) (w : Vacuum k) :
    J k a m (J k b n w) =
      J k b n (J k a m w) + (∑ c, bracketTable a b c • J k c (m + n) w)
        + (if m + n = 0 then ((m : ℂ) * k * formTable a b) • w else 0) := by
  have h := LinearMap.congr_fun (current_comm k a b m n) w
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, sub_eq_iff_eq_add'] at h
  rw [h, add_assoc]
  congr 2
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [LinearMap.smul_apply, structureConstant_eq_table]
  · by_cases hmn : m + n = 0
    · rw [if_pos hmn, if_pos hmn, LinearMap.smul_apply, LinearMap.id_apply]
    · rw [if_neg hmn, if_neg hmn, LinearMap.zero_apply]

theorem J_vac_nonneg (a : Fin 8) {m : ℤ} (hm : 0 ≤ m) : J (-3 / 2) a m (vacuumA (-3 / 2)) = 0 :=
  J_vacuum_nonneg _ a hm

/-- **The weight-two singular vector of `V^{-3/2}(sl₃)`** (Perše), highest weight `θ`, in
`generator` coordinates:
`2 h₁(-1)e₁₂(-1)𝟙 - 2 h₂(-1)e₁₂(-1)𝟙 + 6 e₂(-1)e₁(-1)𝟙 + 3 e₁₂(-2)𝟙`. -/
def singVec : Vacuum (-3 / 2) :=
  (2 : ℂ) • J (-3 / 2) 6 (-1) (J (-3 / 2) 2 (-1) (vacuumA (-3 / 2)))
    - (2 : ℂ) • J (-3 / 2) 7 (-1) (J (-3 / 2) 2 (-1) (vacuumA (-3 / 2)))
    + (6 : ℂ) • J (-3 / 2) 1 (-1) (J (-3 / 2) 0 (-1) (vacuumA (-3 / 2)))
    + (3 : ℂ) • J (-3 / 2) 2 (-2) (vacuumA (-3 / 2))

set_option maxHeartbeats 2000000 in -- eight explicit commutator expansions over the table
theorem singVec_J_one (a : Fin 8) : J (-3 / 2) a 1 singVec = 0 := by
  fin_cases a <;>
  simp [singVec, J_J_comm, J_vac_nonneg, Fin.sum_univ_eight, bracketTable, formTable] <;>
  module

set_option maxHeartbeats 2000000 in -- eight explicit commutator expansions over the table
theorem singVec_J_two (a : Fin 8) : J (-3 / 2) a 2 singVec = 0 := by
  fin_cases a <;>
  simp [singVec, J_J_comm, J_vac_nonneg, Fin.sum_univ_eight, bracketTable, formTable]
  module

/-- A creation mode raises the weight of a homogeneous state by `-m`. -/
theorem J_mem_gradingZA (k : ℂ) (hk : k + 3 ≠ 0) (a : Fin 8) (m : ℤ) {q : ℤ} {x : Vacuum k}
    (hx : x ∈ gradingZA k q) : J k a m x ∈ gradingZA k (q - m) := by
  rw [← smulU_currentState k hk]
  have h := (affineSl3VOA k hk).smul_mem_grading (currentState_mem_grading k (generator a)) hx m
  rwa [show (1 : ℤ) + q - m - 1 = q - m by ring] at h

theorem vacuumA_mem (k : ℂ) : vacuumA k ∈ gradingZA k 0 := vacuumA_mem_gradingZA_zero k

/-- The singular vector has conformal weight two. -/
theorem singVec_mem : singVec ∈ gradingZA (-3 / 2) 2 := by
  have hk := level_add_three_ne_zero
  have h11 : ∀ a b : Fin 8, J (-3 / 2) a (-1) (J (-3 / 2) b (-1) (vacuumA (-3 / 2))) ∈
      gradingZA (-3 / 2) 2 := fun a b => by
    have := J_mem_gradingZA _ hk a (-1) (J_mem_gradingZA _ hk b (-1) (vacuumA_mem (-3 / 2)))
    simpa using this
  have h2 : J (-3 / 2) 2 (-2) (vacuumA (-3 / 2)) ∈ gradingZA (-3 / 2) 2 := by
    simpa using J_mem_gradingZA _ hk 2 (-2) (vacuumA_mem (-3 / 2))
  unfold singVec
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _
    (Submodule.smul_mem _ _ (h11 _ _)) (Submodule.smul_mem _ _ (h11 _ _)))
    (Submodule.smul_mem _ _ (h11 _ _))) (Submodule.smul_mem _ _ h2)

/-- **Every strictly positive current mode kills the singular vector.** -/
theorem singVec_singP3 : SingP3 (-3 / 2) singVec := by
  intro a i hi
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · exact singVec_J_one a
  · exact singVec_J_two a
  · have h := J_mem_gradingZA _ level_add_three_ne_zero a i singVec_mem
    rw [gradingZA_positivity _ (2 - i) (by omega)] at h
    exact (Submodule.mem_bot ℂ).mp h

/-- **The singular vector lies in the maximal ideal of `V^{-3/2}(sl₃)`.** -/
theorem singVec_mem_maxIdeal : singVec ∈ maxIdeal (-3 / 2) level_add_three_ne_zero :=
  mem_maxIdeal_of_SingP3 _ _ singVec_singP3 (by norm_num) singVec_mem

/-- **The singular vector vanishes in `L_{-3/2}(sl₃)`.** -/
theorem simpleProjection_singVec :
    simpleProjection (-3 / 2) level_add_three_ne_zero singVec = 0 := by
  rw [simpleProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact singVec_mem_maxIdeal

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.strongly_singular_of_SingP3
#print axioms VOA.DeligneAudit.A2.affineSl3_qp
#print axioms VOA.DeligneAudit.A2.mem_maxIdeal_of_SingP3
#print axioms VOA.DeligneAudit.A2.singVec_singP3
#print axioms VOA.DeligneAudit.A2.simpleProjection_singVec
end AxiomAudit
