import VOA.Classification.COne.OrbSpanMain

/-!
# Xu's two towers and the primary reduction

The generic descent argument is independent of the choice of invariant ring.
In particular the `A₄`-specific `PrimModel` is not asserted for `A₅`.
This file exposes exactly the primary reduction needed for Xu's span and proves
the four-to-two elimination. It does not prove the icosahedral primary reduction.
-/

set_option Elab.async false

noncomputable section
namespace VOA.Classification.COne.OrbXu
open VOA VertexOperatorAlgebra OrbSpan OrbC2c

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- The span in the unchanged `XuIcosahedralPoissonRelations` definition. -/
def twoTowers (X : V) : Submodule ℂ (A₂ W) :=
  Submodule.span ℂ (Set.range (Sum.elim
    (fun n : ℕ => (exceptionalConformalEnd W ^ n) (mk₂ W W.vacuum))
    (fun n : ℕ => (exceptionalConformalEnd W ^ n) (mk₂ W X))))

theorem twoTowers_eq_towerSpan (X : V) :
    twoTowers W X = towerSpan W
      (fun b : Bool => if b then mk₂ W X else mk₂ W W.vacuum) := by
  unfold twoTowers towerSpan
  congr 1
  ext y
  constructor
  · rintro ⟨n | n, rfl⟩
    · exact ⟨(false, n), rfl⟩
    · exact ⟨(true, n), rfl⟩
  · rintro ⟨⟨b, n⟩, rfl⟩
    cases b
    · exact ⟨Sum.inl n, rfl⟩
    · exact ⟨Sum.inr n, rfl⟩

set_option maxHeartbeats 800000 in
-- The induction compares quotient preimages and spans over arbitrary universes.
/-- Graded descent for any seed set gives its conformal-tower spanning theorem. -/
theorem towerSpan_of_gradedDescent (T : Set V) (h : GradedDescent W T) :
    towerSpan W (fun t : T => mk₂ W t.val) = ⊤ := by
  let S := (towerSpan W (fun t : T => mk₂ W t.val)).comap (mk₂ W)
  have hO : O₂ W ≤ S := by
    intro y hy
    change mk₂ W y ∈ towerSpan W (fun t : T => mk₂ W t.val)
    rw [(mk₂_eq_zero_iff W).mpr hy]
    exact Submodule.zero_mem _
  have hT : Submodule.span ℂ T ≤ S := Submodule.span_le.mpr fun y hy => by
    change mk₂ W y ∈ towerSpan W (fun t : T => mk₂ W t.val)
    exact Submodule.subset_span ⟨(⟨y, hy⟩, 0), rfl⟩
  have hL (k : ℕ) {y : V} (hy : y ∈ S) : W.L (-(k : ℤ) - 1) y ∈ S := by
    exact mk₂_virWord_mem W (fun t : T => mk₂ W t.val) y hy [k]
  have hnat : ∀ N : ℕ, W.grading (N : ℤ) ≤ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      refine le_trans (h N) (sup_le (sup_le hO hT) ?_)
      apply Submodule.span_le.mpr
      rintro _ ⟨m, y, hy, rfl⟩
      apply hL
      by_cases hneg : (N : ℤ) - m - 1 < 0
      · rw [W.positivity _ hneg, Submodule.mem_bot] at hy
        rw [hy]
        exact Submodule.zero_mem _
      · have hk : (N : ℤ) - m - 1 = ((N - m - 1 : ℕ) : ℤ) := by omega
        rw [hk] at hy
        exact ih (N - m - 1) (by omega) hy
  have hS : S = ⊤ := by
    apply top_unique
    rw [← W.isInternal.submodule_iSup_eq_top]
    refine iSup_le fun N => ?_
    by_cases hN : N < 0
    · rw [W.positivity N hN]
      exact bot_le
    · simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ N)] using hnat N.toNat
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := mk₂_surjective W y
  exact show x ∈ S from hS ▸ Submodule.mem_top

/-- A version of the descent theorem with an arbitrary indexing family. -/
theorem towerSpan_of_primary (T : Set V) (hD : VirPrimaryDecomp W)
    (hP : PrimaryC2Reduction W T) :
    towerSpan W (fun t : T => mk₂ W t.val) = ⊤ :=
  towerSpan_of_gradedDescent W T (gradedDescent_of_primary W T hD hP)

/-- Two seeds in the primary reduction suffice for the exact span asked for in B4. -/
theorem twoTowers_of_primary (X : V) (hD : VirPrimaryDecomp W)
    (hP : PrimaryC2Reduction W {W.vacuum, X}) : twoTowers W X = ⊤ := by
  have h := towerSpan_of_primary W {W.vacuum, X} hD hP
  apply top_unique
  rw [← h]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨⟨t, ht⟩, n⟩, rfl⟩
  rcases ht with rfl | rfl
  · exact Submodule.subset_span ⟨Sum.inl n, rfl⟩
  · exact Submodule.subset_span ⟨Sum.inr n, rfl⟩

/-- The decomposition hypothesis is already proved for every subgroup of `Aut V₂`. -/
theorem orbifold_twoTowers_of_primary (G : Subgroup (Aut (V2m 1 le_rfl)))
    (X : (orbifold G).carrier)
    (hP : PrimaryC2Reduction (orbifoldVOA G) {(orbifoldVOA G).vacuum, X}) :
    twoTowers (orbifoldVOA G) X = ⊤ :=
  twoTowers_of_primary _ X (virPrimaryDecomp_orbifold 1 le_rfl G) hP

/-- For homogeneous `X`, the two-tower span also implies primary reduction.
Thus replacing the span by this primary statement loses no information. -/
theorem primary_of_twoTowers {X : V} {d : ℤ} (hX : X ∈ W.grading d)
    (hspan : twoTowers W X = ⊤) : PrimaryC2Reduction W {W.vacuum, X} := by
  intro N x hx
  let K := O₂ W ⊔ Submodule.span ℂ ({W.vacuum, X} : Set V) ⊔ lowerDesc W N
  have hO (y : V) (hy : y ∈ O₂ W) : piHom W N y ∈ K :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (piHom_maps_O₂ W N hy))
  have hseed (s : V) (hs : s ∈ ({W.vacuum, X} : Set V)) :
      piHom W N s ∈ K := by
    have hhom : ∃ e, s ∈ W.grading e := by
      rcases hs with rfl | rfl
      · exact ⟨0, W.vacuum_mem⟩
      · exact ⟨d, hX⟩
    obtain ⟨e, he⟩ := hhom
    by_cases h : e = N
    · subst e
      rw [piHom_of_mem W he]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hs))
    · rw [piHom_of_mem_ne W h he]
      exact Submodule.zero_mem _
  have hpow (s : V) (hs : s ∈ ({W.vacuum, X} : Set V)) (n : ℕ) :
      piHom W N ((W.L (-2) ^ n) s) ∈ K := by
    cases n with
    | zero => exact hseed s hs
    | succ n =>
      rw [pow_succ', Module.End.mul_apply]
      have he := piHom_L_neg W N 1 ((W.L (-2) ^ n) s)
      norm_num only [Nat.cast_one] at he
      rw [he]
      exact Submodule.mem_sup_right
        (Submodule.subset_span ⟨1, piHom W (N - 1 - 1) ((W.L (-2) ^ n) s),
          piHom_mem W _ _, by norm_num⟩)
  have hlift : ∀ q ∈ twoTowers W X,
      ∃ y : V, mk₂ W y = q ∧ piHom W N y ∈ K := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨n | n, rfl⟩
      · exact ⟨(W.L (-2) ^ n) W.vacuum, (exceptionalConformalEnd_pow_mk W n _).symm,
          hpow _ (by simp) n⟩
      · exact ⟨(W.L (-2) ^ n) X, (exceptionalConformalEnd_pow_mk W n _).symm,
          hpow _ (by simp) n⟩
    | zero => exact ⟨0, map_zero _, by simp⟩
    | add q r _ _ hq hr =>
      obtain ⟨y, rfl, hy⟩ := hq
      obtain ⟨z, rfl, hz⟩ := hr
      exact ⟨y + z, map_add _ _ _, by rw [map_add]; exact K.add_mem hy hz⟩
    | smul c q _ hq =>
      obtain ⟨y, rfl, hy⟩ := hq
      exact ⟨c • y, map_smul _ _ _, by rw [map_smul]; exact K.smul_mem c hy⟩
  obtain ⟨y, hy, hpy⟩ := hlift (mk₂ W x) (hspan ▸ Submodule.mem_top)
  have hxy : x - y ∈ O₂ W := (mk₂_eq_zero_iff W).mp (by rw [map_sub, hy, sub_self])
  have hp : piHom W N x ∈ K := by
    have := K.add_mem (hO _ hxy) hpy
    simpa only [map_sub, sub_add_cancel] using this
  rwa [piHom_of_mem W hx.1] at hp

theorem orbifold_twoTowers_iff_primary (G : Subgroup (Aut (V2m 1 le_rfl)))
    {X : (orbifold G).carrier} (hX : X ∈ (orbifoldVOA G).grading 36) :
    twoTowers (orbifoldVOA G) X = ⊤ ↔
      PrimaryC2Reduction (orbifoldVOA G) {(orbifoldVOA G).vacuum, X} :=
  ⟨primary_of_twoTowers _ hX, orbifold_twoTowers_of_primary G X⟩

/-- Xu's four-generator reduction and the two eliminations give the two-tower span.
The `Y` relation uses levels 100 and 64, hence powers 50 and 32. -/
theorem twoTowers_of_four (X Y Z : V) (a b : ℂ)
    (hfour : towerSpan W (fun t : ({W.vacuum, X, Y, Z} : Set V) => mk₂ W t.val) = ⊤)
    (hY : mk₂ W Y = a • (exceptionalConformalEnd W ^ 50) (mk₂ W W.vacuum) +
      b • (exceptionalConformalEnd W ^ 32) (mk₂ W X))
    (hZ : mk₂ W Z = 0) : twoTowers W X = ⊤ := by
  have hv (n : ℕ) : (exceptionalConformalEnd W ^ n) (mk₂ W W.vacuum) ∈ twoTowers W X :=
    Submodule.subset_span ⟨Sum.inl n, rfl⟩
  have hx (n : ℕ) : (exceptionalConformalEnd W ^ n) (mk₂ W X) ∈ twoTowers W X :=
    Submodule.subset_span ⟨Sum.inr n, rfl⟩
  have hbase (t : V) (ht : t ∈ ({W.vacuum, X, Y, Z} : Set V)) :
      mk₂ W t ∈ twoTowers W X := by
    rcases ht with rfl | rfl | rfl | rfl
    · exact hv 0
    · exact hx 0
    · rw [hY]
      exact Submodule.add_mem _ (Submodule.smul_mem _ a (hv 50))
        (Submodule.smul_mem _ b (hx 32))
    · rw [hZ]
      exact Submodule.zero_mem _
  apply top_unique
  rw [← hfour]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨⟨t, ht⟩, n⟩, rfl⟩
  change (exceptionalConformalEnd W ^ n) (mk₂ W t) ∈ twoTowers W X
  induction n with
  | zero => exact hbase t ht
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    rw [twoTowers_eq_towerSpan] at ih ⊢
    exact conformal_mem_towerSpan W _ ih

end VOA.Classification.COne.OrbXu
