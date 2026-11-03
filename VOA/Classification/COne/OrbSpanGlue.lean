import VOA.Classification.COne.OrbC2cSpan

/-! # OrbSpan: exact reformulations of the Dong--Jiang Virasoro span

`OrbC2c.DongJiangVirasoroSpan W u v` says that negative Virasoro words on
`{𝟙, u, v} ∪ {u₍ₙ₎u} ∪ O₂(W)` span `W`. This file proves, for an arbitrary VOA:

* `dongJiangVirasoroSpan_iff_towerSpan`: the statement is EQUIVALENT to
  "the conformal towers of `𝟙, u, v, u₍ₙ₎u` span `A₂(W) = W/C₂(W)`", i.e. `A₂(W)` is
  generated as a `ℂ[ω̄]`-module by these classes;
* `dongJiangVirasoroSpan_of_gradedDescent`: a graded Nakayama-type induction. It suffices
  that every homogeneous `x ∈ W_N` lies in `O₂ + span(seeds) + Σ_{m ≥ 1} L(-m) W_{N-m}`;
* `gradedDescent_of_primary`: that graded statement splits into a Virasoro primary
  decomposition (`VirPrimaryDecomp`) and a statement about primaries only
  (`PrimaryC2Reduction`).

All results here are glue; none of the hypotheses is asserted.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbSpan
open VOA VertexOperatorAlgebra OrbC2b OrbC2c
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- The non-`O₂` seeds of Dong--Jiang Lemma 4.2. -/
def djSeedSet (u v : V) : Set V :=
  {W.vacuum, u, v} ∪ Set.range (fun n : ℤ => W.smul u n u)

/-- The span appearing in `DongJiangVirasoroSpan`. -/
def djSpan (u v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (fun p : List ℕ × djSeeds W u v => virWord W p.1 p.2.val))

theorem dongJiangVirasoroSpan_iff_djSpan (u v : V) :
    DongJiangVirasoroSpan W u v ↔ djSpan W u v = ⊤ := Iff.rfl

theorem virWord_mem_djSpan (u v : V) (ks : List ℕ) {x : V} (hx : x ∈ djSeeds W u v) :
    virWord W ks x ∈ djSpan W u v :=
  Submodule.subset_span ⟨(ks, ⟨x, hx⟩), rfl⟩

theorem seed_mem_djSpan (u v : V) {x : V} (hx : x ∈ djSeeds W u v) : x ∈ djSpan W u v :=
  virWord_mem_djSpan W u v [] hx

theorem O₂_le_djSpan (u v : V) : O₂ W ≤ djSpan W u v := fun _ hx =>
  seed_mem_djSpan W u v (Or.inr hx)

theorem djSeedSet_subset (u v : V) : djSeedSet W u v ⊆ djSeeds W u v := fun _ hx =>
  Or.inl hx

/-- The span is stable under every negative Virasoro mode `L(-m-1)`. -/
theorem L_neg_mem_djSpan (u v : V) (m : ℕ) {s : V} (hs : s ∈ djSpan W u v) :
    W.L (-(m : ℤ) - 1) s ∈ djSpan W u v := by
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨ks, ⟨z, hz⟩⟩, rfl⟩ := hy
    exact virWord_mem_djSpan W u v (m :: ks) hz
  | zero => simp
  | add x y _ _ hx hy => simpa using (djSpan W u v).add_mem hx hy
  | smul a x _ hx => simpa using (djSpan W u v).smul_mem a hx

theorem L_neg_two_pow_eq_virWord (n : ℕ) (x : V) :
    ((W.L (-2)) ^ n) x = virWord W (List.replicate n 1) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, List.replicate_succ, virWord]
    norm_num

/-- The seed family used by the tower formulation. -/
def seedFamily (u v : V) : djSeedSet W u v → A₂ W := fun t => mk₂ W t.val

/-- **Exact reformulation.** The Dong--Jiang Virasoro span holds iff the conformal
towers of `𝟙, u, v, u₍ₙ₎u` span `A₂(W)`. -/
theorem dongJiangVirasoroSpan_iff_towerSpan (u v : V) :
    DongJiangVirasoroSpan W u v ↔ towerSpan W (seedFamily W u v) = ⊤ := by
  constructor
  · intro h
    have hbase (x : V) (hx : x ∈ djSeeds W u v) : mk₂ W x ∈ towerSpan W (seedFamily W u v) := by
      rcases hx with hx | hx
      · exact Submodule.subset_span ⟨(⟨x, hx⟩, 0), rfl⟩
      · rw [(mk₂_eq_zero_iff W).mpr hx]; exact Submodule.zero_mem _
    have hall (x : V) : mk₂ W x ∈ towerSpan W (seedFamily W u v) := by
      have hx : x ∈ djSpan W u v := by rw [show djSpan W u v = ⊤ from h]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨ks, ⟨z, hz⟩⟩, rfl⟩ := hy
        exact mk₂_virWord_mem W _ z (hbase z hz) ks
      | zero => simp
      | add x y _ _ hx hy => simpa using (towerSpan W _).add_mem hx hy
      | smul a x _ hx => simpa using (towerSpan W _).smul_mem a hx
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := mk₂_surjective W y
    exact hall x
  · intro h
    change djSpan W u v = ⊤
    have hmap : towerSpan W (seedFamily W u v) ≤ (djSpan W u v).map (mk₂ W) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨t, n⟩, rfl⟩
      refine ⟨((W.L (-2)) ^ n) t.val, ?_, ?_⟩
      · rw [L_neg_two_pow_eq_virWord]
        exact virWord_mem_djSpan W u v _ (djSeedSet_subset W u v t.2)
      · simp only [seedFamily]
        exact (exceptionalConformalEnd_pow_mk W n t.val).symm
    have htop : (djSpan W u v).map (mk₂ W) = ⊤ := top_unique (h ▸ hmap)
    have hker : LinearMap.ker (mk₂ W) ≤ djSpan W u v := by
      intro x hx
      exact O₂_le_djSpan W u v ((mk₂_eq_zero_iff W).mp hx)
    rw [← Submodule.comap_map_eq_self hker, htop, Submodule.comap_top]

/-- The lower Virasoro descendants of weight `N`: `Σ_{m ≥ 1} L(-m) W_{N-m}`. -/
def lowerDesc (N : ℤ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ m : ℕ, ∃ y ∈ W.grading (N - m - 1), x = W.L (-(m : ℤ) - 1) y}

/-- Graded Nakayama-type input: each weight space lies in `O₂ + span T + lower descendants`. -/
def GradedDescent (T : Set V) : Prop :=
  ∀ N : ℤ, W.grading N ≤ O₂ W ⊔ Submodule.span ℂ T ⊔ lowerDesc W N

/-- **Graded induction.** The graded descent with the Dong--Jiang seeds implies
the Dong--Jiang Virasoro span. -/
theorem dongJiangVirasoroSpan_of_gradedDescent (u v : V)
    (h : GradedDescent W (djSeedSet W u v)) : DongJiangVirasoroSpan W u v := by
  change djSpan W u v = ⊤
  have hT : Submodule.span ℂ (djSeedSet W u v) ≤ djSpan W u v :=
    Submodule.span_le.mpr fun x hx => seed_mem_djSpan W u v (djSeedSet_subset W u v hx)
  have hnat : ∀ N : ℕ, W.grading (N : ℤ) ≤ djSpan W u v := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      refine le_trans (h N) (sup_le (sup_le (O₂_le_djSpan W u v) hT) ?_)
      apply Submodule.span_le.mpr
      rintro x ⟨m, y, hy, rfl⟩
      apply L_neg_mem_djSpan
      by_cases hneg : (N : ℤ) - m - 1 < 0
      · rw [W.positivity _ hneg, Submodule.mem_bot] at hy
        rw [hy]; exact Submodule.zero_mem _
      · have hk : (N : ℤ) - m - 1 = ((N - m - 1 : ℕ) : ℤ) := by omega
        rw [hk] at hy
        exact ih (N - m - 1) (by omega) hy
  have hall : ∀ N : ℤ, W.grading N ≤ djSpan W u v := by
    intro N
    by_cases hN : N < 0
    · rw [W.positivity N hN]; exact bot_le
    · have := hnat N.toNat
      rwa [Int.toNat_of_nonneg (by omega)] at this
  apply top_unique
  rw [← W.isInternal.submodule_iSup_eq_top]
  exact iSup_le hall

/-- Virasoro primaries of weight `N`. -/
def prim (N : ℤ) : Submodule ℂ V :=
  W.grading N ⊓ ⨅ m : ℕ, LinearMap.ker (W.L ((m : ℤ) + 1))

theorem mem_prim {N : ℤ} {x : V} :
    x ∈ prim W N ↔ x ∈ W.grading N ∧ ∀ m : ℕ, W.L ((m : ℤ) + 1) x = 0 := by
  simp [prim, Submodule.mem_iInf]

/-- Every weight space is spanned by primaries and lower Virasoro descendants
(complete reducibility as a highest-weight Virasoro module, in its weakest form). -/
def VirPrimaryDecomp : Prop := ∀ N : ℤ, W.grading N ≤ prim W N ⊔ lowerDesc W N

/-- Every primary lies in `O₂ + span T + lower descendants`. -/
def PrimaryC2Reduction (T : Set V) : Prop :=
  ∀ N : ℤ, prim W N ≤ O₂ W ⊔ Submodule.span ℂ T ⊔ lowerDesc W N

theorem gradedDescent_of_primary (T : Set V) (hD : VirPrimaryDecomp W)
    (hG : PrimaryC2Reduction W T) : GradedDescent W T := fun N =>
  le_trans (hD N) (sup_le (hG N) le_sup_right)

/-- **Glue.** Primary decomposition plus the primary reduction give the Dong--Jiang span. -/
theorem dongJiangVirasoroSpan_of_primary (u v : V) (hD : VirPrimaryDecomp W)
    (hG : PrimaryC2Reduction W (djSeedSet W u v)) : DongJiangVirasoroSpan W u v :=
  dongJiangVirasoroSpan_of_gradedDescent W u v (gradedDescent_of_primary W _ hD hG)

end VOA.Classification.COne.OrbSpan
