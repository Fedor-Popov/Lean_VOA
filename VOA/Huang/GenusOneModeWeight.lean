import VOA.Huang.GenusOneModeLinear

/-! # The module square-weight commutator

Port of the locally finite operator calculation in `VOA.Modularity.SqModeWeight`.
The scalar coefficient collapses are reused; every operator here acts on the actual
ordinary module. Source: Zhu's exponential coordinate change, Miyamoto §2.
-/
namespace VOA.Huang.GenusOne.SquareModule
open VOA
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

noncomputable def roundL (A : OrdVModule W M) (n : ℤ) : Module.End ℂ M :=
  mode (A.YM W.conformalVector) (n + 1)

theorem roundL_mode_comm (A : OrdVModule W M) (a : V) (r : ℕ) (i : ℤ) (v : M) :
    roundL A r (mode (A.YM a) i v) - mode (A.YM a) i (roundL A r v) =
      ∑ ℓ ∈ Finset.range (r + 2), gBinom ((r + 1 : ℕ) : ℤ) ℓ •
        mode (A.YM (W.L ((ℓ : ℤ) - 1) a)) ((r + 1 : ℕ) + i - (ℓ : ℕ)) v := by
  rw [roundL, mode_commutator]
  have hs : Function.support (fun l : ℤ => cbz ((r : ℤ) + 1) l •
      mode (A.YM (W.smul W.conformalVector l a)) ((r : ℤ) + 1 + i - l) v)
      ⊆ (Finset.Ico 0 ((r : ℤ) + 2) : Finset ℤ) := by
    intro l hl
    simp only [Function.mem_support, Finset.mem_coe, Finset.mem_Ico] at hl ⊢
    by_contra hn
    apply hl
    by_cases hneg : l < 0
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · rw [cbz_eq_zero_of_lt (by omega) (by omega), zero_smul]
  rw [finsum_eq_finsetSum_of_support_subset _ hs]
  symm
  apply Finset.sum_bij (fun (l : ℕ) _ => (l : ℤ))
  · intro l hl
    simp only [Finset.mem_Ico]
    rw [Finset.mem_range] at hl
    omega
  · intro l hl m hm h
    exact_mod_cast h
  · intro l hl
    simp only [Finset.mem_Ico] at hl
    exact ⟨l.toNat, Finset.mem_range.mpr (by omega), by omega⟩
  · intro l hl
    rw [cbz_apply_nonneg _ (by omega)]
    simp only [Int.toNat_natCast]
    congr 2; simp [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]


theorem vSqZ_eq_nat_finsum (A : OrdVModule W M) (a : V) (k : ℕ) (j : ℤ) (v : M) :
    sqAct A a k j v = ∑ᶠ n : ℕ,
      sqBracketCoeffZ k j (j + (n : ℤ)) • mode (A.YM a) (j + (n : ℤ)) v := by
  rw [sqAct_apply, finsum_int_ge_eq_nat_shift]
  intro i hi
  rw [sqBracketCoeffZ_of_lt k hi, zero_smul]

/-- `L[0]` written as its natural Virasoro tail `Σ_{r≥0} d_r L_r`. -/
theorem Lsq_zero_eq_nat_finsum (A : OrdVModule W M) (v : M) :
    sqL A 0 v = ∑ᶠ r : ℕ,
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) • roundL A (r : ℤ) v := by
  simp only [sqL, show (0 : ℤ) ≠ -2 by norm_num, if_false, zero_smul, sub_zero]
  rw [vSqZ_eq_nat_finsum]
  apply finsum_congr
  intro r
  congr 2 <;> simp [roundL, Nat.cast_add, add_comm]

/-! ## The locally finite commutator expansion -/

theorem dLNat_support_finite (A : OrdVModule W M) (v : M) :
    (Function.support fun r : ℕ ↦
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) • roundL A (r : ℤ) v).Finite := by
  have h := (sqAct_support_finite A W.conformalVector 2 1 v).preimage
    (f := fun r : ℕ => (r : ℤ) + 1) (by
      intro a b hab
      exact_mod_cast (add_right_cancel hab : (a : ℤ) = b) :
      Function.Injective fun r : ℕ => (r : ℤ) + 1).injOn
  simpa only [Set.mem_preimage, Nat.cast_add, Nat.cast_one, roundL] using h

theorem sqNat_support_finite (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    (Function.support fun n : ℕ ↦
      sqBracketCoeffZ k j (j + (n : ℤ)) • mode (A.YM a) (j + (n : ℤ)) v).Finite := by
  have h := (sqAct_support_finite A a k j v).preimage
    (f := fun n : ℕ ↦ j + (n : ℤ)) (by
      intro r s hrs
      have : (r : ℤ) = (s : ℤ) := add_left_cancel hrs
      exact_mod_cast this : Function.Injective fun n : ℕ ↦ j + (n : ℤ)).injOn
  refine h.subset fun n hn ↦ ?_
  simpa only [Set.mem_preimage] using hn

/-- The composite `L[0] ∘ a[j]` as a natural double sum. -/
theorem Lsq_zero_vSqZ_comp (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    sqL A 0 (sqAct A a k j v) = ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v) := by
  rw [vSqZ_eq_nat_finsum,
    map_finsum (sqL A 0) (sqNat_support_finite A a k j v)]
  refine finsum_congr fun n ↦ ?_
  rw [map_smul, Lsq_zero_eq_nat_finsum,
    smul_finsum' _ (dLNat_support_finite A (mode (A.YM a) (j + (n : ℤ)) v))]
  refine finsum_congr fun r ↦ ?_
  rw [smul_smul, mul_comm]

/-- Joint finiteness for the `a[j] ∘ L[0]` composite. -/
theorem sqLJoint_support_finite (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    (Function.support fun p : ℕ × ℕ ↦
      (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (p.2 : ℤ))) •
          mode (A.YM a) (j + (p.2 : ℤ)) (roundL A (p.1 : ℤ) v)).Finite := by
  refine Set.Finite.subset
    ((dLNat_support_finite A v).biUnion fun r _ ↦
      (sqNat_support_finite A a k j (roundL A (r : ℤ) v)).image fun n ↦ (r, n)) ?_
  intro p hp
  simp only [Function.mem_support, ne_eq, smul_ne_zero_iff, mul_ne_zero_iff] at hp
  obtain ⟨⟨hdr, hcn⟩, hvec⟩ := hp
  simp only [Set.mem_iUnion, Set.mem_image, Function.mem_support, ne_eq,
    smul_ne_zero_iff, exists_prop]
  refine ⟨p.1, ⟨hdr, fun hz ↦ hvec (by rw [hz, map_zero])⟩, p.2, ?_, rfl⟩
  exact ⟨hcn, hvec⟩

/-- The composite `a[j] ∘ L[0]`, put in the same `(n,r)` order. -/
theorem vSqZ_Lsq_zero_comp (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    sqAct A a k j (sqL A 0 v) = ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v) := by
  have hraw : sqAct A a k j (sqL A 0 v) = ∑ᶠ r : ℕ, ∑ᶠ n : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v) := by
    rw [Lsq_zero_eq_nat_finsum,
      map_finsum (sqAct A a k j) (dLNat_support_finite A v)]
    refine finsum_congr fun r ↦ ?_
    rw [map_smul, vSqZ_eq_nat_finsum,
      smul_finsum' _ (sqNat_support_finite A a k j (roundL A (r : ℤ) v))]
    refine finsum_congr fun n ↦ ?_
    rw [smul_smul]
  rw [hraw]
  exact (finsum_finsum_comm_sq
    (fun r n : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v))
    (sqLJoint_support_finite A a k j v)).symm

/-- The square/ordinary commutator expanded as a locally finite natural double sum of ordinary
Virasoro commutators. -/
theorem Lsq_zero_vSqZ_comm_double (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    sqL A 0 (sqAct A a k j v) - sqAct A a k j (sqL A 0 v) =
      ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            (roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v)
              - mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)) := by
  rw [Lsq_zero_vSqZ_comp, vSqZ_Lsq_zero_comp]
  have hout1 : (Function.support fun n : ℕ ↦ ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v)).Finite := by
    refine (sqNat_support_finite A a k j v).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hzero
    have heq : (∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v)) =
        sqBracketCoeffZ k j (j + (n : ℤ)) •
          sqL A 0 (mode (A.YM a) (j + (n : ℤ)) v) := by
      rw [Lsq_zero_eq_nat_finsum,
        smul_finsum' _ (dLNat_support_finite A (mode (A.YM a) (j + (n : ℤ)) v))]
      refine finsum_congr fun r ↦ ?_
      rw [smul_smul]
      congr 1
      ring
    apply hn
    rw [heq, ← map_smul, hzero, map_zero]
  have hout2 : (Function.support fun n : ℕ ↦ ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)).Finite := by
    refine (sqNat_support_finite A a k j (sqL A 0 v)).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hzero
    have hfinmap : (Function.support fun r : ℕ ↦
        sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
          mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)).Finite := by
      refine (dLNat_support_finite A v).subset ?_
      intro r hr
      simp only [Function.mem_support, ne_eq] at hr ⊢
      intro hz
      apply hr
      have hz' := congrArg (fun x ↦ mode (A.YM a) (j + (n : ℤ)) x) hz
      simpa only [map_smul, map_zero] using hz'
    have heq : (∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)) =
        sqBracketCoeffZ k j (j + (n : ℤ)) •
          mode (A.YM a) (j + (n : ℤ)) (sqL A 0 v) := by
      rw [Lsq_zero_eq_nat_finsum,
        map_finsum (mode (A.YM a) (j + (n : ℤ))) (dLNat_support_finite A v)]
      simp_rw [map_smul]
      rw [smul_finsum' _ hfinmap]
      refine finsum_congr fun r ↦ ?_
      rw [smul_smul]
      congr 1
      ring
    exact hn (heq.trans hzero)
  rw [← finsum_sub_distrib hout1 hout2]
  refine finsum_congr fun n ↦ ?_
  have hin1 : (Function.support fun r : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v)).Finite := by
    refine (dLNat_support_finite A (mode (A.YM a) (j + (n : ℤ)) v)).subset ?_
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro hbase
    apply hr
    calc
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v)
        = sqBracketCoeffZ k j (j + (n : ℤ)) •
            (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
              roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v)) := by
            rw [smul_smul]
            congr 1
            ring
      _ = 0 := by rw [hbase, smul_zero]
  have hin2 : (Function.support fun r : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)).Finite := by
    refine (dLNat_support_finite A v).subset ?_
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro hbase
    apply hr
    have hmap : sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
        mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v) = 0 := by
      rw [← map_smul, hbase, map_zero]
    calc
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (n : ℤ))) •
            mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)
        = sqBracketCoeffZ k j (j + (n : ℤ)) •
            (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
              mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)) := by
            rw [smul_smul]
            congr 1
            ring
      _ = 0 := by rw [hmap, smul_zero]
  rw [← finsum_sub_distrib hin1 hin2]
  refine finsum_congr fun r ↦ ?_
  rw [smul_sub]

/-- The ordinary commutator split into the combined translation/weight term and the strictly
positive Virasoro tail. -/
theorem L_nat_mode_comm_split (A : OrdVModule W M) {a : V} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (r : ℕ) (i : ℤ) (v : M) :
    roundL A (r : ℤ) (mode (A.YM a) i v) - mode (A.YM a) i (roundL A (r : ℤ) v) =
      ((k : ℂ) * ((r : ℂ) + 1) - ((r : ℂ) + (i : ℂ) + 1)) •
          mode (A.YM a) ((r : ℤ) + i) v
        + ∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
            mode (A.YM (W.L ((q + 1 : ℕ) : ℤ) a))
              ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
  have h := roundL_mode_comm A a r i v
  have htail : (∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
      mode (A.YM (W.L ((q + 1 : ℕ) : ℤ) a))
        ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v) =
      ∑ q ∈ Finset.range r, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        mode (A.YM (W.L ((q + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
    apply finsum_eq_finsetSum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hqr
    push Not at hqr
    apply hq
    rw [gBinom_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]
  rw [htail, h]
  rw [Finset.sum_range_succ' (n := r + 1),
    Finset.sum_range_succ' (f := fun ℓ : ℕ ↦
      gBinom ((r + 1 : ℕ) : ℤ) (ℓ + 1) •
        mode (A.YM (W.L (((ℓ + 1 : ℕ) : ℤ) - 1) a))
          ((r + 1 : ℕ) + i - (ℓ + 1 : ℕ)) v) (n := r)]
  have hg0 : gBinom ((r + 1 : ℕ) : ℤ) 0 = 1 := gBinom_zero _
  have hg1 : gBinom ((r + 1 : ℕ) : ℤ) 1 = ((r : ℂ) + 1) := by
    rw [gBinom_natCast]
    simp
  rw [hg0, hg1, one_smul,
    show (((0 : ℕ) : ℤ) - 1) = -1 by norm_num,
    show (((1 : ℕ) : ℤ) - 1) = 0 by norm_num]
  have hcastL : ∀ q : ℕ, ((((q + 1 : ℕ) + 1 : ℕ) : ℤ) - 1)
      = ((q + 1 : ℕ) : ℤ) := by intro q; push_cast; ring
  have hcastI : ∀ q : ℕ, ((r + 1 : ℕ) : ℤ) + i - ((q + 1 : ℕ) : ℤ)
      = (r : ℤ) + i - q := by intro q; push_cast; ring
  simp_rw [hcastL, hcastI]
  simp only [Nat.cast_zero, sub_zero]
  rw [show mode (A.YM (W.L (-1) a)) (((r + 1 : ℕ) : ℤ) + i) v =
      (-((((r + 1 : ℕ) : ℤ) + i) : ℂ)) • mode (A.YM a) ((r : ℤ) + i) v by
    simpa only [WeakModule.act, Int.cast_add, Int.cast_natCast, PreVertexAlgebra.smul_def,
      show (((r + 1 : ℕ) : ℤ) + i - 1)
      = (r : ℤ) + i by push_cast; ring] using
        act_T_covariance A.toWeakModule a (((r + 1 : ℕ) : ℤ) + i) v,
    W.L_zero_grading a ha, map_smul, mode_smul, LinearMap.smul_apply,
    smul_smul]
  have htailsame : (∑ x ∈ Finset.range r,
      gBinom ((r + 1 : ℕ) : ℤ) (x + 1 + 1) •
        mode (A.YM (W.L ((x + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((x + 1 : ℕ) : ℤ)) v) =
      ∑ q ∈ Finset.range r, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        mode (A.YM (W.L ((q + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
    apply Finset.sum_congr rfl
    intro q _
    congr 3
  rw [htailsame]
  push_cast
  module

/-! ## Collapse of the vector-valued commutator pieces -/

theorem modeNat_support_finite (A : OrdVModule W M) (a : V) (j : ℤ) (v : M) :
    (Function.support fun t : ℕ ↦ mode (A.YM a) (j + (t : ℤ)) v).Finite := by
  obtain ⟨R, hR⟩ := A.truncation a v
  refine Set.Finite.subset (Set.finite_Iio ((R - j).toNat + 1)) ?_
  intro t ht
  simp only [Function.mem_support, ne_eq] at ht
  rw [Set.mem_Iio]
  by_contra hlarge
  push Not at hlarge
  apply ht
  apply hR
  have hself := Int.self_le_toNat (R - j)
  omega

/-- The complete low (`L₋₁` plus `L₀`) double sum collapses to
`(k-j-1)a[j]v`. -/
theorem sqLow_comm_collapse (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    (∑ᶠ p : ℕ × ℕ,
      (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (p.2 : ℤ))
        * ((k : ℂ) * ((p.1 : ℂ) + 1)
          - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
            mode (A.YM a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v) =
      ((k : ℂ) - (j : ℂ) - 1) • sqAct A a k j v := by
  rw [sqLowPair_vector_collapse k j
    (fun t : ℕ ↦ mode (A.YM a) (j + (t : ℤ)) v)
    (modeNat_support_finite A a j v), vSqZ_eq_nat_finsum,
    smul_finsum' _ (sqNat_support_finite A a k j v)]
  refine finsum_congr fun t ↦ ?_
  rw [smul_smul]

/-- For fixed `Q≥1`, the reindexed positive-tail double sum collapses to
`d_Q·(L_Qa)[j]v`. -/
theorem sqPositive_comm_collapse (A : OrdVModule W M) {a : V}
    {Q k : ℕ} (hQ : 1 ≤ Q) (hQk : Q ≤ k) (j : ℤ) (v : M) :
    (∑ᶠ p : ℕ × ℕ,
      ((sqBracketCoeffZ 2 1 ((p.1 + Q + 1 : ℕ) : ℤ)
        * gBinom ((p.1 + Q + 1 : ℕ) : ℤ) (Q + 1))
        * sqBracketCoeffZ k j (j + (p.2 : ℤ))) •
          mode (A.YM (W.L (Q : ℤ) a))
            (j + ((p.1 + p.2 : ℕ) : ℤ)) v) =
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        sqAct A (W.L (Q : ℤ) a) (k - Q) j v := by
  rw [sqPositiveTail_vector_collapse hQ hQk j
    (fun t : ℕ ↦ mode (A.YM (W.L (Q : ℤ) a)) (j + (t : ℤ)) v)
    (modeNat_support_finite A (W.L (Q : ℤ) a) j v),
    vSqZ_eq_nat_finsum,
    smul_finsum' _ (sqNat_support_finite A (W.L (Q : ℤ) a) (k - Q) j v)]
  refine finsum_congr fun t ↦ ?_
  rw [smul_smul]

/-- The low commutator summand, indexed as `(n,r)` for the nested square-mode expansion. -/
noncomputable def sqLowCommTerm (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) (p : ℕ × ℕ) : M :=
  (sqBracketCoeffZ 2 1 ((p.2 + 1 : ℕ) : ℤ)
    * sqBracketCoeffZ k j (j + (p.1 : ℤ))
    * ((k : ℂ) * ((p.2 : ℂ) + 1)
      - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
        mode (A.YM a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v

/-- The positive commutator summand before the shift `r=Q+s`, indexed as `(n,r)`. -/
noncomputable def sqPositiveCommTerm (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) (Q : ℕ) (p : ℕ × ℕ) : M :=
  ((sqBracketCoeffZ 2 1 ((p.2 + 1 : ℕ) : ℤ)
    * sqBracketCoeffZ k j (j + (p.1 : ℤ)))
    * gBinom ((p.2 + 1 : ℕ) : ℤ) (Q + 1)) •
      mode (A.YM (W.L (Q : ℤ) a))
        (j + ((p.1 + (p.2 - Q) : ℕ) : ℤ)) v

/-- The same positive summand after `r=Q+s`, indexed as `(s,n)`. -/
noncomputable def sqPositiveReindexedTerm (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) (Q : ℕ) (p : ℕ × ℕ) : M :=
  ((sqBracketCoeffZ 2 1 ((p.1 + Q + 1 : ℕ) : ℤ)
    * gBinom ((p.1 + Q + 1 : ℕ) : ℤ) (Q + 1))
    * sqBracketCoeffZ k j (j + (p.2 : ℤ))) •
      mode (A.YM (W.L (Q : ℤ) a))
        (j + ((p.1 + p.2 : ℕ) : ℤ)) v

theorem sqLowCommTerm_support_finite (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    (Function.support (sqLowCommTerm A a k j v)).Finite := by
  let g : ℕ × ℕ → M := fun p ↦
    (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
      * sqBracketCoeffZ k j (j + (p.2 : ℤ))
      * ((k : ℂ) * ((p.1 : ℂ) + 1)
        - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
          mode (A.YM a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v
  have h : (Function.support g).Finite := support_pair_smul_add_finite
    (fun p : ℕ × ℕ ↦ sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
      * sqBracketCoeffZ k j (j + (p.2 : ℤ))
      * ((k : ℂ) * ((p.1 : ℂ) + 1)
        - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1)))
    (fun t : ℕ ↦ mode (A.YM a) (j + (t : ℤ)) v)
    (modeNat_support_finite A a j v)
  have hswap := h.preimage (f := Prod.swap) (Function.Injective.injOn Prod.swap_injective)
  refine hswap.subset fun p hp ↦ ?_
  change g (Prod.swap p) ≠ 0
  rcases p with ⟨n, r⟩
  simpa only [g, sqLowCommTerm, Prod.swap_prod_mk, Prod.fst, Prod.snd,
    Nat.add_comm] using hp

theorem sqPositiveReindexedTerm_support_finite (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) (Q : ℕ) :
    (Function.support (sqPositiveReindexedTerm A a k j v Q)).Finite := by
  exact support_pair_smul_add_finite _ _
    (modeNat_support_finite A (W.L (Q : ℤ) a) j v)

theorem sqPositiveCommTerm_support_finite (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) (Q : ℕ) :
    (Function.support (sqPositiveCommTerm A a k j v Q)).Finite := by
  let φ : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, Q + p.1)
  have hR := sqPositiveReindexedTerm_support_finite A a k j v Q
  refine Set.Finite.subset (hR.image φ) ?_
  intro p hp
  have hrQ : Q ≤ p.2 := by
    by_contra hr
    push Not at hr
    rw [Function.mem_support] at hp
    apply hp
    rw [sqPositiveCommTerm, gBinom_natCast,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_smul]
  let s := p.2 - Q
  have hs : Q + s = p.2 := Nat.add_sub_of_le hrQ
  have hterm : sqPositiveReindexedTerm A a k j v Q (s, p.1) ≠ 0 := by
    change sqPositiveCommTerm A a k j v Q p ≠ 0 at hp
    simpa only [sqPositiveCommTerm, sqPositiveReindexedTerm, Prod.fst, Prod.snd,
      hs, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      mul_assoc, mul_comm, mul_left_comm] using hp
  exact ⟨(s, p.1), hterm, by ext <;> simp [φ, hs]⟩

/-- Reindex the full fixed-`Q` positive contribution by `r=Q+s`, then apply the positive scalar
collapse. -/
theorem sqPositiveCommTerm_collapse (A : OrdVModule W M) {a : V}
    {Q k : ℕ} (hQ : 1 ≤ Q) (hQk : Q ≤ k) (j : ℤ) (v : M) :
    (∑ᶠ p : ℕ × ℕ, sqPositiveCommTerm A a k j v Q p) =
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        sqAct A (W.L (Q : ℤ) a) (k - Q) j v := by
  let φ : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, Q + p.1)
  have hinj : Function.Injective φ := by
    intro p q hpq
    apply Prod.ext
    · have := congrArg Prod.snd hpq
      dsimp only [φ] at this
      omega
    · have := congrArg Prod.fst hpq
      exact this
  have hsub : Function.support (sqPositiveCommTerm A a k j v Q) ⊆ Set.range φ := by
    intro p hp
    have hrQ : Q ≤ p.2 := by
      by_contra hr
      push Not at hr
      rw [Function.mem_support] at hp
      apply hp
      rw [sqPositiveCommTerm, gBinom_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_smul]
    exact ⟨(p.2 - Q, p.1), by ext <;> simp [φ, Nat.add_sub_of_le hrQ]⟩
  rw [← finsum_mem_of_support_subset_sq
      (sqPositiveCommTerm A a k j v Q) _ hsub,
    finsum_mem_range hinj]
  have hreindex : ∀ p : ℕ × ℕ,
      sqPositiveCommTerm A a k j v Q (φ p) =
        sqPositiveReindexedTerm A a k j v Q p := by
    rintro ⟨s, n⟩
    simp only [φ, sqPositiveCommTerm, sqPositiveReindexedTerm,
      Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_assoc, mul_comm, mul_left_comm]
  rw [finsum_congr hreindex]
  exact sqPositive_comm_collapse A hQ hQk j v

theorem sqLowCommTerm_collapse (A : OrdVModule W M) (a : V)
    (k : ℕ) (j : ℤ) (v : M) :
    (∑ᶠ p : ℕ × ℕ, sqLowCommTerm A a k j v p) =
      ((k : ℂ) - (j : ℂ) - 1) • sqAct A a k j v := by
  rw [← finsum_comp_equiv (Equiv.prodComm ℕ ℕ)]
  have heq : ∀ p : ℕ × ℕ,
      sqLowCommTerm A a k j v ((Equiv.prodComm ℕ ℕ) p) =
        (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
          * sqBracketCoeffZ k j (j + (p.2 : ℤ))
          * ((k : ℂ) * ((p.1 : ℂ) + 1)
            - ((j : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
              mode (A.YM a) (j + ((p.1 + p.2 : ℕ) : ℤ)) v := by
    rintro ⟨r, n⟩
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, sqLowCommTerm, Nat.add_comm]
  rw [finsum_congr heq]
  exact sqLow_comm_collapse A a k j v

/-! ## Reassembly as the square mode of `L[0]a` -/

/-- Every natural Virasoro descendant is interpreted by the linearly extended square mode with
its correct ordinary weight, including the zero region `Q>k`. -/
theorem sqMode_L_nat_of_mem_grading (A : OrdVModule W M) {a : V} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (Q : ℕ) (j : ℤ) :
    sqMode A j (W.L (Q : ℤ) a) = sqAct A (W.L (Q : ℤ) a) (k - Q) j := by
  by_cases hQk : Q ≤ k
  · have hmem := L_mem_grading W ha (Q : ℤ)
    have hgrade : W.L (Q : ℤ) a ∈ W.grading ((k - Q : ℕ) : ℤ) := by
      convert hmem using 1
      rw [Nat.cast_sub hQk]
    simpa using sqMode_of_mem_grading A hgrade j
  · have hzero := L_nat_eq_zero_of_lt W ha (by omega : k < Q)
    rw [hzero, map_zero, sqAct_zero_left]

/-- The square mode of `L[0]a` is the locally finite sum of the square modes of its ordinary
Virasoro descendants. -/
theorem sqMode_Lsq_zero_of_mem_grading (A : OrdVModule W M) {a : V} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) :
    sqMode A j (Lsq W 0 a) = ∑ᶠ Q : ℕ,
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        sqAct A (W.L (Q : ℤ) a) (k - Q) j := by
  rw [VOA.Lsq_zero_eq_nat_finsum,
    map_finsum (sqMode A j) (VOA.dLNat_support_finite W a)]
  refine finsum_congr fun Q ↦ ?_
  rw [map_smul, sqMode_L_nat_of_mem_grading A ha]

/-- The full homogeneous commutator after the finite Borcherds sum has been split and regrouped. -/
theorem Lsq_zero_vSqZ_comm_collapsed (A : OrdVModule W M) {a : V} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) (v : M) :
    sqL A 0 (sqAct A a k j v) - sqAct A a k j (sqL A 0 v) =
      ((k : ℂ) - (j : ℂ) - 1) • sqAct A a k j v
        + ∑ Q ∈ Finset.range k,
            sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
              sqAct A (W.L ((Q + 1 : ℕ) : ℤ) a) (k - (Q + 1)) j v := by
  rw [Lsq_zero_vSqZ_comm_double]
  let H : ℕ × ℕ → M := fun p ↦ sqLowCommTerm A a k j v p
    + ∑ Q ∈ Finset.range k, sqPositiveCommTerm A a k j v (Q + 1) p
  have hterm : ∀ n r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffZ k j (j + (n : ℤ))) •
          (roundL A (r : ℤ) (mode (A.YM a) (j + (n : ℤ)) v)
            - mode (A.YM a) (j + (n : ℤ)) (roundL A (r : ℤ) v)) = H (n, r) := by
    intro n r
    rw [L_nat_mode_comm_split A ha r (j + (n : ℤ)) v, smul_add]
    have htail : (∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        mode (A.YM (W.L ((q + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + (j + (n : ℤ)) - ((q + 1 : ℕ) : ℤ)) v) =
        ∑ q ∈ Finset.range k, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
          mode (A.YM (W.L ((q + 1 : ℕ) : ℤ) a))
            ((r : ℤ) + (j + (n : ℤ)) - ((q + 1 : ℕ) : ℤ)) v := by
      apply finsum_eq_finsetSum_of_support_subset
      intro q hq
      simp only [Function.mem_support, ne_eq] at hq
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hqk
      push Not at hqk
      exact hq (by rw [L_nat_eq_zero_of_lt W ha (by omega : k < q + 1), map_zero,
        mode_zero, LinearMap.zero_apply, smul_zero])
    rw [htail, Finset.smul_sum]
    change _ = sqLowCommTerm A a k j v (n, r)
      + ∑ Q ∈ Finset.range k, sqPositiveCommTerm A a k j v (Q + 1) (n, r)
    congr 1
    · simp only [sqLowCommTerm, smul_smul]
      have hidx : (r : ℤ) + (j + (n : ℤ)) = j + ((n + r : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hidx]
      congr 1
      push_cast
      ring
    · apply Finset.sum_congr rfl
      intro Q hQ
      by_cases hQr : Q + 1 ≤ r
      · have hidx : (r : ℤ) + (j + (n : ℤ)) - ((Q + 1 : ℕ) : ℤ) =
            j + ((n + (r - (Q + 1)) : ℕ) : ℤ) := by
          push_cast [hQr]
          ring
        simp only [sqPositiveCommTerm, smul_smul]
        rw [hidx]
      · have hbin : gBinom ((r + 1 : ℕ) : ℤ) (Q + 1 + 1) = 0 := by
          rw [gBinom_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        rw [hbin, zero_smul, smul_zero, sqPositiveCommTerm, hbin, mul_zero, zero_smul]
  simp_rw [hterm]
  have hposUnion : (Function.support fun p : ℕ × ℕ ↦
      ∑ Q ∈ Finset.range k, sqPositiveCommTerm A a k j v (Q + 1) p).Finite := by
    refine Set.Finite.subset
      ((Finset.range k).finite_toSet.biUnion fun Q _ ↦
        sqPositiveCommTerm_support_finite A a k j v (Q + 1)) ?_
    intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    obtain ⟨Q, hQ, hQne⟩ : ∃ Q ∈ Finset.range k,
        sqPositiveCommTerm A a k j v (Q + 1) p ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hp (Finset.sum_eq_zero fun Q hQ ↦ hnone Q hQ)
    rw [Set.mem_iUnion]
    refine ⟨Q, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hQ, hQne⟩
  have hH : (Function.support H).Finite := by
    refine Set.Finite.subset
      ((sqLowCommTerm_support_finite A a k j v).union hposUnion) ?_
    intro p hp
    by_cases hlow : sqLowCommTerm A a k j v p = 0
    · right
      change (∑ Q ∈ Finset.range k,
        sqPositiveCommTerm A a k j v (Q + 1) p) ≠ 0
      intro hpos
      change H p ≠ 0 at hp
      exact hp (by simp only [H, hlow, hpos, add_zero])
    · left
      exact hlow
  rw [← finsum_curry H hH]
  change (∑ᶠ p : ℕ × ℕ,
      (sqLowCommTerm A a k j v p
        + ∑ Q ∈ Finset.range k, sqPositiveCommTerm A a k j v (Q + 1) p)) = _
  rw [finsum_add_distrib (sqLowCommTerm_support_finite A a k j v) hposUnion,
    sqLowCommTerm_collapse,
    finsum_sum_comm (Finset.range k)
      (fun p Q ↦ sqPositiveCommTerm A a k j v (Q + 1) p)
      (fun Q _ ↦ sqPositiveCommTerm_support_finite A a k j v (Q + 1))]
  apply congrArg (fun z ↦ ((k : ℂ) - (j : ℂ) - 1) • sqAct A a k j v + z)
  apply Finset.sum_congr rfl
  intro Q hQ
  exact sqPositiveCommTerm_collapse A (by omega) (by rw [Finset.mem_range] at hQ; omega) j v

/-! ## The `L[0]` commutator -/

/-- On an ordinary-homogeneous input, the square mode of `L[0]a` is the scalar weight term plus
the same positive Virasoro tail which occurs in the collapsed commutator. -/
theorem sqMode_Lsq_zero_of_mem_grading_explicit (A : OrdVModule W M)
    {a : V} {k : ℕ} (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) (v : M) :
    sqMode A j (Lsq W 0 a) v =
      (k : ℂ) • sqAct A a k j v
        + ∑ Q ∈ Finset.range k,
            sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
              sqAct A (W.L ((Q + 1 : ℕ) : ℤ) a) (k - (Q + 1)) j v := by
  have hmap : sqMode A j (Lsq W 0 a) =
      (k : ℂ) • sqAct A a k j
        + ∑ Q ∈ Finset.range k,
            sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
              sqAct A (W.L ((Q + 1 : ℕ) : ℤ) a) (k - (Q + 1)) j := by
    rw [sqMode_Lsq_zero_of_mem_grading A ha]
    have hsub : Function.support (fun Q : ℕ ↦
        sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
          sqAct A (W.L (Q : ℤ) a) (k - Q) j) ⊆ Finset.range (k + 1) := by
      intro Q hQ
      simp only [Function.mem_support, ne_eq] at hQ
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hQk
      push Not at hQk
      exact hQ (by rw [L_nat_eq_zero_of_lt W ha (by omega : k < Q),
        sqAct_zero_left, smul_zero])
    rw [finsum_eq_finsetSum_of_support_subset _ hsub, Finset.sum_range_succ']
    have hd0 : sqBracketCoeffZ 2 1 (1 : ℤ) = 1 := by
      simpa using sqBracketCoeff_zero_diag
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.zero_add, Nat.sub_zero]
    rw [hd0, one_smul, W.L_zero_grading a ha, sqAct_smul_left]
    abel
  simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply] using
    congrArg (fun T : Module.End ℂ M ↦ T v) hmap

/-- The `L[0]` commutator for an ordinary-homogeneous first input. -/
theorem Lsq_zero_sqMode_comm_of_mem_grading (A : OrdVModule W M)
    {a : V} {k : ℕ} (ha : a ∈ W.grading (k : ℤ)) (j : ℤ) (v : M) :
    sqL A 0 (sqMode A j a v) - sqMode A j a (sqL A 0 v) =
      sqMode A j (Lsq W 0 a) v - ((j : ℂ) + 1) • sqMode A j a v := by
  have hsq : sqMode A j a = sqAct A a k j := by
    simpa using sqMode_of_mem_grading A ha j
  rw [hsq]
  rw [Lsq_zero_vSqZ_comm_collapsed A ha,
    sqMode_Lsq_zero_of_mem_grading_explicit A ha]
  module

/-- Zhu's square-bracket grading keystone:
`[L[0], a[j]] = (L[0]a)[j] - (j+1)a[j]`, with no homogeneity hypothesis. -/
theorem Lsq_zero_sqMode_comm (A : OrdVModule W M) (a : V) (j : ℤ) (v : M) :
    sqL A 0 (sqMode A j a v) - sqMode A j a (sqL A 0 v) =
      sqMode A j (Lsq W 0 a) v - ((j : ℂ) + 1) • sqMode A j a v := by
  refine ordinaryGrading_induction W (P := fun a ↦
    sqL A 0 (sqMode A j a v) - sqMode A j a (sqL A 0 v) =
      sqMode A j (Lsq W 0 a) v - ((j : ℂ) + 1) • sqMode A j a v) ?_ ?_ ?_ a
  · intro k x hx
    by_cases hk : k < 0
    · have hx0 : x = 0 := by
        rw [W.positivity k hk, Submodule.mem_bot] at hx
        exact hx
      subst hx0
      simp
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
      exact Lsq_zero_sqMode_comm_of_mem_grading A hx j v
  · simp
  · intro x y hx hy
    calc
      sqL A 0 (sqMode A j (x + y) v) - sqMode A j (x + y) (sqL A 0 v) =
          (sqL A 0 (sqMode A j x v) - sqMode A j x (sqL A 0 v))
            + (sqL A 0 (sqMode A j y v) - sqMode A j y (sqL A 0 v)) := by
              simp only [map_add, LinearMap.add_apply]
              module
      _ = (sqMode A j (Lsq W 0 x) v - ((j : ℂ) + 1) • sqMode A j x v)
            + (sqMode A j (Lsq W 0 y) v - ((j : ℂ) + 1) • sqMode A j y v) := by
              rw [hx, hy]
      _ = sqMode A j (Lsq W 0 (x + y)) v
            - ((j : ℂ) + 1) • sqMode A j (x + y) v := by
              simp only [map_add, LinearMap.add_apply]
              module


end VOA.Huang.GenusOne.SquareModule
