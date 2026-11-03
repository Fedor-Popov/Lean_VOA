import VOA.Huang.GenusOneSquareModes
import VOA.Huang.MatrixCoeffIterate

/-! # Collected Eisenstein recursion for a general intertwiner insertion -/
namespace VOA.Huang.GenusOne
open VOA Module
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Uniform truncation on a fixed traced weight space, including nonintegral modes. -/
theorem intertwiner_eventually_zero_on_weight (Y : IntertwiningOperator A N N)
    {α : ℂ} {w : M₁} (hw : w ∈ A.weight α) (β b : ℂ) :
    ∃ K : ℤ, ∀ i : ℤ, K ≤ i → ∀ x ∈ N.weight β, Y.val (b + i) w x = 0 := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  obtain ⟨K, hK⟩ := exists_int_gt (α.re + β.re - b.re - 1 - B)
  refine ⟨K, fun i hi x hx => ?_⟩
  have hmem := FusionTop.mem_weight Y.property hw hx (b + i)
  have hbot : N.weight (α + β - (b + i) - 1) = ⊥ := by
    by_contra hn
    have hb := hB _ hn
    have hki : (K : ℝ) ≤ i := by exact_mod_cast hi
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at hb
    linarith
  simpa only [hbot, Submodule.mem_bot] using hmem

noncomputable def tracePair (Y : IntertwiningOperator A N N) (a : V) (w : M₁)
    (k : ℤ) (α : ℂ) (p : ℤ) : Module.End ℂ M :=
  if p ≤ -1 then mode (N.YM a) p * Y.val ((k : ℂ) + α - p - 2) w
  else Y.val ((k : ℂ) + α - p - 2) w * mode (N.YM a) p

noncomputable def traceTwo (Y : IntertwiningOperator A N N) (a : V) (w : M₁) : FormalQSeries :=
  gradedTraceOp N (oMod N a * zeroMode A Y.val w)

variable (Y : IntertwiningOperator A N N) {ka : ℤ} {l : ℂ} {a : V} {v : M₁}

theorem zeroMode_neg_one_eq_finsum_tracePair (ha : a ∈ W.grading ka) (hv : v ∈ A.weight l)
    (x : M) : zeroMode A Y.val (mode (A.YM a) (-1) v) x = ∑ᶠ p : ℤ, tracePair Y a v ka l p x := by
  rw [zeroMode_of_mem _ _ (mode_mem_weight A ha hv (-1)),
    MatrixCoeffIterate.mode_neg_one_left Y.property]
  have hind : ∀ j : ℤ, l + ka - (-1 : ℤ) - 1 - 1 + j = (ka : ℂ) + l - (-1 - j) - 2 := by
    intro j; push_cast; ring
  have hind' : ∀ j : ℤ, l + ka - (-1 : ℤ) - 1 - 1 - 1 - j = (ka : ℂ) + l - j - 2 := by
    intro j; push_cast; ring
  simp_rw [hind, hind']
  -- finiteness of the two families (pointwise truncation)
  obtain ⟨Nv, hNv⟩ := Y.property.truncation v x ((ka : ℂ) + l - 1)
  obtain ⟨Na, hNa⟩ := N.truncation a x
  have hfinA : (Function.support fun j : ℕ =>
      mode (N.YM a) (-1 - j) (Y.val ((ka : ℂ) + l - (-1 - j) - 2) v x)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio Nv.toNat) (fun j hj => ?_)
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc; push Not at hc
    exact hj (by rw [show (ka : ℂ) + l - (-1 - (j : ℂ)) - 2 =
        ((ka : ℂ) + l - 1) + ((j : ℤ) : ℂ) by push_cast; ring,
      hNv _ (by omega), map_zero])
  have hfinB : (Function.support fun j : ℕ =>
      Y.val ((ka : ℂ) + l - j - 2) v (mode (N.YM a) j x)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio Na.toNat) (fun j hj => ?_)
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc; push Not at hc
    exact hj (by rw [hNa _ (by omega), map_zero])
  -- the `ℤ`-sum of the indicator form is the `ℕ`-sum
  have hL : (∑ᶠ j : ℤ, if 0 ≤ j then
      (mode (N.YM a) (-1 - j) (Y.val ((ka : ℂ) + l - (-1 - j) - 2) v x)
      + Y.val ((ka : ℂ) + l - j - 2) v (mode (N.YM a) j x)) else 0)
      = ∑ᶠ j : ℕ, (mode (N.YM a) (-1 - j) (Y.val ((ka : ℂ) + l - (-1 - j) - 2) v x)
          + Y.val ((ka : ℂ) + l - j - 2) v (mode (N.YM a) j x)) := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ))
      (fun j hj => ?_), finsum_mem_range Nat.cast_injective]
    · refine finsum_congr (fun j => ?_)
      rw [if_pos (by positivity)]
      push_cast
      rfl
    · simp only [Set.mem_univ, Set.mem_range, true_iff]
      rw [Function.mem_support] at hj
      by_cases h0 : 0 ≤ j
      · exact ⟨j.toNat, by omega⟩
      · exact absurd (if_neg h0) hj
  rw [hL, finsum_add_distrib hfinA hfinB]
  -- the `p`-sum splits into `p ≥ 0` (reversed pairs) and `p = −1−j` (standard pairs)
  have hfinP : (Function.support fun p : ℤ => tracePair Y a v ka l p x).Finite := by
    refine Set.Finite.subset (Set.finite_Icc (-Nv.toNat - 1 : ℤ) Na.toNat)
      (fun p hp => ?_)
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_Icc]
    by_contra hc
    refine hp ?_
    rw [tracePair]
    by_cases hp1 : p ≤ -1
    · rw [if_pos hp1]
      change mode (N.YM a) p (Y.val ((ka : ℂ) + l - p - 2) v x) = 0
      rw [show (ka : ℂ) + l - p - 2 = ((ka : ℂ) + l - 1) + ((-p - 1 : ℤ) : ℂ) by push_cast; ring,
        hNv _ (by omega), map_zero]
    · rw [if_neg hp1]
      change Y.val ((ka : ℂ) + l - p - 2) v (mode (N.YM a) p x) = 0
      rw [hNa _ (by omega), map_zero]
  have hsplit := finsum_int_split_two (fun p => tracePair Y a v ka l p x) hfinP
    (fun j : ℕ => (j : ℤ))
    (fun j : ℕ => -1 - j) Nat.cast_injective (fun a b h => by simpa using h) ?_ ?_
  · rw [hsplit, add_comm]
    congr 1
    · refine finsum_congr (fun j => ?_)
      change _ = tracePair Y a v ka l (j : ℤ) x
      rw [tracePair, if_neg (by omega)]
      rfl
    · refine finsum_congr (fun j => ?_)
      change _ = tracePair Y a v ka l (-1 - (j : ℤ)) x
      rw [tracePair, if_pos (by omega)]
      push_cast
      rfl
  · rw [Set.disjoint_left]
    rintro p ⟨a, rfl⟩ ⟨b, hb⟩
    simp only at hb
    omega
  · refine Set.eq_univ_of_forall (fun p => ?_)
    by_cases hp : 0 ≤ p
    · exact Or.inl ⟨p.toNat, by simp; omega⟩
    · exact Or.inr ⟨(-1 - p).toNat, by simp; omega⟩

/-- **The `i = −1` iterate at a fixed degree, as a sum over all mode indices**:
`𝒵_M(a₍₋₁₎v)(e) = Σᶠ_p 𝒯(pairOp p)(e)`.  Uniform truncation on the (finite-dimensional) weight
space makes the operator sum finite on `M_α`, and outside that window each pair annihilates `M_α`,
so its trace vanishes. -/
theorem trace_neg_one_eq_finsum_tracePair (ha : a ∈ W.grading ka) (hv : v ∈ A.weight l)
    (e : ℂ) :
    trace Y (mode (A.YM a) (-1) v) e = ∑ᶠ p : ℤ, gradedTraceOp N (tracePair Y a v ka l p) e := by
  set α : ℂ := e + W.centralCharge / 24 with hα
  obtain ⟨Nv, hNv⟩ := intertwiner_eventually_zero_on_weight Y hv α ((ka : ℂ) + l - 1)
  obtain ⟨Na, hNa⟩ := mode_eventually_zero_on_weight N a α
  set lo : ℤ := min (-1) (-Nv - 1) with hlo
  set hi : ℤ := max 0 Na with hhi
  -- pairs outside `[lo, hi]` kill `M_α`
  have hkill : ∀ p : ℤ, ¬(lo ≤ p ∧ p ≤ hi) → ∀ x ∈ N.weight α, tracePair Y a v ka l p x = 0 := by
    intro p hp x hx
    rw [tracePair]
    by_cases hp1 : p ≤ -1
    · rw [if_pos hp1]
      change mode (N.YM a) p (Y.val ((ka : ℂ) + l - p - 2) v x) = 0
      rw [show (ka : ℂ) + l - p - 2 = ((ka : ℂ) + l - 1) + ((-p - 1 : ℤ) : ℂ) by push_cast; ring,
        hNv _ (by omega) x hx, map_zero]
    · rw [if_neg hp1]
      change Y.val ((ka : ℂ) + l - p - 2) v (mode (N.YM a) p x) = 0
      rw [hNa _ (by omega) x hx, map_zero]
  -- on `M_α` the operator is the finite sum over `Icc lo hi`
  set Op : Module.End ℂ M := ∑ p ∈ Finset.Icc lo hi, tracePair Y a v ka l p with hOp
  have hagree : ∀ x ∈ N.weight α, zeroMode A Y.val (mode (A.YM a) (-1) v) x = Op x := by
    intro x hx
    rw [zeroMode_neg_one_eq_finsum_tracePair Y ha hv x, hOp, LinearMap.sum_apply]
    refine finsum_eq_sum_of_support_subset _ (fun p hp => ?_)
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hp (hkill p hc x hx)
  have hblk : weightBlock N (zeroMode A Y.val (mode (A.YM a) (-1) v)) α = weightBlock N Op α := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.isInternal _) (zeroMode A Y.val (mode (A.YM a) (-1) v) (y : M)) : M)
      = ((internalProjTo N.isInternal _) (Op (y : M)) : M)
    rw [hagree (y : M) y.2]
  have hlhs : trace Y (mode (A.YM a) (-1) v) e = gradedTraceOp N Op e := by
    haveI := N.finrank α
    change LinearMap.trace ℂ _ (weightBlock N (zeroMode A Y.val (mode (A.YM a) (-1) v)) α) = _
    rw [hblk]
    rfl
  rw [hlhs, hOp, ← gradedTraceAt_apply, map_sum]
  simp only [gradedTraceAt_apply]
  symm
  refine finsum_eq_sum_of_support_subset _ (fun p hp => ?_)
  simp only [Function.mem_support, ne_eq] at hp
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hc
  refine hp ?_
  rw [tracePair]
  by_cases hp1 : p ≤ -1
  · rw [if_pos hp1]
    exact gradedTraceOp_mul_eq_zero_of_kills N _ _ e (fun x hx => by
      rw [show (ka : ℂ) + l - p - 2 = ((ka : ℂ) + l - 1) + ((-p - 1 : ℤ) : ℂ) by push_cast; ring]
      exact hNv _ (by omega) x hx)
  · rw [if_neg hp1]
    exact gradedTraceOp_mul_eq_zero_of_kills N _ _ e (fun x hx => hNa _ (by omega) x hx)


/-- The lower geometric telescope at a specified depth. -/
theorem trace_pair_geom (i : ℤ) (ha : a ∈ W.grading ka) (hv : v ∈ A.weight l)
    (e : ℂ) (n : ℕ)
    (hz : gradedTraceOp N (mode (N.YM a) i * Y.val ((ka : ℂ) + l - i - 2) v)
      (e - (n : ℂ) * ((ka : ℂ) - i - 1)) = 0) :
    gradedTraceOp N (mode (N.YM a) i * Y.val ((ka : ℂ) + l - i - 2) v) e =
      -∑ j ∈ Finset.range n, ∑ᶠ r : ℤ,
        cbz i r * trace Y (mode (A.YM a) r v) (e - ((j : ℂ) + 1) * ((ka : ℂ) - i - 1)) := by
  have h := gradedTrace_geomSolve _ (fun e =>
    -(∑ᶠ r : ℤ, cbz i r * trace Y (mode (A.YM a) r v) e)) _
    (fun e => by simpa only [sub_eq_add_neg] using trace_pair_step Y ha hv i e) e n hz
  simpa only [Finset.sum_neg_distrib] using h

theorem trace_pair_geom_up (i : ℤ) (ha : a ∈ W.grading ka) (hv : v ∈ A.weight l)
    (e : ℂ) (n : ℕ)
    (hz : gradedTraceOp N (mode (N.YM a) i * Y.val ((ka : ℂ) + l - i - 2) v)
      (e + (n : ℂ) * ((ka : ℂ) - i - 1)) = 0) :
    gradedTraceOp N (mode (N.YM a) i * Y.val ((ka : ℂ) + l - i - 2) v) e =
      ∑ j ∈ Finset.range n, ∑ᶠ r : ℤ,
        cbz i r * trace Y (mode (A.YM a) r v) (e + (j : ℂ) * ((ka : ℂ) - i - 1)) := by
  have h := gradedTrace_geomSolve_up _ (fun e =>
    -(∑ᶠ r : ℤ, cbz i r * trace Y (mode (A.YM a) r v) e)) _
    (fun e => by simpa only [sub_eq_add_neg] using trace_pair_step Y ha hv i e) e n hz
  simpa only [Finset.sum_neg_distrib, neg_neg] using h

theorem trace_reversed_pair (ha : a ∈ W.grading ka) (hv : v ∈ A.weight l)
    (i : ℤ) (e : ℂ) :
    gradedTraceOp N (Y.val ((ka : ℂ) + l - i - 2) v * mode (N.YM a) i) e =
      gradedTraceOp N (mode (N.YM a) i * Y.val ((ka : ℂ) + l - i - 2) v)
        (e + ((ka : ℂ) - i - 1)) := by
  exact gradedTraceOp_comm_shift N _ _ _
    (weightShift_partner Y hv ka i) (VOA.weightShift_mode N ha i) e

theorem trace_pair_zero_shift (ha : a ∈ W.grading ka) (hv : v ∈ A.weight l) (e : ℂ) :
    gradedTraceOp N (mode (N.YM a) (ka - 1) *
      Y.val ((ka : ℂ) + l - ((ka - 1 : ℤ) : ℂ) - 2) v) e = traceTwo Y a v e := by
  rw [traceTwo, oMod_of_mem_grading N ha, zeroMode_of_mem _ _ hv]
  rw [show (ka : ℂ) + l - ((ka - 1 : ℤ) : ℂ) - 2 = l - 1 by push_cast; ring]

variable {k : ℕ}

theorem tracePair_eq (hk : 1 ≤ k) (ha : a ∈ W.grading (k : ℤ)) (hv : v ∈ A.weight l)
    (e : ℂ) (D : ℕ) (hD : ∀ (A : Module.End ℂ M) (n : ℕ), D < n → gradedTraceOp N A (e - n) = 0)
    (p : ℤ) :
    gradedTraceOp N (tracePair Y a v k l p) e
      = (if p = (k : ℤ) - 1 then traceTwo Y a v e else 0)
        + (if 0 ≤ p ∧ p ≤ (k : ℤ) - 2
            then -(commTraceZ (fun r e' => trace Y (mode (A.YM a) r v) e') p e) else 0)
        + modeSgn k p * telescopeZ (fun r e' => trace Y (mode (A.YM a) r v) e') k D e p := by
  set Z : ℤ → ℂ → ℂ := fun r e' => trace Y (mode (A.YM a) r v) e' with hZ
  -- the commutator trace at a shifted degree, in the `commTraceZ` shape
  have hCz : ∀ e' : ℂ, (∑ᶠ r : ℤ, cbz p r * trace Y (mode (A.YM a) r v) e') = commTraceZ Z p e' :=
    fun e' => rfl
  have hD' : ∀ (A : Module.End ℂ M) (n : ℕ), D < n → gradedTraceOp N A (e - n) = 0 := hD
  rcases lt_trichotomy p ((k : ℤ) - 1) with hlt | heq | hgt
  · -- `p < kₐ − 1`: shift `s = kₐ − p − 1 ≥ 1`, telescope down
    have hdist : ((modeDist k p : ℕ) : ℂ) = (k : ℂ) - (p : ℂ) - 1 := modeDist_cast_of_le hlt.le
    have hdpos : 1 ≤ modeDist k p := modeDist_pos_of_ne hlt.ne
    have hne : p ≠ (k : ℤ) - 1 := hlt.ne
    rw [if_neg hne, zero_add, modeSgn, if_neg (not_lt.mpr hlt.le), if_pos hlt, neg_one_mul]
    -- the standard-orientation pair trace, telescoped to depth `n`
    have hstd : ∀ n : ℕ, D < n * modeDist k p →
        gradedTraceOp N (mode (N.YM a) p * Y.val (((k : ℤ) : ℂ) + l - p - 2) v) e
          = -∑ j ∈ Finset.range n, commTraceZ Z p (e - ((j : ℂ) + 1) * (modeDist k p : ℂ)) := by
      intro n hn
      rw [trace_pair_geom Y p ha hv e n]
      · simp only [Int.cast_natCast, hCz, hdist]
      · simp only [Int.cast_natCast]
        rw [show e - (n : ℂ) * ((k : ℂ) - (p : ℂ) - 1) = e - ((n * modeDist k p : ℕ) : ℂ) from by
          rw [Nat.cast_mul, hdist]]
        exact hD' _ _ hn
    by_cases hp0 : 0 ≤ p
    · -- reversed pair: `𝒯(v·a₍ₚ₎)(e) = 𝒯(a₍ₚ₎·v)(e + s)`, telescope to depth `D + 2`
      rw [if_pos ⟨hp0, by omega⟩, tracePair, if_neg (by omega),
        trace_reversed_pair Y ha hv p e]
      simp only [Int.cast_natCast]
      have hstd' : ∀ n : ℕ, D < n * modeDist k p →
          gradedTraceOp N (mode (N.YM a) p * Y.val (((k : ℤ) : ℂ) + l - p - 2) v)
              (e + ((k : ℂ) - (p : ℂ) - 1))
            = -∑ j ∈ Finset.range (n + 1),
                commTraceZ Z p (e - ((j : ℂ)) * (modeDist k p : ℂ)) := by
        intro n hn
        rw [trace_pair_geom Y p ha hv _ (n + 1)]
        · simp only [Int.cast_natCast, hCz, hdist]
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          congr 1
          ring
        · simp only [Int.cast_natCast]
          rw [show e + ((k : ℂ) - (p : ℂ) - 1) - ((n + 1 : ℕ) : ℂ) * ((k : ℂ) - (p : ℂ) - 1)
              = e - ((n * modeDist k p : ℕ) : ℂ) from by
            rw [Nat.cast_mul, hdist]; push_cast; ring]
          exact hD' _ _ hn
      simp only [Int.cast_natCast] at hstd'
      rw [hstd' (D + 1) (by nlinarith), Finset.sum_range_succ', telescopeZ, hZ]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero]
      rw [neg_add, add_comm]
    · -- standard pair (`p ≤ −1`), telescope to depth `D + 1`
      push Not at hp0
      rw [if_neg (fun h => absurd h.1 (not_le.mpr hp0)), zero_add, tracePair, if_pos (by omega),
        hstd (D + 1) (by nlinarith), telescopeZ]
  · -- `p = kₐ − 1`: the zero-mode pair, i.e. the two-point term
    subst heq
    rw [if_pos rfl, if_neg (fun h => by omega), add_zero, modeSgn_self,
      zero_mul, add_zero, tracePair,
      if_neg (by omega), trace_reversed_pair Y ha hv _ e,
      trace_pair_zero_shift Y ha hv]
    all_goals (congr 1; push_cast; ring)
  · -- `p > kₐ − 1`: reversed pair, telescope up to depth `D + 1`
    have hdist : ((modeDist k p : ℕ) : ℂ) = (p : ℂ) - (k : ℂ) + 1 := modeDist_cast_of_ge hgt.le
    have hdpos : 1 ≤ modeDist k p := modeDist_pos_of_ne hgt.ne'
    rw [if_neg hgt.ne', zero_add, if_neg (fun h => by omega), zero_add, modeSgn, if_pos hgt,
      one_mul, tracePair, if_neg (by omega), trace_reversed_pair Y ha hv p e,
      trace_pair_geom_up Y p ha hv _ (D + 1)]
    · rw [telescopeZ, hZ]
      simp only [Int.cast_natCast]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hdist]
      apply congrArg (commTraceZ (fun r e' => trace Y (mode (A.YM a) r v) e') p)
      ring
    · simp only [Int.cast_natCast]
      rw [show e + ((k : ℂ) - (p : ℂ) - 1) + ((D + 1 : ℕ) : ℂ) * ((k : ℂ) - (p : ℂ) - 1)
          = e - (((D + 2) * modeDist k p : ℕ) : ℂ) from by
        rw [Nat.cast_mul, hdist]; push_cast; ring]
      exact hD' _ _ (by nlinarith)

/-- The Eisenstein tail has finite support as a family of formal series. -/
theorem trace_recursion_support_finite (a : V) (w : M₁) (k : ℕ) :
    (Function.support fun m : ℕ =>
      qConv (zhuG (m + 1)) (trace Y (sqAct A a k (2 * (m + 1) - 1 : ℤ) w))).Finite := by
  obtain ⟨K, hK⟩ := sqAct_eventually_zero A a k w
  refine (Set.finite_Iio K.toNat).subset fun m hm => ?_
  simp only [Function.mem_support] at hm
  by_contra hn
  exact hm (by rw [hK _ (by simp only [Set.mem_Iio] at hn; omega), map_zero, qConv_zero_right])

theorem trace_sqAct_negOne_of_homogeneous {ka : ℕ} (hk : 1 ≤ ka)
    (ha : a ∈ W.grading (ka : ℤ)) (hv : v ∈ A.weight l) :
    trace Y (sqAct A a ka (-1) v) = traceTwo Y a v +
      ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (trace Y (sqAct A a ka (2 * (m + 1) - 1 : ℤ) v)) := by
  funext e
  set Z : ℤ → ℂ → ℂ := fun r e' => trace Y (mode (A.YM a) r v) e' with hZ
  obtain ⟨D, hD⟩ := exists_gradedTraceOp_bound N e
  obtain ⟨R, hR⟩ := A.truncation a v
  -- (1) the left-hand side: `Z_{−1}(e) + Σ_{r≥0} c(k,−1,r) Z_r(e)`
  have hL1 : trace Y (sqAct A a ka (-1) v) e
      = trace Y (mode (A.YM a) (-1) v) e
        + ∑ᶠ r : ℤ, (if 0 ≤ r then sqBracketCoeffZ ka (-1) r * Z r e else 0) := by
    rw [trace_sqAct_expand]
    have hsplit : ∀ i : ℤ, sqBracketCoeffZ ka (-1) i * trace Y (mode (A.YM a) i v) e
        = (if i = -1 then trace Y (mode (A.YM a) (-1) v) e else 0)
          + (if 0 ≤ i then sqBracketCoeffZ ka (-1) i * Z i e else 0) := by
      intro i
      rcases lt_trichotomy i (-1) with h | h | h
      · rw [if_neg h.ne, if_neg (by omega), sqBracketCoeffZ_of_lt ka h, zero_mul, add_zero]
      · subst h
        rw [if_pos rfl, if_neg (by norm_num), add_zero, sqBracketCoeffZ_neg_one_diag, one_mul]
      · rw [if_neg h.ne', if_pos (by omega), zero_add]
    rw [finsum_congr hsplit, finsum_add_distrib,
      finsum_eq_single _ (-1 : ℤ) (fun i hi => if_neg hi),
      if_pos rfl]
    · refine Set.Finite.subset (Set.finite_singleton (-1 : ℤ)) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_singleton_iff]
      by_contra hc
      exact hi (if_neg hc)
    · refine Set.Finite.subset (Set.finite_Ico (0 : ℤ) R) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_Ico]
      refine ⟨?_, ?_⟩
      · by_contra hc; exact hi (if_neg hc)
      · by_contra hc; push Not at hc
        refine hi ?_
        rw [hZ]
        simp only
        rw [show mode (A.YM a) i v = 0 from hR i hc, map_zero, Pi.zero_apply, mul_zero, ite_self]
  -- (2) `Z_{−1}(e)` as the two-point term plus the abstract `p`-sum
  have hL2 : trace Y (mode (A.YM a) (-1) v) e
      = traceTwo Y a v e
        + ∑ᶠ p : ℤ, ((if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0)
            + modeSgn ka p * telescopeZ Z ka D e p) := by
    rw [trace_neg_one_eq_finsum_tracePair Y ha hv e,
      finsum_congr (fun p => tracePair_eq Y hk ha hv e D hD p)]
    have hsupp1 : (Function.support fun p : ℤ =>
        (if p = (ka : ℤ) - 1 then traceTwo Y a v e else 0)).Finite := by
      refine Set.Finite.subset (Set.finite_singleton ((ka : ℤ) - 1)) (fun p hp => ?_)
      simp only [Function.mem_support, ne_eq] at hp
      simp only [Set.mem_singleton_iff]
      by_contra hc
      exact hp (if_neg hc)
    have hsupp2 : (Function.support fun p : ℤ =>
        ((if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0)
          + modeSgn ka p * telescopeZ Z ka D e p)).Finite := by
      refine Set.Finite.subset (Set.finite_Icc (-(D : ℤ) - ka) ((ka : ℤ) + D)) (fun p hp => ?_)
      simp only [Function.mem_support, ne_eq] at hp
      simp only [Set.mem_Icc]
      by_contra hc
      have hdist : D < modeDist ka p := by rw [modeDist]; omega
      have hDZ : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0 := fun r n hn => hD _ n hn
      refine hp ?_
      rw [telescopeZ_eq_zero_of_lt hDZ p hdist, mul_zero, add_zero, if_neg (fun h => by omega)]
    simp_rw [add_assoc]
    rw [finsum_add_distrib hsupp1 hsupp2,
      finsum_eq_single _ ((ka : ℤ) - 1) (fun p hp => if_neg hp), if_pos rfl]
  -- (3) hypotheses of the abstract assembly
  have hRZ : ∀ r, R ≤ r → ∀ e', Z r e' = 0 := by
    intro r hr e'
    rw [hZ]
    simp only
    rw [show mode (A.YM a) r v = 0 from hR r hr, map_zero, Pi.zero_apply]
  have hDZ : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0 := fun r n hn => hD _ n hn
  have hvan : ∑ᶠ r : ℤ, sqBracketCoeffZ ka 0 r * Z r e = 0 := by
    have h := congrFun (trace_sqAct_zero Y ha hk v) e
    rw [trace_sqAct_expand, Pi.zero_apply] at h
    exact h
  -- (4) assemble
  rw [hL1, hL2, add_assoc, zhu_abstract_assembly hk e R D hRZ hDZ hvan, Pi.add_apply,
    finsum_apply (trace_recursion_support_finite Y a v ka)]
  congr 1
  refine finsum_congr (fun m => ?_)
  rw [qConv]
  refine finsum_congr (fun n => ?_)
  rw [trace_sqAct_expand]


theorem trace_shift_support_finite (w : M₁) (e : ℂ) (f : ℕ → ℂ) :
    (Function.support fun n : ℕ => f n * trace Y w (e - n)).Finite := by
  obtain ⟨D, hD⟩ := exists_gradedTraceOp_bound N e
  refine (Set.finite_Iic D).subset fun n hn => ?_
  simp only [Function.mem_support] at hn
  by_contra hc
  exact hn (by change f n * gradedTraceOp N (zeroMode A Y.val w) (e - n) = 0
               rw [hD _ n (by simp only [Set.mem_Iic] at hc; omega), mul_zero])

/-- Zhu's collected recursion with an arbitrary insertion vector in an ordinary module. -/
theorem trace_sqAct_negOne {ka : ℕ} (hk : 1 ≤ ka) {a : V}
    (ha : a ∈ W.grading (ka : ℤ)) (w : M₁) :
    trace Y (sqAct A a ka (-1) w) = traceTwo Y a w +
      ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (trace Y (sqAct A a ka (2 * (m + 1) - 1 : ℤ) w)) := by
  refine FusionTop.induction_weight A w ?_ ?_ (fun _ _ hx =>
    trace_sqAct_negOne_of_homogeneous Y hk ha hx)
  · simp only [map_zero, traceTwo, mul_zero]
    have hz : gradedTraceOp N (0 : Module.End ℂ M) = 0 := by
      funext e
      exact map_zero (gradedTraceAt N e)
    simp only [hz, qConv_zero_right, finsum_zero, add_zero]
  · intro x y hx hy
    funext e
    have htwo : traceTwo Y a (x + y) = traceTwo Y a x + traceTwo Y a y := by
      simp only [traceTwo, map_add, mul_add, gradedTraceOp_add]
    have htail : ∀ m : ℕ,
        qConv (zhuG (m + 1)) (trace Y (sqAct A a ka (2 * (m + 1) - 1 : ℤ) (x + y))) e =
          qConv (zhuG (m + 1)) (trace Y (sqAct A a ka (2 * (m + 1) - 1 : ℤ) x)) e +
          qConv (zhuG (m + 1)) (trace Y (sqAct A a ka (2 * (m + 1) - 1 : ℤ) y)) e := by
      intro m
      rw [map_add, map_add, qConv_add_apply _ _ _ e
        (trace_shift_support_finite Y _ e _) (trace_shift_support_finite Y _ e _)]
    rw [map_add, map_add, Pi.add_apply, hx, hy, Pi.add_apply, Pi.add_apply,
      finsum_apply (trace_recursion_support_finite Y a x ka),
      finsum_apply (trace_recursion_support_finite Y a y ka), Pi.add_apply, htwo, Pi.add_apply,
      finsum_apply (trace_recursion_support_finite Y a (x + y) ka), finsum_congr htail,
      finsum_add_distrib]
    · ring
    · exact (trace_recursion_support_finite Y a x ka).subset fun m hm => by
        simp only [Function.mem_support] at hm ⊢
        intro h; exact hm (by rw [h]; rfl)
    · exact (trace_recursion_support_finite Y a y ka).subset fun m hm => by
        simp only [Function.mem_support] at hm ⊢
        intro h; exact hm (by rw [h]; rfl)

/-- The intertwiner omega recursion, with the central-charge shift cancelled exactly. -/
theorem trace_sqL_negTwo (w : M₁) :
    trace Y (sqL A (-2) w) = qDeriv (trace Y w) +
      ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (trace Y (sqL A (2 * (m + 1) - 2 : ℤ) w)) := by
  have hr := trace_sqAct_negOne Y (ka := 2) (by norm_num) W.conformalVector_mem_grading_two w
  have hm : sqAct A W.conformalVector 2 (-1) w = sqL A (-2) w + (W.centralCharge / 24) • w := by
    simp only [sqL, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    norm_num
  have ho : ∀ m : ℕ, sqAct A W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) w =
      sqL A (2 * (m + 1) - 2 : ℤ) w := by
    intro m
    simp only [sqL, if_neg (show (2 * (m + 1) - 2 : ℤ) ≠ -2 by omega),
      zero_smul, sub_zero]
    congr 2
    ring
  have ht : traceTwo Y W.conformalVector w =
      qDeriv (trace Y w) + (W.centralCharge / 24) • trace Y w := by
    funext e
    rw [traceTwo, oMod_conformalVector, gradedTraceOp_L0_mul]
    change (e + W.centralCharge / 24) * trace Y w e = e * trace Y w e + _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hm, map_add, map_smul, ht] at hr
  simp_rw [ho] at hr
  exact add_right_cancel (show trace Y (sqL A (-2) w) + (W.centralCharge / 24) • trace Y w =
    (qDeriv (trace Y w) + ∑ᶠ m : ℕ, qConv (zhuG (m + 1))
      (trace Y (sqL A (2 * (m + 1) - 2 : ℤ) w))) + (W.centralCharge / 24) • trace Y w by
    rw [hr]; abel)

end VOA.Huang.GenusOne
