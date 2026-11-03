import VOA.Huang.GenusOneCloseDefect

/-!
# Resolving a formal logarithmic pair

For a formal block `G` and a defect block `H` with defect `κ • G`, `κ ≠ 0`,
both supported at `b`, the leading functional of `H` is a generalized central
eigenfunctional of exponent two. It is realized by traces, the realization
forces `κ · G(b) = 0`, and subtraction raises both supports. A uniform finite
determining jet ends the induction: `G = 0` and `H` is a finite trace sum.

This is the formal content of Miyamoto, math/0010180, Lemma 4.13 and
Proposition 4.14 for a Jordan chain of length two. The bimodule and Li lifting
inputs are explicit hypotheses here.
-/
namespace VOA.Huang.GenusOne.Close
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} [Fintype ι]

theorem QSeriesAt.of_add_nat {χ : FormalQSeries} {b : ℂ} (k : ℕ)
    (hχ : χ ∈ QSeriesAt (b + (k : ℂ))) : χ ∈ QSeriesAt b := by
  intro e he
  apply hχ
  intro n hn
  exact he (k + n) (by rw [hn]; push_cast; ring)

theorem QSeriesAt.coeff_below {χ : FormalQSeries} {b : ℂ} {N k : ℕ}
    (hχ : χ ∈ QSeriesAt (b + (N : ℂ))) (hk : k < N) : χ (b + (k : ℂ)) = 0 := by
  apply hχ
  intro j hj
  have h : ((k : ℕ) : ℂ) = ((N + j : ℕ) : ℂ) := by push_cast; linear_combination hj
  have := Nat.cast_injective h
  omega

theorem trace_zero_apply {N' : Type u} [AddCommGroup N'] [Module ℂ N'] {Nm : OrdVModule W N'}
    (w : M) : trace (0 : IntertwiningOperator A Nm Nm) w = 0 := by
  have hz := congrArg (fun t : M →ₗ[ℂ] FormalQSeries => t w)
    (traceLinear (A := A) (N := Nm)).map_zero
  exact hz

theorem trace_add_apply {N' : Type u} [AddCommGroup N'] [Module ℂ N'] {Nm : OrdVModule W N'}
    (Y Z : IntertwiningOperator A Nm Nm) (w : M) :
    trace (Y + Z) w = trace Y w + trace Z w := by
  have h := congrArg (fun t : M →ₗ[ℂ] FormalQSeries => t w)
    ((traceLinear (A := A) (N := Nm)).map_add Y Z)
  exact h

/-- Support condition for an intertwiner family relative to a base exponent. -/
def SuppAt (P : ι → LWModule W) (b : ℂ)
    (Z : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod) : Prop :=
  ∀ i, Z i ≠ 0 → ∃ k : ℕ, (P i).h = b + (k : ℂ) + W.centralCharge / 24

omit [Fintype ι] in
theorem SuppAt.trace_mem {P : ι → LWModule W} {b : ℂ}
    {Z : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod} (hZ : SuppAt P b Z)
    (i : ι) (w : M) : trace (Z i) w ∈ QSeriesAt b := by
  by_cases hi : Z i = 0
  · rw [hi, trace_zero_apply]
    exact (QSeriesAt b).zero_mem
  · obtain ⟨k, hk⟩ := hZ i hi
    have ht := trace_mem_QSeriesAt (Z i) ⟨(P i).realized, (P i).isLow⟩ w
    rw [hk, add_sub_cancel_right] at ht
    exact QSeriesAt.of_add_nat k ht

theorem SuppAt.sum_mem {P : ι → LWModule W} {b : ℂ}
    {Z : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod} (hZ : SuppAt P b Z)
    (w : M) : (∑ i, trace (Z i)) w ∈ QSeriesAt b := by
  rw [LinearMap.coe_sum, Finset.sum_apply]
  exact Submodule.sum_mem _ fun i _ => hZ.trace_mem i w

theorem SuppAt.formal {P : ι → LWModule W} {b : ℂ}
    {Z : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod} (hZ : SuppAt P b Z) :
    IsInsertionFormalBlock A (∑ i, trace (Z i)) :=
  isInsertionFormalBlock_sum Finset.univ _ (fun i _ w => hZ.trace_mem i w)
    (fun i _ => isInsertionFormalBlock_trace (Z i))

/-- One step of the logarithmic subtraction at the common exponent `b`. -/
theorem defect_pair_step (P : ι → LWModule W) (hB : InsertionTopBimoduleExists A P)
    (hlift : InsertionTopSurjectivity A P) {G H : M →ₗ[ℂ] FormalQSeries} {b κ : ℂ}
    (hGb : ∀ w, G w ∈ QSeriesAt b) (hHb : ∀ w, H w ∈ QSeriesAt b)
    (hG : IsInsertionFormalBlock A G) (hH : IsDefectBlock A H (κ • G)) :
    (∀ w, κ * G w b = 0) ∧
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      (∀ w, (∑ i, trace (Y i) w) ∈ QSeriesAt b) ∧
      ∀ w, H w - ∑ i, trace (Y i) w ∈ QSeriesAt (b + 1) := by
  classical
  obtain ⟨B⟩ := hB
  have hO := leading_kills_fzO hHb hH
  have hbal : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
      Cusp.leading H b (fzLeft A.toWeakModule p a w) =
        Cusp.leading H b (fzRight A.toWeakModule p a w) :=
    fun p _ ha w => leading_balanced hH p ha w
  have hone : ∀ w, (fzO A.toWeakModule).liftQ (Cusp.leading H b) hO
      (insertionCuspOmega P B (b + W.centralCharge / 24) ((fzO A.toWeakModule).mkQ w)) =
        κ * G w b := by
    intro w
    rw [insertionCuspOmega_mk, Submodule.mkQ_apply, Submodule.liftQ_apply, map_sub, map_smul,
      leading_conformal hHb hH w]
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Cusp.leading_apply]
    ring
  have hGc := Cusp.leading_conformal hGb hG
  have htwo : ∀ x, (fzO A.toWeakModule).liftQ (Cusp.leading H b) hO
      ((insertionCuspOmega P B (b + W.centralCharge / 24))^[2] x) = 0 := by
    intro x
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    rw [Function.iterate_succ_apply, Function.iterate_one, insertionCuspOmega_mk, hone,
      map_sub, map_smul]
    have h := hGc w
    simp only [Cusp.leading_apply] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h, sub_self, mul_zero]
  have hg := htwo
  simp only [insertionCuspOmega_eq_diagonal] at hg
  have hz := BimoduleTrace.central_power_elimination B.actions (fun i => (P i).h)
    (b + W.centralCharge / 24) ((fzO A.toWeakModule).liftQ (Cusp.leading H b) hO) 2 hg
  refine ⟨fun w => ?_, ?_⟩
  · have hw := hz ((fzO A.toWeakModule).mkQ w)
    rw [← insertionCuspOmega_eq_diagonal, hone] at hw
    exact hw
  obtain ⟨Y, hY, he⟩ := functional_realized_at_weight_of_generalized P B hlift b
    (Cusp.leading H b) hO hbal 2 htwo
  have htrace (w : M) : (∑ i, trace (Y i) w) ∈ QSeriesAt b := by
    apply Submodule.sum_mem
    intro i _
    by_cases hi : (P i).h = b + W.centralCharge / 24
    · have ht := trace_mem_QSeriesAt (Y i) ⟨(P i).realized, (P i).isLow⟩ w
      simpa only [hi, add_sub_cancel_right] using ht
    · rw [hY i hi, trace_zero_apply]
      exact (QSeriesAt b).zero_mem
  exact ⟨Y, hY, htrace, fun w => Cusp.support_sub_succ (hHb w) (htrace w)
    (by simpa only [Finset.sum_apply] using he w)⟩

/-- **Formal log elimination and spanning for a pair.** -/
theorem defect_pair_resolve (P : ι → LWModule W) (hB : InsertionTopBimoduleExists A P)
    (hlift : InsertionTopSurjectivity A P) {G H : M →ₗ[ℂ] FormalQSeries} {b κ : ℂ}
    (hκ : κ ≠ 0)
    (hGb : ∀ w, G w ∈ QSeriesAt b) (hHb : ∀ w, H w ∈ QSeriesAt b)
    (hG : IsInsertionFormalBlock A G) (hH : IsDefectBlock A H (κ • G)) :
    G = 0 ∧ ∃ Z : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      SuppAt P b Z ∧ H = ∑ i, trace (Z i) := by
  classical
  obtain ⟨N, hN⟩ := exists_formal_determining_jet P hB b
  have claim : ∀ n : ℕ, (∀ w, G w ∈ QSeriesAt (b + (n : ℂ))) ∧
      ∃ Z : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
        SuppAt P b Z ∧ ∀ w, (H - ∑ i, trace (Z i)) w ∈ QSeriesAt (b + (n : ℂ)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun w => by simpa using hGb w, 0, fun i hi => absurd rfl hi, fun w => ?_⟩
      have hz : (∑ i, trace ((0 : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod) i)) =
          0 := by
        apply LinearMap.ext
        intro v
        rw [LinearMap.coe_sum, Finset.sum_apply]
        exact Finset.sum_eq_zero fun i _ => trace_zero_apply v
      rw [hz, sub_zero]
      simpa using hHb w
    | succ n ih =>
      obtain ⟨hGn, Z, hZ, hHn⟩ := ih
      have hH' : IsDefectBlock A (H - ∑ i, trace (Z i)) (κ • G) :=
        hH.sub_formal hHb hZ.sum_mem hZ.formal
      obtain ⟨hk, Y, hY, htr, hsub⟩ := defect_pair_step P hB hlift hGn hHn hG hH'
      have hcast : b + ((n + 1 : ℕ) : ℂ) = b + (n : ℂ) + 1 := by push_cast; ring
      refine ⟨fun w => ?_, fun i => Z i + Y i, ?_, fun w => ?_⟩
      · rw [hcast]
        have h := Cusp.support_shift (hGn w) 1 (fun k hk' => by
          have : k = 0 := by omega
          subst k
          simpa using (mul_eq_zero.mp (hk w)).resolve_left hκ)
        simpa using h
      · intro i hi
        change Z i + Y i ≠ 0 at hi
        by_cases hz : Z i = 0
        · have hy : Y i ≠ 0 := by
            intro hy
            exact hi (by rw [hz, hy, add_zero])
          by_contra hne
          exact hy (hY i (by
            intro he
            exact hne ⟨n, by rw [he]⟩))
        · exact hZ i hz
      · rw [hcast]
        have h := hsub w
        have he : (H - ∑ i, trace (Z i + Y i)) w =
            (H - ∑ i, trace (Z i)) w - ∑ i, trace (Y i) w := by
          simp only [LinearMap.sub_apply, LinearMap.coe_sum, Finset.sum_apply,
            trace_add_apply, Finset.sum_add_distrib]
          abel
        rw [he]
        exact h
  obtain ⟨hGN, Z, hZ, hHN⟩ := claim N
  have hG0 : G = 0 := hN G hGb hG (fun w k hk => QSeriesAt.coeff_below (hGN w) hk)
  refine ⟨hG0, Z, hZ, ?_⟩
  have hH' : IsDefectBlock A (H - ∑ i, trace (Z i)) (κ • G) :=
    hH.sub_formal hHb hZ.sum_mem hZ.formal
  rw [hG0, smul_zero, isDefectBlock_zero_iff] at hH'
  have h0 := hN (H - ∑ i, trace (Z i))
    (fun w => (QSeriesAt b).sub_mem (hHb w) (hZ.sum_mem w)) hH'
    (fun w k hk => QSeriesAt.coeff_below (hHN w) hk)
  exact sub_eq_zero.mp h0

end VOA.Huang.GenusOne.Close
