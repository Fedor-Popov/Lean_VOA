import VOA.Huang.GenusOneCentralSemisimple

/-! # Realization at the prescribed conformal weight

The central-character part of Miyamoto, math/0010180, Lemma 4.10 and the
leading-coefficient step of Lemma 4.13. The quotient bimodule and Li lifting
hypotheses remain explicit. This file does not assert analytic cusp extraction.
-/
namespace VOA.Huang.GenusOne.BimoduleTrace
open scoped BigOperators
variable {ι : Type*} [Fintype ι] {U : ι → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  [∀ i, FiniteDimensional ℂ (U i)]
  {E : Type*} [AddCommGroup E] [Module ℂ E]

omit [Fintype ι] [∀ i, FiniteDimensional ℂ (U i)] in
/-- Every generalized eigenfunctional for the diagonal central action is an
eigenfunctional, with no bound on the size of the bimodule. The exponent may
be zero, in which case the hypothesis already says the functional vanishes. -/
theorem central_power_elimination [Finite ι]
    (B : Actions (∀ i, Module.End ℂ (U i)) E) (h : ι → ℂ) (r : ℂ)
    (f : E →ₗ[ℂ] ℂ) (N : ℕ)
    (hf : ∀ x, f ((B.left (fun i => (h i - r) • (1 : Module.End ℂ (U i))))^[N] x) = 0) :
    ∀ x, f (B.left (fun i => (h i - r) • (1 : Module.End ℂ (U i))) x) = 0 := by
  classical
  letI := Fintype.ofFinite ι
  let a : ∀ i, Module.End ℂ (U i) := fun i => (h i - r) • 1
  let e (i : ι) : ∀ j, Module.End ℂ (U j) := Pi.single i 1
  have hae (i : ι) : a * e i = (h i - r) • e i := by
    funext j
    by_cases hj : j = i
    · subst j; simp [a, e]
    · simp [a, e, Pi.single_eq_of_ne hj]
  have heval (i : ι) (x : E) : B.left a (B.left (e i) x) =
      (h i - r) • B.left (e i) x := by
    rw [← B.left_mul, hae, map_smul, LinearMap.smul_apply]
  have hpow (n : ℕ) (i : ι) (x : E) :
      (B.left a)^[n] (B.left (e i) x) = (h i - r)^n • B.left (e i) x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, heval, smul_smul, pow_succ]
  have hpieces (i : ι) (x : E) : (h i - r) * f (B.left (e i) x) = 0 := by
    have hv := hf (B.left (e i) x)
    change f ((B.left a)^[N] (B.left (e i) x)) = 0 at hv
    rw [hpow, map_smul, smul_eq_mul] at hv
    by_cases hz : h i - r = 0
    · rw [hz, zero_mul]
    · rw [(mul_eq_zero.mp hv).resolve_left (pow_ne_zero _ hz), mul_zero]
  have he : ∑ i, e i = (1 : ∀ i, Module.End ℂ (U i)) := by
    ext j x
    simp [e]
  have hx (x : E) : x = ∑ i, B.left (e i) x := by
    have hv := congrArg (fun b => B.left b x) he
    simpa only [map_sum, LinearMap.sum_apply, B.left_one] using hv.symm
  intro x
  change f (B.left a x) = 0
  conv_lhs => rw [hx x]
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [heval, map_smul, smul_eq_mul, hpieces]

/-- A balanced central eigenfunctional is realized by bimodule maps supported
only on the simple blocks with the specified central character. -/
theorem exists_end_bimodule_map_weighted
    (B : Actions (∀ i, Module.End ℂ (U i)) E) (h : ι → ℂ) (r : ℂ)
    (f : E →ₗ[ℂ] ℂ) (hf : ∀ a x, f (B.left a x) = f (B.right a x))
    (homega : ∀ x, f (B.left (fun i => (h i - r) • (1 : Module.End ℂ (U i))) x) = 0) :
    ∃ T : E →ₗ[ℂ] (∀ i, Module.End ℂ (U i)),
      (∀ a x, T (B.left a x) = a * T x) ∧
      (∀ a x, T (B.right a x) = T x * a) ∧
      (∀ x, f x = ∑ i, LinearMap.trace ℂ (U i) (T x i)) ∧
      ∀ i, h i ≠ r → ∀ x, T x i = 0 := by
  obtain ⟨T, hL, hR, hT⟩ := exists_bimodule_map B (endTrace U)
    (endTrace_comm U) (endTrace_pairing_bijective U) f hf
  let d : ∀ i, Module.End ℂ (U i) := fun i => (h i - r) • 1
  have hcomm (a : ∀ i, Module.End ℂ (U i)) : a * d = d * a := by
    ext i x
    simp [d]
  have hz (x : E) : T (B.left d x) = 0 := by
    apply (endTrace_pairing_bijective U).1
    ext a
    simp only [pairing_apply, map_zero]
    rw [← hL, hT, ← B.left_mul, hcomm, B.left_mul]
    exact homega _
  refine ⟨T, hL, hR, fun x => by simpa using (hT x).symm, ?_⟩
  intro i hi x
  have he := congrArg (fun a => a i) (hz x)
  rw [hL] at he
  change ((h i - r) • (1 : Module.End ℂ (U i))) * T x i = 0 at he
  rw [smul_mul_assoc, one_mul] at he
  exact (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hi)

end VOA.Huang.GenusOne.BimoduleTrace

namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} [Fintype ι]

/-- Weight-selective top realization on the actual insertion Zhu quotient. -/
theorem insertionTopDecomposition_weighted (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (r : ℂ) (f : M →ₗ[ℂ] ℂ)
    (hO : fzO A.toWeakModule ≤ LinearMap.ker f)
    (hbal : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
      f (fzLeft A.toWeakModule p a w) = f (fzRight A.toWeakModule p a w))
    (homega : ∀ w, f (fzLeft A.toWeakModule 2 W.conformalVector w) = r * f w) :
    ∃ T : ∀ i, fzSpace A (P i) (P i),
      (∀ w, f w = ∑ i, LinearMap.trace ℂ (bot (P i)) ((T i).val w)) ∧
      ∀ i, (P i).h ≠ r → T i = 0 := by
  let g := (fzO A.toWeakModule).liftQ f hO
  have hg : ∀ x, g (B.actions.left
      (fun i => ((P i).h - r) • (1 : Module.End ℂ (bot (P i)))) x) = 0 := by
    intro x
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    rw [← insertionCuspOmega_eq_diagonal, insertionCuspOmega_mk]
    change f (fzLeft A.toWeakModule 2 W.conformalVector w - r • w) = 0
    rw [map_sub, map_smul, smul_eq_mul, homega, sub_self]
  obtain ⟨T, hL, hR, hT, hzero⟩ := BimoduleTrace.exists_end_bimodule_map_weighted
    B.actions (fun i => (P i).h) r g (quotient_balanced_of_topBimodule P B f hO hbal) hg
  let C : ∀ i, M →ₗ[ℂ] Module.End ℂ (bot (P i)) := fun i =>
    (LinearMap.proj i).comp (T.comp (fzO A.toWeakModule).mkQ)
  have hCL (p : ℕ) (a : V) (ha : a ∈ W.grading (p : ℤ)) (w : M) (i : ι) :
      C i (fzLeft A.toWeakModule p a w) = rhoLW (P i).isMod (P i).h a * C i w := by
    have ht := congrArg (fun b => b i)
      (hL (insertionTopRep P a) ((fzO A.toWeakModule).mkQ w))
    rw [B.left_mk _ _ ha] at ht
    exact ht
  have hCR (p : ℕ) (a : V) (ha : a ∈ W.grading (p : ℤ)) (w : M) (i : ι) :
      C i (fzRight A.toWeakModule p a w) = C i w * rhoLW (P i).isMod (P i).h a := by
    have ht := congrArg (fun b => b i)
      (hR (insertionTopRep P a) ((fzO A.toWeakModule).mkQ w))
    rw [B.right_mk _ _ ha] at ht
    exact ht
  have hC (i : ι) : C i ∈ fzSpace A (P i) (P i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      change T ((fzO A.toWeakModule).mkQ w) i = 0
      have hq : (fzO A.toWeakModule).mkQ w = 0 := by simpa using hw
      rw [hq, map_zero]
      rfl
    · intro p a ha w x
      rw [hCL p a ha]
      change ((rhoLW (P i).isMod (P i).h a (C i w x) : bot (P i)) : (P i).carrier) = _
      rw [rhoLW_apply_coe, oMod_homogeneous (P i).isMod ha]
    · intro p _ a ha w x x' hx
      rw [hCR p a ha]
      change C i w (rhoLW (P i).isMod (P i).h a x) = C i w x'
      congr 1
      apply Subtype.ext
      rw [rhoLW_apply_coe, oMod_homogeneous (P i).isMod ha, hx]
  refine ⟨fun i => ⟨C i, hC i⟩, fun w => by simpa [g, C] using hT ((fzO A.toWeakModule).mkQ w), ?_⟩
  intro i hi
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  exact hzero i hi ((fzO A.toWeakModule).mkQ w)

/-- The lifts may be chosen zero away from the required weight. Thus their
traces cancel a coefficient at a common exponent, not at unrelated exponents. -/
theorem functional_realized_at_weight (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (hlift : InsertionTopSurjectivity A P)
    (b : ℂ) (f : M →ₗ[ℂ] ℂ)
    (hO : fzO A.toWeakModule ≤ LinearMap.ker f)
    (hbal : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
      f (fzLeft A.toWeakModule p a w) = f (fzRight A.toWeakModule p a w))
    (homega : ∀ w, f (fzLeft A.toWeakModule 2 W.conformalVector w) =
      (b + W.centralCharge / 24) * f w) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      ∀ w, f w = ∑ i, trace (Y i) w b := by
  classical
  obtain ⟨T, hT, hzero⟩ := insertionTopDecomposition_weighted P B
    (b + W.centralCharge / 24) f hO hbal homega
  choose Z hZ using fun i => hlift i (T i)
  let Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod :=
    fun i => if (P i).h = b + W.centralCharge / 24 then Z i else 0
  refine ⟨Y, fun i hi => if_neg hi, fun w => ?_⟩
  rw [hT w]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (P i).h = b + W.centralCharge / 24
  · have hb : b = (P i).h - W.centralCharge / 24 := by rw [hi]; ring
    rw [show Y i = Z i from if_pos hi, hb, trace_leading_eq_top, hZ]
  · rw [show Y i = 0 from if_neg hi, hzero i hi]
    have hz := congrArg (fun t : M →ₗ[ℂ] FormalQSeries => t w b)
      (traceLinear (A := A) (N := (P i).isMod)).map_zero
    change trace (0 : IntertwiningOperator A (P i).isMod (P i).isMod) w b = 0 at hz
    simpa only [ZeroMemClass.coe_zero, LinearMap.zero_apply, map_zero] using hz.symm

/-- Generalized central-character realization, the form needed for the
leading coefficients of logarithmic expansions (Miyamoto (4.23)). Descent,
balance and the generalized relation remain explicit algebraic hypotheses. -/
theorem functional_realized_at_weight_of_generalized (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (hlift : InsertionTopSurjectivity A P)
    (b : ℂ) (f : M →ₗ[ℂ] ℂ)
    (hO : fzO A.toWeakModule ≤ LinearMap.ker f)
    (hbal : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
      f (fzLeft A.toWeakModule p a w) = f (fzRight A.toWeakModule p a w))
    (N : ℕ) (homega : ∀ x, (fzO A.toWeakModule).liftQ f hO
      ((insertionCuspOmega P B (b + W.centralCharge / 24))^[N] x) = 0) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      ∀ w, f w = ∑ i, trace (Y i) w b := by
  have hg := homega
  simp only [insertionCuspOmega_eq_diagonal] at hg
  have hz := BimoduleTrace.central_power_elimination B.actions (fun i => (P i).h)
    (b + W.centralCharge / 24) ((fzO A.toWeakModule).liftQ f hO) N hg
  apply functional_realized_at_weight P B hlift b f hO hbal
  intro w
  have hw := hz ((fzO A.toWeakModule).mkQ w)
  rw [← insertionCuspOmega_eq_diagonal, insertionCuspOmega_mk] at hw
  change f (fzLeft A.toWeakModule 2 W.conformalVector w -
    (b + W.centralCharge / 24) • w) = 0 at hw
  simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hw

end VOA.Huang.GenusOne
