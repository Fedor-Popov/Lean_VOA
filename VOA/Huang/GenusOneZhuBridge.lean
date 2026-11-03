import VOA.Huang.GenusOneTopRealization
import VOA.Huang.GenusOneBimoduleTrace

/-! # From quotient bimodule actions to the actual Frenkel–Zhu top space

This bridge proves the trace-decomposition step once the quotient action laws
and the full top representation are supplied. The residual contains neither
trace functionals nor intertwiner lifting. Its intended hypotheses are a
rational C₂-cofinite VOA and a complete irredundant family of irreducibles.
Sources: Frenkel–Zhu's bimodule theorem and Miyamoto, math/0010180, Lemma 4.10.
-/
namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} [Fintype ι]

/-- The simultaneous zero-mode representation, before descent through `O(V)`. -/
noncomputable def insertionTopRep (P : ι → LWModule W) :
    V →ₗ[ℂ] (∀ i, Module.End ℂ (bot (P i))) :=
  LinearMap.pi fun i => rhoLW (P i).isMod (P i).h

/-- The missing quotient algebra: an action of the full algebra of top
endomorphisms on `M/O(M)` agreeing with the raw Frenkel–Zhu operations.
Surjectivity identifies this algebra with the image of `A(V)`. -/
structure InsertionTopBimodule (A : OrdVModule W M) (P : ι → LWModule W) where
  actions : BimoduleTrace.Actions (∀ i, Module.End ℂ (bot (P i)))
    (M ⧸ fzO A.toWeakModule)
  full : Function.Surjective (insertionTopRep P)
  left_mk : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
    actions.left (insertionTopRep P a) ((fzO A.toWeakModule).mkQ w) =
      (fzO A.toWeakModule).mkQ (fzLeft A.toWeakModule p a w)
  right_mk : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
    actions.right (insertionTopRep P a) ((fzO A.toWeakModule).mkQ w) =
      (fzO A.toWeakModule).mkQ (fzRight A.toWeakModule p a w)

/-- Named remaining quotient-action target. No trace-spanning assertion is
included. Constructing it still requires the module Zhu associator identities. -/
def InsertionTopBimoduleExists (A : OrdVModule W M) (P : ι → LWModule W) : Prop :=
  Nonempty (InsertionTopBimodule A P)

omit [Fintype ι] in
/-- Balance on homogeneous states is balance for the entire top algebra. -/
theorem quotient_balanced_of_topBimodule (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (f : M →ₗ[ℂ] ℂ)
    (hO : fzO A.toWeakModule ≤ LinearMap.ker f)
    (hbal : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
      f (fzLeft A.toWeakModule p a w) = f (fzRight A.toWeakModule p a w)) :
    ∀ a x, (fzO A.toWeakModule).liftQ f hO (B.actions.left a x) =
      (fzO A.toWeakModule).liftQ f hO (B.actions.right a x) := by
  intro a x
  obtain ⟨v, rfl⟩ := B.full a
  obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
  refine ordinaryGrading_induction W (P := fun v =>
    (fzO A.toWeakModule).liftQ f hO
      (B.actions.left (insertionTopRep P v) ((fzO A.toWeakModule).mkQ w)) =
    (fzO A.toWeakModule).liftQ f hO
      (B.actions.right (insertionTopRep P v) ((fzO A.toWeakModule).mkQ w))) ?_ ?_ ?_ v
  · intro k v hv
    by_cases hk : k < 0
    · rw [W.positivity k hk, Submodule.mem_bot] at hv
      simp [hv]
    · have hv' : v ∈ W.grading (k.toNat : ℤ) := by rwa [Int.toNat_of_nonneg (by omega)]
      rw [B.left_mk _ _ hv', B.right_mk _ _ hv']
      exact hbal _ _ hv' w
  · simp
  · intro v v' hv hv'
    simp only [map_add, LinearMap.add_apply, hv, hv']

/-- The abstract bimodule map lands in the library's `fzSpace`, with its exact
left and right top identities. -/
theorem insertionSymmetricTopDecomposition_of_bimodule (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) : InsertionSymmetricTopDecomposition A P := by
  intro f hO hbal
  let g := (fzO A.toWeakModule).liftQ f hO
  obtain ⟨T, hL, hR, hT⟩ := BimoduleTrace.exists_bimodule_map B.actions
    (BimoduleTrace.endTrace (fun i => bot (P i))) (BimoduleTrace.endTrace_comm _)
    (BimoduleTrace.endTrace_pairing_bijective _ ) g
    (quotient_balanced_of_topBimodule P B f hO hbal)
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
  refine ⟨fun i => ⟨C i, hC i⟩, fun w => ?_⟩
  simpa [g, C] using (hT ((fzO A.toWeakModule).mkQ w)).symm

/-- Full algebraic leading realization, with quotient actions as the
remaining decomposition input; lifting is still the separate Li theorem. -/
theorem leading_realized_of_bimodule (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P) (hlift : InsertionTopSurjectivity A P)
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      ∀ w, S w b = ∑ i, trace (Y i) w ((P i).h - W.centralCharge / 24) := by
  obtain ⟨B⟩ := hB
  exact leading_realized_on_tops P (insertionSymmetricTopDecomposition_of_bimodule P B)
    hlift hsupp hS

end VOA.Huang.GenusOne
