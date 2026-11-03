import VOA.DeligneAudit.D4FusionToroidalFinalCyclic

/-! Stability of the coadjoint graded image under the zero `u` current. -/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V) (m : ℕ)
variable (U : Submodule ℂ V)

theorem subGr_op (hU : ∀ c s, U ≤ U.comap (A.op c 0 s))
    (c : Fin n) (s : ℕ) :
    subGr A w U ≤ (subGr A w U).comap (grOp A w m c 0 s) := by
  rw [subGr, Submodule.span_le]
  rintro _ ⟨d, x, hx, hu, rfl⟩
  change grOp A w m c 0 s _ ∈ subGr A w U
  by_cases hs : s < m
  · rw [grOp_single A w m c 0 s d hs x hx]
    apply Submodule.subset_span
    refine ⟨d + s, A.op c 0 s x, ?_, hU c s hu, rfl⟩
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      evalFbelow_op A w c 0 s (d + 1) hx
  · rw [grOp_high_zero A w m c 0 s (Nat.le_of_not_lt hs)]
    exact Submodule.zero_mem _

theorem subGr_generator (hw : w ∈ U) : grGenerator A w ∈ subGr A w U := by
  apply Submodule.subset_span
  exact ⟨0, w, generator_mem A w, hw, rfl⟩

end

end VOA.DeligneAudit.Toroidal.FusionGr

namespace VOA.DeligneAudit.Toroidal.D4Fusion

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

noncomputable section

def coadjointSource (N : ℕ) : Submodule ℂ (D1TensorG.Space 28 N) :=
  LinearMap.range (FusionUZero.embedCo 28 N)

theorem coadjointSource_generator (N : ℕ) :
    generator N ∈ coadjointSource N := by
  refine ⟨PiTensorProduct.tprod ℂ (fun _ : Fin N =>
    (Pi.single D4sector.c₀ 1 : D1SiteG.Co 28)), ?_⟩
  simp [FusionUZero.embedCo, generator, D4sector, D1TensorG.D4Check.highest,
    D1TensorG.generator, PiTensorProduct.map_tprod, D1SiteG.inCo, D1SiteG.w]

theorem coadjointSource_local (N : ℕ) (q : Fin N) (c : Fin 28) :
    coadjointSource N ≤ (coadjointSource N).comap
      (localOp q (D1SiteG.zeroOp (fC 28 br) c)) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨localOp q (D1SiteG.coOp (fC 28 br) c) v, ?_⟩
  have he : (localOp q (D1SiteG.zeroOp (fC 28 br) c)).comp
      (FusionUZero.embedCo 28 N) =
      (FusionUZero.embedCo 28 N).comp
        (localOp q (D1SiteG.coOp (fC 28 br) c)) := by
    apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top)
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, FusionUZero.embedCo,
      PiTensorProduct.map_tprod, localOp_tprod, D1SiteG.zeroOp, D1SiteG.inCo]
    congr 1
    funext j
    by_cases hj : j = q
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  exact congrArg (fun T : FusionUZero.CoTensor 28 N →ₗ[ℂ]
    D1TensorG.Space 28 N => T v) he |>.symm

theorem coadjointSource_op (N : ℕ) (c : Fin 28) (s : ℕ) :
    coadjointSource N ≤ (coadjointSource N).comap ((action N).op c 0 s) := by
  intro v hv
  change ((action N).op c 0 s) v ∈ coadjointSource N
  rw [action, d1EvalAction_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro q _
  apply Submodule.smul_mem
  change localOp q (D1SiteG.zeroOp (fC 28 br) c) v ∈ coadjointSource N
  exact coadjointSource_local N q c hv

end

end VOA.DeligneAudit.Toroidal.D4Fusion

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.subGr_op
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.coadjointSource_op
