import VOA.DeligneAudit.DeligneFusionCLAssembly
import VOA.DeligneAudit.DeligneFusionAssembly
import VOA.DeligneAudit.DeligneFusionCount

/-!
# `FusionTotalDim` from the kernel lower bound (S2)

The relations of `M_{a,b+1}` imply those of `M_{a+1,b}` (`mabRel_succ`), so there is a surjection
`π : U_{a+1,b} → U_{a,b+1}` (`univMap`) killing Ravinder's kernel vector `vK = f_θ(2a+b+1) wU`, hence killing
`SK = U·vK`.  Rank–nullity on the degree-`M` piece gives

  `u_{a,b+1}(M) + dim (U·vK)_{M−s} ≤ u_{a+1,b}(M)`,  `s = 2a+b+1`  (`step_kernel`),

and `dim (U·vK)_n` dominates the same count in any model (`kU_ge_model`).  With (S1) at `b = 0`
(`finrank_cycDeg_le` and `demazureHilb_sum`), an induction on `b` gives `Σ u_{a,b} ≤ 9^a 8^b`, in particular
`FusionTotalDim`, from the single named residual `RavinderKernelLower` (`fusionTotalDim_of_kernelLower`).
-/

namespace VOA.DeligneAudit.A2

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneGaussian VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- **S2, the kernel lower bound**: in some model of `M_{a+1,b}`, the cyclic module of Ravinder's kernel
vector `f_θ(2a+b+1) w` has total dimension at least `9^a 8^b`. -/
def RavinderKernelLower : Prop :=
  ∀ a b : ℕ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : CurrentModule (bracketTable) V)
    (w : V), MabRel ρ w (a + 1) b ∧
    ∃ B, 9 ^ a * 8 ^ b ≤ ∑ n ∈ Finset.range B,
      Module.finrank ℂ (cycDeg ρ (ρ.op 5 (2 * a + b + 1) w) n)

/-- The relations of `M_{a,b+1}` imply those of `M_{a+1,b}`. -/
theorem mabRel_succ {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}
    {w : V} {a b : ℕ} (h : MabRel ρ w a (b + 1)) : MabRel ρ w (a + 1) b where
  raising := h.raising
  cartan_pos := h.cartan_pos
  cartan_zero hh h6 := by rw [h.cartan_zero hh h6]; congr 2; omega
  lowering_f1 := by rw [show a + 1 + b + 1 = a + (b + 1) + 1 by omega]; exact h.lowering_f1
  lowering_f2 := by rw [show a + 1 + b + 1 = a + (b + 1) + 1 by omega]; exact h.lowering_f2
  trunc_f1 := by rw [show a + 1 + b = a + (b + 1) by omega]; exact h.trunc_f1
  trunc_f2 := by rw [show a + 1 + b = a + (b + 1) by omega]; exact h.trunc_f2
  trunc_theta := by
    have := f_trunc_up (fα := 5) (by decide) (by decide) h.trunc_theta
      (fun j hj => h.cartan_pos 6 (by decide) j hj) 1
    rw [show 2 * (a + 1) + b = 2 * a + (b + 1) + 1 by omega]; exact this

/-- All degree pieces of all universal modules are finite-dimensional (unconditionally). -/
theorem univ_fd0 : ∀ a b N, FiniteDimensional ℂ (cycDeg (univRep a b) (SectorWeyl.wU a b) N)
  | 0, b, N => cycDeg_finiteDimensional ((mabRel_zero_iff _ _ _).mp (univ_mabRel 0 b)) N
  | a + 1, b, N => by
      haveI := univ_fd0 a (b + 1) N
      haveI := univ_fd0 a b (N - (2 * a + b + 1))
      exact SectorWeyl.fd_step a b (ravinderKernelRel_of_trunc ravinderKernelTrunc) N

/-- Rank–nullity for a submodule, as an equality. -/
theorem finrank_map_add_inf_ker {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (f : V →ₗ[ℂ] W) (P : Submodule ℂ V) [FiniteDimensional ℂ P] :
    Module.finrank ℂ (P.map f) + Module.finrank ℂ (P ⊓ LinearMap.ker f : Submodule ℂ V) =
      Module.finrank ℂ P := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have e : Module.finrank ℂ ((LinearMap.ker f).comap P.subtype) =
      Module.finrank ℂ (P ⊓ LinearMap.ker f : Submodule ℂ V) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective P.subtype P.injective_subtype _).finrank_eq
  omega

section Step

variable (a b : ℕ)

/-- The degree-`n` piece of the cyclic module of `vK` in `U_{a+1,b}`. -/
abbrev kU (n : ℕ) : Submodule ℂ (UMod (a + 1) b) := cycDeg (univRep (a + 1) b) (vK a b) n

theorem wordOp_vK' (l : List Ltr) :
    wordOp (univRep (a + 1) b) l (vK a b) =
      wordOp (univRep (a + 1) b) (l ++ [((5 : Fin 8), 2 * a + b + 1)]) (SectorWeyl.wU (a + 1) b) := by
  rw [wordOp_append]; rfl

theorem kU_le (n : ℕ) :
    kU a b n ≤ cycDeg (univRep (a + 1) b) (SectorWeyl.wU (a + 1) b) (n + (2 * a + b + 1)) ⊓ SK a b := by
  rw [kU, cycDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  refine ⟨Submodule.subset_span ⟨_, ?_, wordOp_vK' a b l⟩, wordOp_mem_cycSub _ _ l⟩
  simp only [SectorGraded.wordDeg, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil] at hl ⊢
  omega

instance (n : ℕ) : FiniteDimensional ℂ (kU a b n) := by
  haveI := univ_fd0 (a + 1) b (n + (2 * a + b + 1))
  exact Submodule.finiteDimensional_of_le ((kU_le a b n).trans inf_le_left)

/-- The surjection `π : U_{a+1,b} → U_{a,b+1}`. -/
abbrev piU : UMod (a + 1) b →ₗ[ℂ] UMod a (b + 1) := univMap (mabRel_succ (univ_mabRel a (b + 1)))

theorem SK_le_ker : SK a b ≤ LinearMap.ker (piU a b) := by
  rw [SK, cycSub, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  rw [wordOp_vK', univMap_wordOp, wordOp_append]
  have : wordOp (univRep a (b + 1)) [((5 : Fin 8), 2 * a + b + 1)] (SectorWeyl.wU a (b + 1)) = 0 := by
    have := (univ_mabRel a (b + 1)).trunc_theta
    rw [show 2 * a + (b + 1) = 2 * a + b + 1 by omega] at this
    exact this
  rw [this, wordOp_zero]

/-- **The kernel step**: `u_{a,b+1}(n+s) + dim (U·vK)_n ≤ u_{a+1,b}(n+s)`. -/
theorem step_kernel (n : ℕ) :
    Module.finrank ℂ (cycDeg (univRep a (b + 1)) (SectorWeyl.wU a (b + 1)) (n + (2 * a + b + 1))) +
      Module.finrank ℂ (kU a b n) ≤
    Module.finrank ℂ (cycDeg (univRep (a + 1) b) (SectorWeyl.wU (a + 1) b) (n + (2 * a + b + 1))) := by
  set P := cycDeg (univRep (a + 1) b) (SectorWeyl.wU (a + 1) b) (n + (2 * a + b + 1))
  haveI : FiniteDimensional ℂ P := univ_fd0 (a + 1) b _
  have h := finrank_map_add_inf_ker (piU a b) P
  rw [map_cycDeg] at h
  have hk : kU a b n ≤ P ⊓ LinearMap.ker (piU a b) :=
    fun x hx => ⟨((kU_le a b n) hx).1, SK_le_ker a b ((kU_le a b n) hx).2⟩
  have := Submodule.finrank_mono hk
  omega

/-- Below the shift, `u_{a,b+1}(M) ≤ u_{a+1,b}(M)`. -/
theorem step_le (M : ℕ) :
    Module.finrank ℂ (cycDeg (univRep a (b + 1)) (SectorWeyl.wU a (b + 1)) M) ≤
      Module.finrank ℂ (cycDeg (univRep (a + 1) b) (SectorWeyl.wU (a + 1) b) M) := by
  haveI := univ_fd0 (a + 1) b M
  exact finrank_cycDeg_le_univ (mabRel_succ (univ_mabRel a (b + 1))) M

/-- `dim (U·vK)_n` dominates the same count in any model of `M_{a+1,b}`. -/
theorem kU_ge_model {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}
    {w : V} (h : MabRel ρ w (a + 1) b) (n : ℕ) :
    Module.finrank ℂ (cycDeg ρ (ρ.op 5 (2 * a + b + 1) w) n) ≤ Module.finrank ℂ (kU a b n) := by
  have : (kU a b n).map (univMap h) = cycDeg ρ (ρ.op 5 (2 * a + b + 1) w) n := by
    rw [kU, cycDeg, cycDeg, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨u, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨l, hl, ?_⟩
      rw [wordOp_vK', univMap_wordOp, wordOp_append]; rfl
    · rintro ⟨l, hl, rfl⟩
      refine ⟨_, ⟨l, hl, rfl⟩, ?_⟩
      rw [wordOp_vK', univMap_wordOp, wordOp_append]; rfl
  rw [← this]
  exact Submodule.finrank_map_le _ _

end Step

/-- The truncated total of `U_{a,b}`. -/
abbrev uTot (a b B : ℕ) : ℕ :=
  ∑ M ∈ Finset.range B, Module.finrank ℂ (cycDeg (univRep a b) (SectorWeyl.wU a b) M)

theorem uTot_mono (a b : ℕ) {B B' : ℕ} (h : B ≤ B') : uTot a b B ≤ uTot a b B' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- **Totals of the universal modules** from (S1) and S2: `Σ u_{a,b} ≤ 9^a 8^b`. -/
theorem uTot_le (hK : RavinderKernelLower) : ∀ b a B, uTot a b B ≤ 9 ^ a * 8 ^ b
  | 0, a, B => by
      obtain ⟨B1, hB0, hB1⟩ := demazureHilb_sum a
      have hle : ∀ M, Module.finrank ℂ (cycDeg (univRep a 0) (SectorWeyl.wU a 0) M) ≤
          demazureHilb a M := fun M => CLAssembly.finrank_cycDeg_le (univ_mabRel a 0) M
      calc uTot a 0 B ≤ uTot a 0 (max B B1) := uTot_mono a 0 (le_max_left _ _)
        _ ≤ ∑ M ∈ Finset.range (max B B1), demazureHilb a M := Finset.sum_le_sum fun M _ => hle M
        _ = 9 ^ a := by
          rw [← hB1]
          refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun e he he' => ?_).symm
          exact hB0 e (by simp at he he'; omega)
        _ = 9 ^ a * 8 ^ 0 := by ring
  | b + 1, a, B => by
      obtain ⟨V, _, _, ρ, w, hR, B0, hB0⟩ := hK a b
      set s := 2 * a + b + 1
      set B' := max B B0
      have ih := uTot_le hK b (a + 1) (s + B')
      have hk : 9 ^ a * 8 ^ b ≤ ∑ n ∈ Finset.range B', Module.finrank ℂ (kU a b n) :=
        hB0.trans ((Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_right _ _))).trans
          (Finset.sum_le_sum fun n _ => kU_ge_model a b hR n))
      have hsplit : uTot a (b + 1) (s + B') + ∑ n ∈ Finset.range B', Module.finrank ℂ (kU a b n) ≤
          uTot (a + 1) b (s + B') := by
        simp only [uTot, Finset.sum_range_add]
        have h1 : ∑ x ∈ Finset.range s, Module.finrank ℂ (cycDeg (univRep a (b + 1)) (SectorWeyl.wU a (b + 1)) x) ≤
            ∑ x ∈ Finset.range s, Module.finrank ℂ (cycDeg (univRep (a + 1) b) (SectorWeyl.wU (a + 1) b) x) :=
          Finset.sum_le_sum fun M _ => step_le a b M
        have h2 : ∑ x ∈ Finset.range B', (Module.finrank ℂ
              (cycDeg (univRep a (b + 1)) (SectorWeyl.wU a (b + 1)) (s + x)) + Module.finrank ℂ (kU a b x)) ≤
            ∑ x ∈ Finset.range B', Module.finrank ℂ (cycDeg (univRep (a + 1) b) (SectorWeyl.wU (a + 1) b) (s + x)) :=
          Finset.sum_le_sum fun n _ => by rw [add_comm s n]; exact step_kernel a b n
        rw [Finset.sum_add_distrib] at h2
        omega
      have hB : uTot a (b + 1) B ≤ uTot a (b + 1) (s + B') := uTot_mono a (b + 1) (by omega)
      have e : 9 ^ (a + 1) * 8 ^ b = 9 * (9 ^ a * 8 ^ b) := by ring
      have e2 : 9 ^ a * 8 ^ (b + 1) = 8 * (9 ^ a * 8 ^ b) := by ring
      omega

/-- **`FusionTotalDim` from S2**: the A₂ dimension input reduces to `RavinderKernelLower`. -/
theorem fusionTotalDim_of_kernelLower (hK : RavinderKernelLower) : FusionTotalDim := by
  intro m V _ _ ρ w hW B
  have h0 := (mabRel_zero_iff ρ w m).mpr hW
  calc ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ uTot 0 m B :=
        Finset.sum_le_sum fun N _ => by
          haveI := univ_fd0 0 m N
          exact finrank_cycDeg_le_univ h0 N
    _ ≤ 9 ^ 0 * 8 ^ m := uTot_le hK m 0 B
    _ = 8 ^ m := by ring

/-- **A₂ classical freeness from S2 and U7.** -/
theorem classicallyFree_of_kernelLower (hK : RavinderKernelLower) (hD : ∀ n, DemazureRealization n) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_totalDim (fusionTotalDim_of_kernelLower hK) hD

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.step_kernel
#print axioms VOA.DeligneAudit.A2.fusionTotalDim_of_kernelLower
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_kernelLower
end AxiomAudit
