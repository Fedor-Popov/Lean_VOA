import VOA.DeligneAudit.DeligneFusionKernelLower

/-!
# `M_{0,N} = D(N)/(g⊗t^N ℂ[t])·D(N)` and the ideal form of `FusionTotalDim`

In a module with `MabRel ρ w 0 N` every current mode `x ⊗ tᵏ`, `k ≥ N`, kills the whole cyclic module
(`trunc_all`: the Lie ideal `g⊗t^Nℂ[t]` kills `w`).  Hence the surjection `U_{N,0} ↠ U_{0,N}` kills
`I·U_{N,0}`, whose degree-`d` part `IVd` is spanned by `x⊗tᵏ · (word) · w`, `k ≥ N`.  Rank–nullity in each degree,
(S1) for `U_{N,0}` and the transfer of `IVd` from any model give:

**`fusionTotalDim_of_idealLower`**: if for every `N` some model of `M_{N,0}` has `Σ_d dim IVd ≥ 9^N − 8^N`, then
`FusionTotalDim` holds.  This is the interface for Feigin's route (Cor. 3.9: `D(N)/I·D(N) ≅ g^{**N}`).
-/

namespace VOA.DeligneAudit.A2

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

/-- The degree-`d` part of `I·⟨w⟩`: span of `x ⊗ tᵏ · (word) · w` with `k ≥ N`, total degree `d`. -/
def IVd {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V) (N d : ℕ) :
    Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ (c : Fin 8) (k : ℕ) (l : List (Fin 8 × ℕ)), N ≤ k ∧
    k + SectorGraded.wordDeg l = d ∧ v = ρ.op c k (wordOp ρ l w)}

/-- `MabRel a (b + j) ⇒ MabRel (a + j) b`. -/
theorem mabRel_shift {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}
    {w : V} {a b : ℕ} : ∀ j, MabRel ρ w a (b + j) → MabRel ρ w (a + j) b
  | 0, h => h
  | j + 1, h => by
      have := mabRel_shift j (mabRel_succ (show MabRel ρ w a (b + j + 1) from h))
      rwa [show a + 1 + j = a + (j + 1) by ring] at this

/-- In `M_{0,N}` every mode `≥ N` kills the whole cyclic module. -/
theorem trunc_all {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}
    {w : V} {N : ℕ} (h : MabRel ρ w 0 N) :
    ∀ (l : List (Fin 8 × ℕ)) (c : Fin 8) (k : ℕ), N ≤ k → ρ.op c k (wordOp ρ l w) = 0
  | [], c, k, hk => by
      change ρ.op c k w = 0
      have hcart : ∀ j, 1 ≤ j → ρ.op 6 j w = 0 := fun j hj => h.cartan_pos 6 (by decide) j hj
      rcases (show c.val < 3 ∨ (3 ≤ c.val ∧ c.val < 6) ∨ 6 ≤ c.val by omega) with hc | hc | hc
      · exact h.raising c hc k
      · obtain ⟨j, rfl⟩ : ∃ j, k = N + j := ⟨k - N, by omega⟩
        have : c = 3 ∨ c = 4 ∨ c = 5 := by omega
        rcases this with rfl | rfl | rfl
        · exact f_trunc_up (by decide) (by decide) (by simpa using h.trunc_f1) hcart j
        · exact f_trunc_up (by decide) (by decide) (by simpa using h.trunc_f2) hcart j
        · exact f_trunc_up (by decide) (by decide) (by simpa using h.trunc_theta) hcart j
      · rcases Nat.eq_zero_or_pos k with rfl | hk1
        · have := h.cartan_zero c hc
          have hN : N = 0 := by omega
          subst hN; simpa using this
        · exact h.cartan_pos c hc k hk1
  | (x :: l), c, k, hk => by
      change ρ.op c k (ρ.op x.1 x.2 (wordOp ρ l w)) = 0
      rw [comm_apply c x.1 k x.2, trunc_all h l c k hk]
      simp only [map_zero, zero_add]
      exact Finset.sum_eq_zero fun e _ => by rw [trunc_all h l e (k + x.2) (by omega), smul_zero]

theorem IVd_le_cyc {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V)
    (N d : ℕ) : IVd ρ w N d ≤ cycDeg ρ w d := by
  rw [IVd, Submodule.span_le]
  rintro _ ⟨c, k, l, -, hd, rfl⟩
  exact Submodule.subset_span ⟨(c, k) :: l, by simp [SectorGraded.wordDeg] at hd ⊢; omega, rfl⟩

/-- `IVd` of the universal module dominates `IVd` of any model. -/
theorem IVd_ge_model {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}
    {w : V} {N : ℕ} (h : MabRel ρ w N 0) (d : ℕ) :
    Module.finrank ℂ (IVd ρ w N d) ≤ Module.finrank ℂ (IVd (univRep N 0) (SectorWeyl.wU N 0) N d) := by
  haveI := univ_fd0 N 0 d
  haveI : FiniteDimensional ℂ (IVd (univRep N 0) (SectorWeyl.wU N 0) N d) :=
    Submodule.finiteDimensional_of_le (IVd_le_cyc _ _ N d)
  have : (IVd (univRep N 0) (SectorWeyl.wU N 0) N d).map (univMap h) = IVd ρ w N d := by
    rw [IVd, IVd, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨_, ⟨c, k, l, hk, hd, rfl⟩, rfl⟩
      exact ⟨c, k, l, hk, hd, univMap_wordOp h ((c, k) :: l)⟩
    · rintro ⟨c, k, l, hk, hd, rfl⟩
      exact ⟨_, ⟨c, k, l, hk, hd, rfl⟩, univMap_wordOp h ((c, k) :: l)⟩
  rw [← this]
  exact Submodule.finrank_map_le _ _

/-- The degree-wise inequality `u_{0,N}(d) + dim (I·U_{N,0})_d ≤ u_{N,0}(d)`. -/
theorem step_ideal (N d : ℕ) :
    Module.finrank ℂ (cycDeg (univRep 0 N) (SectorWeyl.wU 0 N) d) +
      Module.finrank ℂ (IVd (univRep N 0) (SectorWeyl.wU N 0) N d) ≤
    Module.finrank ℂ (cycDeg (univRep N 0) (SectorWeyl.wU N 0) d) := by
  have hR : MabRel (univRep 0 N) (SectorWeyl.wU 0 N) N 0 := by
    have := mabRel_shift (a := 0) (b := 0) N (by simpa using univ_mabRel 0 N); simpa using this
  set P := cycDeg (univRep N 0) (SectorWeyl.wU N 0) d
  haveI : FiniteDimensional ℂ P := univ_fd0 N 0 d
  have h := finrank_map_add_inf_ker (univMap hR) P
  rw [map_cycDeg] at h
  have hk : IVd (univRep N 0) (SectorWeyl.wU N 0) N d ≤ P ⊓ LinearMap.ker (univMap hR) := by
    refine le_inf (IVd_le_cyc _ _ N d) ?_
    rw [IVd, Submodule.span_le]
    rintro _ ⟨c, k, l, hkN, -, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [show (univRep N 0).op c k (wordOp (univRep N 0) l (SectorWeyl.wU N 0)) =
      wordOp (univRep N 0) ((c, k) :: l) (SectorWeyl.wU N 0) from rfl, univMap_wordOp]
    exact trunc_all (univ_mabRel 0 N) l c k hkN
  have := Submodule.finrank_mono hk
  omega

theorem uTot_base (a B : ℕ) : uTot a 0 B ≤ 9 ^ a := by
  obtain ⟨B1, hB0, hB1⟩ := demazureHilb_sum a
  have hle : ∀ M, Module.finrank ℂ (cycDeg (univRep a 0) (SectorWeyl.wU a 0) M) ≤
      demazureHilb a M := fun M => CLAssembly.finrank_cycDeg_le (univ_mabRel a 0) M
  calc uTot a 0 B ≤ uTot a 0 (max B B1) := uTot_mono a 0 (le_max_left _ _)
    _ ≤ ∑ M ∈ Finset.range (max B B1), demazureHilb a M := Finset.sum_le_sum fun M _ => hle M
    _ = 9 ^ a := by
      rw [← hB1]
      refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun e he he' => ?_).symm
      exact hB0 e (by simp at he he'; omega)

/-- **The ideal lower bound** (the interface for Feigin's route): some model of `M_{N,0}` has
`Σ_d dim (I·⟨w⟩)_d ≥ 9^N − 8^N`. -/
def IdealLower : Prop :=
  ∀ N : ℕ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : CurrentModule (bracketTable) V)
    (w : V), MabRel ρ w N 0 ∧ ∃ B, 9 ^ N ≤ 8 ^ N + ∑ d ∈ Finset.range B, Module.finrank ℂ (IVd ρ w N d)

/-- **`FusionTotalDim` from the ideal lower bound.** -/
theorem fusionTotalDim_of_idealLower (hI : IdealLower) : SectorWeyl.FusionTotalDim := by
  intro m V _ _ ρ w hW B
  obtain ⟨V', _, _, ρ', w', hR', B0, hB0⟩ := hI m
  set B' := max B B0
  have hsum : uTot 0 m B' + ∑ d ∈ Finset.range B', Module.finrank ℂ (IVd ρ' w' m d) ≤ uTot m 0 B' := by
    rw [uTot, uTot, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun d _ => (Nat.add_le_add_left (IVd_ge_model hR' d) _).trans (step_ideal m d)
  have hmono : ∑ d ∈ Finset.range B0, Module.finrank ℂ (IVd ρ' w' m d) ≤
      ∑ d ∈ Finset.range B', Module.finrank ℂ (IVd ρ' w' m d) :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_right _ _))
  have hbase := uTot_base m B'
  have h0 := (mabRel_zero_iff ρ w m).mpr hW
  calc ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ uTot 0 m B :=
        Finset.sum_le_sum fun N _ => by
          haveI := univ_fd0 0 m N
          exact finrank_cycDeg_le_univ h0 N
    _ ≤ uTot 0 m B' := uTot_mono 0 m (le_max_left _ _)
    _ ≤ 8 ^ m := by omega

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.trunc_all
#print axioms VOA.DeligneAudit.A2.fusionTotalDim_of_idealLower
end AxiomAudit
