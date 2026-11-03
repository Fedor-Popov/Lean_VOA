import VOA.DeligneAudit.D4FusionToroidalStarB
import VOA.DeligneAudit.D4FusionToroidalStarB2Series
import VOA.DeligneAudit.D4FusionToroidalStarB2Graded

/-!
# (★b, all `j`): the tuple expansion of `P^{(j)}_N w` in the evaluation tensor model

With `Z = (c₀ ⊗ 1)` (coadjoint) and `O = (c₀ ⊗ u)` (evaluation into the line) at each site,

`[z^b] g(z)^j w = ∑_{p : Fin j → Fin m} h_b(z ∘ p) · O_{p 0} ⋯ O_{p (j−1)} w`,

`P^{(j)}_N w = ∑_{p : Fin (j+1) → Fin m} h_N(z ∘ p) · Z_{p 0} O_{p 1} ⋯ O_{p j} w`
(`PsymA_eq`),

and the vectors `W_p = Z_{p 0} O_{p 1} ⋯ O_{p j} w` vanish for non-injective `p` (`O` kills the
line, `Z` kills the line).  The scalar reduction `hvecT_mem` then places `P^{(j)}_N w` in the
`t`-degree `< N` filtration piece for `N ≥ m − j` (`PsymA_mem`), and the graded transfer
`Psym_zero_of_mem` gives `P^{(j)}_N v_F = 0`.  Specialised to `D4`: `Jprime_le_annF`, i.e. the
named Prop `Toroidal.JprimeLeAnnF m`, for every `m ≥ 1`.
-/

namespace VOA.DeligneAudit.Toroidal.StarB2

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.Toroidal.StarB
open Finset PowerSeries

noncomputable section

section Generic

variable {n m : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (hJ : JacobiCoord f)
  (hskew : ∀ a b c, f a b c = -f b a c) (z : Fin m → ℂ) (c₀ : Fin n)

/-- The reindexing of a double sum over `Fin m × (Fin j → Fin m)` as a sum over
`Fin (j + 1) → Fin m`. -/
theorem reindex (j : ℕ) (α : Fin m → ℂ) (β : (Fin j → Fin m) → ℂ)
    (B : Module.End ℂ (D1SiteG.Space n)) (G : (Fin j → Fin m) → Space n m) :
    ∑ q, α q • localOp q B (∑ p, β p • G p) =
      ∑ p' : Fin (j + 1) → Fin m,
        (α (p' 0) * β (Fin.tail p')) • localOp (p' 0) B (G (Fin.tail p')) := by
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin m) _ _ (fun qp => by
    simp [Fin.consEquiv, Fin.tail_cons, Fin.cons_zero])

/-- `O_{p 0} ⋯ O_{p (j−1)} v`. -/
def OW : (j : ℕ) → (Fin j → Fin m) → Space n m → Space n m
  | 0, _, v => v
  | j + 1, p, v => localOp (p 0) (D1SiteG.op f c₀ 1) (OW j (Fin.tail p) v)

theorem hT_cons (j : ℕ) (q : Fin m) (p : Fin j → Fin m) (N : ℕ) :
    hT z (j + 1) (Fin.cons q p) N =
      ∑ ab ∈ antidiagonal N, z q ^ ab.1 * hT z j p ab.2 := by
  simp only [hT, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, coeff_mul, geo, coeff_mk]

/-- One evaluation letter applied to an `h`-expansion. -/
theorem expand_step (j : ℕ) (c : Fin n) (i : ℕ) (G : (Fin j → Fin m) → Space n m)
    (Y : ℕ → Space n m) (hY : ∀ b, Y b = ∑ p, hT z j p b • G p) (N : ℕ) :
    ∑ ab ∈ antidiagonal N, (act f hJ hskew z).op c i ab.1 (Y ab.2) =
      ∑ p' : Fin (j + 1) → Fin m,
        hT z (j + 1) p' N • localOp (p' 0) (D1SiteG.op f c i) (G (Fin.tail p')) := by
  have h1 : ∀ ab ∈ antidiagonal N, (act f hJ hskew z).op c i ab.1 (Y ab.2) =
      ∑ p' : Fin (j + 1) → Fin m,
        (z (p' 0) ^ ab.1 * hT z j (Fin.tail p') ab.2) •
          localOp (p' 0) (D1SiteG.op f c i) (G (Fin.tail p')) := by
    intro ab _
    rw [act_op_apply, hY, reindex]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun p' _ => ?_
  rw [← sum_smul]
  congr 1
  rw [← Fin.cons_self_tail p', hT_cons, Fin.cons_zero, Fin.tail_cons]

theorem gpowA_eq (j : ℕ) :
    ∀ b, FusionGr.StarB2.gpowA (act f hJ hskew z) c₀ j b (gen c₀) =
      ∑ p : Fin j → Fin m, hT z j p b • OW f c₀ j p (gen c₀) := by
  induction j with
  | zero =>
    intro b
    rw [Fintype.sum_subsingleton _ (fun i => i.elim0)]
    simp only [FusionGr.StarB2.gpowA, OW, hT, Fin.prod_univ_zero, coeff_one]
    split_ifs <;> simp
  | succ j ih =>
    intro b
    simp only [FusionGr.StarB2.gpowA]
    rw [expand_step f hJ hskew z j c₀ 1 (fun p => OW f c₀ j p (gen c₀)) _ ih b]
    rfl

/-- The tuple vectors `W_p = Z_{p 0} O_{p 1} ⋯ O_{p j} w`. -/
def Wt (j : ℕ) (p : Fin (j + 1) → Fin m) : Space n m :=
  localOp (p 0) (D1SiteG.op f c₀ 0) (OW f c₀ j (Fin.tail p) (gen c₀))

/-- `P^{(j)}_N w = ∑_p h_N(z ∘ p) W_p`. -/
theorem PsymA_eq (j N : ℕ) :
    FusionGr.StarB2.PsymA (act f hJ hskew z) c₀ j N (gen c₀) =
      ∑ p : Fin (j + 1) → Fin m, hT z (j + 1) p N • Wt f c₀ j p := by
  simp only [FusionGr.StarB2.PsymA]
  rw [expand_step f hJ hskew z j c₀ 0 (fun p => OW f c₀ j p (gen c₀)) _
    (gpowA_eq f hJ hskew z c₀ j) N]
  rfl

/-! ## Vanishing on non-injective tuples -/

open Classical in
/-- The pure tensor with the sites of `S` in the trivial line. -/
def st (S : Set (Fin m)) : Space n m :=
  PiTensorProduct.tprod ℂ fun r => if r ∈ S then D1SiteG.vac n else D1SiteG.w c₀

theorem st_empty : st (n := n) c₀ (∅ : Set (Fin m)) = gen c₀ := by
  simp [st, gen, generator]

theorem oneOp_vac : D1SiteG.op f c₀ 1 (D1SiteG.vac n) = 0 := by
  simp [D1SiteG.op, D1SiteG.vac]

theorem zeroOp_vac : D1SiteG.op f c₀ 0 (D1SiteG.vac n) = 0 := by
  simp [D1SiteG.op, D1SiteG.vac]

open Classical in
theorem localOp_one_st (S : Set (Fin m)) (q : Fin m) (hq : q ∉ S) :
    localOp q (D1SiteG.op f c₀ 1) (st c₀ S) = st c₀ (insert q S) := by
  rw [st, st, localOp_tprod]
  congr 1
  funext r
  by_cases hr : r = q
  · subst hr
    simp [hq, D1SiteG.op, D1SiteG.w, D1SiteG.vac]
  · simp [hr]

open Classical in
theorem localOp_st_mem (S : Set (Fin m)) (q : Fin m) (hq : q ∈ S)
    (B : Module.End ℂ (D1SiteG.Space n)) (hB : B (D1SiteG.vac n) = 0) :
    localOp q B (st c₀ S) = 0 := by
  rw [st, localOp_tprod]
  simp only [hq, if_true, hB]
  exact MultilinearMap.map_update_zero _ _ _

theorem tail_injective {j : ℕ} {p : Fin (j + 1) → Fin m} (hp : Function.Injective p) :
    Function.Injective (Fin.tail p) :=
  hp.comp (Fin.succ_injective j)

/-- `O_{p 0} ⋯ O_{p (j−1)} w` is the state tensor of `range p` for injective `p`, else `0`. -/
theorem OW_state (j : ℕ) : ∀ p : Fin j → Fin m,
    OW f c₀ j p (gen c₀) = if Function.Injective p then st c₀ (Set.range p) else 0 := by
  induction j with
  | zero =>
    intro p
    rw [if_pos (show Function.Injective p from fun a b _ => Subsingleton.elim a b),
      Set.range_eq_empty, st_empty]
    rfl
  | succ j ih =>
    intro p
    change localOp (p 0) (D1SiteG.op f c₀ 1) (OW f c₀ j (Fin.tail p) (gen c₀)) = _
    rw [ih]
    by_cases ht : Function.Injective (Fin.tail p)
    · rw [if_pos ht]
      by_cases h0 : p 0 ∈ Set.range (Fin.tail p)
      · rw [localOp_st_mem c₀ _ _ h0 _ (oneOp_vac f c₀), if_neg]
        intro hp
        obtain ⟨i, hi⟩ := h0
        exact absurd (hp hi) (Fin.succ_ne_zero i)
      · rw [localOp_one_st f c₀ _ _ h0, if_pos, Fin.range_fin_succ]
        rw [← Fin.cons_self_tail p]
        exact Fin.cons_injective_of_injective h0 ht
    · rw [if_neg ht, map_zero, if_neg (fun hp => ht (tail_injective hp))]

theorem Wt_zero (j : ℕ) (p : Fin (j + 1) → Fin m) (hp : ¬ Function.Injective p) :
    Wt f c₀ j p = 0 := by
  rw [Wt, OW_state]
  by_cases ht : Function.Injective (Fin.tail p)
  · rw [if_pos ht]
    by_cases h0 : p 0 ∈ Set.range (Fin.tail p)
    · exact localOp_st_mem c₀ _ _ h0 _ (zeroOp_vac f c₀)
    · exfalso
      apply hp
      rw [← Fin.cons_self_tail p]
      exact Fin.cons_injective_of_injective h0 ht
  · rw [if_neg ht, map_zero]

/-! ## The transfer map and the filtration membership -/

/-- The linear transfer from functions on `(j+1)`-tuples to the tensor model. -/
def PsiT (j : ℕ) : ((Fin (j + 1) → Fin m) → ℂ) →ₗ[ℂ] Space n m :=
  Fintype.linearCombination ℂ (fun p : Fin (j + 1) → Fin m => Wt f c₀ j p)

theorem PsiT_NI (j : ℕ) (φ : (Fin (j + 1) → Fin m) → ℂ) (hφ : φ ∈ NI (j + 1)) :
    PsiT f c₀ j φ = 0 := by
  rw [PsiT, Fintype.linearCombination_apply]
  refine sum_eq_zero fun p _ => ?_
  by_cases hp : Function.Injective p
  · rw [hφ p hp, zero_smul]
  · rw [Wt_zero f c₀ j p hp, smul_zero]

/-- The monomial word `g_{l 0} ⋯ g_{l (j−1)} v`. -/
def gword : (j : ℕ) → (Fin j → ℕ) → Space n m → Space n m
  | 0, _, v => v
  | j + 1, l, v => (act f hJ hskew z).op c₀ 1 (l 0) (gword j (Fin.tail l) v)

theorem gword_eq (j : ℕ) : ∀ (l : Fin j → ℕ) (v : Space n m),
    gword f hJ hskew z c₀ j l v = ∑ p : Fin j → Fin m, monT z j l p • OW f c₀ j p v := by
  induction j with
  | zero =>
    intro l v
    rw [Fintype.sum_subsingleton _ (fun i => i.elim0)]
    simp [gword, OW, monT]
  | succ j ih =>
    intro l v
    change (act f hJ hskew z).op c₀ 1 (l 0) (gword f hJ hskew z c₀ j (Fin.tail l) v) = _
    rw [ih, act_op_apply, reindex]
    refine sum_congr rfl fun p _ => ?_
    simp only [monT, Fin.prod_univ_succ, Fin.tail]
    rfl

theorem gword_mem (j : ℕ) : ∀ (l : Fin j → ℕ) (v : Space n m) (d : ℕ),
    v ∈ evalFbelow (act f hJ hskew z) (gen c₀) d →
      gword f hJ hskew z c₀ j l v ∈
        evalFbelow (act f hJ hskew z) (gen c₀) (d + ∑ i, l i) := by
  induction j with
  | zero =>
    intro l v d hv
    simpa [gword] using hv
  | succ j ih =>
    intro l v d hv
    change (act f hJ hskew z).op c₀ 1 (l 0) (gword f hJ hskew z c₀ j (Fin.tail l) v) ∈ _
    have h := evalFbelow_op (act f hJ hskew z) (gen c₀) c₀ 1 (l 0) _
      (ih (Fin.tail l) v d hv)
    refine evalFbelow_mono _ _ (le_of_eq ?_) h
    rw [Fin.sum_univ_succ]
    simp only [Fin.tail]
    omega

theorem PsiT_monT (j : ℕ) (l : Fin (j + 1) → ℕ) :
    PsiT f c₀ j (monT z (j + 1) l) =
      (act f hJ hskew z).op c₀ 0 (l 0) (gword f hJ hskew z c₀ j (Fin.tail l) (gen c₀)) := by
  rw [gword_eq, act_op_apply, reindex, PsiT, Fintype.linearCombination_apply]
  refine sum_congr rfl fun p _ => ?_
  simp only [monT, Fin.prod_univ_succ, Fin.tail, Wt]

theorem PsiT_lowSpan (j N : ℕ) :
    Submodule.map (PsiT f c₀ j) (lowSpanT z (j + 1) N) ≤
      evalFbelow (act f hJ hskew z) (gen c₀) N := by
  rw [lowSpanT, Submodule.map_span_le]
  rintro _ ⟨l, hl, rfl⟩
  rw [PsiT_monT f hJ hskew]
  have h := evalFbelow_op (act f hJ hskew z) (gen c₀) c₀ 0 (l 0) _
    (gword_mem f hJ hskew z c₀ j (Fin.tail l) (gen c₀) 1
      (FusionGr.generator_mem (act f hJ hskew z) (gen c₀)))
  refine evalFbelow_mono _ _ ?_ h
  rw [Fin.sum_univ_succ] at hl
  simp only [Fin.tail] at h ⊢
  omega

/-- **The ungraded `P^{(j)}_N w` lies in `F_{<N}` for `N ≥ m − j`** (arbitrary points,
every `j`). -/
theorem PsymA_mem (j N : ℕ) (hN : m ≤ N + j) (hN0 : 1 ≤ N) :
    FusionGr.StarB2.PsymA (act f hJ hskew z) c₀ j N (gen c₀) ∈
      evalFbelow (act f hJ hskew z) (gen c₀) N := by
  have heq : FusionGr.StarB2.PsymA (act f hJ hskew z) c₀ j N (gen c₀) =
      PsiT f c₀ j (hvecT z (j + 1) N) := by
    rw [PsymA_eq f hJ hskew, PsiT, Fintype.linearCombination_apply]
    rfl
  rw [heq]
  have hmem := hvecT_mem z (j + 1) N (by omega) hN0
  rw [Submodule.mem_sup] at hmem
  obtain ⟨φ₁, h₁, φ₂, h₂, hsum⟩ := hmem
  rw [← hsum, map_add, PsiT_NI f c₀ j φ₂ h₂, add_zero]
  exact PsiT_lowSpan f hJ hskew z c₀ j N (Submodule.mem_map_of_mem h₁)

/-- **(★b, every `j`, generic points)**: `P^{(j)}_N` kills the graded generator of the
evaluation model for `N ≥ m − j`, `N ≥ 1` (no injectivity of the points is needed). -/
theorem psym_zero (j N : ℕ) (hN : m ≤ N + j) (hN0 : 1 ≤ N) :
    Psym (FusionGr.evalGrToroidal (siteFam f hJ hskew m) z (gen c₀)) c₀ j N
      (FusionGr.grGenerator (act f hJ hskew z) (gen c₀)) = 0 :=
  FusionGr.StarB2.Psym_zero_of_mem (act f hJ hskew z) (gen c₀) m
    (FusionGr.evalHighTShift (siteFam f hJ hskew m) z (gen c₀)) c₀ j N
    (PsymA_mem f hJ hskew z c₀ j N hN hN0)

end Generic

/-! ## The `D4` instance -/

section D4

open VOA.DeligneAudit.DeligneSector.D4 VOA.DeligneAudit.DeligneSector.Sparse

/-- **(★b)**: every `P^{(j)}_N` with `N ≥ m − j`, `N ≥ 1`, kills the `D4` fusion-side
graded highest vector. -/
theorem psymKillsFusion (m j N : ℕ) (hN : m ≤ N + j) (hN0 : 1 ≤ N) :
    Psym (D4Fusion.gradedAction m) D4sector.c₀ j N (D4Fusion.gradedHighest m) = 0 :=
  psym_zero (fC 28 br) D1SiteG.D4Check.table_jacobi D1SiteG.D4Check.table_skewC
    (D1TensorG.points m) (27 : Fin 28) j N hN hN0

/-- **(★b)**: the full family `J'_m` kills the fusion-side graded highest vector. -/
theorem Jprime_le_annF (m : ℕ) (hm : 1 ≤ m) : JprimeLeAnnF m := by
  rintro ρ (h | ⟨j, N, hj, hjm, hN, rfl⟩)
  · exact Jsymbols_le_annF m hm h
  · exact psymKillsFusion m j N hN (by omega)

end D4

end

end VOA.DeligneAudit.Toroidal.StarB2

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.StarB2.PsymA_eq
#print axioms VOA.DeligneAudit.Toroidal.StarB2.Wt_zero
#print axioms VOA.DeligneAudit.Toroidal.StarB2.PsymA_mem
#print axioms VOA.DeligneAudit.Toroidal.StarB2.psym_zero
#print axioms VOA.DeligneAudit.Toroidal.StarB2.psymKillsFusion
#print axioms VOA.DeligneAudit.Toroidal.StarB2.Jprime_le_annF
end AxiomAudit
