import VOA.DeligneAudit.D4FusionToroidalStarBScalar
import VOA.DeligneAudit.D4FusionToroidalGarlandSymbol

/-!
# (★b, `j = 1`): `P^{(1)}_N v_F = 0` for `N ≥ m − 1` in the fusion associated graded

The pure-evaluation tensor model on `m` sites with site module `D1SiteG.Space n`
(coadjoint summand plus trivial line) and highest tensor `w = ⊗ e_{c₀}`.  With
`Z = (c₀ ⊗ 1)` (mode `0`, coadjoint) and `O = (c₀ ⊗ u)` (mode `1`, evaluation into the line):

* same-site terms vanish: `Z (O e_{c₀}) = Z (0, 1) = 0` (`site_zero_one`);
* `f_a g_b w = ∑_{q ≠ p} z_q^a z_p^b · W_{qp}` with `W_{qp} = Z_q O_p w` (`pair_word`);
* hence `∑_{a+b=N} f_a g_b w = Ψ(h_N(z_q, z_p))` for the linear transfer `Ψ` from functions on
  off-diagonal pairs, and the scalar reduction `hvec_mem` places it in the `t`-degree `< N`
  filtration piece (`fullSum_mem`);
* the truncated sum (`a, b < m`) differs by high-mode terms, which lie one step lower by the
  point-polynomial shift (`trunc_term_mem`, `truncSum_mem`);
* in `Gr` the symbol of `P^{(1)}_N` on the generator is the class of `single N (truncated sum)`,
  which is zero (`psym_one_zero`).

Specialised to `D4`: `psymOneKillsFusion : PsymOneKillsFusion m` and
`JprimeOne_le_annF : JprimeOne m ⊆ annF m`.
-/

namespace VOA.DeligneAudit.Toroidal.StarB

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.Toroidal.FusionGr
open Finset

noncomputable section

section Generic

variable {n m : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (hJ : JacobiCoord f)
  (hskew : ∀ a b c, f a b c = -f b a c) (z : Fin m → ℂ) (c₀ : Fin n)

/-- The constant site family. -/
abbrev siteFam (m : ℕ) : Fin m → CurrentModule f (D1SiteG.Space n) :=
  fun _ => D1SiteG.rep f hJ hskew

/-- The pure-evaluation toroidal action. -/
abbrev act : ToroidalAction f (Space n m) := evalAction (siteFam f hJ hskew m) z

/-- The highest tensor. -/
abbrev gen : Space n m := generator c₀

theorem act_op_apply (c : Fin n) (i s : ℕ) (v : Space n m) :
    (act f hJ hskew z).op c i s v = ∑ q, z q ^ s • localOp q (D1SiteG.op f c i) v := by
  change evalOp (siteFam f hJ hskew m) z c i s v = _
  simp only [evalOp, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

/-- Same-site vanishing: the coadjoint action of `c₀` kills the trivial line. -/
theorem site_zero_one : (D1SiteG.op f c₀ 0 * D1SiteG.op f c₀ 1) (D1SiteG.w c₀) = 0 := by
  simp [D1SiteG.op, D1SiteG.w]

theorem localOp_gen_zero (q : Fin m) (B : Module.End ℂ (D1SiteG.Space n))
    (hB : B (D1SiteG.w c₀) = 0) : localOp q B (gen c₀ : Space n m) = 0 := by
  rw [gen, generator, localOp_tprod]
  simp only [hB]
  exact MultilinearMap.map_update_zero _ _ _

/-- `W_{qp} = Z_q O_p w`. -/
def W (q p : Fin m) : Space n m :=
  localOp q (D1SiteG.op f c₀ 0) (localOp p (D1SiteG.op f c₀ 1) (gen c₀))

theorem W_diag (q : Fin m) : W f c₀ q q = 0 := by
  rw [W, ← Module.End.mul_apply, ← localOp_mul]
  exact localOp_gen_zero c₀ q _ (site_zero_one f c₀)

theorem sum_product_offDiag (F : Fin m × Fin m → Space n m) (hF : ∀ q, F (q, q) = 0) :
    ∑ r ∈ Finset.univ ×ˢ Finset.univ, F r = ∑ r : Pairs m, F r.1 := by
  calc ∑ r ∈ Finset.univ ×ˢ Finset.univ, F r
      = ∑ r ∈ (Finset.univ : Finset (Fin m)).offDiag, F r := by
        symm
        apply Finset.sum_subset
        · intro r _
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
        · intro r _ hr
          simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, not_not] at hr
          have hr' : r = (r.1, r.1) := Prod.ext rfl hr.symm
          rw [hr']
          exact hF r.1
    _ = ∑ r : Pairs m, F r.1 :=
        Finset.sum_subtype _ (fun r => by simp [Finset.mem_offDiag]) F

/-- `f_a g_b w = ∑_{q ≠ p} z_q^a z_p^b W_{qp}`. -/
theorem pair_word (a b : ℕ) :
    (act f hJ hskew z).op c₀ 0 a ((act f hJ hskew z).op c₀ 1 b (gen c₀)) =
      ∑ r : Pairs m, mon z a b r • W f c₀ r.1.1 r.1.2 := by
  simp only [act_op_apply, map_sum, map_smul, smul_smul, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_product']
  refine (sum_product_offDiag
    (fun r => (z r.2 ^ b * z r.1 ^ a) • W f c₀ r.1 r.2)
    (fun q => by simp [W_diag])).trans ?_
  refine sum_congr rfl fun r _ => ?_
  congr 1
  simp only [mon]
  ring

/-- The linear transfer from functions on off-diagonal pairs to the tensor model. -/
def Psi : (Pairs m → ℂ) →ₗ[ℂ] Space n m :=
  Fintype.linearCombination ℂ (fun r : Pairs m => W f c₀ r.1.1 r.1.2)

theorem Psi_mon (a b : ℕ) :
    Psi f c₀ (mon z a b) =
      (act f hJ hskew z).op c₀ 0 a ((act f hJ hskew z).op c₀ 1 b (gen c₀)) := by
  rw [pair_word]
  rfl

theorem Psi_lowSpan (N : ℕ) :
    Submodule.map (Psi f c₀) (lowSpan z N) ≤
      evalFbelow (act f hJ hskew z) (gen c₀) N := by
  rw [lowSpan, Submodule.map_span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  rw [Psi_mon f hJ hskew]
  exact Submodule.subset_span ⟨[(c₀, 0, a), (c₀, 1, b)], by simp only [tDegree]; omega, rfl⟩

/-- **The full lift lies one filtration step down**: `∑_{a+b=N} f_a g_b w ∈ F_{<N}` for
`N ≥ m − 1`. -/
theorem fullSum_mem (hz : Function.Injective z) (N : ℕ) (hN : m ≤ N + 1) :
    ∑ p ∈ antidiagonal N,
        (act f hJ hskew z).op c₀ 0 p.1 ((act f hJ hskew z).op c₀ 1 p.2 (gen c₀)) ∈
      evalFbelow (act f hJ hskew z) (gen c₀) N := by
  have h : ∑ p ∈ antidiagonal N,
      (act f hJ hskew z).op c₀ 0 p.1 ((act f hJ hskew z).op c₀ 1 p.2 (gen c₀)) =
      Psi f c₀ (hvec z N) := by
    rw [hvec_eq_sum, map_sum]
    exact sum_congr rfl fun p _ => (Psi_mon f hJ hskew z c₀ p.1 p.2).symm
  rw [h]
  exact Psi_lowSpan f hJ hskew z c₀ N (Submodule.mem_map_of_mem (hvec_mem z hz N hN))

/-- A pair word with a high mode lies one step down. -/
theorem trunc_term_mem (N a b : ℕ) (hab : a + b = N) (hm : m ≤ a ∨ m ≤ b) :
    (act f hJ hskew z).op c₀ 0 a ((act f hJ hskew z).op c₀ 1 b (gen c₀)) ∈
      evalFbelow (act f hJ hskew z) (gen c₀) N := by
  have hsh := evalHighTShift (siteFam f hJ hskew m) z (gen c₀)
  have h1 : (act f hJ hskew z).op c₀ 1 b (gen c₀) ∈
      evalFbelow (act f hJ hskew z) (gen c₀) (b + 1) :=
    Submodule.subset_span ⟨[(c₀, 1, b)], by simp [tDegree], rfl⟩
  rcases hm with ha | hb
  · have h2 := hsh c₀ 0 a (b + 1) ha h1
    exact evalFbelow_mono _ _ (by omega) h2
  · have h2 : (act f hJ hskew z).op c₀ 1 b (gen c₀) ∈
        evalFbelow (act f hJ hskew z) (gen c₀) b := by
      have h3 := hsh c₀ 1 b 1 hb (FusionGr.generator_mem (act f hJ hskew z) (gen c₀))
      exact evalFbelow_mono _ _ (by omega) h3
    have h3 := evalFbelow_op (act f hJ hskew z) (gen c₀) c₀ 0 a b h2
    exact evalFbelow_mono _ _ (by omega) h3

/-- The truncated pair term (modes `< m`), tagged by its degree. -/
def T (N a b : ℕ) : Space n m :=
  if a + b = N ∧ a < m ∧ b < m then
    (act f hJ hskew z).op c₀ 0 a ((act f hJ hskew z).op c₀ 1 b (gen c₀)) else 0

theorem T_mem (N a b : ℕ) :
    T f hJ hskew z c₀ N a b ∈ evalFbelow (act f hJ hskew z) (gen c₀) (N + 1) := by
  unfold T
  split_ifs with h
  · exact Submodule.subset_span ⟨[(c₀, 0, a), (c₀, 1, b)], by simp only [tDegree]; omega, rfl⟩
  · exact Submodule.zero_mem _

/-- The truncated sum also lies one step down. -/
theorem truncSum_mem (hz : Function.Injective z) (N : ℕ) (hN : m ≤ N + 1) :
    ∑ p ∈ antidiagonal N, T f hJ hskew z c₀ N p.1 p.2 ∈
      evalFbelow (act f hJ hskew z) (gen c₀) N := by
  have hY := fullSum_mem f hJ hskew z c₀ hz N hN
  have hdiff : ∑ p ∈ antidiagonal N,
      ((act f hJ hskew z).op c₀ 0 p.1 ((act f hJ hskew z).op c₀ 1 p.2 (gen c₀)) -
        T f hJ hskew z c₀ N p.1 p.2) ∈ evalFbelow (act f hJ hskew z) (gen c₀) N := by
    refine Submodule.sum_mem _ fun p hp => ?_
    have hab := mem_antidiagonal.mp hp
    by_cases h : p.1 < m ∧ p.2 < m
    · rw [T, if_pos ⟨hab, h⟩, sub_self]
      exact Submodule.zero_mem _
    · rw [T, if_neg (fun hc => h hc.2), sub_zero]
      exact trunc_term_mem f hJ hskew z c₀ N p.1 p.2 hab (by omega)
  have h := Submodule.sub_mem _ hY hdiff
  rw [← Finset.sum_sub_distrib] at h
  simpa only [sub_sub_cancel] using h

/-! ## The graded statement -/

theorem mkQ_single_congr {d d' : ℕ} {x x' : Space n m} (hd : d = d') (hx : x = x')
    (h : x ∈ evalFbelow (act f hJ hskew z) (gen c₀) (d + 1))
    (h' : x' ∈ evalFbelow (act f hJ hskew z) (gen c₀) (d' + 1)) :
    (FusionGr.kernel (act f hJ hskew z) (gen c₀)).mkQ
        (FusionGr.single (act f hJ hskew z) (gen c₀) d x h) =
      (FusionGr.kernel (act f hJ hskew z) (gen c₀)).mkQ
        (FusionGr.single (act f hJ hskew z) (gen c₀) d' x' h') := by
  subst hd
  subst hx
  rfl

theorem mkQ_single_zero (d : ℕ) (x : Space n m)
    (h : x ∈ evalFbelow (act f hJ hskew z) (gen c₀) (d + 1))
    (hx : x ∈ evalFbelow (act f hJ hskew z) (gen c₀) d) :
    (FusionGr.kernel (act f hJ hskew z) (gen c₀)).mkQ
      (FusionGr.single (act f hJ hskew z) (gen c₀) d x h) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span ⟨d, x, hx, rfl⟩

theorem mkQ_single_sum {ι : Type*} (s : Finset ι) (d : ℕ) (x : ι → Space n m)
    (h : ∀ i, x i ∈ evalFbelow (act f hJ hskew z) (gen c₀) (d + 1)) :
    ∑ i ∈ s, (FusionGr.kernel (act f hJ hskew z) (gen c₀)).mkQ
        (FusionGr.single (act f hJ hskew z) (gen c₀) d (x i) (h i)) =
      (FusionGr.kernel (act f hJ hskew z) (gen c₀)).mkQ
        (FusionGr.single (act f hJ hskew z) (gen c₀) d (∑ i ∈ s, x i)
          (Submodule.sum_mem _ fun i _ => h i)) := by
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  simp [FusionGr.single, Finsupp.single_finsetSum]

/-- Each graded pair term on the generator is the class of the tagged truncated term. -/
theorem grTerm (a b N : ℕ) (hab : a + b = N) :
    FusionGr.grOp (act f hJ hskew z) (gen c₀) m c₀ 0 a
        (FusionGr.grOp (act f hJ hskew z) (gen c₀) m c₀ 1 b
          (FusionGr.grGenerator (act f hJ hskew z) (gen c₀))) =
      (FusionGr.kernel (act f hJ hskew z) (gen c₀)).mkQ
        (FusionGr.single (act f hJ hskew z) (gen c₀) N (T f hJ hskew z c₀ N a b)
          (T_mem f hJ hskew z c₀ N a b)) := by
  by_cases ha : a < m
  · by_cases hb : b < m
    · rw [FusionGr.grGenerator,
        FusionGr.grOp_single _ _ m c₀ 1 b 0 hb _ (FusionGr.generator_mem _ _),
        FusionGr.grOp_single _ _ m c₀ 0 a (0 + b) ha _ _]
      exact mkQ_single_congr f hJ hskew z c₀ (by omega)
        (by rw [T, if_pos ⟨hab, ha, hb⟩]) _ _
    · rw [FusionGr.grOp_high_zero _ _ m c₀ 1 b (Nat.le_of_not_lt hb), LinearMap.zero_apply,
        map_zero]
      symm
      apply mkQ_single_zero
      rw [T, if_neg (fun hc => hb hc.2.2)]
      exact Submodule.zero_mem _
  · rw [FusionGr.grOp_high_zero _ _ m c₀ 0 a (Nat.le_of_not_lt ha), LinearMap.zero_apply]
    symm
    apply mkQ_single_zero
    rw [T, if_neg (fun hc => ha hc.2.1)]
    exact Submodule.zero_mem _

/-- **(★b, `j = 1`, generic points)**: `P^{(1)}_N` kills the graded generator of the
evaluation model for every `N ≥ m − 1`, for any injective family of `m` points. -/
theorem psym_one_zero (hz : Function.Injective z) (N : ℕ) (hN : m ≤ N + 1) :
    Psym (evalGrToroidal (siteFam f hJ hskew m) z (gen c₀)) c₀ 1 N
      (FusionGr.grGenerator (act f hJ hskew z) (gen c₀)) = 0 := by
  rw [Psym_one]
  change ∑ p ∈ antidiagonal N, FusionGr.grOp (act f hJ hskew z) (gen c₀) m c₀ 0 p.1
    (FusionGr.grOp (act f hJ hskew z) (gen c₀) m c₀ 1 p.2
      (FusionGr.grGenerator (act f hJ hskew z) (gen c₀))) = 0
  rw [sum_congr rfl (fun p hp =>
    grTerm f hJ hskew z c₀ p.1 p.2 N (mem_antidiagonal.mp hp))]
  rw [mkQ_single_sum f hJ hskew z c₀ (antidiagonal N) N
    (fun p => T f hJ hskew z c₀ N p.1 p.2) (fun p => T_mem f hJ hskew z c₀ N p.1 p.2)]
  exact mkQ_single_zero f hJ hskew z c₀ N _ _ (truncSum_mem f hJ hskew z c₀ hz N hN)

end Generic

/-! ## The `D4` instance -/

section D4

open VOA.DeligneAudit.DeligneSector.D4 VOA.DeligneAudit.DeligneSector.Sparse

/-- **(★b, `j = 1`)**: `P^{(1)}_N v_F = 0` for all `N ≥ m − 1`, on the `D4` fusion-side
graded highest vector, for every site count `m`. -/
theorem psymOneKillsFusion (m : ℕ) : PsymOneKillsFusion m := by
  intro N hN
  exact psym_one_zero (fC 28 br) D1SiteG.D4Check.table_jacobi D1SiteG.D4Check.table_skewC
    (D1TensorG.points m) (27 : Fin 28) (D1TensorG.points_injective m) N hN

/-- `J'_m` at `j = 1` kills the fusion-side graded highest vector. -/
theorem JprimeOne_le_annF (m : ℕ) (hm : 1 ≤ m) : JprimeOne m ⊆ annF m :=
  JprimeOne_le_annF_of m hm (psymOneKillsFusion m)

end D4

end

end VOA.DeligneAudit.Toroidal.StarB

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.StarB.pair_word
#print axioms VOA.DeligneAudit.Toroidal.StarB.fullSum_mem
#print axioms VOA.DeligneAudit.Toroidal.StarB.truncSum_mem
#print axioms VOA.DeligneAudit.Toroidal.StarB.psym_one_zero
#print axioms VOA.DeligneAudit.Toroidal.StarB.psymOneKillsFusion
#print axioms VOA.DeligneAudit.Toroidal.StarB.JprimeOne_le_annF
end AxiomAudit
