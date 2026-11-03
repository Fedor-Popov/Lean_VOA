import VOA.Classification.COne.PlusRat4Prod

/-! # Transfer for arbitrary mode-word combinations (general VOA)

A *word combination* `F = Σ cᵢ wᵢ` (homogeneous mode words `wᵢ`, all of total degree `d`) can be
evaluated on any weak module.  Let `x ∈ A` and `e ∈ B` be top vectors with the same zero-mode
character and `L(0)`-eigenvalue `h`, `e ≠ 0`, no generalized weights of `A` below `h`, and no
nonzero top vectors of `A` at the intermediate eigenvalues `h + k`, `0 < k < D`.

`word_transfer`: if `F(e) = 0` (`deg F = d ≤ D`) then `F(x)` is a top vector of `A`, and
`F(x) = 0` when `d < D`.

Proof: strong induction on `d`; a lowering mode applied to `F` is the word combination with that
letter prepended, of smaller degree; degree zero is `word_zero_scalar`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

/-- Word combinations. -/
abbrev WComb (W : VertexOperatorAlgebra V) := List (ℂ × List (HomogeneousLetter W))

/-- Evaluation of a word combination. -/
def evalW (A : WeakModule W M) (F : WComb W) (y : M) : M :=
  (F.map fun p => p.1 • homogeneousWord A p.2 y).sum

/-- All words of `F` have total degree `d`. -/
def WDeg (F : WComb W) (d : ℤ) : Prop := ∀ p ∈ F, homogeneousDegree p.2 = d

/-- Prepend a letter to every word. -/
def prependW (a : HomogeneousLetter W) (F : WComb W) : WComb W :=
  F.map fun p => (p.1, a :: p.2)

theorem evalW_prepend (A : WeakModule W M) (a : HomogeneousLetter W) (y : M) :
    ∀ F : WComb W, evalW A (prependW a F) y = mode (A.YM a.state) a.modeIndex (evalW A F y)
  | [] => by simp [evalW, prependW]
  | p :: F => by
    have ih := evalW_prepend A a y F
    simp only [evalW, prependW, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, map_add, map_smul]
    rfl

theorem WDeg_prepend (a : HomogeneousLetter W) {F : WComb W} {d : ℤ} (hF : WDeg F d) :
    WDeg (prependW a F) (a.weight - a.modeIndex - 1 + d) := by
  intro p hp
  simp only [prependW, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [homogeneousDegree, hF q hq]

theorem word_eigen (A : WeakModule W M) {y : M} {h : ℂ} (hy : L0 A y = h • y) :
    ∀ l : List (HomogeneousLetter W),
      L0 A (homogeneousWord A l y) = (h + (homogeneousDegree l : ℂ)) • homogeneousWord A l y
  | [] => by
    simp only [homogeneousWord, homogeneousDegree, LinearMap.id_apply]
    rw [hy]; simp
  | a :: l => by
    have ih := word_eigen A hy l
    simp only [homogeneousWord, homogeneousDegree, LinearMap.comp_apply]
    rw [L0_commutator_weak A a.homogeneous, ih, map_smul, ← add_smul]
    congr 1
    push_cast; ring

theorem evalW_eigen (A : WeakModule W M) {y : M} {h : ℂ} (hy : L0 A y = h • y) {d : ℤ} :
    ∀ F : WComb W, WDeg F d → L0 A (evalW A F y) = (h + (d : ℂ)) • evalW A F y
  | [] => by simp [evalW]
  | p :: F => by
    intro hF
    have ih := evalW_eigen A hy F (fun q hq => hF q (List.mem_cons_of_mem _ hq))
    simp only [evalW, List.map_cons, List.sum_cons] at ih ⊢
    rw [map_add, ih, map_smul, word_eigen A hy, hF p List.mem_cons_self, smul_add, smul_comm]

theorem evalW_zero_scalar (A : WeakModule W M) (B : WeakModule W N) (χ : VOA.A W → ℂ) {h : ℂ}
    {x : M} {e : N} (hx : x ∈ Omega A) (he : e ∈ Omega B)
    (hχx : ∀ r, topEvaluation A x hx r = χ r • x) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hxL : L0 A x = h • x) (heL : L0 B e = h • e) :
    ∀ F : WComb W, WDeg F 0 → ∃ c : ℂ, evalW A F x = c • x ∧ evalW B F e = c • e
  | [] => fun _ => ⟨0, by simp [evalW], by simp [evalW]⟩
  | p :: F => by
    intro hF
    obtain ⟨c1, h1, h2⟩ := word_zero_scalar A B χ hx he hχx hχe hxL heL p.2 (hF p List.mem_cons_self)
    obtain ⟨c2, h3, h4⟩ := evalW_zero_scalar A B χ hx he hχx hχe hxL heL F
      (fun q hq => hF q (List.mem_cons_of_mem _ hq))
    refine ⟨p.1 * c1 + c2, ?_, ?_⟩
    · simp only [evalW, List.map_cons, List.sum_cons] at h3 ⊢
      rw [h1, h3, add_smul, smul_smul]
    · simp only [evalW, List.map_cons, List.sum_cons] at h4 ⊢
      rw [h2, h4, add_smul, smul_smul]

/-- **Transfer for word combinations.** -/
theorem word_transfer (A : WeakModule W M) (B : WeakModule W N) (χ : VOA.A W → ℂ) {h : ℂ}
    {x : M} {e : N} (hx : x ∈ Omega A) (he : e ∈ Omega B)
    (hχx : ∀ r, topEvaluation A x hx r = χ r • x) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hxL : L0 A x = h • x) (heL : L0 B e = h • e) (he0 : e ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (D : ℕ)
    (hmid : ∀ k : ℕ, 0 < k → k < D → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0) :
    ∀ d : ℕ, d ≤ D → ∀ F : WComb W, WDeg F (d : ℤ) → evalW B F e = 0 →
      evalW A F x ∈ Omega A ∧ (d < D → evalW A F x = 0) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hdD F hF hFe
  have hxg : x ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  by_cases hd0 : d = 0
  · subst hd0
    obtain ⟨c, h1, h2⟩ := evalW_zero_scalar A B χ hx he hχx hχe hxL heL F (by simpa using hF)
    rw [hFe] at h2
    have hc : c = 0 := (smul_eq_zero.mp h2.symm).resolve_right he0
    rw [h1, hc, zero_smul]
    exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
  have hΩ : evalW A F x ∈ Omega A := by
    intro β c hc n hn
    set a : HomogeneousLetter W := ⟨c, β, n, hc⟩
    by_cases hj : (d : ℤ) + (β - n - 1) < 0
    · -- lowering below the bottom
      have hv := evalW_eigen A hxL F hF
      have hg : evalW A F x ∈ (L0 A).maxGenEigenspace (h + (d : ℂ)) :=
        Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hv)
      have h3 := mode_mem_maxGenEigenspace A hc n hg
      apply hlow _ _ _ h3
      have : (((d : ℤ) + (β - n - 1) : ℤ) : ℝ) < 0 := by exact_mod_cast hj
      rw [Complex.add_re, Complex.add_re, Complex.intCast_re, Complex.natCast_re]
      push_cast at this ⊢
      linarith
    · obtain ⟨d', hd'⟩ : ∃ d' : ℕ, (d' : ℤ) = (d : ℤ) + (β - n - 1) := ⟨_, Int.toNat_of_nonneg (by omega)⟩
      have hd'lt : d' < d := by omega
      have hG := WDeg_prepend a hF
      have hGd : WDeg (prependW a F) (d' : ℤ) := by
        intro p hp; rw [hG p hp, hd']; simp only [a]; ring
      have hGe : evalW B (prependW a F) e = 0 := by
        rw [evalW_prepend, hFe, map_zero]
      have := (ih d' hd'lt (by omega) (prependW a F) hGd hGe).2 (by omega)
      rw [evalW_prepend] at this
      exact this
  refine ⟨hΩ, fun hdD' => ?_⟩
  have hv := evalW_eigen A hxL F hF
  exact hmid d (by omega) hdD' _ hΩ (by exact_mod_cast hv)

end VOA.Classification.COne.PlusRat4
