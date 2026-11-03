import VOA.Classification.COne.PlusRat5Omega

/-! # Spectral identities transfer from a model to a simple kernel (general VOA)

Let `P` be a simple submodule of a weak module `A` with a top vector `k₀` of weight `h`, and let
`e` be a top vector of the same weight and zero-mode character in some weak module `B` (the
"model"; no irreducibility of `B` is used).  If a zero-degree word combination `G` kills the
`L(0)`-eigenspace `B_{h+d}`, then it kills `P_{h+d}` (`kernel_annihilate`, from `word_transfer`
and `omega_mem_atom_eq_zero`).

Applied to annihilating polynomials `∏ (T - v)` of a zero-mode polynomial `T` this gives
injectivity of `T` on `P_{h+d}` from the joint spectrum of the two zero modes on the model
(`kernel_inj`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3 PlusRational PlusRat4
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

/-! ## §1  Word combinations -/

section Words
variable (A : WeakModule W M)

theorem homogeneousWord_append (l₁ l₂ : List (HomogeneousLetter W)) (y : M) :
    homogeneousWord A (l₁ ++ l₂) y = homogeneousWord A l₁ (homogeneousWord A l₂ y) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    simp only [List.cons_append, homogeneousWord, LinearMap.comp_apply, ih]

theorem homogeneousDegree_append (l₁ l₂ : List (HomogeneousLetter W)) :
    homogeneousDegree (l₁ ++ l₂) = homogeneousDegree l₁ + homogeneousDegree l₂ := by
  induction l₁ with
  | nil => simp [homogeneousDegree]
  | cons a l ih => simp only [List.cons_append, homogeneousDegree, ih]; ring

theorem evalW_nil (y : M) : evalW A ([] : WComb W) y = 0 := by simp [evalW]

theorem evalW_cons (p : ℂ × List (HomogeneousLetter W)) (F : WComb W) (y : M) :
    evalW A (p :: F) y = p.1 • homogeneousWord A p.2 y + evalW A F y := by
  simp [evalW]

theorem evalW_append (F G : WComb W) (y : M) :
    evalW A (F ++ G) y = evalW A F y + evalW A G y := by
  simp [evalW]

theorem evalW_add (F : WComb W) (x y : M) : evalW A F (x + y) = evalW A F x + evalW A F y := by
  induction F with
  | nil => simp [evalW]
  | cons p F ih => rw [evalW_cons, evalW_cons, evalW_cons, map_add, ih, smul_add]; abel

theorem evalW_smul (F : WComb W) (c : ℂ) (x : M) : evalW A F (c • x) = c • evalW A F x := by
  induction F with
  | nil => simp [evalW]
  | cons p F ih => rw [evalW_cons, evalW_cons, map_smul, ih, smul_add, smul_comm]

theorem evalW_zero (F : WComb W) : evalW A F 0 = 0 := by
  have := evalW_smul A F 0 0
  rwa [zero_smul, zero_smul] at this

/-- Composition of word combinations. -/
def compW (G F : WComb W) : WComb W :=
  G.flatMap fun g => F.map fun f => (g.1 * f.1, g.2 ++ f.2)

theorem evalW_map_mul (g : ℂ × List (HomogeneousLetter W)) (F : WComb W) (y : M) :
    evalW A (F.map fun f => (g.1 * f.1, g.2 ++ f.2)) y = g.1 • homogeneousWord A g.2 (evalW A F y) := by
  induction F with
  | nil => simp [evalW]
  | cons f F ihF =>
    rw [List.map_cons, evalW_cons, ihF, evalW_cons, map_add, map_smul, smul_add, smul_smul,
      homogeneousWord_append]

theorem evalW_compW (G F : WComb W) (y : M) :
    evalW A (compW G F) y = evalW A G (evalW A F y) := by
  induction G with
  | nil => simp [compW, evalW]
  | cons g G ih =>
    rw [compW, List.flatMap_cons, ← compW, evalW_append, ih, evalW_cons, evalW_map_mul]

theorem WDeg_compW {G F : WComb W} {d : ℤ} (hG : WDeg G 0) (hF : WDeg F d) :
    WDeg (compW G F) d := by
  intro p hp
  simp only [compW, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨g, hg, f, hf, rfl⟩ := hp
  simp only [homogeneousDegree_append, hG g hg, hF f hf, zero_add]

theorem WDeg_append {F G : WComb W} {d : ℤ} (hF : WDeg F d) (hG : WDeg G d) :
    WDeg (F ++ G) d := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hF p h
  · exact hG p h

theorem evalW_map_smul (c : ℂ) (F : WComb W) (x : M) :
    evalW A (F.map fun p => (c * p.1, p.2)) x = c • evalW A F x := by
  induction F with
  | nil => simp [evalW]
  | cons p F ih => rw [List.map_cons, evalW_cons, evalW_cons, ih, smul_add, smul_smul]

/-- Every vector of a degree span is a word combination applied to the seed. -/
theorem exists_wcomb_of_mem_degreeSpan {x v : M} {d : ℤ} (hv : v ∈ homogeneousDegreeSpan A x d) :
    ∃ F : WComb W, WDeg F d ∧ evalW A F x = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, hl, rfl⟩ := hv
    refine ⟨[(1, l)], fun p hp => ?_, ?_⟩
    · rw [List.mem_singleton] at hp; subst hp; exact hl
    · simp [evalW]
  | zero => exact ⟨[], fun p hp => by simp at hp, by simp [evalW]⟩
  | add a b _ _ ha hb =>
    obtain ⟨F, hF, rfl⟩ := ha
    obtain ⟨G, hG, rfl⟩ := hb
    exact ⟨F ++ G, WDeg_append hF hG, evalW_append A F G x⟩
  | smul c a _ ha =>
    obtain ⟨F, hF, rfl⟩ := ha
    refine ⟨F.map fun p => (c * p.1, p.2), ?_, ?_⟩
    · intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hF q hq
    · exact evalW_map_smul A c F x

/-- Word combinations preserve mode submodules. -/
theorem evalW_mem (P : Submodule (modeAlg A) M) {x : M} (hx : x ∈ P) :
    ∀ F : WComb W, evalW A F x ∈ P := by
  have hw : ∀ l : List (HomogeneousLetter W), homogeneousWord A l x ∈ P := by
    intro l
    induction l with
    | nil => exact hx
    | cons a l ih =>
      simp only [homogeneousWord, LinearMap.comp_apply]
      exact P.smul_mem (⟨mode (A.YM a.state) a.modeIndex,
        Algebra.subset_adjoin ⟨a.state, a.modeIndex, rfl⟩⟩ : modeAlg A) ih
  intro F
  induction F with
  | nil => simp [evalW]
  | cons p F ih =>
    rw [evalW_cons]
    exact P.add_mem (P.smul_mem (algebraMap ℂ (modeAlg A) p.1) (by simpa using hw p.2)) ih

theorem evalW_span (F : WComb W) (U : Set M) {b : M} (hb : b ∈ Submodule.span ℂ U)
    (hU : ∀ u ∈ U, evalW A F u = 0) : evalW A F b = 0 := by
  induction hb using Submodule.span_induction with
  | mem u hu => exact hU u hu
  | zero => exact evalW_zero A F
  | add x y _ _ hx hy => rw [evalW_add, hx, hy, add_zero]
  | smul c x _ hx => rw [evalW_smul, hx, smul_zero]

end Words

/-! ## §2  The transfer -/

section Transfer

/-- **Annihilation transfer.** -/
theorem kernel_annihilate (hC2 : C2Cofinite W) (A : WeakModule W M) (B : WeakModule W N)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P) (χ : VOA.A W → ℂ) {h : ℂ}
    {k₀ : M} {e : N} (hk₀P : k₀ ∈ P) (hk₀0 : k₀ ≠ 0) (hk₀ : k₀ ∈ Omega A) (he : e ∈ Omega B)
    (hχk : ∀ r, topEvaluation A k₀ hk₀ r = χ r • k₀) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hkL : L0 A k₀ = h • k₀) (heL : L0 B e = h • e) (he0 : e ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (D : ℕ)
    (hmid : ∀ k : ℕ, 0 < k → k < D → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0)
    (d : ℕ) (hdD : d ≤ D) (G : WComb W) (hG : WDeg G 0)
    (hGB : ∀ b : N, L0 B b = (h + (d : ℂ)) • b → evalW B G b = 0) :
    ∀ v ∈ P, L0 A v = (h + (d : ℂ)) • v → evalW A G v = 0 := by
  intro v hvP hvL
  have hk₀g : k₀ ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hkL)
  have hvg : v ∈ (L0 A).maxGenEigenspace (h + ((d : ℤ) : ℂ)) := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hvL
  have hcyc : cyclic A k₀ = P := by
    have hle : cyclic A k₀ ≤ P := Submodule.span_le.mpr (by rintro _ rfl; exact hk₀P)
    rcases hP.le_iff.mp hle with h0 | h1
    · exfalso; apply hk₀0
      have : k₀ ∈ cyclic A k₀ := Submodule.mem_span_singleton_self k₀
      rw [h0] at this
      exact (Submodule.mem_bot _).mp this
    · exact h1
  have hvc : v ∈ (cyclic A k₀).restrictScalars ℂ := by rw [hcyc]; exact hvP
  have hvd : v ∈ homogeneousDegreeSpan A k₀ (d : ℤ) := by
    rw [← cyclic_inf_gen_eq_degreeSpan hC2 A hk₀g (d : ℤ)]
    exact ⟨hvc, hvg⟩
  obtain ⟨F, hF, rfl⟩ := exists_wcomb_of_mem_degreeSpan A hvd
  have hGF := WDeg_compW hG hF
  have hBe : evalW B (compW G F) e = 0 := by
    rw [evalW_compW]
    apply hGB
    exact_mod_cast evalW_eigen B heL F hF
  have ht := word_transfer A B χ hk₀ he hχk hχe hkL heL he0 hlow D hmid d hdD (compW G F) hGF hBe
  rw [← evalW_compW]
  rcases Nat.lt_or_ge d D with hlt | hge
  · exact ht.2 hlt
  · have hdD' : d = D := le_antisymm hdD hge
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      obtain ⟨c, h1, h2⟩ := evalW_zero_scalar A B χ hk₀ he hχk hχe hkL heL (compW G F)
        (by simpa using hGF)
      rw [hBe] at h2
      have hc : c = 0 := (smul_eq_zero.mp h2.symm).resolve_right he0
      rw [h1, hc, zero_smul]
    · exact omega_mem_atom_eq_zero A hC2 P hP hk₀P hk₀0 hk₀g (evalW_mem A P hk₀P _) ht.1 d hdpos
        (by exact_mod_cast evalW_eigen A hkL (compW G F) hGF)

end Transfer

/-! ## §3  Zero-mode polynomials -/

section Poly
variable (A : WeakModule W M)

/-- `Σ c a^i b^j` (letters `a`, `b`) as a word combination. -/
def polyW (a b : HomogeneousLetter W) (L : List (ℂ × ℕ × ℕ)) : WComb W :=
  L.map fun t => (t.1, List.replicate t.2.1 a ++ List.replicate t.2.2 b)

/-- Its value at a joint eigenvalue. -/
def polyV (L : List (ℂ × ℕ × ℕ)) (s t : ℂ) : ℂ :=
  (L.map fun q => q.1 * s ^ q.2.1 * t ^ q.2.2).sum

theorem WDeg_replicate (a : HomogeneousLetter W) (ha : a.weight - a.modeIndex - 1 = 0) :
    ∀ n : ℕ, homogeneousDegree (List.replicate n a) = 0
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, homogeneousDegree, WDeg_replicate a ha n, ha]; rfl

theorem WDeg_polyW (a b : HomogeneousLetter W) (ha : a.weight - a.modeIndex - 1 = 0)
    (hb : b.weight - b.modeIndex - 1 = 0) (L : List (ℂ × ℕ × ℕ)) : WDeg (polyW a b L) 0 := by
  intro p hp
  simp only [polyW, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  rw [homogeneousDegree_append, WDeg_replicate a ha, WDeg_replicate b hb]; rfl

theorem word_replicate_eigen (a : HomogeneousLetter W) {u : M} {s : ℂ}
    (hu : mode (A.YM a.state) a.modeIndex u = s • u) :
    ∀ n : ℕ, homogeneousWord A (List.replicate n a) u = s ^ n • u
  | 0 => by simp [homogeneousWord]
  | n + 1 => by
    rw [List.replicate_succ, homogeneousWord, LinearMap.comp_apply, word_replicate_eigen a hu n,
      map_smul, hu, smul_smul, pow_succ]

theorem evalW_polyW_eigen (a b : HomogeneousLetter W) {u : M} {s t : ℂ}
    (hua : mode (A.YM a.state) a.modeIndex u = s • u)
    (hub : mode (A.YM b.state) b.modeIndex u = t • u) (L : List (ℂ × ℕ × ℕ)) :
    evalW A (polyW a b L) u = polyV L s t • u := by
  induction L with
  | nil => simp [polyW, polyV, evalW]
  | cons q L ih =>
    rw [polyW, List.map_cons, evalW_cons, ← polyW, ih,
      show polyV (q :: L) s t = q.1 * s ^ q.2.1 * t ^ q.2.2 + polyV L s t by simp [polyV]]
    simp only
    rw [homogeneousWord_append, word_replicate_eigen A b hub, map_smul,
      word_replicate_eigen A a hua, smul_smul, smul_smul, ← add_smul]
    congr 1
    ring

/-- `∏_{v ∈ Vs} (T - v)` for `T = polyW a b L`. -/
def annW (a b : HomogeneousLetter W) (L : List (ℂ × ℕ × ℕ)) : List ℂ → WComb W
  | [] => [(1, [])]
  | v :: Vs => compW (polyW a b L ++ [(-v, [])]) (annW a b L Vs)

theorem WDeg_annW (a b : HomogeneousLetter W) (ha : a.weight - a.modeIndex - 1 = 0)
    (hb : b.weight - b.modeIndex - 1 = 0) (L : List (ℂ × ℕ × ℕ)) :
    ∀ Vs : List ℂ, WDeg (annW a b L Vs) 0
  | [] => by intro p hp; simp only [annW, List.mem_singleton] at hp; subst hp; rfl
  | v :: Vs => by
    apply WDeg_compW _ (WDeg_annW a b ha hb L Vs)
    apply WDeg_append (WDeg_polyW a b ha hb L)
    intro p hp; rw [List.mem_singleton] at hp; subst hp; rfl

theorem evalW_annW_eigen (a b : HomogeneousLetter W) {u : M} {s t : ℂ}
    (hua : mode (A.YM a.state) a.modeIndex u = s • u)
    (hub : mode (A.YM b.state) b.modeIndex u = t • u) (L : List (ℂ × ℕ × ℕ)) :
    ∀ Vs : List ℂ, evalW A (annW a b L Vs) u = (Vs.map fun v => polyV L s t - v).prod • u
  | [] => by simp [annW, evalW, homogeneousWord]
  | v :: Vs => by
    rw [annW, evalW_compW, evalW_annW_eigen a b hua hub L Vs, evalW_append, evalW_smul,
      evalW_smul, evalW_polyW_eigen A a b hua hub, List.map_cons, List.prod_cons]
    simp only [evalW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, homogeneousWord,
      LinearMap.id_apply, add_zero]
    module

theorem evalW_annW_kernel (a b : HomogeneousLetter W) {u : M} (L : List (ℂ × ℕ × ℕ))
    (hu : evalW A (polyW a b L) u = 0) :
    ∀ Vs : List ℂ, evalW A (annW a b L Vs) u = (Vs.map fun v => -v).prod • u
  | [] => by simp [annW, evalW, homogeneousWord]
  | v :: Vs => by
    rw [annW, evalW_compW, evalW_annW_kernel a b L hu Vs, evalW_append, evalW_smul,
      evalW_smul, hu, List.map_cons, List.prod_cons]
    simp only [evalW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, homogeneousWord,
      LinearMap.id_apply, add_zero, smul_zero, zero_add]
    module


theorem evalW_annW_modP (P : Submodule (modeAlg A) M) (a b : HomogeneousLetter W) {x : M}
    (L : List (ℂ × ℕ × ℕ)) (hx : evalW A (polyW a b L) x ∈ P) :
    ∀ Vs : List ℂ, evalW A (annW a b L Vs) x - (Vs.map fun v => -v).prod • x ∈ P
  | [] => by simp [annW, evalW, homogeneousWord]
  | v :: Vs => by
    have ih := evalW_annW_modP P a b L hx Vs
    set c := (Vs.map fun v => -v).prod with hc
    set y := evalW A (annW a b L Vs) x
    have hy : y = c • x + (y - c • x) := by abel
    rw [annW, evalW_compW, ← show y = evalW A (annW a b L Vs) x from rfl, evalW_append, hy,
      evalW_add, evalW_add, evalW_smul, evalW_smul, List.map_cons, List.prod_cons, ← hc]
    simp only [evalW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, homogeneousWord,
      LinearMap.id_apply, add_zero]
    have h1 : c • evalW A (polyW a b L) x ∈ P := P.smul_mem (algebraMap ℂ (modeAlg A) c) (by simpa using hx)
    have h2 : evalW A (polyW a b L) (y - c • x) ∈ P := evalW_mem A P ih _
    have h3 : (-v) • (y - c • x) ∈ P := P.smul_mem (algebraMap ℂ (modeAlg A) (-v)) (by simpa using ih)
    simp only [evalW] at h1 h2
    convert P.add_mem (P.add_mem h1 h2) h3 using 1
    module

/-- `T` commutes with `∏ (T - v)`. -/
theorem evalW_polyW_annW_comm (a b : HomogeneousLetter W) (L : List (ℂ × ℕ × ℕ)) (y : M) :
    ∀ Vs : List ℂ, evalW A (polyW a b L) (evalW A (annW a b L Vs) y) =
      evalW A (annW a b L Vs) (evalW A (polyW a b L) y)
  | [] => by simp [annW, evalW, homogeneousWord]
  | v :: Vs => by
    rw [annW, evalW_compW, evalW_compW, ← evalW_polyW_annW_comm a b L y Vs, evalW_append,
      evalW_append, evalW_add]
    simp only [evalW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, homogeneousWord,
      LinearMap.id_apply, add_zero]
    have := evalW_smul A (polyW a b L) (-v) (evalW A (annW a b L Vs) y)
    simp only [evalW] at this
    rw [this]

end Poly

/-! ## §4  Injectivity on the kernel from the joint spectrum of the model -/

section Inj

/-- **Kernel annihilators.** -/
theorem kernel_ann_exists (hC2 : C2Cofinite W) (A : WeakModule W M) (B : WeakModule W N)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P) (χ : VOA.A W → ℂ) {h : ℂ}
    {k₀ : M} {e : N} (hk₀P : k₀ ∈ P) (hk₀0 : k₀ ≠ 0) (hk₀ : k₀ ∈ Omega A) (he : e ∈ Omega B)
    (hχk : ∀ r, topEvaluation A k₀ hk₀ r = χ r • k₀) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hkL : L0 A k₀ = h • k₀) (heL : L0 B e = h • e) (he0 : e ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (D : ℕ)
    (hmid : ∀ k : ℕ, 0 < k → k < D → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0)
    (d : ℕ) (hdD : d ≤ D)
    (a b : HomogeneousLetter W) (ha : a.weight - a.modeIndex - 1 = 0)
    (hb : b.weight - b.modeIndex - 1 = 0) (C : ℕ) (Q : ℕ → ℕ → Prop)
    (hspan : ∀ y : N, L0 B y = (h + (d : ℂ)) • y → y ∈ Submodule.span ℂ
      {u | ∃ s t : ℕ, Q s t ∧ s ≤ C ∧ t ≤ C ∧ mode (B.YM a.state) a.modeIndex u = (s : ℂ) • u ∧
        mode (B.YM b.state) b.modeIndex u = (t : ℂ) • u})
    (L : List (ℂ × ℕ × ℕ)) (hne : ∀ s t : ℕ, Q s t → s ≤ C → t ≤ C → polyV L s t ≠ 0) :
    ∃ Vs : List ℂ, (Vs.map fun v => -v).prod ≠ 0 ∧
      ∀ v ∈ P, L0 A v = (h + (d : ℂ)) • v → evalW A (annW a b L Vs) v = 0 := by
  classical
  -- the list of values
  let pairs : List (ℕ × ℕ) := ((List.range (C + 1)).flatMap fun s =>
    (List.range (C + 1)).map fun t => (s, t)).filter fun p => Q p.1 p.2
  let Vs : List ℂ := pairs.map fun p => polyV L p.1 p.2
  have hV0 : (Vs.map fun v => -v).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    simp only [List.mem_map, Vs, pairs, List.mem_filter, List.mem_flatMap, List.mem_range] at hz
    obtain ⟨v, ⟨p, ⟨⟨s, hs, hp⟩, hQ⟩, rfl⟩, hv⟩ := hz
    obtain ⟨t, ht, rfl⟩ := hp
    exact hne s t (by simpa using hQ) (by omega) (by omega) (neg_eq_zero.mp hv)
  have hann := kernel_annihilate hC2 A B P hP χ hk₀P hk₀0 hk₀ he hχk hχe hkL heL he0 hlow D hmid
    d hdD (annW a b L Vs) (WDeg_annW a b ha hb L Vs) (by
      intro y hy
      apply evalW_span B _ _ (hspan y hy)
      rintro u ⟨s, t, hQ, hsC, htC, hus, hut⟩
      rw [evalW_annW_eigen B a b hus hut L Vs]
      have hmem : polyV L s t ∈ Vs :=
        List.mem_map.mpr ⟨(s, t), List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨s,
          List.mem_range.mpr (by omega), List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩⟩,
          decide_eq_true hQ⟩, rfl⟩
      have hz : (Vs.map fun v => polyV L s t - v).prod = 0 :=
        List.prod_eq_zero (List.mem_map.mpr ⟨_, hmem, sub_self _⟩)
      rw [hz, zero_smul])
  exact ⟨Vs, hV0, hann⟩

/-- **Kernel injectivity.**  If the model weight space `B_{h+d}` is spanned by joint
eigenvectors of the two zero modes with eigenvalue pairs `(s,t) ∈ ℕ²`, `s,t ≤ C`, satisfying
`Q`, and the polynomial `T` has no zero on that set, then `T` is injective on `P_{h+d}`. -/
theorem kernel_inj (hC2 : C2Cofinite W) (A : WeakModule W M) (B : WeakModule W N)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P) (χ : VOA.A W → ℂ) {h : ℂ}
    {k₀ : M} {e : N} (hk₀P : k₀ ∈ P) (hk₀0 : k₀ ≠ 0) (hk₀ : k₀ ∈ Omega A) (he : e ∈ Omega B)
    (hχk : ∀ r, topEvaluation A k₀ hk₀ r = χ r • k₀) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hkL : L0 A k₀ = h • k₀) (heL : L0 B e = h • e) (he0 : e ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (D : ℕ)
    (hmid : ∀ k : ℕ, 0 < k → k < D → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0)
    (d : ℕ) (hdD : d ≤ D)
    (a b : HomogeneousLetter W) (ha : a.weight - a.modeIndex - 1 = 0)
    (hb : b.weight - b.modeIndex - 1 = 0) (C : ℕ) (Q : ℕ → ℕ → Prop)
    (hspan : ∀ y : N, L0 B y = (h + (d : ℂ)) • y → y ∈ Submodule.span ℂ
      {u | ∃ s t : ℕ, Q s t ∧ s ≤ C ∧ t ≤ C ∧ mode (B.YM a.state) a.modeIndex u = (s : ℂ) • u ∧
        mode (B.YM b.state) b.modeIndex u = (t : ℂ) • u})
    (L : List (ℂ × ℕ × ℕ)) (hne : ∀ s t : ℕ, Q s t → s ≤ C → t ≤ C → polyV L s t ≠ 0) :
    ∀ v ∈ P, L0 A v = (h + (d : ℂ)) • v → evalW A (polyW a b L) v = 0 → v = 0 := by
  obtain ⟨Vs, hV0, hann⟩ := kernel_ann_exists hC2 A B P hP χ hk₀P hk₀0 hk₀ he hχk hχe hkL heL he0
    hlow D hmid d hdD a b ha hb C Q hspan L hne
  intro v hvP hvL hT
  have h1 := hann v hvP hvL
  rw [evalW_annW_kernel A a b L hT Vs] at h1
  exact (smul_eq_zero.mp h1).resolve_left hV0

end Inj

end VOA.Classification.COne.PlusRat5
