import VOA.Classification.COne.PlusRat4Fourteen

/-! # Top vectors from generators; top vectors inside a simple submodule (general VOA)

* `mem_Omega_of_generators` (Abe, Math. Z. 249 (2005), Prop. 2.2): if `V` is spanned by iterated
  products of a set `G` of homogeneous states of positive weight modulo `C₂(V)`, then a vector
  killed by every lowering mode of every generator is a top vector (`∈ Ω`).
* `degreeSpan_neg_eq_bot`: words of negative total degree kill a top vector.
* `omega_mem_atom_eq_zero`: a top vector of a simple submodule `P` (with nonzero generalized
  weight-`h` part) of generalized weight `h + d`, `d ≥ 1`, is zero.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3 PlusRational
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

section Gen
variable (A : WeakModule W M)

/-- **The kill step.**  If `a` and every homogeneous state of weight `< α + β + p - 1` kill `u` by
their lowering modes, then so does `a₍₋ₚ₎b`. -/
theorem kill_step {u : M} {α β : ℤ} {a b : V}
    (ha : a ∈ W.grading α) (hb : b ∈ W.grading β) (p : ℤ) (hp : 1 ≤ p) (hα0 : 0 ≤ α)
    (hap : 1 ≤ α ∨ 2 ≤ p)
    (IH : ∀ (j : ℤ) (c : V), c ∈ W.grading j → j < α + β + p - 1 →
      ∀ n : ℤ, j ≤ n → mode (A.YM c) n u = 0)
    (haK : ∀ n : ℤ, α ≤ n → mode (A.YM a) n u = 0) :
    ∀ n : ℤ, α + β + p - 1 ≤ n → mode (A.YM (W.smul a (-p) b)) n u = 0 := by
  intro n hn
  have hβ : β < α + β + p - 1 := by rcases hap with h | h <;> omega
  rw [module_iterate0 A a b u (-p) n]
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  by_cases hi : i < 0
  · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]
  have h1 : mode (A.YM b) (n + i) u = 0 := IH β b hb hβ _ (by omega)
  rw [h1, map_zero, zero_sub]
  by_cases hai : α ≤ i
  · rw [haK i hai, map_zero, smul_zero, neg_zero, smul_zero]
  · -- commute `b₍q₎` past `a₍ᵢ₎`
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) := ⟨i.toNat, by omega⟩
    have hc := zero_mode_comm A k a b (-p + n - k) u
    have hbq : mode (A.YM b) (-p + n - k) u = 0 := IH β b hb hβ _ (by omega)
    rw [hbq, map_zero] at hc
    have hsum : ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) •
        mode (A.YM (W.smul a j b)) ((k : ℤ) + (-p + n - k) - j) u = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hg := W.toPreVertexAlgebra.smul_mem_grading ha hb j
      rw [IH _ _ hg (by omega) _ (by omega), smul_zero]
    rw [hsum, add_zero] at hc
    rw [← hc, smul_zero, neg_zero, smul_zero]

/-- **Abe's Prop. 2.2.**  Lowering modes of generators kill `u` ⇒ `u ∈ Ω`. -/
theorem mem_Omega_of_generators {G : Set V} (hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ W.grading j)
    (htop : (⊤ : Submodule ℂ V) = Submodule.span ℂ {y | IsIterProd W G y} ⊔ O₂ W) {u : M}
    (hgen : ∀ g ∈ G, ∀ j : ℤ, g ∈ W.grading j → ∀ n : ℤ, j ≤ n → mode (A.YM g) n u = 0) :
    u ∈ Omega A := by
  suffices H : ∀ N : ℕ, ∀ (k : ℤ) (a : V), a ∈ W.grading k → k < N →
      ∀ n : ℤ, k ≤ n → mode (A.YM a) n u = 0 by
    intro β a ha n hn
    exact H (β.toNat + 1) β a ha (by omega) n hn
  intro N
  induction N with
  | zero =>
    intro k a ha hk
    rw [W.positivity k (by omega), Submodule.mem_bot] at ha
    subst ha
    intro n _
    rw [map_zero, mode_zero, LinearMap.zero_apply]
  | succ N ih =>
    intro k a ha hk
    by_cases hkN : k < N
    · exact ih k a ha hkN
    have IH : ∀ (j : ℤ) (c : V), c ∈ W.grading j → j < k →
        ∀ n : ℤ, j ≤ n → mode (A.YM c) n u = 0 := fun j c hc hj => ih j c hc (by omega)
    have hgenk : ∀ y : V, (IsIterProd W G y ∨ y ∈ O₂homGen W) → y ∈ W.grading k →
        ∀ n : ℤ, k ≤ n → mode (A.YM y) n u = 0 := by
      intro y hy hyk n hn
      rcases hy with hy | ⟨p, q, a', b', ha', hb', rfl⟩
      · cases hy with
        | vacuum =>
          have := A.act_vacuum n u
          rw [WeakModule.act_def] at this
          by_cases hk0 : k = 0
          · subst hk0
            rw [this, if_neg (by omega)]
          · have h0 := eq_zero_of_mem_two_gradings (W := W) hk0 hyk W.vacuum_mem
            rw [h0, map_zero, mode_zero, LinearMap.zero_apply]
        | step s hs p hp b hb =>
          obtain ⟨α, hα, hsα⟩ := hG s hs
          obtain ⟨β, hβ, hbβ, _⟩ := iterProd_homog hG hb
          have hyg := step_mem_grading W (m := p) hsα hbβ
          by_cases hkk : k = α + β + p - 1
          · subst hkk
            exact kill_step A hsα hbβ p hp (by omega) (Or.inl hα) IH (hgen s hs α hsα) n hn
          · have h0 := eq_zero_of_mem_two_gradings (W := W) hkk hyk hyg
            rw [h0, map_zero, mode_zero, LinearMap.zero_apply]
      · by_cases hz : W.smul a' (-2) b' = 0
        · rw [hz, map_zero, mode_zero, LinearMap.zero_apply]
        have hyg := gen_mem_grading W ha' hb'
        have hpq := factor_deg_lt W ha' hb' rfl hz
        have hp0 : 0 ≤ p := by
          by_contra hneg
          apply hz
          rw [W.positivity p (by omega), Submodule.mem_bot] at ha'
          rw [ha', W.smul_zero_left]
        by_cases hkk : k = p + q + 1
        · subst hkk
          have := kill_step A ha' hb' 2 (by norm_num) hp0 (Or.inr le_rfl)
            (fun j c hc hj => IH j c hc (by omega)) (IH p a' ha' (by omega)) n (by omega)
          exact this
        · exact absurd (eq_zero_of_mem_two_gradings (W := W) hkk hyk hyg) hz
    have hspan : a ∈ Submodule.span ℂ ({y | IsIterProd W G y} ∪ O₂homGen W) := by
      have hmem : a ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
      rw [htop, O₂_eq_span_homGen, ← Submodule.span_union] at hmem
      exact hmem
    have hproj : ∀ y ∈ Submodule.span ℂ ({y | IsIterProd W G y} ∪ O₂homGen W),
        ∀ n : ℤ, k ≤ n → mode (A.YM (piHom W k y)) n u = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro n hn
        have hyh : ∃ d : ℤ, y ∈ W.grading d := by
          rcases hy with hy | hy
          · obtain ⟨d, _, hd, _⟩ := iterProd_homog hG hy; exact ⟨d, hd⟩
          · exact O₂homGen_homog W hy
        obtain ⟨d, hd⟩ := hyh
        by_cases hdk : d = k
        · subst hdk
          rw [piHom_of_mem W hd]
          exact hgenk y hy hd n hn
        · rw [piHom_of_mem_ne W hdk hd, map_zero, mode_zero, LinearMap.zero_apply]
      | zero => intro n _; rw [map_zero, map_zero, mode_zero, LinearMap.zero_apply]
      | add y z _ _ hy hz =>
        intro n hn; rw [map_add, map_add, mode_add, LinearMap.add_apply, hy n hn, hz n hn, add_zero]
      | smul c y _ hy =>
        intro n hn; rw [map_smul, map_smul, mode_smul, LinearMap.smul_apply, hy n hn, smul_zero]
    intro n hn
    have := hproj a hspan n hn
    rwa [piHom_of_mem W ha] at this

end Gen

section Li
variable (A : WeakModule W M)

/-- The single-mode span of a top vector of eigenvalue `k` lies in generalized weights `k + ℕ`. -/
theorem modeSpan_le_spectral_ge {x : M} (hx : x ∈ Omega A) (k : ℂ) (hL : L0 A x = k • x) :
    VOA.Moonshine.SigmaExist.modeSpan A {x} ≤ spectralPart A {μ | ∃ n : ℕ, μ = k + n} := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    exact Module.End.mem_eigenspace_iff.mpr hL
  apply Submodule.span_le.mpr
  rintro _ ⟨a, q, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hv : a ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun a => A.act a q y ∈ spectralPart A _) hv
    ?_ ?_ ?_
  · intro j b hb
    by_cases hq : j ≤ q
    · rw [WeakModule.act_def, Omega_mode_vanish hx hb hq]
      exact Submodule.zero_mem _
    · have h := mode_mem_maxGenEigenspace A hb q hxg
      apply Submodule.mem_iSup_of_mem (k + ((j - q - 1 : ℤ) : ℂ))
      apply Submodule.mem_iSup_of_mem
      · exact h
      · exact ⟨(j - q - 1).toNat, by
          rw [show (((j - q - 1).toNat : ℕ) : ℂ) = ((j - q - 1 : ℤ) : ℂ) by
            exact_mod_cast Int.toNat_of_nonneg (by omega)]⟩
  · simp
  · intro a b ha hb
    have he : A.act (a + b) q y = A.act a q y + A.act b q y := by
      simp only [WeakModule.act_def, map_add, mode_add, LinearMap.add_apply]
    rw [he]
    exact Submodule.add_mem _ ha hb

/-- Words of negative degree vanish on a top vector. -/
theorem degreeSpan_neg_eq_bot {x : M} (hx : x ∈ Omega A) (k : ℂ) (hL : L0 A x = k • x)
    (d : ℕ) (hd : 0 < d) : homogeneousDegreeSpan A x (-(d : ℤ)) = ⊥ := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    exact Module.End.mem_eigenspace_iff.mpr hL
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  have hg := homogeneousDegreeSpan_gen A hxg (-(d : ℤ)) hv
  have hsp : v ∈ spectralPart A {μ | ∃ n : ℕ, μ = k + n} := by
    refine Submodule.span_induction
      (p := fun v _ => v ∈ spectralPart A {μ | ∃ n : ℕ, μ = k + n}) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨l, _, rfl⟩
      exact modeSpan_le_spectral_ge A hx k hL (homogeneousWord_mem_modeSpan A x l)
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; exact Submodule.smul_mem _ c ha
  have hdis : Disjoint ({k + ((-(d : ℤ) : ℤ) : ℂ)} : Set ℂ) {μ | ∃ n : ℕ, μ = k + n} := by
    rw [Set.disjoint_left]
    rintro μ hμ ⟨n, hn⟩
    rw [Set.mem_singleton_iff] at hμ
    rw [hμ] at hn
    have h1 : ((-(d : ℤ) : ℤ) : ℂ) = (n : ℂ) := add_left_cancel hn
    have h2 : (-(d : ℤ) : ℤ) = (n : ℤ) := by exact_mod_cast h1
    omega
  have hd' := spectralPart_disjoint A hdis
  have hg' : v ∈ spectralPart A {k + ((-(d : ℤ) : ℤ) : ℂ)} := by
    apply Submodule.mem_iSup_of_mem (k + ((-(d : ℤ) : ℤ) : ℂ))
    exact Submodule.mem_iSup_of_mem rfl hg
  exact Submodule.disjoint_def.mp hd' v hg' hsp

end Li

section Atom
variable (A : WeakModule W M)

/-- A top vector of a simple submodule `P` above the bottom of `P` vanishes. -/
theorem omega_mem_atom_eq_zero (hC2 : C2Cofinite W) (P : Submodule (modeAlg A) M) (hP : IsAtom P)
    {y : M} (hyP : y ∈ P) (hy0 : y ≠ 0) {h : ℂ} (hyg : y ∈ (L0 A).maxGenEigenspace h)
    {v : M} (hvP : v ∈ P) (hvΩ : v ∈ Omega A) (d : ℕ) (hd : 0 < d)
    (hvL : L0 A v = (h + d) • v) : v = 0 := by
  by_contra hv0
  have hvg : v ∈ (L0 A).maxGenEigenspace (h + d) := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    exact Module.End.mem_eigenspace_iff.mpr hvL
  have hcle : cyclic A v ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ rfl
    exact hvP
  have hcyc : cyclic A v = P := by
    rcases hP.le_iff.mp hcle with h0 | h1
    · exfalso
      apply hv0
      have : v ∈ cyclic A v := Submodule.mem_span_singleton_self v
      rw [h0] at this
      exact (Submodule.mem_bot _).mp this
    · exact h1
  have hyc : y ∈ cyclic A v := hcyc ▸ hyP
  have hyg' : y ∈ (L0 A).maxGenEigenspace ((h + d) + ((-(d : ℤ) : ℤ) : ℂ)) := by
    have : (h + (d : ℂ)) + ((-(d : ℤ) : ℤ) : ℂ) = h := by push_cast; ring
    rw [this]; exact hyg
  have hn := (no_mode_word_iff_not_mem_degreeSpan hC2 A hvg (-(d : ℤ)) hyg').mpr (by
    rw [degreeSpan_neg_eq_bot A hvΩ (h + d) hvL d hd]
    intro hm
    exact hy0 ((Submodule.mem_bot ℂ).mp hm))
  change y ∈ Submodule.span (modeAlg A) {v} at hyc
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hyc
  exact hn r hr

end Atom

end VOA.Classification.COne.PlusRat5
