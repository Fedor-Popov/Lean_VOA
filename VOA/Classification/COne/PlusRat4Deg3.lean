import VOA.Classification.COne.PlusRat4Degree

/-! # The degree-three raising lemma (general VOA)

`Deg2Plane A x`: every degree-two single mode on `x` lies in `span(L(-1)²x, L(-2)x)`.

`raise3_mem`: if `x` is a scalar top vector with `Deg1Line` and `Deg2Plane`, and `G` generates
`V` modulo `C₂`, then every degree-three single mode `a₍ₖ₋₄₎x` lies in
`span ({L(-1)³x, L(-1)L(-2)x, L(-3)x} ∪ {g₍wt g - 4₎x : g ∈ G})`.

The commutator with `L(-2) = ω₍₋₁₎` is taken with `ω` on the left,
`[ω₍₋₁₎, c₍ₙ₎] = Σᵢ (-1)ⁱ (ωᵢc)₍ₙ₋₁₋ᵢ₎`, whose `i = 0, 1` terms are `(L(-1)c)` and `wt(c)·c`
(modes of `c` itself) and whose `i ≥ 2` terms have lower weight.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

/-- Every degree-two single mode on `x` is a combination of `L(-1)²x` and `L(-2)x`. -/
def Deg2Plane (x : M) : Prop :=
  ∀ (j : ℤ) (c : V), c ∈ W.grading j →
    ∃ a b : ℂ, mode (A.YM c) (j - 3) x =
      a • mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 x) +
        b • mode (A.YM W.conformalVector) (-1) x

/-- `span ({L(-1)³x, L(-1)L(-2)x, L(-3)x} ∪ {g₍wt g - 4₎x})`. -/
def raiseSpan3 (G : Set V) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ ({mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0
      (mode (A.YM W.conformalVector) 0 x)),
    mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) (-1) x),
    mode (A.YM W.conformalVector) (-2) x} ∪
    {y | ∃ (j : ℤ) (g : V), g ∈ G ∧ g ∈ W.grading j ∧ y = mode (A.YM g) (j - 4) x})

variable {A}

section Helpers
variable {G : Set V} {x : M}

theorem V1_mem3 : mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0
    (mode (A.YM W.conformalVector) 0 x)) ∈ raiseSpan3 A G x :=
  Submodule.subset_span (Or.inl (Set.mem_insert _ _))

theorem V2_mem3 : mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) (-1) x) ∈
    raiseSpan3 A G x :=
  Submodule.subset_span (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

theorem V3_mem3 : mode (A.YM W.conformalVector) (-2) x ∈ raiseSpan3 A G x :=
  Submodule.subset_span (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

theorem mem_raiseSpan3_of_gen {j : ℤ} {g : V} (hg : g ∈ G) (hj : g ∈ W.grading j) :
    mode (A.YM g) (j - 4) x ∈ raiseSpan3 A G x :=
  Submodule.subset_span (Or.inr ⟨j, g, hg, hj, rfl⟩)

/-- `L(-1)` of a degree-two single mode. -/
theorem omega0_D2 (hD2 : Deg2Plane A x) {j : ℤ} {c : V} (hc : c ∈ W.grading j) :
    mode (A.YM W.conformalVector) 0 (mode (A.YM c) (j - 3) x) ∈ raiseSpan3 A G x := by
  obtain ⟨a, b, hab⟩ := hD2 j c hc
  rw [hab, map_add, map_smul, map_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ V1_mem3) (Submodule.smul_mem _ _ V2_mem3)

/-- A degree-two mode on `L(-1)x`. -/
theorem modeL_mem3 (hD2 : Deg2Plane A x) {j : ℤ} {c : V} (hc : c ∈ W.grading j)
    (hcS : mode (A.YM c) (j - 4) x ∈ raiseSpan3 A G x) :
    mode (A.YM c) (j - 3) (mode (A.YM W.conformalVector) 0 x) ∈ raiseSpan3 A G x := by
  rw [mode_translation, show j - 3 - 1 = j - 4 by ring]
  exact Submodule.add_mem _ (omega0_D2 hD2 hc) (Submodule.smul_mem _ _ hcS)

/-- A degree-one mode on `L(-1)²x`. -/
theorem modeR_mem3 (hD1 : Deg1Line A x) (hD2 : Deg2Plane A x) {j : ℤ} {c : V}
    (hc : c ∈ W.grading j) (hcS : mode (A.YM c) (j - 4) x ∈ raiseSpan3 A G x) :
    mode (A.YM c) (j - 2) (mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 x)) ∈
      raiseSpan3 A G x := by
  rw [mode_translation A c (j - 2) (mode (A.YM W.conformalVector) 0 x),
    mode_translation A c (j - 2) x, show j - 2 - 1 = j - 3 by ring]
  obtain ⟨κ, hκ⟩ := hD1 j c hc
  rw [hκ]
  simp only [map_add, map_smul]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ V1_mem3)
    (Submodule.smul_mem _ _ (omega0_D2 hD2 hc))) (Submodule.smul_mem _ _ (modeL_mem3 hD2 hc hcS))

/-- A degree-one mode on `L(-2)x`. -/
theorem modeQ1_mem3 (hD1 : Deg1Line A x) {j : ℤ} {c : V}
    (hc : c ∈ W.grading j) (hcS : mode (A.YM c) (j - 4) x ∈ raiseSpan3 A G x)
    (hIH : ∀ i : ℕ, 2 ≤ i → mode (A.YM (W.smul W.conformalVector i c)) (j - 3 - i) x ∈
      raiseSpan3 A G x) :
    mode (A.YM c) (j - 2) (mode (A.YM W.conformalVector) (-1) x) ∈ raiseSpan3 A G x := by
  set S := raiseSpan3 A G x
  have hc1 := mode_commutator A W.conformalVector c x (-1) (j - 2)
  rw [sub_eq_iff_eq_add] at hc1
  have hcomm : (∑ᶠ i : ℤ, cbz (-1) i • mode (A.YM (W.smul W.conformalVector i c)) (-1 + (j - 2) - i) x)
      ∈ S := by
    apply finsum_mem_submodule_of_forall
    intro i
    by_cases hi : i < 0
    · rw [cbz_apply_neg _ hi, zero_smul]; exact S.zero_mem
    apply S.smul_mem
    obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
    by_cases h0 : i' = 0
    · subst h0
      rw [show W.smul W.conformalVector ((0 : ℕ) : ℤ) c = W.L (-1) c by
        rw [VertexOperatorAlgebra.L_def]; rfl, T_mode, show -1 + (j - 2) - ((0 : ℕ) : ℤ) - 1 = j - 4 by
        push_cast; ring]
      exact S.smul_mem _ hcS
    by_cases h1 : i' = 1
    · subst h1
      rw [show W.smul W.conformalVector ((1 : ℕ) : ℤ) c = (j : ℂ) • c by
        rw [← VertexOperatorAlgebra.L_zero_grading W c hc, VertexOperatorAlgebra.L_def]; rfl,
        map_smul, mode_smul, LinearMap.smul_apply, show -1 + (j - 2) - ((1 : ℕ) : ℤ) = j - 4 by
        push_cast; ring]
      exact S.smul_mem _ hcS
    · have := hIH i' (by omega)
      rwa [show j - 3 - (i' : ℤ) = -1 + (j - 2) - (i' : ℤ) by ring] at this
  rw [← sub_eq_iff_eq_add'] at hc1
  rw [show mode (A.YM c) (j - 2) (mode (A.YM W.conformalVector) (-1) x) =
      mode (A.YM W.conformalVector) (-1) (mode (A.YM c) (j - 2) x) -
        ∑ᶠ i : ℤ, cbz (-1) i • mode (A.YM (W.smul W.conformalVector i c)) (-1 + (j - 2) - i) x by
    rw [hc1]]
  apply S.sub_mem _ hcomm
  obtain ⟨κ, hκ⟩ := hD1 j c hc
  rw [hκ, map_smul, mode_translation, show (-1 : ℤ) - 1 = -2 by norm_num]
  push_cast
  exact S.smul_mem _ (S.add_mem V2_mem3 (S.smul_mem _ V3_mem3))

end Helpers

/-- **The product step** (degree three). -/
theorem raise3_step {G : Set V} {x : M} (hx : ScalarTop A x) (hD1 : Deg1Line A x)
    (hD2 : Deg2Plane A x) {α β : ℤ} {a b : V} (ha : a ∈ W.grading α) (hb : b ∈ W.grading β)
    (p : ℤ) (hp : 1 ≤ p) (hα0 : 0 ≤ α) (_hβ0 : 0 ≤ β) (hap : 1 ≤ α ∨ 2 ≤ p)
    (IH : ∀ (j : ℤ) (c : V), c ∈ W.grading j → j < α + β + p - 1 →
      mode (A.YM c) (j - 4) x ∈ raiseSpan3 A G x)
    (haS : mode (A.YM a) (α - 4) x ∈ raiseSpan3 A G x) :
    mode (A.YM (W.smul a (-p) b)) (α + β + p - 1 - 4) x ∈ raiseSpan3 A G x := by
  set S := raiseSpan3 A G x
  have hbS : mode (A.YM b) (β - 4) x ∈ S := IH β b hb (by rcases hap with h | h <;> omega)
  -- lower-weight `ωᵢ c` for `c = a, b`
  have hIHa : ∀ i : ℕ, 2 ≤ i → mode (A.YM (W.smul W.conformalVector i a)) (α - 3 - i) x ∈ S := by
    intro i hi
    have hg := W.toPreVertexAlgebra.smul_mem_grading W.conformal_mem ha (i : ℤ)
    have := IH (2 + α - i - 1) _ hg (by omega)
    rwa [show 2 + α - (i : ℤ) - 1 - 4 = α - 3 - i by ring] at this
  have hIHb : ∀ i : ℕ, 2 ≤ i → mode (A.YM (W.smul W.conformalVector i b)) (β - 3 - i) x ∈ S := by
    intro i hi
    have hg := W.toPreVertexAlgebra.smul_mem_grading W.conformal_mem hb (i : ℤ)
    have := IH (2 + β - i - 1) _ hg (by rcases hap with h | h <;> omega)
    rwa [show 2 + β - (i : ℤ) - 1 - 4 = β - 3 - i by ring] at this
  -- commutator terms `(b_j a)` of degree three lie in `S`
  have hcomm : ∀ q r : ℤ, q + r = α + β - 5 →
      (∑ᶠ j : ℤ, cbz q j • mode (A.YM (W.smul b j a)) (q + r - j) x) ∈ S := by
    intro q r hqr
    apply finsum_mem_submodule_of_forall
    intro j
    by_cases hj : j < 0
    · rw [cbz_apply_neg q hj, zero_smul]; exact S.zero_mem
    · apply S.smul_mem
      have hg := W.toPreVertexAlgebra.smul_mem_grading hb ha j
      have := IH (β + α - j - 1) _ hg (by omega)
      rwa [show β + α - j - 1 - 4 = q + r - j by omega] at this
  -- `a`/`b` on the degree-two plane
  have hplane : ∀ {γ : ℤ} {c : V}, c ∈ W.grading γ → mode (A.YM c) (γ - 4) x ∈ S →
      (∀ i : ℕ, 2 ≤ i → mode (A.YM (W.smul W.conformalVector i c)) (γ - 3 - i) x ∈ S) →
      ∀ {j : ℤ} {d : V}, d ∈ W.grading j →
        mode (A.YM c) (γ - 2) (mode (A.YM d) (j - 3) x) ∈ S := by
    intro γ c hc hcS hIHc j d hd
    obtain ⟨a', b', hab⟩ := hD2 j d hd
    rw [hab, map_add, map_smul, map_smul]
    exact S.add_mem (S.smul_mem _ (modeR_mem3 hD1 hD2 hc hcS))
      (S.smul_mem _ (modeQ1_mem3 hD1 hc hcS hIHc))
  rw [module_iterate0 A a b x (-p) _]
  apply finsum_mem_submodule_of_forall
  intro i
  by_cases hi : i < 0
  · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]; exact S.zero_mem
  apply S.smul_mem
  apply S.sub_mem
  · -- first family: `a_{-p-i} b_{n+i} x`
    by_cases hd : β ≤ α + β + p - 1 - 4 + i
    · rw [Omega_mode_vanish hx.omega hb hd, map_zero]; exact S.zero_mem
    by_cases h0 : α + β + p - 1 - 4 + i = β - 1
    · obtain ⟨s, hs⟩ := hx.zero β b hb
      rw [h0, hs, map_smul, show -p - i = α - 4 by omega]
      exact S.smul_mem _ haS
    by_cases h1 : α + β + p - 1 - 4 + i = β - 2
    · obtain ⟨κ, hκ⟩ := hD1 β b hb
      rw [h1, hκ, map_smul, show -p - i = α - 3 by omega]
      exact S.smul_mem _ (modeL_mem3 hD2 ha haS)
    · have he : α + β + p - 1 - 4 + i = β - 3 := by
        rcases hap with h | h <;> omega
      rw [he, show -p - i = α - 2 by omega]
      exact hplane ha haS hIHa hb
  · apply S.smul_mem
    -- second family: `b_q a_i x`
    by_cases hd : α ≤ i
    · rw [Omega_mode_vanish hx.omega ha hd, map_zero]; exact S.zero_mem
    by_cases h0 : i = α - 1
    · subst h0
      obtain ⟨s, hs⟩ := hx.zero α a ha
      rw [hs, map_smul, show -p + (α + β + p - 1 - 4) - (α - 1) = β - 4 by ring]
      exact S.smul_mem _ hbS
    by_cases h1 : i = α - 2
    · subst h1
      obtain ⟨κ, hκ⟩ := hD1 α a ha
      rw [hκ, map_smul, show -p + (α + β + p - 1 - 4) - (α - 2) = β - 3 by ring]
      exact S.smul_mem _ (modeL_mem3 hD2 hb hbS)
    by_cases h2 : i = α - 3
    · subst h2
      rw [show -p + (α + β + p - 1 - 4) - (α - 3) = β - 2 by ring]
      exact hplane hb hbS hIHb ha
    by_cases h3 : i = α - 4
    · subst h3
      have hc := mode_commutator A b a x (β - 1) (α - 4)
      rw [sub_eq_iff_eq_add] at hc
      rw [show -p + (α + β + p - 1 - 4) - (α - 4) = β - 1 by ring, hc]
      apply S.add_mem (hcomm _ _ (by ring))
      obtain ⟨s, hs⟩ := hx.zero β b hb
      rw [hs, map_smul]
      exact S.smul_mem _ haS
    · have hq : β ≤ -p + (α + β + p - 1 - 4) - i := by omega
      have hc := mode_commutator A b a x (-p + (α + β + p - 1 - 4) - i) i
      rw [Omega_mode_vanish hx.omega hb hq, map_zero, sub_zero] at hc
      rw [hc]
      exact hcomm _ _ (by ring)

/-- **The degree-three raising lemma.** -/
theorem raise3_mem {G : Set V} (hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ W.grading j)
    (htop : (⊤ : Submodule ℂ V) = Submodule.span ℂ {y | IsIterProd W G y} ⊔ O₂ W)
    {x : M} (hx : ScalarTop A x) (hD1 : Deg1Line A x) (hD2 : Deg2Plane A x) :
    ∀ (k : ℤ) (a : V), a ∈ W.grading k → mode (A.YM a) (k - 4) x ∈ raiseSpan3 A G x := by
  set S := raiseSpan3 A G x
  suffices H : ∀ N : ℕ, ∀ (k : ℤ) (a : V), a ∈ W.grading k → k < N →
      mode (A.YM a) (k - 4) x ∈ S by
    intro k a ha
    exact H (k.toNat + 1) k a ha (by omega)
  intro N
  induction N with
  | zero =>
    intro k a ha hk
    rw [W.positivity k (by omega), Submodule.mem_bot] at ha
    subst ha
    rw [map_zero, mode_zero, LinearMap.zero_apply]
    exact S.zero_mem
  | succ N ih =>
    intro k a ha hk
    by_cases hkN : k < N
    · exact ih k a ha hkN
    have IH : ∀ (j : ℤ) (c : V), c ∈ W.grading j → j < k →
        mode (A.YM c) (j - 4) x ∈ S := fun j c hc hj => ih j c hc (by omega)
    have hgen : ∀ y : V, (IsIterProd W G y ∨ y ∈ O₂homGen W) → y ∈ W.grading k →
        mode (A.YM y) (k - 4) x ∈ S := by
      intro y hy hyk
      rcases hy with hy | ⟨p, q, a', b', ha', hb', rfl⟩
      · cases hy with
        | vacuum =>
          by_cases hk3 : k = 3
          · subst hk3
            have h0 := eq_zero_of_mem_two_gradings (W := W) (show (3 : ℤ) ≠ 0 by norm_num) hyk
              W.vacuum_mem
            rw [h0, map_zero, mode_zero, LinearMap.zero_apply]; exact S.zero_mem
          · have := A.act_vacuum (k - 4) x
            rw [WeakModule.act_def] at this
            rw [this, if_neg (by omega)]; exact S.zero_mem
        | step s hs p hp b hb =>
          obtain ⟨α, hα, hsα⟩ := hG s hs
          obtain ⟨β, hβ, hbβ, hb0⟩ := iterProd_homog hG hb
          have hyg := step_mem_grading W (m := p) hsα hbβ
          by_cases hkk : k = α + β + p - 1
          · subst hkk
            by_cases hspec : p = 1 ∧ β = 0
            · obtain ⟨rfl, rfl⟩ := hspec
              rcases hb0 rfl with rfl | rfl
              · rw [show W.smul s (-1) W.vacuum = s from (W.creation s).1]
                rw [show α + 0 + 1 - 1 - 4 = α - 4 by ring]
                exact mem_raiseSpan3_of_gen hs hsα
              · rw [W.smul_zero_right, map_zero, mode_zero, LinearMap.zero_apply]; exact S.zero_mem
            · exact raise3_step hx hD1 hD2 hsα hbβ p hp (by omega) hβ (Or.inl hα) IH
                (mem_raiseSpan3_of_gen hs hsα)
          · have h0 := eq_zero_of_mem_two_gradings (W := W) hkk hyk hyg
            rw [h0, map_zero, mode_zero, LinearMap.zero_apply]; exact S.zero_mem
      · by_cases hz : W.smul a' (-2) b' = 0
        · rw [hz, map_zero, mode_zero, LinearMap.zero_apply]; exact S.zero_mem
        have hyg := gen_mem_grading W ha' hb'
        have hpq := factor_deg_lt W ha' hb' rfl hz
        have hp0 : 0 ≤ p := by
          by_contra hneg
          apply hz
          rw [W.positivity p (by omega), Submodule.mem_bot] at ha'
          rw [ha', W.smul_zero_left]
        have hq0 : 0 ≤ q := by
          by_contra hneg
          apply hz
          rw [W.positivity q (by omega), Submodule.mem_bot] at hb'
          rw [hb', W.smul_zero_right]
        by_cases hkk : k = p + q + 1
        · subst hkk
          have := raise3_step hx hD1 hD2 ha' hb' 2 (by norm_num) hp0 hq0 (Or.inr le_rfl)
            (fun j c hc hj => IH j c hc (by omega)) (IH p a' ha' (by omega))
          rwa [show p + q + 2 - 1 - 4 = p + q + 1 - 4 by ring] at this
        · exact absurd (eq_zero_of_mem_two_gradings (W := W) hkk hyk hyg) hz
    have hspan : a ∈ Submodule.span ℂ ({y | IsIterProd W G y} ∪ O₂homGen W) := by
      have hmem : a ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
      rw [htop, O₂_eq_span_homGen, ← Submodule.span_union] at hmem
      exact hmem
    have hproj : ∀ y ∈ Submodule.span ℂ ({y | IsIterProd W G y} ∪ O₂homGen W),
        mode (A.YM (piHom W k y)) (k - 4) x ∈ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        have hyh : ∃ d : ℤ, y ∈ W.grading d := by
          rcases hy with hy | hy
          · obtain ⟨d, _, hd, _⟩ := iterProd_homog hG hy; exact ⟨d, hd⟩
          · exact O₂homGen_homog W hy
        obtain ⟨d, hd⟩ := hyh
        by_cases hdk : d = k
        · subst hdk
          rw [piHom_of_mem W hd]
          exact hgen y hy hd
        · rw [piHom_of_mem_ne W hdk hd, map_zero, mode_zero, LinearMap.zero_apply]
          exact S.zero_mem
      | zero => rw [map_zero, map_zero, mode_zero, LinearMap.zero_apply]; exact S.zero_mem
      | add y z _ _ hy hz => rw [map_add, map_add, mode_add, LinearMap.add_apply]; exact S.add_mem hy hz
      | smul c y _ hy => rw [map_smul, map_smul, mode_smul, LinearMap.smul_apply]; exact S.smul_mem c hy
    have := hproj a hspan
    rwa [piHom_of_mem W ha] at this

end VOA.Classification.COne.PlusRat4
