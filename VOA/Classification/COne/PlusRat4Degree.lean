import VOA.Classification.COne.PlusRat3Degree
import VOA.Classification.COne.PlusRat3Iterate

/-! # Degree-`d` single modes and the degree-two raising lemma (general VOA)

* `degreeSpan_le`: for an `L(0)`-eigenvector `x`, every homogeneous mode word of total degree `d`
  on `x` is a sum of single modes `a₍β-1-d₎x` (Li's single-mode spanning).
* `Deg1Line A x`: every degree-one single mode on `x` is a multiple of `L(-1)x`.
* `raise2_mem`: if `x` is a scalar top vector with `Deg1Line`, and `G` generates `V` modulo
  `C₂`, then every degree-two single mode `a₍ₖ₋₃₎x` lies in
  `span ({L(-1)²x} ∪ {g₍wt g - 3₎x : g ∈ G})`.

The proof is the degree-two analogue of `PlusRat3.raise_mem`: strong induction on the weight, the
Borcherds iterate formula for `a₍₋ₚ₎b`, the commutator formula, `x ∈ Ω`, and
`a₍ₙ₎L(-1) = L(-1)a₍ₙ₎ + n a₍ₙ₋₁₎`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

/-! ## §1  Degree-`d` words are single modes -/

/-- The span of the single degree-`d` modes on `x`. -/
def degSpan (x : M) (d : ℤ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (β : ℤ) (a : V), a ∈ W.grading β ∧ y = mode (A.YM a) (β - 1 - d) x}

theorem degSpan_le_gen {x : M} {k : ℂ} (hL : L0 A x = k • x) (d : ℤ) :
    degSpan A x d ≤ (L0 A).maxGenEigenspace (k + d) := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hL)
  apply Submodule.span_le.mpr
  rintro _ ⟨β, a, ha, rfl⟩
  have h := mode_mem_maxGenEigenspace A ha (β - 1 - d) hxg
  have hc : k + ((β - (β - 1 - d) - 1 : ℤ) : ℂ) = k + d := by push_cast; ring
  rwa [hc] at h

theorem modeSpan_le_degSpan_sup {x : M} {k : ℂ} (hL : L0 A x = k • x) (d : ℤ) :
    VOA.Moonshine.SigmaExist.modeSpan A {x} ≤
      degSpan A x d ⊔ spectralPart A {μ | μ ≠ k + d} := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hL)
  apply Submodule.span_le.mpr
  rintro _ ⟨a, q, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hv : a ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun a => A.act a q y ∈
    degSpan A y d ⊔ spectralPart A {μ | μ ≠ k + d}) hv ?_ ?_ ?_
  · intro j b hb
    by_cases hq : q = j - 1 - d
    · subst hq
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, b, hb, rfl⟩)
    · apply Submodule.mem_sup_right
      have h := mode_mem_maxGenEigenspace A hb q hxg
      apply Submodule.mem_iSup_of_mem (k + ((j - q - 1 : ℤ) : ℂ))
      apply Submodule.mem_iSup_of_mem
      · exact h
      · intro he
        have h2 : ((j - q - 1 : ℤ) : ℂ) = ((d : ℤ) : ℂ) := by linear_combination he
        have h3 : (j - q - 1 : ℤ) = d := by exact_mod_cast h2
        omega
  · simp
  · intro a b ha hb
    have he : A.act (a + b) q y = A.act a q y + A.act b q y := by
      simp only [WeakModule.act_def, map_add, mode_add, LinearMap.add_apply]
    rw [he]
    exact Submodule.add_mem _ ha hb

/-- Degree-`d` words on an eigenvector are sums of single degree-`d` modes. -/
theorem degreeSpan_le {x : M} {k : ℂ} (hL : L0 A x = k • x) (d : ℤ) :
    homogeneousDegreeSpan A x d ≤ degSpan A x d := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hL)
  intro w hw
  have hg := homogeneousDegreeSpan_gen A hxg d hw
  have hsp : w ∈ VOA.Moonshine.SigmaExist.modeSpan A {x} := by
    refine Submodule.span_induction
      (p := fun v _ => v ∈ VOA.Moonshine.SigmaExist.modeSpan A {x}) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨l, _, rfl⟩
      exact homogeneousWord_mem_modeSpan A x l
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; exact Submodule.smul_mem _ c ha
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (modeSpan_le_degSpan_sup A hL d hsp)
  have hs' := degSpan_le_gen A hL d hs
  have htg : t ∈ (L0 A).maxGenEigenspace (k + d) := by
    have : t = w - s := by rw [← hst]; abel
    rw [this]; exact Submodule.sub_mem _ hg hs'
  have ht0 : t = 0 := by
    have hd := spectralPart_disjoint A (s := {k + d}) (t := {μ | μ ≠ k + d})
      (Set.disjoint_left.mpr (by intro μ hμ hn; exact hn (Set.mem_singleton_iff.mp hμ)))
    have htg' : t ∈ spectralPart A {k + d} := by
      apply Submodule.mem_iSup_of_mem (k + d)
      exact Submodule.mem_iSup_of_mem rfl htg
    exact Submodule.disjoint_def.mp hd t htg' ht
  rw [← hst, ht0, add_zero]
  exact hs

/-! ## §2  The degree-two raising lemma -/

/-- Every degree-one single mode on `x` is a multiple of `L(-1)x`. -/
def Deg1Line (x : M) : Prop :=
  ∀ (j : ℤ) (c : V), c ∈ W.grading j →
    ∃ κ : ℂ, mode (A.YM c) (j - 2) x = κ • mode (A.YM W.conformalVector) 0 x

/-- `span ({L(-1)²x} ∪ {g₍wt g - 3₎x : g ∈ G})`. -/
def raiseSpan2 (G : Set V) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ ({mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 x)} ∪
    {y | ∃ (j : ℤ) (g : V), g ∈ G ∧ g ∈ W.grading j ∧ y = mode (A.YM g) (j - 3) x})

variable {A}

theorem mem_raiseSpan2_of_gen {G : Set V} {x : M} {j : ℤ} {g : V} (hg : g ∈ G)
    (hj : g ∈ W.grading j) : mode (A.YM g) (j - 3) x ∈ raiseSpan2 A G x :=
  Submodule.subset_span (Or.inr ⟨j, g, hg, hj, rfl⟩)

theorem LL_mem_raiseSpan2 (G : Set V) (x : M) :
    mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 x) ∈ raiseSpan2 A G x :=
  Submodule.subset_span (Or.inl rfl)

/-- A degree-one mode of `c` on `L(-1)x` lies in `S` once `c₍ⱼ₋₃₎x` does. -/
theorem mode_L_mem {G : Set V} {x : M} (hD : Deg1Line A x) {j : ℤ} {c : V}
    (hc : c ∈ W.grading j) (hcS : mode (A.YM c) (j - 3) x ∈ raiseSpan2 A G x) :
    mode (A.YM c) (j - 2) (mode (A.YM W.conformalVector) 0 x) ∈ raiseSpan2 A G x := by
  rw [mode_translation, show j - 2 - 1 = j - 3 by ring]
  obtain ⟨κ, hκ⟩ := hD j c hc
  rw [hκ, map_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (LL_mem_raiseSpan2 G x))
    (Submodule.smul_mem _ _ hcS)

/-- **The product step** (degree two). -/
theorem raise2_step {G : Set V} {x : M} (hx : ScalarTop A x) (hD : Deg1Line A x) {α β : ℤ}
    {a b : V} (ha : a ∈ W.grading α) (hb : b ∈ W.grading β) (p : ℤ) (hp : 1 ≤ p) (hα0 : 0 ≤ α)
    (_hβ0 : 0 ≤ β) (hap : 1 ≤ α ∨ 2 ≤ p)
    (IH : ∀ (j : ℤ) (c : V), c ∈ W.grading j → j < α + β + p - 1 →
      mode (A.YM c) (j - 3) x ∈ raiseSpan2 A G x)
    (haS : mode (A.YM a) (α - 3) x ∈ raiseSpan2 A G x) :
    mode (A.YM (W.smul a (-p) b)) (α + β + p - 1 - 3) x ∈ raiseSpan2 A G x := by
  set S := raiseSpan2 A G x
  -- commutator terms `(b_j a)` of degree two lie in `S`
  have hcomm : ∀ q r : ℤ, q + r = α + β - 4 →
      (∑ᶠ j : ℤ, cbz q j • mode (A.YM (W.smul b j a)) (q + r - j) x) ∈ S := by
    intro q r hqr
    apply finsum_mem_submodule_of_forall
    intro j
    by_cases hj : j < 0
    · rw [cbz_apply_neg q hj, zero_smul]; exact S.zero_mem
    · apply S.smul_mem
      have hg := W.toPreVertexAlgebra.smul_mem_grading hb ha j
      have := IH (β + α - j - 1) _ hg (by omega)
      rwa [show β + α - j - 1 - 3 = q + r - j by omega] at this
  rw [module_iterate0 A a b x (-p) _]
  apply finsum_mem_submodule_of_forall
  intro i
  by_cases hi : i < 0
  · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]; exact S.zero_mem
  apply S.smul_mem
  apply S.sub_mem
  · -- first family: `a_{-p-i} b_{n+i} x`
    by_cases hd : β ≤ α + β + p - 1 - 3 + i
    · rw [Omega_mode_vanish hx.omega hb hd, map_zero]; exact S.zero_mem
    by_cases h0 : α + β + p - 1 - 3 + i = β - 1
    · obtain ⟨s, hs⟩ := hx.zero β b hb
      rw [h0, hs, map_smul, show -p - i = α - 3 by omega]
      exact S.smul_mem _ haS
    · have he : α + β + p - 1 - 3 + i = β - 2 := by
        rcases hap with h | h <;> omega
      obtain ⟨κ, hκ⟩ := hD β b hb
      rw [he, hκ, map_smul, show -p - i = α - 2 by omega]
      exact S.smul_mem _ (mode_L_mem hD ha haS)
  · apply S.smul_mem
    -- second family: `b_q a_i x`
    by_cases hd : α ≤ i
    · rw [Omega_mode_vanish hx.omega ha hd, map_zero]; exact S.zero_mem
    by_cases h0 : i = α - 1
    · subst h0
      obtain ⟨s, hs⟩ := hx.zero α a ha
      rw [hs, map_smul]
      apply S.smul_mem
      have := IH β b hb (by rcases hap with h | h <;> omega)
      rwa [show -p + (α + β + p - 1 - 3) - (α - 1) = β - 3 by ring]
    by_cases h1 : i = α - 2
    · subst h1
      obtain ⟨κ, hκ⟩ := hD α a ha
      rw [hκ, map_smul, show -p + (α + β + p - 1 - 3) - (α - 2) = β - 2 by ring]
      apply S.smul_mem
      exact mode_L_mem hD hb (IH β b hb (by rcases hap with h | h <;> omega))
    by_cases h2 : i = α - 3
    · subst h2
      have hc := mode_commutator A b a x (β - 1) (α - 3)
      rw [sub_eq_iff_eq_add] at hc
      rw [show -p + (α + β + p - 1 - 3) - (α - 3) = β - 1 by ring, hc]
      apply S.add_mem (hcomm _ _ (by ring))
      obtain ⟨s, hs⟩ := hx.zero β b hb
      rw [hs, map_smul]
      exact S.smul_mem _ haS
    · -- `i ≤ α - 4`: `b_q` lowers, commute
      have hq : β ≤ -p + (α + β + p - 1 - 3) - i := by omega
      have hc := mode_commutator A b a x (-p + (α + β + p - 1 - 3) - i) i
      rw [Omega_mode_vanish hx.omega hb hq, map_zero, sub_zero] at hc
      rw [hc]
      exact hcomm _ _ (by ring)

/-- **The degree-two raising lemma.** -/
theorem raise2_mem {G : Set V} (hG : ∀ g ∈ G, ∃ j : ℤ, 1 ≤ j ∧ g ∈ W.grading j)
    (htop : (⊤ : Submodule ℂ V) = Submodule.span ℂ {y | IsIterProd W G y} ⊔ O₂ W)
    {x : M} (hx : ScalarTop A x) (hD : Deg1Line A x) :
    ∀ (k : ℤ) (a : V), a ∈ W.grading k → mode (A.YM a) (k - 3) x ∈ raiseSpan2 A G x := by
  set S := raiseSpan2 A G x
  suffices H : ∀ N : ℕ, ∀ (k : ℤ) (a : V), a ∈ W.grading k → k < N →
      mode (A.YM a) (k - 3) x ∈ S by
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
        mode (A.YM c) (j - 3) x ∈ S := fun j c hc hj => ih j c hc (by omega)
    have hgen : ∀ y : V, (IsIterProd W G y ∨ y ∈ O₂homGen W) → y ∈ W.grading k →
        mode (A.YM y) (k - 3) x ∈ S := by
      intro y hy hyk
      rcases hy with hy | ⟨p, q, a', b', ha', hb', rfl⟩
      · cases hy with
        | vacuum =>
          by_cases hk2 : k = 2
          · subst hk2
            have h0 := eq_zero_of_mem_two_gradings (W := W) (show (2 : ℤ) ≠ 0 by norm_num) hyk
              W.vacuum_mem
            rw [h0, map_zero, mode_zero, LinearMap.zero_apply]; exact S.zero_mem
          · have := A.act_vacuum (k - 3) x
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
                rw [show α + 0 + 1 - 1 - 3 = α - 3 by ring]
                exact mem_raiseSpan2_of_gen hs hsα
              · rw [W.smul_zero_right, map_zero, mode_zero, LinearMap.zero_apply]; exact S.zero_mem
            · exact raise2_step hx hD hsα hbβ p hp (by omega) hβ (Or.inl hα) IH
                (mem_raiseSpan2_of_gen hs hsα)
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
          have := raise2_step hx hD ha' hb' 2 (by norm_num) hp0 hq0 (Or.inr le_rfl)
            (fun j c hc hj => IH j c hc (by omega)) (IH p a' ha' (by omega))
          rwa [show p + q + 2 - 1 - 3 = p + q + 1 - 3 by ring] at this
        · exact absurd (eq_zero_of_mem_two_gradings (W := W) hkk hyk hyg) hz
    have hspan : a ∈ Submodule.span ℂ ({y | IsIterProd W G y} ∪ O₂homGen W) := by
      have hmem : a ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
      rw [htop, O₂_eq_span_homGen, ← Submodule.span_union] at hmem
      exact hmem
    have hproj : ∀ y ∈ Submodule.span ℂ ({y | IsIterProd W G y} ∪ O₂homGen W),
        mode (A.YM (piHom W k y)) (k - 3) x ∈ S := by
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
