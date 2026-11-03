/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorFinGraded

/-!
# Module-level `C₂`-cofiniteness of finitely generated logarithmic modules (stage T1d, part 2)

For a `C₂`-cofinite VOA `V` and a finitely generated `LogVModule` `N`:

* `exists_c2_cofinite_weights` — **graded `C₂`-cofiniteness of `N`**: there is a finite set
  `F ⊂ ℂ` of weights such that for `α ∉ F`, every vector of `N_[α]` lies in `c2Part N α`, the
  span of `u₍ℓ₎ w` with `u ∈ V_(d)`, `ℓ ≤ −2`, `w ∈ N_[α − (d − ℓ − 1)]`.
  (This is the graded form of `dim N/C₂(N) < ∞`; Buhl, Gaberdiel–Neitzke, Miyamoto.)
* `exists_weight_cosets` — the weights of `N` lie in finitely many cosets `h + ℤ`;
* `exists_finset_weights_re_lt` — hence only finitely many weights have `Re α < C`.

The source of both is the library's Buhl spanning theorem for arbitrary weak cyclic modules,
`ABDWeakAdmissible.weak_cyclic_spanning`: a cyclic module `⟨x⟩` is spanned by *normal* words
(modes sorted increasingly from the outside, bounded repetitions, modes `< Bm`) applied to `x`.
A normal word whose outermost mode is `≥ −1` has *all* modes in `[−1, Bm)`, and there are only
finitely many of those; every other normal word has outermost mode `≤ −2`, i.e. lies in `C₂`.

No `sorry`, no new axioms.
-/

namespace VOA.LogTensor.LogFin

open Module (End)
open VOA.Classification.COne VOA.Huang.BuhlSpanning ABDWeakAdmissible C2LevelFinite PlusRational

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M] (N : LogVModule W M)

/-- A finitely generated `LogVModule` is the sum of finitely many cyclic submodules on
homogeneous generators. -/
theorem exists_homogeneous_generators (hfg : FinGen N.toWeakModule) :
    ∃ G : Finset (M × ℂ), (∀ p ∈ G, p.1 ∈ N.weight p.2) ∧
      ∀ y : M, y ∈ (⨆ p : G, cyclic N.toWeakModule p.1.1) := by
  classical
  obtain ⟨S, hSfin, hgen⟩ := hfg
  have hdec : ∀ s : M, ∃ (F : Finset ℂ) (μ : ∀ α, N.weight α), ∑ α ∈ F, (μ α : M) = s := by
    intro s
    have hs : s ∈ ⨆ α, N.weight α := by rw [iSup_weight_eq_top]; trivial
    obtain ⟨F, hF⟩ := Submodule.mem_iSup_iff_exists_finset.mp hs
    obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hF
    exact ⟨F, μ, hμ⟩
  choose F μ hμ using hdec
  let G : Finset (M × ℂ) :=
    hSfin.toFinset.biUnion (fun s => (F s).image (fun α => ((μ s α : M), α)))
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    simp only [G, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨s, _, α, _, rfl⟩ := hp
    exact (μ s α).2
  · set P := ⨆ p : G, cyclic N.toWeakModule p.1.1 with hP
    have htop : P.restrictScalars ℂ = ⊤ := by
      apply hgen
      · intro s hs
        rw [← hμ s]
        refine Submodule.sum_mem _ (fun α hα => ?_)
        have hp : ((μ s α : M), α) ∈ G := by
          simp only [G, Finset.mem_biUnion, Finset.mem_image]
          exact ⟨s, hSfin.mem_toFinset.mpr hs, α, hα, rfl⟩
        exact (le_iSup (fun p : G => cyclic N.toWeakModule p.1.1) ⟨_, hp⟩)
          (Submodule.mem_span_singleton_self _)
      · exact modeStable_restrictScalars N P
    intro y
    have : y ∈ P.restrictScalars ℂ := by rw [htop]; trivial
    exact this

/-- A word in the Buhl generators applied to a homogeneous vector is homogeneous. -/
theorem wordL_mem_weight (D : GenData W) (l : List (Ltr D)) {x : M} {β : ℂ}
    (hx : x ∈ N.weight β) :
    wordL D N.toWeakModule l x ∈ N.weight (β + (degree D l : ℂ)) := by
  induction l with
  | nil => simpa using hx
  | cons a l ih =>
    rw [wordL_cons]
    have h := mode_mem_weight N (D.gen_mem a.1) a.2 ih
    convert h using 2
    rw [degree_cons]
    push_cast
    ring

/-- The structure of one cyclic submodule on a homogeneous generator of weight `β`: outside a
finite set of weights its graded pieces lie in `C₂`, and all its weights lie in `β + ℤ`. -/
theorem cyclic_struct (hC2 : C2Cofinite W) {x : M} {β : ℂ} (hx : x ∈ N.weight β) :
    ∃ F : Finset ℂ, ∀ y ∈ (cyclic N.toWeakModule x).restrictScalars ℂ,
      (∀ α, α ∉ F → proj N α y ∈ c2Part N α) ∧
      (∀ α, (∀ d : ℤ, α ≠ β + d) → proj N α y = 0) := by
  classical
  obtain ⟨D, Q, Bm, _, _, hspan⟩ := weak_cyclic_spanning hC2 N.toWeakModule x
  let Al : Finset (Ltr D) := Finset.univ ×ˢ Finset.Icc (-1 : ℤ) Bm
  have hfin := finite_lists_count_lt Al Q
  let F : Finset ℂ := hfin.toFinset.image (fun l => β + (degree D l : ℂ))
  refine ⟨F, fun y hy => ?_⟩
  have hy' := hspan hy
  refine Submodule.iSup_induction _
    (motive := fun y => (∀ α, α ∉ F → proj N α y ∈ c2Part N α) ∧
      (∀ α, (∀ d : ℤ, α ≠ β + d) → proj N α y = 0)) hy' ?_ ?_ ?_
  · intro d z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, ⟨hn, hm, _⟩, rfl⟩ := hz
      have hw := wordL_mem_weight N D l hx
      constructor
      · intro α hα
        by_cases he : β + (degree D l : ℂ) = α
        · rw [← he, proj_of_mem N hw]
          -- the word is not in the finite small set, so it has a mode `≤ −2`
          have hnot : ¬ ((∀ e ∈ l, e ∈ Al) ∧ ∀ a, l.count a < Q) := by
            intro hsmall
            apply hα
            rw [← he]
            exact Finset.mem_image.mpr ⟨l, hfin.mem_toFinset.mpr hsmall, rfl⟩
          have hex : ∃ e ∈ l, e.2 ≤ -2 := by
            by_contra hcon
            push Not at hcon
            apply hnot
            refine ⟨fun e he' => ?_, hn.2⟩
            have h1 := hcon e he'
            have h2 := hm e he'
            simp only [Al, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
            omega
          obtain ⟨e, he', hle⟩ := hex
          cases l with
          | nil => simp at he'
          | cons a t =>
            have ha : a.2 ≤ -2 := by
              rcases List.mem_cons.mp he' with h | h
              · rw [← h]; exact hle
              · have := List.rel_of_pairwise_cons hn.1 h
                simp only [modeLE] at this
                omega
            rw [wordL_cons]
            have hwt := wordL_mem_weight N D t hx
            refine Submodule.subset_span ⟨(D.wt a.1 : ℤ), a.2, D.gen a.1,
              wordL D N.toWeakModule t x, D.gen_mem a.1, by positivity, ha, ?_, rfl⟩
            convert hwt using 2
            rw [degree_cons]
            push_cast
            ring
        · rw [proj_of_mem_ne N hw he]
          exact Submodule.zero_mem _
      · intro α hα
        exact proj_of_mem_ne N hw (fun h => hα (degree D l) h.symm)
    | zero =>
      exact ⟨fun α _ => by simp, fun α _ => by simp⟩
    | add a b _ _ ha hb =>
      simp only [map_add]
      exact ⟨fun α hα => Submodule.add_mem _ (ha.1 α hα) (hb.1 α hα),
        fun α hα => by rw [ha.2 α hα, hb.2 α hα, add_zero]⟩
    | smul c a _ ha =>
      simp only [map_smul]
      exact ⟨fun α hα => Submodule.smul_mem _ c (ha.1 α hα),
        fun α hα => by rw [ha.2 α hα, smul_zero]⟩
  · exact ⟨fun α _ => by simp, fun α _ => by simp⟩
  · intro a b ha hb
    simp only [map_add]
    exact ⟨fun α hα => Submodule.add_mem _ (ha.1 α hα) (hb.1 α hα),
      fun α hα => by rw [ha.2 α hα, hb.2 α hα, add_zero]⟩

/-- Per-generator data, chosen uniformly over a finite homogeneous generating family. -/
theorem exists_generator_data (hC2 : C2Cofinite W) (hfg : FinGen N.toWeakModule) :
    ∃ (G : Finset (M × ℂ)) (F : Finset ℂ),
      (∀ y : M, y ∈ (⨆ p : G, cyclic N.toWeakModule p.1.1)) ∧
      ∀ p : G, ∀ y ∈ (cyclic N.toWeakModule p.1.1).restrictScalars ℂ,
        (∀ α, α ∉ F → proj N α y ∈ c2Part N α) ∧
        (∀ α, (∀ d : ℤ, α ≠ p.1.2 + d) → proj N α y = 0) := by
  classical
  obtain ⟨G, hG, hspan⟩ := exists_homogeneous_generators N hfg
  have h : ∀ p : G, ∃ F : Finset ℂ, ∀ y ∈ (cyclic N.toWeakModule p.1.1).restrictScalars ℂ,
      (∀ α, α ∉ F → proj N α y ∈ c2Part N α) ∧
      (∀ α, (∀ d : ℤ, α ≠ p.1.2 + d) → proj N α y = 0) :=
    fun p => cyclic_struct N hC2 (hG p.1 p.2)
  choose Fp hFp using h
  refine ⟨G, Finset.univ.biUnion Fp, hspan, fun p y hy => ⟨fun α hα => ?_, (hFp p y hy).2⟩⟩
  exact (hFp p y hy).1 α (fun h' => hα (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, h'⟩))

/-- **Graded `C₂`-cofiniteness of a finitely generated logarithmic module.** -/
theorem exists_c2_cofinite_weights (hC2 : C2Cofinite W) (hfg : FinGen N.toWeakModule) :
    ∃ F : Finset ℂ, ∀ α, α ∉ F → N.weight α ≤ c2Part N α := by
  obtain ⟨G, F, hspan, hdat⟩ := exists_generator_data N hC2 hfg
  refine ⟨F, fun α hα w hw => ?_⟩
  rw [← proj_of_mem N hw]
  refine Submodule.iSup_induction _ (motive := fun z => proj N α z ∈ c2Part N α)
    (hspan w) ?_ ?_ ?_
  · intro p z hz
    exact (hdat p z hz).1 α hα
  · dsimp only; rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    dsimp only at ha hb ⊢; rw [map_add]; exact Submodule.add_mem _ ha hb

/-- The weights of a finitely generated logarithmic module lie in finitely many `ℤ`-cosets. -/
theorem exists_weight_cosets (hC2 : C2Cofinite W) (hfg : FinGen N.toWeakModule) :
    ∃ H : Finset ℂ, ∀ α, N.weight α ≠ ⊥ → ∃ h ∈ H, ∃ d : ℤ, α = h + d := by
  classical
  obtain ⟨G, F, hspan, hdat⟩ := exists_generator_data N hC2 hfg
  refine ⟨G.image Prod.snd, fun α hα => ?_⟩
  by_contra hno
  push Not at hno
  apply hα
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot, ← proj_of_mem N hw]
  refine Submodule.iSup_induction _ (motive := fun z => proj N α z = 0) (hspan w) ?_ ?_ ?_
  · intro p z hz
    exact (hdat p z hz).2 α (fun d hd => hno p.1.2 (Finset.mem_image.mpr ⟨p.1, p.2, rfl⟩) d hd)
  · dsimp only; rw [map_zero]
  · intro a b ha hb
    dsimp only at ha hb ⊢; rw [map_add, ha, hb, add_zero]

/-- Only finitely many weights of a finitely generated logarithmic module have `Re α < C`. -/
theorem exists_finset_weights_re_lt (hC2 : C2Cofinite W) (hfg : FinGen N.toWeakModule)
    (C : ℝ) : ∃ F : Finset ℂ, ∀ α, N.weight α ≠ ⊥ → α.re < C → α ∈ F := by
  classical
  obtain ⟨H, hH⟩ := exists_weight_cosets N hC2 hfg
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine ⟨H.biUnion (fun h => (Finset.Icc ⌈B - h.re⌉ ⌊C - h.re⌋).image
    (fun d : ℤ => h + (d : ℂ))), fun α hα hre => ?_⟩
  obtain ⟨h, hh, d, rfl⟩ := hH α hα
  have hlo := hB _ hα
  simp only [Complex.add_re, Complex.intCast_re] at hlo hre
  refine Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_image.mpr ⟨d, ?_, rfl⟩⟩
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.ceil_le]; linarith
  · rw [Int.le_floor]; linarith

end VOA.LogTensor.LogFin
