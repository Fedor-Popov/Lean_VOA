/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ModuleC2Reduction
import VOA.Modularity.GNLink2Representatives
import VOA.Modularity.AnFiniteDim
import VOA.Modularity.C2GradedVanishing

/-!
# Buhl's spanning theorem for modules, layer 1: generator words and the grade filtration

Fix a `C₂`-cofinite `𝒱` with a finite family of homogeneous generators `gen i ∈ 𝒱_{wt i}`
(`wt i ≥ 1`) spanning `𝒱` modulo `ℂ𝟙 + C₂(𝒱)` (`GenData`), a weak module `M` and a subspace
`B₀ ⊆ M` (later: the bottom level).  A **generator word** is a list of letters `(i, k)`, acting
as `gen_{i₁,(k₁)} ⋯ gen_{iᵣ,(kᵣ)}` (head outermost) with **arbitrary** integer modes; its
**grade** is `Σ wt iⱼ`.  `E G` is the span of the words of grade `≤ G` applied to `B₀`.

* `act_mem_E` — for `u ∈ 𝒱_p` and every mode, `u₍ₖ₎ · E G ⊆ E (G + p)` (induction on `p`
  through the iterate formula for `a₍₋₂₎b`);
* `O₂_act_mem_E` — for `u ∈ C₂(𝒱) ∩ 𝒱_p` the grade drops: `u₍ₖ₎ · E G ⊆ E (G + p − 1)`;
* `perm_sub_mem_E` — permuting the letters of a word of grade `G` changes it only by an
  element of `E (G − 1)` (commutator formula), so `gr^E M` is commutative;
* `iSup_E_eq_top` — if `B₀` generates `M`, the filtration is exhaustive.

No `sorry`, no axioms beyond Lean's three.
-/

namespace VOA.Huang.BuhlSpanning

open VOA VOA.Huang.FusionC2 VOA.Huang.ModuleC2
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A finite homogeneous generating family of `𝒱` modulo `ℂ𝟙 + C₂(𝒱)`, of positive weights. -/
structure GenData (W : VertexOperatorAlgebra 𝒱) where
  /-- Number of generators. -/
  g : ℕ
  /-- The generators. -/
  gen : Fin g → 𝒱
  /-- Their weights. -/
  wt : Fin g → ℕ
  wt_pos : ∀ i, 1 ≤ wt i
  gen_mem : ∀ i, gen i ∈ W.grading (wt i : ℤ)
  dec : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W

/-- Generator data exist for a `C₂`-cofinite `𝒱`. -/
theorem exists_genData (hC2 : C2Cofinite W) : Nonempty (GenData W) := by
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  exact ⟨⟨g, gen, wt, hwt, hgen, hdec⟩⟩

variable (D : GenData W) (A : WeakModule W M) (B₀ : Submodule ℂ M)

/-- A letter `(i, k)`: the mode `gen_{i,(k)}`. -/
abbrev Ltr (D : GenData W) := Fin D.g × ℤ

/-- The action of a word, head outermost, as a linear map. -/
noncomputable def wordL : List (Ltr D) → (M →ₗ[ℂ] M)
  | [] => LinearMap.id
  | a :: l => mode (A.YM (D.gen a.1)) a.2 ∘ₗ wordL l

@[simp] theorem wordL_nil : wordL D A [] = LinearMap.id := rfl

@[simp] theorem wordL_cons (a : Ltr D) (l : List (Ltr D)) (x : M) :
    wordL D A (a :: l) x = mode (A.YM (D.gen a.1)) a.2 (wordL D A l x) := rfl

theorem wordL_append (l₁ l₂ : List (Ltr D)) (x : M) :
    wordL D A (l₁ ++ l₂) x = wordL D A l₁ (wordL D A l₂ x) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The grade `Σ wt` of a word. -/
def grade (l : List (Ltr D)) : ℕ := (l.map (fun a => D.wt a.1)).sum

@[simp] theorem grade_nil : grade D [] = 0 := rfl

@[simp] theorem grade_cons (a : Ltr D) (l : List (Ltr D)) :
    grade D (a :: l) = D.wt a.1 + grade D l := by simp [grade]

theorem grade_append (l₁ l₂ : List (Ltr D)) : grade D (l₁ ++ l₂) = grade D l₁ + grade D l₂ := by
  simp [grade]

theorem grade_perm {l₁ l₂ : List (Ltr D)} (h : l₁.Perm l₂) : grade D l₁ = grade D l₂ :=
  (h.map _).sum_eq

theorem grade_eq_zero {l : List (Ltr D)} (h : grade D l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l =>
      rw [grade_cons] at h
      have := D.wt_pos a.1
      omega

/-- `E G`: words of grade `≤ G` applied to `B₀`. -/
noncomputable def E (G : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List (Ltr D)) (b : M), grade D l ≤ G ∧ b ∈ B₀ ∧ y = wordL D A l b}

variable {D A B₀}

theorem E_mono {G G' : ℕ} (h : G ≤ G') : E D A B₀ G ≤ E D A B₀ G' := by
  refine Submodule.span_mono ?_
  rintro y ⟨l, b, hl, hb, rfl⟩
  exact ⟨l, b, le_trans hl h, hb, rfl⟩

theorem wordL_mem_E {l : List (Ltr D)} {b : M} (hb : b ∈ B₀) {G : ℕ} (hl : grade D l ≤ G) :
    wordL D A l b ∈ E D A B₀ G :=
  Submodule.subset_span ⟨l, b, hl, hb, rfl⟩

theorem mem_E_zero {b : M} (hb : b ∈ B₀) (G : ℕ) : b ∈ E D A B₀ G := by
  have := wordL_mem_E (D := D) (A := A) (l := []) hb (G := G) (by simp)
  simpa using this

/-- Prepending a letter raises the grade by its weight. -/
theorem gen_act_mem_E (i : Fin D.g) (k : ℤ) {G : ℕ} {y : M} (hy : y ∈ E D A B₀ G) :
    mode (A.YM (D.gen i)) k y ∈ E D A B₀ (G + D.wt i) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, b, hl, hb, rfl⟩ := hz
      have h := wordL_mem_E (D := D) (A := A) (l := (i, k) :: l) hb (G := G + D.wt i)
        (by rw [grade_cons]; dsimp only; omega)
      simpa using h
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- A word of grade `H` maps `E G` into `E (G + H)`. -/
theorem wordL_E_mem (l : List (Ltr D)) {G : ℕ} {y : M} (hy : y ∈ E D A B₀ G) :
    wordL D A l y ∈ E D A B₀ (G + grade D l) := by
  induction l with
  | nil => simpa using hy
  | cons a l ih =>
      rw [wordL_cons, grade_cons]
      have := gen_act_mem_E (D := D) a.1 a.2 ih
      refine (E_mono ?_) this
      omega

/-- A `C₂`-generator `a₍₋₂₎b` with `a ∈ 𝒱_q`, `b ∈ 𝒱_r` acts with grade raise `q + r`, provided
`a` and `b` themselves act with grade raise `≤` their weights. -/
theorem smulNegTwo_act_mem_E {a b : 𝒱} {q r : ℕ}
    (ha : ∀ (k : ℤ) (G : ℕ) (y : M), y ∈ E D A B₀ G → mode (A.YM a) k y ∈ E D A B₀ (G + q))
    (hb : ∀ (k : ℤ) (G : ℕ) (y : M), y ∈ E D A B₀ G → mode (A.YM b) k y ∈ E D A B₀ (G + r))
    (k : ℤ) {G : ℕ} {y : M} (hy : y ∈ E D A B₀ G) :
    mode (A.YM (W.smul a (-2) b)) k y ∈ E D A B₀ (G + q + r) := by
  rw [module_iterate0 A a b y (-2) k]
  refine finsum_mem_submodule_lf _ _ (fun i => Submodule.smul_mem _ _ ?_)
  refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · have h1 := hb (k + i) G y hy
    have h2 := ha (-2 - i) (G + r) _ h1
    refine (E_mono ?_) h2; omega
  · have h1 := ha i G y hy
    have h2 := hb (-2 + k - i) (G + q) _ h1
    refine (E_mono ?_) h2; omega

/-- **Modes of `𝒱_p` raise the grade by at most `p`.** -/
theorem act_mem_E : ∀ (p : ℕ) (u : 𝒱), u ∈ W.grading (p : ℤ) →
    ∀ (k : ℤ) (G : ℕ) (y : M), y ∈ E D A B₀ G → mode (A.YM u) k y ∈ E D A B₀ (G + p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
  intro u hu k G y hy
  have hdecomp := gnLink2_homog_mem_repSpan_sup_O₂ W D.gen D.wt D.gen_mem D.dec hu
  obtain ⟨s, hs, o, ho, rfl⟩ := Submodule.mem_sup.mp hdecomp
  clear hdecomp hu
  rw [mode_YM_add]
  refine Submodule.add_mem _ ?_ ?_
  · induction hs using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨i, hi, rfl⟩ | ⟨hp0, rfl⟩
        · have := gen_act_mem_E (D := D) i k hy
          rwa [hi] at this
        · subst hp0
          have hv := A.act_vacuum k y
          simp only [WeakModule.act_def] at hv
          rw [hv]
          split_ifs
          · simpa using hy
          · exact Submodule.zero_mem _
    | zero => simp
    | add x z _ _ hx hz => rw [mode_YM_add]; exact Submodule.add_mem _ hx hz
    | smul c x _ hx => rw [mode_YM_smul]; exact Submodule.smul_mem _ c hx
  · have ho' : o ∈ Submodule.span ℂ (CGenHomDeg W (-2) (p : ℤ)) :=
      CGen_inf_grading_le_span_deg W (-2) (p : ℤ) ho
    clear ho hs
    induction ho' using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨q, r, a, b, ha, hb, hqr, rfl⟩ := hz
        rcases lt_or_ge q 0 with hq | hq
        · rw [W.positivity q hq, Submodule.mem_bot] at ha
          subst ha
          simp [PreVertexAlgebra.smul_def]
        rcases lt_or_ge r 0 with hr | hr
        · rw [W.positivity r hr, Submodule.mem_bot] at hb
          subst hb
          simp [PreVertexAlgebra.smul_def]
        obtain ⟨Q, rfl⟩ : ∃ Q : ℕ, q = (Q : ℤ) := ⟨q.toNat, by omega⟩
        obtain ⟨R, rfl⟩ : ∃ R : ℕ, r = (R : ℤ) := ⟨r.toNat, by omega⟩
        have hQ : Q < p := by omega
        have hR : R < p := by omega
        have h := smulNegTwo_act_mem_E (D := D) (A := A) (B₀ := B₀)
          (fun k G y hy => IH Q hQ a ha k G y hy) (fun k G y hy => IH R hR b hb k G y hy) k hy
        refine (E_mono ?_) h
        omega
    | zero => simp
    | add x z _ _ hx hz => rw [mode_YM_add]; exact Submodule.add_mem _ hx hz
    | smul c x _ hx => rw [mode_YM_smul]; exact Submodule.smul_mem _ c hx

/-- **`C₂(𝒱)` drops the grade**: for `u ∈ C₂(𝒱) ∩ 𝒱_p`, `u₍ₖ₎ · E G ⊆ E (G + p − 1)`. -/
theorem O₂_act_mem_E (p : ℕ) {u : 𝒱} (hu : u ∈ O₂ W ⊓ W.grading (p : ℤ)) (k : ℤ) {G : ℕ}
    {y : M} (hy : y ∈ E D A B₀ G) : mode (A.YM u) k y ∈ E D A B₀ (G + (p - 1)) := by
  have ho' : u ∈ Submodule.span ℂ (CGenHomDeg W (-2) (p : ℤ)) :=
    CGen_inf_grading_le_span_deg W (-2) (p : ℤ) hu
  clear hu
  induction ho' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨q, r, a, b, ha, hb, hqr, rfl⟩ := hz
      rcases lt_or_ge q 0 with hq | hq
      · rw [W.positivity q hq, Submodule.mem_bot] at ha
        subst ha
        simp [PreVertexAlgebra.smul_def]
      rcases lt_or_ge r 0 with hr | hr
      · rw [W.positivity r hr, Submodule.mem_bot] at hb
        subst hb
        simp [PreVertexAlgebra.smul_def]
      obtain ⟨Q, rfl⟩ : ∃ Q : ℕ, q = (Q : ℤ) := ⟨q.toNat, by omega⟩
      obtain ⟨R, rfl⟩ : ∃ R : ℕ, r = (R : ℤ) := ⟨r.toNat, by omega⟩
      have h := smulNegTwo_act_mem_E (D := D) (A := A) (B₀ := B₀)
        (fun k G y hy => act_mem_E Q a ha k G y hy) (fun k G y hy => act_mem_E R b hb k G y hy)
        k hy
      refine (E_mono ?_) h
      omega
  | zero => simp
  | add x z _ _ hx hz => rw [mode_YM_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [mode_YM_smul]; exact Submodule.smul_mem _ c hx

/-- **Reordering a word costs one grade.** -/
theorem perm_sub_mem_E {l₁ l₂ : List (Ltr D)} (h : l₁.Perm l₂) {b : M} (hb : b ∈ B₀) :
    wordL D A l₁ b - wordL D A l₂ b ∈ E D A B₀ (grade D l₁ - 1) := by
  induction h with
  | nil => simp
  | cons x h ih =>
      rename_i l₁ l₂
      by_cases h0 : l₁ = []
      · subst h0
        rw [List.Perm.nil_eq h]; simp
      · have hg : 1 ≤ grade D l₁ := by
          by_contra hcon
          exact h0 (grade_eq_zero D (by omega))
        rw [wordL_cons, wordL_cons, ← map_sub]
        have := gen_act_mem_E (D := D) x.1 x.2 ih
        refine (E_mono ?_) this
        rw [grade_cons]; omega
  | swap x y l =>
      rw [wordL_cons, wordL_cons, wordL_cons, wordL_cons,
        VOA.mode_commutator A (D.gen y.1) (D.gen x.1) (wordL D A l b) y.2 x.2]
      refine finsum_mem_submodule_lf _ _ (fun s => ?_)
      rcases lt_or_ge s 0 with hs | hs
      · rw [cbz_apply_neg _ hs, zero_smul]; exact Submodule.zero_mem _
      refine Submodule.smul_mem _ _ ?_
      have hgr := W.smul_mem_grading (D.gen_mem y.1) (D.gen_mem x.1) s
      rcases lt_or_ge ((D.wt y.1 : ℤ) + (D.wt x.1 : ℤ) - s - 1) 0 with hneg | hnn
      · rw [W.positivity _ hneg, Submodule.mem_bot] at hgr
        rw [hgr]; simp
      obtain ⟨P, hP⟩ : ∃ P : ℕ, ((D.wt y.1 : ℤ) + (D.wt x.1 : ℤ) - s - 1) = (P : ℤ) :=
        ⟨_, (Int.toNat_of_nonneg hnn).symm⟩
      rw [hP] at hgr
      have hz : wordL D A l b ∈ E D A B₀ (grade D l) := wordL_mem_E hb le_rfl
      have := act_mem_E P _ hgr (y.2 + x.2 - s) _ _ hz
      refine (E_mono ?_) this
      rw [grade_cons, grade_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ =>
      rename_i l₁ l₂ l₃
      have h12 := grade_perm D h₁
      have := Submodule.add_mem _ ih₁ (h12 ▸ ih₂)
      rwa [sub_add_sub_cancel] at this

/-- Every mode of every vector of `𝒱` preserves `⨆ E`. -/
theorem act_mem_iSup_E (u : 𝒱) (k : ℤ) {y : M} (hy : y ∈ ⨆ G, E D A B₀ G) :
    mode (A.YM u) k y ∈ ⨆ G, E D A B₀ G := by
  have hdir : Directed (· ≤ ·) (E D A B₀) := fun a b =>
    ⟨max a b, E_mono (le_max_left a b), E_mono (le_max_right a b)⟩
  obtain ⟨G, hG⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hy
  refine induction_grading (W := W) (motive := fun u => mode (A.YM u) k y ∈ ⨆ G, E D A B₀ G) u
    (by simp) (fun a b ha hb => ?_) (fun p a ha => ?_)
  · change mode (A.YM (a + b)) k y ∈ _
    rw [mode_YM_add]; exact Submodule.add_mem _ ha hb
  · rcases lt_or_ge p 0 with hp | hp
    · rw [W.positivity p hp, Submodule.mem_bot] at ha
      subst ha; simp
    · obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
      exact Submodule.mem_iSup_of_mem (G + P) (act_mem_E P a ha k G y hG)

/-- `⨆ E` as a weak submodule. -/
noncomputable def iSupESub : WeakModule.Submodule' A where
  carrier := ⨆ G, E D A B₀ G
  act_mem := fun u n _ hx => act_mem_iSup_E u n hx

/-- If `B₀` generates `M`, the grade filtration is exhaustive. -/
theorem iSup_E_eq_top
    (hgen : ∀ S : WeakModule.Submodule' A, B₀ ≤ S.carrier → S.carrier = ⊤) :
    (⨆ G, E D A B₀ G) = ⊤ :=
  hgen (iSupESub (D := D) (A := A) (B₀ := B₀))
    (fun _ hb => Submodule.mem_iSup_of_mem 0 (mem_E_zero hb 0))

end VOA.Huang.BuhlSpanning
