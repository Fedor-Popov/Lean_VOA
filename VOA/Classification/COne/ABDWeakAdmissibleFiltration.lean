import VOA.Classification.COne.ABDWeakAdmissibleDegree

/-! Buhl's weight filtration with total mode degree retained. -/
namespace VOA.Classification.COne.ABDWeakAdmissible.DegreeFiltration
open VOA.Huang.BuhlSpanning VOA.Huang.FusionC2 VOA.Huang.ModuleC2 C2LevelFinite

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

theorem degree_append (D : GenData W) (l r : List (Ltr D)) :
    degree D (l ++ r) = degree D l + degree D r := by simp [degree]

theorem degree_perm (D : GenData W) {l r : List (Ltr D)} (h : l.Perm r) :
    degree D l = degree D r := (h.map _).sum_eq

theorem degree_eq (D : GenData W) (l : List (Ltr D)) :
    degree D l = (grade D l : ℤ) - modeSum D l - l.length := by
  induction l with
  | nil => simp [modeSum]
  | cons a l ih => simp [degree_cons, grade_cons, modeSum, ih]; ring

/-- The generator-word filtration in one fixed total mode degree. -/
noncomputable def E (D : GenData W) (A : WeakModule W M) (B : Submodule ℂ M)
    (G : ℕ) (d : ℤ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List (Ltr D)) (b : M),
    grade D l ≤ G ∧ degree D l = d ∧ b ∈ B ∧ y = wordL D A l b}

variable {D : GenData W} {A : WeakModule W M} {B : Submodule ℂ M}

theorem E_mono {G H : ℕ} {d : ℤ} (h : G ≤ H) : E D A B G d ≤ E D A B H d := by
  apply Submodule.span_mono
  rintro y ⟨l, b, hl, hd, hb, rfl⟩
  exact ⟨l, b, hl.trans h, hd, hb, rfl⟩

theorem wordL_mem_E {l : List (Ltr D)} {b : M} (hb : b ∈ B)
    {G : ℕ} (hl : grade D l ≤ G) : wordL D A l b ∈ E D A B G (degree D l) :=
  Submodule.subset_span ⟨l, b, hl, rfl, hb, rfl⟩

theorem mem_E_zero {b : M} (hb : b ∈ B) (G : ℕ) : b ∈ E D A B G 0 := by
  exact Submodule.subset_span ⟨[], b, by simp, rfl, hb, rfl⟩

theorem gen_act_mem_E (i : Fin D.g) (k : ℤ) {G : ℕ} {d : ℤ} {y : M}
    (hy : y ∈ E D A B G d) :
    mode (A.YM (D.gen i)) k y ∈ E D A B (G + D.wt i) (d + (D.wt i - k - 1)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, b, hl, hd, hb, rfl⟩ := hz
    exact Submodule.subset_span ⟨(i,k) :: l, b, by simp; omega,
      by simp [hd]; omega, hb, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem wordL_E_mem (l : List (Ltr D)) {G : ℕ} {d : ℤ} {y : M}
    (hy : y ∈ E D A B G d) :
    wordL D A l y ∈ E D A B (G + grade D l) (d + degree D l) := by
  induction l with
  | nil => simpa using hy
  | cons a l ih =>
    have h := gen_act_mem_E a.1 a.2 ih
    simpa only [wordL_cons, grade_cons, degree_cons, Nat.add_left_comm,
      Nat.add_assoc, add_left_comm, add_assoc, add_comm] using h

theorem smulNegTwo_act_mem_E {a b : 𝒱} {q r : ℕ}
    (ha : ∀ (k : ℤ) (G : ℕ) (d : ℤ) (y : M), y ∈ E D A B G d →
      mode (A.YM a) k y ∈ E D A B (G + q) (d + (q - k - 1)))
    (hb : ∀ (k : ℤ) (G : ℕ) (d : ℤ) (y : M), y ∈ E D A B G d →
      mode (A.YM b) k y ∈ E D A B (G + r) (d + (r - k - 1)))
    (k : ℤ) {G : ℕ} {d : ℤ} {y : M} (hy : y ∈ E D A B G d) :
    mode (A.YM (W.smul a (-2) b)) k y ∈ E D A B (G + q + r) (d + (q + r - k)) := by
  rw [module_iterate0 A a b y (-2) k]
  refine finsum_mem_submodule_lf _ _ (fun i => Submodule.smul_mem _ _ ?_)
  refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · have h := ha (-2 - i) (G + r) _ _ (hb (k + i) G d y hy)
    convert h using 1 <;> congr 1 <;> omega
  · have h := hb (-2 + k - i) (G + q) _ _ (ha i G d y hy)
    convert h using 1 <;> congr 1 <;> omega

theorem act_mem_E : ∀ (p : ℕ) (u : 𝒱), u ∈ W.grading (p : ℤ) →
    ∀ (k : ℤ) (G : ℕ) (d : ℤ) (y : M), y ∈ E D A B G d →
      mode (A.YM u) k y ∈ E D A B (G + p) (d + (p - k - 1)) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
  intro u hu k G d y hy
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
          split_ifs with hk
          · subst k; simpa using hy
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
        have h := smulNegTwo_act_mem_E (D := D) (A := A) (B := B)
          (fun k G d y hy => IH Q hQ a ha k G d y hy)
          (fun k G d y hy => IH R hR b hb k G d y hy) k hy
        have he : d + ((Q : ℤ) + R - k) = d + (p - k - 1) := by omega
        rw [he] at h
        exact E_mono (by omega) h
    | zero => simp
    | add x z _ _ hx hz => rw [mode_YM_add]; exact Submodule.add_mem _ hx hz
    | smul c x _ hx => rw [mode_YM_smul]; exact Submodule.smul_mem _ c hx

/-- **`C₂(𝒱)` drops the grade**: for `u ∈ C₂(𝒱) ∩ 𝒱_p`, `u₍ₖ₎ · E G ⊆ E (G + p − 1)`. -/
theorem O₂_act_mem_E (p : ℕ) {u : 𝒱} (hu : u ∈ O₂ W ⊓ W.grading (p : ℤ)) (k : ℤ) {G : ℕ} {d : ℤ}
    {y : M} (hy : y ∈ E D A B G d) :
    mode (A.YM u) k y ∈ E D A B (G + (p - 1)) (d + (p - k - 1)) := by
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
      have h := smulNegTwo_act_mem_E (D := D) (A := A) (B := B)
        (fun k G d y hy => act_mem_E Q a ha k G d y hy)
        (fun k G d y hy => act_mem_E R b hb k G d y hy)
        k hy
      have he : d + ((Q : ℤ) + R - k) = d + (p - k - 1) := by omega
      rw [he] at h
      exact E_mono (by omega) h
  | zero => simp
  | add x z _ _ hx hz => rw [mode_YM_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [mode_YM_smul]; exact Submodule.smul_mem _ c hx


theorem perm_sub_mem_E {l₁ l₂ : List (Ltr D)} (h : l₁.Perm l₂) {b : M} (hb : b ∈ B) :
    wordL D A l₁ b - wordL D A l₂ b ∈ E D A B (grade D l₁ - 1) (degree D l₁) := by
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
        have he : degree D l₁ + ((D.wt x.1 : ℤ) - x.2 - 1) = degree D (x :: l₁) := by
          rw [degree_cons]; omega
        rw [he] at this
        exact E_mono (by rw [grade_cons]; omega) this
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
      have hz : wordL D A l b ∈ E D A B (grade D l) (degree D l) := wordL_mem_E hb le_rfl
      have := act_mem_E P _ hgr (y.2 + x.2 - s) _ _ _ hz
      have he : degree D l + ((P : ℤ) - (y.2 + x.2 - s) - 1) =
          degree D (y :: x :: l) := by simp only [degree_cons]; omega
      rw [he] at this
      exact E_mono (by rw [grade_cons, grade_cons]; omega) this
  | trans h₁ h₂ ih₁ ih₂ =>
      rename_i l₁ l₂ l₃
      have h12 := grade_perm D h₁
      have hd := degree_perm D h₁
      rw [← h12, ← hd] at ih₂
      have := Submodule.add_mem _ ih₁ ih₂
      rwa [sub_add_sub_cancel] at this


end VOA.Classification.COne.ABDWeakAdmissible.DegreeFiltration
