import VOA.Classification.COne.PlusRat2Rational

/-! # Eigenvector lifts in a two-step extension

General `C₂`-cofinite VOA `W`.  For a weak module `A` with a simple submodule `P`, simple quotient
`A / P`, kernel bottom `hi` and quotient bottom `hj ≠ hi`:

* `bottom_eigen`: `L(0)` is semisimple on the bottom generalized weight space of `P`;
* `exists_eigen_lift`: the quotient bottom has an honest `L(0)`-eigenvector lift `x ∉ P`;
* `exists_ordinary_or_split`: either `P` has a complement, or `A` is the underlying weak module
  of an ordinary module (an `OrdVModule`).

No logarithmic extension of two different simple modules exists.  The argument: if
`y = (L(0) - hj) x ≠ 0`, then `y` generates `P`, so the bottom vector of `P` is
`(L(0) - hi) w` for a degree word `w` on `x`; `w` lies in `P` (the quotient has no weight `hi`),
where `L(0) - hi` vanishes.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat2Dual
open PlusSplitting ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible PlusRational

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A homogeneous word intertwines shifted `L(0)` operators. -/
theorem homogeneousWord_shift (A : WeakModule W M) (l : List (HomogeneousLetter W)) (c : ℂ)
    (x : M) :
    (L0 A - (c + (homogeneousDegree l : ℂ)) • 1) (homogeneousWord A l x) =
      homogeneousWord A l ((L0 A - c • 1) x) := by
  induction l with
  | nil => simp [homogeneousWord, homogeneousDegree]
  | cons a l ih =>
    simp only [homogeneousWord, LinearMap.comp_apply]
    rw [← ih, ← shifted_L0_mode A a.homogeneous a.modeIndex]
    congr 2
    simp only [homogeneousDegree]
    push_cast
    congr 1
    ring

/-- Degree spans of a shifted vector are shifted degree spans. -/
theorem degreeSpan_shift (A : WeakModule W M) (x : M) (c : ℂ) (d : ℤ) {v : M}
    (hv : v ∈ homogeneousDegreeSpan A ((L0 A - c • 1) x) d) :
    ∃ w ∈ homogeneousDegreeSpan A x d, v = (L0 A - (c + (d : ℂ)) • 1) w := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, hl, rfl⟩ := hv
    change homogeneousDegree l = d at hl
    refine ⟨homogeneousWord A l x, Submodule.subset_span ⟨l, hl, rfl⟩, ?_⟩
    rw [← hl, homogeneousWord_shift]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨wa, hwa, rfl⟩ := ha
    obtain ⟨wb, hwb, rfl⟩ := hb
    exact ⟨wa + wb, Submodule.add_mem _ hwa hwb, by rw [map_add]⟩
  | smul r a _ ha =>
    obtain ⟨wa, hwa, rfl⟩ := ha
    exact ⟨r • wa, Submodule.smul_mem _ r hwa, by rw [map_smul]⟩

theorem mem_P_mode (A : WeakModule W M) (P : Submodule (modeAlg A) M) (a : V) (n : ℤ)
    {x : M} (hx : x ∈ P) : mode (A.YM a) n x ∈ P :=
  P.smul_mem (⟨mode (A.YM a) n, Algebra.subset_adjoin ⟨a, n, rfl⟩⟩ : modeAlg A) hx

/-- An eigenvector inside a mode submodule (generic copy of `PlusRatSign.exists_eigen_in`). -/
theorem exists_eigen_in (A : WeakModule W M) (P : Submodule (modeAlg A) M) (μ : ℂ) {v : M}
    (hvP : v ∈ P) (hv : v ∈ (L0 A).maxGenEigenspace μ) (hv0 : v ≠ 0) :
    ∃ z ∈ P, z ≠ 0 ∧ L0 A z = μ • z := by
  classical
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
  set f := L0 A - μ • (1 : Module.End ℂ M)
  have hmem : ∀ j : ℕ, (f ^ j) v ∈ P := by
    intro j
    induction j with
    | zero => simpa using hvP
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      change L0 A ((f ^ j) v) - μ • (f ^ j) v ∈ P
      exact P.sub_mem (mem_P_mode A P _ 1 ih) (P.smul_of_tower_mem μ ih)
  have hex : ∃ j : ℕ, (f ^ (j + 1)) v = 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (by simpa using hk) hv0
    · exact ⟨k - 1, by rwa [Nat.sub_add_cancel hk0]⟩
  let j := Nat.find hex
  have hj : (f ^ (j + 1)) v = 0 := Nat.find_spec hex
  refine ⟨(f ^ j) v, hmem j, ?_, ?_⟩
  · intro h0
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero] at h0; exact hv0 h0
    · have := Nat.find_min hex (show j - 1 < j by omega)
      apply this
      rwa [Nat.sub_add_cancel hj0]
  · have h := hj
    rw [pow_succ', Module.End.mul_apply] at h
    change L0 A ((f ^ j) v) - μ • (f ^ j) v = 0 at h
    exact sub_eq_zero.mp h

/-- The cyclic module of a nonzero vector of an atom is the atom. -/
theorem cyclic_eq_of_atom (A : WeakModule W M) (P : Submodule (modeAlg A) M) (hP : IsAtom P)
    {z : M} (hzP : z ∈ P) (hz0 : z ≠ 0) : cyclic A z = P := by
  have hle : cyclic A z ≤ P := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzP)
  rcases hP.le_iff.mp hle with h | h
  · exfalso
    have hz : z ∈ cyclic A z := Submodule.mem_span_singleton_self z
    rw [h] at hz
    exact hz0 ((Submodule.mem_bot _).mp hz)
  · exact h

/-- `L(0)` is semisimple on the bottom generalized weight space of a simple submodule. -/
theorem bottom_eigen (hC2 : C2Cofinite W) (A : WeakModule W M) (P : Submodule (modeAlg A) M)
    (hP : IsAtom P) (h : ℂ) (hb : FactorBottom A ⊥ P h) {v : M} (hvP : v ∈ P)
    (hv : v ∈ (L0 A).maxGenEigenspace h) : L0 A v = h • v := by
  obtain ⟨v0, hv0, hv0P⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hv0' : v0 ≠ 0 := fun h0 => hv0P (by rw [h0]; exact Submodule.zero_mem _)
  obtain ⟨e, heP, he0, heL⟩ := exists_eigen_in A P h hv0.1 hv0.2 hv0'
  have hcyc := cyclic_eq_of_atom A P hP heP he0
  have heg : e ∈ (L0 A).maxGenEigenspace h := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    exact Module.End.mem_eigenspace_iff.mpr heL
  have hdeg := cyclic_inf_gen_eq_degreeSpan hC2 A heg 0
  have hvd : v ∈ homogeneousDegreeSpan A e 0 := by
    rw [← hdeg]
    refine ⟨?_, ?_⟩
    · change v ∈ cyclic A e
      rw [hcyc]; exact hvP
    · simpa using hv
  have h2 := homogeneousDegreeSpan_eigen A heL 0 hvd
  rw [Module.End.mem_eigenspace_iff] at h2
  simpa using h2

/-- **Eigenvector lift**: the quotient bottom lifts to an honest `L(0)`-eigenvector. -/
theorem exists_eigen_lift (hC2 : C2Cofinite W) (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P) {hi hj : ℂ} (hne : hi ≠ hj)
    (hb : FactorBottom A ⊥ P hi) (ht : FactorBottom A P ⊤ hj) :
    ∃ x : M, L0 A x = hj • x ∧ x ∉ P := by
  classical
  obtain ⟨x0, hx0, hx0P⟩ := exists_generalized_lift_of_factorBottom A P hj ht
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx0
  set f := L0 A - hj • (1 : Module.End ℂ M) with hfdef
  have hfmem : ∀ j : ℕ, (f ^ j) x0 ∈ (L0 A).maxGenEigenspace hj := by
    intro j
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    refine ⟨k, ?_⟩
    rw [← Module.End.mul_apply, ← pow_add, add_comm, pow_add, Module.End.mul_apply, hk,
      map_zero]
  have hex : ∃ j : ℕ, (f ^ (j + 1)) x0 ∈ P := ⟨k, by
    rw [show k + 1 = 1 + k by ring, pow_add, Module.End.mul_apply, hk, map_zero]
    exact Submodule.zero_mem _⟩
  let jj := Nat.find hex
  have hjf : (f ^ (jj + 1)) x0 ∈ P := Nat.find_spec hex
  have hjP : (f ^ jj) x0 ∉ P := by
    rcases Nat.eq_zero_or_pos jj with hj0 | hj0
    · rw [hj0, pow_zero]; exact hx0P
    · have := Nat.find_min hex (show jj - 1 < jj by omega)
      rwa [Nat.sub_add_cancel hj0] at this
  set x := (f ^ jj) x0 with hxdef
  have hxg : x ∈ (L0 A).maxGenEigenspace hj := hfmem jj
  have hfx : f x = (f ^ (jj + 1)) x0 := by rw [hxdef, pow_succ', Module.End.mul_apply]
  set y := f x with hydef
  have hyP : y ∈ P := by rw [hfx]; exact hjf
  have hyg : y ∈ (L0 A).maxGenEigenspace hj := by rw [hfx]; exact hfmem (jj + 1)
  refine ⟨x, ?_, hjP⟩
  suffices hy0 : y = 0 by
    have h := hy0
    rw [hydef, hfdef] at h
    change L0 A x - hj • x = 0 at h
    exact sub_eq_zero.mp h
  by_contra hy0
  -- the kernel bottom lies in the coset of `hj`
  have hle : hi.re ≤ hj.re := hb.2 hj (fun hh => hy0 ((Submodule.mem_bot ℂ).mp (hh ⟨hyP, hyg⟩)))
  have hcyc := cyclic_eq_of_atom A P hP hyP hy0
  obtain ⟨p, hp, hpP⟩ := SetLike.not_le_iff_exists.mp hb.1
  have hp0 : p ≠ 0 := fun h0 => hpP (by rw [h0]; exact Submodule.zero_mem _)
  have hpc : p ∈ cyclic A y := by rw [hcyc]; exact hp.1
  have hcoset : SameCoset hj hi := by
    by_contra hn
    have hyb : y ∈ cosetBlock A hj := by
      change y ∈ spectralPart A {γ | SameCoset hj γ}
      exact Submodule.mem_iSup_of_mem hj (Submodule.mem_iSup_of_mem (sameCoset_refl hj) hyg)
    have hcb : cyclic A y ≤ cosetBlock A hj :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hyb)
    have hpo : p ∈ otherCosets A hj := by
      change p ∈ spectralPart A {γ | ¬SameCoset hj γ}
      exact Submodule.mem_iSup_of_mem hi (Submodule.mem_iSup_of_mem hn hp.2)
    exact hp0 (Submodule.disjoint_def.mp (cosetBlock_disjoint_otherCosets A hj) p
      (hcb hpc) hpo)
  obtain ⟨z, hz⟩ := hcoset
  have hzre : (z : ℝ) < 0 := by
    have hre := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.intCast_re] at hre
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hz)
    have : (z : ℝ) ≤ 0 := by linarith
    have hz0' : (z : ℝ) ≠ 0 := by exact_mod_cast hz0
    exact lt_of_le_of_ne this hz0'
  have hdeg := cyclic_inf_gen_eq_degreeSpan hC2 A hyg z
  have hpd : p ∈ homogeneousDegreeSpan A y z := by
    rw [← hdeg]
    refine ⟨hpc, ?_⟩
    rw [← hz]; exact hp.2
  rw [hydef, hfdef] at hpd
  obtain ⟨w, hwd, hpw⟩ := degreeSpan_shift A x hj z hpd
  have hwg : w ∈ (L0 A).maxGenEigenspace hi := by
    have := homogeneousDegreeSpan_gen A hxg z hwd
    rwa [← hz] at this
  have hwP : w ∈ P := by
    by_contra hwP
    have hfw : FactorWeight A P ⊤ hi := fun hh => hwP (hh ⟨Submodule.mem_top, hwg⟩)
    have := ht.2 hi hfw
    have hre := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.intCast_re] at hre
    linarith
  have hwe := bottom_eigen hC2 A P hP hi hb hwP hwg
  apply hp0
  rw [hpw, ← hz]
  change L0 A w - hi • w = 0
  rw [hwe, sub_self]

/-- Either the extension splits, or `A` is the weak module of an ordinary module. -/
theorem exists_ordinary_or_split (hC2 : C2Cofinite W) (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P) (hQ : P ⋖ ⊤) {hi hj : ℂ} (hne : hi ≠ hj)
    (hb : FactorBottom A ⊥ P hi) (ht : FactorBottom A P ⊤ hj) :
    (∃ Q : Submodule (modeAlg A) M, IsCompl P Q) ∨
      ∃ O : OrdVModule W M, O.toWeakModule = A := by
  obtain ⟨x, hxL, hxP⟩ := exists_eigen_lift hC2 A P hP hne hb ht
  by_cases hd : Disjoint P (cyclic A x)
  · left
    apply (exists_cyclic_lift_iff_complement A P hQ hj ht).mp
    refine ⟨x, ?_, hxP, hd⟩
    apply Module.End.eigenspace_le_maxGenEigenspace
    exact Module.End.mem_eigenspace_iff.mpr hxL
  · right
    have hPle : P ≤ cyclic A x := by
      rcases hP.le_iff.mp (inf_le_left : P ⊓ cyclic A x ≤ P) with h | h
      · exact absurd (disjoint_iff.mpr h) hd
      · rw [← h]; exact inf_le_right
    have hlt : P < P ⊔ cyclic A x := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      apply hxP
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have htop : P ⊔ cyclic A x = ⊤ := not_lt_top_iff.mp (hQ.2 hlt)
    have hcyc : cyclic A x = ⊤ := by
      rw [← htop, sup_eq_right.mpr hPle]
    obtain ⟨O, hO, -⟩ := eigen_cyclic_isOrdinary hC2 A x hj hxL hcyc
    exact ⟨O, hO⟩

end VOA.Classification.COne.PlusRat2Dual
