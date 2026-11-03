import VOA.DeligneAudit.DeligneFusionSl2Module
import VOA.DeligneAudit.DeligneFusionFinite

/-!
# The Gelfand–Tsetlin filtration (Chari–Loktev §2.2) at the vector level, and part (i)

For a module with `MabRel ρ w N 0`:
* `u`-words: words in `f_θ = op 5`, `f₂ = op 4` (the abelian `u⁻ = ⟨f_θ, f₂⟩`), with index
  `idx u = ((#f_θ, #f₂), (Σ grades f_θ, Σ grades f₂))`;
* `Sub ρ w P`: the span of `g · u · w` with `g` a word in `e₁, f₁, h₁` and `P (idx u)`;
* `Higher i j`: CL's order (`ℓ` smaller lexicographically, or equal `ℓ` and `d` larger reverse-lexicographically).

Part (i) of CL Prop. 2.2.3: modulo `Sub_{>idx u}`, `u · w` is an `sl₂[t]_{α₁}`-highest-weight vector of weight
`N − ℓ₁ + ℓ₂`, hence `f₁`-polynomials applied to it reduce to box monomials (`part_i`).
-/

namespace VOA.DeligneAudit.CLFilt

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

/-! ## `sl₂` highest weight with a locally nilpotent `f` -/

section HW

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem hw_pow (E F H : V →ₗ[ℂ] V) (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x) {u : V} {lam : ℤ} (hE : E u = 0)
    (hH : H u = (lam : ℂ) • u) :
    ∀ K, F^[K] u = 0 → (lam < 0 → u = 0) ∧ (0 ≤ lam → F^[lam.toNat + 1] u = 0) := by
  intro K
  induction K with
  | zero => intro h; simp only [Function.iterate_zero, id] at h; subst h; simp
  | succ k ih =>
      intro hk
      by_cases hk' : F^[k] u = 0
      · exact ih hk'
      · have hE' := sl2_E_Fpow E F H hEF hHF u lam hE hH k
        rw [hk, map_zero] at hE'
        have hc : ((k : ℂ) + 1) * ((lam : ℂ) - k) = 0 := by
          by_contra hc; exact hk' ((smul_eq_zero.mp hE'.symm).resolve_left hc)
        have hlam : lam = k := by
          rcases mul_eq_zero.mp hc with h | h
          · exfalso; have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
            exact this h
          · exact_mod_cast sub_eq_zero.mp h
        subst hlam
        exact ⟨fun h => absurd h (by omega), fun _ => by simpa using hk⟩

end HW

/-! ## Indices, the order, and the filtration -/

/-- Index `((ℓ₁, ℓ₂), (d₁, d₂))`. -/
abbrev Idx := (ℕ × ℕ) × (ℕ × ℕ)

/-- The index of one letter. -/
def idxL (x : Fin 8 × ℕ) : Idx :=
  if x.1 = 5 then ((1, 0), (x.2, 0)) else if x.1 = 4 then ((0, 1), (0, x.2)) else 0

/-- The index of a word. -/
def idx (u : List (Fin 8 × ℕ)) : Idx := (u.map idxL).sum

theorem idx_cons (x : Fin 8 × ℕ) (u : List (Fin 8 × ℕ)) : idx (x :: u) = idxL x + idx u := by
  simp [idx]

/-- CL's order: `i` is higher than `j`. -/
def Higher (i j : Idx) : Prop :=
  i.1.1 < j.1.1 ∨ (i.1.1 = j.1.1 ∧ i.1.2 < j.1.2) ∨
    (i.1 = j.1 ∧ (j.2.2 < i.2.2 ∨ (i.2.2 = j.2.2 ∧ j.2.1 < i.2.1)))

theorem higher_add (a i j : Idx) : Higher (a + i) (a + j) ↔ Higher i j := by
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := a
  obtain ⟨⟨i1, i2⟩, i3, i4⟩ := i
  obtain ⟨⟨j1, j2⟩, j3, j4⟩ := j
  simp only [Higher, Prod.mk_add_mk, Prod.mk.injEq]
  omega

def uLetter (x : Fin 8 × ℕ) : Prop := x.1 = 4 ∨ x.1 = 5
def g1Letter (x : Fin 8 × ℕ) : Prop := x.1 = 0 ∨ x.1 = 3 ∨ x.1 = 6

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V)

/-- Pure `u`-words with index in `P`. -/
def USub (P : Idx → Prop) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ u, (∀ x ∈ u, uLetter x) ∧ P (idx u) ∧ v = wordOp ρ u w}

/-- `g · u · w` with `g` in `e₁, f₁, h₁` and `P (idx u)`. -/
def Sub (P : Idx → Prop) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ g u, (∀ x ∈ g, g1Letter x) ∧ (∀ x ∈ u, uLetter x) ∧ P (idx u) ∧
    v = wordOp ρ (g ++ u) w}

theorem USub_le_Sub (P : Idx → Prop) : USub ρ w P ≤ Sub ρ w P :=
  Submodule.span_mono fun _ ⟨u, hu, hP, hv⟩ => ⟨[], u, by simp, hu, hP, by simpa using hv⟩

theorem Sub_g1_inv (P : Idx → Prop) {x : Fin 8 × ℕ} (hx : g1Letter x) :
    Sub ρ w P ≤ (Sub ρ w P).comap (ρ.op x.1 x.2) := by
  rw [Sub, Submodule.span_le]
  rintro _ ⟨g, u, hg, hu, hP, rfl⟩
  refine Submodule.subset_span ⟨x :: g, u, ?_, hu, hP, rfl⟩
  intro y hy; rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact hg y hy

/-- A `u`-letter applied to `USub (Higher · j)` lands in `USub (Higher · (idxL x + j))`. -/
theorem USub_cons {x : Fin 8 × ℕ} (hx : uLetter x) (j : Idx) :
    USub ρ w (fun i => Higher i j) ≤ (USub ρ w (fun i => Higher i (idxL x + j))).comap (ρ.op x.1 x.2) := by
  rw [USub, Submodule.span_le]
  rintro _ ⟨u, hu, hP, rfl⟩
  refine Submodule.subset_span ⟨x :: u, ?_, ?_, rfl⟩
  · intro y hy; rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hu y hy
  · show Higher (idx (x :: u)) (idxL x + j)
    rw [idx_cons, higher_add]; exact hP

theorem higher_letters {a b j : Idx} (h : Higher a b) : Higher (a + j) (b + j) := by
  rw [add_comm a, add_comm b, higher_add]; exact h

theorem mem_USub_letter {x : Fin 8 × ℕ} (hx : uLetter x) {u : List (Fin 8 × ℕ)}
    (hu : ∀ y ∈ u, uLetter y) {P : Idx → Prop} (hP : P (idx (x :: u))) :
    ρ.op x.1 x.2 (wordOp ρ u w) ∈ USub ρ w P := by
  refine Submodule.subset_span ⟨x :: u, ?_, hP, rfl⟩
  intro y hy; rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact hu y hy

/-- CL Lemma 3.2.1 (ii) for `e₁ ⊗ tᵏ`. -/
theorem e1_USub (k : ℕ) (hw : ρ.op 0 k w = 0) :
    ∀ u : List (Fin 8 × ℕ), (∀ x ∈ u, uLetter x) →
      ρ.op 0 k (wordOp ρ u w) ∈ USub ρ w (fun i => Higher i (idx u))
  | [], _ => by simp [wordOp, hw]
  | (x :: u), hu => by
      have hx := hu x List.mem_cons_self
      have hu' : ∀ y ∈ u, uLetter y := fun y hy => hu y (List.mem_cons_of_mem _ hy)
      change ρ.op 0 k (ρ.op x.1 x.2 (wordOp ρ u w)) ∈ _
      rw [comm_apply 0 x.1 k x.2]
      refine Submodule.add_mem _ ?_ ?_
      · have := USub_cons ρ w hx (idx u) (e1_USub k hw u hu')
        rwa [← idx_cons] at this
      · rcases hx with h4 | h5
        · rw [h4]; simp [Fin.sum_univ_eight, bracketTable]
        · rw [h5]
          simp only [Fin.sum_univ_eight, bracketTable]
          simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero,
            zero_add, neg_smul, one_smul]
          refine Submodule.neg_mem _ ?_
          refine mem_USub_letter ρ w (x := ((4 : Fin 8), k + x.2)) (Or.inl rfl) hu' ?_
          show Higher (idx (((4 : Fin 8), k + x.2) :: u)) (idx (x :: u))
          rw [idx_cons, idx_cons]
          apply higher_letters
          simp [idxL, h5, Higher]

/-- CL Lemma 3.2.1 (ii) for `h₁ ⊗ tᵏ`, `k ≥ 1`. -/
theorem h1_USub (k : ℕ) (hk : 1 ≤ k) (hw : ρ.op 6 k w = 0) :
    ∀ u : List (Fin 8 × ℕ), (∀ x ∈ u, uLetter x) →
      ρ.op 6 k (wordOp ρ u w) ∈ USub ρ w (fun i => Higher i (idx u))
  | [], _ => by simp [wordOp, hw]
  | (x :: u), hu => by
      have hx := hu x List.mem_cons_self
      have hu' : ∀ y ∈ u, uLetter y := fun y hy => hu y (List.mem_cons_of_mem _ hy)
      change ρ.op 6 k (ρ.op x.1 x.2 (wordOp ρ u w)) ∈ _
      rw [comm_apply 6 x.1 k x.2]
      refine Submodule.add_mem _ ?_ ?_
      · have := USub_cons ρ w hx (idx u) (h1_USub k hk hw u hu')
        rwa [← idx_cons] at this
      · rcases hx with h4 | h5
        · rw [h4]
          simp only [Fin.sum_univ_eight, bracketTable]
          simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero,
            zero_add, one_smul]
          refine mem_USub_letter ρ w (x := ((4 : Fin 8), k + x.2)) (Or.inl rfl) hu' ?_
          show Higher (idx (((4 : Fin 8), k + x.2) :: u)) (idx (x :: u))
          rw [idx_cons, idx_cons]
          apply higher_letters
          simp [idxL, h4, Higher]; omega
        · rw [h5]
          simp only [Fin.sum_univ_eight, bracketTable]
          simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero,
            zero_add, neg_smul, one_smul]
          refine Submodule.neg_mem _ ?_
          refine mem_USub_letter ρ w (x := ((5 : Fin 8), k + x.2)) (Or.inr rfl) hu' ?_
          show Higher (idx (((5 : Fin 8), k + x.2) :: u)) (idx (x :: u))
          rw [idx_cons, idx_cons]
          apply higher_letters
          simp [idxL, h5, Higher]; omega

/-- CL Lemma 3.2.1 (ii) for `h₁ ⊗ 1`: the weight `N − ℓ₁ + ℓ₂`. -/
theorem h1_zero_word (N : ℂ) (hw : ρ.op 6 0 w = N • w) :
    ∀ u : List (Fin 8 × ℕ), (∀ x ∈ u, uLetter x) →
      ρ.op 6 0 (wordOp ρ u w) = (N - (idx u).1.1 + (idx u).1.2) • wordOp ρ u w
  | [], _ => by simp [wordOp, hw, idx]
  | (x :: u), hu => by
      have hx := hu x List.mem_cons_self
      have hu' : ∀ y ∈ u, uLetter y := fun y hy => hu y (List.mem_cons_of_mem _ hy)
      change ρ.op 6 0 (ρ.op x.1 x.2 (wordOp ρ u w)) = _ • ρ.op x.1 x.2 (wordOp ρ u w)
      rw [comm_apply 6 x.1 0 x.2, h1_zero_word N hw u hu', map_smul, idx_cons]
      rcases hx with h4 | h5
      · rw [h4]
        simp only [Fin.sum_univ_eight, bracketTable]
        simp [idxL, h4]; module
      · rw [h5]
        simp only [Fin.sum_univ_eight, bracketTable]
        simp [idxL, h5]; module

/-! ## Part (i) via the quotient by the higher filtration -/

open VOA.DeligneAudit.Sl2Weyl in
/-- Evaluation commutes with a quotient map. -/
theorem evAlg_mkQ {W : Type*} [AddCommGroup W] [Module ℂ W] (F : ℕ → Module.End ℂ W)
    (hFF : ∀ i j, F i * F j = F j * F i) (S : Submodule ℂ W) (hS : ∀ i, S ≤ S.comap (F i))
    (hFF' : ∀ i j, S.mapQ S (F i) (hS i) * S.mapQ S (F j) (hS j) =
      S.mapQ S (F j) (hS j) * S.mapQ S (F i) (hS i)) (p : R) (y : W) :
    Sl2Weyl.evAlg (fun i => S.mapQ S (F i) (hS i)) hFF' p (S.mkQ y) = S.mkQ (Sl2Weyl.evAlg F hFF p y) := by
  induction p using MvPolynomial.induction_on generalizing y with
  | C a =>
      rw [MvPolynomial.C_eq_smul_one, map_smul, map_one, map_smul, map_one]
      simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X p i hp =>
      have h1 : Sl2Weyl.evAlg (fun i => S.mapQ S (F i) (hS i)) hFF' (MvPolynomial.X i) = S.mapQ S (F i) (hS i) :=
        Sl2Weyl.evAlg_z _ _ i
      have h2 : Sl2Weyl.evAlg F hFF (MvPolynomial.X i) = F i := Sl2Weyl.evAlg_z _ _ i
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1, h2, Submodule.mkQ_apply,
        Submodule.mapQ_apply, ← Submodule.mkQ_apply, hp]

theorem f1_comm (i j : ℕ) : ρ.op 3 i * ρ.op 3 j = ρ.op 3 j * ρ.op 3 i := by
  ext v
  simp only [Module.End.mul_apply]
  rw [comm_apply 3 3 i j]; simp [Fin.sum_univ_eight, bracketTable]

open VOA.DeligneAudit.Sl2Weyl in
/-- **CL Prop. 2.2.3 (i), vector level**: for a `u`-word `u` (index `((ℓ₁,ℓ₂),·)`), every
`f₁`-polynomial applied to `u·w` lies in the span of the `f₁`-box monomials (box size
`N − ℓ₁ + ℓ₂`) applied to `u·w`, modulo the strictly higher filtration. -/
theorem part_i {N : ℕ} (h : MabRel ρ w N 0) (u : List (Fin 8 × ℕ)) (hu : ∀ x ∈ u, uLetter x)
    (p : R) :
    Sl2Weyl.evAlg (fun k => ρ.op 3 k) (f1_comm ρ) p (wordOp ρ u w) ∈
      Submodule.span ℂ {v | ∃ f, BoxP ((N : ℤ) - (idx u).1.1 + (idx u).1.2).toNat f ∧
          v = Sl2Weyl.evAlg (fun k => ρ.op 3 k) (f1_comm ρ) (MvPolynomial.monomial f 1) (wordOp ρ u w)} ⊔
        Sub ρ w (fun i => Higher i (idx u)) := by
  set y := wordOp ρ u w with hy
  set S := Sub ρ w (fun i => Higher i (idx u)) with hSdef
  have inv : ∀ (c : Fin 8) k, g1Letter (c, k) → S ≤ S.comap (ρ.op c k) :=
    fun c k hc => Sub_g1_inv ρ w _ (x := (c, k)) hc
  let FQ : ℕ → Module.End ℂ (V ⧸ S) := fun k => S.mapQ S (ρ.op 3 k) (inv 3 k (Or.inr (Or.inl rfl)))
  let HQ : ℕ → Module.End ℂ (V ⧸ S) := fun k => S.mapQ S (ρ.op 6 k) (inv 6 k (Or.inr (Or.inr rfl)))
  let EQ : ℕ → Module.End ℂ (V ⧸ S) := fun k => S.mapQ S (ρ.op 0 k) (inv 0 k (Or.inl rfl))
  -- relations in the quotient, from those in `V`
  have qext : ∀ (A B : Module.End ℂ (V ⧸ S)), (∀ v, A (S.mkQ v) = B (S.mkQ v)) → A = B := by
    intro A B hAB; ext v; exact hAB v
  have hFFQ : ∀ i j, FQ i * FQ j = FQ j * FQ i := by
    intro i j; refine qext _ _ fun v => ?_
    simp only [Module.End.mul_apply, FQ, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [← Module.End.mul_apply (ρ.op 3 i), f1_comm, Module.End.mul_apply]
  have hEF : ∀ k, EQ 1 * FQ k - FQ k * EQ 1 = HQ (k + 1) := by
    intro k; refine qext _ _ fun v => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, FQ, EQ, HQ, Submodule.mkQ_apply,
      Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
    congr 1
    rw [ρ.comm 0 3 1 k v]; simp [Fin.sum_univ_eight, bracketTable, add_comm 1 k]
  have hHF : ∀ m k, HQ (m + 1) * FQ k - FQ k * HQ (m + 1) = (-2 : ℂ) • FQ (m + 1 + k) := by
    intro m k; refine qext _ _ fun v => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, FQ, HQ,
      Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [ρ.comm 6 3 (m + 1) k v]; simp [Fin.sum_univ_eight, bracketTable]
  have hEF0 : ∀ x, EQ 0 (FQ 0 x) - FQ 0 (EQ 0 x) = HQ 0 x := by
    intro x; obtain ⟨v, rfl⟩ := S.mkQ_surjective x
    simp only [FQ, EQ, HQ, Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
    congr 1
    rw [ρ.comm 0 3 0 0 v]; simp [Fin.sum_univ_eight, bracketTable]
  have hHF0 : ∀ x, HQ 0 (FQ 0 x) - FQ 0 (HQ 0 x) = (-2 : ℂ) • FQ 0 x := by
    intro x; obtain ⟨v, rfl⟩ := S.mkQ_surjective x
    simp only [FQ, HQ, Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub,
      ← Submodule.Quotient.mk_smul]
    congr 1
    rw [ρ.comm 6 3 0 0 v]; simp [Fin.sum_univ_eight, bracketTable]
  -- the class of `y`
  have memS : ∀ v, v ∈ USub ρ w (fun i => Higher i (idx u)) → S.mkQ v = 0 := fun v hv =>
    (Submodule.Quotient.mk_eq_zero S).mpr (USub_le_Sub ρ w _ hv)
  have hE1 : EQ 1 (S.mkQ y) = 0 := by
    simp only [EQ, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact memS _ (e1_USub ρ w 1 (h.raising 0 (by decide) 1) u hu)
  have hE0 : EQ 0 (S.mkQ y) = 0 := by
    simp only [EQ, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact memS _ (e1_USub ρ w 0 (h.raising 0 (by decide) 0) u hu)
  have hH : ∀ m, HQ (m + 1) (S.mkQ y) = 0 := by
    intro m
    simp only [HQ, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact memS _ (h1_USub ρ w (m + 1) (by omega) (h.cartan_pos 6 (by decide) (m + 1) (by omega)) u hu)
  set lam : ℤ := (N : ℤ) - (idx u).1.1 + (idx u).1.2 with hlam
  have hH0 : HQ 0 (S.mkQ y) = (lam : ℂ) • S.mkQ y := by
    simp only [HQ, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [h1_zero_word ρ w (N : ℂ) (by simpa using h.cartan_zero 6 (by decide)) u hu]
    rw [← Submodule.Quotient.mk_smul, hlam]; push_cast; rfl
  -- local nilpotency of `f₁`
  have hw3 : (ρ.op 3 0 ^ (N + 1)) w = 0 := by
    rw [Module.End.pow_apply]; simpa using h.lowering_f1
  have hnilV := pow_kill_wordOp (ρ := ρ) 3 (by decide) hw3 u
  have hiter : ∀ K (v : V), (FQ 0)^[K] (S.mkQ v) = S.mkQ ((ρ.op 3 0)^[K] v) := by
    intro K; induction K with
    | zero => intro v; rfl
    | succ K ih => intro v; rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl
  have hnil : (FQ 0)^[2 * u.length + (N + 1)] (S.mkQ y) = 0 := by
    rw [hiter, ← Module.End.pow_apply, hnilV, map_zero]
  obtain ⟨hneg, hpos⟩ := hw_pow (EQ 0) (FQ 0) (HQ 0) hEF0 hHF0 hE0 hH0 _ hnil
  -- conclusion
  have key := evAlg_mkQ (fun k => ρ.op 3 k) (f1_comm ρ) S (fun k => inv 3 k (Or.inr (Or.inl rfl))) hFFQ p y
  by_cases hl : lam < 0
  · refine Submodule.mem_sup_right ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← key, hneg hl, map_zero]
  · have hN : (FQ 0 ^ (lam.toNat + 1)) (S.mkQ y) = 0 := by
      rw [Module.End.pow_apply]; exact hpos (by omega)
    have hsp := weyl_span_box FQ hFFQ hEF hHF hE1 hH lam.toNat hN p
    rw [key] at hsp
    have : S.mkQ (Sl2Weyl.evAlg (fun k => ρ.op 3 k) (f1_comm ρ) p y) ∈
        (Submodule.span ℂ {v | ∃ f, BoxP lam.toNat f ∧
          v = Sl2Weyl.evAlg (fun k => ρ.op 3 k) (f1_comm ρ) (MvPolynomial.monomial f 1) y}).map S.mkQ := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_ hsp
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, hf, rfl⟩, (evAlg_mkQ (fun k => ρ.op 3 k) (f1_comm ρ) S
        (fun k => inv 3 k (Or.inr (Or.inl rfl))) hFFQ _ y).symm⟩
    rw [← Submodule.mem_comap, Submodule.comap_map_mkQ] at this
    rw [sup_comm] at this
    exact this

/-! ## The `α₂` part is reduced exactly -/

theorem f2_comm (i j : ℕ) : ρ.op 4 i * ρ.op 4 j = ρ.op 4 j * ρ.op 4 i := by
  ext v
  simp only [Module.End.mul_apply]
  rw [comm_apply 4 4 i j]; simp [Fin.sum_univ_eight, bracketTable]

open VOA.DeligneAudit.Sl2Weyl in
/-- **The `α₂`-box**: a bihomogeneous `f₂`-polynomial applied to `w` is a combination of
`f₂`-box monomials (box `N`) of the same bidegree applied to `w` — exactly, in `V`. -/
theorem alpha2_box {N : ℕ} (h : MabRel ρ w N 0) {p : R} {n : ℕ × ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous om p n) :
    Sl2Weyl.evAlg (fun k => ρ.op 4 k) (f2_comm ρ) p w ∈
      Submodule.span ℂ {v | ∃ f, BoxP N f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg (fun k => ρ.op 4 k) (f2_comm ρ) (MvPolynomial.monomial f 1) w} := by
  refine weyl_span_box_graded (fun k => ρ.op 4 k) (f2_comm ρ) (E1 := ρ.op 1 1)
    (H := fun k => ρ.op 7 k) ?_ ?_ (h.raising 1 (by decide) 1)
    (fun m => h.cartan_pos 7 (by decide) (m + 1) (by omega)) N ?_ hp
  · intro k; ext v; simp only [LinearMap.sub_apply, Module.End.mul_apply]
    rw [ρ.comm 1 4 1 k v]; simp [Fin.sum_univ_eight, bracketTable, add_comm 1 k]
  · intro m k; ext v; simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [ρ.comm 7 4 (m + 1) k v]; simp [Fin.sum_univ_eight, bracketTable]
  · rw [Module.End.pow_apply]; simpa using h.lowering_f2

end

end VOA.DeligneAudit.CLFilt


section AxiomAudit
#print axioms VOA.DeligneAudit.CLFilt.part_i
end AxiomAudit
