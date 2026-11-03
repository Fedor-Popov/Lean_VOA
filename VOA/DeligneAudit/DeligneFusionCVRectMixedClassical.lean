import VOA.DeligneAudit.DeligneFusionCVRectSingle

/-!
# Classical straightening for mixed rectangular branching

This module extracts the actual Heisenberg straightening used in the
Gelfand--Tsetlin argument from its equal-weight presentation. Only the first
simple-root zero-mode nilpotence is needed. No second weight, current-degree
bound, fusion identification, or branching hypothesis enters the theorem.
-/

namespace VOA.DeligneAudit.A2.CVRectMixedClassical

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CLGT
open VOA.DeligneAudit.CLNormal VOA.DeligneAudit.CLFilt

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Every zero-mode normal word can be straightened until its highest-root
exponent is bounded by the first simple-root highest weight. The proof is
triangular normal ordering, with its nonzero coefficient explicitly canceled. -/
theorem theta_length_of_first_nil {N : ℕ}
    (hNil : (ρ.op 3 0 ^ (N + 1)) w = 0) :
    ∀ C p q, C ≤ p → C ≤ q →
      Mv ρ w p q C ∈ Submodule.span ℂ {v | ∃ C', C' ≤ N ∧ C' ≤ p ∧ C' ≤ q ∧ v = Mv ρ w p q C'} := by
  intro C
  induction C using Nat.strong_induction_on with
  | _ C ih =>
  intro p q hp hq
  by_cases hC : C ≤ N
  · exact Submodule.subset_span ⟨C, hC, hp, hq, rfl⟩
  set X := ρ.op 3 0
  set Y := ρ.op 4 0
  set Z := ρ.op 5 0
  set c := C - N - 1
  set a := p - C
  set b := q - c
  have hrel : (X ^ a * Z ^ c * (Y ^ b * X ^ (N + 1))) w = 0 := by
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]
    change (X ^ a) ((Z ^ c) ((Y ^ b) ((ρ.op 3 0 ^ (N + 1)) w))) = 0
    rw [hNil]
    simp
  have hno := normal_order (f2f1 ρ) (f1fθ ρ) (f2fθ ρ) (N + 1) b (by omega)
  set s := Y ^ b * X ^ (N + 1) - ((b.descFactorial (N + 1) : ℕ) : ℂ) • (Z ^ (N + 1) * Y ^ (b - (N + 1)))
  have hsplit : Y ^ b * X ^ (N + 1) =
      ((b.descFactorial (N + 1) : ℕ) : ℂ) • (Z ^ (N + 1) * Y ^ (b - (N + 1))) + s := by
    simp only [s]; abel
  have hZX : ∀ i k, Z ^ i * X ^ k = X ^ k * Z ^ i := fun i k =>
    ((Commute.pow_pow (show Commute X Z from f1fθ ρ) k i).eq).symm
  -- the top term is `M(C)`
  have htop : (X ^ a * Z ^ c * (Z ^ (N + 1) * Y ^ (b - (N + 1)))) w = Mv ρ w p q C := by
    simp only [Mv, X, Y, Z]
    rw [show b - (N + 1) = q - C by omega, ← mul_assoc, mul_assoc (X ^ a) (Z ^ c), ← pow_add,
      show c + (N + 1) = C by omega]
  -- the lower terms
  have hlow : (X ^ a * Z ^ c * s) w ∈
      Submodule.span ℂ {v | ∃ C', C' ≤ N ∧ C' ≤ p ∧ C' ≤ q ∧ v = Mv ρ w p q C'} := by
    have : ∀ T ∈ Tsp X Y Z (N + 1) b, (X ^ a * Z ^ c * T) w ∈
        Submodule.span ℂ {v | ∃ C', C' ≤ N ∧ C' ≤ p ∧ C' ≤ q ∧ v = Mv ρ w p q C'} := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
          obtain ⟨i, hi, rfl⟩ := hT
          have := ih (c + i) (by omega) p q (by omega) (by omega)
          convert this using 1
          simp only [Mv, X, Y, Z]
          rw [show q - (c + i) = b - i by omega, show p - (c + i) = a + (N + 1 - i) by omega]
          simp only [← mul_assoc]
          rw [mul_assoc (X ^ a) (Z ^ c), hZX, ← mul_assoc, ← pow_add, mul_assoc _ (Z ^ c), ← pow_add]
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx => rw [mul_smul_comm, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hx
    exact this s hno
  rw [hsplit, mul_add, mul_smul_comm, LinearMap.add_apply, LinearMap.smul_apply, htop] at hrel
  have hκ : ((b.descFactorial (N + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  have : Mv ρ w p q C = -(((b.descFactorial (N + 1) : ℕ) : ℂ))⁻¹ • (X ^ a * Z ^ c * s) w := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, ← smul_eq_zero_iff_right hκ, smul_add, smul_smul,
      mul_inv_cancel₀ hκ, one_smul]
    exact hrel
  rw [this]
  exact Submodule.smul_mem _ _ hlow

/-- The commuting outer block for branching to the first simple root. -/
def outer (b c : ℕ) : V := (ρ.op 5 0 ^ b) ((ρ.op 4 0 ^ c) w)

def outerWord (b c : ℕ) : List (Fin 8 × ℕ) :=
  List.replicate b (5, 0) ++ List.replicate c (4, 0)

theorem outerWord_eval (b c : ℕ) : wordOp ρ (outerWord b c) w = outer ρ w b c := by
  rw [outerWord, wordOp_append, ← iterate_eq_wordOp ρ (5, 0),
    ← iterate_eq_wordOp ρ (4, 0), ← Module.End.pow_apply, ← Module.End.pow_apply]
  rfl

theorem outerWord_letters (b c : ℕ) : ∀ x ∈ outerWord b c, uLetter x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hx' := List.eq_of_mem_replicate hx
    subst x
    exact Or.inr rfl
  · have hx' := List.eq_of_mem_replicate hx
    subst x
    exact Or.inl rfl

theorem outerWord_index (b c : ℕ) : idx (outerWord b c) = ((b, c), (0, 0)) := by
  simp [outerWord, idx, idxL, Prod.smul_mk, nsmul_eq_mul]

/-- The first-simple-root words, all in current degree zero. -/
def firstWord (g : List (Fin 8 × ℕ)) : Prop :=
  ∀ x ∈ g, x = (0, 0) ∨ x = (3, 0) ∨ x = (6, 0)

/-- The genuine lower outer-block filtration. Its generators include whole
first-root orbits, so invariance does not assume a branching statement. -/
def prior (r : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ (g : List (Fin 8 × ℕ)) (b c : ℕ),
    b < r ∧ firstWord g ∧ v = wordOp ρ g (outer ρ w b c)}

theorem outer_mem_prior (r b c : ℕ) (hb : b < r) : outer ρ w b c ∈ prior ρ w r :=
  Submodule.subset_span ⟨[], b, c, hb, by simp [firstWord], rfl⟩

theorem prior_inv (r : ℕ) (d : Fin 8) (hd : d = 0 ∨ d = 3 ∨ d = 6) :
    prior ρ w r ≤ (prior ρ w r).comap (ρ.op d 0) := by
  rw [prior, Submodule.span_le]
  rintro _ ⟨g, b, c, hb, hg, rfl⟩
  refine Submodule.subset_span ⟨(d, 0) :: g, b, c, hb, ?_, rfl⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases hd with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact hg x hx

theorem first_outer_raise (hE : ρ.op 0 0 w = 0) (b c : ℕ) :
    ρ.op 0 0 (outer ρ w b c) ∈ prior ρ w b := by
  have hEv : ρ.op 0 0 ((ρ.op 4 0 ^ c) w) = 0 := by
    have hc := (show Commute (ρ.op 0 0) (ρ.op 4 0) from c_e1f4 ρ 0 0).pow_right c
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hE, map_zero]
  cases b with
  | zero =>
      change ρ.op 0 0 ((ρ.op 4 0 ^ c) w) ∈ prior ρ w 0
      rw [hEv]
      exact Submodule.zero_mem _
  | succ b =>
      have hcomm : ρ.op 0 0 * ρ.op 5 0 - ρ.op 5 0 * ρ.op 0 0 = -ρ.op 4 0 := by
        rw [c_e1f5]
        simp
      have hZ : ρ.op 5 0 * -ρ.op 4 0 = -ρ.op 4 0 * ρ.op 5 0 := by
        rw [mul_neg, neg_mul, ← c_f4f5 ρ 0 0]
      have hh := congrArg (fun T : Module.End ℂ V => T ((ρ.op 4 0 ^ c) w))
        (CVPolarization.power_mul_operator hcomm hZ b)
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        hEv, map_zero] at hh
      have he : ρ.op 0 0 (outer ρ w (b + 1) c) =
          (b + 1) • ((-ρ.op 4 0) ((ρ.op 5 0 ^ b) ((ρ.op 4 0 ^ c) w))) :=
        sub_eq_zero.mp hh.symm
      rw [he, LinearMap.neg_apply]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
      apply Submodule.smul_mem
      apply Submodule.neg_mem
      have hc := (show Commute (ρ.op 4 0) (ρ.op 5 0) from c_f4f5 ρ 0 0).pow_right b
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply,
        ← Module.End.mul_apply (ρ.op 4 0), ← pow_succ']
      exact outer_mem_prior ρ w (b + 1) b (c + 1) (by omega)

theorem first_outer_weight {m : ℕ} (hH : ρ.op 6 0 w = (m : ℂ) • w) (b c : ℕ) :
    ρ.op 6 0 (outer ρ w b c) = ((m : ℂ) - b + c) • outer ρ w b c := by
  have hh := h1_zero_word ρ w (m : ℂ) hH (outerWord b c) (outerWord_letters b c)
  simpa only [outerWord_eval, outerWord_index] using hh

/-- The actual first-root string on an outer vector is sharp modulo lower
outer blocks. All quotient highest-weight and nilpotence facts are derived
from source relations, with no branching or finite-dimensionality premise. -/
theorem first_string_mod_prior {m : ℕ} (hE : ρ.op 0 0 w = 0)
    (hH : ρ.op 6 0 w = (m : ℂ) • w) (hNil : (ρ.op 3 0 ^ (m + 1)) w = 0)
    (b c : ℕ) (hb : b ≤ m) :
    (ρ.op 3 0 ^ (m - b + c + 1)) (outer ρ w b c) ∈ prior ρ w b := by
  let S := prior ρ w b
  let E := S.mapQ S (ρ.op 0 0) (prior_inv ρ w b 0 (Or.inl rfl))
  let F := S.mapQ S (ρ.op 3 0) (prior_inv ρ w b 3 (Or.inr (Or.inl rfl)))
  let H := S.mapQ S (ρ.op 6 0) (prior_inv ρ w b 6 (Or.inr (Or.inr rfl)))
  have hEF : ∀ x, E (F x) - F (E x) = H x := by
    intro x
    obtain ⟨v, rfl⟩ := S.mkQ_surjective x
    simp only [E, F, H, Submodule.mkQ_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub]
    congr 1
    rw [ρ.comm 0 3 0 0 v]
    simp [Fin.sum_univ_eight, bracketTable]
  have hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x := by
    intro x
    obtain ⟨v, rfl⟩ := S.mkQ_surjective x
    simp only [F, H, Submodule.mkQ_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [ρ.comm 6 3 0 0 v]
    simp [Fin.sum_univ_eight, bracketTable]
  have hEu : E (S.mkQ (outer ρ w b c)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr (first_outer_raise ρ w hE b c)
  have hHu : H (S.mkQ (outer ρ w b c)) =
      (((m : ℤ) - b + c : ℤ) : ℂ) • S.mkQ (outer ρ w b c) := by
    change S.mkQ (ρ.op 6 0 (outer ρ w b c)) = _
    rw [first_outer_weight ρ w hH, map_smul]
    push_cast
    rfl
  have hiter : ∀ K (v : V), F^[K] (S.mkQ v) = S.mkQ ((ρ.op 3 0)^[K] v) := by
    intro K
    induction K with
    | zero => intro v; rfl
    | succ K ih =>
        intro v
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        rfl
  have hN := pow_kill_wordOp (ρ := ρ) 3 (by decide) hNil (outerWord b c)
  rw [outerWord_eval] at hN
  have hnu : F^[2 * (outerWord b c).length + (m + 1)]
      (S.mkQ (outer ρ w b c)) = 0 := by
    rw [hiter, ← Module.End.pow_apply, hN, map_zero]
  have hsharp := (hw_pow E F H hEF hHF hEu hHu _ hnu).2 (by omega)
  have hi : ((m : ℤ) - b + c).toNat = m - b + c := by omega
  rw [hi, hiter, ← Module.End.pow_apply] at hsharp
  exact (Submodule.Quotient.mk_eq_zero _).mp hsharp

/-- A finite zero-mode simple-root string. -/
def rootString (F : Module.End ℂ V) (u : V) (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ a : ℕ, a ≤ m ∧ v = F^[a] u}

theorem rootString_self (F : Module.End ℂ V) (u : V) (m : ℕ) :
    u ∈ rootString F u m := Submodule.subset_span ⟨0, by omega, rfl⟩

theorem rootString_inv (E F H : Module.End ℂ V) (u : V) (m : ℕ)
    (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (hEu : E u = 0) (hHu : H u = (m : ℂ) • u) (hNu : F^[m + 1] u = 0) :
    (rootString F u m ≤ (rootString F u m).comap E) ∧
      (rootString F u m ≤ (rootString F u m).comap F) ∧
      (rootString F u m ≤ (rootString F u m).comap H) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [rootString, Submodule.span_le] <;>
    rintro _ ⟨a, ha, rfl⟩
  · change E (F^[a] u) ∈ rootString F u m
    cases a with
    | zero => rw [Function.iterate_zero, id, hEu]; exact Submodule.zero_mem _
    | succ a =>
        rw [sl2_E_Fpow E F H hEF hHF u (m : ℂ) hEu hHu a]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, by omega, rfl⟩)
  · change F (F^[a] u) ∈ rootString F u m
    rw [← Function.iterate_succ_apply' F a]
    by_cases ham : a < m
    · exact Submodule.subset_span ⟨a + 1, by omega, rfl⟩
    · have he : a = m := by omega
      rw [he, hNu]
      exact Submodule.zero_mem _
  · change H (F^[a] u) ∈ rootString F u m
    rw [sl2_H_Fpow F H hHF u (m : ℂ) hHu a]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

/-- Every actual first-root word on an outer generator is spanned by the sharp
finite string, modulo strictly lower outer blocks. -/
theorem first_word_spanning_mod_prior {m : ℕ} (hE : ρ.op 0 0 w = 0)
    (hH : ρ.op 6 0 w = (m : ℂ) • w) (hNil : (ρ.op 3 0 ^ (m + 1)) w = 0)
    (b c : ℕ) (hb : b ≤ m) (g : List (Fin 8 × ℕ)) (hg : firstWord g) :
    wordOp ρ g (outer ρ w b c) ∈
      (Submodule.span ℂ {v | ∃ a : ℕ, a ≤ m - b + c ∧
        v = (ρ.op 3 0)^[a] (outer ρ w b c)}) ⊔ prior ρ w b := by
  let S := prior ρ w b
  let E := S.mapQ S (ρ.op 0 0) (prior_inv ρ w b 0 (Or.inl rfl))
  let F := S.mapQ S (ρ.op 3 0) (prior_inv ρ w b 3 (Or.inr (Or.inl rfl)))
  let H := S.mapQ S (ρ.op 6 0) (prior_inv ρ w b 6 (Or.inr (Or.inr rfl)))
  let u := S.mkQ (outer ρ w b c)
  have hEF : ∀ x, E (F x) - F (E x) = H x := by
    intro x
    obtain ⟨v, rfl⟩ := S.mkQ_surjective x
    simp only [E, F, H, Submodule.mkQ_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub]
    congr 1
    rw [ρ.comm 0 3 0 0 v]
    simp [Fin.sum_univ_eight, bracketTable]
  have hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x := by
    intro x
    obtain ⟨v, rfl⟩ := S.mkQ_surjective x
    simp only [F, H, Submodule.mkQ_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [ρ.comm 6 3 0 0 v]
    simp [Fin.sum_univ_eight, bracketTable]
  have hEu : E u = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (first_outer_raise ρ w hE b c)
  have hHu : H u = ((m - b + c : ℕ) : ℂ) • u := by
    change S.mkQ (ρ.op 6 0 (outer ρ w b c)) = _
    rw [first_outer_weight ρ w hH, map_smul, Nat.cast_add, Nat.cast_sub hb]
  have hiter : ∀ a (v : V), F^[a] (S.mkQ v) = S.mkQ ((ρ.op 3 0)^[a] v) := by
    intro a
    induction a with
    | zero => intro v; rfl
    | succ a ih =>
        intro v
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        rfl
  have hNu : F^[m - b + c + 1] u = 0 := by
    rw [show u = S.mkQ (outer ρ w b c) from rfl, hiter, ← Module.End.pow_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (first_string_mod_prior ρ w hE hH hNil b c hb)
  have hinv := rootString_inv E F H u (m - b + c) hEF hHF hEu hHu hNu
  have hword : ∀ g : List (Fin 8 × ℕ), firstWord g →
      S.mkQ (wordOp ρ g (outer ρ w b c)) ∈ rootString F u (m - b + c) := by
    intro g
    induction g with
    | nil => intro _; exact rootString_self F u _
    | cons x g ih =>
        intro hg
        have hi := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy))
        rcases hg x List.mem_cons_self with rfl | rfl | rfl
        · exact hinv.1 hi
        · exact hinv.2.1 hi
        · exact hinv.2.2 hi
  let T : Submodule ℂ V := Submodule.span ℂ {v | ∃ a : ℕ,
    a ≤ m - b + c ∧ v = (ρ.op 3 0)^[a] (outer ρ w b c)}
  have hmap : rootString F u (m - b + c) ≤ T.map S.mkQ := by
    rw [rootString, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨(ρ.op 3 0)^[a] (outer ρ w b c), Submodule.subset_span ⟨a, ha, rfl⟩,
      (hiter a (outer ρ w b c)).symm⟩
  have hv := hmap (hword g hg)
  change wordOp ρ g (outer ρ w b c) ∈ (T.map S.mkQ).comap S.mkQ at hv
  rw [Submodule.comap_map_mkQ] at hv
  exact (sup_comm S T) ▸ hv

/-- The classical branching indices: one outer choice and its first-root string. -/
abbrev ClassicalIndex (m n : ℕ) :=
  {i : Fin (m + 1) × Fin (n + 1) × Fin (m + n + 1) //
    i.2.2.val ≤ m - i.1.val + i.2.1.val}

def classicalWord (m n : ℕ) (i : ClassicalIndex m n) : V :=
  (ρ.op 3 0)^[i.1.2.2.val] (outer ρ w i.1.1.val i.1.2.1.val)

def classicalSpan (m n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (classicalWord ρ w m n))

theorem classicalWord_mem (m n a b c : ℕ) (hb : b ≤ m) (hc : c ≤ n)
    (ha : a ≤ m - b + c) :
    (ρ.op 3 0)^[a] (outer ρ w b c) ∈ classicalSpan ρ w m n := by
  exact Submodule.subset_span
    ⟨⟨(⟨b, by omega⟩, ⟨c, by omega⟩, ⟨a, by omega⟩), ha⟩, rfl⟩

theorem prior_mono {r s : ℕ} (hrs : r ≤ s) : prior ρ w r ≤ prior ρ w s := by
  apply Submodule.span_mono
  rintro _ ⟨g, b, c, hb, hg, rfl⟩
  exact ⟨g, b, c, by omega, hg, rfl⟩

/-- The actual lower filtration is absorbed by the finite classical family,
using the proved first-root strings and the source second-root nilpotence. -/
theorem prior_le_classicalSpan {m n : ℕ} (hE : ρ.op 0 0 w = 0)
    (hH : ρ.op 6 0 w = (m : ℂ) • w) (hNil : (ρ.op 3 0 ^ (m + 1)) w = 0)
    (hNil2 : (ρ.op 4 0 ^ (n + 1)) w = 0) :
    ∀ r : ℕ, r ≤ m + 1 → prior ρ w r ≤ classicalSpan ρ w m n := by
  intro r
  induction r with
  | zero =>
      intro _
      rw [prior, Submodule.span_le]
      rintro _ ⟨g, b, c, hb, _, _⟩
      omega
  | succ r ih =>
      intro hr
      have hi := ih (by omega)
      rw [prior, Submodule.span_le]
      rintro _ ⟨g, b, c, hb, hg, rfl⟩
      by_cases hc : c ≤ n
      · have hbm : b ≤ m := by omega
        have hv := first_word_spanning_mod_prior ρ w hE hH hNil b c hbm g hg
        have hle :
            (Submodule.span ℂ {v | ∃ a : ℕ, a ≤ m - b + c ∧
              v = (ρ.op 3 0)^[a] (outer ρ w b c)}) ⊔ prior ρ w b ≤
                classicalSpan ρ w m n := by
          apply sup_le
          · rw [Submodule.span_le]
            rintro _ ⟨a, ha, rfl⟩
            exact classicalWord_mem ρ w m n a b c hbm hc ha
          · exact (prior_mono ρ w (by omega : b ≤ r)).trans hi
        exact hle hv
      · have hzero : outer ρ w b c = 0 := by
          have hce : c = (c - (n + 1)) + (n + 1) := by omega
          rw [outer, hce, pow_add, Module.End.mul_apply, hNil2, map_zero, map_zero]
        rw [hzero, wordOp_zero]
        exact Submodule.zero_mem _

/-- Every zero-mode normal word belongs to the genuine finite classical
branching family. No irreducibility or Weyl dimension theorem is assumed. -/
theorem normal_mem_classicalSpan {m n : ℕ} (hE : ρ.op 0 0 w = 0)
    (hH : ρ.op 6 0 w = (m : ℂ) • w) (hNil : (ρ.op 3 0 ^ (m + 1)) w = 0)
    (hNil2 : (ρ.op 4 0 ^ (n + 1)) w = 0) (a b c : ℕ) :
    (ρ.op 3 0 ^ a) (outer ρ w b c) ∈ classicalSpan ρ w m n := by
  have hv := theta_length_of_first_nil ρ w hNil b (a + b) (b + c) (by omega) (by omega)
  have he : Mv ρ w (a + b) (b + c) b = (ρ.op 3 0 ^ a) (outer ρ w b c) := by
    simp only [Mv, outer, Module.End.mul_apply]
    rw [show a + b - b = a by omega, show b + c - b = c by omega]
  rw [he] at hv
  apply prior_le_classicalSpan ρ w hE hH hNil hNil2 (m + 1) le_rfl
  apply (Submodule.span_le.mpr ?_) hv
  rintro _ ⟨b', hb', _, _, rfl⟩
  apply Submodule.subset_span
  refine ⟨List.replicate (a + b - b') (3, 0), b', b + c - b', by omega, ?_, ?_⟩
  · intro x hx
    have hx' := List.eq_of_mem_replicate hx
    subst x
    exact Or.inr (Or.inl rfl)
  · rw [← iterate_eq_wordOp ρ (3, 0), ← Module.End.pow_apply]
    rfl

/-- The span of all classical zero-mode normal words. -/
def zeroNormalSpan : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun t : ℕ × ℕ × ℕ =>
    (ρ.op 3 0 ^ t.1) (outer ρ w t.2.1 t.2.2))

/-- The constructive classical branching bound, stated using the finite
index cardinality so it does not import a Weyl character formula. -/
theorem zeroNormalSpan_bound {m n : ℕ} (hE : ρ.op 0 0 w = 0)
    (hH : ρ.op 6 0 w = (m : ℂ) • w) (hNil : (ρ.op 3 0 ^ (m + 1)) w = 0)
    (hNil2 : (ρ.op 4 0 ^ (n + 1)) w = 0) :
    FiniteDimensional ℂ (zeroNormalSpan ρ w) ∧
      Module.finrank ℂ (zeroNormalSpan ρ w) ≤ Fintype.card (ClassicalIndex m n) := by
  classical
  have hle : zeroNormalSpan ρ w ≤ classicalSpan ρ w m n := by
    rw [zeroNormalSpan, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact normal_mem_classicalSpan ρ w hE hH hNil hNil2 t.1 t.2.1 t.2.2
  haveI : FiniteDimensional ℂ (classicalSpan ρ w m n) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (zeroNormalSpan ρ w) :=
    Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, (Submodule.finrank_mono hle).trans ?_⟩
  exact finrank_range_le_card (classicalWord ρ w m n)

end

end VOA.DeligneAudit.A2.CVRectMixedClassical

#print axioms VOA.DeligneAudit.A2.CVRectMixedClassical.theta_length_of_first_nil
#print axioms VOA.DeligneAudit.A2.CVRectMixedClassical.first_string_mod_prior
#print axioms VOA.DeligneAudit.A2.CVRectMixedClassical.first_word_spanning_mod_prior
#print axioms VOA.DeligneAudit.A2.CVRectMixedClassical.zeroNormalSpan_bound
