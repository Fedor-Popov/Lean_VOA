/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GhostConjEndpoint

/-!
# Creation and annihilation on the monomial basis of one ghost pair, and their adjointness

On `FockSF` with its monomial basis `fockBasis` (monomials in increasing lexicographic order):

* `creBase_fockBasis` — `creBase p e_s = 0` if `p ∈ s`, else `σ(p, s) e_{s ∪ p}`;
* `annBase_fockBasis` — `annBase p e_s = σ(p, s) e_{s \ p}` if `p ∈ s`, else `0`;

with the common sign `σ(p, s) = (-1)^{#{q ∈ s | q < p}}` (`modeSign`).

* `basisForm_cre_adj` — for a multiplicative weight (`w (s ∪ p) = ν p · w s`), the creation
  operator is adjoint to `ν p ·` the annihilation operator for `basisForm fockBasis w`:
  `⟨creBase p x, y⟩ = ν p ⟨x, annBase p y⟩`; and the mirror statement `basisForm_ann_adj`;
* `basisForm_hermitian` — the basis form is Hermitian.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-! ### Generic: sesquilinear forms agreeing on a basis -/

section Generic

variable {κ V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The form `(x, y) ↦ c · P (f x) (g y)`. -/
def sesqComp (P : SesqForm V) (c : ℂ) (f g : V →ₗ[ℂ] V) : SesqForm V where
  toFun x y := c * P (f x) (g y)
  add_left x x' y := by rw [map_add, P.add_left]; ring
  smul_left z x y := by rw [map_smul, P.smul_left]; ring
  add_right x y y' := by rw [map_add, P.add_right]; ring
  smul_right z x y := by rw [map_smul, P.smul_right]; ring

@[simp] theorem sesqComp_apply (P : SesqForm V) (c : ℂ) (f g : V →ₗ[ℂ] V) (x y : V) :
    sesqComp P c f g x y = c * P (f x) (g y) := rfl

/-- Two sesquilinear forms agreeing on all pairs of basis vectors agree. -/
theorem sesq_ext_basis (b : Module.Basis κ ℂ V) (P Q : SesqForm V)
    (h : ∀ s t, P (b s) (b t) = Q (b s) (b t)) (x y : V) : P x y = Q x y := by
  have hx : x ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  have hy : y ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨t, rfl⟩ := hy; exact h s t
      | zero => rw [P.zero_right, Q.zero_right]
      | add y y' _ _ h1 h2 => rw [P.add_right, Q.add_right, h1, h2]
      | smul c y _ h1 => rw [P.smul_right, Q.smul_right, h1]
  | zero => rw [P.zero_left, Q.zero_left]
  | add x x' _ _ h1 h2 => rw [P.add_left, Q.add_left, h1 y hy, h2 y hy]
  | smul c x _ h1 => rw [P.smul_left, Q.smul_left, h1 y hy]

end Generic

/-! ### The monomial basis -/

theorem fockWord_eq_sort (s : Finset ModeIdx) : fockWord s = (s.sort (· ≤ ·)).map ofLex := by
  unfold fockWord
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp
    rfl

/-- The generator of one mode. -/
abbrev gen (p : ModeIdx) : FockSF := CliffordAlgebra.ι QSF (Finsupp.single (ofLex p) (1 : ℂ))

theorem fockBasis_insert_min {a : ModeIdx} {s : Finset ModeIdx} (ha : ∀ q ∈ s, a < q) :
    fockBasis (insert a s) = gen a * fockBasis s := by
  have has : a ∉ s := fun h => lt_irrefl a (ha a h)
  rw [fockBasis_eq_word, fockBasis_eq_word, fockWord_eq_sort, fockWord_eq_sort,
    Finset.sort_insert (· ≤ ·) (fun q hq => (ha q hq).le) has, List.map_cons, stWordSF_cons]

theorem fockBasis_empty : fockBasis ∅ = 1 := by
  rw [fockBasis_eq_word, fockWord_empty, stWordSF_nil]

theorem gen_mul_gen_anticomm (p q : ModeIdx) : gen p * gen q = -(gen q * gen p) := by
  have h := creBase_anticomm (ofLex p) (ofLex q) (1 : FockSF)
  simp only [creBase, LinearMap.mulLeft_apply, mul_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem gen_mul_self (p : ModeIdx) : gen p * gen p = 0 := by
  have h := gen_mul_gen_anticomm p p
  have h2 : (2 : ℂ) • (gen p * gen p) = 0 := by rw [two_smul]; nth_rewrite 1 [h]; abel
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The sign of moving the mode `p` past the modes of `s` below it. -/
def modeSign (p : ModeIdx) (s : Finset ModeIdx) : ℂ := (-1) ^ (s.filter (· < p)).card

theorem modeSign_insert_lt {p a : ModeIdx} {s : Finset ModeIdx} (has : a ∉ s) (hap : a < p) :
    modeSign p (insert a s) = -modeSign p s := by
  unfold modeSign
  rw [Finset.filter_insert, if_pos hap, Finset.card_insert_of_notMem (by simp [has]), pow_succ]
  ring

theorem modeSign_insert_gt {p a : ModeIdx} {s : Finset ModeIdx} (hap : p < a) :
    modeSign p (insert a s) = modeSign p s := by
  unfold modeSign
  rw [Finset.filter_insert, if_neg (not_lt.mpr hap.le)]

theorem modeSign_of_min {p : ModeIdx} {s : Finset ModeIdx} (hp : ∀ q ∈ s, p < q) :
    modeSign p s = 1 := by
  unfold modeSign
  rw [Finset.filter_false_of_mem (fun q hq => not_lt.mpr (hp q hq).le), Finset.card_empty,
    pow_zero]

theorem modeSign_sq (p : ModeIdx) (s : Finset ModeIdx) : modeSign p s * modeSign p s = 1 := by
  unfold modeSign; rw [← mul_pow]; norm_num

theorem modeSign_erase {p : ModeIdx} {s : Finset ModeIdx} :
    modeSign p (s.erase p) = modeSign p s := by
  unfold modeSign
  congr 2
  ext q
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨⟨ne_of_lt h', h⟩, h'⟩

/-- **Creation on the monomial basis.** -/
theorem creBase_fockBasis (p : ModeIdx) (s : Finset ModeIdx) :
    creBase (ofLex p) (fockBasis s) =
      if p ∈ s then 0 else modeSign p s • fockBasis (insert p s) := by
  induction s using Finset.induction_on_min with
  | empty =>
      rw [if_neg (Finset.notMem_empty p), modeSign_of_min (by simp), one_smul,
        fockBasis_insert_min (by simp), fockBasis_empty, creBase, LinearMap.mulLeft_apply]
  | insert a s ha ih =>
      have has : a ∉ s := fun h => lt_irrefl a (ha a h)
      rw [fockBasis_insert_min ha, creBase, LinearMap.mulLeft_apply, ← mul_assoc]
      rcases lt_trichotomy p a with hpa | rfl | hap
      · have hp : p ∉ insert a s := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hpa.ne, fun h => lt_asymm hpa (ha p h)⟩
        have hmin : ∀ q ∈ insert a s, p < q := by
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hpa
          · exact hpa.trans (ha q hq)
        rw [if_neg hp, modeSign_of_min hmin, one_smul, fockBasis_insert_min hmin,
          fockBasis_insert_min ha, mul_assoc]
      · rw [gen_mul_self, zero_mul, if_pos (Finset.mem_insert_self _ _)]
      · rw [gen_mul_gen_anticomm, neg_mul, mul_assoc]
        have ih' : gen p * fockBasis s =
            if p ∈ s then 0 else modeSign p s • fockBasis (insert p s) := by
          rw [← ih, creBase, LinearMap.mulLeft_apply]
        rw [ih']
        by_cases hps : p ∈ s
        · rw [if_pos hps, mul_zero, neg_zero, if_pos (Finset.mem_insert_of_mem hps)]
        · have hp : p ∉ insert a s := by
            simp only [Finset.mem_insert, not_or]; exact ⟨hap.ne', hps⟩
          rw [if_neg hps, if_neg hp, mul_smul_comm, modeSign_insert_lt has hap,
            Finset.insert_comm, fockBasis_insert_min (a := a) (fun q hq => ?_), neg_smul]
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hap
          · exact ha q hq

/-- **Annihilation on the monomial basis.** -/
theorem annBase_fockBasis (p : ModeIdx) (s : Finset ModeIdx) :
    annBase (ofLex p) (fockBasis s) =
      if p ∈ s then modeSign p s • fockBasis (s.erase p) else 0 := by
  induction s using Finset.induction_on_min with
  | empty =>
      rw [if_neg (Finset.notMem_empty p), fockBasis_empty, ← stWordSF_nil, annBase_stWordSF_nil]
  | insert a s ha ih =>
      have has : a ∉ s := fun h => lt_irrefl a (ha a h)
      have e : annBase (ofLex p) (fockBasis (insert a s)) =
          (if ofLex p = ofLex a then (1 : ℂ) else 0) • fockBasis s -
            gen a * annBase (ofLex p) (fockBasis s) := by
        rw [fockBasis_insert_min ha, fockBasis_eq_word, ← stWordSF_cons, annBase_stWordSF_cons]
      rw [e, ih]
      by_cases hpa : p = a
      · subst hpa
        have hm : modeSign p (insert p s) = 1 := by
          unfold modeSign
          rw [Finset.filter_insert, if_neg (lt_irrefl p),
            Finset.filter_false_of_mem (fun q hq => not_lt.mpr (ha q hq).le), Finset.card_empty,
            pow_zero]
        rw [if_pos rfl, if_neg has, mul_zero, sub_zero, one_smul, if_pos (Finset.mem_insert_self _ _),
          hm, one_smul, Finset.erase_insert has]
      · have hpa' : ofLex p ≠ ofLex a := fun h => hpa (by simpa using h)
        rw [if_neg hpa', zero_smul, zero_sub]
        by_cases hps : p ∈ s
        · have hap : a < p := ha p hps
          rw [if_pos hps, if_pos (Finset.mem_insert_of_mem hps), mul_smul_comm,
            modeSign_insert_lt has hap, ← fockBasis_insert_min (fun q hq => ha q (Finset.mem_of_mem_erase hq)),
            Finset.erase_insert_of_ne (Ne.symm hpa), neg_smul]
        · have hp : p ∉ insert a s := by
            simp only [Finset.mem_insert, not_or]; exact ⟨hpa, hps⟩
          rw [if_neg hps, if_neg hp, mul_zero, neg_zero]

/-! ### The basis form -/

section BF

variable {κ V : Type*} [AddCommGroup V] [Module ℂ V]

theorem basisForm_basis_self (b : Module.Basis κ ℂ V) (w : κ → ℝ) (s : κ) :
    basisForm b w (b s) (b s) = (w s : ℂ) := by
  classical
  change (orthSum (fun s : κ => stdForm (w s))).toFun
    (finsuppLEquivDirectSum ℂ ℂ κ (b.repr (b s)))
    (finsuppLEquivDirectSum ℂ ℂ κ (b.repr (b s))) = _
  rw [b.repr_self, finsuppLEquivDirectSum_single, DirectSum.lof_eq_of]
  convert orthSum_of_same (fun s => stdForm (w s)) s (1 : ℂ) (1 : ℂ) using 1
  change _ = (w s : ℂ) * (starRingEnd ℂ) 1 * 1
  simp

theorem basisForm_basis [DecidableEq κ] (b : Module.Basis κ ℂ V) (w : κ → ℝ) (s t : κ) :
    basisForm b w (b s) (b t) = if s = t then (w s : ℂ) else 0 := by
  by_cases hst : s = t
  · subst hst; rw [if_pos rfl, basisForm_basis_self]
  · rw [if_neg hst]; exact basisForm_basis_ne b w hst

end BF

/-! ### Adjointness of creation and annihilation -/

theorem modeSign_insert_self (p : ModeIdx) (s : Finset ModeIdx) :
    modeSign p (insert p s) = modeSign p s := by
  unfold modeSign
  rw [Finset.filter_insert, if_neg (lt_irrefl p)]

theorem conj_modeSign (p : ModeIdx) (s : Finset ModeIdx) :
    (starRingEnd ℂ) (modeSign p s) = modeSign p s := by
  unfold modeSign; simp

/-- A weight is multiplicative with mode norms `ν`. -/
def MultWeight (w : Finset ModeIdx → ℝ) (ν : ModeIdx → ℝ) : Prop :=
  ∀ p s, p ∉ s → w (insert p s) = ν p * w s

theorem fockForm_basis (w : Finset ModeIdx → ℝ) (s t : Finset ModeIdx) :
    fockForm w (fockBasis s) (fockBasis t) = if s = t then (w s : ℂ) else 0 := by
  by_cases hst : s = t
  · subst hst; rw [if_pos rfl]; exact basisForm_basis_self _ _ _
  · rw [if_neg hst]; exact basisForm_basis_ne _ _ hst

/-- **Creation is adjoint to `ν ·` annihilation** for a multiplicative basis form. -/
theorem fockForm_cre_adj {w : Finset ModeIdx → ℝ} {ν : ModeIdx → ℝ} (hw : MultWeight w ν)
    (p : ModeIdx) (x y : FockSF) :
    fockForm w (creBase (ofLex p) x) y = (ν p : ℂ) * fockForm w x (annBase (ofLex p) y) := by
  have key := sesq_ext_basis fockBasis (sesqComp (fockForm w) 1 (creBase (ofLex p)) LinearMap.id)
    (sesqComp (fockForm w) (ν p) LinearMap.id (annBase (ofLex p))) ?_ x y
  · simpa using key
  intro s t
  change 1 * _ = _ * _
  simp only [LinearMap.id_apply, one_mul]
  rw [creBase_fockBasis, annBase_fockBasis]
  by_cases hps : p ∈ s
  · rw [if_pos hps, (fockForm w).zero_left]
    by_cases hpt : p ∈ t
    · rw [if_pos hpt, (fockForm w).smul_right, fockForm_basis, if_neg]
      · simp
      · rintro rfl; simp at hps
    · rw [if_neg hpt, (fockForm w).zero_right, mul_zero]
  · rw [if_neg hps, (fockForm w).smul_left, fockForm_basis, conj_modeSign]
    by_cases hst : insert p s = t
    · subst hst
      rw [if_pos rfl, if_pos (Finset.mem_insert_self _ _), (fockForm w).smul_right,
        Finset.erase_insert hps, fockForm_basis, if_pos rfl, modeSign_insert_self, hw p s hps]
      push_cast; ring
    · rw [if_neg hst, mul_zero]
      by_cases hpt : p ∈ t
      · rw [if_pos hpt, (fockForm w).smul_right, fockForm_basis, if_neg, mul_zero, mul_zero]
        rintro rfl
        exact hst (Finset.insert_erase hpt)
      · rw [if_neg hpt, (fockForm w).zero_right, mul_zero]

/-- **Annihilation is adjoint to `ν⁻¹ ·` creation**, in the form
`ν ⟨annBase p x, y⟩ = ⟨x, creBase p y⟩`. -/
theorem fockForm_ann_adj {w : Finset ModeIdx → ℝ} {ν : ModeIdx → ℝ} (hw : MultWeight w ν)
    (p : ModeIdx) (x y : FockSF) :
    (ν p : ℂ) * fockForm w (annBase (ofLex p) x) y = fockForm w x (creBase (ofLex p) y) := by
  have key := sesq_ext_basis fockBasis (sesqComp (fockForm w) (ν p) (annBase (ofLex p))
    LinearMap.id) (sesqComp (fockForm w) 1 LinearMap.id (creBase (ofLex p))) ?_ x y
  · simpa using key
  intro s t
  change _ * _ = 1 * _
  simp only [LinearMap.id_apply, one_mul]
  rw [creBase_fockBasis, annBase_fockBasis]
  by_cases hpt : p ∈ t
  · rw [if_pos hpt, (fockForm w).zero_right]
    by_cases hps : p ∈ s
    · rw [if_pos hps, (fockForm w).smul_left, fockForm_basis, if_neg]
      · simp
      · rintro rfl; simp at hpt
    · rw [if_neg hps, (fockForm w).zero_left, mul_zero]
  · rw [if_neg hpt, (fockForm w).smul_right, fockForm_basis]
    by_cases hst : s = insert p t
    · subst hst
      rw [if_pos rfl, if_pos (Finset.mem_insert_self _ _), (fockForm w).smul_left,
        Finset.erase_insert hpt, fockForm_basis, if_pos rfl, modeSign_insert_self,
        conj_modeSign, hw p t hpt]
      push_cast; ring
    · rw [if_neg hst, mul_zero]
      by_cases hps : p ∈ s
      · rw [if_pos hps, (fockForm w).smul_left, fockForm_basis, if_neg, mul_zero, mul_zero]
        intro h
        exact hst (by rw [← h, Finset.insert_erase hps])
      · rw [if_neg hps, (fockForm w).zero_left, mul_zero]

/-- The flipped-conjugated form `(x, y) ↦ conj ⟨y, x⟩`. -/
def sesqFlip {V : Type*} [AddCommGroup V] [Module ℂ V] (P : SesqForm V) : SesqForm V where
  toFun x y := (starRingEnd ℂ) (P y x)
  add_left x x' y := by rw [P.add_right, map_add]
  smul_left z x y := by rw [P.smul_right, map_mul]
  add_right x y y' := by rw [P.add_left, map_add]
  smul_right z x y := by rw [P.smul_left, map_mul, Complex.conj_conj]

/-- The basis form is Hermitian. -/
theorem fockForm_hermitian (w : Finset ModeIdx → ℝ) (x y : FockSF) :
    fockForm w x y = (starRingEnd ℂ) (fockForm w y x) := by
  refine sesq_ext_basis fockBasis (fockForm w) (sesqFlip (fockForm w)) ?_ x y
  intro s t
  change _ = (starRingEnd ℂ) _
  rw [fockForm_basis, fockForm_basis]
  by_cases hst : s = t
  · subst hst; simp
  · rw [if_neg hst, if_neg (Ne.symm hst), map_zero]

end

end VOA.ConcreteHodge
