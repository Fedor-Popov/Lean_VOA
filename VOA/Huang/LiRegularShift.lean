import VOA.Huang.LiRegularOpp
import VOA.Huang.LiRegularExp

/-! # Translating the opposite base: `Y°(v, x + c) = e^{−cL(1)} Y°(v, x) e^{cL(1)}`

For an ordinary module `N`, the operator `L(1)` is locally nilpotent and the opposite modes
satisfy `[L(1), v°ₙ] = n v°ₙ₋₁` (`L1_oppB`), i.e. `L(1)` is the translation generator of
the right module `(M, Y°)` (Li, Remark 2.9, with `L°(−1) = L(1)`).  Hence conjugation by
the finite exponential `e^{cL(1)}` translates the opposite base:

  `e^{cL(1)} v°ₙ e^{−cL(1)} = Σⱼ C(n,j) cʲ v°ₙ₋ⱼ`.

The translated base is again an `OppBase` (conjugation preserves the opposite Jacobi
identity), which is what Li's left action `Y^L_{P(z)}` is built from (Li, Lemma 3.20).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The commutator formula for a weak module. -/
theorem module_commutator (A : WeakModule W M) (a b : V) (p q : ℤ) (x : M) :
    mode (A.YM a) p (mode (A.YM b) q x) - mode (A.YM b) q (mode (A.YM a) p x)
      = ∑ᶠ i : ℤ, cbz p i • mode (A.YM (W.smul a i b)) (p + q - i) x := by
  have h := A.jacobi a b x 0 p q
  have h1 : negOnePow (0 : ℤ) = 1 := by simp [negOnePow]
  rw [finsum_eq_single _ 0 (fun i hi => by
    rcases lt_or_gt_of_ne hi with h' | h'
    · rw [cbz_apply_neg 0 h', mul_zero, zero_smul]
    · rw [cbz_lt (p := 0) (c := i) le_rfl h', mul_zero, zero_smul])] at h
  simpa [h1] using h

section L1

variable (N : OrdVModule W M)

/-- `L(1)` on the module. -/
noncomputable def L1m : Module.End ℂ M := mode (N.YM W.conformalVector) 2

/-- `[L(1), uₘ] = (2 wt u − m − 2) uₘ₊₁ + (L(1)u)ₘ` for homogeneous `u`. -/
theorem L1m_comm {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (m : ℤ) (x : M) :
    L1m N (mode (N.YM u) m x) - mode (N.YM u) m (L1m N x)
      = ((2 * wt - m - 2 : ℤ) : ℂ) • mode (N.YM u) (m + 1) x
        + mode (N.YM (W.L 1 u)) m x := by
  rw [L1m, module_commutator N.toWeakModule]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (0 : ℤ) 2) (fun i hi => by
    rw [Function.mem_support] at hi
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg 2 h, zero_smul]
    · rw [cbz_lt (p := 2) (c := i) (by norm_num) h, zero_smul])]
  rw [show Finset.Icc (0 : ℤ) 2 = {0, 1, 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e0 : W.smul W.conformalVector 0 u = W.L (-1) u := by
    rw [L_def]; rfl
  have e1 : W.smul W.conformalVector 1 u = (wt : ℂ) • u := by
    rw [← L_zero_grading W u hu, L_def]; rfl
  have e2 : W.smul W.conformalVector 2 u = W.L 1 u := by
    rw [L_def]; rfl
  rw [e0, e1, e2]
  have hT := act_T_covariance N.toWeakModule u (2 + m - 0) x
  simp only [WeakModule.act_def] at hT
  rw [hT, map_smul, mode_smul, LinearMap.smul_apply]
  have c0 : cbz 2 0 = 1 := cbz_zero 2
  have c1 : cbz 2 1 = 2 := by
    have := cbz_natCast_eq_choose (a := 2) (k := 1) (by norm_num)
    norm_num at this; exact this
  have c2 : cbz 2 2 = 1 := by
    have := cbz_natCast_eq_choose (a := 2) (k := 2) (by norm_num)
    norm_num at this; exact this
  rw [c0, c1, c2, show 2 + m - 0 - 1 = m + 1 by ring, show 2 + m - 1 = m + 1 by ring,
    show 2 + m - 2 = m by ring]
  push_cast
  module

/-- **`L(1)` is the translation generator of the opposite modes**:
`[L(1), v°ₙ] = n v°ₙ₋₁`. -/
theorem L1_oppB (v : V) (n : ℤ) (x : M) :
    L1m N (oppB N v n x) - oppB N v n (L1m N x) = (n : ℂ) • oppB N v (n - 1) x := by
  refine reduce_homogeneous W (P := fun v => L1m N (oppB N v n x) - oppB N v n (L1m N x)
    = (n : ℂ) • oppB N v (n - 1) x) ?_ (by simp) ?_ v
  swap
  · intro a b ha hb
    simp only [map_add, Pi.add_apply, LinearMap.add_apply] at ha hb ⊢
    rw [smul_add, ← ha, ← hb]; abel
  intro wt v hv
  rcases lt_or_ge wt 0 with hw | hw
  · have hv0 : v = 0 := by
      have := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hv (j := 0) (by omega)
      simpa using this
    subst hv0; simp
  obtain ⟨w, rfl⟩ : ∃ w : ℕ, wt = w := ⟨wt.toNat, (Int.toNat_of_nonneg hw).symm⟩
  rw [oppB_homog N hv, oppB_homog N hv]
  simp only [Int.toNat_natCast, LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply,
    map_smul, map_sum]
  set T : ℕ → M := fun j =>
    mode (N.YM ((W.L 1 ^ j) v)) (2 * (w : ℤ) - (n - 1) - 2 - (j : ℤ)) x with hT
  have hcomm : ∀ j ∈ Finset.range (w + 1),
      L1m N (mode (N.YM ((W.L 1 ^ j) v)) (2 * (w : ℤ) - n - 2 - (j : ℤ)) x)
        - mode (N.YM ((W.L 1 ^ j) v)) (2 * (w : ℤ) - n - 2 - (j : ℤ)) (L1m N x)
      = ((n : ℂ) - j) • T j + T (j + 1) := by
    intro j _
    have hj := L_one_pow_mem W hv j
    rw [L1m_comm N hj]
    simp only [hT]
    rw [show 2 * ((w : ℤ) - (j : ℤ)) - (2 * (w : ℤ) - n - 2 - (j : ℤ)) - 2 = n - j by ring,
      show 2 * (w : ℤ) - n - 2 - (j : ℤ) + 1 = 2 * (w : ℤ) - (n - 1) - 2 - (j : ℤ) by ring,
      show 2 * (w : ℤ) - n - 2 - (j : ℤ) = 2 * (w : ℤ) - (n - 1) - 2 - ((j + 1 : ℕ) : ℤ) by
        push_cast; ring, ← Module.End.mul_apply, ← pow_succ']
    push_cast
    rfl
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun j hj => by
    rw [← smul_sub, hcomm j hj]]
  have htop : T (w + 1) = 0 := by
    simp only [hT]
    rw [VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hv (j := w + 1) (by push_cast; omega),
      map_zero, mode_zero, LinearMap.zero_apply]
  have hshift : ∑ j ∈ Finset.range (w + 1), ((j.factorial : ℂ)⁻¹) • T (j + 1)
      = ∑ j ∈ Finset.range (w + 1), ((j : ℂ) * (j.factorial : ℂ)⁻¹) • T j := by
    have h1 : ∑ j ∈ Finset.range (w + 2), ((j : ℂ) * (j.factorial : ℂ)⁻¹) • T j
        = ∑ j ∈ Finset.range (w + 1), ((j.factorial : ℂ)⁻¹) • T (j + 1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    rw [← h1, Finset.sum_range_succ, htop, smul_zero, add_zero]
  have hsplit : ∀ j ∈ Finset.range (w + 1),
      ((j.factorial : ℂ)⁻¹) • (((n : ℂ) - j) • T j + T (j + 1))
        = (((n : ℂ) - j) * (j.factorial : ℂ)⁻¹) • T j + ((j.factorial : ℂ)⁻¹) • T (j + 1) := by
    intro j _
    rw [smul_add, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hshift, ← Finset.sum_add_distrib]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_add, smul_smul, smul_smul, ← add_smul]
  exact congrArg₂ _ (by ring) rfl

end L1

/-! ## Conjugating an opposite base -/

namespace OppBase

variable (Bs : OppBase W M)

theorem modeJacL_fin (a b : V) (w : M) (l m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz l i) •
      (Bs.B b (n + i) (Bs.B a (l + m - i) w)
        - negOnePow l • Bs.B a (m + i) (Bs.B b (l + n - i) w))).Finite := by
  obtain ⟨Ka, hKa⟩ := Bs.trunc a w
  obtain ⟨Kb, hKb⟩ := Bs.trunc b w
  apply (Set.finite_Icc 0 (max (l + m - Ka) (l + n - Kb))).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp [cbz_apply_neg l h]
  · rw [hKa _ (by omega), hKb _ (by omega), map_zero, map_zero, smul_zero, sub_zero, smul_zero]

theorem modeJacR_fin (a b : V) (w : M) (l m n : ℤ) :
    (Function.support fun i : ℤ => cbz m i • Bs.B (W.smul a (l + i) b) (m + n - i) w).Finite := by
  obtain ⟨R, hR⟩ := W.regularity a b
  apply (Set.finite_Icc 0 (R - l)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp [cbz_apply_neg m h]
  · rw [show W.smul a (l + i) b = 0 from hR _ (by omega)]; simp

/-- Conjugation of an opposite base by mutually inverse linear maps. -/
noncomputable def conj (Φ Ψ : Module.End ℂ M) (h₁ : ∀ x, Φ (Ψ x) = x)
    (h₂ : ∀ x, Ψ (Φ x) = x) : OppBase W M where
  B :=
    { toFun := fun a n => Φ ∘ₗ Bs.B a n ∘ₗ Ψ
      map_add' := fun a b => by
        funext n; simp only [map_add, Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun c a => by
        funext n
        simp only [map_smul, Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul,
          RingHom.id_apply] }
  trunc a y := by
    obtain ⟨K, hK⟩ := Bs.trunc a (Ψ y)
    exact ⟨K, fun n hn => by simp [hK n hn]⟩
  vacuum n y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      Bs.vacuum]
    split_ifs
    · exact h₁ y
    · exact map_zero _
  jacobi a b y l m n := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply, h₂]
    have hL : ∀ i : ℤ, (negOnePow i * cbz l i) •
        (Φ (Bs.B b (n + i) (Bs.B a (l + m - i) (Ψ y)))
          - negOnePow l • Φ (Bs.B a (m + i) (Bs.B b (l + n - i) (Ψ y))))
        = Φ ((negOnePow i * cbz l i) • (Bs.B b (n + i) (Bs.B a (l + m - i) (Ψ y))
          - negOnePow l • Bs.B a (m + i) (Bs.B b (l + n - i) (Ψ y)))) := by
      intro i; simp only [map_smul, map_sub]
    have hR : ∀ i : ℤ, cbz m i • Φ (Bs.B (W.smul a (l + i) b) (m + n - i) (Ψ y))
        = Φ (cbz m i • Bs.B (W.smul a (l + i) b) (m + n - i) (Ψ y)) := by
      intro i; simp only [map_smul]
    rw [finsum_congr hL, finsum_congr hR, ← map_finsum Φ (Bs.modeJacL_fin a b (Ψ y) l m n),
      ← map_finsum Φ (Bs.modeJacR_fin a b (Ψ y) l m n), Bs.jacobi]

@[simp] theorem conj_B (Φ Ψ : Module.End ℂ M) (h₁ : ∀ x, Φ (Ψ x) = x)
    (h₂ : ∀ x, Ψ (Φ x) = x) (a : V) (n : ℤ) (y : M) :
    (Bs.conj Φ Ψ h₁ h₂).B a n y = Φ (Bs.B a n (Ψ y)) := rfl

/-- A **translation datum** for an opposite base: a locally nilpotent operator `X` with
`[X, B(a)ₙ] = n B(a)ₙ₋₁` (for the opposite base of an ordinary module, `X = L(1)`). -/
structure Shift where
  X : Module.End ℂ M
  locNil : LocNil X
  comm : ∀ (a : V) (n : ℤ) (y : M), X (Bs.B a n y) - Bs.B a n (X y) = (n : ℂ) • Bs.B a (n - 1) y

/-- The translated base `B(a, x + c)`, the conjugate by `e^{cX}`. -/
noncomputable def tBase (S : Bs.Shift) (c : ℂ) : OppBase W M :=
  Bs.conj (expOp S.locNil c) (expOp S.locNil (-c)) (expOp_neg_cancel S.locNil c)
    (expOp_cancel_neg S.locNil c)

/-- **The translated modes**: `B^{(c)}(a)ₙ = Σₖ C(n,k) cᵏ B(a)ₙ₋ₖ`. -/
theorem tBase_B (S : Bs.Shift) (c : ℂ) (a : V) (n : ℤ) (y : M) :
    (Bs.tBase S c).B a n y = ∑ᶠ k : ℕ, (cbz n k * c ^ k) • Bs.B a (n - k) y := by
  rw [tBase, conj_B]
  have h := expOp_conj S.locNil (fun n => Bs.B a n) (fun n y => S.comm a n y)
    (fun y => Bs.trunc a y) c n (expOp S.locNil (-c) y)
  rw [expOp_neg_cancel] at h
  exact h

end OppBase

/-! ## The translated opposite base of an ordinary module -/

section Trans

variable (N : OrdVModule W M)

theorem L1m_pow_mem {α : ℂ} {x : M} (hx : x ∈ N.weight α) (J : ℕ) :
    (L1m N ^ J) x ∈ N.weight (α - J) := by
  induction J with
  | zero => simpa using hx
  | succ J ih =>
    rw [pow_succ', Module.End.mul_apply, L1m]
    have h := mode_mem_weight N W.conformalVector_mem_grading_two ih 2
    convert h using 2
    push_cast; ring

/-- `L(1)` is locally nilpotent on an ordinary module. -/
theorem L1m_locNil : LocNil (L1m N) := by
  intro x
  refine Submodule.iSup_induction N.weight (motive := fun x => ∃ J : ℕ, (L1m N ^ J) x = 0)
    (mem_iSup_weight_ord N x) ?_ ⟨0, by simp⟩ ?_
  · intro α x hx
    obtain ⟨B, hB⟩ := N.boundedBelow
    obtain ⟨J, hJ⟩ := exists_nat_gt (α.re - B)
    refine ⟨J, ?_⟩
    have hmem := L1m_pow_mem N hx J
    have hbot : N.weight (α - J) = ⊥ := by
      by_contra h
      have := hB _ h
      simp only [Complex.sub_re, Complex.natCast_re] at this
      linarith
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · rintro x y ⟨J, hJ⟩ ⟨J', hJ'⟩
    exact ⟨max J J', by rw [map_add, pow_apply_eq_zero_of_le hJ (le_max_left _ _),
      pow_apply_eq_zero_of_le hJ' (le_max_right _ _), add_zero]⟩

/-- The translation datum of the opposite base of an ordinary module: `L(1)`. -/
noncomputable def oppShift : (oppBase N).Shift where
  X := L1m N
  locNil := L1m_locNil N
  comm := fun a n y => L1_oppB N a n y

/-- **The translated opposite base** `Y°(v, x + c)`, realized as the conjugate of the opposite
base by `e^{cL(1)}`. -/
noncomputable def transBase (c : ℂ) : OppBase W M := (oppBase N).tBase (oppShift N) c

/-- **The translated modes**: `(Y°)^{(c)}ₙ = Σₖ C(n,k) cᵏ v°ₙ₋ₖ`. -/
theorem transBase_B (c : ℂ) (a : V) (n : ℤ) (y : M) :
    (transBase N c).B a n y = ∑ᶠ k : ℕ, (cbz n k * c ^ k) • oppB N a (n - k) y :=
  (oppBase N).tBase_B (oppShift N) c a n y

end Trans

end VOA.Huang.LiRegular
