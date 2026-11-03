/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.LiAssociatedGraded
import VOA.Modularity.BuhlSpanningData

/-!
# Multiplicativity of the adjoint Li filtration

If `F^p` denotes `liFiltration W p`, this file proves

* `F^p _{(-1)} F^q ⊆ F^{p+q}`;
* `L_{-1} F^p ⊆ F^{p+1}`;
* the strengthened nonnegative-mode estimate `F^p _{(n)} F^q ⊆ F^{p+q-n}`;
* the one-step commutator estimate
  `x_{(-1)}y - y_{(-1)}x ∈ F^{p+q+1}`;
* the one-step associator estimate
  `(x_{(-1)}y)_{(-1)}z - x_{(-1)}(y_{(-1)}z) ∈ F^{p+q+r+1}`;
* descended product maps on finite fixed-weight Li layers, with `HEq` commutativity and
  associativity across propositionally equal target bidegrees.

The actual engine is the stronger all-mode estimate
`F^p _{(N)} F^q ⊆ F^{p+q-N-1}`, stated first with integer filtration indices.  Its proof is
an induction on a word spanning the first input.  The existing one-input estimate
`act_mem_Gfil` handles the correction term in the all-integer iterate formula `mode_iterate`.

The final sections descend the `(-1)`-product to the finite fixed-weight layers, prove
commutativity by skew-symmetry, and prove associativity by isolating the leading term of the
iterate formula.  This is the smallest honest associated-graded multiplication interface
available before packaging the direct sum over the two gradings.  The direct-sum algebra structure
and the differential algebra structure are not claimed here.
-/

namespace VOA

universe u

section LiMultiplicativity

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

private theorem wordAct_smul_mem_adjointGfil (W : VertexOperatorAlgebra V)
    (hLW : LWGenerated (adjointWeakModule W) ({W.vacuum} : Set V))
    (l : List (Letter V)) (hl : WordOK W l) {q N : ℤ} {y : V}
    (hy : y ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) q) :
    W.smul (wordAct (adjointWeakModule W) l W.vacuum) N y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V)
        ((wordLevel l : ℤ) + q - N - 1) := by
  induction l generalizing q N y with
  | nil =>
      simp only [wordAct_nil, wordLevel_nil, Nat.cast_zero, zero_add]
      rw [PreVertexAlgebra.smul_vacuum_left]
      split_ifs with hN
      · subst N
        simpa using hy
      · exact Submodule.zero_mem _
  | cons pc t ih =>
      obtain ⟨hpc, ht⟩ := WordOK_of_cons hl
      change W.smul
          (W.smul pc.1 (-(pc.2.2 : ℤ) - 1)
            (wordAct (adjointWeakModule W) t W.vacuum)) N y ∈ _
      rw [VertexOperatorAlgebra.mode_iterate W]
      refine finsum_mem_submodule_lf _ _ (fun i => ?_)
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
      · have hinner := ih ht (q := q) (N := N + (i : ℤ)) hy
        have hpre := Gfil_prepend (adjointWeakModule W) ({W.vacuum} : Set V)
          (n := pc.2.2 + i) hpc hinner
        have hidx : -(pc.2.2 : ℤ) - 1 - (i : ℤ) = -((pc.2.2 + i : ℕ) : ℤ) - 1 := by
          push_cast
          ring
        rw [hidx]
        change mode ((adjointWeakModule W).YM pc.1) (-((pc.2.2 + i : ℕ) : ℤ) - 1)
          (W.smul (wordAct (adjointWeakModule W) t W.vacuum) (N + (i : ℤ)) y) ∈ _
        convert hpre using 1
        norm_num [wordLevel_cons]
        ring_nf
      · have ha := act_mem_Gfil (adjointWeakModule W) ({W.vacuum} : Set V) hLW hpc
          (i : ℤ) hy
        have hinner := ih ht (q := q - (i : ℤ) - 1)
          (N := -(pc.2.2 : ℤ) - 1 + N - (i : ℤ)) ha
        convert hinner using 1
        norm_num [wordLevel_cons]
        ring_nf

/-- A homogeneous nonnegative mode acts one Li step better than the generic mode estimate. -/
private theorem homogeneous_smul_nonneg_word_mem_adjointGfil
    (W : VertexOperatorAlgebra V) (l : List (Letter V)) (hl : WordOK W l)
    {u : V} {bu : ℕ} (hu : u ∈ W.grading (bu : ℤ)) (k : ℕ) :
    W.smul u (k : ℤ) (wordAct (adjointWeakModule W) l W.vacuum) ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V)
        ((wordLevel l : ℤ) - (k : ℤ)) := by
  induction l with
  | nil =>
      simp only [wordAct_nil, wordLevel_nil, Nat.cast_zero, zero_sub]
      rw [PreVertexAlgebra.smul_vacuum_nonneg W.toPreVertexAlgebra u (Int.natCast_nonneg k)]
      exact Submodule.zero_mem _
  | cons pc t ih =>
      obtain ⟨hpc, ht⟩ := WordOK_of_cons hl
      have hcomm := mode_commutator (adjointWeakModule W) u pc.1
        (wordAct (adjointWeakModule W) t W.vacuum) (k : ℤ) (-(pc.2.2 : ℤ) - 1)
      have hsplit :
          mode ((adjointWeakModule W).YM u) (k : ℤ)
              (wordAct (adjointWeakModule W) (pc :: t) W.vacuum) =
            mode ((adjointWeakModule W).YM pc.1) (-(pc.2.2 : ℤ) - 1)
                (mode ((adjointWeakModule W).YM u) (k : ℤ)
                  (wordAct (adjointWeakModule W) t W.vacuum))
              + ∑ᶠ j : ℤ, cbz (k : ℤ) j •
                  mode ((adjointWeakModule W).YM (W.smul u j pc.1))
                    ((k : ℤ) + (-(pc.2.2 : ℤ) - 1) - j)
                    (wordAct (adjointWeakModule W) t W.vacuum) := by
        rw [wordAct_cons, ← hcomm]
        abel
      change mode ((adjointWeakModule W).YM u) (k : ℤ)
        (wordAct (adjointWeakModule W) (pc :: t) W.vacuum) ∈ _
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · have hpre := Gfil_prepend (adjointWeakModule W) ({W.vacuum} : Set V)
          (n := pc.2.2) hpc (ih ht)
        convert hpre using 1
        norm_num [wordLevel_cons]
        ring_nf
      · refine finsum_mem_submodule_lf _ _ (fun j => ?_)
        rcases lt_or_ge j 0 with hj | hj
        · rw [cbz_apply_neg _ hj, zero_smul]
          exact Submodule.zero_mem _
        · refine Submodule.smul_mem _ _ ?_
          have hgr : W.smul u j pc.1 ∈
              W.grading ((bu : ℤ) + (pc.2.1 : ℤ) - j - 1) :=
            W.smul_mem_grading hu hpc j
          rcases lt_or_ge ((bu : ℤ) + (pc.2.1 : ℤ) - j - 1) 0 with hneg | hnn
          · have hz : W.smul u j pc.1 = 0 := by
              rw [W.positivity _ hneg, Submodule.mem_bot] at hgr
              exact hgr
            rw [hz]
            simp only [map_zero, mode_zero, LinearMap.zero_apply]
            exact Submodule.zero_mem _
          · obtain ⟨γ, hγ⟩ :
                ∃ γ : ℕ, ((bu : ℤ) + (pc.2.1 : ℤ) - j - 1) = (γ : ℤ) :=
              ⟨((bu : ℤ) + (pc.2.1 : ℤ) - j - 1).toNat, by omega⟩
            rw [hγ] at hgr
            have hact := wordAct_act_mem_Gfil (adjointWeakModule W)
              ({W.vacuum} : Set V) (lwGenerated_adjoint W) t
              (Set.mem_singleton W.vacuum) ht (W.smul u j pc.1) γ hgr
              ((k : ℤ) + (-(pc.2.2 : ℤ) - 1) - j)
            refine (Gfil_antitone (adjointWeakModule W) ({W.vacuum} : Set V) ?_) hact
            simp only [wordLevel_cons]
            push_cast
            omega

/-- The nonnegative-mode one-step improvement for a homogeneous first input and an arbitrary
filtered second input. -/
private theorem homogeneous_smul_nonneg_mem_adjointGfil
    (W : VertexOperatorAlgebra V) {u : V} {bu : ℕ} (hu : u ∈ W.grading (bu : ℤ))
    (k : ℕ) {q : ℤ} {y : V}
    (hy : y ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) q) :
    W.smul u (k : ℤ) y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (q - (k : ℤ)) := by
  refine Submodule.span_induction
    (p := fun y _ => W.smul u (k : ℤ) y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (q - (k : ℤ))) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨l, w, hl, hw, hlev, rfl⟩
    simp only [Set.mem_singleton_iff] at hw
    subst w
    have hword := homogeneous_smul_nonneg_word_mem_adjointGfil W l hl hu k
    refine (Gfil_antitone (adjointWeakModule W) ({W.vacuum} : Set V) ?_) hword
    have hq : q.toNat ≤ wordLevel l := hlev
    omega
  · simpa only [PreVertexAlgebra.smul_zero_right] using
      (Submodule.zero_mem
        (Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (q - (k : ℤ))))
  · intro a b _ _ ha hb
    rw [PreVertexAlgebra.smul_add_right]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [PreVertexAlgebra.smul_smul_right]
    exact Submodule.smul_mem _ c ha

/-- The word-generator case of the one-step improved two-input estimate for nonnegative modes. -/
private theorem wordAct_smul_nonneg_mem_adjointGfil (W : VertexOperatorAlgebra V)
    (l : List (Letter V)) (hl : WordOK W l) {q : ℤ} {n : ℕ} {y : V}
    (hy : y ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) q) :
    W.smul (wordAct (adjointWeakModule W) l W.vacuum) (n : ℤ) y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V)
        ((wordLevel l : ℤ) + q - (n : ℤ)) := by
  induction l generalizing q n y with
  | nil =>
      simp only [wordAct_nil, wordLevel_nil, Nat.cast_zero, zero_add]
      rw [PreVertexAlgebra.smul_vacuum_left]
      rw [if_neg (by omega)]
      exact Submodule.zero_mem _
  | cons pc t ih =>
      obtain ⟨hpc, ht⟩ := WordOK_of_cons hl
      change W.smul
          (W.smul pc.1 (-(pc.2.2 : ℤ) - 1)
            (wordAct (adjointWeakModule W) t W.vacuum)) (n : ℤ) y ∈ _
      rw [VertexOperatorAlgebra.mode_iterate W]
      refine finsum_mem_submodule_lf _ _ (fun i => ?_)
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
      · have hinner := ih ht (q := q) (n := n + i) hy
        have hpre := Gfil_prepend (adjointWeakModule W) ({W.vacuum} : Set V)
          (n := pc.2.2 + i) hpc hinner
        have hidx : -(pc.2.2 : ℤ) - 1 - (i : ℤ) = -((pc.2.2 + i : ℕ) : ℤ) - 1 := by
          push_cast
          ring
        rw [hidx]
        change mode ((adjointWeakModule W).YM pc.1) (-((pc.2.2 + i : ℕ) : ℤ) - 1)
          (W.smul (wordAct (adjointWeakModule W) t W.vacuum) ((n + i : ℕ) : ℤ) y) ∈ _
        convert hpre using 1
        norm_num [wordLevel_cons]
        ring_nf
      · have ha := homogeneous_smul_nonneg_mem_adjointGfil W hpc i hy
        have hinner := wordAct_smul_mem_adjointGfil W (lwGenerated_adjoint W) t ht
          (q := q - (i : ℤ))
          (N := -(pc.2.2 : ℤ) - 1 + (n : ℤ) - (i : ℤ)) ha
        convert hinner using 1
        norm_num [wordLevel_cons]
        ring_nf

/-- The all-mode multiplicativity estimate for the adjoint Li filtration, with integer indices:
`F^p _{(N)} F^q ⊆ F^{p+q-N-1}`.  The explicit lowest-weight-generation hypothesis is the
only input needed by the underlying one-input estimate `act_mem_Gfil`. -/
theorem adjointGfil_smul_mem (W : VertexOperatorAlgebra V)
    (hLW : LWGenerated (adjointWeakModule W) ({W.vacuum} : Set V))
    {p q N : ℤ} {x y : V}
    (hx : x ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) p)
    (hy : y ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) q) :
    W.smul x N y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q - N - 1) := by
  refine Submodule.span_induction
    (p := fun x _ => W.smul x N y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q - N - 1)) ?_ ?_ ?_ ?_ hx
  · rintro z ⟨l, w, hl, hw, hlev, rfl⟩
    simp only [Set.mem_singleton_iff] at hw
    subst w
    have hword := wordAct_smul_mem_adjointGfil W hLW l hl (N := N) hy
    refine (Gfil_antitone (adjointWeakModule W) ({W.vacuum} : Set V) ?_) hword
    have hp : p.toNat ≤ wordLevel l := hlev
    omega
  · simpa only [PreVertexAlgebra.smul_zero_left] using
      (Submodule.zero_mem
        (Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q - N - 1)))
  · intro a b _ _ ha hb
    rw [PreVertexAlgebra.smul_add_left]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [PreVertexAlgebra.smul_smul_left]
    exact Submodule.smul_mem _ c ha

/-- The improved two-input estimate for nonnegative modes:
`F^p _{(n)} F^q ⊆ F^{p+q-n}` for `n ≥ 0`.

This is one Li step stronger than `adjointGfil_smul_mem`.  Its proof uses the ordinary
commutator formula to move a homogeneous nonnegative mode through the word representing the
second input, then the all-integer iterate formula to induct on the word representing the first
input. -/
theorem adjointGfil_smul_nonneg_mem (W : VertexOperatorAlgebra V) {p q : ℤ} (n : ℕ)
    {x y : V}
    (hx : x ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) p)
    (hy : y ∈ Gfil (adjointWeakModule W) ({W.vacuum} : Set V) q) :
    W.smul x (n : ℤ) y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q - (n : ℤ)) := by
  refine Submodule.span_induction
    (p := fun x _ => W.smul x (n : ℤ) y ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q - (n : ℤ))) ?_ ?_ ?_ ?_ hx
  · rintro z ⟨l, w, hl, hw, hlev, rfl⟩
    simp only [Set.mem_singleton_iff] at hw
    subst w
    have hword := wordAct_smul_nonneg_mem_adjointGfil W l hl (n := n) hy
    refine (Gfil_antitone (adjointWeakModule W) ({W.vacuum} : Set V) ?_) hword
    have hp : p.toNat ≤ wordLevel l := hlev
    omega
  · simpa only [PreVertexAlgebra.smul_zero_left] using
      (Submodule.zero_mem
        (Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q - (n : ℤ))))
  · intro a b _ _ ha hb
    rw [PreVertexAlgebra.smul_add_left]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [PreVertexAlgebra.smul_smul_left]
    exact Submodule.smul_mem _ c ha

/-- The `(-1)`-product adds Li degrees. -/
theorem liFiltration_smul_neg_one_mem (W : VertexOperatorAlgebra V) {p q : ℕ} {x y : V}
    (hx : x ∈ liFiltration W p) (hy : y ∈ liFiltration W q) :
    W.smul x (-1) y ∈ liFiltration W (p + q) := by
  have h := adjointGfil_smul_mem W (lwGenerated_adjoint W)
    (p := (p : ℤ)) (q := (q : ℤ)) (N := -1) hx hy
  simpa [liFiltration, adjointModule] using h

/-- A negative mode of depth `d` raises the total Li degree by `d`. -/
theorem liFiltration_smul_negSucc_mem (W : VertexOperatorAlgebra V)
    {p q : ℕ} (d : ℕ) {x y : V}
    (hx : x ∈ liFiltration W p) (hy : y ∈ liFiltration W q) :
    W.smul x (-(d : ℤ) - 1) y ∈ liFiltration W (p + q + d) := by
  have h := adjointGfil_smul_mem W (lwGenerated_adjoint W)
    (p := (p : ℤ)) (q := (q : ℤ)) (N := -(d : ℤ) - 1) hx hy
  convert h using 1
  norm_num [liFiltration, adjointModule]
  ring_nf

/-- For a nonnegative mode not exceeding the sum of the two Li degrees, the improved estimate is
expressed with natural-number Li indices. -/
theorem liFiltration_smul_nonneg_mem (W : VertexOperatorAlgebra V)
    {p q n : ℕ} (hn : n ≤ p + q) {x y : V}
    (hx : x ∈ liFiltration W p) (hy : y ∈ liFiltration W q) :
    W.smul x (n : ℤ) y ∈ liFiltration W (p + q - n) := by
  have h := adjointGfil_smul_nonneg_mem W n
    (p := (p : ℤ)) (q := (q : ℤ)) hx hy
  simpa only [liFiltration, adjointModule, Nat.cast_sub hn, Nat.cast_add] using h

/-- Translation raises Li degree by one. -/
theorem liFiltration_L_neg_one_mem (W : VertexOperatorAlgebra V) {p : ℕ} {x : V}
    (hx : x ∈ liFiltration W p) : W.L (-1) x ∈ liFiltration W (p + 1) := by
  have hvac : W.vacuum ∈ liFiltration W 0 := by
    exact mem_Gfil_of_mem_B (adjointWeakModule W) ({W.vacuum} : Set V)
      (Set.mem_singleton W.vacuum) (by norm_num)
  have h := adjointGfil_smul_mem W (lwGenerated_adjoint W) hx hvac (N := -2)
  rw [← VertexOperatorAlgebra.T_eq_Lneg1, PreVertexAlgebra.T_apply]
  convert h using 1
  norm_num [liFiltration, adjointModule]
  ring_nf

/-- The adjoint Li filtration is decreasing. -/
theorem liFiltration_antitone (W : VertexOperatorAlgebra V) {p q : ℕ} (hpq : p ≤ q) :
    liFiltration W q ≤ liFiltration W p := by
  exact Gfil_antitone (adjointWeakModule W) ({W.vacuum} : Set V) (by exact_mod_cast hpq)

/-- The degree-zero adjoint Li piece is the whole VOA. -/
theorem liFiltration_zero_eq_top (W : VertexOperatorAlgebra V) : liFiltration W 0 = ⊤ := by
  simpa only [liFiltration, adjointModule, LWGenerated] using lwGenerated_adjoint W

/-- Iterated translation raises Li degree by the number of translations. -/
theorem liFiltration_T_pow_mem (W : VertexOperatorAlgebra V) {p : ℕ} (j : ℕ) {x : V}
    (hx : x ∈ liFiltration W p) :
    (W.toPreVertexAlgebra.T ^ j) x ∈ liFiltration W (p + j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hTapply : W.toPreVertexAlgebra.T ((W.toPreVertexAlgebra.T ^ j) x) =
          W.L (-1) ((W.toPreVertexAlgebra.T ^ j) x) := by
        rw [VertexOperatorAlgebra.T_eq_Lneg1]
      rw [hTapply]
      have h := liFiltration_L_neg_one_mem W ih
      simpa only [Nat.add_assoc] using h

/-! ## The `(-1)`-product on finite fixed-weight layers -/

/-- The `(-1)`-product preserves both the sum of Li degrees and the sum of conformal weights. -/
theorem liWeightPiece_smul_neg_one_mem (W : VertexOperatorAlgebra V)
    {p q N M : ℕ} {x y : V} (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) :
    W.smul x (-1) y ∈ liWeightPiece W (p + q) (N + M) := by
  change x ∈ liFiltration W p ⊓ W.grading N at hx
  change y ∈ liFiltration W q ⊓ W.grading M at hy
  change W.smul x (-1) y ∈ liFiltration W (p + q) ⊓ W.grading (N + M)
  rw [Submodule.mem_inf] at hx hy ⊢
  refine ⟨liFiltration_smul_neg_one_mem W hx.1 hy.1, ?_⟩
  have hgr := W.smul_mem_grading hx.2 hy.2 (-1)
  convert hgr using 1
  norm_num

/-- The representative-level `(-1)`-product, already projected to the target Li layer. -/
noncomputable def liWeightPieceMul (W : VertexOperatorAlgebra V) (p q N M : ℕ) :
    liWeightPiece W p N →ₗ[ℂ]
      liWeightPiece W q M →ₗ[ℂ] liWeightLayer W (p + q) (N + M) where
  toFun x :=
    { toFun := fun y =>
        ((liWeightPiece W (p + q + 1) (N + M)).comap
          (liWeightPiece W (p + q) (N + M)).subtype).mkQ
            ⟨W.smul x.1 (-1) y.1,
              liWeightPiece_smul_neg_one_mem W x.property y.property⟩
      map_add' := fun y₁ y₂ => by
        apply congrArg ((liWeightPiece W (p + q + 1) (N + M)).comap
          (liWeightPiece W (p + q) (N + M)).subtype).mkQ
        ext
        exact W.smul_add_right x.1 (-1) y₁.1 y₂.1
      map_smul' := fun c y => by
        apply congrArg ((liWeightPiece W (p + q + 1) (N + M)).comap
          (liWeightPiece W (p + q) (N + M)).subtype).mkQ
        ext
        exact W.smul_smul_right x.1 c (-1) y.1 }
  map_add' x₁ x₂ := by
    refine LinearMap.ext fun y => ?_
    apply congrArg ((liWeightPiece W (p + q + 1) (N + M)).comap
      (liWeightPiece W (p + q) (N + M)).subtype).mkQ
    ext
    exact W.smul_add_left x₁.1 x₂.1 (-1) y.1
  map_smul' c x := by
    refine LinearMap.ext fun y => ?_
    apply congrArg ((liWeightPiece W (p + q + 1) (N + M)).comap
      (liWeightPiece W (p + q) (N + M)).subtype).mkQ
    ext
    exact W.smul_smul_left c x.1 (-1) y.1

private theorem liWeightPieceMul_right_ker (W : VertexOperatorAlgebra V) (p q N M : ℕ)
    (x : liWeightPiece W p N) :
    (liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype ≤
      LinearMap.ker (liWeightPieceMul W p q N M x) := by
  intro y hy
  rw [LinearMap.mem_ker, liWeightPieceMul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change W.smul x.1 (-1) y.1 ∈ liWeightPiece W (p + q + 1) (N + M)
  have hy' : y.1 ∈ liWeightPiece W (q + 1) M := by simpa using hy
  have hprod := liWeightPiece_smul_neg_one_mem W x.property hy'
  simpa only [Nat.add_assoc] using hprod

/-- For a representative of the first layer, multiplication descends through the second layer. -/
noncomputable def liWeightLayerMulRight (W : VertexOperatorAlgebra V) (p q N M : ℕ)
    (x : liWeightPiece W p N) :
    liWeightLayer W q M →ₗ[ℂ] liWeightLayer W (p + q) (N + M) :=
  ((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).liftQ
    (liWeightPieceMul W p q N M x) (liWeightPieceMul_right_ker W p q N M x)

/-- The partially descended product is linear in the remaining representative. -/
noncomputable def liWeightLayerMulLeft (W : VertexOperatorAlgebra V) (p q N M : ℕ) :
    liWeightPiece W p N →ₗ[ℂ]
      liWeightLayer W q M →ₗ[ℂ] liWeightLayer W (p + q) (N + M) where
  toFun := liWeightLayerMulRight W p q N M
  map_add' x₁ x₂ := by
    refine LinearMap.ext fun ybar => ?_
    refine Submodule.Quotient.induction_on _ ybar fun y => ?_
    change liWeightPieceMul W p q N M (x₁ + x₂) y =
      liWeightPieceMul W p q N M x₁ y + liWeightPieceMul W p q N M x₂ y
    exact LinearMap.congr_fun (map_add (liWeightPieceMul W p q N M) x₁ x₂) y
  map_smul' c x := by
    refine LinearMap.ext fun ybar => ?_
    refine Submodule.Quotient.induction_on _ ybar fun y => ?_
    change liWeightPieceMul W p q N M (c • x) y =
      c • liWeightPieceMul W p q N M x y
    exact LinearMap.congr_fun (map_smul (liWeightPieceMul W p q N M) c x) y

private theorem liWeightLayerMulLeft_ker (W : VertexOperatorAlgebra V) (p q N M : ℕ) :
    (liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype ≤
      LinearMap.ker (liWeightLayerMulLeft W p q N M) := by
  intro x hx
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun ybar => ?_
  refine Submodule.Quotient.induction_on _ ybar fun y => ?_
  change liWeightPieceMul W p q N M x y = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change W.smul x.1 (-1) y.1 ∈ liWeightPiece W (p + q + 1) (N + M)
  have hx' : x.1 ∈ liWeightPiece W (p + 1) N := by simpa using hx
  have hprod := liWeightPiece_smul_neg_one_mem W hx' y.property
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hprod

/-- The `(-1)`-product on exact fixed-weight Li layers.

This gives the bidegree `(p,N) * (q,M) → (p+q,N+M)` multiplication maps.  The results below prove
commutativity and associativity across propositionally equal target bidegrees, but do not yet
package the layers' direct sum into an algebra. -/
noncomputable def liWeightLayerMul (W : VertexOperatorAlgebra V) (p q N M : ℕ) :
    liWeightLayer W p N →ₗ[ℂ]
      liWeightLayer W q M →ₗ[ℂ] liWeightLayer W (p + q) (N + M) :=
  ((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).liftQ
    (liWeightLayerMulLeft W p q N M) (liWeightLayerMulLeft_ker W p q N M)

/-- Evaluation of the descended layer product on representatives. -/
@[simp] theorem liWeightLayerMul_mk (W : VertexOperatorAlgebra V) (p q N M : ℕ)
    (x : liWeightPiece W p N) (y : liWeightPiece W q M) :
    liWeightLayerMul W p q N M
        (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
        (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y) =
      ((liWeightPiece W (p + q + 1) (N + M)).comap
        (liWeightPiece W (p + q) (N + M)).subtype).mkQ
          ⟨W.smul x.1 (-1) y.1,
            liWeightPiece_smul_neg_one_mem W x.property y.property⟩ := by
  rfl

/-! ## The state-level commutator estimate -/

/-- The state-level one-step commutator estimate needed for commutativity of the Li associated
graded product.

The existing theorem `smul_comm_mem_Gfil` proves the corresponding one-step estimate for swapping
two homogeneous negative modes acting on a third vector.  The proof below instead combines
skew-symmetry with `adjointGfil_smul_nonneg_mem`; the generic all-mode theorem
`adjointGfil_smul_mem` alone is one Li step too weak for that route. -/
def LiNegOneCommutatorEstimate (W : VertexOperatorAlgebra V) : Prop :=
  ∀ {p q : ℕ} {x y : V}, x ∈ liFiltration W p → y ∈ liFiltration W q →
    W.smul x (-1) y - W.smul y (-1) x ∈ liFiltration W (p + q + 1)

/-- Every positive-index summand in the skew-mode expansion of the `(-1)`-product lies one
Li step above the product degree. -/
private theorem skew_neg_one_summand_mem_next (W : VertexOperatorAlgebra V)
    {p q : ℕ} {x y : V} (hx : x ∈ liFiltration W p) (hy : y ∈ liFiltration W q)
    (j : ℕ) (hj : j ≠ 0) :
    ((j.factorial : ℂ)⁻¹) • (sgn (-(-1 : ℤ) - 1 - (j : ℤ))) •
        ((W.toPreVertexAlgebra.T ^ j) ((W.Y y) (-(-1 : ℤ) - 1 - (j : ℤ)) x)) ∈
      liFiltration W (p + q + 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
  rw [show -(-1 : ℤ) - 1 - (Nat.succ r : ℤ) = -(r : ℤ) - 1 by push_cast; ring]
  change (W.toPreVertexAlgebra.T ^ Nat.succ r) (W.smul y (r : ℤ) x) ∈
    liFiltration W (p + q + 1)
  by_cases hr : r ≤ p + q
  · have hr' : r ≤ q + p := by omega
    have hmode := liFiltration_smul_nonneg_mem W (p := q) (q := p) hr' hy hx
    have hT := liFiltration_T_pow_mem W (r + 1) hmode
    have hdeg : q + p - r + (r + 1) = p + q + 1 := by omega
    rw [hdeg] at hT
    exact hT
  · have htop : liFiltration W 0 = ⊤ := by
      simpa only [liFiltration, adjointModule, LWGenerated] using lwGenerated_adjoint W
    have hmode : W.smul y (r : ℤ) x ∈ liFiltration W 0 := by
      rw [htop]
      exact Submodule.mem_top
    have hT := liFiltration_T_pow_mem W (r + 1) hmode
    exact liFiltration_antitone W (by omega) hT

/-- The one-step commutator estimate follows from the improved nonnegative-mode bound and
skew-symmetry. -/
theorem liNegOneCommutatorEstimate_proven (W : VertexOperatorAlgebra V) :
    LiNegOneCommutatorEstimate W := by
  intro p q x y hx hy
  let f : ℕ → V := fun j =>
    ((j.factorial : ℂ)⁻¹) • (sgn (-(-1 : ℤ) - 1 - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y y) (-(-1 : ℤ) - 1 - (j : ℤ)) x))
  have hskew : W.smul x (-1) y = ∑ᶠ j : ℕ, f j := by
    simpa only [f] using W.skew_mode x y (-1)
  have hf0 : f 0 = W.smul y (-1) x := by
    simp only [f, Nat.factorial_zero, Nat.cast_one, inv_one, neg_neg, one_smul, Nat.cast_zero,
      sub_zero, pow_zero, Module.End.one_apply]
    norm_num [sgn, PreVertexAlgebra.smul_def]
  have hfin : (Function.support f).Finite := by
    simpa only [f, neg_neg] using W.skew_support_finite x y 0
  let s : Finset ℕ := hfin.toFinset.erase 0
  have hsupp : Function.support f ⊆ (↑(insert 0 s) : Set ℕ) := by
    intro j hj
    change j ∈ insert 0 s
    rw [Finset.mem_insert]
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    · refine Or.inr ?_
      change j ∈ hfin.toFinset.erase 0
      rw [Finset.mem_erase]
      exact ⟨hj0, hfin.mem_toFinset.mpr hj⟩
  rw [hskew, finsum_eq_finsetSum_of_support_subset f hsupp,
    Finset.sum_insert (Finset.notMem_erase 0 hfin.toFinset), hf0]
  rw [add_sub_cancel_left]
  refine Submodule.sum_mem _ (fun j hj => ?_)
  exact skew_neg_one_summand_mem_next W hx hy j (Finset.ne_of_mem_erase hj)

/-- Under the exact commutator gate, the difference of the two products lies in the next
fixed-weight Li piece. -/
theorem liWeightPiece_neg_one_comm_mem (W : VertexOperatorAlgebra V)
    (hcomm : LiNegOneCommutatorEstimate W) {p q N M : ℕ}
    {x y : V} (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    W.smul x (-1) y - W.smul y (-1) x ∈
      liWeightPiece W (p + q + 1) (N + M) := by
  change x ∈ liFiltration W p ⊓ W.grading N at hx
  change y ∈ liFiltration W q ⊓ W.grading M at hy
  change W.smul x (-1) y - W.smul y (-1) x ∈
    liFiltration W (p + q + 1) ⊓ W.grading (N + M)
  rw [Submodule.mem_inf] at hx hy ⊢
  refine ⟨hcomm hx.1 hy.1, ?_⟩
  exact Submodule.sub_mem _
    (liWeightPiece_smul_neg_one_mem W hx hy).2
    (by
      have h := (liWeightPiece_smul_neg_one_mem W hy hx).2
      simpa only [Nat.add_comm] using h)

/-- The commutator gate identifies the two representative products in the common target layer. -/
theorem liWeightLayerMul_mk_eq_swap_of_commutator (W : VertexOperatorAlgebra V)
    (hcomm : LiNegOneCommutatorEstimate W) (p q N M : ℕ)
    (x : liWeightPiece W p N) (y : liWeightPiece W q M) :
    liWeightLayerMul W p q N M
        (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
        (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y) =
      ((liWeightPiece W (p + q + 1) (N + M)).comap
        (liWeightPiece W (p + q) (N + M)).subtype).mkQ
          ⟨W.smul y.1 (-1) x.1, by
            have h := liWeightPiece_smul_neg_one_mem W y.property x.property
            simpa only [Nat.add_comm] using h⟩ := by
  rw [liWeightLayerMul_mk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  exact liWeightPiece_neg_one_comm_mem W hcomm x.property y.property

private theorem liWeightLayer_mk_heq_of_indices_eq (W : VertexOperatorAlgebra V)
    {a b c d : ℕ} (hac : a = c) (hbd : b = d) {z : V}
    (hz : z ∈ liWeightPiece W a b) (hz' : z ∈ liWeightPiece W c d) :
    HEq
      (((liWeightPiece W (a + 1) b).comap (liWeightPiece W a b).subtype).mkQ ⟨z, hz⟩)
      (((liWeightPiece W (c + 1) d).comap (liWeightPiece W c d).subtype).mkQ ⟨z, hz'⟩) := by
  subst c
  subst d
  rfl

/-- Commutativity of the `(-1)`-product on finite fixed-weight Li layers.  `HEq` is used only
because the two displayed products have propositionally, rather than definitionally, equal target
indices `(p+q,N+M)` and `(q+p,M+N)`. -/
theorem liWeightLayerMul_comm (W : VertexOperatorAlgebra V) (p q N M : ℕ)
    (xbar : liWeightLayer W p N) (ybar : liWeightLayer W q M) :
    HEq (liWeightLayerMul W p q N M xbar ybar)
      (liWeightLayerMul W q p M N ybar xbar) := by
  refine Submodule.Quotient.induction_on _ xbar fun x => ?_
  refine Submodule.Quotient.induction_on _ ybar fun y => ?_
  change HEq
    (liWeightLayerMul W p q N M
      (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
      (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y))
    (liWeightLayerMul W q p M N
      (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y)
      (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x))
  have h := liWeightLayerMul_mk_eq_swap_of_commutator W
    (liNegOneCommutatorEstimate_proven W) p q N M x y
  rw [liWeightLayerMul_mk, liWeightLayerMul_mk]
  rw [liWeightLayerMul_mk] at h
  rw [h]
  exact liWeightLayer_mk_heq_of_indices_eq W (Nat.add_comm p q) (Nat.add_comm N M) _ _

/-! ## The state-level associator estimate -/

/-- The first iterate family, away from its leading term, lies one Li step above the total
product degree. -/
private theorem liAssoc_first_mem_next (W : VertexOperatorAlgebra V)
    {p q r : ℕ} {x y z : V} (hx : x ∈ liFiltration W p)
    (hy : y ∈ liFiltration W q) (hz : z ∈ liFiltration W r)
    (i : ℕ) (hi : i ≠ 0) :
    W.smul x (-1 - (i : ℤ)) (W.smul y (-1 + (i : ℤ)) z) ∈
      liFiltration W (p + q + r + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [show -1 + (Nat.succ j : ℤ) = (j : ℤ) by push_cast; ring,
    show -1 - (Nat.succ j : ℤ) = -(Nat.succ j : ℤ) - 1 by ring]
  by_cases hj : j ≤ q + r
  · have hinner := liFiltration_smul_nonneg_mem W hj hy hz
    have houter := liFiltration_smul_negSucc_mem W (Nat.succ j) hx hinner
    have hdeg : p + (q + r - j) + Nat.succ j = p + q + r + 1 := by omega
    rw [hdeg] at houter
    exact houter
  · have hinner : W.smul y (j : ℤ) z ∈ liFiltration W 0 := by
      rw [liFiltration_zero_eq_top]
      exact Submodule.mem_top
    have houter := liFiltration_smul_negSucc_mem W (Nat.succ j) hx hinner
    exact liFiltration_antitone W (by omega) houter

/-- Every term in the second iterate family lies one Li step above the total product degree. -/
private theorem liAssoc_second_mem_next (W : VertexOperatorAlgebra V)
    {p q r : ℕ} {x y z : V} (hx : x ∈ liFiltration W p)
    (hy : y ∈ liFiltration W q) (hz : z ∈ liFiltration W r) (i : ℕ) :
    W.smul y (-1 + -1 - (i : ℤ)) (W.smul x (i : ℤ) z) ∈
      liFiltration W (p + q + r + 1) := by
  rw [show -1 + -1 - (i : ℤ) = -((i + 1 : ℕ) : ℤ) - 1 by push_cast; ring]
  by_cases hi : i ≤ p + r
  · have hinner := liFiltration_smul_nonneg_mem W hi hx hz
    have houter := liFiltration_smul_negSucc_mem W (i + 1) hy hinner
    have hdeg : q + (p + r - i) + (i + 1) = p + q + r + 1 := by omega
    rw [hdeg] at houter
    exact houter
  · have hinner : W.smul x (i : ℤ) z ∈ liFiltration W 0 := by
      rw [liFiltration_zero_eq_top]
      exact Submodule.mem_top
    have houter := liFiltration_smul_negSucc_mem W (i + 1) hy hinner
    exact liFiltration_antitone W (by omega) houter

/-- The iterate summand for the associator of three `(-1)`-products. -/
private noncomputable def liAssocTerm (W : VertexOperatorAlgebra V)
    (x y z : V) (i : ℕ) : V :=
  ((-1 : ℂ) ^ i * gBinom (-1 : ℤ) i) •
    (W.smul x (-1 - (i : ℤ)) (W.smul y (-1 + (i : ℤ)) z)
      - ((-1 : ℂ) ^ (-1 : ℤ)) •
          W.smul y (-1 + -1 - (i : ℤ)) (W.smul x (i : ℤ) z))

private theorem liAssoc_mode_iterate (W : VertexOperatorAlgebra V) (x y z : V) :
    W.smul (W.smul x (-1) y) (-1) z = ∑ᶠ i : ℕ, liAssocTerm W x y z i :=
  VertexOperatorAlgebra.mode_iterate W x y (-1) (-1) z

private theorem liAssocTerm_support_finite (W : VertexOperatorAlgebra V) (x y z : V) :
    (Function.support (liAssocTerm W x y z)).Finite := by
  obtain ⟨Ny, hNy⟩ := W.regularity y z
  obtain ⟨Nx, hNx⟩ := W.regularity x z
  apply Set.Finite.subset (Set.finite_Icc 0 (max (Ny + 1) Nx).toNat)
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  rw [not_le] at hbig
  apply hi
  simp only [liAssocTerm]
  have hA : W.smul y (-1 + (i : ℤ)) z = 0 := hNy (-1 + (i : ℤ)) (by
    have h1 : Ny + 1 ≤ max (Ny + 1) Nx := le_max_left _ _
    omega)
  have hB : W.smul x (i : ℤ) z = 0 := hNx (i : ℤ) (by
    have h1 : Nx ≤ max (Ny + 1) Nx := le_max_right _ _
    omega)
  rw [hA, hB, PreVertexAlgebra.smul_zero_right, PreVertexAlgebra.smul_zero_right, smul_zero,
    sub_zero, smul_zero]

/-- Subtracting the leading nested product from an iterate summand always leaves an element one
Li step above the total product degree. -/
private theorem liAssocTerm_sub_leading_mem_next (W : VertexOperatorAlgebra V)
    {p q r : ℕ} {x y z : V} (hx : x ∈ liFiltration W p)
    (hy : y ∈ liFiltration W q) (hz : z ∈ liFiltration W r) (i : ℕ) :
    liAssocTerm W x y z i -
        (if i = 0 then W.smul x (-1) (W.smul y (-1) z) else 0) ∈
      liFiltration W (p + q + r + 1) := by
  simp only [liAssocTerm]
  by_cases hi : i = 0
  · subst i
    rw [if_pos rfl]
    have hc0 : ((-1 : ℂ) ^ (0 : ℕ) * gBinom (-1 : ℤ) 0) = 1 := by
      simp only [pow_zero, gBinom_zero, mul_one]
    rw [hc0, one_smul]
    simp only [Nat.cast_zero, sub_zero, add_zero]
    rw [show ((-1 : ℤ) + -1) = (-2 : ℤ) by norm_num]
    rw [show W.smul x (-1) (W.smul y (-1) z)
          - ((-1 : ℂ) ^ (-1 : ℤ)) • W.smul y (-2) (W.smul x 0 z)
          - W.smul x (-1) (W.smul y (-1) z) =
        -(((-1 : ℂ) ^ (-1 : ℤ)) • W.smul y (-2) (W.smul x 0 z)) by abel]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _
      (liAssoc_second_mem_next W hx hy hz 0))
  · rw [if_neg hi, sub_zero]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (liAssoc_first_mem_next W hx hy hz i hi)
      (Submodule.smul_mem _ _ (liAssoc_second_mem_next W hx hy hz i)))

/-- The state-level one-step associator estimate needed for associativity of the Li associated
graded product. -/
def LiNegOneAssociatorEstimate (W : VertexOperatorAlgebra V) : Prop :=
  ∀ {p q r : ℕ} {x y z : V},
    x ∈ liFiltration W p → y ∈ liFiltration W q → z ∈ liFiltration W r →
      W.smul (W.smul x (-1) y) (-1) z -
          W.smul x (-1) (W.smul y (-1) z) ∈ liFiltration W (p + q + r + 1)

/-- The iterate formula and the improved nonnegative-mode estimate prove the one-step
associator estimate. -/
theorem liNegOneAssociatorEstimate_proven (W : VertexOperatorAlgebra V) :
    LiNegOneAssociatorEstimate W := by
  intro p q r x y z hx hy hz
  rw [liAssoc_mode_iterate W x y z]
  have hRHS : W.smul x (-1) (W.smul y (-1) z) =
      ∑ᶠ i : ℕ, if i = 0 then W.smul x (-1) (W.smul y (-1) z) else 0 := by
    rw [finsum_eq_single _ 0 (fun j hj => if_neg hj), if_pos rfl]
  rw [hRHS, ← finsum_sub_distrib (liAssocTerm_support_finite W x y z)
    (by
      apply Set.Finite.subset (Set.finite_singleton 0)
      intro i hi
      rw [Function.mem_support] at hi
      by_contra hc
      rw [Set.mem_singleton_iff] at hc
      exact hi (if_neg hc))]
  exact finsum_mem_submodule_lf _ _
    (fun i => liAssocTerm_sub_leading_mem_next W hx hy hz i)

/-- Under the associator estimate, the difference of the two nested products lies in the next
fixed-weight Li piece. -/
theorem liWeightPiece_neg_one_assoc_mem (W : VertexOperatorAlgebra V)
    (hassoc : LiNegOneAssociatorEstimate W) {p q r N M K : ℕ}
    {x y z : V} (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M)
    (hz : z ∈ liWeightPiece W r K) :
    W.smul (W.smul x (-1) y) (-1) z - W.smul x (-1) (W.smul y (-1) z) ∈
      liWeightPiece W (p + q + r + 1) (N + M + K) := by
  change x ∈ liFiltration W p ⊓ W.grading N at hx
  change y ∈ liFiltration W q ⊓ W.grading M at hy
  change z ∈ liFiltration W r ⊓ W.grading K at hz
  change W.smul (W.smul x (-1) y) (-1) z - W.smul x (-1) (W.smul y (-1) z) ∈
    liFiltration W (p + q + r + 1) ⊓ W.grading (N + M + K)
  rw [Submodule.mem_inf] at hx hy hz ⊢
  refine ⟨hassoc hx.1 hy.1 hz.1, ?_⟩
  have hxy := liWeightPiece_smul_neg_one_mem W hx hy
  have hyz := liWeightPiece_smul_neg_one_mem W hy hz
  have hleft := (liWeightPiece_smul_neg_one_mem W hxy hz).2
  have hright := (liWeightPiece_smul_neg_one_mem W hx hyz).2
  exact Submodule.sub_mem _ hleft
    (by
      have hidx : (↑N + ↑M + ↑K : ℤ) = ↑(N + (M + K)) := by omega
      rw [hidx]
      exact hright)

/-- Evaluation of finite-layer associativity on representatives, with the right-nested product
written in the common left-associated target bidegree. -/
theorem liWeightLayerMul_assoc_mk_eq (W : VertexOperatorAlgebra V)
    (p q r N M K : ℕ) (x : liWeightPiece W p N) (y : liWeightPiece W q M)
    (z : liWeightPiece W r K) :
    liWeightLayerMul W (p + q) r (N + M) K
        (liWeightLayerMul W p q N M
          (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
          (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y))
        (((liWeightPiece W (r + 1) K).comap (liWeightPiece W r K).subtype).mkQ z) =
      ((liWeightPiece W (p + q + r + 1) (N + M + K)).comap
        (liWeightPiece W (p + q + r) (N + M + K)).subtype).mkQ
          ⟨W.smul x.1 (-1) (W.smul y.1 (-1) z.1), by
            have hyz := liWeightPiece_smul_neg_one_mem W y.property z.property
            have h := liWeightPiece_smul_neg_one_mem W x.property hyz
            simpa only [Nat.add_assoc] using h⟩ := by
  rw [liWeightLayerMul_mk, liWeightLayerMul_mk]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact liWeightPiece_neg_one_assoc_mem W (liNegOneAssociatorEstimate_proven W)
    x.property y.property z.property

/-- Associativity of the `(-1)`-product on finite fixed-weight Li layers.  As for commutativity,
`HEq` records only the propositionally equal target bidegrees. -/
theorem liWeightLayerMul_assoc (W : VertexOperatorAlgebra V) (p q r N M K : ℕ)
    (xbar : liWeightLayer W p N) (ybar : liWeightLayer W q M)
    (zbar : liWeightLayer W r K) :
    HEq
      (liWeightLayerMul W (p + q) r (N + M) K
        (liWeightLayerMul W p q N M xbar ybar) zbar)
      (liWeightLayerMul W p (q + r) N (M + K) xbar
        (liWeightLayerMul W q r M K ybar zbar)) := by
  refine Submodule.Quotient.induction_on _ xbar fun x => ?_
  refine Submodule.Quotient.induction_on _ ybar fun y => ?_
  refine Submodule.Quotient.induction_on _ zbar fun z => ?_
  change HEq
    (liWeightLayerMul W (p + q) r (N + M) K
      (liWeightLayerMul W p q N M
        (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
        (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y))
      (((liWeightPiece W (r + 1) K).comap (liWeightPiece W r K).subtype).mkQ z))
    (liWeightLayerMul W p (q + r) N (M + K)
      (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ x)
      (liWeightLayerMul W q r M K
        (((liWeightPiece W (q + 1) M).comap (liWeightPiece W q M).subtype).mkQ y)
        (((liWeightPiece W (r + 1) K).comap (liWeightPiece W r K).subtype).mkQ z)))
  have h := liWeightLayerMul_assoc_mk_eq W p q r N M K x y z
  rw [h, liWeightLayerMul_mk, liWeightLayerMul_mk]
  exact liWeightLayer_mk_heq_of_indices_eq W (Nat.add_assoc p q r)
    (Nat.add_assoc N M K) _ _

end LiMultiplicativity

end VOA
