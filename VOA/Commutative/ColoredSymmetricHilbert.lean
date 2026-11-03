/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.BlockSymmetricWeightedDegree

/-! # Hilbert series of polynomials invariant within arbitrary finite color fibers -/
namespace VOA.ColoredSymmetricHilbert
open MvPolynomial IteratedBlockSymmetricInvariant BlockSymmetricWeightedDegree
noncomputable section
variable {K : Type*} [Field K]

/-- Split a dependent sigma type over `Fin (n+1)` into its head fiber and tail sigma type. -/
def finSuccSigmaEquiv {n : ℕ} (rho : Fin (n + 1) → ℕ) :
    Fin (rho 0) ⊕ (Σ c : Fin n, Fin (rho c.succ)) ≃
      Σ c : Fin (n + 1), Fin (rho c) where
  toFun
    | Sum.inl i => ⟨0, i⟩
    | Sum.inr ⟨c, i⟩ => ⟨c.succ, i⟩
  invFun x := Fin.cases (fun i ↦ Sum.inl i)
    (fun c i ↦ Sum.inr ⟨c, i⟩) x.1 x.2
  left_inv x := by
    rcases x with i | ⟨c, i⟩ <;> rfl
  right_inv x := by
    rcases x with ⟨c, i⟩
    cases c using Fin.cases <;> rfl

def profileBlocks : {n : ℕ} → (Fin n → ℕ) → List ℕ
  | 0, _ => []
  | _+1, rho => rho 0 :: profileBlocks (fun c => rho c.succ)

theorem profileBlocks_eq_ofFn {n : ℕ} (rho : Fin n → ℕ) :
    profileBlocks rho = List.ofFn rho := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [profileBlocks, List.ofFn_succ, ih]

def profileBlockSlotEquiv : {n : ℕ} → (rho : Fin n → ℕ) →
    BlockSlots (profileBlocks rho) ≃ (Σ c : Fin n, Fin (rho c))
  | 0, _ =>
      { toFun := fun i => Fin.elim0 i
        invFun := fun x => Fin.elim0 x.1
        left_inv := fun i => Fin.elim0 i
        right_inv := fun x => Fin.elim0 x.1 }
  | n+1, rho => (Equiv.sumCongr (Equiv.refl (Fin (rho 0)))
      (profileBlockSlotEquiv (fun c : Fin n => rho c.succ))).trans
        (finSuccSigmaEquiv rho)

def profileBlockRelabelingEquiv : {n : ℕ} → (rho : Fin n → ℕ) →
    BlockRelabeling (profileBlocks rho) ≃ (∀ c, Equiv.Perm (Fin (rho c)))
  | 0, _ =>
      { toFun := fun _ c => Fin.elim0 c
        invFun := fun _ => PUnit.unit
        left_inv := fun x => by cases x; rfl
        right_inv := fun f => by funext c; exact Fin.elim0 c }
  | n+1, rho => (Equiv.prodCongr (Equiv.refl (Equiv.Perm (Fin (rho 0))))
      (profileBlockRelabelingEquiv (fun c : Fin n => rho c.succ))).trans
        (Fin.consEquiv fun c : Fin (n+1) => Equiv.Perm (Fin (rho c)))

/-- Slot reindexing intertwines the actual independent permutations. -/
theorem profileBlockSlotEquiv_action {n : ℕ} (rho : Fin n → ℕ)
    (h : BlockRelabeling (profileBlocks rho)) (i : BlockSlots (profileBlocks rho)) :
    profileBlockSlotEquiv rho (blockAction _ h i) =
      (Equiv.sigmaCongrRight (profileBlockRelabelingEquiv rho h))
        (profileBlockSlotEquiv rho i) := by
  induction n with
  | zero => exact Fin.elim0 (show Fin 0 from i)
  | succ n ih =>
    rcases i with i | i
    · rfl
    · exact congrArg (fun x : Σ c : Fin n, Fin (rho c.succ) =>
          (⟨x.1.succ, x.2⟩ : Σ c : Fin (n+1), Fin (rho c)))
          (ih (fun c => rho c.succ) h.2 i)


/-- Homogeneous polynomials fixed by a specified concrete permutation family. -/
def actionPiece {η A : Type*} (act : A → Equiv.Perm η) (d : ℕ) :
    Submodule K (MvPolynomial η K) where
  carrier := {p | (∀ a, rename (act a) p = p) ∧ p.IsHomogeneous d}
  zero_mem' := ⟨by simp, isHomogeneous_zero _ _ _⟩
  add_mem' hp hq := ⟨fun a => by rw [map_add, hp.1 a, hq.1 a], hp.2.add hq.2⟩
  smul_mem' c p hp := ⟨fun a => by simp [hp.1 a], (homogeneousSubmodule η K d).smul_mem c hp.2⟩

theorem rename_intertwine {η ζ : Type*} (e : η ≃ ζ)
    (a : Equiv.Perm η) (b : Equiv.Perm ζ) (h : ∀ i, e (a i) = b (e i))
    (p : MvPolynomial η K) : rename b (rename e p) = rename e (rename a p) := by
  simp only [rename_rename]
  congr 2
  funext i
  exact (h i).symm

/-- Relabeling variables and the permutation family preserves every degree piece. -/
def actionPieceEquiv {η ζ A B : Type*} (a : A → Equiv.Perm η)
    (b : B → Equiv.Perm ζ) (e : η ≃ ζ) (g : A ≃ B)
    (h : ∀ t i, e (a t i) = b (g t) (e i)) (d : ℕ) :
    actionPiece (K := K) a d ≃ₗ[K] actionPiece (K := K) b d where
  toFun p := ⟨rename e p.val, by
    constructor
    · intro t
      have hi := rename_intertwine e (a (g.symm t)) (b t)
        (by simpa using h (g.symm t)) p.val
      rw [hi, p.property.1]
    · exact p.property.2.rename_isHomogeneous⟩
  invFun p := ⟨rename e.symm p.val, by
    constructor
    · intro t
      have hi := rename_intertwine e.symm (b (g t)) (a t) (by
        intro i
        apply e.injective
        simpa using (h t (e.symm i)).symm) p.val
      rw [hi, p.property.1]
    · exact p.property.2.rename_isHomogeneous⟩
  left_inv p := by apply Subtype.ext; exact (renameEquiv K e).left_inv p.val
  right_inv p := by apply Subtype.ext; exact (renameEquiv K e).right_inv p.val
  map_add' p q := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c p := by apply Subtype.ext; exact map_smul _ _ _

/-- Exact Hilbert coefficient for a dependent list of finite color fibers. -/
theorem finColorPiece_finrank_eq_coeff {n : ℕ} (rho : Fin n → ℕ) (d : ℕ) :
    (Module.finrank K (actionPiece (K := K)
      (fun h : ∀ c, Equiv.Perm (Fin (rho c)) => Equiv.sigmaCongrRight h) d) : ℚ) =
      PowerSeries.coeff d (∏ c, (QSeries.reciprocalQFactorial (rho c) : PowerSeries ℚ)) := by
  have he := (actionPieceEquiv (K := K) (blockAction (profileBlocks rho))
    (fun h : ∀ c, Equiv.Perm (Fin (rho c)) => Equiv.sigmaCongrRight h)
    (profileBlockSlotEquiv rho) (profileBlockRelabelingEquiv rho)
    (profileBlockSlotEquiv_action rho) d).finrank_eq
  have hp : actionPiece (K := K) (blockAction (profileBlocks rho)) d =
      blockInvariantPiece (K := K) (profileBlocks rho) d := by rfl
  rw [hp] at he
  rw [← he, blockInvariantPiece_finrank_eq_coeff, profileBlocks_eq_ofFn]
  simp [List.prod_ofFn]


/-- Fiberwise polynomial invariants are unchanged by finite reindexing of
both the colors and their actual variable sets. -/
def sigmaActionPieceEquiv {ι κ : Type*} {η : ι → Type*} {ζ : κ → Type*}
    (e : ι ≃ κ) (f : ∀ c, η c ≃ ζ (e c)) (d : ℕ) :
    actionPiece (K := K) (fun h : ∀ c, Equiv.Perm (η c) => Equiv.sigmaCongrRight h) d ≃ₗ[K]
      actionPiece (K := K) (fun h : ∀ c, Equiv.Perm (ζ c) => Equiv.sigmaCongrRight h) d :=
  actionPieceEquiv _ _ (Equiv.sigmaCongr e f)
    (Equiv.piCongr e (fun c => (f c).permCongr)) (by
      intro h i
      rcases i with ⟨c, i⟩
      simp [Equiv.sigmaCongr, Equiv.sigmaCongrLeft, Equiv.permCongr_apply]) d

/-- Exact dimensions of invariants in an arbitrary finite dependent family
of finite variable sets. -/
theorem sigmaPiece_finrank_eq_coeff {κ : Type*} [Fintype κ]
    (η : κ → Type*) [∀ c, Fintype (η c)] (d : ℕ) :
    (Module.finrank K (actionPiece (K := K)
      (fun h : ∀ c, Equiv.Perm (η c) => Equiv.sigmaCongrRight h) d) : ℚ) =
      PowerSeries.coeff d (∏ c, (QSeries.reciprocalQFactorial (Fintype.card (η c)) :
        PowerSeries ℚ)) := by
  let e := (Fintype.equivFin κ).symm
  let rho : Fin (Fintype.card κ) → ℕ := fun c => Fintype.card (η (e c))
  have he := (sigmaActionPieceEquiv (K := K) e
    (fun c => (Fintype.equivFin (η (e c))).symm) d).finrank_eq
  rw [← he, finColorPiece_finrank_eq_coeff]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)


/-- The genuine group of all permutations preserving a variable's color. -/
def ColorPermutation {η κ : Type*} (color : η → κ) :=
  {e : Equiv.Perm η // ∀ i, color (e i) = color i}

/-- Every color-preserving permutation restricts to a permutation of each fiber. -/
def fiberPermutation {η κ : Type*} (color : η → κ) (e : ColorPermutation color) (c : κ) :
    Equiv.Perm {i // color i = c} where
  toFun i := ⟨e.val i.val, (e.property i.val).trans i.property⟩
  invFun i := ⟨e.val.symm i.val, by
    rw [← e.property (e.val.symm i.val), Equiv.apply_symm_apply]
    exact i.property⟩
  left_inv i := by apply Subtype.ext; exact e.val.symm_apply_apply i.val
  right_inv i := by apply Subtype.ext; exact e.val.apply_symm_apply i.val

/-- Independent fiber permutations are precisely all color-preserving permutations. -/
def colorPermutationEquiv {η κ : Type*} (color : η → κ) :
    (∀ c, Equiv.Perm {i // color i = c}) ≃ ColorPermutation color where
  toFun h := ⟨(Equiv.sigmaFiberEquiv color).permCongr (Equiv.sigmaCongrRight h),
    fun i => (h (color i) ⟨i, rfl⟩).property⟩
  invFun e := fiberPermutation color e
  left_inv h := by
    funext c
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change (h (color i.val) ⟨i.val, rfl⟩).val = (h c i).val
    cases i with
    | mk i hi => subst c; rfl
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rfl

/-- Actual color-invariant homogeneous polynomials, with no chosen enumeration. -/
def coloredInvariantPiece {η κ : Type*} (color : η → κ) (d : ℕ) :
    Submodule K (MvPolynomial η K) :=
  actionPiece (fun e : ColorPermutation color => e.val) d

/-- Exact Hilbert series coefficient for all permutations preserving any finite color map. -/
theorem coloredInvariantPiece_finrank_eq_coeff {η κ : Type*} [Fintype η] [Fintype κ]
    (color : η → κ) (d : ℕ) :
    (Module.finrank K (coloredInvariantPiece (K := K) color d) : ℚ) =
      PowerSeries.coeff d (∏ c, (QSeries.reciprocalQFactorial
        (Nat.card {i // color i = c}) : PowerSeries ℚ)) := by
  classical
  have he := (actionPieceEquiv (K := K)
    (fun h : ∀ c, Equiv.Perm {i // color i = c} => Equiv.sigmaCongrRight h)
    (fun e : ColorPermutation color => e.val)
    (Equiv.sigmaFiberEquiv color) (colorPermutationEquiv color) (by
      intro h i
      rcases i with ⟨c, i, hi⟩
      subst c
      rfl) d).finrank_eq
  calc
    _ = (Module.finrank K (actionPiece (K := K)
        (fun h : ∀ c, Equiv.Perm {i // color i = c} => Equiv.sigmaCongrRight h) d) : ℚ) :=
      congrArg (fun n : ℕ => (n : ℚ)) he.symm
    _ = _ := by
      simpa only [Nat.card_eq_fintype_card] using
        sigmaPiece_finrank_eq_coeff (K := K) (fun c => {i // color i = c}) d

end
end VOA.ColoredSymmetricHilbert
