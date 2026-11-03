import VOA.Huang.GenusOneWardTrace

/-!
# The Ward relations of the level-indexed traces

q-graded cyclicity moves the boundary mode around the trace; the commutator
formula for both intertwining operators produces the descendant traces; the
Jacobi iterate formula expands the minus-one descendant. All identities are
between finite-dimensional traces at fixed levels.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.QEquation (TailBound)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section Rel
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
  {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier} {c : V} {kc : ℤ}

/-- Linearity of a level trace. -/
theorem lvl_sub (T T' : Module.End ℂ N.carrier) (m : ℤ) :
    lvl N (T - T') m = lvl N T m - lvl N T' m := by
  simp only [lvl, gradedTraceOp_sub, Pi.sub_apply]

theorem lvl_add (T T' : Module.End ℂ N.carrier) (m : ℤ) :
    lvl N (T + T') m = lvl N T m + lvl N T' m := by
  simp only [lvl, gradedTraceOp_add, Pi.add_apply]

theorem lvl_sum {ι : Type*} (s : Finset ι) (T : ι → Module.End ℂ N.carrier) (m : ℤ) :
    lvl N (∑ i ∈ s, T i) m = ∑ i ∈ s, lvl N (T i) m := by
  simp only [lvl]
  have h := map_sum (gradedTraceAt N.isMod (N.h - W.centralCharge / 24 + m)) T s
  simpa only [gradedTraceAt_apply] using h

theorem lvl_smul (a : ℂ) (T : Module.End ℂ N.carrier) (m : ℤ) :
    lvl N (a • T) m = a * lvl N T m := by
  simp only [lvl, gradedTraceOp_smul, Pi.smul_apply, smul_eq_mul]

/-- The two-insertion block shifts the weight by `−d`. -/
theorem weightShift_block (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (n k : ℤ) (d : ℂ) :
    WeightShift N.isMod ((Y₁.val (sMode N Q α₁ n k + d) x).comp (Y₂.val (rMode N Q α₂ n k) y))
      (-d) := by
  intro β v hv
  have h₂ := FusionTop.mem_weight Y₂.property hy hv (rMode N Q α₂ n k)
  have h₁ := FusionTop.mem_weight Y₁.property hx h₂ (sMode N Q α₁ n k + d)
  convert h₁ using 2
  unfold rMode sMode
  ring

/-- Cyclicity moves the boundary mode to the other side, `d` levels down. -/
theorem AZ_eq_lvl_comm (hc : c ∈ W.grading kc) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (p n k : ℤ) :
    AZ Y₁ Y₂ c kc x y α₁ α₂ p n k =
      lvl N (((Y₁.val (sMode N Q α₁ n k + ((kc : ℂ) - p - 1)) x).comp
        (Y₂.val (rMode N Q α₂ n k) y)) * mode (N.isMod.YM c) p) (n - (kc - 1 - p)) := by
  have hB := weightShift_block Y₁ Y₂ hx hy n k ((kc : ℂ) - p - 1)
  have hC := VOA.weightShift_mode N.isMod hc p
  have h := gradedTraceOp_comm_shift N.isMod _ _ ((kc : ℂ) - p - 1) hB hC
    (N.h - W.centralCharge / 24 + ((n - (kc - 1 - p) : ℤ) : ℂ))
  unfold AZ lvl
  rw [h]
  congr 1
  push_cast
  ring

/-- The commutator of the boundary mode with the two-insertion block. -/
theorem block_commutator (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (p : ℤ) (s r : ℂ) :
    mode (N.isMod.YM c) p * (Y₁.val s x).comp (Y₂.val r y) -
        (Y₁.val s x).comp (Y₂.val r y) * mode (N.isMod.YM c) p =
      ∑ j ∈ Finset.range K, cbz p j •
          (Y₁.val ((p : ℂ) + s - j) (mode (P₁.isMod.YM c) j x)).comp (Y₂.val r y) +
        ∑ j ∈ Finset.range K, cbz p j •
          (Y₁.val s x).comp (Y₂.val ((p : ℂ) + r - j) (mode (P₂.isMod.YM c) j y)) := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  have h₂ := HuangODEModes.comm_range Y₂.property c y v p r K (fun j hj => (hK j hj).2)
  have h₁ := HuangODEModes.comm_range Y₁.property c x (Y₂.val r y v) p s K
    (fun j hj => (hK j hj).1)
  rw [h₂, map_sub, h₁, map_sum]
  simp only [map_smul]
  abel

/-- The commutator with the first insertion only. -/
theorem left_commutator (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (p : ℤ) (s r : ℂ) :
    (Y₁.val s x).comp ((mode (Q.isMod.YM c) p).comp (Y₂.val r y)) =
      mode (N.isMod.YM c) p * (Y₁.val s x).comp (Y₂.val r y) -
        ∑ j ∈ Finset.range K, cbz p j •
          (Y₁.val ((p : ℂ) + s - j) (mode (P₁.isMod.YM c) j x)).comp (Y₂.val r y) := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact HuangODEModes.comm_range Y₁.property c x (Y₂.val r y v) p s K
    (fun j hj => (hK j hj).1)

/-- **The level cyclicity relation.** With `d = kc − 1 − p`,
`A_p(n,k) = A_p(n−d,k−d) − Σ_j C(p,j) τ(c₍ⱼ₎x,y)(n−d,k−d) − Σ_j C(p,j) τ(x,c₍ⱼ₎y)(n−d,k)`. -/
theorem AZ_cyc (hc : c ∈ W.grading kc) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (p n k : ℤ) :
    AZ Y₁ Y₂ c kc x y α₁ α₂ p n k =
      AZ Y₁ Y₂ c kc x y α₁ α₂ p (n - (kc - 1 - p)) (k - (kc - 1 - p)) -
      ∑ j ∈ Finset.range K, cbz p j * tauZ Y₁ Y₂ (mode (P₁.isMod.YM c) j x) y
        (α₁ + (kc : ℂ) - (j : ℤ) - 1) α₂ (n - (kc - 1 - p)) (k - (kc - 1 - p)) -
      ∑ j ∈ Finset.range K, cbz p j * tauZ Y₁ Y₂ x (mode (P₂.isMod.YM c) j y)
        α₁ (α₂ + (kc : ℂ) - (j : ℤ) - 1) (n - (kc - 1 - p)) k := by
  set s := sMode N Q α₁ n k + ((kc : ℂ) - p - 1) with hs
  set r := rMode N Q α₂ n k with hr
  rw [AZ_eq_lvl_comm Y₁ Y₂ hc hx hy]
  rw [← hs, ← hr]
  have hcomm := block_commutator Y₁ Y₂ K hK p s r
  have he : (Y₁.val s x).comp (Y₂.val r y) * mode (N.isMod.YM c) p =
      mode (N.isMod.YM c) p * (Y₁.val s x).comp (Y₂.val r y) -
        (∑ j ∈ Finset.range K, cbz p j •
          (Y₁.val ((p : ℂ) + s - j) (mode (P₁.isMod.YM c) j x)).comp (Y₂.val r y) +
        ∑ j ∈ Finset.range K, cbz p j •
          (Y₁.val s x).comp (Y₂.val ((p : ℂ) + r - j) (mode (P₂.isMod.YM c) j y))) := by
    rw [← hcomm]; abel
  have e1 : lvl N (mode (N.isMod.YM c) p * (Y₁.val s x).comp (Y₂.val r y)) (n - (kc - 1 - p)) =
      AZ Y₁ Y₂ c kc x y α₁ α₂ p (n - (kc - 1 - p)) (k - (kc - 1 - p)) := by
    unfold AZ
    congr 3
    · rw [hs]; unfold sMode; push_cast; ring
    · rw [hr]; unfold rMode; push_cast; ring
  have e2 : ∀ j : ℕ, lvl N ((Y₁.val ((p : ℂ) + s - j) (mode (P₁.isMod.YM c) j x)).comp
      (Y₂.val r y)) (n - (kc - 1 - p)) = tauZ Y₁ Y₂ (mode (P₁.isMod.YM c) j x) y
        (α₁ + (kc : ℂ) - (j : ℤ) - 1) α₂ (n - (kc - 1 - p)) (k - (kc - 1 - p)) := by
    intro j
    unfold tauZ
    congr 3
    · rw [hs]; unfold sMode; push_cast; ring
    · rw [hr]; unfold rMode; push_cast; ring
  have e3 : ∀ j : ℕ, lvl N ((Y₁.val s x).comp
      (Y₂.val ((p : ℂ) + r - j) (mode (P₂.isMod.YM c) j y))) (n - (kc - 1 - p)) =
      tauZ Y₁ Y₂ x (mode (P₂.isMod.YM c) j y) α₁ (α₂ + (kc : ℂ) - (j : ℤ) - 1)
        (n - (kc - 1 - p)) k := by
    intro j
    unfold tauZ
    congr 3
    · rw [hs]; unfold sMode; push_cast; ring
    · rw [hr]; unfold rMode; push_cast; ring
  rw [he, lvl_sub, lvl_add, lvl_sum, lvl_sum, e1]
  simp only [lvl_smul, e2, e3]
  ring

/-- The middle mode is the boundary mode minus the first-slot commutator. -/
theorem MZ_eq (K : ℕ) (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (p n k : ℤ) :
    MZ Y₁ Y₂ c kc x y α₁ α₂ p n k = AZ Y₁ Y₂ c kc x y α₁ α₂ p n k -
      ∑ j ∈ Finset.range K, cbz p j * tauZ Y₁ Y₂ (mode (P₁.isMod.YM c) j x) y
        (α₁ + (kc : ℂ) - (j : ℤ) - 1) α₂ n k := by
  unfold MZ AZ
  rw [left_commutator Y₁ Y₂ K hK, lvl_sub, lvl_sum]
  simp only [lvl_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold tauZ
  congr 3
  unfold sMode
  push_cast
  ring

end Rel

end VOA.Huang.GenusOneWard
