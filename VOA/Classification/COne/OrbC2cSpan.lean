import VOA.Classification.COne.OrbC2bRelations

/-! # From the Dong--Jiang normal form to finite conformal towers

This proves the quotient step of Lemma 4.2, including truncation of its
infinite mode index. It does not assume the spanning theorem itself.
All C₂ spaces in this file are intrinsic to the VOA under discussion.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2c
open VOA VertexOperatorAlgebra OrbC2b
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A word of negative Virasoro modes; entry k denotes L(-k-1). -/
def virWord (W : VertexOperatorAlgebra V) : List ℕ → V → V
  | [], x => x
  | k :: ks, x => W.L (-(k : ℤ)-1) (virWord W ks x)

/-- The seeds left by Dong--Jiang Lemma 4.2 after its negative generator
products are put in the intrinsic C₂ space. -/
def djSeeds (W : VertexOperatorAlgebra V) (u v : V) : Set V :=
  {W.vacuum, u, v} ∪ Set.range (fun n : ℤ => W.smul u n u) ∪ (O₂ W : Set V)

/-- State-level residual implied by the published normal form. It retains
all mode indices; their finiteness modulo C₂ is proved below. -/
def DongJiangVirasoroSpan (W : VertexOperatorAlgebra V) (u v : V) : Prop :=
  Submodule.span ℂ (Set.range (fun p : List ℕ × djSeeds W u v =>
    virWord W p.1 p.2.val)) = ⊤

def towerSpan (W : VertexOperatorAlgebra V) {ι : Type*} (f : ι → A₂ W) :
    Submodule ℂ (A₂ W) :=
  Submodule.span ℂ (Set.range (fun p : ι × ℕ =>
    (exceptionalConformalEnd W ^ p.2) (f p.1)))

theorem conformal_mem_towerSpan (W : VertexOperatorAlgebra V) {ι : Type*}
    (f : ι → A₂ W) {x : A₂ W} (hx : x ∈ towerSpan W f) :
    exceptionalConformalEnd W x ∈ towerSpan W f := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, n⟩, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨(i, n+1), by dsimp only; rw [pow_succ', Module.End.mul_apply]⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using (towerSpan W f).add_mem hx hy
  | smul a x _ hx => simpa using (towerSpan W f).smul_mem a hx

theorem mk₂_virWord_mem (W : VertexOperatorAlgebra V) {ι : Type*}
    (f : ι → A₂ W) (x : V) (hx : mk₂ W x ∈ towerSpan W f) (ks : List ℕ) :
    mk₂ W (virWord W ks x) ∈ towerSpan W f := by
  induction ks with
  | nil => exact hx
  | cons k ks ih =>
    cases k with
    | zero =>
      change mk₂ W (W.L (-1) _) ∈ _
      rw [(mk₂_eq_zero_iff W).mpr (L_neg_one_mem_O₂ W _)]
      exact Submodule.zero_mem _
    | succ k =>
      cases k with
      | zero =>
        change mk₂ W (W.L (-2) _) ∈ _
        rw [← exceptionalConformalEnd_mk]
        exact conformal_mem_towerSpan W f ih
      | succ k =>
        have hz : W.L (-((k+1+1 : ℕ) : ℤ)-1) (virWord W ks x) ∈ O₂ W :=
          smul_le_neg_two_mem_O₂ W _ _ (by omega)
        rw [virWord, (mk₂_eq_zero_iff W).mpr hz]
        exact Submodule.zero_mem _

theorem conformalTowerSpan_of_towerSpan_eq_top (W : VertexOperatorAlgebra V)
    {ι : Type*} [Finite ι] (f : ι → A₂ W) (hf : towerSpan W f = ⊤) :
    ConformalTowerSpan W := by
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => f (e.symm i), ?_⟩
  have hr : Set.range (fun p : Fin (Fintype.card ι) × ℕ =>
      (exceptionalConformalEnd W ^ p.2) (f (e.symm p.1))) =
      Set.range (fun p : ι × ℕ => (exceptionalConformalEnd W ^ p.2) (f p.1)) := by
    ext x
    constructor
    · rintro ⟨⟨i,n⟩, rfl⟩; exact ⟨(e.symm i,n), rfl⟩
    · rintro ⟨⟨i,n⟩, rfl⟩; exact ⟨(e i,n), by simp⟩
  rw [hr]
  exact hf

/-- The infinite mode family and arbitrary negative Virasoro words in the
normal form yield only finitely many conformal towers. -/
theorem conformalTowerSpan_of_dongJiangVirasoroSpan
    (W : VertexOperatorAlgebra V) (u v : V) (h : DongJiangVirasoroSpan W u v) :
    ConformalTowerSpan W := by
  classical
  obtain ⟨N, hN⟩ := W.smul_eventually_zero u u
  let M := N.toNat + 1
  let seeds : Fin 3 ⊕ Fin (M+1) → V := Sum.elim ![W.vacuum, u, v]
    (fun i => W.smul u ((i.val : ℤ)-1) u)
  let f := fun i => mk₂ W (seeds i)
  have hseed (i) : f i ∈ towerSpan W f :=
    Submodule.subset_span ⟨(i, 0), rfl⟩
  have hbase (x : V) (hx : x ∈ djSeeds W u v) : mk₂ W x ∈ towerSpan W f := by
    rcases hx with (hx | hx) | hx
    · rcases hx with rfl | rfl | rfl
      · exact hseed (.inl 0)
      · exact hseed (.inl 1)
      · exact hseed (.inl 2)
    · obtain ⟨n, rfl⟩ := hx
      dsimp only
      by_cases hlo : n ≤ -2
      · rw [(mk₂_eq_zero_iff W).mpr (smul_le_neg_two_mem_O₂ W u u hlo)]
        exact Submodule.zero_mem _
      by_cases hhi : N ≤ n
      · rw [hN n hhi, map_zero]; exact Submodule.zero_mem _
      have hi : (n+1).toNat < M+1 := by dsimp [M]; omega
      have he : (((n+1).toNat : ℕ) : ℤ)-1 = n := by omega
      simpa only [f, seeds, Sum.elim_inr, he] using hseed (.inr ⟨(n+1).toNat, hi⟩)
    · rw [(mk₂_eq_zero_iff W).mpr hx]; exact Submodule.zero_mem _
  have hall (x : V) : mk₂ W x ∈ towerSpan W f := by
    have hx : x ∈ Submodule.span ℂ (Set.range (fun p : List ℕ × djSeeds W u v =>
        virWord W p.1 p.2.val)) := by rw [h]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨ks, ⟨z, hz⟩⟩, rfl⟩ := hy
      exact mk₂_virWord_mem W f z (hbase z hz) ks
    | zero => simp
    | add x y _ _ hx hy => simpa using (towerSpan W f).add_mem hx hy
    | smul a x _ hx => simpa using (towerSpan W f).smul_mem a hx
  apply conformalTowerSpan_of_towerSpan_eq_top W f
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := mk₂_surjective W y
  exact hall x

/-- OPEN: the actual state-level normal form of Dong--Jiang Lemma 4.2,
specialized to the concrete tetrahedral fixed VOA. -/
def TetrahedralVirasoroSpan : Prop :=
  ∃ u v : (orbifold tetra).carrier,
    u ∈ (orbifoldVOA tetra).grading 9 ∧ v ∈ (orbifoldVOA tetra).grading 16 ∧
    DongJiangVirasoroSpan (orbifoldVOA tetra) u v

theorem tetrahedralConformalSpan_of_virasoroSpan (h : TetrahedralVirasoroSpan) :
    TetrahedralConformalSpan := by
  obtain ⟨u,v,_,_,h⟩ := h
  exact conformalTowerSpan_of_dongJiangVirasoroSpan _ u v h

end VOA.Classification.COne.OrbC2c
