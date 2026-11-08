import VOA.Moonshine.MoonshineLRCommutant

/-!
# Column and triality block restrictions on the rational Griess commutant
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA.Moonshine.MonsterGriess
open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.SpinLattice VOA.Moonshine.MonsterGriess.Visible
open Matrix
open scoped BigOperators

/-- Every entry of the octad triality matrix is nonzero. -/
theorem commutB_octHD_ne_zero (d : OctadWord)
    (v w : Octad.EvenQuot (octSupp d)) : octHD d v w ≠ 0 := by
  have hs (s : ZMod 2) : MonsterGriess.sgn s ≠ 0 := by
    intro h
    have e := sgn_mul_self s
    rw [h, zero_mul] at e
    exact zero_ne_one e
  rw [octHD, octD, signMatrix, Matrix.mul_diagonal, octH, fourierMatrix]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num))) (hs _))
    (hs _)

/-- Extraspecial commutation preserves every octad basis line. -/
theorem commutB_oct_eigen (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u)) (o : OctIdx) :
    ∃ a : ℚ, T (tbasis (.inr (.inr (.inr o)))) =
      a • tbasis (.inr (.inr (.inr o))) := by
  rw [tbasis_oct]
  exact commutXlift_eigen T hQ _ (isShortCoord_labelElt (.inr (.inr (.inr o))))

/-- Triality forces all short-line eigenvalues in one octad block to coincide. -/
theorem commutB_oct_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (d : OctadWord) :
    ∃ a : ℚ, ∀ v : Octad.EvenQuot (octSupp d),
      T (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
        a • tbasis (.inr (.inr (.inr ⟨d, v⟩))) := by
  classical
  choose c hc using fun v : Octad.EvenQuot (octSupp d) => commutB_oct_eigen T hQ ⟨d, v⟩
  have he (v w : Octad.EvenQuot (octSupp d)) : c v = c w := by
    have e := hτ (tbasis (.inr (.inr (.inr ⟨d, v⟩))))
    rw [tauB_oct, map_sum, hc, map_smul, tauB_oct] at e
    simp only [map_smul, hc] at e
    have e' := congrArg (fun u => tbasis.repr u (.inr (.inr (.inr ⟨d, w⟩)))) e
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, tbasis.repr_self] at e'
    simp only [Finsupp.single_apply, Sum.inr.injEq, Sigma.mk.inj_iff,
      true_and, heq_eq_eq] at e'
    simp [mul_ite, eq_comm] at e'
    simpa [mul_comm, commutB_octHD_ne_zero d v w] using e'
  exact ⟨c 0, fun v => by rw [hc, he v 0]⟩

/-- Codeword translations act transitively on the code component of the spin basis. -/
theorem commutB_rho_translate (c d : C₀) (η : ZMod 2) (i : Fin 24) :
    rhoEquiv (spinEquiv ⟨0, (c : C) + (d : C), 0⟩)
        (0, 0, tensor (Spin.E η c) (Pi.single i 1)) =
      (0, 0, tensor (Spin.E η d) (Pi.single i 1)) := by
  rw [rhoEquiv_tensor]
  change (0, 0, tensor (Pi.single (η, c) 1 ᵥ*
    qmatR ℚ 0 ((c : C) + (d : C)) 0) (Pi.single i 1)) = _
  rw [single_vecMul_qmatR]
  have hshift : shift ((c : C) + (d : C)) c = d := by
    rw [shift, ← add_assoc, add_self_C, zero_add, π₀_coe]
  simp [qPerm, qSign, hshift, sgnR, Spin.E]

/-- The spin eigenvalue depends only on the tensor column. -/
theorem commutB_column_eq (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (c d : C₀) (i : Fin 24) :
    commutOddScalar T c i = commutOddScalar T d i := by
  have e := hQ (spinEquiv ⟨0, (c : C) + (d : C), 0⟩)
    (0, 0, tensor (Spin.E 0 c) (Pi.single i 1))
  rw [commutB_rho_translate, commutSpin_eigen T hQ hτ,
    commutSpin_eigen T hQ hτ, map_smul, commutB_rho_translate] at e
  have e' := congrArg (fun u : SpaceB => u.2.2 (0, d) i) e
  simpa [tensor, Spin.E, Matrix.vecMulVec_apply] using e'.symm

/-- On the spin-tensor space, the commutant acts by a diagonal matrix on the right. -/
theorem commutB_columns (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (N : SpaceW) :
    T (0, 0, N) = (0, 0, N * Matrix.diagonal (commutOddScalar T 0)) := by
  classical
  have hn : ((0, 0, N) : SpaceB) =
      ∑ j, ∑ i, N j i • ((0, 0, tensor (Spin.E j.1 j.2) (Pi.single i 1)) : SpaceB) := by
    ext
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Prod.fst_sum]
    · simp [Prod.snd_sum, Matrix.sum_apply, tensor, Spin.E, Matrix.vecMulVec_apply,
        Pi.single_apply]
  rw [hn, map_sum]
  simp only [map_sum, map_smul, commutSpin_eigen T hQ hτ,
    commutB_column_eq T hQ hτ _ 0]
  ext
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, Prod.fst_sum]
  · simp [Prod.snd_sum, Matrix.sum_apply, tensor, Spin.E, Matrix.vecMulVec_apply,
      Pi.single_apply, Matrix.mul_diagonal]

/-- Triality and a minus short-line eigenvector determine an entire pair block. -/
theorem commutB_pair_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (p : LtPair) :
    ∃ a : ℚ, ∀ k : Fin 3, T (tbasis (.inr (.inl (p, k)))) =
      a • tbasis (.inr (.inl (p, k))) := by
  obtain ⟨a, ha⟩ := commutXlift_eigen T hQ (rMinus p.1.1 p.1.2)
    (isShortCoord_labelElt (.inl p))
  let v (k : Fin 3) := tbasis (.inr (.inl (p, k)))
  have hv (k : Fin 3) : tauB (v k) = v (k + 1) := tauB_pair p k
  have hs : v 1 + v 2 = (2 : ℚ) • ((0, Xlift (rMinus p.1.1 p.1.2), 0) : SpaceB) := by
    dsimp [v]
    rw [tbasis_pair_one, tbasis_pair_two]
    ext <;> simp
    ring
  have h12 : T (v 1 + v 2) = a • (v 1 + v 2) := by
    rw [hs, map_smul, ha, smul_comm]
  have h20 : T (v 2 + v 0) = a • (v 2 + v 0) := by
    have h := hτ (v 1 + v 2)
    simpa only [map_add, hv, h12, map_smul] using h
  have h01 : T (v 0 + v 1) = a • (v 0 + v 1) := by
    have h := hτ (v 2 + v 0)
    simpa only [map_add, hv, h20, map_smul] using h
  have h0 : T (v 0) = a • v 0 := by
    have he : v 0 = (1 / 2 : ℚ) • ((v 0 + v 1) + (v 2 + v 0) - (v 1 + v 2)) := by
      module
    calc
      T (v 0) = (1 / 2 : ℚ) •
          (T (v 0 + v 1) + T (v 2 + v 0) - T (v 1 + v 2)) := by
        conv_lhs => rw [he]
        simp only [map_smul, map_sub, map_add]
      _ = a • v 0 := by rw [h01, h20, h12]; module
  have hnext (k : Fin 3) (hk : T (v k) = a • v k) :
      T (v (k + 1)) = a • v (k + 1) := by
    rw [← hv, hτ, hk, map_smul, hv]
  refine ⟨a, ?_⟩
  intro k
  fin_cases k
  · exact h0
  · exact hnext 0 h0
  · exact hnext 1 (hnext 0 h0)

/-- The pair's two short lines and its symmetric matrix share a single eigenvalue. -/
theorem commutB_pair_lines (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (p : LtPair) :
    ∃ a : ℚ,
      T (basisA s(p.1.1, p.1.2), 0, 0) =
        a • ((basisA s(p.1.1, p.1.2), 0, 0) : SpaceB) ∧
      T (0, Xlift (rMinus p.1.1 p.1.2), 0) =
        a • ((0, Xlift (rMinus p.1.1 p.1.2), 0) : SpaceB) ∧
      T (0, Xlift (rPlus p.1.1 p.1.2), 0) =
        a • ((0, Xlift (rPlus p.1.1 p.1.2), 0) : SpaceB) := by
  obtain ⟨a, ha⟩ := commutB_pair_scalar T hQ hτ p
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa only [tbasis_pair_zero] using ha 0
  · have he : ((0, Xlift (rMinus p.1.1 p.1.2), 0) : SpaceB) =
        (1 / 2 : ℚ) • (tbasis (.inr (.inl (p, 1))) +
          tbasis (.inr (.inl (p, 2)))) := by
      rw [tbasis_pair_one, tbasis_pair_two]
      ext <;> simp
      ring
    rw [he, map_smul, map_add, ha, ha]
    module
  · have he : ((0, Xlift (rPlus p.1.1 p.1.2), 0) : SpaceB) =
        (1 / 2 : ℚ) • (tbasis (.inr (.inl (p, 2))) -
          tbasis (.inr (.inl (p, 1)))) := by
      rw [tbasis_pair_one, tbasis_pair_two]
      ext <;> simp
      ring
    rw [he, map_smul, map_sub, ha, ha]
    module

/-- Expand an embedded symmetric matrix in its matrix basis. -/
theorem commutB_A_sum (A : symMat) :
    ((A, 0, 0) : SpaceB) = ∑ z, symEntry A z • ((basisA z, 0, 0) : SpaceB) := by
  conv_lhs => rw [symMat_eq_sum A]
  ext
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]
  · simp [Prod.snd_sum]

/-- The symmetric-matrix component of triality has no off-diagonal entries. -/
theorem commutB_tau_A_offdiag (A : symMat) (i j : Fin 24) (hij : i ≠ j) :
    (tauB (A, 0, 0)).1.val i j = 0 := by
  classical
  have hp (p : LtPair) : (tauB (basisA s(p.1.1, p.1.2), 0, 0)).1 = 0 := by
    rw [← tbasis_pair_zero, tauB_pair]
    change (tbasis (.inr (.inl (p, 1)))).1 = 0
    rw [tbasis_pair_one]
  have hz (z : PairIdx) : (tauB (basisA z, 0, 0)).1.val i j = 0 := by
    induction z using Sym2.ind with
    | h k l =>
      rcases lt_trichotomy k l with h | rfl | h
      · rw [hp ⟨(k, l), h⟩]
        rfl
      · rw [← tbasis_diag, tauB_diag, tbasis_diag]
        simp only [coe_basisA]
        simp only [ite_true, Matrix.single_apply, ite_eq_right_iff, one_ne_zero,
          imp_false, not_and]
        intro hi hj
        exact hij (hi.symm.trans hj)
      · rw [Sym2.eq_swap, hp ⟨(l, k), h⟩]
        rfl
  rw [commutB_A_sum, map_sum]
  simp only [map_smul, Prod.fst_sum, Prod.smul_fst, Submodule.coe_sum,
    Submodule.coe_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hz,
    mul_zero, Finset.sum_const_zero]

/-- Triality fixes every diagonal symmetric matrix. -/
theorem commutB_tau_diagonal (A : symMat)
    (hA : ∀ i j, i ≠ j → A.val i j = 0) : tauB (A, 0, 0) = (A, 0, 0) := by
  classical
  rw [commutB_A_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul]
  induction z using Sym2.ind with
  | h i j =>
    by_cases h : i = j
    · subst j
      rw [← tbasis_diag, tauB_diag]
    · rw [symEntry_mk, hA i j h, zero_smul, zero_smul]

/-- Commutation with the extraspecial group and triality preserves diagonal matrices. -/
theorem commutB_preserves_diagonal (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (A : symMat)
    (hA : ∀ i j, i ≠ j → A.val i j = 0) :
    T (A, 0, 0) = ((T (A, 0, 0)).1, 0, 0) ∧
      ∀ i j, i ≠ j → (T (A, 0, 0)).1.val i j = 0 := by
  refine ⟨commutPreservesA T hQ A, ?_⟩
  intro i j hij
  have he : tauB (T (A, 0, 0)) = T (A, 0, 0) := by
    rw [← hτ, commutB_tau_diagonal A hA]
  rw [commutPreservesA T hQ A] at he
  have h := congrArg (fun u : SpaceB => u.1.val i j) he
  exact h.symm.trans (commutB_tau_A_offdiag _ i j hij)

/-- A single scalar acts on every linear combination in a fixed octad block. -/
theorem commutB_oct_block (T : SpaceB →ₗ[ℚ] SpaceB)
    (hQ : ∀ r u, T (rhoEquiv r u) = rhoEquiv r (T u))
    (hτ : ∀ u, T (tauB u) = tauB (T u)) (d : OctadWord) :
    ∃ a : ℚ, ∀ f : Octad.EvenQuot (octSupp d) → ℚ,
      T (∑ v, f v • tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
        a • ∑ v, f v • tbasis (.inr (.inr (.inr ⟨d, v⟩))) := by
  obtain ⟨a, ha⟩ := commutB_oct_scalar T hQ hτ d
  refine ⟨a, fun f => ?_⟩
  simp only [map_sum, map_smul, ha, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact smul_comm _ _ _

/-- The generated-group commutant scales each spin column and its odd short lines together. -/
theorem commutB_Gmat_columns (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    (∀ N : SpaceW,
      T (0, 0, N) = (0, 0, N * Matrix.diagonal (commutOddScalar T 0))) ∧
    ∀ (c : C₀) (i : Fin 24), T (0, Xlift (rOdd c i), 0) =
      commutOddScalar T 0 i • ((0, Xlift (rOdd c i), 0) : SpaceB) := by
  have hQ := fun r => h _ (commutRho_mem_Gmat r)
  have hτ := h _ commutTau_mem_Gmat
  refine ⟨commutB_columns T hQ hτ, fun c i => ?_⟩
  rw [commutOdd_Xlift T hQ hτ, commutB_column_eq T hQ hτ c 0 i]

/-- Each pair block has one scalar under the generated-group commutant. -/
theorem commutB_Gmat_pair (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (p : LtPair) :
    ∃ a : ℚ, ∀ k : Fin 3, T (tbasis (.inr (.inl (p, k)))) =
      a • tbasis (.inr (.inl (p, k))) :=
  commutB_pair_scalar T (fun r => h _ (commutRho_mem_Gmat r)) (h _ commutTau_mem_Gmat) p

/-- Each octad block has one scalar under the generated-group commutant. -/
theorem commutB_Gmat_oct (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (d : OctadWord) :
    ∃ a : ℚ, ∀ v : Octad.EvenQuot (octSupp d),
      T (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
        a • tbasis (.inr (.inr (.inr ⟨d, v⟩))) :=
  commutB_oct_scalar T (fun r => h _ (commutRho_mem_Gmat r)) (h _ commutTau_mem_Gmat) d

/-- The generated-group commutant preserves the diagonal symmetric-matrix space. -/
theorem commutB_Gmat_diagonal (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (A : symMat)
    (hA : ∀ i j, i ≠ j → A.val i j = 0) :
    T (A, 0, 0) = ((T (A, 0, 0)).1, 0, 0) ∧
      ∀ i j, i ≠ j → (T (A, 0, 0)).1.val i j = 0 :=
  commutB_preserves_diagonal T (fun r => h _ (commutRho_mem_Gmat r))
    (h _ commutTau_mem_Gmat) A hA

end VOA.Moonshine.ConwayNorton.M8
