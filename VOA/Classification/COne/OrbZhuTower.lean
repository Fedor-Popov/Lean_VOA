import VOA.Classification.COne.PlusSplitC2Dimension
import VOA.Classification.COne.ExceptionalOrbifoldC2
import VOA.Examples.ZhuTripletW2

/-!
# OrbZhu (1): conformal towers in Zhu's algebra and the tower dimension count

For any VOA `W`, let `Tω` be left multiplication by `[ω]` on `A(W)` (`omegaL`).

* `mk_L_neg_two`: `[L(-2)x] = Tω[x] + k[x]` for `x ∈ W_k`;
* `mk_L_neg_two_pow_mem`: `[L(-2)^a x]` lies in the `Tω`-tower `span{Tω^b [x] : b ≤ a}`;
* `pow_mem_towerSub_of_monic`: a monic relation `P(Tω)[x] = 0` truncates the tower at
  `deg P`;
* `finrank_A_le_of_towers`: if the conformal towers `ω̄^a s̄_i` (`a < N i`) span
  `R(W) = W/C₂(W)`, and the `Tω`-tower of `[s_i]` is already spanned by its first `M i`
  members up to height `N i`, then `dim A(W) ≤ Σ M i`.

The last statement is Zhu's filtration argument (`span_sup_O_eq_top`) combined with the tower
calculus; it is how relations in `A(W)` that are NOT visible in `R(W)` sharpen the C₂ count.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbZhu

open VOA VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- Left multiplication by `[ω]` on Zhu's algebra. -/
def omegaL : Module.End ℂ (A W) := Amul (zhuRingData_holds W) (mk W W.conformalVector)

theorem L_neg_two_eq_smul (x : 𝒱) : W.L (-2) x = W.smul W.conformalVector (-1) x := by
  rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]; norm_num

/-- `[L(-2)x] = [ω]·[x] + k[x]` for `x ∈ W_k`. -/
theorem mk_L_neg_two {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) :
    mk W (W.L (-2) x) = omegaL W (mk W x) + (k : ℂ) • mk W x := by
  have h := ZhuW2.Amul_omega_mk W hx
  rw [omegaL, h, L_neg_two_eq_smul]
  abel

theorem L_mem_grading_ {ℓ : ℤ} {v : 𝒱} (hv : v ∈ W.grading ℓ) (m : ℤ) :
    W.L m v ∈ W.grading (ℓ - m) := by
  have h := W.grading_mode W.conformalVector W.conformal_mem v hv (m + 1)
  rw [show (2 + ℓ - (m + 1) - 1) = ℓ - m from by ring] at h
  exact h

theorem L_neg_two_pow_mem_grading {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) (a : ℕ) :
    ((W.L (-2)) ^ a) x ∈ W.grading (k + 2 * a) := by
  induction a with
  | zero => simpa using hx
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := L_mem_grading_ W ih (-2)
    rw [show k + 2 * (a : ℤ) - (-2) = k + 2 * ((a + 1 : ℕ) : ℤ) by push_cast; ring] at h
    exact h

/-- The `Tω`-tower of height `n` over `y`. -/
def towerSub (y : A W) (n : ℕ) : Submodule ℂ (A W) :=
  Submodule.span ℂ (Set.range fun i : Fin n => (omegaL W ^ (i : ℕ)) y)

theorem pow_mem_towerSub (y : A W) {n b : ℕ} (hb : b < n) :
    (omegaL W ^ b) y ∈ towerSub W y n :=
  Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩

theorem towerSub_mono (y : A W) {n m : ℕ} (h : n ≤ m) : towerSub W y n ≤ towerSub W y m :=
  Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact pow_mem_towerSub W y (lt_of_lt_of_le i.2 h))

theorem omegaL_mem_towerSub (y : A W) {n : ℕ} {z : A W} (hz : z ∈ towerSub W y n) :
    omegaL W z ∈ towerSub W y (n + 1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    have : omegaL W ((omegaL W ^ (i : ℕ)) y) = (omegaL W ^ ((i : ℕ) + 1)) y := by
      rw [pow_succ', Module.End.mul_apply]
    rw [this]
    exact pow_mem_towerSub W y (by omega)
  | zero => simp
  | add x y' _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

/-- `[L(-2)^a x]` lies in the `Tω`-tower of `[x]` of height `a + 1`. -/
theorem mk_L_neg_two_pow_mem {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) (a : ℕ) :
    mk W (((W.L (-2)) ^ a) x) ∈ towerSub W (mk W x) (a + 1) := by
  induction a with
  | zero => simpa using pow_mem_towerSub W (mk W x) (n := 1) (b := 0) (by omega)
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply,
      mk_L_neg_two W (L_neg_two_pow_mem_grading W hx a)]
    exact Submodule.add_mem _ (omegaL_mem_towerSub W _ ih)
      (Submodule.smul_mem _ _ (towerSub_mono W _ (by omega) ih))

theorem aeval_mem_towerSub (y : A W) (Q : Polynomial ℂ) {n : ℕ} (hQ : Q.natDegree < n) :
    (Polynomial.aeval (omegaL W) Q) y ∈ towerSub W y n := by
  rw [Polynomial.as_sum_range' Q n hQ, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
  exact Submodule.smul_mem _ _ (pow_mem_towerSub W y (Finset.mem_range.mp hi))

/-- A monic relation `P([ω])[x] = 0` truncates the tower of `[x]` at `deg P`. -/
theorem pow_mem_towerSub_of_monic (y : A W) {P : Polynomial ℂ} (hP : P.Monic)
    (hy : (Polynomial.aeval (omegaL W) P) y = 0) (b : ℕ) :
    (omegaL W ^ b) y ∈ towerSub W y P.natDegree := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · -- `P = 1`, so `y = 0`
    have hP1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP h0
    rw [hP1, map_one, Module.End.one_apply] at hy
    rw [hy, map_zero]; exact Submodule.zero_mem _
  · have hdecomp := Polynomial.modByMonic_add_div (Polynomial.X ^ b) P
    rw [mul_comm P] at hdecomp
    have hsplit : (Polynomial.aeval (omegaL W)) (Polynomial.X ^ b : Polynomial ℂ) =
        Polynomial.aeval (omegaL W) (Polynomial.X ^ b %ₘ P) +
          Polynomial.aeval (omegaL W) (Polynomial.X ^ b /ₘ P) *
            Polynomial.aeval (omegaL W) P := by
      rw [← map_mul, ← map_add, hdecomp]
    have key : (omegaL W ^ b) y =
        (Polynomial.aeval (omegaL W) (Polynomial.X ^ b %ₘ P)) y := by
      have h1 : omegaL W ^ b = Polynomial.aeval (omegaL W) (Polynomial.X ^ b : Polynomial ℂ) := by
        simp
      rw [h1, hsplit, LinearMap.add_apply, Module.End.mul_apply, hy, map_zero, add_zero]
    rw [key]
    apply aeval_mem_towerSub
    have hdeg := Polynomial.degree_modByMonic_lt (Polynomial.X ^ b) hP
    by_cases hz : Polynomial.X ^ b %ₘ P = 0
    · rw [hz]; simpa using hpos
    · exact Polynomial.natDegree_lt_natDegree hz hdeg

/-- **The tower span in `A(W)`.**  If the conformal towers `ω̄^a s̄_i` (`a < N i`) span
`R(W)` and the `Tω`-tower of `[s_i]` is spanned by its first `M i` members up to height `N i`,
then the classes `Tω^a [s_i]` (`a < M i`) span `A(W)`. -/
theorem span_towers_A_eq_top {ι : Type} [Fintype ι] (s : ι → 𝒱) (k : ι → ℤ)
    (hs : ∀ i, s i ∈ W.grading (k i)) (N M : ι → ℕ)
    (hspan : Submodule.span ℂ (Set.range fun p : (Σ i, Fin (N i)) =>
      mk₂ W (((W.L (-2)) ^ (p.2 : ℕ)) (s p.1))) = ⊤)
    (hM : ∀ i, ∀ a < N i, (omegaL W ^ a) (mk W (s i)) ∈ towerSub W (mk W (s i)) (M i)) :
    Submodule.span ℂ (Set.range fun p : (Σ i, Fin (M i)) =>
      (omegaL W ^ (p.2 : ℕ)) (mk W (s p.1))) = ⊤ := by
  classical
  let lift : (Σ i, Fin (N i)) → 𝒱 := fun p => ((W.L (-2)) ^ (p.2 : ℕ)) (s p.1)
  let S : Set 𝒱 := Set.range lift
  have hShom : ∀ x ∈ S, IsHomog W x := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, L_neg_two_pow_mem_grading W (hs p.1) p.2⟩
  have htop₂ : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W := by
    have hmap : (Submodule.span ℂ S).map (O₂ W).mkQ = ⊤ := by
      rw [Submodule.map_span, ← hspan]
      congr 1
      ext y; constructor
      · rintro ⟨_, ⟨p, rfl⟩, rfl⟩; exact ⟨p, rfl⟩
      · rintro ⟨p, rfl⟩; exact ⟨lift p, ⟨p, rfl⟩, rfl⟩
    have := congrArg (Submodule.comap (O₂ W).mkQ) hmap
    simpa only [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] using this.symm
  have htop := span_sup_O_eq_top W S hShom htop₂
  let g : (Σ i, Fin (M i)) → A W := fun p => (omegaL W ^ (p.2 : ℕ)) (mk W (s p.1))
  have hsub : ∀ i, towerSub W (mk W (s i)) (M i) ≤ Submodule.span ℂ (Set.range g) := by
    intro i
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨i, j⟩, rfl⟩
  have hS : ∀ y ∈ Submodule.span ℂ S, mk W y ∈ Submodule.span ℂ (Set.range g) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have h1 := mk_L_neg_two_pow_mem W (hs p.1) (p.2 : ℕ)
      have h2 : towerSub W (mk W (s p.1)) ((p.2 : ℕ) + 1) ≤
          towerSub W (mk W (s p.1)) (M p.1) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact hM p.1 j (by have := p.2.2; have := j.2; omega)
      exact hsub p.1 (h2 h1)
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
  apply top_unique
  rintro q -
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (O W) q
  have hx : x ∈ Submodule.span ℂ S ⊔ O W := by rw [← htop]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hz0 : (O W).mkQ z = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hz
  rw [map_add, hz0, add_zero]
  exact hS y hy

/-- **The tower dimension count.** -/
theorem finrank_A_le_of_towers {ι : Type} [Fintype ι] (s : ι → 𝒱) (k : ι → ℤ)
    (hs : ∀ i, s i ∈ W.grading (k i)) (N M : ι → ℕ)
    (hspan : Submodule.span ℂ (Set.range fun p : (Σ i, Fin (N i)) =>
      mk₂ W (((W.L (-2)) ^ (p.2 : ℕ)) (s p.1))) = ⊤)
    (hM : ∀ i, ∀ a < N i, (omegaL W ^ a) (mk W (s i)) ∈ towerSub W (mk W (s i)) (M i)) :
    FiniteDimensional ℂ (A W) ∧ Module.finrank ℂ (A W) ≤ ∑ i, M i := by
  classical
  let g : (Σ i, Fin (M i)) → A W := fun p => (omegaL W ^ (p.2 : ℕ)) (mk W (s p.1))
  have hgtop : Submodule.span ℂ (Set.range g) = ⊤ :=
    span_towers_A_eq_top W s k hs N M hspan hM
  have hfin : FiniteDimensional ℂ (A W) := by
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
    rw [hgtop] at this
    exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl)
  refine ⟨hfin, ?_⟩
  have h := finrank_range_le_card (R := ℂ) g
  rw [Set.finrank, hgtop, finrank_top] at h
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

end VOA.Classification.COne.OrbZhu
