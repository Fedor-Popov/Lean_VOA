import VOA.Examples.LeeYangCharacterSorting
import VOA.Examples.LeeYangProper
import VOA.Examples.LeeYangRigidity

/-!
# Gap-two spanning of the Lee–Yang length filtration

The spanning (upper-bound) half of the Rogers–Ramanujan description of the vacuum Lee–Yang
module `L(-22/5,0)`, **compatible with the PBW-length filtration**:

* `leeYangRelation_mem` — for every word `r` and every `k`, the vector
  `5 Σ_{e+f=k} L_r L_{-e-2} L_{-f-2}|0⟩ - (3(k+1)(k+2)/2) L_r L_{-k-4}|0⟩` lies in the maximal
  ideal.  It is `L_r` applied to `L_{-1}^k s / k!` for the Lee–Yang singular vector
  `s = 5L_{-2}^2|0⟩ - 3L_{-4}|0⟩`; only Virasoro-mode stability of the ideal is used.
* `goodFil_leeYang_eq_gapSpan` — the length-`≤ p`, weight-`N` step of the PBW flag of
  `L(-22/5,0)` is spanned by the images of the **gap-two** words (adjacent entries differing by
  at least two) of length `≤ p` and energy `N`.

The proof is the leading-term straightening of the jet relation `x(z)^2 = 0`: a sorted word with
an adjacent pair `a ≥ b`, `a - b ≤ 1` is rewritten, modulo the ideal and the strictly lower length
step, as a combination of sorted words of the same length whose entries are strictly more spread
out (larger sum of squares).  Everything here is proved; no hypothesis is introduced.
-/

namespace VOA.LeeYangCharacter

open VOA.VirModule VOA.VirGoodFil VOA.VirSimple VOA.LeeYang
open scoped BigOperators

/-! ## §1  Mode stability of the maximal ideal, and words applied to vectors -/

section General

variable (c : ℂ)

/-- The maximal ideal is stable under every Virasoro mode. -/
theorem Lop_mem_maxIdealVir (m : ℤ) {v : VirUniv c} (hv : v ∈ maxIdealVir c) :
    Lop c m v ∈ maxIdealVir c := by
  have h := maxIdealVir_isIdeal c (virasoroVOA c).conformalVector v (m + 1) hv
  have he : (virasoroVOA c).L m v =
      (virasoroVOA c).smul (virasoroVOA c).conformalVector (m + 1) v := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  rw [virasoroVOA_L_eq_Lop] at he
  rw [he]; exact h

/-- The linear operator `L_{-r₁-2} ⋯ L_{-r_m-2}` attached to a word `r`. -/
noncomputable def applyWord : List ℕ → Module.End ℂ (VirUniv c)
  | [] => LinearMap.id
  | a :: r => (Lop c (-(a : ℤ) - 2)).comp (applyWord r)

theorem negWordVir_append (r w : List ℕ) :
    negWordVir c (r ++ w) = applyWord c r (negWordVir c w) := by
  induction r with
  | nil => rfl
  | cons a r ih =>
      rw [List.cons_append, negWordVir_cons, ih]
      rfl

theorem applyWord_mem_maxIdealVir (r : List ℕ) {v : VirUniv c} (hv : v ∈ maxIdealVir c) :
    applyWord c r v ∈ maxIdealVir c := by
  induction r with
  | nil => exact hv
  | cons a r ih => exact Lop_mem_maxIdealVir c _ ih

/-! ## §2  `L_{-1}` on one- and two-letter words -/

/-- `L₋₁ L₋ₑ₋₂ = L₋ₑ₋₂ L₋₁ + (e+1) L₋ₑ₋₃`. -/
theorem Lop_neg_one_comm (e : ℕ) (x : VirUniv c) :
    Lop c (-1) (Lop c (-(e : ℤ) - 2) x) =
      Lop c (-(e : ℤ) - 2) (Lop c (-1) x) + ((e : ℂ) + 1) • Lop c (-((e + 1 : ℕ) : ℤ) - 2) x := by
  have h := Lop_apply_bracket c (-1) (-(e : ℤ) - 2) x
  rw [if_neg (by omega), zero_smul, add_zero,
    show (-1 : ℤ) + (-(e : ℤ) - 2) = -((e + 1 : ℕ) : ℤ) - 2 by push_cast; ring,
    show (((-1 : ℤ) : ℂ) - ((-(e : ℤ) - 2 : ℤ) : ℂ)) = (e : ℂ) + 1 by push_cast; ring] at h
  exact h

theorem Lop_neg_one_single (j : ℕ) :
    Lop c (-1) (negWordVir c [j]) = ((j : ℂ) + 1) • negWordVir c [j + 1] := by
  simp only [negWordVir_cons, negWordVir_nil]
  rw [Lop_neg_one_comm, Lop_vacuum c (le_refl _), map_zero, zero_add]

theorem Lop_neg_one_pair (e f : ℕ) :
    Lop c (-1) (negWordVir c [e, f]) =
      ((e : ℂ) + 1) • negWordVir c [e + 1, f] + ((f : ℂ) + 1) • negWordVir c [e, f + 1] := by
  have h := Lop_neg_one_single c f
  rw [show negWordVir c [e, f] = Lop c (-(e : ℤ) - 2) (negWordVir c [f]) from rfl,
    Lop_neg_one_comm, h, map_smul]
  rw [show negWordVir c [e + 1, f] = Lop c (-((e + 1 : ℕ) : ℤ) - 2) (negWordVir c [f]) from rfl,
    show negWordVir c [e, f + 1] = Lop c (-(e : ℤ) - 2) (negWordVir c [f + 1]) from rfl]
  abel

/-- The quadratic jet coefficient `T_k = Σ_{e+f=k} L₋ₑ₋₂ L₋f₋₂ |0⟩`. -/
noncomputable def quadWord (k : ℕ) : VirUniv c :=
  ∑ p ∈ Finset.antidiagonal k, negWordVir c [p.1, p.2]

theorem Lop_neg_one_quadWord (k : ℕ) :
    Lop c (-1) (quadWord c k) = ((k : ℂ) + 1) • quadWord c (k + 1) := by
  unfold quadWord
  rw [map_sum]
  simp only [Lop_neg_one_pair]
  rw [Finset.sum_add_distrib]
  have hk : ((k : ℂ) + 1) • ∑ p ∈ Finset.antidiagonal (k + 1), negWordVir c [p.1, p.2] =
      ∑ p ∈ Finset.antidiagonal (k + 1), ((p.1 : ℂ) • negWordVir c [p.1, p.2]) +
      ∑ p ∈ Finset.antidiagonal (k + 1), ((p.2 : ℂ) • negWordVir c [p.1, p.2]) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [← add_smul]
    congr 1
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, ← hp]
    push_cast; ring
  rw [hk, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.cast_zero, zero_smul, zero_add, Nat.cast_add, Nat.cast_one]

/-- The jet relation vectors `σ_k = 5 T_k - (3(k+1)(k+2)/2) L₋ₖ₋₄|0⟩`. -/
noncomputable def sigmaWord (k : ℕ) : VirUniv c :=
  (5 : ℂ) • quadWord c k - ((3 : ℂ) * ((k : ℂ) + 1) * ((k : ℂ) + 2) / 2) • negWordVir c [k + 2]

theorem Lop_neg_one_sigmaWord (k : ℕ) :
    Lop c (-1) (sigmaWord c k) = ((k : ℂ) + 1) • sigmaWord c (k + 1) := by
  unfold sigmaWord
  rw [map_sub, map_smul, map_smul, Lop_neg_one_quadWord, Lop_neg_one_single]
  rw [smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2
  · ring
  · push_cast; ring

end General

/-! ## §3  The relations in the Lee–Yang maximal ideal -/

theorem sigmaWord_zero : sigmaWord leeYangC 0 = leeYangSingular := by
  unfold sigmaWord quadWord leeYangSingular
  rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  rw [show (0 + 2 : ℕ) = 2 from rfl, negWordVir_two, negWordVir_zero_zero]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  norm_num

theorem sigmaWord_mem (k : ℕ) : sigmaWord leeYangC k ∈ maxIdealVir leeYangC := by
  induction k with
  | zero => rw [sigmaWord_zero]; exact leeYangSingular_mem_maxIdealVir
  | succ k ih =>
      have h := Lop_mem_maxIdealVir leeYangC (-1) ih
      rw [Lop_neg_one_sigmaWord] at h
      have hk : ((k : ℂ) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      have := Submodule.smul_mem _ ((k : ℂ) + 1)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at this

/-- **The Lee–Yang jet relations.**  For every word `r` and `k`,
`5 Σ_{e+f=k} L_r L₋ₑ₋₂ L₋f₋₂|0⟩ - (3(k+1)(k+2)/2) L_r L₋ₖ₋₄|0⟩ ∈ J`. -/
theorem leeYangRelation_mem (r : List ℕ) (k : ℕ) :
    (5 : ℂ) • (∑ p ∈ Finset.antidiagonal k, negWordVir leeYangC (r ++ [p.1, p.2])) -
      ((3 : ℂ) * ((k : ℂ) + 1) * ((k : ℂ) + 2) / 2) • negWordVir leeYangC (r ++ [k + 2])
      ∈ maxIdealVir leeYangC := by
  have h := applyWord_mem_maxIdealVir leeYangC r (sigmaWord_mem k)
  unfold sigmaWord quadWord at h
  rw [map_sub, map_smul, map_smul, map_sum] at h
  simp only [← negWordVir_append] at h
  exact h

/-! ## §4  Gap-two words -/

/-- A **gap-two word**: adjacent entries differ by at least two (Rogers–Ramanujan condition).
In the entry convention `i ↦ L₋ᵢ₋₂` this is the "parts `≥ 2`, difference `≥ 2`" condition. -/
def GapTwo (w : List ℕ) : Prop := w.IsChain (fun a b => b + 2 ≤ a)

instance (w : List ℕ) : Decidable (GapTwo w) := by unfold GapTwo; infer_instance

theorem GapTwo.sorted : ∀ {w : List ℕ}, GapTwo w → SortedWord w
  | [], _ => sortedWord_nil
  | [a], _ => sortedWord_singleton a
  | a :: b :: l, h => by
      rw [GapTwo, List.isChain_cons_cons] at h
      have ih := GapTwo.sorted (w := b :: l) h.2
      refine SortedWord.cons ih ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := ih.head_ge x hx; omega

theorem exists_violation : ∀ {w : List ℕ}, SortedWord w → ¬ GapTwo w →
    ∃ l₁ a b l₂, w = l₁ ++ a :: b :: l₂ ∧ b ≤ a ∧ a < b + 2
  | [], _, h => absurd List.IsChain.nil h
  | [a], _, h => absurd (List.IsChain.singleton a) h
  | a :: b :: l, hs, h => by
      by_cases hab : b + 2 ≤ a
      · have h' : ¬ GapTwo (b :: l) := fun h' => h (List.IsChain.cons_cons hab h')
        obtain ⟨l₁, x, y, l₂, he, h1, h2⟩ := exists_violation hs.tail h'
        exact ⟨a :: l₁, x, y, l₂, by rw [he]; rfl, h1, h2⟩
      · exact ⟨[], a, b, l, rfl, hs.head_ge b (by simp), by omega⟩

/-- Sum of squares of the entries: the spreading potential. -/
def sqSum (w : List ℕ) : ℕ := (w.map (· ^ 2)).sum

theorem sqSum_perm {w w' : List ℕ} (h : w.Perm w') : sqSum w = sqSum w' :=
  (h.map _).sum_eq

theorem sqSum_append_pair (r : List ℕ) (e f : ℕ) : sqSum (r ++ [e, f]) = sqSum r + e ^ 2 + f ^ 2 := by
  simp [sqSum, List.sum_append]; ring

theorem sqSum_le (w : List ℕ) : sqSum w ≤ energyVir w ^ 2 := by
  induction w with
  | nil => simp [sqSum]
  | cons a w ih =>
      have h : sqSum (a :: w) = a ^ 2 + sqSum w := by simp [sqSum]
      rw [h, energyVir_cons]
      nlinarith [ih, Nat.zero_le a, Nat.zero_le (energyVir w)]

theorem sq_spread {a b e f : ℕ} (hs : e + f = a + b) (hba : b ≤ a) (hab : a < b + 2)
    (hea : e ≠ a) (heb : e ≠ b) : a ^ 2 + b ^ 2 < e ^ 2 + f ^ 2 := by
  rcases (by omega : a < e ∨ e < b) with h | h
  · obtain ⟨x, rfl⟩ : ∃ x, e = a + 1 + x := ⟨e - a - 1, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, b = f + 1 + x + y := ⟨b - f - 1 - x, by omega⟩
    nlinarith
  · obtain ⟨x, rfl⟩ : ∃ x, b = e + 1 + x := ⟨b - e - 1, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, f = a + 1 + x + y := ⟨f - a - 1 - x, by omega⟩
    nlinarith

/-! ## §5  The straightening -/

/-- Gap-two words of length `≤ ℓ` and energy `N`, in `V(-22/5,0)`. -/
noncomputable def gapSpan (ℓ N : ℕ) : Submodule ℂ (VirUniv leeYangC) :=
  Submodule.span ℂ
    {x | ∃ u : List ℕ, GapTwo u ∧ energyVir u = N ∧ u.length ≤ ℓ ∧ negWordVir leeYangC u = x}

/-- Gap-two words plus the maximal ideal. -/
noncomputable def goodSpan (ℓ N : ℕ) : Submodule ℂ (VirUniv leeYangC) :=
  gapSpan ℓ N ⊔ maxIdealVir leeYangC

theorem gapSpan_mono {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') (N : ℕ) : gapSpan ℓ N ≤ gapSpan ℓ' N :=
  Submodule.span_mono fun _ ⟨u, hu, he, hl, hx⟩ => ⟨u, hu, he, hl.trans h, hx⟩

theorem goodSpan_mono {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') (N : ℕ) : goodSpan ℓ N ≤ goodSpan ℓ' N :=
  sup_le_sup_right (gapSpan_mono h N) _

theorem perm_violation (l₁ l₂ : List ℕ) (a b : ℕ) :
    ((l₁ ++ l₂) ++ [a, b]).Perm (l₁ ++ a :: b :: l₂) := by
  rw [List.append_assoc]
  exact (List.perm_append_comm (l₁ := l₂) (l₂ := [a, b])).append_left l₁

/-- **Straightening.**  Every sorted word of length `ℓ` lies in the span of gap-two words of
length `≤ ℓ` and the same energy, modulo the maximal ideal. -/
theorem sorted_mem_goodSpan : ∀ ℓ : ℕ, ∀ u : List ℕ, SortedWord u → u.length = ℓ →
    negWordVir leeYangC u ∈ goodSpan ℓ (energyVir u) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihℓ =>
  -- lower-length words of energy `N` are already good at length `ℓ`
  have hlow : ∀ (N : ℕ) (w : List ℕ), w.length < ℓ → energyVir w = N →
      negWordVir leeYangC w ∈ goodSpan ℓ N := by
    intro N w hw hN
    have hmem := negWordVir_mem_virFil leeYangC (le_refl w.length) hN
    have hle : virFil leeYangC w.length (N : ℤ) ≤ goodSpan ℓ N := by
      rw [virFil, Submodule.span_le]
      rintro _ ⟨u, hu, hen, hl, rfl⟩
      have hen' : energyVir u = N := by exact_mod_cast hen
      have := ihℓ u.length (by omega) u hu rfl
      rw [hen'] at this
      exact goodSpan_mono (by omega) N this
    exact hle hmem
  have hlowFil : ∀ (N : ℕ) (m : ℕ), m < ℓ → virFil leeYangC m (N : ℤ) ≤ goodSpan ℓ N := by
    intro N m hm
    rw [virFil, Submodule.span_le]
    rintro _ ⟨u, hu, hen, hl, rfl⟩
    exact hlow N u (by omega) (by exact_mod_cast hen)
  suffices H : ∀ t : ℕ, ∀ u : List ℕ, SortedWord u → u.length = ℓ →
      energyVir u ^ 2 - sqSum u = t → negWordVir leeYangC u ∈ goodSpan ℓ (energyVir u) by
    intro u hu hl
    exact H _ u hu hl rfl
  intro t
  induction t using Nat.strong_induction_on with
  | _ t iht =>
  intro u hu hl ht
  by_cases hg : GapTwo u
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨u, hg, rfl, hl.le, rfl⟩)
  obtain ⟨l₁, a, b, l₂, rfl, hba, hab⟩ := exists_violation hu hg
  set u := l₁ ++ a :: b :: l₂ with hu_def
  set r := l₁ ++ l₂ with hr
  set N := energyVir u with hN
  set k := a + b with hk
  have hperm : (r ++ [a, b]).Perm u := perm_violation l₁ l₂ a b
  have hlenr : r.length + 2 = ℓ := by
    rw [← hl, ← hperm.length_eq]; simp
  have hEpair : ∀ e f : ℕ, e + f = k → energyVir (r ++ [e, f]) = N := by
    intro e f hef
    rw [hN, ← energyVir_perm hperm, energyVir_eq_sum, energyVir_eq_sum]
    simp [List.sum_append]; omega
  -- each summand, compared with `u`
  have hterm : ∀ p ∈ Finset.antidiagonal k,
      negWordVir leeYangC (r ++ [p.1, p.2]) -
        (if p.1 = a ∨ p.1 = b then (1 : ℂ) else 0) • negWordVir leeYangC u ∈ goodSpan ℓ N := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    set w := r ++ [p.1, p.2] with hw
    have hwE : energyVir w = N := hEpair p.1 p.2 hp
    have hwl : w.length = ℓ := by rw [hw]; simp; omega
    have hdiff := negWordVir_sub_sortDesc_mem leeYangC w
    rw [hwE] at hdiff
    have hdiff' : negWordVir leeYangC w - negWordVir leeYangC (sortDesc w) ∈ goodSpan ℓ N :=
      hlowFil N _ (by omega) hdiff
    by_cases hpa : p.1 = a ∨ p.1 = b
    · rw [if_pos hpa, one_smul]
      have hwu : sortDesc w = u := by
        have hpw : w.Perm u := by
          rcases hpa with h1 | h1
          · have h2 : p.2 = b := by omega
            rw [hw, h1, h2]; exact hperm
          · have h2 : p.2 = a := by omega
            rw [hw, h1, h2]
            exact ((List.Perm.swap a b []).append_left r).trans hperm
        exact List.Perm.eq_of_pairwise (fun x y _ _ h1 h2 => le_antisymm h2 h1)
          (sortDesc_sorted w) hu ((sortDesc_perm w).trans hpw)
      rwa [hwu] at hdiff'
    · rw [if_neg hpa, zero_smul, sub_zero]
      have hsq : sqSum u < sqSum (sortDesc w) := by
        rw [sqSum_perm (sortDesc_perm w), hw, sqSum_append_pair, ← sqSum_perm hperm,
          sqSum_append_pair]
        have := sq_spread (e := p.1) (f := p.2) (by omega) hba hab
          (fun h => hpa (Or.inl h)) (fun h => hpa (Or.inr h))
        omega
      have hsE : energyVir (sortDesc w) = N := by rw [energyVir_sortDesc, hwE]
      have hbound := sqSum_le (sortDesc w)
      rw [hsE] at hbound
      have hmem := iht (energyVir (sortDesc w) ^ 2 - sqSum (sortDesc w))
        (by rw [← ht, hsE]; omega) (sortDesc w) (sortDesc_sorted w)
        (by rw [length_sortDesc, hwl]) rfl
      rw [hsE] at hmem
      have := Submodule.add_mem _ hdiff' hmem
      simpa using this
  have hsum := Submodule.sum_mem (goodSpan ℓ N) hterm
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_boole] at hsum
  set m : ℂ := (((Finset.antidiagonal k).filter (fun p : ℕ × ℕ => p.1 = a ∨ p.1 = b)).card : ℂ)
    with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Nat.cast_ne_zero]
    apply Finset.card_ne_zero_of_mem (a := (a, b))
    simp [Finset.mem_filter, Finset.mem_antidiagonal, hk]
  have hrel := leeYangRelation_mem r k
  have hY : negWordVir leeYangC (r ++ [k + 2]) ∈ goodSpan ℓ N := by
    apply hlow N _ (by simp; omega)
    rw [hN, ← energyVir_perm hperm, energyVir_eq_sum, energyVir_eq_sum]
    simp [List.sum_append]; omega
  have hcomb : ((5 : ℂ) * m) • negWordVir leeYangC u =
      ((5 : ℂ) • (∑ p ∈ Finset.antidiagonal k, negWordVir leeYangC (r ++ [p.1, p.2])) -
        ((3 : ℂ) * ((k : ℂ) + 1) * ((k : ℂ) + 2) / 2) • negWordVir leeYangC (r ++ [k + 2])) +
      ((3 : ℂ) * ((k : ℂ) + 1) * ((k : ℂ) + 2) / 2) • negWordVir leeYangC (r ++ [k + 2]) -
      (5 : ℂ) • ((∑ p ∈ Finset.antidiagonal k, negWordVir leeYangC (r ++ [p.1, p.2])) -
        m • negWordVir leeYangC u) := by
    rw [mul_smul]; module
  have h5m : ((5 : ℂ) * m) • negWordVir leeYangC u ∈ goodSpan ℓ N := by
    rw [hcomb]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.mem_sup_right hrel)
      (Submodule.smul_mem _ _ hY)) (Submodule.smul_mem _ _ hsum)
  have h5m0 : (5 : ℂ) * m ≠ 0 := mul_ne_zero (by norm_num) hm0
  have := Submodule.smul_mem _ ((5 : ℂ) * m)⁻¹ h5m
  rwa [smul_smul, inv_mul_cancel₀ h5m0, one_smul] at this

/-- The universal length step is contained in gap-two words plus the maximal ideal. -/
theorem virFil_le_goodSpan (ℓ N : ℕ) : virFil leeYangC ℓ (N : ℤ) ≤ goodSpan ℓ N := by
  rw [virFil, Submodule.span_le]
  rintro _ ⟨u, hu, hen, hl, rfl⟩
  have hen' : energyVir u = N := by exact_mod_cast hen
  have := sorted_mem_goodSpan u.length u hu rfl
  rw [hen'] at this
  exact goodSpan_mono hl N this

theorem gapSpan_le_virFil (ℓ N : ℕ) : gapSpan ℓ N ≤ virFil leeYangC ℓ (N : ℤ) := by
  rw [gapSpan, Submodule.span_le]
  rintro _ ⟨u, hu, hen, hl, rfl⟩
  exact negWordVir_mem_virFil_of_sorted leeYangC hu.sorted hl hen

/-- **Gap-two spanning of the Lee–Yang PBW flag.**  The length-`≤ p`, weight-`N` step of the
length filtration on `L(-22/5,0)` is the image of the span of gap-two words of length `≤ p` and
energy `N`. -/
theorem goodFil_leeYang_eq_gapSpan (p N : ℕ) :
    goodFil leeYangC p (N : ℤ) = (gapSpan p N).map (maxIdealVir leeYangC).mkQ := by
  apply le_antisymm
  · rw [goodFil]
    refine (Submodule.map_mono (virFil_le_goodSpan p N)).trans ?_
    rw [goodSpan, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  · exact Submodule.map_mono (gapSpan_le_virFil p N)

end VOA.LeeYangCharacter
