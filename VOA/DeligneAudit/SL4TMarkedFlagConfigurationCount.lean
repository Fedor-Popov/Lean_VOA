import VOA.DeligneAudit.SL4TMarkedFlagDeformationAudit
import VOA.DeligneAudit.SL4TStratumConfigurationRecursion
import VOA.DeligneAudit.SL4TStratumInvariantCount

/-!
# Counting marked full-flag configurations by their selected doubles

A paired configuration with one doubled site has its double inside a selected set `Y` in exactly
`C(|Y|, 2) · (n - 2)!` of its `n!/2` labellings (`oneDoubleStratum_card`, stated without
division: `2 · #{double ⊄ Y} + 2 · C(|Y|, 2) · (n - 2)! = n!`). The proof deletes the positions
outside `Y` one at a time with the existing deletion recursion.

A singly marked configuration is the marked root at the zero point together with a paired
configuration of the other roots; a doubly marked configuration has the zero pair (one root of
each group) at the zero point. Its selected doubles (`singlyMarkedSelectedDoubles`,
`doublyMarkedSelectedDoubles`) are the points carrying two selected roots: the doubled sites inside
`Y` and, for the doubly marked flag, the zero pair when both of its roots lie in `Y`. The number of
configurations with fewer than `j` selected doubles is a sum of unmarked stratum counts
(`singlyMarkedSelectedDoubles_card`, `doublyMarkedSelectedDoubles_card`). With one double these
counts are closed forms that match the lower bounds already proved for the stratum ideals
(`singlyMarked_oneDouble_count`, `doublyMarked_oneDouble_count`,
`doublyMarked_twoDouble_count`): the complement of each lower-bound count is exactly the number
of configurations with fewer selected doubles.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Finset

/-- `2 · C(n, 2) · (n - 2)! = n!`. -/
theorem two_mul_choose_two_mul_factorial (n : ℕ) (hn : 2 ≤ n) :
    2 * n.choose 2 * (n - 2).factorial = n.factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial hn
  rw [Nat.factorial_two] at h
  rw [mul_comm 2 (n.choose 2)]
  exact h

/-- With one doubled site, the whole position set contains the double. -/
theorem fullFlagDoublesIn_univ_one (n : ℕ) (hn : 2 ≤ n) (f : FullFlagConfiguration n 1) :
    fullFlagDoublesIn Finset.univ f = 1 := by
  unfold fullFlagDoublesIn
  rw [Finset.card_eq_one]
  refine ⟨⟨0, by omega⟩, ?_⟩
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, implies_true, and_true, true_and,
    Finset.mem_singleton]
  constructor
  · intro h
    exact Fin.ext (by simp only; omega)
  · rintro rfl
    simp

/-- A set of positions avoiding `0` is the shift of its preimage. -/
theorem finset_eq_map_succ_of_zero_notMem {m : ℕ} (Y : Finset (Fin (m + 1)))
    (h0 : (0 : Fin (m + 1)) ∉ Y) :
    (Finset.univ.filter fun j : Fin m => j.succ ∈ Y).map (Fin.succEmb m) = Y := by
  ext x
  refine Fin.cases ?_ (fun j => ?_) x
  · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_succEmb]
    constructor
    · rintro ⟨j, _, hj⟩
      exact absurd hj (Fin.succ_ne_zero j)
    · intro h
      exact absurd h h0
  · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_succEmb]
    constructor
    · rintro ⟨i, hi, hij⟩
      rw [Fin.succ_inj.mp hij] at hi
      exact hi
    · intro h
      exact ⟨j, h, rfl⟩

/-- **The one-double stratum count.** Among the `n!/2` paired configurations with one double,
`C(|Y|, 2) (n - 2)!` have their double inside `Y`. -/
theorem oneDoubleStratum_card (m : ℕ) (Y : Finset (Fin (m + 2))) :
    2 * Nat.card (FullFlagStratumConfiguration (m + 2) 1 1 Y) +
        2 * Y.card.choose 2 * m.factorial = (m + 2).factorial := by
  classical
  induction m with
  | zero =>
      by_cases hY : Y = Finset.univ
      · subst hY
        haveI : IsEmpty (FullFlagStratumConfiguration (0 + 2) 1 1 Finset.univ) :=
          ⟨fun f => by
            have h := f.property
            rw [fullFlagDoublesIn_univ_one (0 + 2) (by omega)] at h
            omega⟩
        rw [Nat.card_of_isEmpty, Finset.card_univ, Fintype.card_fin]
        decide
      · obtain ⟨i, hi⟩ : ∃ i, i ∉ Y := by
          by_contra h
          exact hY (Finset.eq_univ_iff_forall.mpr fun x => by
            by_contra hx
            exact h ⟨x, hx⟩)
        let e := Equiv.swap (0 : Fin 2) i
        have h0 : (0 : Fin 2) ∉ Y.map e.toEmbedding := by
          simp only [Finset.mem_map_equiv]
          change e.symm 0 ∉ Y
          rw [Equiv.symm_swap, Equiv.swap_apply_left]
          exact hi
        have hmap := finset_eq_map_succ_of_zero_notMem (Y.map e.toEmbedding) h0
        have hcard := Nat.card_congr (fullFlagStratumConfiguration_relabel 2 1 1 Y e)
        rw [← hmap, fullFlagStratumConfiguration_card_recursion 1 1 1 _ (by omega)] at hcard
        have hall := Nat.card_congr (fullFlagStratumConfiguration_allEquiv 1 0 1
          (Finset.univ.filter fun j : Fin 1 => j.succ ∈ Y.map e.toEmbedding) (by omega))
        have hfac := fullFlagConfiguration_card_closed 1 0 (by omega)
        simp only [pow_zero, one_mul] at hfac
        have hY1 : Y.card ≤ 1 := by
          have := Finset.card_le_card (show Y ⊆ Finset.univ.erase i from
            fun y hy => Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hy), Finset.mem_univ _⟩)
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin] at this
          exact this
        rw [Nat.choose_eq_zero_of_lt (by omega : Y.card < 2)]
        simp only [Nat.sub_self] at hcard
        rw [hcard, hall, hfac]
        simp [Nat.factorial]
  | succ p ih =>
      by_cases hY : Y = Finset.univ
      · subst hY
        haveI : IsEmpty (FullFlagStratumConfiguration (p + 1 + 2) 1 1 Finset.univ) :=
          ⟨fun f => by
            have h := f.property
            rw [fullFlagDoublesIn_univ_one (p + 1 + 2) (by omega)] at h
            omega⟩
        rw [Nat.card_of_isEmpty, Finset.card_univ, Fintype.card_fin, mul_zero, zero_add]
        have h := two_mul_choose_two_mul_factorial (p + 1 + 2) (by omega)
        rwa [show p + 1 + 2 - 2 = p + 1 by omega] at h
      · obtain ⟨i, hi⟩ : ∃ i, i ∉ Y := by
          by_contra h
          exact hY (Finset.eq_univ_iff_forall.mpr fun x => by
            by_contra hx
            exact h ⟨x, hx⟩)
        let e := Equiv.swap (0 : Fin (p + 1 + 2)) i
        have h0 : (0 : Fin (p + 1 + 2)) ∉ Y.map e.toEmbedding := by
          simp only [Finset.mem_map_equiv]
          change e.symm 0 ∉ Y
          rw [Equiv.symm_swap, Equiv.swap_apply_left]
          exact hi
        let Y' := Finset.univ.filter fun j : Fin (p + 1 + 1) => j.succ ∈ Y.map e.toEmbedding
        have hmap : Y'.map (Fin.succEmb (p + 1 + 1)) = Y.map e.toEmbedding :=
          finset_eq_map_succ_of_zero_notMem (Y.map e.toEmbedding) h0
        have hY' : Y'.card = Y.card := by
          rw [← Finset.card_map (Fin.succEmb (p + 1 + 1)), hmap, Finset.card_map]
        have hcard := Nat.card_congr (fullFlagStratumConfiguration_relabel (p + 1 + 2) 1 1 Y e)
        rw [← hmap, fullFlagStratumConfiguration_card_recursion (p + 1 + 1) 1 1 Y'
          (by omega)] at hcard
        have hall := Nat.card_congr (fullFlagStratumConfiguration_allEquiv (p + 1 + 1) 0 1 Y'
          (by omega))
        have hfac := fullFlagConfiguration_card_closed (p + 1 + 1) 0 (by omega)
        simp only [pow_zero, one_mul] at hfac
        simp only [Nat.sub_self] at hcard
        rw [hcard, hall, hfac, ← hY']
        have hih : 2 * Nat.card (FullFlagStratumConfiguration (p + 1 + 1) 1 1 Y') +
            2 * Y'.card.choose 2 * p.factorial = (p + 1 + 1).factorial := ih Y'
        have e1 : (p + 1).factorial = (p + 1) * p.factorial := Nat.factorial_succ p
        have e2 : (p + 1 + 2).factorial = (p + 1 + 2) * (p + 1 + 1).factorial :=
          Nat.factorial_succ (p + 1 + 1)
        rw [show p + 1 + 1 + 1 - 1 - 1 = p + 1 by omega, e1, e2, ← hih]
        ring

/-! ### Singly marked configurations -/

/-- The selected doubles of a singly marked configuration: the doubled sites whose two roots lie
in `Y`. The zero point carries one root and never counts. -/
def singlyMarkedSelectedDoubles {B k : ℕ} {V : Finset (Fin (B + 1))} (Y : Finset (Fin (B + 1)))
    (c : SinglyMarkedConfiguration B k V) : ℕ :=
  fullFlagDoublesIn (deletedGroup c.1.val Y) c.2

/-- Singly marked configurations with fewer than `j` selected doubles, counted by the marked
root at zero. -/
theorem singlyMarkedSelectedDoubles_card (B k j : ℕ) (V Y : Finset (Fin (B + 1))) :
    Nat.card {c : SinglyMarkedConfiguration B k V // singlyMarkedSelectedDoubles Y c < j} =
      ∑ v ∈ V, Nat.card (FullFlagStratumConfiguration B k j (deletedGroup v Y)) := by
  classical
  refine (Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (v : {v : Fin (B + 1) // v ∈ V}) (f : FullFlagConfiguration B k) =>
      fullFlagDoublesIn (deletedGroup v.val Y) f < j))).trans ?_
  rw [Nat.card_sigma]
  exact Finset.sum_coe_sort V
    (fun v => Nat.card (FullFlagStratumConfiguration B k j (deletedGroup v Y)))

/-- Summing `C(|Y ∖ v|, 2)` over a group splits by membership in `Y`. -/
theorem sum_deletedGroup_choose_two {n : ℕ} (V Y : Finset (Fin (n + 1))) :
    ∑ v ∈ V, (deletedGroup v Y).card.choose 2 =
      (V ∩ Y).card * (Y.card - 1).choose 2 + (V \ Y).card * Y.card.choose 2 := by
  classical
  have h : ∀ v ∈ V, (deletedGroup v Y).card.choose 2 =
      if v ∈ Y then (Y.card - 1).choose 2 else Y.card.choose 2 := by
    intro v _
    split_ifs with hv
    · have := deletedGroup_card_of_mem Y v hv
      rw [show (deletedGroup v Y).card = Y.card - 1 by omega]
    · rw [deletedGroup_card_of_notMem Y v hv]
  rw [Finset.sum_congr rfl h, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff, smul_eq_mul, smul_eq_mul]

/-- **Singly marked count.** With one double on `p + 3` roots (`h = p + 1`), the configurations
with no selected double and the lower-bound count of `singlyMarkedOneDoubleCount` add up to all
`|V| (p + 2)!/2` configurations. -/
theorem singlyMarked_oneDouble_count (p : ℕ) (V Y : Finset (Fin (p + 3))) :
    2 * Nat.card {c : SinglyMarkedConfiguration (p + 2) 1 V //
        singlyMarkedSelectedDoubles Y c < 1} +
      2 * singlyMarkedOneDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card * p.factorial =
        V.card * (p + 2).factorial := by
  classical
  have hY := compl_inter_card_add_inter_card V Y
  have hcount : singlyMarkedOneDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card =
      ∑ v ∈ V, (deletedGroup v Y).card.choose 2 := by
    rw [sum_deletedGroup_choose_two, singlyMarkedOneDoubleCount, hY]
  have hsum : ∑ v ∈ V, (2 * Nat.card (FullFlagStratumConfiguration (p + 2) 1 1
      (deletedGroup v Y)) + 2 * (deletedGroup v Y).card.choose 2 * p.factorial) =
        ∑ v ∈ V, (p + 2).factorial :=
    Finset.sum_congr rfl (fun v _ => oneDoubleStratum_card p (deletedGroup v Y))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, smul_eq_mul] at hsum
  rw [singlyMarkedSelectedDoubles_card, hcount]
  linarith

/-! ### Doubly marked configurations -/

/-- The selected doubles of a doubly marked configuration: the zero pair when both of its roots
lie in `Y`, and the doubled sites inside `Y`. -/
def doublyMarkedSelectedDoubles {B k : ℕ} {V : Finset (Fin (B + 2))} (Y : Finset (Fin (B + 2)))
    (c : DoublyMarkedConfiguration B k V) : ℕ :=
  (if c.1.val ∈ Y ∧ c.1.val.succAbove c.2.1.val ∈ Y then 1 else 0) +
    fullFlagDoublesIn (deletedGroup c.2.1.val (deletedGroup c.1.val Y)) c.2.2

/-- A subtype of a sigma type is the sigma type of the fibrewise subtypes. -/
def subtypeSigmaEquivSigmaSubtype {α : Type*} {β : α → Type*} (P : (Σ a, β a) → Prop) :
    {c : Σ a, β a // P c} ≃ Σ a, {b : β a // P ⟨a, b⟩} where
  toFun c := ⟨c.1.1, ⟨c.1.2, c.2⟩⟩
  invFun c := ⟨⟨c.1, c.2.1⟩, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Doubly marked configurations with fewer than `j` selected doubles, counted by the zero
pair. -/
theorem doublyMarkedSelectedDoubles_card (B k j : ℕ) (V Y : Finset (Fin (B + 2))) :
    Nat.card {c : DoublyMarkedConfiguration B k V // doublyMarkedSelectedDoubles Y c < j} =
      ∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, Nat.card (FullFlagStratumConfiguration B k
        (j - if u ∈ Y ∧ u.succAbove v ∈ Y then 1 else 0)
        (deletedGroup v (deletedGroup u Y))) := by
  classical
  have hsplit : ∀ (u : {u : Fin (B + 2) // u ∉ V}),
      Nat.card {c : SinglyMarkedConfiguration B k (deletedGroup u.val V) //
        (if u.val ∈ Y ∧ u.val.succAbove c.1.val ∈ Y then 1 else 0) +
          fullFlagDoublesIn (deletedGroup c.1.val (deletedGroup u.val Y)) c.2 < j} =
        ∑ v ∈ deletedGroup u.val V, Nat.card (FullFlagStratumConfiguration B k
          (j - if u.val ∈ Y ∧ u.val.succAbove v ∈ Y then 1 else 0)
          (deletedGroup v (deletedGroup u.val Y))) := by
    intro u
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (v : {v : Fin (B + 1) // v ∈ deletedGroup u.val V}) (f : FullFlagConfiguration B k) =>
        (if u.val ∈ Y ∧ u.val.succAbove v.val ∈ Y then 1 else 0) +
          fullFlagDoublesIn (deletedGroup v.val (deletedGroup u.val Y)) f < j)), Nat.card_sigma]
    rw [← Finset.sum_coe_sort (deletedGroup u.val V)]
    apply Finset.sum_congr rfl
    intro v _
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro f
    constructor <;> intro h <;> omega
  rw [Nat.card_congr (subtypeSigmaEquivSigmaSubtype _), Nat.card_sigma,
    Finset.sum_subtype Vᶜ (p := fun u => u ∉ V) (fun x => Finset.mem_compl)]
  exact Finset.sum_congr rfl (fun u _ => hsplit u)

/-- A sum of a two-valued function over a group splits by membership in `Y`. -/
theorem sum_ite_mem_eq {n : ℕ} (V Y : Finset (Fin n)) (α β : ℕ) :
    ∑ w ∈ V, (if w ∈ Y then α else β) = (V ∩ Y).card * α + (V \ Y).card * β := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.filter_notMem_eq_sdiff, smul_eq_mul, smul_eq_mul]

/-- The pair sum of a weight depending only on which roots of the zero pair are selected. -/
theorem pair_sum_selected {n : ℕ} (V Y : Finset (Fin (n + 1))) (A B C D : ℕ) :
    ∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V,
        (if u.succAbove v ∈ Y then (if u ∈ Y then A else B) else (if u ∈ Y then C else D)) =
      (Vᶜ ∩ Y).card * ((V ∩ Y).card * A + (V \ Y).card * C) +
        (Vᶜ \ Y).card * ((V ∩ Y).card * B + (V \ Y).card * D) := by
  classical
  have hin : ∀ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V,
      (if u.succAbove v ∈ Y then (if u ∈ Y then A else B) else (if u ∈ Y then C else D)) =
        if u ∈ Y then (V ∩ Y).card * A + (V \ Y).card * C
        else (V ∩ Y).card * B + (V \ Y).card * D := by
    intro u hu
    rw [sum_deletedGroup_of_notMem (fun w =>
      if w ∈ Y then (if u ∈ Y then A else B) else (if u ∈ Y then C else D)) V u
      (Finset.mem_compl.mp hu), sum_ite_mem_eq]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl hin, sum_ite_mem_eq]

/-- Nested pair sums of a per-pair identity `2 T + 2 W c = K`. -/
theorem nested_pair_sum {n : ℕ} (V : Finset (Fin (n + 1))) (T W : Fin (n + 1) → Fin n → ℕ)
    (c K : ℕ) (h : ∀ u ∈ Vᶜ, ∀ v ∈ deletedGroup u V, 2 * T u v + 2 * W u v * c = K) :
    2 * (∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, T u v) +
        2 * (∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, W u v) * c = Vᶜ.card * V.card * K := by
  classical
  calc 2 * (∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, T u v) +
        2 * (∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, W u v) * c
      = ∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, (2 * T u v + 2 * W u v * c) := by
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
    _ = ∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, K :=
        Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => h u hu v hv
    _ = Vᶜ.card * V.card * K := by
        rw [Finset.sum_congr rfl fun u hu => by
          rw [Finset.sum_const, smul_eq_mul,
            deletedGroup_card_of_notMem V u (Finset.mem_compl.mp hu)]]
        rw [Finset.sum_const, smul_eq_mul, mul_assoc]

/-- The selected roots left after deleting the zero pair. -/
theorem deletedGroup_pair_card {n : ℕ} (Y : Finset (Fin (n + 2))) (u : Fin (n + 2))
    (v : Fin (n + 1)) :
    (deletedGroup v (deletedGroup u Y)).card + (if u ∈ Y then 1 else 0) +
      (if u.succAbove v ∈ Y then 1 else 0) = Y.card := by
  have h1 := card_eq_deletedGroup Y u
  have h2 := card_eq_deletedGroup (deletedGroup u Y) v
  have hv : v ∈ deletedGroup u Y ↔ u.succAbove v ∈ Y := mem_deletedGroup u Y v
  by_cases hu : u ∈ Y <;> by_cases hw : u.succAbove v ∈ Y <;>
    simp only [hu, hw, hv, if_true, if_false] at h1 h2 ⊢ <;> omega

/-- **Doubly marked count, one selected double.** On `p + 4` roots (`h = p + 1`), the
configurations without a selected double and the lower-bound count of
`doublyMarkedOneDoubleCount` add up to all `|U| |V| (p + 2)!/2` configurations. -/
theorem doublyMarked_oneDouble_count (p : ℕ) (V Y : Finset (Fin (p + 4))) :
    2 * Nat.card {c : DoublyMarkedConfiguration (p + 2) 1 V //
        doublyMarkedSelectedDoubles Y c < 1} +
      2 * doublyMarkedOneDoubleCount (p + 1) (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card
        (Vᶜ \ Y).card * p.factorial = Vᶜ.card * V.card * (p + 2).factorial := by
  classical
  have hY := compl_inter_card_add_inter_card V Y
  let W : Fin (p + 4) → Fin (p + 3) → ℕ := fun u v =>
    if u.succAbove v ∈ Y then (if u ∈ Y then (p + 1 + 1).choose 2 else (Y.card - 1).choose 2)
    else (if u ∈ Y then (Y.card - 1).choose 2 else Y.card.choose 2)
  have hD : doublyMarkedOneDoubleCount (p + 1) (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card
      (Vᶜ \ Y).card = ∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, W u v := by
    simp only [W]
    rw [pair_sum_selected, doublyMarkedOneDoubleCount, doublyMarkedResidualCount, hY]
    ring
  rw [doublyMarkedSelectedDoubles_card, hD]
  apply nested_pair_sum
  intro u _ v _
  have hc := deletedGroup_pair_card Y u v
  simp only [W]
  by_cases hu : u ∈ Y <;> by_cases hw : u.succAbove v ∈ Y
  · haveI : IsEmpty (FullFlagStratumConfiguration (p + 2) 1
        (1 - if u ∈ Y ∧ u.succAbove v ∈ Y then 1 else 0)
        (deletedGroup v (deletedGroup u Y))) :=
      ⟨fun f => by have := f.property; simp only [hu, hw, and_self, if_true] at this; omega⟩
    rw [Nat.card_of_isEmpty]
    simp only [hu, hw, if_true]
    have := two_mul_choose_two_mul_factorial (p + 2) (by omega)
    rw [show p + 2 - 2 = p by omega] at this
    show 2 * 0 + 2 * (p + 2).choose 2 * p.factorial = (p + 2).factorial
    linarith
  all_goals
    simp only [hu, hw, and_false, false_and, if_true, if_false, Nat.sub_zero] at hc ⊢
    have := oneDoubleStratum_card p (deletedGroup v (deletedGroup u Y))
    first
      | (rw [show Y.card - 1 = (deletedGroup v (deletedGroup u Y)).card by omega]; exact this)
      | (rw [show Y.card = (deletedGroup v (deletedGroup u Y)).card by omega]; exact this)

/-- **Doubly marked count, two selected doubles.** The configurations with at most one selected
double and the lower-bound count `a b C(a + b - 2, 2) (m - 1)!` add up to all configurations. -/
theorem doublyMarked_twoDouble_count (p : ℕ) (V Y : Finset (Fin (p + 4))) :
    2 * Nat.card {c : DoublyMarkedConfiguration (p + 2) 1 V //
        doublyMarkedSelectedDoubles Y c < 2} +
      2 * ((Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2) *
        p.factorial = Vᶜ.card * V.card * (p + 2).factorial := by
  classical
  have hY := compl_inter_card_add_inter_card V Y
  let W : Fin (p + 4) → Fin (p + 3) → ℕ := fun u v =>
    if u.succAbove v ∈ Y then (if u ∈ Y then (Y.card - 2).choose 2 else 0)
    else (if u ∈ Y then 0 else 0)
  have hD : (Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2 =
      ∑ u ∈ Vᶜ, ∑ v ∈ deletedGroup u V, W u v := by
    simp only [W]
    rw [pair_sum_selected, hY]
    ring
  rw [doublyMarkedSelectedDoubles_card, hD]
  apply nested_pair_sum
  intro u _ v _
  have hc := deletedGroup_pair_card Y u v
  have hall := Nat.card_congr (fullFlagStratumConfiguration_allEquiv (p + 2) 1 2
    (deletedGroup v (deletedGroup u Y)) (by omega))
  have hfac := fullFlagConfiguration_card_closed (p + 2) 1 (by omega)
  rw [pow_one] at hfac
  simp only [W]
  by_cases hu : u ∈ Y <;> by_cases hw : u.succAbove v ∈ Y
  · simp only [hu, hw, and_self, if_true, Nat.reduceSub] at hc ⊢
    have := oneDoubleStratum_card p (deletedGroup v (deletedGroup u Y))
    rw [show Y.card - 2 = (deletedGroup v (deletedGroup u Y)).card by omega]
    exact this
  all_goals
    simp only [hu, hw, and_false, false_and, if_true, if_false, Nat.sub_zero, mul_zero,
      zero_mul, add_zero] at hc ⊢
    rw [hall]
    omega

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.two_mul_choose_two_mul_factorial
#print axioms VOA.DeligneAudit.SL4T.fullFlagDoublesIn_univ_one
#print axioms VOA.DeligneAudit.SL4T.finset_eq_map_succ_of_zero_notMem
#print axioms VOA.DeligneAudit.SL4T.oneDoubleStratum_card
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedDoubles
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedDoubles_card
#print axioms VOA.DeligneAudit.SL4T.sum_deletedGroup_choose_two
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_oneDouble_count
#print axioms VOA.DeligneAudit.SL4T.subtypeSigmaEquivSigmaSubtype
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedSelectedDoubles
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedSelectedDoubles_card
#print axioms VOA.DeligneAudit.SL4T.sum_ite_mem_eq
#print axioms VOA.DeligneAudit.SL4T.pair_sum_selected
#print axioms VOA.DeligneAudit.SL4T.nested_pair_sum
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_pair_card
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_oneDouble_count
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_twoDouble_count
