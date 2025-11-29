
/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM


/-!
# BinarySearch on a sorted array

In this file we introduce `contains_bs` which is a binary search algoithm on `SortedArrayFun`.
The time complexity of `contains_bs` is the number of array accesses.

--
## Main results

- `bs_correct`: Given a key `q`, `contains_bs` returns some index
                if and only if the array contains `q`.
- `bs_time`: the number of array accesses is at most `Nat.log 2 (n-1) + 2`.

-/

namespace TimeM

set_option autoImplicit false
set_option tactic.hygienic false

structure SortedArrayFun (α : Type) [LinearOrder α] (n : ℕ) where
  get : ℕ → α
  size : ℕ := n
  sorted: Monotone get

variable {α : Type} [LinearOrder α]

def contains_bs {n : ℕ} (arr : SortedArrayFun α n) (q : α) : TimeM (Option ℕ) :=
  bs_aux 0 (n-1)
  where bs_aux (a b : ℕ) (h: a ≤ b := by omega): TimeM (Option ℕ) := do
  if h: a = b then
    if q = arr.get a then ✓ (some a)
    else ✓ none
  else
    let mid := (a+b)/(2 :ℕ)
    let arr_mid := arr.get mid
    if q < arr_mid then
      let result ← bs_aux a mid
      ✓ result
    else if arr_mid < q then
      let result ← bs_aux (mid+1) b
      ✓ result
    else ✓ (some mid)

theorem subinterval_to_interval_qlt {n : ℕ} (arr : SortedArrayFun α n) (q : α) (a mid b : ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q : q < arr.get mid) :
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, a ≤ i ∧ i ≤ mid ∧ arr.get i = q)  := by
  constructor
  · intro h'
    obtain ⟨i,hi⟩ := h'
    use i
    suffices  i ≤ mid by grind
    replace hi: arr.get i = q := by grind
    rw [← hi] at h_q
    have: Monotone arr.get := arr.sorted
    simp only [Monotone] at this
    by_contra h_con
    simp at h_con
    have h_con': mid ≤ i := by grind
    grind
  · grind

theorem subinterval_to_interval_qgt {n : ℕ} (arr : SortedArrayFun α n) (q : α) (a mid b : ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q : arr.get mid < q) :
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, (mid+1) ≤ i ∧ i ≤ b ∧ arr.get i = q)  := by
  constructor
  · intro h'
    obtain ⟨i,hi⟩ := h'
    use i
    suffices  mid ≤ i by grind
    replace hi: arr.get i = q := by grind
    rw [← hi] at h_q
    have: Monotone arr.get := arr.sorted
    simp only [Monotone] at this
    by_contra h_con
    simp at h_con
    have h_con': i ≤ mid := by grind
    grind
  · grind


theorem bs_correct (n : ℕ) (q : α) (h : 0 < n) (arr : SortedArrayFun α n) :
  (∃ i, i < n ∧ arr.get i = q) ↔ ((contains_bs arr q).ret ≠ none) := by
  unfold contains_bs
  have := bs_correct_aux n q arr 0 (n-1) (by omega)
  grind
where bs_correct_aux (n : ℕ) (q : α) (arr : SortedArrayFun α n) (a b : ℕ) (h_le : a ≤ b) :
(∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ ((contains_bs.bs_aux arr q a b h_le).ret ≠ none) := by {
    fun_induction contains_bs.bs_aux
    · simp_all only [le_refl, tick, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
      use b_1
    · simp
      grind
    · simp_all only [ne_eq, Bind.bind, tick, ret_bind]
      rw [← ih1]
      rw [subinterval_to_interval_qlt arr q a_1 mid b_1 (by grind) (by grind)]
    · simp_all only [not_lt, ne_eq, Bind.bind, tick, ret_bind]
      rw [← ih1]
      rw [subinterval_to_interval_qgt arr q a_1 (mid) b_1 (by grind) (by grind)]
    · simp only [tick, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
      grind
}


theorem bs_return_correct_idx (n : ℕ) (q : α) (arr : SortedArrayFun α n) :
  ∀ i, (contains_bs arr q).ret = some i → arr.get i = q := by
    intro i hi
    apply bs_return_correct_idx_aux n q 0 (n-1) (by omega)
    rw [contains_bs.eq_def] at hi
    exact hi
where bs_return_correct_idx_aux (n : ℕ) (q : α) (a b : ℕ)
  (h_ab : a ≤ b) (arr : SortedArrayFun α n) :
  ∀ i : ℕ, (contains_bs.bs_aux arr q a b h_ab).ret = some i → arr.get i = q := by {
    fun_induction contains_bs.bs_aux
    · intro i hi
      have h_eq : i = b_1 := by aesop
      rw [h_eq]
      apply Eq.symm
      exact h_1
    · intro i hi
      contradiction
    · intro i hi
      apply ih1
      exact hi
    · intro i hi
      apply ih1
      exact hi
    · intro i hi
      have h_eq : i = mid := by aesop
      grind
  }

-- This recursive function g has the smallest number of cases.
def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

private def g' (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else g' (n/2) + 1

theorem g'_eq_g : g' = g := by
  ext n
  fun_induction g' <;> first | simp [g] | unfold g; rw [ih1]; simpa

-- Function g' is more convenient to work with functional induction.
theorem g'_close_form (n : ℕ) : g' n ≤ (Nat.log 2 n) +1  := by
  fun_induction g'
  · simp only [Nat.log_zero_right, zero_add, zero_le]
  · simp only [Nat.log_one_right, zero_add, le_refl]
  · simp only [add_le_add_iff_right]
    grw [ih1]
    simp only [Nat.log_div_base]
    rw [Nat.sub_add_cancel ?_]
    (expose_names; rw [propext (Nat.le_log_iff_pow_le Nat.le.refl h)])
    grind

theorem g_monotone : Monotone g := by
  intro a b hab
  apply g_monotone_aux b (by omega) (by omega)
where g_monotone_aux {a b : ℕ} (n : ℕ) (hab : a ≤ b) (hn : b ≤ n) : g a ≤ g b := by {
  induction n using Nat.strong_induction_on generalizing a b
  unfold g
  split_ifs
  · simp only [le_refl]
  · simp only [le_add_iff_nonneg_left, zero_le]
  · simp_all only [nonpos_iff_eq_zero]
  · simp_all only [add_le_add_iff_right]
    expose_names
    apply a_1
    pick_goal 4
    · exact n_1/2
    all_goals omega
}

theorem bs_time (n : ℕ) (q : α) (arr : SortedArrayFun α n) :
  (contains_bs arr q).time ≤ Nat.log 2 (n-1) + 2 := by
  have:= bs_time_le_g n q arr 0 (n-1) (by omega)
  simp only [tsub_zero] at this
  simp only [contains_bs, ge_iff_le]
  grw [this]
  rw [← g'_eq_g]
  simp only [add_le_add_iff_right]
  exact g'_close_form (n - 1)
where bs_time_le_g (n : ℕ) (q : α) (arr : SortedArrayFun α n) (a b : ℕ) (h_le : a ≤ b) :
  (contains_bs.bs_aux arr q a b).time ≤ g (b-a) + 1 := by {
  fun_induction contains_bs.bs_aux arr q a b
  · simp
  · simp
  · simp_all only [Bind.bind, tick, time_of_bind, add_le_add_iff_right]
    grw [ih1]
    subst mid
    have: (b_1 - a_1)/2 = (a_1 + b_1) / 2 - a_1 := by grind
    rw [← this]
    conv =>
      right
      unfold g
    split_ifs<;> try grind
  · simp only [Bind.bind, tick, time_of_bind, add_le_add_iff_right]
    grw [ih1]
    subst mid
    have: b_1 - ((a_1 + b_1) / 2 + 1) ≤ (b_1 - a_1)/2  := by grind
    have gmono:= g_monotone
    simp [Monotone] at gmono
    conv =>
      right
      unfold g
    split_ifs <;> try grind
  · simp
}
end TimeM
