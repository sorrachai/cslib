/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

import Cslib.Init

/-!

# TimeM: Time Complexity Monad
`TimeM α` represents a computation that produces a value of type `α` and tracks its time cost.

## Design Principles
1. **Pure inputs, timed outputs**: Functions take plain values and return `TimeM` results
2. **Time annotations are trusted**: The `time` field is NOT verified against actual cost.
   You must manually ensure annotations match the algorithm's complexity in your cost model.
3. **Separation of concerns**: Prove correctness properties on `.ret`, prove complexity on `.time`

## Cost Model
**Document your cost model explicitly** Decide and be consistent about:
- **What costs 1 unit?** (comparison, arithmetic operation, etc.)
- **What is free?** (variable lookup, pattern matching, etc.)
- **Recursive calls:** Do you charge for the call itself?

## Notation
- **`✓`** : A tick of time, see `tick`.
- **`⟪tm⟫`** : Extract the pure value from a `TimeM` computation (notation for `tm.ret`)

## References

See [Danielsson2008] for the discussion.
-/
namespace Cslib.Algorithms.Lean


/-- A monad for tracking time complexity of computations.
`TimeM α` represents a computation that returns a value of type `α`
and accumulates a time cost (represented as a natural number). -/
structure TimeM (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated time cost of the computation -/
  time : ℕ

namespace TimeM

/-- Lifts a pure value into a `TimeM` computation with zero time cost. -/
private def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

/-- Sequentially composes two `TimeM` computations, summing their time costs. -/
private def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

-- The Monad Instance
instance : Monad TimeM where
  pure := pure
  bind := bind


-- The `tick` function returns PUnit (separation of cost and value)
/-- Advances the time cost by `c` (default 1) without changing the value. -/
def tick (c : ℕ := 1) : TimeM PUnit := ⟨.unit, c⟩

-- Notation Macros
-- This allows writing `✓ return x` or `✓ let y := ...` inside do blocks.
macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do TimeM.tick $c; $body:doElem)
macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

/-- Notation for extracting the return value: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

-- Simplification Lemmas
@[simp] theorem ret_pure {α} (a : α) : (pure a : TimeM α).ret = a := rfl
@[simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (m >>= f).ret = (f m.ret).ret := rfl
@[simp] theorem ret_tick (c : ℕ) : (tick c).ret = () := rfl
 -- This ensures 'ret' moves inside 'if-then-else' blocks
@[simp] theorem ret_ite {α} (c : Prop) [Decidable c] (t e : TimeM α) :
  (if c then t else e).ret = if c then t.ret else e.ret := by split <;> rfl
-- Ensure 'ret' can see through the Monad instance 'pure'
@[simp] theorem ret_monad_pure {α} (a : α) :
  (return a : TimeM α).ret = a := rfl

@[simp] theorem time_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (m >>= f).time = m.time + (f m.ret).time := rfl
@[simp] theorem time_pure {α} (a : α) : (Pure.pure a : TimeM α).time = 0 := rfl
@[simp] theorem time_tick (c : ℕ) : (tick c).time = c := rfl

@[simp] theorem time_ite {α} (prop : Prop) [Decidable prop] (t e : TimeM α) :
  (if prop then t else e).time = if prop then t.time else e.time := by
  split <;> rfl

-- Rules for Functor/Applicative (map and seq)
@[simp] theorem ret_map {α β} (f : α → β) (m : TimeM α) : (f <$> m).ret = f m.ret := rfl
@[simp] theorem time_map {α β} (f : α → β) (m : TimeM α) : (f <$> m).time = m.time := rfl

@[simp] theorem ret_seq {α β} (f : TimeM (α → β)) (x : TimeM α) :
  (f <*> x).ret = f.ret x.ret := rfl
@[simp] theorem time_seq {α β} (f : TimeM (α → β)) (x : TimeM α) :
  (f <*> x).time = f.time + x.time := rfl

@[congr]
theorem bind_congr {α β} {m1 m2 : TimeM α} {f1 f2 : α → TimeM β}
    (h_m : m1 = m2) (h_f : ∀ x, f1 x = f2 x) : m1 >>= f1 = m2 >>= f2 := by
  subst h_m
  exact _root_.bind_congr h_f

-- SeqRight (*>)
@[simp] theorem ret_seqRight {α β} (x : TimeM α) (y : TimeM β) :
  (x *> y).ret = y.ret := rfl

@[simp] theorem time_seqRight {α β} (x : TimeM α) (y : TimeM β) :
  (x *> y).time = x.time + y.time := rfl

-- SeqLeft (<*)
@[simp] theorem ret_seqLeft {α β} (x : TimeM α) (y : TimeM β) :
  (x <* y).ret = x.ret := rfl

@[simp] theorem time_seqLeft {α β} (x : TimeM α) (y : TimeM β) :
  (x <* y).time = x.time + y.time := rfl

end TimeM

end Cslib.Algorithms.Lean
