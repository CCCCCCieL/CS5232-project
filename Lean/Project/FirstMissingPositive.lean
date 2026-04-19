import Auto

import Ssreflect.Lang

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 1
set_option auto.smt.solver.name "cvc5"

/-!
# First Missing Positive

This is the project file.
The goal is to return the first positive integer which is not in the array.
-/

namespace Project
namespace FirstMissingPositive

-- `x` occurs in the array, after casting `x` to an integer.
@[grind]
def occursPositive (a : Array Int) (x : Nat) : Prop :=
  exists i, i < a.size /\ a[i]! = Int.ofNat x

-- This is the main correctness statement for the answer.
@[grind]
def IsFirstMissingPositive (a : Array Int) (ans : Nat) : Prop :=
  0 < ans /\
  Not (occursPositive a ans) /\
  forall x, 0 < x -> x < ans -> occursPositive a x

/-!
The first implementation plan is simple:
try 1, then 2, then 3, and scan the array each time.

This is slower than the usual in-place algorithm, but the proof should be
easier to finish first.
-/

method firstMissingPositiveBaseline (a : Array Int) return (ans : Nat)
  ensures IsFirstMissingPositive a ans
  do
    -- TODO: replace this stub with the candidate-scanning loop.
    return 1

prove_correct firstMissingPositiveBaseline by
  -- TODO: prove the loop invariants after the implementation is filled.
  sorry

/-!
The next step is the in-place algorithm. It should move a value `x` to
index `x - 1` when `1 <= x <= n`.
-/

method firstMissingPositiveInPlace (mut arr : Array Int) return (ans : Nat)
  ensures IsFirstMissingPositive arrOld ans
  do
    -- TODO: replace this with the real in-place rearrangement.
    let ans : Nat ← firstMissingPositiveBaseline arr
    return ans

prove_correct firstMissingPositiveInPlace by
  loom_solve

end FirstMissingPositive
end Project
