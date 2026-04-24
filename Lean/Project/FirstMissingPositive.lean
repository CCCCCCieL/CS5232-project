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

-- I will need this later when I compare the changed array with the old array.
@[grind]
def sameOccurrences (a b : Array Int) : Prop :=
  forall x, occursPositive a x <-> occursPositive b x

-- A small helper for the normal in-place solution.
@[grind]
def inRangeForArray (a : Array Int) (x : Int) : Prop :=
  1 <= x /\ x <= Int.ofNat a.size

@[grind]
def targetIndex (x : Int) : Nat :=
  Int.toNat x - 1

example : occursPositive #[1, 2, 0] 1 := by
  exists 0

example : occursPositive #[1, 2, 0] 2 := by
  exists 1

example : Not (occursPositive #[7, 8, 9, 11, 12] 1) := by
  grind [occursPositive]

-- example : IsFirstMissingPositive #[1, 2, 0] 3 := by
--   grind [IsFirstMissingPositive, occursPositive]

-- example : IsFirstMissingPositive #[3, 4, -1, 1] 2 := by
--   grind [IsFirstMissingPositive, occursPositive]

-- example : IsFirstMissingPositive #[7, 8, 9, 11, 12] 1 := by
--   grind [IsFirstMissingPositive, occursPositive]

/-!
The first implementation plan is simple:
try 1, then 2, then 3, and scan the array each time.
-/

method firstMissingPositiveBaseline (a : Array Int) return (ans : Nat)
  ensures IsFirstMissingPositive a ans
  do
    -- TODO: replace this stub with the candidate-scanning loop.
    return 1

prove_correct firstMissingPositiveBaseline by
  -- TODO: prove the loop invariants after the implementation is filled.
  sorry


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
