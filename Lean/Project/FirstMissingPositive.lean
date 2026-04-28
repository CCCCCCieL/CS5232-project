import Auto

import Ssreflect.Lang

import LoVe.LoVelib

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

Given an integer array, return the first positive number which is missing.

-/

namespace Project
namespace FirstMissingPositive

-- `x` occurs in the array, after casting `x` to an integer.
@[grind]
def occursPositive (a : Array Int) (x : Nat) : Prop :=
  exists i, i < a.size /\ a[i]! = Int.ofNat x

@[grind]
def IsFirstMissingPositive (a : Array Int) (ans : Nat) : Prop :=
  0 < ans /\
  Not (occursPositive a ans) /\
  forall x, 0 < x -> x < ans -> occursPositive a x

@[grind]
def sameOccurrences (a b : Array Int) : Prop :=
  forall x, occursPositive a x <-> occursPositive b x

@[grind]
def correctlyPlacedUpTo (a : Array Int) (k : Nat) : Prop :=
  forall i, i < k -> i < a.size -> a[i]! = Int.ofNat (i + 1)

theorem not_occurs_size_add_one_of_all_smaller
    (a : Array Int)
    (hsmall : forall x, 0 < x -> x < a.size + 1 -> occursPositive a x) :
    Not (occursPositive a (a.size + 1)) := by
  -- Small pigeonhole fact used when the answer is `size + 1`.
  classical
  intro hlast
  let idxOf : (x : Nat) -> 0 < x -> x <= a.size + 1 -> Fin a.size :=
    fun x hxpos hxle =>
      if hxlast : x = a.size + 1 then
        let witness := Classical.choose hlast
        ⟨witness, (Classical.choose_spec hlast).left⟩
      else
        let hxlt : x < a.size + 1 := by omega
        let witness := Classical.choose (hsmall x hxpos hxlt)
        ⟨witness, (Classical.choose_spec (hsmall x hxpos hxlt)).left⟩
  let f : Fin (a.size + 1) -> Fin a.size :=
    fun k => idxOf (k.val + 1) (by omega) (by omega)
  have hf : Function.Injective f := by
    intro p q hpq
    have hpval : a[(f p).val]! = Int.ofNat (p.val + 1) := by
      dsimp [f, idxOf]
      split
      · rename_i hxlast
        change a[Classical.choose hlast]! = Int.ofNat (p.val + 1)
        have hcast : Int.ofNat (p.val + 1) = Int.ofNat (a.size + 1) :=
          congrArg Int.ofNat hxlast
        rw [hcast]
        exact (Classical.choose_spec hlast).right
      · exact (Classical.choose_spec (hsmall (p.val + 1) (by omega) (by omega))).right
    have hqval : a[(f q).val]! = Int.ofNat (q.val + 1) := by
      dsimp [f, idxOf]
      split
      · rename_i hxlast
        change a[Classical.choose hlast]! = Int.ofNat (q.val + 1)
        have hcast : Int.ofNat (q.val + 1) = Int.ofNat (a.size + 1) :=
          congrArg Int.ofNat hxlast
        rw [hcast]
        exact (Classical.choose_spec hlast).right
      · exact (Classical.choose_spec (hsmall (q.val + 1) (by omega) (by omega))).right
    have hvals : Int.ofNat (p.val + 1) = Int.ofNat (q.val + 1) := by
      calc
        Int.ofNat (p.val + 1) = a[(f p).val]! := hpval.symm
        _ = a[(f q).val]! := by rw [hpq]
        _ = Int.ofNat (q.val + 1) := hqval
    have : p.val = q.val := by
      norm_num at hvals
      omega
    exact Fin.ext this
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard

/-!
The baseline checks 1, then 2, then 3, etc.
Not smart but easy to understand, as a baseline
-/

method firstMissingPositiveBaseline (a : Array Int) return (ans : Nat)
  ensures IsFirstMissingPositive a ans
  do
    let n := a.size
    let mut current_x := 1
    let mut ans := n + 1
    let mut done := false

    while current_x <= n && !done
      invariant 1 <= current_x
      invariant current_x <= n + 1
      invariant ans = n + 1 ∨ IsFirstMissingPositive a ans
      invariant done = false -> ans = n + 1
      invariant done = true -> IsFirstMissingPositive a ans
      invariant done = false -> forall x, 0 < x -> x < current_x -> occursPositive a x
      decreasing n + 1 - current_x
    do
      let mut i := 0
      let mut seen := false

      while i < n
        invariant i <= n
        invariant seen = true -> occursPositive a current_x
        invariant seen = false -> forall j, j < i -> a[j]! != Int.ofNat current_x
        decreasing n - i
      do
        if a[i]! = Int.ofNat current_x then
          seen := true
        else
          seen := seen
        i := i + 1

      if seen then
        current_x := current_x + 1
      else
        ans := current_x
        done := true
        current_x := current_x + 1

    return ans

#eval (firstMissingPositiveBaseline #[1, 2, 0]).run
#eval (firstMissingPositiveBaseline #[3, 4, -1, 1]).run
#eval (firstMissingPositiveBaseline #[7, 8, 9, 11, 12]).run

prove_correct firstMissingPositiveBaseline by
  loom_solve
  grind [IsFirstMissingPositive, not_occurs_size_add_one_of_all_smaller]

@[grind]
def inRangeForArray (a : Array Int) (x : Int) : Prop :=
  1 <= x /\ x <= Int.ofNat a.size

@[grind]
def targetIndex (x : Int) : Nat :=
  Int.toNat x - 1

/-!
This is the LeetCode style solution idea.
It tries to put value `x` into index `x - 1`.

reference: https://leetcode.com/problems/first-missing-positive/solutions/4925226/first-missing-positive-by-leetcode-5ihk/
-/

method firstMissingPositiveLeetCodeDemo (mut arr : Array Int) return (ans : Nat)
  do
    let n := arr.size
    let mut i := 0

    while i < n
      invariant arr.size = n
      invariant i <= n
      decreasing n - i
    do
      let mut fuel := n

      while fuel > 0
        invariant arr.size = n
        invariant i < n
        invariant fuel <= n
        decreasing fuel
      do
        let x := arr[i]!
        if 1 <= x && x <= Int.ofNat n then
          let target := Int.toNat x - 1
          if arr[target]! != x then
            let oldTarget := arr[target]!
            arr := arr.set! target x
            arr := arr.set! i oldTarget
            fuel := fuel - 1
          else
            fuel := 0
        else
          fuel := 0

      i := i + 1

    let mut j := 0
    let mut ans := n + 1
    let mut found := false

    while j < n && !found
      invariant arr.size = n
      invariant j <= n
      decreasing n - j
    do
      if arr[j]! != Int.ofNat (j + 1) then
        ans := j + 1
        found := true
        j := j + 1
      else
        j := j + 1

    return ans

-- check correctness
#eval! (firstMissingPositiveLeetCodeDemo #[1, 2, 0]).run
#eval! (firstMissingPositiveLeetCodeDemo #[3, 4, -1, 1]).run
#eval! (firstMissingPositiveLeetCodeDemo #[7, 8, 9, 11, 12]).run
#eval! (firstMissingPositiveLeetCodeDemo #[1, 1]).run
#eval! (firstMissingPositiveLeetCodeDemo #[2, 1]).run

method firstMissingPositiveInPlace (mut arr : Array Int) return (ans : Nat)
  ensures IsFirstMissingPositive arrOld ans
  do
    let ans : Nat ← firstMissingPositiveBaseline arr
    return ans

#eval (firstMissingPositiveInPlace #[1, 2, 0]).run
#eval (firstMissingPositiveInPlace #[3, 4, -1, 1]).run
#eval (firstMissingPositiveInPlace #[7, 8, 9, 11, 12]).run

prove_correct firstMissingPositiveInPlace by
  loom_solve

end FirstMissingPositive
end Project
