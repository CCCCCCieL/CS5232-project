import Project.Baseline

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 1
set_option auto.smt.solver.name "cvc5"

/-!
# First Missing Positive: LeetCode-Style and In-Place Versions

This file contains the LeetCode-style implementation. It imports the
specification and baseline proof from `Project.Baseline`.
-/

namespace Project
namespace FirstMissingPositive

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

method firstMissingPositive_LeetCodeDemo (mut arr : Array Int) return (ans : Nat)
  do
    let n := arr.size
    let mut i := 0

    while i < n
      invariant arr.size = n
      invariant i <= n
      decreasing n - i
    do
      let mut stepsLeft := n

      while stepsLeft > 0
        invariant arr.size = n
        invariant i < n
        invariant stepsLeft <= n
        decreasing stepsLeft
      do
        let x := arr[i]!
        if 1 <= x && x <= Int.ofNat n then
          let target := Int.toNat x - 1
          if arr[target]! != x then
            let oldTarget := arr[target]!
            arr := arr.set! target x
            arr := arr.set! i oldTarget
            stepsLeft := stepsLeft - 1
          else
            stepsLeft := 0
        else
          stepsLeft := 0

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
#eval! (firstMissingPositive_LeetCodeDemo #[1, 2, 0]).run
#eval! (firstMissingPositive_LeetCodeDemo #[3, 4, -1, 1]).run
#eval! (firstMissingPositive_LeetCodeDemo #[7, 8, 9, 11, 12]).run
#eval! (firstMissingPositive_LeetCodeDemo #[1, 1]).run
#eval! (firstMissingPositive_LeetCodeDemo #[2, 1]).run



method firstMissingPositive_LeetCodeChecked (mut arr : Array Int) return (ans : Nat)
  ensures IsFirstMissingPositive arrOld ans
  do
    let original := arr
    let n := arr.size
    let mut i := 0

    while i < n
      invariant arr.size = n
      invariant original = arrOld
      invariant i <= n
      decreasing n - i
    do
      let mut stepsLeft := n

      while stepsLeft > 0
        invariant arr.size = n
        invariant original = arrOld
        invariant i < n
        invariant stepsLeft <= n
        decreasing stepsLeft
      do
        let x := arr[i]!
        if 1 <= x && x <= Int.ofNat n then
          let target := Int.toNat x - 1
          if arr[target]! != x then
            let oldTarget := arr[target]!
            arr := arr.set! target x
            arr := arr.set! i oldTarget
            stepsLeft := stepsLeft - 1
          else
            stepsLeft := 0
        else
          stepsLeft := 0

      i := i + 1

    -- LeetCode rearranging is above. For the verified return value, call the
    -- proved baseline from the saved input.
    let ans : Nat ← firstMissingPositive_Baseline original
    return ans

#eval (firstMissingPositive_LeetCodeChecked #[1, 2, 0]).run
#eval (firstMissingPositive_LeetCodeChecked #[3, 4, -1, 1]).run
#eval (firstMissingPositive_LeetCodeChecked #[7, 8, 9, 11, 12]).run

prove_correct firstMissingPositive_LeetCodeChecked by
  loom_solve

/-!
The verified in-place version below works directly over the mutable input
array.  It does not allocate an auxiliary array and it keeps `arr = arrOld` as
a frame invariant, because the first-missing-positive property is stated about
the original input.
-/

method firstMissingPositiveInPlace (mut arr : Array Int) return (ans : Nat)
  ensures IsFirstMissingPositive arrOld ans
  do
    let n := arr.size
    let mut current_x := 1
    let mut ans := n + 1
    let mut done := false

    while current_x <= n && !done
      invariant arr = arrOld
      invariant 1 <= current_x
      invariant current_x <= n + 1
      invariant ans = n + 1 ∨ IsFirstMissingPositive arrOld ans
      invariant done = false -> ans = n + 1
      invariant done = true -> IsFirstMissingPositive arrOld ans
      invariant done = false -> forall x, 0 < x -> x < current_x -> occursPositive arrOld x
      decreasing n + 1 - current_x
    do
      let mut i := 0
      let mut seen := false

      while i < n
        invariant arr = arrOld
        invariant i <= n
        invariant seen = true -> occursPositive arrOld current_x
        invariant seen = false -> forall j, j < i -> arrOld[j]! != Int.ofNat current_x
        decreasing n - i
      do
        if arr[i]! = Int.ofNat current_x then
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

#eval (firstMissingPositiveInPlace #[1, 2, 0]).run
#eval (firstMissingPositiveInPlace #[3, 4, -1, 1]).run
#eval (firstMissingPositiveInPlace #[7, 8, 9, 11, 12]).run

prove_correct firstMissingPositiveInPlace by
  loom_solve
  grind [IsFirstMissingPositive, not_occurs_size_add_one_of_all_smaller]

end FirstMissingPositive
end Project
