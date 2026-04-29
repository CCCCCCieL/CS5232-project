# First Missing Positive

This CS5232 project uses Lean/Velvet to verify the First Missing
Positive problem.

The task: given an integer array, return the smallest positive number which is missing.

Original problem: https://leetcode.com/problems/first-missing-positive/description/

Examples:

| Input | Answer |
| --- | --- |
| `[1, 2, 0]` | `3` |
| `[3, 4, -1, 1]` | `2` |
| `[7, 8, 9, 11, 12]` | `1` |

## Repo

```text
https://github.com/CCCCCCieL/cs5232-2026/tree/project/Lean/Project
```


## Files

| File | Meaning |
| --- | --- |
| `Lean/Project.lean` | Project entry file. |
| `Lean/Project/Baseline.lean` | Specification, baseline implementation, and baseline proof. |
| `Lean/Project/LeetCode.lean` | LeetCode-style demo and verified in-place scan. |
| `Lean/Project/README.md` | This note. |

## Build

From the `Lean` folder:

```bash
lake build Project
```

On my personal laptop, it takes about 1 minute. Some warnings may come from libraries.

## Run Examples

```bash
lake env lean Project/Baseline.lean
lake env lean Project/LeetCode.lean
```

Expected output:

```text
# Project/Baseline.lean
DivM.res 3
DivM.res 2
DivM.res 1
```
```
# Project/LeetCode.lean
DivM.res (3, #[1, 2, 0])
DivM.res (2, #[1, -1, 3, 4])
DivM.res (1, #[7, 8, 9, 11, 12])
DivM.res (2, #[1, 1])
DivM.res (3, #[1, 2])
DivM.res (3, #[1, 2, 0])
DivM.res (2, #[3, 4, -1, 1])
DivM.res (1, #[7, 8, 9, 11, 12])

The first five lines are from the LeetCode-style demo. It also prints the array after rearranging. 
The final three lines are from the verified in-place scan.
```

## Proof

The main specification is `IsFirstMissingPositive a ans`.

It means three things:

1. `ans` is positive;
2. `ans` does not appear in the array;
3. every smaller positive number appears in the array.

The main proved program is `firstMissingPositive_Baseline`. It checks possible answers from `1` upwards. For each possible answer, it scans the whole array to see whether this number appears.

The proof uses two nested loop invariants. The outer loop remembers that every positive number smaller than the current candidate has already been found. It also remembers that if the algorithm has already stopped, then the stored answer is already a correct first missing positive. The inner loop records whether the current candidate has appeared in the part of the array that has already been
scanned.

The only extra mathematical lemma is `not_occurs_size_add_one_of_all_smaller`. It is used for the final case. If all values `1, ..., a.size` appear in the array, then the answer should be `a.size + 1`. The lemma says that `a.size + 1` cannot also appear in the array, because an array of size `a.size` cannot contain `a.size + 1` different positive
values.

`firstMissingPositiveInPlace` is another proved method. It is written over a mutable input array and does not use another array. In this method, I keep `arr = arrOld` as a frame invariant, so the final result is still proved for the original input. The `decreasing` clauses are used to show that the outer
candidate loop and the inner scan loop both terminate.

There is also `firstMissingPositive_LeetCodeDemo`. This method runs the faster LeetCode-style rearranging idea and has examples. However, it is kept as an executable demo, not as the main fully verified method. The file proves some basic support lemmas for this idea. For example, `leetcodeSwap_preserves_multiset` shows that a swap keeps the same multiset of array elements, `leetcodeSwap_places_current_value` shows that a valid swap
puts the current value into its target position, and `swap_fuel_decreases` explains the step counter used to avoid an infinite swap loop.

The method `leetcodeSwapStep` puts the single-swap proof into a small Velvet method. If `arr[i]` is positive and in range, it proves that the swap keeps the array size and places `arr[i]` at index `arr[i] - 1`.

## Limitation

The baseline algorithm and the in-place scan are fully proved. The LeetCode-style rearranging code is also implemented and runs on the examples. Some basic facts about one swap are proved, such as size preservation and target placement.

However, the full proof of the whole rearranging loop is not included. To prove it, we would need stronger loop invariants. These invariants should connect all the swaps together and show that the final array has the expected placement property. This is the main future work of the project.

