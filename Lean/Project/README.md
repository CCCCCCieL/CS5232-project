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

The tagged release link can be added after the final tag is made.

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

On the current machine it takes about 1 minute. Some warnings may come from libraries.

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

# Project/LeetCode.lean
DivM.res (3, #[1, 2, 0])
DivM.res (2, #[1, -1, 3, 4])
DivM.res (1, #[7, 8, 9, 11, 12])
DivM.res (2, #[1, 1])
DivM.res (3, #[1, 2])
DivM.res (3, #[1, 2, 0])
DivM.res (2, #[3, 4, -1, 1])
DivM.res (1, #[7, 8, 9, 11, 12])
```

The first three lines are from the baseline file. In the LeetCode file, the first five lines are from the LeetCode-style demo. It also prints the array after rearranging. The final three lines are from the verified in-place scan.

## Proof

The main spec is `IsFirstMissingPositive a ans`.

It says:

1. `ans` is positive;
2. `ans` is not in the array;
3. every smaller positive number is in the array.

The proved program is `firstMissingPositive_Baseline`. It checks candidate answers from 1 upward and scans the array each time.

The proof uses two nested loop invariants. The outer loop records that every positive number smaller than the current candidate has already been found. It also records that if the algorithm has stopped early, the stored answer already satisfies `IsFirstMissingPositive`. The inner loop records whether the current candidate has been seen in the scanned prefix.

The only extra mathematical lemma is `not_occurs_size_add_one_of_all_smaller`. It covers the case where all values `1, ..., a.size` occur in the array. The lemma proves that `a.size + 1` cannot also occur: otherwise those `a.size + 1` positive values would give an injection into only `a.size` array positions, which is impossible.

`firstMissingPositiveInPlace` is the verified in-place scan used for the minimum project goal. It works directly over the mutable input array, uses no auxiliary array, and keeps `arr = arrOld` as a frame invariant so that the final postcondition is about the original input. Its `decreasing` clauses give the termination arguments for the outer candidate loop and the inner array scan.

There is also `firstMissingPositive_LeetCodeDemo`. This one runs the improved rearranging idea and has examples, but it is kept as an executable demo rather than the main verified development.

## Limitation

The baseline algorithm and the in-place scan are fully proved. The LeetCode-style rearranging code is implemented and runs on the examples, but the direct proof of the rearranging loop is not included. Such a proof would need invariants showing that each swap preserves the multiset of positive values and that after the rearranging loop, every present value `x` in range is placed at index `x - 1`.

