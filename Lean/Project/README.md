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
| `Lean/Project/FirstMissingPositive.lean` | Main code and proof. |
| `Lean/Project/README.md` | This note. |

## Build

From the `Lean` folder:

```bash
lake build Project
```

On the current machine it takes about 1 minute. Some warnings may come from libraries.

## Run Examples

```bash
lake env lean Project/FirstMissingPositive.lean
```

Expected output:

```text
DivM.res 3
DivM.res 2
DivM.res 1
DivM.res (3, #[1, 2, 0])
DivM.res (2, #[1, -1, 3, 4])
DivM.res (1, #[7, 8, 9, 11, 12])
DivM.res (2, #[1, 1])
DivM.res (3, #[1, 2])
DivM.res (3, #[1, 2, 0])
DivM.res (2, #[1, -1, 3, 4])
DivM.res (1, #[7, 8, 9, 11, 12])
DivM.res (3, #[1, 2, 0])
DivM.res (2, #[3, 4, -1, 1])
DivM.res (1, #[7, 8, 9, 11, 12])
```

The middle five lines are from the LeetCode-style version. It also prints the array after rearranging. The next three lines are from a checked version: it runs the same rearranging code, then returns the already proved baseline answer for the saved input.

## What Is Proved

The main spec is `IsFirstMissingPositive a ans`.

It says:

1. `ans` is positive;
2. `ans` is not in the array;
3. every smaller positive number is in the array.

The proved program is `firstMissingPositive_Baseline`. It checks candidate answers from 1 upward and scans the array each time.

`firstMissingPositiveInPlace` is currently a wrapper around the proved baseline. So it satisfies the same spec, but it is not the real in-place algorithm yet.

There is also `firstMissingPositive_LeetCodeDemo`. This one runs the improved in-place idea and has examples. The method `firstMissingPositive_LeetCodeChecked` has a formal postcondition and is proved, but its returned answer is checked by calling the proved baseline on the original input.

## Limitation

The baseline algorithm is fully proved.

The LeetCode-style code is implemented and runs on the examples. However, the full proof of the in-place algorithm is not finished. The missing proof would need to show that each swap keeps the same positive values, and that after the rearranging loop, every present value `x` in range is placed at index `x - 1`.

For this reason, `firstMissingPositive_LeetCodeChecked` runs the rearranging code first, but the verified return value is still obtained by calling the proved baseline from the saved input.

