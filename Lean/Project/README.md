# First Missing Positive

This is my CS5232 project.

The problem:

Given an integer array, return the smallest positive integer that is missing.

Examples:

| Input | Answer |
| --- | --- |
| `[1, 2, 0]` | `3` |
| `[3, 4, -1, 1]` | `2` |
| `[7, 8, 9, 11, 12]` | `1` |

## Files

| File | Meaning |
| --- | --- |
| `Lean/Project.lean` | Project entry file. |
| `Lean/Project/FirstMissingPositive.lean` | Main code skeleton. |
| `Lean/Project/README.md` | Project notes. |

## Build

From the `Lean` folder:

```bash
lake build Project
```

This first version is only the project framework. The baseline loop and the
main proof will be filled in later.

## Plan

1. Write the formal specification.
2. Implement the simple baseline algorithm.
3. Prove the baseline algorithm.
4. Try the in-place algorithm if there is time.
