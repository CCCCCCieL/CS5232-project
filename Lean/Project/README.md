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

## Current Stage

This is stage 2 for me.

What is done now:

* the main spec is written;
* a few small examples check the spec;
* some helper names for the in-place algorithm are added.

The actual baseline loop is still not finished yet.

## Files

| File | Meaning |
| --- | --- |
| `Lean/Project.lean` | Project entry file. |
| `Lean/Project/FirstMissingPositive.lean` | Spec and current code skeleton. |
| `Lean/Project/README.md` | Project notes. |

## Build

From the `Lean` folder:

```bash
lake build Project
```

This version is mostly for the specification. The file still has a `sorry`
because the algorithm proof is not done yet.

## Plan

1. Write the formal specification. Done.
2. Add small examples for the spec. Done.
3. Implement the simple baseline algorithm. Next.
4. Prove the baseline algorithm.
5. Try the in-place algorithm if there is time.
