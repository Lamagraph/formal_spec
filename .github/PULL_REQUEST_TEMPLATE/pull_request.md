---
name: Pull request
about: Merging a feature branch to dev, or dev to main (release).
title: ""
labels: []
---

**Task / issue**

<!-- The task issue this PR completes, e.g. #12. For a release PR (dev -> main),
     list the tasks included. -->

**What changed**

<!-- Summary of the change. Reference the subtask commits (S1, S2, ...). -->

**Verification**

<!-- Confirm the quality gate passed: `make`, `make validate`, `make html`. -->

- [ ] `make` green (zero `Admitted`/`Admit`/`Abort`)
- [ ] `make validate` (coqchk) clean
- [ ] `make html` (coqdoc) clean
- [ ] Code review complete, zero findings

**Design notes**

<!-- Link to `tasks/detailed_plan.md` Design Notes if any subtask was blocked or
     a design decision was made. -->
