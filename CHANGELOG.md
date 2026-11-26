# Changelog

All notable changes to the specification are documented here. The format is
loosely based on [Keep a Changelog](https://keepachangelog.com/); versions
follow the scheme in the `release` skill.

## [Unreleased]

### Added
- Initial repository setup: Coq (coq_makefile) build, `src/Basics.v` starter,
  `docs/` (design + developer guides), the `AGENTS.md` entrypoint, and the
  `.opencode/skills/` workflow.
- Documentation website at https://lamagraph.github.io/formal_spec/: the
  rocqdoc output extracted from the `.v` sources plus one start page,
  deployed from `main` at each release
  (`.github/workflows/deploy-docs.yml`).

### Changed
- Build system migrated from coq_makefile to **dune + opam** (`dune-project`,
  `src/dune`, `lamagraph-formal-spec.opam`); the prover moved from Coq 8.20.1
  to **Rocq 9.3** (the official successor after the Coq→Rocq rename — dune
  3.24+ removed the old Coq build language). Sources now use `From Stdlib`.
- CI runs the gate (build + `rocqchk` + docs) inside the prebuilt
  `rocq/rocq-prover:9.3` image via docker-coq-action, instead of compiling
  the prover from source.
