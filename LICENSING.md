# Licensing scope

The single repository-level licence for the Robin1984 snapshot is the
[Apache License 2.0](LICENSE), as recorded by `project.license` in
`formalization.yaml`. Except where a file says otherwise, Apache-2.0 applies
to the copyrightable interests that the project contributors are authorized
to license in original repository material, including its Lean source,
certificate generators and project-authored arrangement or expression of
certificate data, scripts, configuration, and project documentation.

## Research paper

The original expression in
`paper/robin1984-formalization.tex` and the PDF built from it is available, at
the recipient's choice, under either:

- Apache License 2.0; or
- [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/)
  (`CC-BY-4.0`).

The paper carries this notice in both its source and rendered PDF. This
additional option does not replace or make ambiguous the repository's
Apache-2.0 default.

## Mathematics, sources, and dependencies

Licensing and scholarly provenance are separate:

- The mathematical statements, facts, methods, and results attributed to Guy
  Robin, Jean-Louis Nicolas, Edmund Landau, and the other cited authors are not
  claimed as original copyrightable content of this repository. Their sources
  and relationships to individual Lean modules are recorded in
  `formalization.yaml`, `docs/PROVENANCE.md`, and `provenance/ledger.json`.
- This repository does not distribute copies of the cited papers. Those papers
  retain their own copyrights and terms of access.
- Git dependencies named in `lake-manifest.json` and the Lean toolchain retain
  their own licences and copyright notices. The root Apache-2.0 licence does
  not relicense them.
- A file that incorporates third-party copyrightable material under a
  compatible licence remains subject to the third party's notice and licence
  as well as any licence that applies to project-authored modifications.

## Generated distributions

The Linux Lean-build release archive contains the repository's compiled build
outputs and a copy of this licensing information. It does not include the
checked-out dependency source trees under `.lake/packages`.

The API-documentation archive is an aggregate: doc-gen4 emits pages for
Robin1984 and its transitive imports so declaration links work offline. CI
therefore adds a `licensing/` directory containing this project notice, the
root Apache-2.0 text, the Lean toolchain notices, and the licence or notice
files from every pinned package represented in the documentation. Nothing in
that archive changes the terms that apply to third-party material.

## Contributions

Unless explicitly agreed and marked otherwise, contributions are accepted
under Apache-2.0 so they can be distributed as part of the repository
snapshot. Contributors must preserve applicable third-party notices and must
not submit material they are not authorized to license.
