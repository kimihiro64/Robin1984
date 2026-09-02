# Provenance and attribution

Every Lean file in this repository has been reviewed from its retained
contents.  The review considered the file's module documentation, imports,
definitions and theorem statements, proof role, and exact dependency path to
the two advertised results.  Paths, filenames, and keyword searches were used
only to find material for inspection; they did not determine classifications.

The machine-readable record is [`provenance/ledger.json`](../provenance/ledger.json).
It contains one entry for each of the 157 Lean files and records the
content-level basis for its designation. `scripts/check-provenance.ps1`
requires exact agreement between the ledger and every project provenance
header; upstream-ready files below `Robin1984/Mathlib/` instead require the
standard Mathlib copyright, licence, authorship, and module-documentation
markers.

The four designations mean:

- **Direct source formalization**: the retained mathematical statement or
  argument reconstructs a named result of Robin, Nicolas, or Landau used in
  the source proof.  The Lean encoding and proof engineering remain the work
  of this formalization.
- **Other published source formalization**: the primary retained result comes
  from another named published source, including Alaoglu--Erdos, Costa
  Pereira, or the Hadamard factorization of the xi function.
- **Standard mathematical formalization**: the retained material is a
  conventional algebraic, analytic, order-theoretic, or finite-sum fact for
  which no single originating author is claimed.
- **Primarily project-original**: the retained code is a certificate format,
  exact generated data, a formalization-specific interface, a new proof
  decomposition, or connective proof engineering.  Any imported published
  theorem keeps its attribution at its own source.

Current reviewed counts are 37 direct-source files, 3 other-source files,
19 standard-mathematics files, and 98 primarily project-original files.
The last group includes all exact finite row and prime-product certificates:
their mathematical obligation comes from Robin's cutoff, but their data
format, interval partition, and kernel verification are original to this
formalization.
