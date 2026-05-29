// Seq prelude — loaded only when the program references sequence machinery
// (`Sequence.*` or any of the seq trigger names in
// `VerusLean/VLIR/Boole/Prelude.lean`).
//
// The `nat` type and its API live in `prelude/Nat.boole.st`, which is
// always loaded — `nat` shows up in many non-Seq programs too.
//
// This file is intentionally (almost) empty: the Seq helper functions that
// used to live here are now emitted as on-demand SupportDecls in
// `SupportEmit.lean` (`Set`, `Seq_new`, `Seq_lib_map`, `Seq_lib_map_values`,
// `Seq_lib_filter`, `Seq_lib_sort_by`, `Seq_lib_to_set`, `Set_finite`,
// `Seq_lib_zip_with`).  They are polymorphic / higher-order, and Strata's SMT
// encoder cannot monomorphize a declared-but-unused polymorphic function's
// type vars (`Unimplemented encoding for type var`).  Emitting them only when
// a call site actually references them — where the type vars monomorphize —
// avoids that.  `Seq_len` / `Seq_lib_insert` / `Seq_subrange` were dropped
// outright: the translator lowers Verus `Seq::len` / `::subrange` to Strata's
// built-in `Sequence.length` / `Sequence.subrange` directly, so nothing ever
// referenced them.
