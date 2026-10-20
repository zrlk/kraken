import WeakCore.TermFreeQW
import WeakCore.TermA4P

/-! # TermFreeQWP: `freeQW` at the `FreeP` pieces (pre-wire of hWbR under A1)

COPIES (scratch; to be folded into `TermFreeQW` once route (B) lands): `valOfR_zero_fill` and
`freeQW_exists` with the piece condition `tb 0 U ∧ ¬ affine U` generalised to `TermA4.FreeP U` (the
key-free branch via `TermA4.VR_VRR_rc_closed`).

(R4 dedup) `valOfR_zero_fillP` and `freeQW_existsP` now live in `TermFreeQW`; this module
only re-exports them.
-/
