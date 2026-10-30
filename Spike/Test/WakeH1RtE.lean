import Spike.Test.WakeLinkedA64Ctr
import Spike.Lib.A64WakeH1Rt

/-!
# `H1G`'s `resA`/`tcbA`/`hdrA`/`tid` dischargers at `Le` (non-vacuity)

`A64WakeH1Rt`'s field lemmas instantiated at `placeW_e`, `ie`, `hlo`, `hstat`,
`hA13_e`, `hpa`/`hwp` from the loader check `hP` (`parsed_outLit`), `hland`
at the first heap word (`b := arW.heap + 8`, `n := 1`), `F := fun _ => False`
(the hun* obligations vacuous); `tcbA_W`'s `BandSp3` is a parameter (from `BoxPure`
by `WakeWcW1I.bands_of_box` in `wake_linkedU`).
-/

namespace Spike.Test.WakeLinkedA64

open Spike.Lib.A64.WakePh.H1Rt
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- The new label's landing at the heap's first word. -/
theorem hland_e : Spike.Lib.HeapLand.AllocLand (Spike.Lib.WakeOD.arW placeW_e ie).heap
    (Spike.Lib.WakeOD.arW placeW_e ie).cells ((Spike.Lib.WakeOD.arW placeW_e ie).heap + 8) 1 := by
  show _ + 8 ≤ _ ∧ _ ∧ _
  refine ⟨Nat.le_refl _, ?_, show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide⟩
  show _ + 8 + 8 * 1 ≤ _ + 16 * Scc.Cert.PlaceOK.allocCells
  have : 1 ≤ Scc.Cert.PlaceOK.allocCells := by decide
  omega

variable (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
  SccCertificate.outLit.secs = true)

example (E : Scc.Sem.Entry) (cT) (ls0) (R : Spike.Lib.Region) :=
  resA_W placeW_e ie E cT ls0 (l := default) (Spike.Lib.WakeSpawnRP.parsed_outLit hP).1
    (Spike.Lib.WakeSpawnRP.parsed_outLit hP).2.1 hlo hstat hA13_e hland_e (F := fun _ => False) (R := R)
    (fun _ h => h.elim)
example (E : Scc.Sem.Entry) (cT) (ls0) {R : Spike.Lib.Region} (hb : Spike.Lib.A64.WakePh.Tcb2CallW.BandSp3 Le R) :=
  tcbA_W placeW_e ie E cT ls0 (l := default) (Spike.Lib.WakeSpawnRP.parsed_outLit hP).1
    (Spike.Lib.WakeSpawnRP.parsed_outLit hP).2.1 hlo hstat hA13_e hland_e (F := fun _ => False) hb
    (fun _ h => h.elim)
example (E : Scc.Sem.Entry) (cT) (ls0) :=
  hdrA_W placeW_e ie E cT ls0 (l := default) hstat hA13_e hland_e (F := fun _ => False) (fun _ h => h.elim)
example (E : Scc.Sem.Entry) (cT) (ls0) :=
  tid_W placeW_e ie E cT ls0 (l := default) hstat hA13_e hland_e (F := fun _ => False) (fun _ h => h.elim)

end Spike.Test.WakeLinkedA64
