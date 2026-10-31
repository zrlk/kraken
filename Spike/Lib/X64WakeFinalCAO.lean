/-
**wake's x86-64 certificate's decided instance facts**: the facts of wake's
x86-64 output that do not depend on the layout, and a sanity check of the
layout-specific ones at the certificate's canonical link layout.

- `ctrZ_cert`: the counter's zeroed item at the certificate (`Rt.CtrZ`,
  `X64WakeRootO.wake_finalX_LUO`'s `hc`).
- `placeWX_cert`: `PlaceWX` at the certificate's link layout `tablesOf`
  (`prog_placeOK_1` to `prog_placeOK_9`).
- `hnt_cert`: `scc_rt_nthreads` starts at `0` there (`X64WakeOInit.NtZ`).
- `hstat_cert`: no static labels there.

Unlike AArch64 (`Spike/Lib/WakeFinalCAO.lean`), this module does not restate
the final theorem: the x86-64 statement is `X64WakeRootO.wake_finalX_LUO`.
`PlaceWX` carries all of A1–A9 (AArch64's `PlaceW` only A1, A2, A4, A6, A8),
so `placeWX_cert` takes all nine components. The binding instance is at
`Λe`, the layout of the linked executable (`Spike/Test/WakeLinkedX64Le.lean`,
`.text` at `0x401000`); `tablesOf placeCfg outLit` (code base `0x400000`) is
a sanity check only.
-/
import Spike.Test.Cert.X64WakeCert
import Spike.Lib.X64PlaceW
import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Spike.Lib.X64WakeOInit

namespace Spike.Lib.X64WakeFinalCAO

/-- **`PlaceWX` at wake's certificate**: A1–A9 at its link layout. -/
theorem placeWX_cert :
    PlaceWX SccCertificate.placeCfg
      (Scc.Cert.PlaceOK.X64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ SccCertificate.outLit :=
  ⟨SccCertificate.prog_placeOK_1, SccCertificate.prog_placeOK_2, SccCertificate.prog_placeOK_3,
    SccCertificate.prog_placeOK_4, SccCertificate.prog_placeOK_5, SccCertificate.prog_placeOK_6,
    SccCertificate.prog_placeOK_7, SccCertificate.prog_placeOK_8, SccCertificate.prog_placeOK_9⟩

/-- A key's lookup is one of the list's pairs. -/
private theorem lookup_mem {β : Type} : ∀ {l : List (String × β)} {k : String} {b : β},
    l.lookup k = some b → (k, b) ∈ l
  | [], _, _, h => by simp at h
  | (k', b') :: l, k, b, h => by
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have hne : (k == k') = false := by simpa using hk
      simp [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **The counter's zeroed item at wake's certificate** (`Rt.CtrZ`,
`wake_finalX_LUO`'s `hc`): `scc_rt_heap_use` labels an all-zero item of 8
bytes in the emitted `.bss`/`.data`. -/
theorem ctrZ_cert : Spike.Lib.X64.Rt.CtrZ SccCertificate.outLit := by
  cases h : (Scc.Cert.Link.symItems (SccCertificate.outLit.secs.bss ++ SccCertificate.outLit.secs.data)).lookup
    Scc.Cert.PlaceOK.heapUseSym with
  | none => exact absurd h (by decide)
  | some its =>
    refine ⟨its, lookup_mem h, ?_, ?_⟩
    · have : ((Scc.Cert.Link.symItems (SccCertificate.outLit.secs.bss ++ SccCertificate.outLit.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map Scc.Cert.Link.allZero = some true := by decide
      rw [h] at this; simpa using this
    · have : ((Scc.Cert.Link.symItems (SccCertificate.outLit.secs.bss ++ SccCertificate.outLit.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map (fun its => decide (8 ≤ Scc.Cert.Link.itemLen its)) = some true := by
        decide
      rw [h] at this; simpa using this

/-- **`scc_rt_nthreads` starts at `0` at wake's certificate's link layout**
(`X64WakeOInit.NtZ`). -/
theorem hnt_cert :
    Spike.Lib.X64WakeOInit.NtZ (Scc.Cert.PlaceOK.X64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ
      SccCertificate.outLit = true := by
  decide +kernel

/-- **No static labels at wake's certificate's link layout.** -/
theorem hstat_cert :
    (Scc.Cert.PlaceOK.X64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ.static = fun _ => none :=
  rfl

end Spike.Lib.X64WakeFinalCAO

/-- info: 'Spike.Lib.X64WakeFinalCAO.placeWX_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinalCAO.placeWX_cert

/-- info: 'Spike.Lib.X64WakeFinalCAO.ctrZ_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinalCAO.ctrZ_cert

/-- info: 'Spike.Lib.X64WakeFinalCAO.hnt_cert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinalCAO.hnt_cert

/-- info: 'Spike.Lib.X64WakeFinalCAO.hstat_cert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinalCAO.hstat_cert
