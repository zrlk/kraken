/-
**hello's certificate's decided root facts** (AArch64; row: the RootPrem instance builder's loader facts): the facts
`HelloRootBase.toPrem` and its base read off the emitted output, closed at hello's certificate
(`Spike/Test/Cert/A64HelloCert.lean`) as wake's `WakeFinalCAO` closes them at wake's.

- `hstat_helloCert`: no static labels at the certificate's link tables (`toPrem`'s `hstat`;
  `HelloRootBase.hstat_tablesOf` at `placeCfg`, `outLit`).
- `ctrZ_helloCert`: the counter's zeroed item at the certificate (`Rt.CtrZ`, `HelloRootBase.har_W`'s premise).
- `pinZ_helloCert`: the pinned region's `.zero` has `131072` bytes (`StartPlaceLy.hpin2_W`'s `hz`).

The module imports hello's certificate and no wake module: both certificates declare `SccCertificate`, so a module
must not import both.
-/
import Spike.Test.Cert.A64HelloCert
import Spike.Lib.Rt.A64ArenaOfPlaceOK

namespace Spike.Lib.A64.HelloPh.CertFacts

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

/-- **No static labels at hello's certificate** (`HelloRootBase.toPrem`'s `hstat`, at the certificate's link
tables). -/
theorem hstat_helloCert :
    (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ.static = fun _ => none := rfl

/-- **The pinned region's `.zero` at hello's certificate** (`StartPlaceLy.hpin2_W`'s `hz`, wake's
`hpin2_outLit`'s): the `.zero` after `scc_rt_pinned` in the emitted `.bss`/`.data` has `131072` bytes, so a root
at this certificate has `hpin2` by `hpin2_W … pinZ_helloCert (by decide)`. -/
theorem pinZ_helloCert :
    Scc.Cert.PlaceOK.zeroAfter (SccCertificate.outLit.secs.bss ++ SccCertificate.outLit.secs.data)
      Scc.Cert.Link.pinnedSym = some 131072 := by decide

/-- **The counter's zeroed item at hello's certificate** (`Rt.CtrZ`, `HelloRootBase.har_W`'s premise):
`scc_rt_heap_use` labels an all-zero item of 8 bytes in the emitted `.bss`/`.data`. -/
theorem ctrZ_helloCert : Spike.Lib.A64.Rt.CtrZ SccCertificate.outLit := by
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

end Spike.Lib.A64.HelloPh.CertFacts

/-- info: 'Spike.Lib.A64.HelloPh.CertFacts.hstat_helloCert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CertFacts.hstat_helloCert

/-- info: 'Spike.Lib.A64.HelloPh.CertFacts.ctrZ_helloCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CertFacts.ctrZ_helloCert

/-- info: 'Spike.Lib.A64.HelloPh.CertFacts.pinZ_helloCert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CertFacts.pinZ_helloCert
