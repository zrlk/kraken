/-
**wake.w's obligations at the certificate's output, one parse premise**
(AArch64): `WakeSpawnR.wake_obligations_RE` and
`wake_obligations_RS` at `o := SccCertificate.outLit`, their three parse
premises (`hpa`, `hwp`, `hd`) from the single loader check
`parsesTo SccCertificate.asm outLit.prog outLit.secs` (the certificate's
trust boundary, `#guard`ed there on `out`), with `outLit.prog = wakeProg`
by `kernel_rfl` (both are the loader's parse of the same listing, elaborated
to the same literal).

- `outLit_prog`: `outLit.prog = wakeProg`.
- `parsed_outLit`: `hpa`, `hwp`, `hd` from `parsesTo`.
- `wake_obligations_REP`, `wake_obligations_RSP`: the two at `outLit`.
-/
import Spike.Lib.WakeSpawnR

namespace Spike.Lib.WakeSpawnRP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeT1 Spike.Lib.WakeSpawnR
open Spike.Lib.WakePreTi (Pre1T TiPre)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)
open SccCertificate (outLit)

/-- **The certificate's program is `wakeProg`**: both are the loader's parse
of `SccCertificate.asm`, elaborated to the same literal. -/
theorem outLit_prog : outLit.prog = wakeProg := by kernel_rfl

/-- **The three parse equations from the single loader check.** -/
theorem parsed_outLit (h : Scc.Cert.Link.A64.parsesTo SccCertificate.asm outLit.prog outLit.secs = true) :
    textProgram SccCertificate.asm = .ok outLit.prog ∧ textProgram SccCertificate.asm = .ok wakeProg ∧
      dataSections SccCertificate.asm = some outLit.secs :=
  let hp := Scc.Cert.Link.A64.parsed_of_parsesTo h
  ⟨hp.1, outLit_prog ▸ hp.1, hp.2⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout} (hp : PlaceW pcfg Λ0 outLit)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
  (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm outLit.prog outLit.secs = true)

/-- **`wake_obligations_RE` at the certificate's output** (see the module
doc), its `hpa` the first of `parsed_outLit hP`. -/
theorem wake_obligations_REP {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hE : E.clear (RuntimeLayout.ofPlaceW hp i).Λ = true)
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E R1 Ab Ac)
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.armv8 ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ)
        tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧ (WakeAssemblyR.QR hp i (parsed_outLit hP).1 arch R1 r0 r1).Post
        (RuntimeLayout.ofPlaceW hp i).Λ (afterClone abi d tid th stack tls r) s') :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm
      (WakeAssemblyR.QR hp i (parsed_outLit hP).1 arch R1 r0 r1) E (TiPre Ab Ac) :=
  wake_obligations_RE hp i (parsed_outLit hP).1 (parsed_outLit hP).2.1 (parsed_outLit hP).2.2 hE O spawn

/-- **`wake_obligations_RS` at the certificate's output** (see the module
doc): open the instance facts (decided at the linked layout), `hpre`
and `hMainR`. -/
theorem wake_obligations_RSP {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hE : E.clear (RuntimeLayout.ofPlaceW hp i).Λ = true)
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E R1 Ab Ac)
    /- instance facts -/
    (hlo : (RuntimeLayout.ofPlaceW hp i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    /- OPEN -/
    (hpre : HPre hp i SccCertificate.asm E arch R1 (WakeAssemblyR.μR hp i)
      (WakeAssemblyR.MR hp i (parsed_outLit hP).1) r0 r1)
    (hMainR : HMainR hp i SccCertificate.asm E arch R1 (WakeAssemblyR.μR hp i)
      (WakeAssemblyR.MR hp i (parsed_outLit hP).1) r0 r1) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm
      (WakeAssemblyR.QR hp i (parsed_outLit hP).1 arch R1 r0 r1) E (TiPre Ab Ac) :=
  wake_obligations_RS hp i (parsed_outLit hP).1 (parsed_outLit hP).2.1 (parsed_outLit hP).2.2 hE O hlo hpin2
    hinit2 hwide hpre hMainR

end Inst

end Spike.Lib.WakeSpawnRP

/-- info: 'Spike.Lib.WakeSpawnRP.outLit_prog' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.WakeSpawnRP.outLit_prog

/-- info: 'Spike.Lib.WakeSpawnRP.wake_obligations_REP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSpawnRP.wake_obligations_REP

/-- info: 'Spike.Lib.WakeSpawnRP.wake_obligations_RSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSpawnRP.wake_obligations_RSP
