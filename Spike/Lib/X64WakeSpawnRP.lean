/-
**x86-64 wake's obligations at the certificate's output** (X64-trust-params;
the twin of `Spike/Lib/WakeSpawnRP.lean`): `X64WakeSpawnR.wake_obligations_RE`
and `wake_obligations_RS` at `o := outLit` and `asm := X64WakeParse.certAsm`.
Their four trust-boundary parses (`hpa`, `hwp`, `hd`, `hoffs`) come from the
single loader check `hP : parsesTo certAsm outLit.prog outLit.secs` via
`X64WakeParse.parsed_outLit`. After this, `hP` is the only trust premise; the
budget's `hB` stays with the final theorem.

- `wake_obligations_REP`: `wake_obligations_RE` at `outLit`, its `hpa`
  the first of `parsed_outLit hP`.
- `wake_obligations_RSP`: `wake_obligations_RS` at `outLit`; still open:
  the instance facts, `hpre`, `hMainR`.

**Where this differs from AArch64**: the certificate is `certAsm` (the
text with GNU `as`'s sizes and label offsets), and there is a fourth parse,
`hoffs`. `X64WakeParse.outLit_offs` closes it. `RS` has the instance fact
`hA13` in addition to AArch64's.
-/
import Spike.Lib.X64WakeSpawnR
import Spike.Lib.X64WakeParse

namespace Spike.Lib.X64WakeSpawnRP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeSpawnR
open Spike.Lib.X64WakePreTi (Pre1T TiPre)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeParse (certAsm parsed_outLit)
open SccCertificate (outLit)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout} (hp : PlaceWX pcfg Λ0 outLit)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
  (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`wake_obligations_RE` at the certificate's output**: its four parses
from `parsed_outLit hP`. -/
theorem wake_obligations_REP {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hE : E.clear (Ly).Λ = true)
    (O : Pre1T arch (Ly).Λ B certAsm E R1 Ab Ac)
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks certAsm (Ly).Λ)
        tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧ (X64WakeAssemblyR.QR hp i certAsm (parsed_outLit hP).1 arch R1 r0 r1).Post
        (Ly).Λ (afterClone abi d tid th stack tls r) s') :
    WakeObligations arch (Ly).Λ B certAsm (X64WakeAssemblyR.QR hp i certAsm (parsed_outLit hP).1 arch R1 r0 r1)
      E (TiPre Ab Ac) :=
  wake_obligations_RE hp i (parsed_outLit hP).1 (parsed_outLit hP).2.1 (parsed_outLit hP).2.2.1
    (parsed_outLit hP).2.2.2 hE O spawn

/-- **`wake_obligations_RS` at the certificate's output**: still open are
the instance facts (decided at the linked layout), `hpre` and `hMainR`. -/
theorem wake_obligations_RSP {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hE : E.clear (Ly).Λ = true)
    (O : Pre1T arch (Ly).Λ B certAsm E R1 Ab Ac)
    /- instance facts -/
    (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideX64.ExeWide (Ly).exe)
    /- OPEN -/
    (hpre : HPre hp i certAsm E arch R1 (X64WakeAssemblyR.μR hp i certAsm)
      (X64WakeAssemblyR.MR hp i certAsm (parsed_outLit hP).1) r0 r1)
    (hMainR : HMainR hp i certAsm E arch R1 (X64WakeAssemblyR.μR hp i certAsm)
      (X64WakeAssemblyR.MR hp i certAsm (parsed_outLit hP).1) r0 r1) :
    WakeObligations arch (Ly).Λ B certAsm (X64WakeAssemblyR.QR hp i certAsm (parsed_outLit hP).1 arch R1 r0 r1)
      E (TiPre Ab Ac) :=
  wake_obligations_RS hp i (parsed_outLit hP).1 (parsed_outLit hP).2.1 (parsed_outLit hP).2.2.1
    (parsed_outLit hP).2.2.2 hE O hlo hA13 hpin2 hinit2 hwide hpre hMainR

end Inst

end Spike.Lib.X64WakeSpawnRP

/-- info: 'Spike.Lib.X64WakeSpawnRP.wake_obligations_REP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeSpawnRP.wake_obligations_REP

/-- info: 'Spike.Lib.X64WakeSpawnRP.wake_obligations_RSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeSpawnRP.wake_obligations_RSP
