import Spike.Test.WakeLinkedX64
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeImms

/-!
# `wake.w` on x86-64: the placed runtime layout `Le` at `Λe` and its facts

The x86-64 twin of the layout facts of `Spike/Test/WakeLinkedA64.lean` and
`WakeLinkedA64Ctr.lean`. Decided at `Λe`, each by `decide +kernel` or from a library
fact:

* `placeWX_e : PlaceWX placeCfg Λe outLit` (`PlaceWX.of2 wake_placeOK2At`);
* `ie := X64.WakeImms.iW Λe`, `Le := ofPlaceWX placeWX_e ie`;
* `hstat`, `hnz` (`scc_rt_nthreads` decided, no initial word), `hpin2`
  (the first 200 bytes in the pinned region), `hinit2` (the second
  TCB's limit word `pinA + 144` starts at `0`), `hsub1` (the child's stack in
  the pool), `hwide` (the executable in the wide fragment);
* `hctrD_e`, `hctr2_e`, `hA13_e` (the counters in `.data`, off `lim2A`; A13's
  data part).

`.text` is at `0x401000` (`WakeLinkedX64Elf`), not at AArch64's
`WakePh.lo`; `hlo` is `Λe.code.lo = 0x401000` here, the x86-64
`X64.WakePh.lo` is that base, and the x86-64 phase constants are taken at it.
The x86-64 `NtZ`, `lim2A` and `r1Of` are stated inline (their AArch64
modules `WakeOInit`, `WakeGOf2`, `Rt/A64RtPreChild` import AArch64's
consumer); they are those definitions token for token at `Scc.Cert.Rt.X64`.
-/

namespace Spike.Test.WakeLinkedX64

open Spike.Lib
open Spike.Lib.X64.Rt (RuntimeLayout)
open SccCertificate (outLit placeCfg)

/-- **`PlaceWX` at the executable's layout** (A1–A9 of `placeOK2At`). -/
theorem placeWX_e : PlaceWX placeCfg Λe outLit := PlaceWX.of2 wake_placeOK2At

/-- The root's immediate table at `Λe`. -/
noncomputable abbrev ie : CoreTerm.Expr → String → Nat → Option Nat := Spike.Lib.X64.WakeImms.iW Λe

/-- The placed runtime layout at `Λe`. -/
noncomputable abbrev Le : RuntimeLayout := RuntimeLayout.ofPlaceWX placeWX_e ie

/-- `.text` at `0x401000`. -/
theorem hlo : Λe.code.lo = 0x401000 := by decide +kernel

/-- No static words. -/
theorem hstat : Λe.static = fun _ => none := rfl

/-- **`scc_rt_nthreads` is decided and starts at `0`** (no initial word; the
x86-64 `WakeOInit.NtZ`). -/
def NtZ (Λ : Scc.Sem.Layout) (o : Scc.Cert.PlaceOK.X64.Out) : Bool :=
  (Scc.Cert.Rt.X64.symLab Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata) "scc_rt_nthreads").isSome &&
    ((Scc.Cert.Rt.X64.initOf Λ o.prog o.secs).find?
      (·.1 == ⟨Scc.Cert.Rt.X64.rtA Λ o.prog o.secs "scc_rt_nthreads", 8⟩)).isNone

/-- `scc_rt_nthreads` starts at `0`. -/
theorem hnz : NtZ Λe outLit = true := by decide +kernel

/-- The first 200 bytes fit the pinned region. -/
theorem hpin2 : Le.pinA.toNat + 200 ≤ Le.Λ.pinned.lo + Le.Λ.pinned.size := by decide +kernel

/-- **The second TCB's limit word** (`WakeGOf2.lim2A`): `pinA + 144`. -/
abbrev lim2A (L : RuntimeLayout) : BitVec 64 := L.pinA + 144#64

/-- The second TCB's limit word starts at `0`. -/
theorem hinit2 : (Spike.Lib.X64.PhRec.m0Of Le.Λ outLit.prog outLit.secs).initVal ⟨lim2A Le, 8⟩ = 0 := by
  decide +kernel

/-- **The child's take's range**: the second stack (`Rt.PreChild.r1Of`). -/
def r1Of (lab : Label → Int64) : Scc.Sem.Range :=
  ⟨(Spike.Lib.X64.Flow.Ret0.stacksA lab + 16384#64).toNat, 16384⟩

/-- The child's stack range lies in the stack pool. -/
theorem hsub1 : (r1Of Le.lab).Sub Le.Λ.stackPool := by
  -- the kernel does not reduce the executable's label lookup: through `lab_stacks`
  have h := Le.lab_stacks
  unfold Scc.Sem.Range.Sub r1Of RuntimeLayout.lab
  rw [h]
  decide +kernel

/-- The executable is in the wide fragment (A4, `wideSt_threadAt`). -/
theorem hwide : Scc.Cert.WideX64.ExeWide Le.exe :=
  (Scc.Cert.WideX64.wideSt_threadAt (PlaceWX.wideIn_of_placeWX placeWX_e) Scc.Sem.Entry.linux _ _).2

-- The counters' facts are those of the concrete layout `Le`, decided one word at a time.

/-- **The counters lie in `.data`** at `Le` (`hctrD`). -/
theorem hctrD_e : ∀ a ∈ [Le.pnA, Le.lockA, Le.freeNA, Le.nextA], Le.Λ.data.contains a.toNat := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The counters are not the second limit word** at `Le` (`hctr2`). -/
theorem hctr2_e : ∀ a ∈ [Le.pnA, Le.lockA, Le.freeNA, Le.nextA], a ≠ lim2A Le := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **A13's data part** at `Le` (`hA13`). -/
theorem hA13_e : Scc.Cert.Spawn.X64.a13data Le.Λ outLit.prog outLit.secs = true := by
  decide +kernel

end Spike.Test.WakeLinkedX64

/-- info: 'Spike.Test.WakeLinkedX64.hsub1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.hsub1

/-- info: 'Spike.Test.WakeLinkedX64.hA13_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.hA13_e
