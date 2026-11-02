/-
**hello.w's child print `write` on x86-64** (the twin of `Spike/Lib/HelloChildSvc.lean`; the child premise
`hsvc` of `Hello.ChildPrem`): `print`'s `write` node in the child's `wc_worker` call is a segment
(`PrintF.FA.hsvc_of_emitTNN`), for any memory side whose byte step contains `print`'s
(`ByteOutP helloSrc lbl`, `hbo`) and whose abort justification holds at the node (`hwe`).

The child segment's memory side has the byte step `ByteOutP` and the abort justification
`WeAb abi (WriteAb.Ab lab)`; `hsvc_IW` states `hsvc` there.

- `prW_byte`: `print`'s byte step at `PrW` (`byteOutP_printCP` closed under the predicate's local runs).
- `hsvc_W`: the `hsvc` field (`SvcX`) from `hbo`, `hwe`, the slice's placement and the count's bound.
- `printSvcWeF`: every refused result of the `write` lands in the write abort's phase, from the `syscall`'s
  cell (instead of `InstOk`).
- `hsvc_IW`: `hsvc_W` with `hwe` discharged by `printSvcWeF`.

## Differences from the AArch64 version

- The source is `X64HelloSrc.helloSrc`; the byte step is `X64HelloByteOutP.ByteOutP` (`X64HelloEmitEx`).
- `SvcX` is x86-64's (`X64HelloWorkerSegR`): every region `Rw` of `wc_worker`, the call node `Body.wCall` (whose
  states name the head's flags), `print`'s region `R'.lo ≤ -40`, `16 ≤ R'.hi` (no alignment), its `write` node
  `.sys` (AArch64 `.svc`), its nodes `PrintF.cN … (-96) σC`.
- The buffer and count are `%rdi`, `%rsi` (`Body.wkC_rdi`; AArch64 `x0`, `x1`); `hwe`'s count premise is on
  `%rsi`.
- `print`'s node facts are `SegR.wcR_hZPc` at `.sys` (`NodeZA.toW`; AArch64 `Z.wcR_hZP`).
- `printSvcWeF` reads the stored length at `-16(%rbp)` (`PrintG.bpLoad_of_abs`; AArch64 `[sp + 8]`) and takes
  the `syscall`'s code as `hsvc_of_emitTNN`'s `hcode` does; the return is `WriteAb.pcRet`, the `syscall`'s next
  pc.
-/
import Spike.Lib.X64HelloWorkerSegP
import Spike.Lib.X64HelloEmitEx
import Spike.Lib.X64HelloPrintNN
import Spike.Lib.X64PrintGSvc
import Spike.Lib.X64HelloZSrc

namespace Spike.Lib.X64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (wcP)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.X64HelloPrintSrcPub (PrintCP)
open Spike.Lib.X64HelloByteOutP (ByteOutP)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.X64.Flow.Worker.Hello.Z (ZR prW_notUnpk)
open Scc.Cert.Rt.X64 (Lays endOf)
open SccCode (helloCells)

/-- **`print`'s byte step at `PrW`**: byte `k + j` of the slice placed at
`buf0` from `PrW … (k + j)` into `PrW … (k + j + 1)`. -/
theorem prW_byte {I : ISA} {lbl : WeakMem.AllocLabel → Option Nat} {s : I.State} {pw wn : TermRun.Word}
    {l : WeakMem.AllocLabel} {n m : Nat} {buf0 : BitVec 64}
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some buf0.toNat) (hwn : wn.val = .num n)
    (hfit : buf0.toNat + printN n m < 2 ^ 64) {k j : Nat} {c1 : Ctl} (hkj : k + j < printN n m)
    (h : PrW pw wn n m (k + j) c1) :
    ByteOutP helloSrc lbl s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (PrW pw wn n m (k + j + 1)) := by
  obtain ⟨⟨c1', r, hc⟩, -⟩ := h
  have e : (buf0 + BitVec.ofNat 64 k).toNat + j = buf0.toNat + (k + j) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [e]
  exact X64HelloByteOutP.ByteOutP.closed r.toLocalRun (X64HelloEmitEx.byteOutP_printCP (s := s) hpw hl hwn hkj hc)
    fun c2 h2 => ⟨c2, .refl _, X64HelloWorkerCallSrc.PrW.of_printCP h2⟩

section Svc

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {F : MachineData → Prop}

/-- **`ChildPrem.hsvc`** for any memory side containing `print`'s byte step
(`hbo`) and its abort justification at the `write` node (`hwe`): the slice
`w0` a locative to `l`, placed at the buffer the worker's block computes
(`wkC_rdi`: `w.w0` plus the low word of `w.w1`), its count in bounds. -/
theorem hsvc_W (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} {l : WeakMem.AllocLabel}
    (hpw : w0.val = .loc ⟨l, 0⟩ 0)
    (hl : lbl l = some (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat) (hwn : w2.val = .num n)
    (hfit : (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat + printN n m < 2 ^ 64)
    (hlen : printN n m < 2 ^ 63)
    (hbo : ∀ fr s a c Q, ByteOutP helloSrc lbl s a c Q → (ms [fr]).bo s a c Q)
    (hwe : ∀ fr (R' : Region) (F' : MachineData → Prop) (σC : AS), R'.lo ≤ -40 → 16 ≤ R'.hi →
      (σC.regs.get64 .rsi).toNat = printN n m → ∀ s c,
      At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
        (fun _ => PrW w0 w2 n m) (-96) σC .sys) s c → ∀ k c1, PrW w0 w2 n m k c1 → (ms [fr]).we s c1) :
    SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m := by
  intro rbp ra Rw fr R' F' hR' hlo' hhi' hF' _ _ σC c _ hJ _ Xf hXf
  obtain ⟨⟨σ0, c0, fl, hJ0, rfl⟩, -, hx1⟩ := hJ
  have hx0 : (Body.wkC (_root_.Executable.labels exe).label σ0 fl).regs.get64 .rdi =
      w.w0 + BitVec.setWidth 64 (w.w1.take 32) := by
    rw [Body.wkC_rdi, hJ0.2.1, hJ0.2.2.1]
  refine PrintF.FA.hsvc_of_emitTNN (hK [fr]) hF' (fun _ _ _ => by rw [hx1]; exact hlen)
    (fun s he hn => (Wk.printCode (c0 := wcP w0 w1 w2 w3 w4) (rbp0 := 0) (ra := 0) hp hend).sys s he hn)
    (fun _ _ h => h) ?_
    (hwe fr R' F' _ hlo' hhi' hx1)
    (NodeW.and (NodeZA.toW (d := (.instr (.regular .W64 .W64 .syscall), 2))
      (wcR_hZPc (fr := fr) (F := F') (Pc := fun _ => PrW w0 w2 n m) (Qc := fun _ => PrW w0 w2 n m) (ko := -96)
        (σC := Body.wkC (_root_.Executable.labels exe).label σ0 fl) hp hend hR' hlo' hhi'
        (fun _ _ h => prW_notUnpk h) (fun _ _ h => prW_notUnpk h) .sys)) hXf)
  intro s _ _ k j c1 hkj h
  rw [hx1] at hkj
  rw [hx0]
  exact hbo fr s _ c1 _ (prW_byte hpw hl hwn hfit hkj h)

omit [Kraken.Executable.ValidLayout exe] in
/-- **Every refused result of `print`'s `write` lands in the write abort's
phase** (`WeAb abi (WriteAb.Ab lab)`, `PrintG.printSvcWe` at `PrintA.N`'s
`syscall` node under a thread pointer, from the `syscall`'s code instead of
`InstOk`): the return is at `pcRet`, the stored length `-16(%rbp)` (cell
`-16`) at most `len0 < 2^63`. -/
theorem printSvcWeF {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop} {tp : UInt64}
    {R : Region}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (PrintA.N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).pc
        [(.instr (.regular .W64 .W64 .syscall), 2)])
    (hlo : R.lo ≤ -16) (hhi : -8 ≤ R.hi) (hlen : len0 < 2 ^ 63) {s : State} {c : Ctl}
    (hAt : At exe endPc R F ((PrintA.N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys).withTp tp)
      s c) :
    X64ConsumerA.WeAb Scc.Sem.X64.abi (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s c := by
  intro r hr
  obtain ⟨hs, hn, -, hpc, σ, hA, -, ⟨⟨k, ⟨-, -, -, h16, hk⟩, -⟩, -⟩, -⟩ := id hAt
  have hc : CellAt s (.instr (.regular .W64 .W64 .syscall)) 2 := (hcode s hs hn).cell0 rfl rfl hpc
  have hret : (Scc.Sem.X64.abi.ret s r).st.2 = Spike.Lib.X64.WriteAb.pcRet (_root_.Executable.labels exe).label := by
    show Scc.Sem.X64.nextPc s = _
    rw [Scc.Sem.X64.nextPc_of_cellAt hc, hpc]
    simp only [ND.withTp, PrintA.N, Spike.Lib.X64.Print.pcSys, Spike.Lib.X64.WriteAb.pcRet]
    rw [Int64.add_assoc]; rfl
  have hl : Spike.Lib.X64.WriteAb.bpLoad (Scc.Sem.X64.abi.ret s r) (-16) = some (σ.slot (-16)) :=
    Spike.Lib.X64.PrintG.bpLoad_of_abs (s := s) hA rfl hlo hhi
  have hx : (Scc.Sem.X64.abi.ret s r).st.1.regs.get64 .rax = r := by
    simp [Scc.Sem.X64.abi, Scc.Sem.X64.retRegs64, Reg64s.get64]
  refine .inl ⟨hret, σ.slot (-16), hl, ?_⟩
  rw [hx]
  refine Spike.Lib.X64.PrintAb.refusal_of_refused ?_ hr
  rw [h16, BitVec.toNat_ofNat]
  omega

/-- **`ChildPrem.hsvc` at the write abort's phase**: `hsvc_W` with the
abort justification any memory side containing `WeAb abi (WriteAb.Ab lab)`
(`hwe`), discharged by `printSvcWeF`. -/
theorem hsvc_IW (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} {l : WeakMem.AllocLabel}
    (hpw : w0.val = .loc ⟨l, 0⟩ 0)
    (hl : lbl l = some (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat) (hwn : w2.val = .num n)
    (hfit : (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat + printN n m < 2 ^ 64)
    (hlen : printN n m < 2 ^ 63)
    (hbo : ∀ fr s a c Q, ByteOutP helloSrc lbl s a c Q → (ms [fr]).bo s a c Q)
    (hwe : ∀ fr s c, X64ConsumerA.WeAb Scc.Sem.X64.abi
      (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s c → (ms [fr]).we s c) :
    SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m :=
  hsvc_W hp hend hK hpw hl hwn hfit hlen hbo fun fr' R'' F'' σC' hlo'' hhi'' hx s c' hAt _ c1 _ =>
    hwe fr' s c1 (printSvcWeF (F := F'') (P := PrW w0 w2 n m) (Q := PrW w0 w2 n m)
      (fun s he hn => (Wk.printCode (c0 := wcP w0 w1 w2 w3 w4) (rbp0 := 0) (ra := 0) hp hend).sys s he hn)
      (by omega) (by omega)
      (by rw [hx]; exact hlen) (R := R'') (c := c') hAt)

end Svc

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegR.prW_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prW_byte

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegR.hsvc_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsvc_W

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegR.printSvcWeF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcWeF

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegR.hsvc_IW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsvc_IW

end Spike.Lib.X64.Flow.Worker.Hello.SegR
