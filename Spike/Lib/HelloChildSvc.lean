/-
**hello.w's child print `write`** (ChildPrem row `hsvc` of
`Hello.SegR.ChildPrem`): `print`'s `write` node in the child's `wc_worker`
call is a segment (`PrintF.FA.hsvc_of_emitTNN`), for any memory side whose
byte step contains `print`'s (`ByteOutP helloSrc lbl`, `hbo`) and whose
abort justification holds at the node (`hwe`).

`ChildPrem` at `msH` (`bo`, `we` the defaults, none) cannot meet `hbyte`;
this row is stated generically; the child segment is at `HelloMsW.msWH`
(byte step `ByteOutP`, abort justification `WeAb abi (WriteAb.Ab lab)`),
where `HelloChildSvcI.hsvc_I` instantiates it (so `hsvc`
is not vacuous).

- `prW_byte`: `print`'s byte step at `PrW` (`byteOutP_printCP` closed under
  the predicate's local runs).
- `hsvc_W`: the `hsvc` field from `hbo`, `hwe`, the slice's placement and
  the count's bound.
-/
import Spike.Lib.A64HelloWorkerSegP
import Spike.Lib.HelloEmitEx
import Spike.Lib.A64PrintGAb

namespace Spike.Lib.A64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.HelloPrintSrcPub (PrintCP)
open Spike.Lib.HelloByteOutP (ByteOutP)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZR prW_notUnpk)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

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
  exact HelloByteOutP.ByteOutP.closed r.toLocalRun (HelloEmitEx.byteOutP_printCP (s := s) hpw hl hwn hkj hc)
    fun c2 h2 => ⟨c2, .refl _, HelloWorkerCallSrc.PrW.of_printCP h2⟩

section Svc

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {F : MachineData → Prop}

/-- **`ChildPrem.hsvc`** for any memory side containing `print`'s byte step
(`hbo`) and its abort justification at the `write` node (`hwe`): the slice
`w0` a locative to `l`, placed at the buffer the worker's block computes
(`wkC_x0`: `w.w0` plus the low word of `w.w1`), its count in bounds. -/
theorem hsvc_W (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} {l : WeakMem.AllocLabel}
    (hpw : w0.val = .loc ⟨l, 0⟩ 0)
    (hl : lbl l = some (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat) (hwn : w2.val = .num n)
    (hfit : (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat + printN n m < 2 ^ 64)
    (hlen : printN n m < 2 ^ 63)
    (hbo : ∀ fr s a c Q, ByteOutP helloSrc lbl s a c Q → (ms [fr]).bo s a c Q)
    (hwe : ∀ fr (R' : Region) (F' : MachineData → Prop) (σC : AS), R'.lo ≤ -48 → 0 ≤ R'.hi →
      σC.regs.X1.toBitVec.toNat = printN n m → ∀ s c,
      At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
        (fun _ => PrW w0 w2 n m) σC .svc) s c → ∀ k c1, PrW w0 w2 n m k c1 → (ms [fr]).we s c1) :
    SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m := by
  intro x29 ra fr R' F' hR' hal' hlo' hhi' hF' _ σC c _ hJ _ Xf hXf
  obtain ⟨⟨σ0, c0, hJ0, rfl⟩, -, hx1⟩ := hJ
  have hx0 : (Body.wkC (_root_.Executable.labels exe).label σ0).regs.X0.toBitVec =
      w.w0 + BitVec.setWidth 64 (w.w1.take 32) := by
    rw [Body.wkC_x0, hJ0.2.1, hJ0.2.2.1]
  have hcode : PrintF.Code c0 x29 ra exe endPc := Wk.printCode hp hend
  refine PrintF.FA.hsvc_of_emitTNN (hK [fr]) hF' (fun _ _ _ => by rw [hx1]; exact hlen)
    (fun s he hn => hcode.svc s he hn) (fun _ _ h => h) ?_
    (hwe fr R' F' _ hlo' hhi' hx1) (NodeW.and (Z.wcR_hZP (fr := fr) (F := F') (Pc := fun _ => PrW w0 w2 n m) (Qc := fun _ => PrW w0 w2 n m)
      (σC := Body.wkC (_root_.Executable.labels exe).label σ0) hp hend hR' hal' (Int.le_trans hlo' (by decide)) hhi'
      (fun _ _ h => prW_notUnpk h) (fun _ _ h => prW_notUnpk h) .svc).toW hXf)
  intro s _ _ k j c1 hkj h
  rw [hx1] at hkj
  rw [hx0]
  exact hbo fr s _ c1 _ (prW_byte hpw hl hwn hfit hkj h)

/-- **Every refused result of `print`'s `write` lands in the write abort's
phase** (`WeAb abi (WriteAb.Ab lab)`, `PrintG.printSvcWe` at `FA.N`'s `write`
node under a thread pointer, from `PrintF.Code` instead of `InstOk`): the
return is at `pcRet`, the stored length `[sp + 8]` (cell `-40`) at most
`len0 < 2^63`. -/
theorem printSvcWeF {c0 : Ctl} {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop} {tp : UInt64}
    {R : Region} (hcode : PrintF.Code c0 x29 ra exe endPc) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hlen : len0 < 2 ^ 63) {s : State} {c : Ctl}
    (hAt : At exe endPc R F ((PrintF.FA.N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp)
      s c) :
    A64ConsumerA.WeAb Scc.Sem.A64.abi (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s c := by
  intro r hr
  obtain ⟨he, hn, -, hpc, σ, hA, -, ⟨⟨k, ⟨-, -, -, h40, hk⟩, -⟩, -⟩, -⟩ := id hAt
  have hc : CellAt s svcDir 4 :=
    (hcode.svc s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp only [ND.withTp, PrintF.FA.N, PrintF.N]; exact (ofNat4_zero _).symm)
  have hret : (Scc.Sem.A64.abi.ret s r).st.2 = Spike.Lib.A64.WriteAb.pcRet (_root_.Executable.labels exe).label := by
    show Scc.Sem.A64.nextPc s = _
    rw [Scc.Sem.A64.nextPc_of_cellAt hc, hpc]; rfl
  obtain ⟨e8, -⟩ := Spike.Lib.A64.PrintG.spLoad_of_abs hA rfl hlo hhi
  have hl : Spike.Lib.A64.WriteAb.spLoad (Scc.Sem.A64.abi.ret s r) 8 = some (σ.slot (-40)) := e8
  have hx : (Scc.Sem.A64.abi.ret s r).st.1.regs.X0.toBitVec = r := by simp [Scc.Sem.A64.abi]
  refine .inl ⟨hret, σ.slot (-40), hl, ?_⟩
  rw [hx]
  refine Spike.Lib.A64.PrintAb.refusal_of_refused ?_ hr
  rw [h40, BitVec.toNat_ofNat]
  omega

/-- **`ChildPrem.hsvc` at the write abort's phase**: `hsvc_W` with the
abort justification any memory side containing `WeAb abi (WriteAb.Ab lab)`
(`hwe`), discharged by `printSvcWeF`. -/
theorem hsvc_IW (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    {w : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} {l : WeakMem.AllocLabel}
    (hpw : w0.val = .loc ⟨l, 0⟩ 0)
    (hl : lbl l = some (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat) (hwn : w2.val = .num n)
    (hfit : (w.w0 + BitVec.setWidth 64 (w.w1.take 32)).toNat + printN n m < 2 ^ 64)
    (hlen : printN n m < 2 ^ 63)
    (hbo : ∀ fr s a c Q, ByteOutP helloSrc lbl s a c Q → (ms [fr]).bo s a c Q)
    (hwe : ∀ fr s c, A64ConsumerA.WeAb Scc.Sem.A64.abi (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label)
      s c → (ms [fr]).we s c) :
    SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m := by
  intro x29 ra fr R' F' hR' hal' hlo' hhi' hF' hFF σC c cE hJ hC Xf hXf
  refine hsvc_W (F := F) hp hend hK hpw hl hwn hfit hlen hbo ?_ x29 ra fr R' F' hR' hal' hlo' hhi' hF' hFF σC c cE
    hJ hC Xf hXf
  intro fr' R'' F'' σC' hlo'' hhi'' hx s c' hAt _ c1 _
  have hl' : σC'.regs.X1.toBitVec.toNat < 2 ^ 63 := by rw [hx]; exact hlen
  exact hwe fr' s c1 fun r hr => printSvcWeF (F := F'') (x29 := σC'.regs.X29.toBitVec) (ra := σC'.regs.X30.toBitVec)
    (buf0 := σC'.regs.X0.toBitVec) (P := PrW w0 w2 n m) (Q := PrW w0 w2 n m) (tp := σC'.regs.TPIDR_EL0)
    (Wk.printCode (c0 := wcP w0 w1 w2 w3 w4) hp hend) hlo'' hhi'' hl' hAt r hr

end Svc

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.hsvc_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsvc_W

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.hsvc_IW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsvc_IW

end Spike.Lib.A64.Flow.Worker.Hello.SegR
