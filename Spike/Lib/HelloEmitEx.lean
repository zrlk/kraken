/-
**hello.w: the output row under `helloMsW`, with its byte step discharged**
(the non-vacuity example of `HelloByteOutP.ByteOutP`). The memory side
`helloMsW` puts `bo := ByteOutP helloSrc lbl`; this file shows that the
byte step of an `Out.emit` row is a theorem at `print`'s published loop,
not a premise, and that the run the byte step names exists at the real
data and emits `"Hello, world\n"`.

- `byteOutP_printCP`: from the loop invariant `PrintCP … k` below `printN n
  m`, byte `b + k` of the buffer placed at `b` is a `ByteOutP` step into
  `PrintCP … (k + 1)` (`printCP_load`, `ByteOutP.load`, `ByteOutP.closed`,
  `printCP_next`).
- `hbyteH`: the byte premise `hbyte` of `PrintF.FA.hsvc_of_emitT` (and its
  twins) at `ms := helloMsW …`, `P := PrintCP …`, `buf0` the buffer's
  address, for every state.
- `emitRowH`: **an `Out.emit` row under `helloMsW`** at a `write(1, b + k0,
  printN n m - k0)` system call, the source at `PrintCP … k0`; its only
  premises on the machine state are the call (`atSys`, `decode`) and the
  write abort's phase on a refusal (`hab`, the `we` clause).
- `hsvc_emitH`: `PrintF.FA.hsvc_of_emitT` at `helloMsW` with `hbyte`
  discharged by `hbyteH`: `print`'s `write` node is a segment.
- `printCP_ex`: at hello's buffer (13 bytes in 2 words, `printN 13 2 = 13`)
  every invariant `PrintCP … k`, `k ≤ 13`, holds of an explicit control, so
  the byte step's premise is inhabited at every byte.
- `loadCP_byte_hello`: **the source side of byte `k < 13`** at a thread `i ≠
  0` at the element's `idx`, the frozen buffer's latest messages holding
  `bufW` (`HelloFrz.hM_frz`): `loadCP_byte_i` emits byte `k` of `"Hello,
  world\n"` and lands in `ByteOutP.load`'s landing set, from which the
  source runs to `PrintCP … (k + 1)`.
-/
import Spike.Lib.HelloByteOutP
import Spike.Lib.HelloFrz
import Spike.Lib.A64HelloInst
import Spike.Lib.A64PrintF

namespace Spike.Lib.HelloEmitEx

open CoreLang CoreTerm TermRun
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.HelloPrintSrcPub (PrintCP loadCP nextCP elemW printCP_load printCP_next printLPD_find loadCP_byte_i)
open Spike.Lib.HelloByteOutP (ByteOutP helloMsW)
open Scc.Sem.Kernel (writeRefused results)
open Spike.Lib.Inv2Core (Inv2Core Inv2Params SpawnRec)

/-! ## The byte step at `print`'s loop -/

/-- **The byte step from the loop invariant**: below `printN n m`, from
`PrintCP … k`, byte `b + k` of the buffer at `b` is a `ByteOutP` step into
`PrintCP … (k + 1)`. -/
theorem byteOutP_printCP {I : ISA} {lbl : WeakMem.AllocLabel → Option Nat} {s : I.State} {pw wn : Word}
    {l : WeakMem.AllocLabel} {b n m k : Nat} {c1 : Ctl} (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some b)
    (hwn : wn.val = .num n) (hk : k < printN n m) (h : PrintCP pw wn n m k c1) :
    ByteOutP HelloSrc.helloSrc lbl s (b + k) c1 (PrintCP pw wn n m (k + 1)) := by
  refine ByteOutP.closed (printCP_load printLPD_find h hk).toLocalRun (ByteOutP.load hpw hl) ?_
  rintro _ ⟨mw, v, rfl⟩
  obtain ⟨c2, r, h2⟩ := printCP_next (lw := elemW pw l (k / 8)) (mw := mw) (b := v) printLPD_find hwn hk
  exact ⟨c2, r.toLocalRun, h2⟩

variable {L : RuntimeLayout} {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {AbW : isaLSE2.State → Prop}

/-- **`hsvc_of_emitT`'s byte premise at `helloMsW`**: `P := PrintCP …`, the
buffer at `buf0` (`buf0.toNat = b`, the whole count below `2^64`). -/
theorem hbyteH {pw wn : Word} {l : WeakMem.AllocLabel} {n m : Nat} {buf0 : BitVec 64}
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some buf0.toNat) (hwn : wn.val = .num n)
    (hfit : buf0.toNat + printN n m < 2 ^ 64) :
    ∀ (s : isaLSE2.State) (k j : Nat) (c1 : Ctl), k + j < printN n m → PrintCP pw wn n m (k + j) c1 →
      (helloMsW L G lbl lsize AbW).bo s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1
        (PrintCP pw wn n m (k + j + 1)) := by
  intro s k j c1 hkj h
  have e : (buf0 + BitVec.ofNat 64 k).toNat + j = buf0.toNat + (k + j) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [e]
  exact byteOutP_printCP (s := s) hpw hl hwn hkj h

/-! ## The output row -/

/-- **Where the output row lands**: the state the kernel returns `r` to
after `j` bytes, the source at `PrintCP … (k0 + j)`. -/
def EmitLand (pw wn : Word) (n m k0 : Nat) (s : isaLSE2.State) : Frag isaLSE2 := fun s' c' =>
  ∃ j r, j ≤ printN n m - k0 ∧ WriteRetOk j r ∧ s' = Scc.Sem.A64.abi.ret s r ∧ PrintCP pw wn n m (k0 + j) c'

/-- **An `Out.emit` row under `helloMsW`**: at a `write(1, b + k0, printN n
m - k0)` system call, the source at `PrintCP … k0` (`Pw j := PrintCP … (k0 +
j)`, `Qw := PrintCP … k0`), each byte step `byteOutP_printCP`, a refusal
landing in the abort phase `AbW` (`hab`). -/
theorem emitRowH {s : isaLSE2.State} {c : Ctl} {pw wn : Word} {l : WeakMem.AllocLabel} {b n m k0 : Nat}
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some b) (hwn : wn.val = .num n)
    (ha : Scc.Sem.A64.abi.atSys s = true)
    (hd : Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.write 1 (b + k0) (printN n m - k0)))
    (hab : ∀ r, writeRefused r = true → AbW (Scc.Sem.A64.abi.ret s r)) (hc : PrintCP pw wn n m k0 c) :
    Out HelloSrc.helloSrc lbl (helloMsW L G lbl lsize AbW) (EmitLand pw wn n m k0 s) s c := by
  refine .emit Scc.Sem.A64.abi (b + k0) (printN n m - k0) (fun j c1 => PrintCP pw wn n m (k0 + j) c1)
    (PrintCP pw wn n m k0) rfl ha hd ⟨c, .refl c, by simpa using hc⟩ ?_ ?_ (fun _ _ r hr => hab r hr)
  · intro j hj c1 h
    have e : b + k0 + j = b + (k0 + j) := by omega
    show ByteOutP HelloSrc.helloSrc lbl s (b + k0 + j) c1 (PrintCP pw wn n m (k0 + (j + 1)))
    rw [e]
    exact byteOutP_printCP (s := s) hpw hl hwn (by omega) h
  · intro j hj c1 h r _ hr
    refine ⟨⟨j, r, hj, hr, rfl, h⟩, fun hj0 _ => ?_⟩
    subst hj0
    simpa using h

/-! ## The `write` node -/

section Svc

open Spike.Lib.A64 Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker Kraken.Promising.Lower.A64

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {x29 ra buf0 : BitVec 64} {tp : UInt64}

/-- **`print`'s `write` node at `helloMsW`** (`PrintF.FA.hsvc_of_emitT` at
`P := PrintCP …`, `len0 := printN n m`, `hbyte` discharged by `hbyteH`); the
abort's justification at the node (`hwe`) as `hsvc_of_emitT` asks it. -/
theorem hsvc_emitH {pw wn : Word} {l : WeakMem.AllocLabel} {n m : Nat} {Q : Nat → Ctl → Prop}
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some buf0.toNat) (hwn : wn.val = .num n)
    (hfit : buf0.toNat + printN n m < 2 ^ 64) (hlen : printN n m < 2 ^ 63) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (PrintF.FA.N (_root_.Executable.labels exe).label x29 ra buf0 (printN n m)
        (PrintCP pw wn n m) Q .svc).pc [svcDir])
    (hPQ : ∀ k c, PrintCP pw wn n m k c → Q k c)
    (hwe : ∀ s c, At exe endPc R F ((PrintF.FA.N (_root_.Executable.labels exe).label x29 ra buf0 (printN n m)
        (PrintCP pw wn n m) Q .svc).withTp tp) s c → ∀ k c1, Q k c1 → (helloMsW L G lbl lsize AbW).we s c1) :
    SegT HelloSrc.helloSrc lbl (helloMsW L G lbl lsize AbW)
      (At exe endPc R F ((PrintF.FA.N (_root_.Executable.labels exe).label x29 ra buf0 (printN n m)
        (PrintCP pw wn n m) Q .svc).withTp tp))
      (At exe endPc R F ((PrintF.FA.N (_root_.Executable.labels exe).label x29 ra buf0 (printN n m)
        (PrintCP pw wn n m) Q .n5).withTp tp)) :=
  PrintF.FA.hsvc_of_emitT rfl hF (fun _ _ _ => hlen) hcode hPQ
    (fun s _ _ => hbyteH (L := L) (G := G) (lsize := lsize) (AbW := AbW) hpw hl hwn hfit s) hwe

end Svc

/-! ## At hello's buffer -/

/-- **Every loop invariant of hello's message is inhabited**: 13 bytes in 2
words, at each `k ≤ 13` an explicit control. -/
theorem printCP_ex {pw wn : Word} (hwn : wn.val = .num 13) (k : Nat) (hk : k ≤ 13) :
    ∃ c, PrintCP pw wn 13 2 k c := by
  by_cases h8 : k < 8
  · exact ⟨⟨HelloPrintSrcPub.printLBodyP, HelloPrintSrcPub.topEnvP (PrintSrc.printArgs pw wn 0 (2 - 1 - 0) k k),
      none⟩, 0, k, rfl, rfl, rfl, by omega, by omega, by omega, hwn⟩
  · exact ⟨⟨HelloPrintSrcPub.printLBodyP, HelloPrintSrcPub.topEnvP (PrintSrc.printArgs pw wn 1 (2 - 1 - 1) k (k - 8)),
      none⟩, 1, k - 8, rfl, rfl, rfl, by omega, by omega, by omega, hwn⟩

/-- hello's message has `printN 13 2 = 13` bytes. -/
theorem printN_hello : printN 13 2 = 13 := rfl

/-- **Byte `k` of hello's buffer words is byte `k` of `"Hello, world\n"`.** -/
theorem bufW_byte {k : Nat} (hk : k < 13) :
    some (laneN .w8 (HelloPreA.bufW (k / 8)) (k % 8)) = ("Hello, world\n".toUTF8.toList.map (·.toNat))[k]? := by
  rw [HelloInst.bufBytes_utf8, ← HelloInst.bufBytes]
  simp [List.getElem?_map, List.getElem?_range hk]

variable {P : SrcParams}

/-- **The source side of byte `k < 13` of hello's message** at a thread `i ≠
0` at the element's `idx`, the buffer `⟨l, ·⟩` frozen with `bufW`
(`HelloFrz.hM_frz`): `loadCP_byte_i` lands in `ByteOutP.load`'s landing
set, from which the source runs locally to `PrintCP … (k + 1)`, and the run
(once its landing is certified) emits byte `k` of `"Hello, world\n"`. -/
theorem loadCP_byte_hello {I : ISA} {Λ : Scc.Sem.Layout} {R : SpawnRec} {Pi : Inv2Params I} {G' : Loc → Val → Prop}
    {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I} {s0 s1 : TTh} {ts : Nat → Option Nat}
    {tp sp : List Nat} (hP : UsesWc P HelloSrc.helloSrc) {s : Cfg} {i : Nat} {th : TTh} {pw wn : Word}
    {l : WeakMem.AllocLabel} {k : Nat} (hk : k < 13) (hwn : wn.val = .num 13)
    (hinv : Inv2Core Λ R Pi G' own tm t0 t1 s.mem s0 s1 ts tp sp) (hb : HelloFrz.FrzBuf R.S l HelloPreA.bufW 2 s.mem)
    (hf : Pi.frzS ⟨l, k / 8⟩)
    (hi0 : i ≠ 0) (hi : s.ths[i]? = some th) (ht : th.term = (loadCP pw wn 2 k).term)
    (he : th.env = (loadCP pw wn 2 k).env) (hσ : th.σs = []) (hpr : th.promises = [])
    (hpw : pw.val = .loc ⟨l, 0⟩ 0)
    (hex : mainExit s = []) (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s) :
    ∃ (th' : TTh) (c' : Ctl), th'.term = c'.term ∧ th'.env = c'.env ∧ th'.σs = [] ∧
      (∃ mw v, c' = nextCP pw wn 2 k (elemW pw l (k / 8)) mw v) ∧
      (∃ c2, LocalRun HelloSrc.helloSrc c' c2 ∧ PrintCP pw wn 13 2 (k + 1) c2) ∧
      (Certified HelloSrc.helloSrc P.k P.arch
          (HelloPrintSrcPub.outCfgI s i th' (laneN .w8 (HelloPreA.bufW (k / 8)) (k % 8))) i →
        (source P HelloSrc.helloSrc).Run s [.out ⟨laneN .w8 (HelloPreA.bufW (k / 8)) (k % 8) % 256,
            Nat.mod_lt _ (by decide)⟩]
          (HelloPrintSrcPub.outCfgI s i th' (laneN .w8 (HelloPreA.bufW (k / 8)) (k % 8)))) ∧
      some (laneN .w8 (HelloPreA.bufW (k / 8)) (k % 8)) = ("Hello, world\n".toUTF8.toList.map (·.toNat))[k]? := by
  have hk8 : k / 8 < 2 := by omega
  obtain ⟨th', mw, ht', he', hσ', -, -, -, -, -, hrun⟩ := loadCP_byte_i (w := HelloPreA.bufW) hP hi0 hi ht he hσ
    hpr hpw hex hx (HelloFrz.hM_frz hinv hb hk8 hf)
  refine ⟨th', _, ht', he', hσ', ⟨mw, _, rfl⟩, ?_, hrun, bufW_byte hk⟩
  obtain ⟨c2, r, h2⟩ := printCP_next (lw := elemW pw l (k / 8)) (mw := mw)
    (b := laneN .w8 (HelloPreA.bufW (k / 8)) (k % 8)) (n := 13) (m := 2) printLPD_find hwn
    (by rw [printN_hello]; exact hk)
  exact ⟨c2, r.toLocalRun, h2⟩

end Spike.Lib.HelloEmitEx

/-- info: 'Spike.Lib.HelloEmitEx.byteOutP_printCP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitEx.byteOutP_printCP

/-- info: 'Spike.Lib.HelloEmitEx.hbyteH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitEx.hbyteH

/-- info: 'Spike.Lib.HelloEmitEx.emitRowH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitEx.emitRowH

/-- info: 'Spike.Lib.HelloEmitEx.hsvc_emitH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitEx.hsvc_emitH

/-- info: 'Spike.Lib.HelloEmitEx.printCP_ex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitEx.printCP_ex

/-- info: 'Spike.Lib.HelloEmitEx.loadCP_byte_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitEx.loadCP_byte_hello
