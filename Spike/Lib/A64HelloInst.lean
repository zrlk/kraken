/-
**hello.w on AArch64: the instance data of the frozen buffer** (prep; ISA-generic except `texitFactsH`). hello's
location sets are
wake's (`WakeP.wakeP`, every word placed at the spawn but `c` frozen) at
location data whose placement also holds rodata's buffer `newBuf` (label
`lB`, base `b0`); this file proves that the buffer's words are frozen on
both sides, fixes the `Prot` conjunct `FrzBufL`, and `kr_exit1` for
hello's kernel relation `KRH`.

- `helloP`: hello's `Inv2Params`, wake's `wakeP` (no new location set).
- `BufPl lbl lsize cS lB b0`: the buffer placed at the spawn (`lbl lB =
  some b0`), at least two words (`2 ≤ lsize lB`), off `c`'s label.
- `lrange_fit`: a placed label's range fits below `2^64` (`MemRelP`, `Λ.WF`).
- `frzS_buf`, `buf_ne_cS`, `frz_buf`: the buffer's source words `⟨lB, i⟩`
  and target words `wordLoc (b0 + 8 i)`, `i < 2`, are frozen (`frz_buf` uses
  `WCompat.cT`'s shape of `cT` and `MemRelP.lbl_disj`).
- `HelloProtB`: hello's `Prot`, `HelloProt` and `FrzBufL R.S lB bufW 2`;
  `helloProtB_start` at the spawn; `HelloProtB.frzL`, `frzL_mono`.
- `frzBufL_of_bufAt`: `ClonePreH`'s buffer conjunct (`BufAtSpawn`) is
  `FrzBufL` at `S = sm.size` (the open `hbuf` of `clonePreH_of` is this
  conjunct's source fact).
- `texitFactsH`: `TexitFacts` for a relation whose kernel relation is `KRH`
  (`kr_exit1 := krh_exit1`).
- Content facts at hello: `bufW_lt`, `bufBytes` (the 13 bytes of
  `"Hello, world\n"` are the lanes of `bufW`), `rodata_bufW` (rodata's two
  lane words are `bufW 0`, `bufW 1`), `rodata_two` (the buffer has 2
  elements, enough for 13 bytes).
-/
import Spike.Lib.WakeP
import Spike.Lib.WakeW1
import Spike.Lib.A64HelloWriteK
import Spike.Lib.A64HelloClonePreHOf
import Spike.Lib.HelloRodataSrc

namespace Spike.Lib.HelloInst

open Kraken.Promising Scc.Sem Spike.Lib.Inv2Core Spike.Lib.WakeP Spike.Lib.HelloFrz
open Spike.Lib.HelloProt (HelloProt CRec helloProt_start)
open Spike.Lib.HelloPreA (bufW BufAtSpawn)
open Scc.Sem.MemRel (SLatest)

/-! ## The location sets -/

/-- **hello's `Inv2Params`**: wake's, at location data whose placement
holds the buffer. -/
abbrev helloP {I : ISA} (K : Kernel.Abi I) (μ : Marks) (W : WakeLocs) : Inv2Params I := wakeP K μ W

/-- **The buffer's placement at the spawn**: label `lB` at `b0`, at least
two words, off `c`'s label. -/
def BufPl (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cS : WeakMem.Address)
    (lB : WeakMem.AllocLabel) (b0 : Nat) : Prop :=
  lbl lB = some b0 ∧ 2 ≤ lsize lB ∧ lB ≠ cS.label

section Frz

variable {I : ISA} {K : Kernel.Abi I} {μ : Marks} {W : WakeLocs} {lB : WeakMem.AllocLabel} {b0 : Nat}

/-- **A placed label's range fits below `2^64`.** -/
theorem lrange_fit {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {l : WeakMem.AllocLabel} {b : Nat}
    (hl : lbl l = some b) : b + 8 * lsize l ≤ 2 ^ 64 := by
  have hpin := hwf.inSpace Λ.pinned (by simp [Layout.regions])
  have hheap := hwf.inSpace Λ.heap (by simp [Layout.regions])
  have hdata := hwf.inSpace Λ.data (by simp [Layout.regions])
  simp only [Range.InSpace] at hpin hheap hdata
  rcases (h.lbl_range l b hl).2 with hs | hs | ⟨-, hs⟩ <;> simp only [lrange, Range.Sub] at hs <;> omega

/-- **The buffer's source words are frozen.** -/
theorem frzS_buf (hB : BufPl W.lbl W.lsize W.cS lB b0) {i : Nat} (hi : i < 2) :
    (helloP K μ W).frzS ⟨lB, i⟩ :=
  ⟨⟨by show (W.lbl lB).isSome = true; rw [hB.1]; rfl, by show i < W.lsize lB; have := hB.2.1; omega⟩,
    fun h => hB.2.2 (congrArg WeakMem.Address.label h)⟩

/-- **The buffer's words are not `c`** (`⟨l, i⟩ ≠ cS`). -/
theorem buf_ne_cS (hB : BufPl W.lbl W.lsize W.cS lB b0) (i : Nat) : (⟨lB, i⟩ : WeakMem.Address) ≠ W.cS :=
  fun h => hB.2.2 (congrArg WeakMem.Address.label h)

/-- **The buffer's target words are frozen**: placed (`BufPl`), and not
`cT`, the word placed for `cS` (`WCompat.cT`'s shape), whose label's range
is disjoint from the buffer's (`MemRelP.lbl_disj`). -/
theorem frz_buf {Λ : Scc.Sem.Layout} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (h : MemRelP Λ W.lbl W.lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hB : BufPl W.lbl W.lsize W.cS lB b0)
    (hcT : ∃ a, W.cT = wordLoc a ∧ wordAddr W.lbl W.cS = some a ∧ W.cS.offset < W.lsize W.cS.label)
    {i : Nat} (hi : i < 2) : (helloP K μ W).frz (wordLoc (b0 + 8 * i)) := by
  have hfit := lrange_fit h hwf hB.1
  have h2 := hB.2.1
  have hb : b0 + 8 * i < 2 ^ 64 := by omega
  refine ⟨⟨lB, b0, hB.1, ?_⟩, fun heq => ?_⟩
  · simp only [wordLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, lrange, Range.contains]
    omega
  · obtain ⟨a, hca, hwa, ho⟩ := hcT
    simp only [wordAddr, Option.map_eq_some_iff] at hwa
    obtain ⟨bc, hbc, rfl⟩ := hwa
    have hfc := lrange_fit h hwf hbc
    have hd := h.lbl_disj _ _ _ _ hB.2.2 hB.1 hbc
    simp only [lrange, Range.Disjoint] at hd
    rw [hca] at heq
    obtain ⟨f, hf⟩ : ∃ f : Nat, W.cS.offset = f := ⟨_, rfl⟩
    rw [hf] at heq ho
    have ho' : f + 1 ≤ W.lsize W.cS.label := ho
    have ha : bc + 8 * f < 2 ^ 64 := by omega
    have := MemRel.wordLoc_inj hb ha heq
    omega

end Frz

/-! ## The `Prot` conjunct -/

section Prot

variable {I : ISA}

/-- **hello's protocol**: `HelloProt` and the frozen buffer `FrzBufL` (its
two words' latest messages below `S - 1` holding `bufW`). -/
def HelloProtB (R : SpawnRec) (C : CRec I) (pT : Loc) (lB : WeakMem.AllocLabel) (tm : Memory) (t0 t1 : Thread I)
    (sm : WeakMem.Memory) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat) : Prop :=
  HelloProt R C pT tm t0 t1 sm s0 s1 ts tp sp ∧ FrzBufL R.S lB bufW 2 sm

/-- `HelloProtB`'s buffer conjunct. -/
theorem HelloProtB.frzL {R : SpawnRec} {C : CRec I} {pT : Loc} {lB : WeakMem.AllocLabel} {tm : Memory}
    {t0 t1 : Thread I} {sm : WeakMem.Memory} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    (h : HelloProtB R C pT lB tm t0 t1 sm s0 s1 ts tp sp) : FrzBufL R.S lB bufW 2 sm :=
  h.2

/-- **The buffer conjunct is kept by every source step** (the memory only
grows). -/
theorem frzL_mono {S : Nat} {lB : WeakMem.AllocLabel} {sm sm' : WeakMem.Memory} (h : FrzBufL S lB bufW 2 sm)
    (he : TermCert.MemExt sm sm') : FrzBufL S lB bufW 2 sm' :=
  h.mono he

/-- **`ClonePreH`'s buffer conjunct is `FrzBufL` at the spawn.** -/
theorem frzBufL_of_bufAt {s : TermRun.Cfg} {lB : WeakMem.AllocLabel} (h : BufAtSpawn s lB) :
    FrzBufL s.mem.size lB bufW 2 s.mem :=
  frzBufL_start h

/-- **hello's protocol at the spawn** (`S = sm.size`): `helloProt_start`'s
facts and the buffer's (`BufAtSpawn`'s shape). -/
theorem helloProtB_start {R : SpawnRec} {C : CRec I} {pT : Loc} {lB : WeakMem.AllocLabel} {tm : Memory}
    {t0 t1 : Thread I} {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {sp : List Nat}
    (hT : tm.last ≤ R.T) (hS : R.S = s.mem.size) (hpT : ¬ C.passT t1.st) (hpS : ¬ C.passS s1)
    (hlt : C.mviewS s1 < R.S ∧ C.obS s1 < R.S) (hb : BufAtSpawn s lB) :
    HelloProtB R C pT lB tm t0 t1 s.mem s0 s1 ts [] sp :=
  ⟨helloProt_start hT (Nat.le_of_eq hS.symm) hpT hpS hlt, hS ▸ frzBufL_of_bufAt hb⟩

end Prot

/-! ## `kr_exit1` -/

/-- **`worker_done`'s facts for hello's kernel relation**: a relation whose
`atTexit` is wake's and whose `KR` is `KRH` (`kr_exit1 := krh_exit1`). -/
theorem texitFactsH {Q : WakeA64.WakeRel} {r0 r1 : Q.ι → Range} (hx : Q.atTexit = WakeW1.atTexit)
    (hKR : Q.KR = A64HelloWriteK.KRH r0 r1) : WakePost1.TexitFacts Q :=
  WakeW1.texitFacts hx fun w t s h _ => by
    rw [hKR] at h ⊢
    exact A64HelloWriteK.krh_exit1 w t s h

/-! ## Content facts at hello -/

/-- The buffer's words are below `2^64`. -/
theorem bufW_lt (i : Nat) : bufW i < 2 ^ 64 := by
  unfold bufW; split <;> decide

/-- **The buffer's 13 bytes are `"Hello, world\n"`**: byte `k` is lane
`k % 8` of word `k / 8`. -/
theorem bufBytes : (List.range 13).map (fun k => TermRun.laneN .w8 (bufW (k / 8)) (k % 8)) =
    [72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10] := by decide

/-- The bytes are the UTF-8 of `"Hello, world\n"`. -/
theorem bufBytes_utf8 : "Hello, world\n".toUTF8.toList.map (·.toNat) =
    [72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10] := by decide +kernel

/-- **rodata's lane words are the buffer's.** -/
theorem rodata_bufW :
    HelloRodataSrc.eW0 = .let_ "w0" (.asLanes false .w8 (.lit (bufW 0))) HelloRodataSrc.eO0 ∧
      HelloRodataSrc.eW1 = .let_ "w1" (.asLanes false .w8 (.lit (bufW 1))) HelloRodataSrc.eO1 :=
  ⟨rfl, rfl⟩

/-- **rodata's buffer has two elements**, enough for the 13 bytes. -/
theorem rodata_two : TermRun.numOf [TermRun.cst (.num 2)] = some 2 ∧ 13 ≤ 8 * 2 :=
  ⟨HelloRodataSrc.rdCN_newBuf.2.2.1, by decide⟩

end Spike.Lib.HelloInst

/-- info: 'Spike.Lib.HelloInst.frz_buf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloInst.frz_buf

/-- info: 'Spike.Lib.HelloInst.helloProtB_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloInst.helloProtB_start

/-- info: 'Spike.Lib.HelloInst.texitFactsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloInst.texitFactsH

/-- info: 'Spike.Lib.HelloInst.bufBytes' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.HelloInst.bufBytes
