/-
**wake.w's `wc_main` at its `clone`'s `syscall` as main's parent node**
(x86-64; twin of `Spike/Lib/A64WakeWcHat.lean`): the end of
`wake_wc_mid_segW` in the form `X64WakeSpawnAt.parent_at_pre` asks of
main's state at the clone (`hat`, `hRb`), with the thread pointer (`%fs`
base) kept across the segment (`SegW.keepTPN`).

- `takeK_tp`: a stack take keeps the thread pointer;
- `SegW.keepTPA`: `KeepTP.SegW.keepTP` for a segment inside `W` at cells
  other than an `arch_prctl`, under an outside move that keeps the thread
  pointer;
- `wc_mid_hat`: a state at `wcNS` (in a region reaching `[-64, 16)`) is at
  `WakePreA.cloneAt` in main's frame (`WcClone.oW`, offsets `[-64, 16)` of
  the same base) with `WakePh.Parent.JS` at its own control, the box's word,
  the saved pair and the thread pointer, the base `%rsp + 64`;
- `stOk_tpXa`, `tcbOkGA_tpXa`, `resOkA_tpXa`, `okb_tpXa`/`okb_of_tpXa`,
  `at_bX_tpXa`: the segment's premises and its entry at `ms` hold at
  `tpXa ms t`;
- `wake_wc_mid_hat`: `wake_wc_mid_segW`'s segment (at `tpXa ms t`, inside
  `NoSetFsW W K`) with the thread pointer `t` at entry ends at
  `wc_mid_hat`'s node;
- `wake_wc_mid_hatW`: the same from `wake_wc_mid_segW`'s premises.

**Where this differs from AArch64**: `wc_main`'s region on x86-64 already
holds the saved `%rbp` and the return address (`wake_wc_mid_segW`'s
`16 ≤ R.hi`: the `call` pushed them above the base), so the parent's region
`[-64, 16)` is a sub-region of `R` and A64's `upAS` (re-reading the cells
above a callee's region), `hfit` and `hup` have no counterpart. The thread
pointer is `fsBase`, kept by every instruction but `arch_prctl`
(`X64KeepTP`), so `NoMsrW` is `NoSetFsW`. The exit's control is the
published `boxPubCtl c0 ty l` (`wake_wc_mid_segW`'s), stated as an equation.
-/
import Spike.Lib.X64WakeWcMid
import Spike.Lib.X64WakeParent
import Spike.Lib.X64WakePreA
import Spike.Lib.X64KeepTPW

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Tcb2Call (oC tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk)
open Spike.Lib.X64.Rt (TcbOkGA hdrA)
open Spike.Lib.X64.Rt.Reserve (ResOkA)
open Spike.Lib.X64WakeBoxDefs (boxTerm boxPubCtl)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt)
open Scc.Cert.Rt.X64 (Lays endOf)

/-- **A stack take keeps the thread pointer**: it moves only memory and
the pc. -/
theorem takeK_tp {a : Int64} {rS : Scc.Sem.Range} {s s' : State} {t : UInt64} (h : Ret0.TakeK a rS s s')
    (hs : TP t s) : TP t s' := by
  obtain ⟨pm, he⟩ := h.mem
  show s'.st.1.regs.fsBase = t
  rw [he]; exact hs

/-- **A segment at cells other than an `arch_prctl` keeps the thread
pointer** (`KeepTP.SegW.keepTP`): inside `W ∧ NoSetFsAt`, at `tpXa ms t`,
under an outside move keeping the thread pointer (`hKt`), the segment with
`TP t` conjoined, inside `W`. -/
theorem SegW.keepTPA {W : Frag isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {P Q : Frag isa} {t : UInt64}
    (hK : ms.K = some Scc.Sem.X64.abi) (h : SegW (fun s c => W s c ∧ NoSetFsAt s) K p lbl (tpXa ms t) P Q)
    (hKt : ∀ s s', K s s' → TP t s → TP t s') :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) :=
  (Spike.Lib.X64.KeepTP.SegW.keepTP hK h (fun _ _ hw => hw.2) fun s _ _ s' hk => hKt s s' hk).mono_W
    fun _ _ hw => hw.1

/-! ## `tpXa` changes only `xa`

`SegW.keepTPN` asks the segment at `tpXa ms t`; the premises the segment's
lemmas take at `ms` hold at `tpXa ms t` (none of them mentions `xa`). -/

theorem stOk_tpXa {ms : MemSide isa} {t : UInt64} {F : MachineData → Prop} {a v : BitVec 64}
    (h : StOk ms F a v) : StOk (tpXa ms t) F a v :=
  { h with }

theorem tcbOkGA_tpXa {ms : MemSide isa} {t : UInt64} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : Spike.Lib.X64.Rt.TcbGG} (h : TcbOkGA ms F0 exe endPc R F q) :
    TcbOkGA (tpXa ms t) F0 exe endPc R F q :=
  ⟨stOk_tpXa h.next, h.own⟩

theorem resOkA_tpXa {ms : MemSide isa} {t : UInt64} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : Spike.Lib.X64.Rt.Reserve.ResG} (h : ResOkA ms F0 exe endPc R F q) :
    ResOkA (tpXa ms t) F0 exe endPc R F q :=
  ⟨stOk_tpXa h.next, h.own⟩

theorem okb_tpXa {ms : MemSide isa} {t : UInt64} {lab : Label → Int64} {q : Spike.Lib.X64.Alloc.Call}
    (h : q.OKB ms lab) : q.OKB (tpXa ms t) lab :=
  { h with toS := { h.toS with } }

theorem okb_of_tpXa {ms : MemSide isa} {t : UInt64} {lab : Label → Int64} {q : Spike.Lib.X64.Alloc.Call}
    (h : q.OKB (tpXa ms t) lab) : q.OKB ms lab :=
  { h with toS := { h.toS with } }

/-- **The box's landing under `tpXa`**: a state at `bX` under `ms` is at
`bX` under `tpXa ms t`. -/
theorem at_bX_tpXa {ms : MemSide isa} {t : UInt64} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (h : At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX (tpXa ms t) (_root_.Executable.labels exe).label J0 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_tpXa q.2⟩, h1, h2, h3⟩

/-- **A state at the clone's `syscall` is main's parent node**: at `wcNS`
in a region `R` reaching `[-64, 16)`, with thread pointer `tp`, it is at
`cloneAt` in the region of the same base and offsets `[-64, 16)` (`OK`),
at `WcClone.oW` with `JS c cA fr.1 fr.2 tp` (`c` its control, `c = c0`),
and `R`'s base is `%rsp + 64`. -/
theorem wc_mid_hat {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl} {tp : UInt64}
    (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi)
    (h : At exe endPc R F (wcNS (_root_.Executable.labels exe).label c0 t k cA m fr) s c) (htp : TP tp s) :
    c = c0 ∧ (⟨R.base, -64, 16⟩ : Region).OK ∧
      At exe endPc ⟨R.base, -64, 16⟩ F ⟨cloneAt exe, oW, JS c cA fr.1 fr.2 tp.toBitVec⟩ s c ∧
      (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64 := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨⟨hc, -, -, h16, -, -, h0, h8⟩, -⟩, -⟩ := h
  have hsp : σ.regs.get64 .rsp = R.addr (-64) := hA.so .rsp (-64) (by simp [SO.get, wcNS])
  have hR1 := hR.lo
  have hR2 := hR.hi
  refine ⟨hc, ⟨by simp only; omega, by simp only; omega⟩, ⟨he, hn, hdc, hpc, σ,
    ⟨hA.regs, hA.zmms, hA.status, hA.so, fun k hk => hA.slot k ⟨hk.1, by have := hk.2.1; simp only at this; omega,
      by have := hk.2.2; simp only at this; omega⟩⟩, hD, rfl, h16, h0, h8, ?_⟩, ?_⟩
  · show σ.regs.fsBase.toBitVec = tp.toBitVec
    rw [← hA.regs]; exact congrArg UInt64.toBitVec htp
  · have := Region.addr_toNat_of hR hlo (by omega : (-64 : Int) < R.hi)
    rw [hA.regs, hsp]
    omega

/-- **`wc_main` from the box's store to main's parent node at the
`clone`**: `wake_wc_mid_segW`'s segment, proved at `tpXa ms t` inside `W`
at cells other than an `arch_prctl`, not moved by `K` (`NoSetFsW W K`,
`h`), with the thread pointer `t` at entry, ends, inside `W` under `ms`, at
a state at the published control with `MidPG`, `FrG`, `FrMG` at its
ghosts, at `wcNS` and at `wc_mid_hat`'s node, the base `%rsp + 64`
(`SegW.keepTPN`). -/
theorem wake_wc_mid_hat {W : Frag isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F₂ : MachineData → Prop} {J0 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {t : UInt64}
    (hK : ms.K = some Scc.Sem.X64.abi) (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi)
    (h : SegW (NoSetFsW W K) K p lbl (tpXa ms t)
      (fun s c => ∃ l A, At exe endPc R F (bX (tpXa ms t) (_root_.Executable.labels exe).label J0 l A) s c ∧
        Q l A c)
      (fun s c => ∃ c0 ty l cA m fr, MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label (boxPubCtl c0 ty l)
          (t2 (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label) cA m fr) s c)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c) ∧
        TP t s)
      (fun s c => ∃ c0 ty l cA m fr, c = boxPubCtl c0 ty l ∧ MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c
          (t2 (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label) cA m fr) s c ∧
        (⟨R.base, -64, 16⟩ : Region).OK ∧
        At exe endPc ⟨R.base, -64, 16⟩ F₂ ⟨cloneAt exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
        (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64 ∧ TP t s) := by
  refine ((SegW.keepTPN hK h).mono_pre fun _ _ ⟨⟨l, A, h, hQ⟩, ht⟩ =>
    ⟨⟨l, A, at_bX_tpXa h, hQ⟩, ht⟩).mono_post ?_
  rintro s c ⟨⟨c0, ty, l, cA, m, fr, hM, hG, hGm, hA⟩, ht⟩
  obtain ⟨rfl, hok, hat, hb⟩ := wc_mid_hat hR hlo hhi hA ht
  exact ⟨c0, ty, l, cA, m, fr, rfl, hM, hG, hGm, hA, hok, hat, hb, ht⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wake_wc_mid_segW` ending at main's parent node** (the parent's
`hat`/`hRb`): `wake_wc_mid_hat` of `wake_wc_mid_segW` at `tpXa ms t`, its
premises at `ms` but the node obligations (`hW`) and the callee (`hti`) at
`tpXa ms t` inside `NoSetFsW W K` (`NodeW.noSetFs`, `BlkW.noSetFs`). -/
theorem wake_wc_mid_hatW {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcMidW (NoSetFsW W K) K exe endPc R F F₂ (tpXa ms t) J0 Q)
    (hpub : ∀ l A c, Q l A c → c.term = boxTerm ∧ c.hold = none ∧
      ∃ ty, TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hP : ms.pub)
    (hres : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, StOk ms F (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-72) (-184) 8) F (tcb2Q g c0))
    (htid : ms.rt (t2 (_root_.Executable.labels exe).label + 56#64).toNat ∧
      ms.mp ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ true ∧
      ms.G ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (_root_.Executable.labels exe).label + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-184) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
      R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J
            σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧
          (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (NoSetFsW W K) K p lbl (tpXa ms t)
          (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) x) s c ∧ M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c) ∧
        TP t s)
      (fun s c => ∃ c0 ty l cA m fr, c = boxPubCtl c0 ty l ∧ MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c
          (t2 (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label) cA m fr) s c ∧
        (⟨R.base, -64, 16⟩ : Region).OK ∧
        At exe endPc ⟨R.base, -64, 16⟩ F₂ ⟨cloneAt exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
        (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64 ∧ TP t s) :=
  wake_wc_mid_hat hK hR (by omega) hhi (wake_wc_mid_segW (ms := tpXa ms t) (W := NoSetFsW W K)
    hp hend hF hR hlo hhi hF₂s hF₂ hW hpub hP
    (fun g => resOkA_tpXa (hres g)) (fun c0 g => stOk_tpXa (hhdr c0 g)) (fun c0 g => tcbOkGA_tpXa (htcb c0 g))
    htid hFK hKR hti)

end Seg

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.takeK_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.takeK_tp

/-- info: 'Spike.Lib.X64.Flow.WakeWc.SegW.keepTPA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.SegW.keepTPA

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wc_mid_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wc_mid_hat

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_hat

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_hatW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_hatW
