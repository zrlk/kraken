/-
**wake.w's `wc_main` at its `clone`'s `svc` as main's parent node**
(AArch64, the pre-spawn consumer; `spawn_R`'s `hMainR`): the end of
`wake_wc_mid_segW` in the form `A64WakeMainClosedWS.main_closed_ws` asks
of main's state at the clone (`hat`, `hRb`), with the thread pointer kept
across the segment (`SegW.keepTP`).

- `takeK_tp`: a stack take keeps the thread pointer;
- `SegW.keepTPA`: `KeepTP.SegW.keepTP` for a segment inside `W` at cells
  other than an `MSR`, under an outside move that keeps the thread pointer;
- `upAS`, `wc_mid_hat`: a state at `wcNS` (a callee's region, `hi ≤ 0`, the
  caller's two cells above it mapped) is at `WakePreA.cloneAt` in main's
  frame (`WakeParent.oP`, offsets `[-96, 16)` of the same base) with
  `WakeParent.JS` at its own control, the box's word, the saved pair and the
  thread pointer, the base `sp + 80`;
- `stOk_tpXa`, `tcbOkGA_tpXa`, `resOkA_tpXa`, `okb_tpXa`/`okb_of_tpXa`,
  `at_bX_tpXa`: the
  segment's premises and its entry at `ms` hold at `tpXa ms t`;
- `wake_wc_mid_hatW`: the same from `wake_wc_mid_segW`'s premises;
- `wake_wc_mid_hat`: `wake_wc_mid_segW`'s segment (at `tpXa ms t`, inside
  `NoMsrW W K`) with the thread pointer `t` at entry
  ends at `wc_mid_hat`'s node.

Every fact at the end is about the machine state (and the ghosts `MidG`,
`FrG`, `FrMG`); none mentions the placement `lbl`. The landing is guarded by
the instance's `Q l A`, `hfr` asked only under it.
-/
import Spike.Lib.A64WakeWcMid
import Spike.Lib.A64WakeParent
import Spike.Lib.A64Hello1RodataTP

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.WcSp4 (FrW wcNS wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW tcb2Q)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX)
open Spike.Lib.A64.Rt (TcbOkGA hdrA)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (NoMsrAt TP tpXa)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)

/-- **A stack take keeps the thread pointer**: it moves only memory and
the pc. -/
theorem takeK_tp {a : Int64} {rS : Scc.Sem.Range} {s s' : State} {t : UInt64} (h : Ret0.TakeK a rS s s')
    (hs : TP t s) : TP t s' := by
  obtain ⟨pm, he⟩ := h.mem
  show s'.st.1.regs.TPIDR_EL0 = t
  rw [he]; exact hs

/-- **A segment at cells other than an `MSR` keeps the thread pointer**
(`KeepTP.SegW.keepTP`): inside `W ∧ NoMsrAt`, at `tpXa ms t`, under an
outside move keeping the thread pointer (`hKt`), the segment with `TP t`
conjoined, inside `W`. -/
theorem SegW.keepTPA {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P Q : Frag isaLSE2} {t : UInt64}
    (hK : ms.K = some Scc.Sem.A64.abi) (h : SegW (fun s c => W s c ∧ NoMsrAt s) K p lbl (tpXa ms t) P Q)
    (hKt : ∀ s s', K s s' → TP t s → TP t s') :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) :=
  (Spike.Lib.A64.KeepTP.SegW.keepTP hK h (fun _ _ hw => hw.2) fun s _ _ s' hk => hKt s s' hk).mono_W
    fun _ _ hw => hw.1

/-! ## `tpXa` changes only `xa`

`SegW.keepTP` asks the segment at `tpXa ms t`; the premises the segment's
lemmas take at `ms` hold at `tpXa ms t` (none of them mentions `xa`). -/

theorem stOk_tpXa {ms : MemSide isaLSE2} {t : UInt64} {F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {a v : BitVec 64} (h : Ret0.StOk ms F exe endPc a v) : Ret0.StOk (tpXa ms t) F exe endPc a v :=
  { h with }

theorem tcbOkGA_tpXa {ms : MemSide isaLSE2} {t : UInt64} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : Spike.Lib.A64.Rt.TcbGG} (h : Spike.Lib.A64.Rt.TcbOkGA ms F0 exe endPc R F q) :
    Spike.Lib.A64.Rt.TcbOkGA (tpXa ms t) F0 exe endPc R F q :=
  ⟨stOk_tpXa h.next, h.own⟩

theorem resOkA_tpXa {ms : MemSide isaLSE2} {t : UInt64} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : Spike.Lib.A64.Rt.Reserve.ResG}
    (h : Spike.Lib.A64.Rt.Reserve.ResOkA ms F0 exe endPc R F q) :
    Spike.Lib.A64.Rt.Reserve.ResOkA (tpXa ms t) F0 exe endPc R F q :=
  ⟨stOk_tpXa h.next, h.own⟩

theorem okb_tpXa {ms : MemSide isaLSE2} {t : UInt64} {lab : Label → Int64} {q : Spike.Lib.A64.Alloc.Call}
    (h : q.OKB ms lab) : q.OKB (tpXa ms t) lab :=
  { h with toS := { h.toS with } }

theorem okb_of_tpXa {ms : MemSide isaLSE2} {t : UInt64} {lab : Label → Int64} {q : Spike.Lib.A64.Alloc.Call}
    (h : q.OKB (tpXa ms t) lab) : q.OKB ms lab :=
  { h with toS := { h.toS with } }

/-- **The box's landing under `tpXa`**: a state at `bX` under `ms` is at
`bX` under `tpXa ms t`. -/
theorem at_bX_tpXa {ms : MemSide isaLSE2} {t : UInt64} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (h : At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX (tpXa ms t) (_root_.Executable.labels exe).label J0 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_tpXa q.2⟩, h1, h2, h3⟩

/-- **The abstract state with the cells at offsets `0 ≤ k` read from `m`**
(at `R`'s base): `σ`'s registers, flags and cells below `0`. -/
def upAS (R : Region) (m : MachineData) (σ : AS) : AS :=
  { σ with slot := fun k => if 0 ≤ k then
      match Mem.loadInt m.dmem (R.addr k) 8 with
      | some j => BitVec.ofInt 64 j
      | none => 0
    else σ.slot k }

/-- **A state at the clone's `svc` is main's parent node**: at `wcNS` in a
region `R` reaching `[-96, 0)` (the callee's, `hi ≤ 0`), with the two cells
above the base mapped (`hup`, the caller's, kept: `CKept`) and room for them
(`hfit`), with thread pointer `tp`, it is at `cloneAt` in the region of the
same base and offsets `[-96, 16)` (`OK`), at `WakeParent.oP` with
`JS c cA fr.1 fr.2 tp` (`c` its control, `c = c0`), and `R`'s base is
`sp + 80`. -/
theorem wc_mid_hat {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl} {tp : UInt64}
    (hR : R.OK) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) (hfit : (R.base.toNat : Int) + 16 ≤ 2 ^ 64)
    (hup : ∀ k : Int, k % 8 = 0 → 0 ≤ k → k < 16 → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome)
    (h : At exe endPc R F (wcNS (_root_.Executable.labels exe).label c0 t k cA m fr) s c) (htp : TP tp s) :
    c = c0 ∧ (⟨R.base, -96, 16⟩ : Region).OK ∧
      At exe endPc ⟨R.base, -96, 16⟩ F
        ⟨Spike.Lib.WakePreA.cloneAt pfxM exe, oP, JS c cA fr.1 fr.2 tp.toBitVec⟩ s c ∧
      (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 80 := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hc, -, -, -, -, -, -, -, -, h72, -, h16, h8⟩ := h
  have hsp : s.st.1.regs.SP.toBitVec = R.addr (-80) := by rw [hA.regs]; exact hA.so .SP _ rfl
  have hoff : R.Off (-80) := ⟨by decide, by omega, by omega⟩
  have hR1 := hR.lo
  refine ⟨hc, ⟨by simp only; omega, by simp only; omega⟩, ⟨he, hn, hdc, hpc, upAS R s.st.1 σ,
    ⟨hA.regs, hA.status, hA.so, fun k hk => ?_⟩, hD, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hk
    simp only at h2 h3
    show ∃ j, Mem.loadInt s.st.1.dmem (R.addr k) 8 = some j ∧ BitVec.ofInt 64 j = (upAS R s.st.1 σ).slot k
    by_cases h0 : 0 ≤ k
    · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hup k h1 h0 (by omega))
      exact ⟨j, hj, by simp only [upAS, if_pos h0, hj]⟩
    · simp only [upAS, if_neg h0]
      exact hA.slot k ⟨h1, by omega, by omega⟩
  · simp only [upAS, show ¬ (0 : Int) ≤ -72 from by decide, if_false]; exact h72
  · simp only [upAS, show ¬ (0 : Int) ≤ -16 from by decide, if_false]; exact h16
  · simp only [upAS, show ¬ (0 : Int) ≤ -8 from by decide, if_false]; exact h8
  · show (upAS R s.st.1 σ).regs.TPIDR_EL0.toBitVec = tp.toBitVec
    simp only [upAS]; rw [← hA.regs]; exact congrArg UInt64.toBitVec htp
  · have := Region.addr_toNat hR hoff
    rw [← hsp] at this
    show (R.base.toNat : Int) = (s.st.1.regs.SP.toBitVec.toNat : Int) + 80
    omega

/-- **`wc_main` from the box's store to main's parent node at the
`clone`**: `wake_wc_mid_segW`'s segment, proved at `tpXa ms t` inside `W`
at cells other than an `MSR`, not moved by `K` (`NoMsrW W K`, `h`), with
the thread pointer `t` at entry, ends, inside `W` under `ms`, at a state
with `MidG`, `FrG`, `FrMG` at its ghosts, at `wcNS` (for `wcNS_clone`) and at
`wc_mid_hat`'s node, the base `sp + 80` (`SegW.keepTPN`). -/
theorem wake_wc_mid_hat {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F₂ : MachineData → Prop} {J0 : AS → Ctl → Prop} {S : WeakMem.AllocLabel → Nat → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {t : UInt64}
    (hK : ms.K = some Scc.Sem.A64.abi) (hR : R.OK) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi)
    (hfit : (R.base.toNat : Int) + 16 ≤ 2 ^ 64)
    (hup : ∀ m, F₂ m → ∀ k : Int, k % 8 = 0 → 0 ≤ k → k < 16 → (Mem.loadInt m.dmem (R.addr k) 8).isSome)
    (h : SegW (NoMsrW W K) K p lbl (tpXa ms t)
      (fun s c => ∃ l A, At exe endPc R F (bX (tpXa ms t) (_root_.Executable.labels exe).label J0 l A) s c ∧
        Q l A c)
      (fun s c => ∃ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) cA m fr) s c)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c) ∧
        TP t s)
      (fun s c => ∃ cA m fr, MidG S c cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c (t2 (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) cA m fr) s c ∧
        (⟨R.base, -96, 16⟩ : Region).OK ∧ At exe endPc ⟨R.base, -96, 16⟩ F₂
          ⟨Spike.Lib.WakePreA.cloneAt pfxM exe, oP, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
        (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 80 ∧ TP t s) := by
  refine ((SegW.keepTPN hK h).mono_pre fun _ _ ⟨⟨l, A, h, hQ⟩, ht⟩ =>
    ⟨⟨l, A, at_bX_tpXa h, hQ⟩, ht⟩).mono_post ?_
  rintro s c ⟨⟨c0, cA, m, fr, hM, hG, hGm, hA⟩, ht⟩
  have hD : F₂ s.st.1 := let ⟨_, _, _, _, _, _, hD, _⟩ := hA; hD
  obtain ⟨rfl, hok, hat, hb⟩ := wc_mid_hat hR hlo hhi hfit (hup _ hD) hA ht
  exact ⟨cA, m, fr, hM, hG, hGm, hA, hok, hat, hb, ht⟩

/-- **`wake_wc_mid_segW` ending at main's parent node** (`spawn_R`'s
`hMainR`): `wake_wc_mid_hat` of `wake_wc_mid_segW` at `tpXa ms t`, its
premises at `ms` but the node obligations (`hW`) and the callee (`hti`) at
`tpXa ms t` inside `NoMsrW W K` (`NodeW.noMsr`, `BlkW.noMsr`: every node
obligation already has `K` not moving it). -/
theorem wake_wc_mid_hatW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hfit : (R.base.toNat : Int) + 16 ≤ 2 ^ 64)
    (hup : ∀ m, F₂ m → ∀ k : Int, k % 8 = 0 → 0 ≤ k → k < 16 → (Mem.loadInt m.dmem (R.addr k) 8).isSome)
    (hW : WcMidW (NoMsrW W K) K exe endPc R F F₂ (tpXa ms t) J0 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-80) (-192) 0) F (tcb2Q g c0))
    (htid : ms.rt (t2 (_root_.Executable.labels exe).label + 56#64).toNat ∧
      ms.mp ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ true ∧
      ms.G ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (_root_.Executable.labels exe).label + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-192) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
      R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-80) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J
            σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-80) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧
          (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-80) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (NoMsrW W K) K p lbl (tpXa ms t)
          (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) x) s c ∧ M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c) ∧
        TP t s)
      (fun s c => ∃ cA m fr, MidG S c cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c (t2 (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) cA m fr) s c ∧
        (⟨R.base, -96, 16⟩ : Region).OK ∧ At exe endPc ⟨R.base, -96, 16⟩ F₂
          ⟨Spike.Lib.WakePreA.cloneAt pfxM exe, oP, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
        (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 80 ∧ TP t s) :=
  wake_wc_mid_hat hK hR (by omega) hhi hfit hup (wake_wc_mid_segW (ms := tpXa ms t) (W := NoMsrW W K)
    hp hend hF hR hal hlo hhi hF₂s hF₂ hW (fun q l A hQ => hfr ⟨q.1, okb_of_tpXa q.2⟩ l A hQ)
    (fun g => resOkA_tpXa (hres g)) (fun c0 g => stOk_tpXa (hhdr c0 g)) (fun c0 g => tcbOkGA_tpXa (htcb c0 g))
    htid hFK hKR hti)

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.takeK_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.takeK_tp

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wc_mid_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wc_mid_hat

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_hat

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_hatW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_hatW
