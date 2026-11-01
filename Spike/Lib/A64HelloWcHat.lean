/-
**hello.w's `wc_main` from the box's store to main's state at the `clone`, the thread pointer kept** (AArch64): the
twin of `Spike/Lib/A64WakeWcHat.lean` at hello's `wc_main` (frame 144). `hello_wc_mid_segW`'s
segment, proved at `tpXa ms t` inside `NoMsrW W K`, is one inside `W` at `ms` keeping `TPIDR_EL0 = t`
(`SegW.keepTPN`); at its exit `wc_main`'s region's base is 144 above `sp`, which with main's stack and the thread
pointer's value is `ClonePostH` (`clonePostH_of`).

Unlike wake's `wc_mid_hat`, no region change is made here: hello's `ClonePostH` keeps `wcNSH` in `wc_main`'s region,
and `Hello.Parent.atJS_of_postH` (B4) reads main's parent node `JS` off it.

- `at_bXH_tpXa`: the box's landing at `ms` is at `tpXa ms t`;
- `wcNSH_base`: at the clone's `svc` in a region reaching `-144`, its base is `sp + 144`;
- `hello_wc_mid_hat`: a segment at `tpXa ms t` inside `NoMsrW W K` to the `svc`, with `TP t` at entry, ends inside
  `W` at `ms` at the `svc`, the base `sp + 144`, `TP t`;
- `hello_wc_mid_hatW`: the same from `hello_wc_mid_segW`'s premises (the node obligations `hW` and the callee `hti`
  at `tpXa ms t` inside `NoMsrW W K`);
- `clonePostH_of`: its exit, with main's stack (`sp + 224` stack 0's top) and `t = pinA + 8`, is `ClonePostH`.

Carried premises as in `A64HelloWcMid`.
-/
import Spike.Lib.A64HelloWcMid
import Spike.Lib.A64HelloClonePreHOf
import Spike.Lib.A64WakeWcHat

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (tiN tiX)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH wcNSH)
open Spike.Lib.A64.Flow.WakeWc (AGB MidG kOf tiQ okb_tpXa okb_of_tpXa stOk_tpXa tcbOkGA_tpXa resOkA_tpXa)
open Spike.Lib.A64.Rt (TcbOkGA hdrA RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.HelloPreA (ClonePostH)

/-- **The box's landing under `tpXa`**: a state at `bXH` under `ms` is at `bXH` under `tpXa ms t`. -/
theorem at_bXH_tpXa {ms : MemSide isaLSE2} {t : UInt64} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (h : At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH (tpXa ms t) (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_tpXa q.2⟩, h1, h2, h3⟩

/-- **At the clone's `svc` the region's base is `sp + 144`**: `wcNSH`'s offsets put `sp` at `-144`, an offset of
`R` (`R.lo ≤ -144`, `0 ≤ R.hi`). -/
theorem wcNSH_base {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (h : At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr) s c) :
    (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 := by
  obtain ⟨-, -, -, -, σ, hA, -, -⟩ := h
  have hsp : s.st.1.regs.SP.toBitVec = R.addr (-144) := by rw [hA.regs]; exact hA.so .SP _ rfl
  have hoff : R.Off (-144) := ⟨by decide, by omega, by omega⟩
  have := Region.addr_toNat hR hoff
  rw [← hsp] at this
  show (R.base.toNat : Int) = (s.st.1.regs.SP.toBitVec.toNat : Int) + 144
  omega

/-- **`wc_main` from the box's store to the `clone`, the thread pointer kept**: `hello_wc_mid_segW`'s segment, proved
at `tpXa ms t` inside `NoMsrW W K` (`h`), with the thread pointer `t` at entry, ends inside `W` under `ms` at a state
with `MidG`, `FrMGH` at its ghosts, at `wcNSH` (the source `c` itself), the base `sp + 144`, `TP t`
(`SegW.keepTPN`). -/
theorem hello_wc_mid_hat {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F₂ : MachineData → Prop} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (h : SegW (NoMsrW W K) K p lbl (tpXa ms t)
      (fun s c => ∃ l A, At exe endPc R F (bXH (tpXa ms t) (_root_.Executable.labels exe).label J1 l A) s c ∧
        Q l A c)
      (fun s c => ∃ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH (_root_.Executable.labels exe).label c0 (tH (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) sl me cA fr) s c)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c ∧ Q l A c) ∧
        TP t s)
      (fun s c => ∃ sl me cA fr, MidG S c cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH (_root_.Executable.labels exe).label c (tH (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) sl me cA fr) s c ∧
        (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 ∧ TP t s) := by
  refine ((SegW.keepTPN hK h).mono_pre fun _ _ ⟨⟨l, A, h, hQ⟩, ht⟩ =>
    ⟨⟨l, A, at_bXH_tpXa h, hQ⟩, ht⟩).mono_post ?_
  rintro s c ⟨⟨c0, sl, me, cA, fr, hM, hG, hA⟩, ht⟩
  have hb := wcNSH_base hR hlo hhi hA
  obtain rfl : c = c0 := let ⟨_, _, _, _, _, _, _, hc, _⟩ := hA; hc
  exact ⟨sl, me, cA, fr, hM, hG, hA, hb, ht⟩

/-- **`hello_wc_mid_segW` ending at main's state at the `clone`**: `hello_wc_mid_hat` of `hello_wc_mid_segW` at
`tpXa ms t`, its premises at `ms` but the node obligations (`hW`) and the callee (`hti`) at `tpXa ms t` inside
`NoMsrW W K` (`NodeW.noMsr`, `BlkW.noMsr`). -/
theorem hello_wc_mid_hatW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {tp : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -400) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcMidWH (NoMsrW W K) K exe endPc R F F₂ (tpXa ms tp) J1 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rARH R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2QH g c0))
      ((tcb2QH g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0))
    (htid : let t := tH (_root_.Executable.labels exe).label
      ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-144) (-192) 0).Off (k - -144) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ c0 sl me cA fr, MidG S c0 cA ∧ FrMGH J1 fr sl me →
      let t := tH (_root_.Executable.labels exe).label
      ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧
          (wcNIH (_root_.Executable.labels exe).label c0 t sl me cA fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (NoMsrW W K) K p lbl (tpXa ms tp)
          (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => (∃ l A, At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c ∧ Q l A c) ∧
        TP tp s)
      (fun s c => ∃ sl me cA fr, MidG S c cA ∧ FrMGH J1 fr sl me ∧
        At exe endPc R F₂ (wcNSH (_root_.Executable.labels exe).label c (tH (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) sl me cA fr) s c ∧
        (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 ∧ TP tp s) :=
  hello_wc_mid_hat hK hR (by omega) hhi (hello_wc_mid_segW (ms := tpXa ms tp) (W := NoMsrW W K)
    hp hend hF hR hal hlo hhi hF₂s hF₂ hW (fun q l A hQ => hfr ⟨q.1, okb_of_tpXa q.2⟩ l A hQ)
    (fun g => resOkA_tpXa (hres g)) (fun c0 g => stOk_tpXa (hhdr c0 g)) (fun c0 g => tcbOkGA_tpXa (htcb c0 g))
    htid hFK hKR hti)

/-- **The `clone` state is `ClonePostH`**: `hello_wc_mid_hat`'s exit (`wcNSH`, the base `sp + 144`, `TP t`) in
the layout `L`, with `R`'s base 16-aligned, main's `sp` 224 below stack 0's top (`hsp`: `scc_rt_main`'s 80 bytes and
`wc_main`'s 144) and the thread pointer `pinA + 8` (`ht`). -/
theorem clonePostH_of {L : RuntimeLayout} {endPc : Int64} {R : Region} {F₂ : MachineData → Prop} {t : UInt64}
    {s : State} {c : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (hal : R.base.toNat % 16 = 0)
    (hA : At L.exe endPc R F₂ (wcNSH (_root_.Executable.labels L.exe).label c
      (tH (_root_.Executable.labels L.exe).label) (kOf (_root_.Executable.labels L.exe).label) sl me cA fr) s c)
    (hb : (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144) (htp : TP t s)
    (hsp : s.st.1.regs.SP.toNat + 224 = L.stacksA.toNat + 16384) (ht : t.toBitVec = L.pinA + 0#64 + 8#64) :
    ClonePostH L endPc t s c :=
  ⟨R, F₂, _, _, sl, me, cA, fr, hal, hA, hb, hsp, congrArg UInt64.toBitVec htp, ht⟩

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.wcNSH_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.wcNSH_base

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_hat

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_hatW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_mid_hatW

/-- info: 'Spike.Lib.A64.Flow.HelloWc.clonePostH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.clonePostH_of
