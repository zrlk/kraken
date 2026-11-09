/-
**hello.w's `wc_main` from inside its box allocator just past the counter's add, the heap abort at `wXA`**
(x86-64; the twin of `Spike/Lib/A64HelloWcN4A.lean`, after `Spike/Lib/X64WakeWcN4.lean`'s `wake_wc_c2_segW`, with
the heap abort keeping `wc_main`'s spills as `Spike/Lib/X64HelloWcPreA.lean`'s `hello_wc_pre_segWA`): from a state
of `scc_rt_alloc`'s `c2` (just past the counter's `lock xadd`) of a box call from `wc_main` returning to
`.Lwc_main.x0`, in the allocator's region under `WcPreWH.alloc`'s frame condition, with `TP t`, to `wXA` with
`TP t`. The allocator's rest (`Alloc.seg_allocBW_at` at `c2`), its exits resumed in `wc_main`'s frame
(`seg_resumeW`, the caller known through `WcCtxH`; the spill slots `-48 … -16` are outside the allocator's region,
so `leave` keeps them), then `.x22` (`hello_wc_sp0_segW`), all at `tpXa ms t` inside `NoSetFsW (tpG t W) K`
(`hWp`, `hWs`), the thread pointer kept (`KeepTP.SegW.keepTP'`).

- `hello_wc_n4_segWA`: the statement.

## Differences from the AArch64 version

- The allocator's node just past the counter's add is `Alloc.AN.c2` (AArch64: `.n4`), and the allocator's segment
  from any node is `Alloc.seg_allocBW_at` (AArch64: `WakeWc.seg_allocB_ofW_at`).
- The box call returns to `.Lwc_main.x0` (AArch64: `.L22_wc_main.sp0`); the allocator's region is
  `wARH R = R.callee (-144) (-160) 8` with `CallerCells R (-144) (-160) 8` (AArch64: `… 0`), so `8 ≤ R.hi` and
  there is no alignment premise (AArch64: `hal`, `0 ≤ R.hi`).
- The spills are at `-16 … -48` (AArch64: `-144 … -112`); `wc_main`'s return exit `wXH .x18` takes the region `R`
  (`%rbp` at `R.addr (-8)`), and its call node keeps the return address and the saved `%rbp` (`0`, `-8`).
- The box's landing (`hxa`) is on `R.fp (-8)`, the frame based at the saved `%rbp`; the thread pointer is
  `fsBase`, the segment inside `NoSetFsW (tpG t W) K`, kept by `KeepTP.SegW.keepTP'` (AArch64: `TPIDR_EL0`,
  `NoMsrW`, `SegW.keepTPN'`).
-/
import Spike.Lib.X64HelloWcPreA
import Spike.Lib.X64WakeWcN4
import Spike.Lib.X64HelloLand3

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64.Flow.WakeWc (AGB BoxW WX okb_tpXa okb_of_tpXa)
open Spike.Lib.X64.Flow.HelloRd (hello_alloc)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG)

section N4

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {q : Call}

/-- **`wc_main` from its box allocator's `c2` is one segment inside `W`, the thread pointer kept, the heap abort at
`wXA`** (module doc): from a state of the allocator's `c2` for a box call `q` returning to `.Lwc_main.x0` (`hq`,
`hra`), in the allocator's region under `WcPreWH.alloc`'s frame condition, with `TP t`, to `wXA` with `TP t`. The
box's landing is the `xa` exit (`hxa`). The other premises are `hello_wc_entry_segWA`'s, `hmem` at the call `q`. -/
theorem hello_wc_n4_segWA {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop}
    (hWp : WcPreWH (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J1)
    (hWs : WcSp0WH (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J1)
    (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hra : q.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x0").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none →
      At exe endPc (R.fp (-8)) F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms
      (fun s c => At exe endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧
          WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m)
        (Alloc.N (_root_.Executable.labels exe).label ms q .c2) s c ∧ TP t s)
      (fun s c => At exe endPc R F (wXA ms (_root_.Executable.labels exe).label J1) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hqt : q.OKB (tpXa ms t) lab := okb_tpXa hq
  have hR' : (wARH R).OK := Region.callee_ok hR (by show R.lo ≤ -144 + -160; omega) (by decide)
    (by show (-144 : Int) < R.hi; omega) (by show (-144 : Int) + 8 ≤ R.hi; omega)
  -- the allocator's rest from `c2`
  have hA := Alloc.seg_allocBW_at (p := p) (lbl := lbl) hp hend hello_alloc
    (Spike.Lib.X64.HelloPh.Land.fstable_wARH (ms := tpXa ms t) (lab := lab) (J0 := J0) (J1 := J1) (q := q) hR hF
      hlo hhi)
    hR' (by simp [Region.callee]) (by simp [Region.callee]) hqt (fun a ha m hm => hmem a ha m hm.1)
    (hWp.alloc q hqt hra) .c2
  -- its exits resumed in `wc_main`'s frame
  have hres := seg_resumeW (N := fun e : Empty => e.elim) (E := wXHA (tpXa ms t) lab R J1) (F₂ := F)
    (M := fun _ => True)
    (PC := fun σC => ∃ c, (wNH lab R J0 J1 .call).J σC c ∧ (Alloc.N lab (tpXa ms t) q .e).J (enter (-144) σC) c)
    (hA.mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
    (fun m ⟨h1, _, mC, σC', c', hA', hJ1, hJ2, hK'⟩ => ⟨h1, mC, σC', ⟨-144, []⟩, hK', hA', c', hJ1, hJ2⟩)
    (fun _ h _ => h) ?_
  · have hsp0 := hello_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoSetFsW (tpG t W) K)
      (Q := fun _ _ => False) hp hend hF hR (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
      (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
      (fun l A s c hl h ht => hxa l A s c hl (at_bXH_of_tpXa h) ht)
    have hin := (hres.mono_post (Q' := fun s c => At exe endPc R F (wXH (tpXa ms t) lab R J1 .x18) s c ∨
      At exe endPc R F (wXA (tpXa ms t) lab J1) s c) fun s c h => by
        rcases h with ⟨e, -⟩ | ⟨y, h⟩
        · exact e.elim
        · cases y
          · exact .inl h
          · exact .inr h).seq_left hsp0
    refine ((KeepTP.SegW.keepTP' hK hin (fun _ _ hw => hw.2.1) (fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim)
      fun _ _ hw ht => hw.1 ht).mono_pre fun s c h => h).mono_post ?_
    rintro s c ⟨h | h, ht⟩
    · exact h.elim
    · exact ⟨at_wXA_of_tpXa h, ht⟩
  -- the allocator's exits land at `wc_main`'s, the spills kept
  rintro x σx c' σC hx ⟨c, ⟨⟨σe, hJe, h0', h8, h16, h24, h32, h40, h48⟩, hb, -, -, -, -⟩, ⟨hc, hfp, -⟩⟩
  have hsl : ∀ k, ¬ (wARH R).Off (k - -144) → (leave (wARH R) (-144) σC σx).slot k = σC.slot k :=
    fun k hn => by simp only [leave]; exact ite_eq_right hn
  have hk : ∀ k : Int, -48 ≤ k → k ≤ 0 → (leave (wARH R) (-144) σC σx).slot k = σC.slot k := fun k h1 h2 =>
    hsl k (by simp only [Region.Off, Region.callee]; omega)
  cases x
  · have hx' := hx
    simp only [Alloc.EB] at hx'
    obtain ⟨o, -, -, -, -, hbx⟩ := hx'
    refine .inr ⟨WX.x18, ?_, by show SO.le ⟨-136, []⟩ ⟨-144 + 8, []⟩ = true; decide, ⟨q, hqt⟩,
      ⟨σe, hc ▸ hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · show lab ".Lwc_main.x0" = Int64.ofBitVec q.ra
      rw [hra, int64_ofBitVec_toBitVec]
    · exact (hk 0 (by decide) (by decide)).trans h0'
    · exact (hk (-8) (by decide) (by decide)).trans h8
    · exact (hk (-16) (by decide) (by decide)).trans h16
    · exact (hk (-24) (by decide) (by decide)).trans h24
    · exact (hk (-32) (by decide) (by decide)).trans h32
    · exact (hk (-40) (by decide) (by decide)).trans h40
    · exact (hk (-48) (by decide) (by decide)).trans h48
    · rw [← hb]
      simp only [Reg64s.get64]
      rw [show (leave (wARH R) (-144) σC σx).regs = σx.regs from rfl, hbx, ← hfp]; rfl
    · exact hx
  · obtain ⟨h2, hfull, hs⟩ := hx
    refine .inr ⟨WX.abort, rfl, by show SO.le ⟨-304, []⟩ ⟨-144 + -160, []⟩ = true; decide, h2, ?_,
      ⟨q, hqt⟩, hfull, σe, hc ▸ hJe, (hk (-16) (by decide) (by decide)).trans h16,
      (hk (-24) (by decide) (by decide)).trans h24, (hk (-32) (by decide) (by decide)).trans h32,
      (hk (-40) (by decide) (by decide)).trans h40, (hk (-48) (by decide) (by decide)).trans h48⟩
    show (leave (wARH R) (-144) σC σx).slot (-304) = _
    simp only [leave]
    rw [ite_eq_left (by simp only [Region.Off, Region.callee]; omega)]
    exact hs

end N4

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_n4_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_n4_segWA
