/-
**hello.w's `wc_main` from inside its box allocator's `n4`, the heap abort at `wXA`** (AArch64, row H2-U-hM; the
twin of `Spike/Lib/A64WakeWcN4.lean`'s `wake_wc_n4_segW`, with the heap abort keeping `wc_main`'s spills as
`Spike/Lib/A64HelloWcPreA.lean`'s `hello_wc_pre_segWA`): from a state of `scc_rt_alloc`'s `n4` (just past the
counter's add) of a box call from `wc_main` returning to `.sp0`, in the allocator's region under `WcPreWH.alloc`'s
frame condition, with `TP t`, to `wXA` with `TP t`. The allocator's rest (`WakeWc.seg_allocB_ofW_at` at `n4`), its
exits resumed in `wc_main`'s frame (`seg_resumeW`, the caller known through `WcCtxH`; the spill slots `-144 … -112`
are outside the allocator's region, so `leave` keeps them), then `.sp0` (`hello_wc_sp0_segW`), all at `tpXa ms t`
inside `NoMsrW (tpG t W) K` (`hWp`, `hWs`), the thread pointer kept (`SegW.keepTPN'`).

- `hello_wc_n4_segWA`: the statement.
-/
import Spike.Lib.A64HelloWcPreA
import Spike.Lib.A64WakeWcN4
import Spike.Lib.A64HelloLand3
import Spike.Lib.A64HelloWcPreG

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.Flow.WakeWc (AGB BoxW tpG okb_tpXa okb_of_tpXa seg_allocB_ofW_at WX)
open Spike.Lib.A64.Flow.HelloRd (hello_alloc)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (TP tpXa)

section N4

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {q : Call}

/-- **`wc_main` from its box allocator's `n4` is one segment inside `W`, the thread pointer kept, the heap abort at
`wXA`** (module doc): from a state of the allocator's `n4` for a box call `q` returning to `.sp0` (`hq`, `hra`), in
the allocator's region under `WcPreWH.alloc`'s frame condition, with `TP t`, to `wXA` with `TP t`. The box's
landing is the `xa` exit (`hxa`). The other premises are `hello_wc_entry_segWA`'s, `hmem` at the call `q`. -/
theorem hello_wc_n4_segWA {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop}
    (hWp : WcPreWH (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J1)
    (hWs : WcSp0WH (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J1)
    (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hra : q.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp0").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms
      (fun s c => At exe endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧
          WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m)
        (Alloc.N (_root_.Executable.labels exe).label ms q .n4) s c ∧ TP t s)
      (fun s c => At exe endPc R F (wXA ms (_root_.Executable.labels exe).label J1) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hqt : q.OKB (tpXa ms t) lab := okb_tpXa hq
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.HelloPh.WcW.wARH_ok hR hal hlo hhi
  -- the allocator's rest from `n4`
  have hA := seg_allocB_ofW_at (p := p) (lbl := lbl) hp hend hello_alloc
    (Spike.Lib.A64.HelloPh.Land.fstable_wARH (ms := tpXa ms t) (lab := lab) (J0 := J0) (J1 := J1) (q := q) hR hF
      hlo hhi)
    hR' hal' (by simp [Region.callee]) (by simp [Region.callee]) hqt (fun a ha m hm => hmem a ha m hm.1)
    (hWp.alloc q hqt hra) .n4
  -- its exits resumed in `wc_main`'s frame
  have hres := seg_resumeW (N := fun e : Empty => e.elim) (E := wXHA (tpXa ms t) lab J1) (F₂ := F)
    (M := fun _ => True)
    (PC := fun σC => ∃ c, (wNH lab J0 J1 .call).J σC c ∧ (Alloc.N lab (tpXa ms t) q .e).J (enter (-144) σC) c)
    (hA.mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
    (fun m ⟨h1, _, mC, σC', c', hA', hJ1, hJ2, hK'⟩ => ⟨h1, mC, σC', ⟨-144, []⟩, hK', hA', c', hJ1, hJ2⟩)
    (fun _ h _ => h) ?_
  · have hsp0 := hello_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
      (Q := fun _ _ => False) hp hend hF hR hal (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
      (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
      (fun l A s c hl h ht => hxa l A s c hl (at_bXH_of_tpXa h) ht)
    have hin := (hres.mono_post (Q' := fun s c => At exe endPc R F (wXH (tpXa ms t) lab J1 .sp0) s c ∨
      At exe endPc R F (wXA (tpXa ms t) lab J1) s c) fun s c h => by
        rcases h with ⟨e, -⟩ | ⟨y, h⟩
        · exact e.elim
        · cases y
          · exact .inl h
          · exact .inr h).seq_left hsp0
    refine ((SegW.keepTPN' hK hin fun _ _ h ht => h ht).mono_pre fun s c h => h).mono_post ?_
    rintro s c ⟨h | h, ht⟩
    · exact h.elim
    · exact ⟨at_wXA_of_tpXa h, ht⟩
  -- the allocator's exits land at `wc_main`'s, the spills kept
  rintro x σx c' σC hx ⟨c, ⟨⟨σe, hJe, h16, h8, h0', h1', h2', h3', h4'⟩, -, -, -, h30⟩, ⟨hc, -, h30', -⟩⟩
  have hsl : ∀ k, ¬ (wARH R).Off (k - -144) → (leave (wARH R) (-144) σC σx).slot k = σC.slot k :=
    fun k hn => by simp only [leave]; exact ite_eq_right hn
  have hk : ∀ k : Int, -144 ≤ k → k < 0 → (leave (wARH R) (-144) σC σx).slot k = σC.slot k := fun k h1 h2 =>
    hsl k (by simp only [Region.Off, Region.callee]; omega)
  cases x
  · refine .inr ⟨WX.sp0, ?_, rfl, ⟨q, hqt⟩, ⟨σe, hc ▸ hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hx⟩
    · show lab ".L22_wc_main.sp0" = Int64.ofBitVec q.ra
      rw [hra, int64_ofBitVec_toBitVec]
    · exact (hk (-16) (by decide) (by decide)).trans h16
    · exact (hk (-8) (by decide) (by decide)).trans h8
    · exact (hk (-144) (by decide) (by decide)).trans h0'
    · exact (hk (-136) (by decide) (by decide)).trans h1'
    · exact (hk (-128) (by decide) (by decide)).trans h2'
    · exact (hk (-120) (by decide) (by decide)).trans h3'
    · exact (hk (-112) (by decide) (by decide)).trans h4'
  · obtain ⟨h2, h30x, hfull⟩ := hx
    exact .inr ⟨WX.abort, rfl, rfl, h2, h30x, ⟨q, hqt⟩, hfull, σe, hc ▸ hJe,
      (hk (-144) (by decide) (by decide)).trans h0', (hk (-136) (by decide) (by decide)).trans h1',
      (hk (-128) (by decide) (by decide)).trans h2', (hk (-120) (by decide) (by decide)).trans h3',
      (hk (-112) (by decide) (by decide)).trans h4'⟩

end N4

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_n4_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_n4_segWA
