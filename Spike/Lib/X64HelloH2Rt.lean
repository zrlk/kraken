/-
**`H1GAH0W`'s runtime fields at `ofPlaceWX`** (hello.w, x86-64; the twin of `Spike/Lib/A64HelloH2Rt.lean` and the
hello twin of `X64WakeH1Rt`): `h2`'s memory side `ms2H … l b n l' b' n'` (the root's guarantee `gWH`, owned words
`ownGH … ntA`, arena `arW`, at the twice extended placement `lbl2H` and sizes) and the runtime words `wc_main`'s
second thread's spawn writes there: `resA`, `hdrA`, `tcbA`, `tid`, `hfld`, `htk`.

- `ms2H`: the side (wake's `WakeH1Inv.ms1W` at `lbl2H`, `gWH`, `ownGH`).
- `rt_H`, `stOkG_H`, `stOk_H`: a word in `.data` or `pinned` is in no label's range (no static label, `hstat`;
  rodata's and the box's labels in the arena's heap, `Fresh2H`'s landings) and, given its value allowed by `gWH`
  (off both limit words: any value), the runtime's to store (`StOk`) when unmapped under `F`.
- `lim2H_mem`, `sepCtr_H`, `hoffSp_H`, `hoff56_H`: hello's second limit word is a spawn word; A13's spawn words are
  apart from the arena's counter, so off the arena (`CalWf.off_of`); in particular the id word `tH + 56 =
  pinA + 168`.
- `ph_rmw2H`: the phase fact at `scc_rt_alloc_tcb`'s counter add (byte `4199228`, `lenL + 158`; bit `0` of `ph2aH`
  set: before `scc_rt_pinned_next`'s add).
- `resA_H2`, `hdrA_H`, `tcbA_H`, `tid_H`, `hfld_H`: the fields. The reserve's counter by `ResA.resA_H`; the
  second TCB's header `pinA + 104` (`tcb2QH_hdrA`), its counter add on a pool stack (`BandSp3H`, `good2aH_of`,
  `ownGH_2a`), its id word `pinA + 168`, its six fields `tH + 8 k` (`pinA + 112 … 152`), the limit field
  `pinA + 120` holding `lim2V` (`gOf2H_lim2V`), the others off both limit words.
- `ctr_stH`, `ctr_ldH`, `ph_takeH`, `htk_H`: the second take's counters (`lockA`, `freeNA`, `nextA`, runtime
  words off both limit words) and their ownership at the take's nodes on the first stack (`BoxPureH`'s
  `R.base + 96`), where `ownGH` picks `own2bH` at phase `12` (wake's `Ti2Tk.htk2_W`).
- `bandSp3H_of`: main's frame at `.x23` on a pool stack from `BoxPureH`'s base.
- `hunSp_H`: `hunH`, `hunT`, `hunF` from one fact, the spawn words unmapped under `F`.

Each field takes its word's `F`-unmapped fact (`hunN`, `hunH`, `hunP`, `hunT`, `hunF`, `hFr`) as a premise: the
root discharges them at the box's frame condition `F0`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The placement is `PlaceWX` and the layout `ofPlaceWX`, the assembly an `Scc.Sem.X64.Asm`; `StOk`/`LdOk` take no
  executable or end pc.
- The phases are decided at byte pcs (`ph_rmw2H` at `4199228`; `ph_takeH` through `X64HelloPh.take2_factH`'s
  rows at `.spin14 + 11` and `.bump + 56`), not by AArch64's label-relative check `phAtH`/`tkChk`, which are
  therefore not stated (as in `X64HelloResA`); `ph_rmw2H` and `ph_takeH` keep their names with these statements.
- The frames are x86-64's, at `BoxPureH`'s base `R.base + 96` (A64's `+ 80`): `scc_rt_alloc_tcb`'s callee region
  `R.callee (-136) (-184) 8` (`BandSp3H`; A64's `(-144) (-192) 0`), the thread init's `R.callee (-136) (-248) 8`
  and the take's `R'.callee (-48 - 0) (-200) 8` at `R.addr (-384)` (A64's `(-144) (-256) 0`, `(-48) (-208) 0`,
  `R.addr (-400)`); the reserve's region is `rARH R = R.callee (-136) (-40) 8`; the take's ghosts are
  `Ret0.AllocTcb.G`, as in `X64WakeWfTi2Tk.htk2_W`.
-/
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.X64WakeH1Rt
import Spike.Lib.X64HelloResA
import Spike.Lib.X64HelloTcb2CallW
import Spike.Lib.X64HelloWcSp3
import Spike.Lib.X64HelloClH
import Spike.Lib.X64HelloTake2
import Spike.Lib.X64HelloWcSp0

namespace Spike.Lib.X64.HelloPh.H2Rt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (helloCells)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout TcbOkGA hdrA tcbNG)
open Spike.Lib.X64.Rt.Reserve (ntA ResOkA)
open Spike.Lib.X64.Rt.PhOfTab (ph_of_factOk)
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH tcb2QH_hdrA tH)
open Spike.Lib.X64.HelloPh.Tcb2CallW (BandSp3H)
open Spike.Lib.X64HelloGOf2H (gWH lim2AH)
open Spike.Lib.HeapLand (AllocLand)

/-- **The phase fact at `scc_rt_alloc_tcb`'s counter add** (byte `4199228`, `lenL + 158`): before
`scc_rt_pinned_next`'s add (wake's `H1Rt.tcb_ph` at `helloCells`). -/
theorem ph_rmw2H : ph2aH 4199228 % 2 = 1 := by
  unfold ph2aH; rw [phH_eq]; decide +kernel

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Scc.Sem.X64.Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`h2`'s memory side** at the root's guarantee `gWH`, owned words `ownGH … ntA`, arena `arW` (no allocation
fragment), the start's labels twice extended (`lbl2H`) and its sizes (wake's `WakeH1Inv.ms1W`). -/
noncomputable def ms2H (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) :
    List TermRun.Frame → Spike.Lib.MemSide isa :=
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
    (gWH hp i (Spike.Lib.X64WakeHG.cTW hp i)) (fun s _ => ownGH (Ly) (ntA (Ly).lab) s)
    (Spike.Lib.X64.WakeOD.arW hp i)
    (fun _ _ _ _ _ => False) (lbl2H (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b l' b')
    (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls) l n) l' n')

variable {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}

set_option hygiene false in
/-- `h2`'s memory side at no frames. -/
local notation "ms2" => ms2H asm hp i E ls l b n l' b' n' []

/-- **A word of `.data` or `pinned` is in no label of `h2`'s placement**: the box's and rodata's labels land in
the arena's heap (`Fresh2H`), main's `ThreadId` box has no cells, and there is no static label (`hstat`). -/
theorem rt_H (hstat : Λ0.static = fun _ => none)
    (hf : Fresh2H (Spike.Lib.X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n') {x : Nat}
    (hx : (Ly).Λ.data.contains x ∨ (Ly).Λ.pinned.contains x) : (ms2).rt x := by
  rintro ⟨l'', b'', hl', hc⟩
  have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (PlaceWX.link i hp)
  obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (PlaceWX.wf_link_of_placeWX i hp).disjoint
  have hdh' : (Ly).Λ.data.Disjoint (Ly).Λ.heap := hdh
  have hph' : (Ly).Λ.heap.Disjoint (Ly).Λ.pinned := hph
  have hh : (Spike.Lib.X64.WakeOD.arW hp i).heap = (Ly).Λ.heap.lo := rfl
  have hn : (Spike.Lib.X64.WakeOD.arW hp i).cells = Scc.Cert.PlaceOK.allocCells := rfl
  obtain ⟨-, hland, -, hland'⟩ := hf
  unfold AllocLand at hland hland'
  rw [hh, hn] at hland hland'
  simp only [lbl2H, Spike.Lib.X64ConsumerA.upd, Spike.Lib.X64ConsumerA.updN, Scc.Sem.lrange] at hl' hc
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hx hdh' hph'
  split at hl'
  · cases hl'; rw [ite_eq_left ‹_›] at hc
    simp only [Scc.Sem.Range.contains] at hc; omega
  · rw [ite_eq_right ‹_›] at hc
    split at hl'
    · cases hl'; rw [ite_eq_left ‹_›] at hc
      simp only [Scc.Sem.Range.contains] at hc; omega
    · obtain ⟨rfl, -⟩ := Spike.Lib.X64WakeLoadT.l0T_some hstat hl'
      rw [ite_eq_right ‹_›] at hc
      simp [Spike.Lib.X64WakeLoadT.ls0T, Spike.Lib.X64ConsumerA.updN, Scc.Sem.Range.contains] at hc
      omega

/-- **A runtime store's word at `h2`'s side** (`Ret0.StOk`), its value allowed by `gWH` (`hG`): in `.data` or
`pinned` byte by byte, unmapped under `F`. -/
theorem stOkG_H (hstat : Λ0.static = fun _ => none)
    (hf : Fresh2H (Spike.Lib.X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n')
    {F : MachineData → Prop} {a v : BitVec 64}
    (hby : ∀ j < 8, (Ly).Λ.data.contains (a.toNat + j) ∨ (Ly).Λ.pinned.contains (a.toNat + j))
    (hG : gWH hp i (Spike.Lib.X64WakeHG.cTW hp i) ⟨a, 8⟩ (v.setWidth 128))
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    StOk ms2 F a v :=
  ⟨rt_H asm hp i E ls hstat hf (hby 0 (by decide)),
    ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem hby, fun _ j hj =>
      (hby j (by simpa [Scc.Sem.Kernel.locBytes] using hj)).elim .inl (.inr ∘ .inr)⟩, hG, hun⟩

/-- **`stOkG_H` off both limit words** (any value). -/
theorem stOk_H (hstat : Λ0.static = fun _ => none)
    (hf : Fresh2H (Spike.Lib.X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n')
    {F : MachineData → Prop} {a v : BitVec 64}
    (hby : ∀ j < 8, (Ly).Λ.data.contains (a.toNat + j) ∨ (Ly).Λ.pinned.contains (a.toNat + j))
    (h1 : a ≠ (Ly).pinA + 16#64) (h2 : a ≠ lim2AH (Ly)) (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    StOk ms2 F a v :=
  stOkG_H asm hp i E ls hstat hf hby (Spike.Lib.WakeG.wakeG_of (Spike.Lib.X64HelloGOf2H.gOf2H_ne h1 h2 _)) hun

/-- hello's second limit word is a spawn word (index `5`). -/
theorem lim2H_mem : lim2AH (Ly) ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨5, List.mem_range.2 (by decide), rfl⟩

/-- **A13's spawn words are apart from the arena's counter.** -/
theorem sepCtr_H (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA,
      Scc.Cert.Rt.X64.WordSep x (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) := by
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq, List.pairwise_cons] at hA13
  exact hA13.1.1.2.2

/-- **A spawn word is off the arena** and not its counter word (wake's `CalWf.hoffPin_W`, from A13 rather than
the pinned region's size). -/
theorem hoffSp_H (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {x : BitVec 64}
    (hx : x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA) :
    ¬ ((Spike.Lib.X64.WakeOD.arW hp i).heap ≤ x.toNat ∧
        x.toNat < (Spike.Lib.X64.WakeOD.arW hp i).heap + 16 * (Spike.Lib.X64.WakeOD.arW hp i).cells) ∧
      (⟨x, 8⟩ : Loc) ≠ (Spike.Lib.X64.WakeOD.arW hp i).ctrLoc :=
  Spike.Lib.X64.WakePh.CalWf.off_of hp i
    (by simpa using (Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13).2.1 x hx 0 (by decide))
    (Spike.Lib.X64.WakePh.CalWf.ne_of_sep (sepCtr_H hp i hA13 x hx))

/-- **The second TCB's id word `tH + 56 = pinA + 168` is off the arena**. -/
theorem hoff56_H (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ¬ ((Spike.Lib.X64.WakeOD.arW hp i).heap ≤ (tH (Ly).lab + 56#64).toNat ∧
        (tH (Ly).lab + 56#64).toNat <
          (Spike.Lib.X64.WakeOD.arW hp i).heap + 16 * (Spike.Lib.X64.WakeOD.arW hp i).cells) ∧
      (⟨tH (Ly).lab + 56#64, 8⟩ : Loc) ≠ (Spike.Lib.X64.WakeOD.arW hp i).ctrLoc := by
  have e : tH (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 11) := by
    show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 112#64 + 56#64 = _
    rw [(Ly).lab_pin, BitVec.add_assoc]; rfl
  rw [e]
  exact hoffSp_H hp i hA13 (List.mem_map.2 ⟨11, List.mem_range.2 (by decide), rfl⟩)

/-- **The second TCB's words unmapped from the spawn words'** (`hS`, one frame fact for the root): the header
`pinA + 104` (`hdrA_H`'s `hunH`), the id word `tH + 56` (`tid_H`'s `hunT`) and the six fields (`hfld_H`'s
`hunF`), spawn words `3`, `11` and `4` to `9`. -/
theorem hunSp_H {F : MachineData → Prop}
    (hS : ∀ m, F m → ∀ x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA, Mem.loadInt m.dmem x 8 = none) :
    (∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 104#64) 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem (tH (Ly).lab + 56#64) 8 = none) ∧
      ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields (tH (Ly).lab)
        (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 16384#64),
        ∀ m, F m → Mem.loadInt m.dmem (tH (Ly).lab + BitVec.ofNat 64 e.1) 8 = none := by
  have hq : ∀ k : Nat, tH (Ly).lab + BitVec.ofNat 64 k = (Ly).pinA + (112#64 + BitVec.ofNat 64 k) := by
    intro k; show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 112#64 + _ = _; rw [(Ly).lab_pin, BitVec.add_assoc]
  have hw : ∀ j < 16, ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + BitVec.ofNat 64 (80 + 8 * j)) 8 = none :=
    fun j hj m hm => hS m hm _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  refine ⟨hw 3 (by decide), ?_, fun e he => ?_⟩
  · have h := hw 11 (by decide)
    rwa [show (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 11) = tH (Ly).lab + 56#64 by rw [hq]; rfl] at h
  simp only [Spike.Lib.X64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [hq]
  · exact hw 4 (by decide)
  · exact hw 5 (by decide)
  · exact hw 6 (by decide)
  · exact hw 7 (by decide)
  · exact hw 8 (by decide)
  · exact hw 9 (by decide)

section Fields

variable (hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x)
  (hstat : Λ0.static = fun _ => none) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
  (hf : Fresh2H (Spike.Lib.X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n')
  {F : MachineData → Prop} {R : Spike.Lib.Region}

include hlab hstat hA13 hf

/-- **`H1GAH0W.resA`**: the reserve's counter `scc_rt_nthreads` at old value `0` (`ResA.resA_H`). -/
theorem resA_H2 (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) :
    ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl, ResOkA ms2 F (Ly).exe (Ly).endPc
      (Spike.Lib.X64.Flow.HelloWc.rARH R) F ⟨g.1, 0#64, g.2⟩ := by
  have hA := Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13
  exact Spike.Lib.X64.HelloPh.ResA.resA_H hlab (fun _ => rfl)
    (stOk_H asm hp i E ls hstat hf hA.1 (hA.2.2.1 _ (Spike.Lib.X64.WakePh.H1Rt.pin16_mem hp i))
      (hA.2.2.2.1 _ (lim2H_mem hp i)) hunN)

omit hlab in
/-- **`H1GAH0W.hdrA`**: the second TCB's header `pinA + 104`. -/
theorem hdrA_H (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 104#64) 8 = none) :
    ∀ c0 g, StOk ms2 F (hdrA (Ly).lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36) := by
  intro c0 g
  rw [tcb2QH_hdrA, (Ly).lab_pin]
  exact stOk_H asm hp i E ls hstat hf
    ((Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨3, List.mem_range.2 (by decide), rfl⟩))
    (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64HelloGOf2H.pin_ne2H (by decide)) hunH

omit hlab in
/-- **`H1GAH0W.tid`**: the second TCB's id word `tH + 56 = pinA + 168`. -/
theorem tid_H (hunT : ∀ m', F m' → Mem.loadInt m'.dmem (tH (Ly).lab + 56#64) 8 = none) :
    (ms2).rt (tH (Ly).lab + 56#64).toNat ∧ (ms2).mp ⟨tH (Ly).lab + 56#64, 8⟩ true ∧
      (ms2).G ⟨tH (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (tH (Ly).lab + 56#64) 8 = none := by
  have e : tH (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 168 := by
    show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 112#64 + 56#64 = _
    rw [(Ly).lab_pin, BitVec.add_assoc]; rfl
  rw [e] at hunT ⊢
  have h : StOk ms2 F ((Ly).pinA + BitVec.ofNat 64 168) 1#64 :=
    stOk_H asm hp i E ls hstat hf
      ((Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13).2.1 _
        (List.mem_map.2 ⟨11, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64HelloGOf2H.pin_ne2H (by decide)) hunT
  exact ⟨h.rt, h.mp, h.G, h.unmapped⟩

/-- **`H1GAH0W.tcbA`**: the second TCB's counter `scc_rt_pinned_next` at old value `80`, its add on a pool stack
(`hb`). -/
theorem tcbA_H (hb : BandSp3H (Ly) R) (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) :
    ∀ c0 g, TcbOkGA ms2 F (Ly).exe (Ly).endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0) := by
  have hA := Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13
  have hd := List.pairwise_cons.mp (Scc.Cert.Rt.X64.words_disj_of_wordsOk
    (Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (PlaceWX.rtWordsOk_link_of_placeWX i hp)))
  refine fun c0 g => ⟨?_, fun s c hAt => ?_⟩
  · show StOk ms2 F (Spike.Lib.X64.Flow.Ret0.pnA (Ly).lab) _
    rw [(Ly).lab_pn]
    exact stOk_H asm hp i E ls hstat hf ((Ly).words_mapped _ (Ly).pn_mem).2.2
      (Spike.Lib.X64.WakePh.CalWf.ne_of_sep
        (hd.1 _ (List.mem_append_right _ (List.mem_map.2 ⟨1, List.mem_range.2 (by decide), rfl⟩))))
      (hA.2.2.2.2 _ (lim2H_mem hp i) _ (Ly).pn_mem).symm hunP
  obtain ⟨-, -, -, hs, σ, hAb, -, -⟩ := hAt
  obtain ⟨-, -, eLen, -, -, -⟩ := Spike.Lib.X64.HelloPh.Tcb2W.tcb_labsH hlab (L := Ly)
  have hpcA : Spike.Lib.X64.HelloPh.Tcb2W.PcAH s.st.2 := by
    rw [hs]; dsimp only [tcbNG, Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc]; rw [eLen]; decide
  have hpc : pcOf s = 4199228 := by
    unfold pcOf; rw [hs]; dsimp only [tcbNG, Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc]; rw [eLen]; rfl
  have hg := Spike.Lib.X64.HelloPh.Tcb2W.good2aH_of hlab hb hpcA
    ⟨-184, by decide, by decide, Spike.Lib.X64ConsumerA.rsp_of_abs hAb⟩
  have hf' := ph_rmw2H
  rw [← hpc] at hf'
  show _ ∈ ownGH (Ly) (ntA (Ly).lab) s
  rw [ownGH_2a hlab hg]
  simp [own2aH, Spike.Lib.X64.WakePh.ownV, hf', (Ly).lab_pn, tcb2QH]

omit hlab in
/-- **`H1GAH0W.hfld`**: `scc_rt_thread_init`'s six fields of the second TCB `tH = pinA + 112` (spawn words `4`
to `9`), the limit field `pinA + 120` holding the second stack's limit (`gOf2H_lim2V`), the others off both limit
words. -/
theorem hfld_H (hunF : ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields (tH (Ly).lab)
      (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 16384#64),
      ∀ m, F m → Mem.loadInt m.dmem (tH (Ly).lab + BitVec.ofNat 64 e.1) 8 = none) :
    ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields (tH (Ly).lab)
      (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 16384#64),
      StOk ms2 F (tH (Ly).lab + BitVec.ofNat 64 e.1) e.2 := by
  have hA := (Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13).2.1
  have hq : ∀ k : Nat, tH (Ly).lab + BitVec.ofNat 64 k = (Ly).pinA + (112#64 + BitVec.ofNat 64 k) := by
    intro k; show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 112#64 + _ = _; rw [(Ly).lab_pin, BitVec.add_assoc]
  intro e he
  have hun := hunF e he
  simp only [Spike.Lib.X64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hun ⊢ <;> rw [hq] at hun ⊢
  · exact stOk_H asm hp i E ls hstat hf (hA _ (List.mem_map.2 ⟨4, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64HelloGOf2H.pin_ne2H (by decide)) hun
  · refine stOkG_H asm hp i E ls hstat hf (hA _ (List.mem_map.2 ⟨5, List.mem_range.2 (by decide), rfl⟩)) ?_ hun
    refine Spike.Lib.WakeG.wakeG_of ?_
    have e : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 16384#64 + 4096#64).setWidth 128 =
        Spike.Lib.X64WakeGOf2.lim2V (Ly) := by
      rw [(Ly).lab_stacks]
    rw [e]
    exact Spike.Lib.X64HelloGOf2H.gOf2H_lim2V
  · exact stOk_H asm hp i E ls hstat hf (hA _ (List.mem_map.2 ⟨6, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64HelloGOf2H.pin_ne2H (by decide)) hun
  · exact stOk_H asm hp i E ls hstat hf (hA _ (List.mem_map.2 ⟨7, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64HelloGOf2H.pin_ne2H (by decide)) hun
  · exact stOk_H asm hp i E ls hstat hf (hA _ (List.mem_map.2 ⟨8, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64HelloGOf2H.pin_ne2H (by decide)) hun
  · exact stOk_H asm hp i E ls hstat hf (hA _ (List.mem_map.2 ⟨9, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64HelloGOf2H.pin_ne2H (by decide)) hun

omit hlab in
/-- **A store to a runtime word at `h2`'s side** off both limit words: the first by A8's `tcbSep`
(`PlaceWX.ctr_neW`), hello's second by A13 (the spawn words apart from the runtime's). -/
theorem ctr_stH (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) {a v : BitVec 64}
    (ha : a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA]) (har : a ∈ (Ly).rtWords) : StOk ms2 F a v :=
  stOk_H asm hp i E ls hstat hf ((Ly).words_mapped _ har).2.2 (PlaceWX.ctr_neW hp i ha)
    ((Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13).2.2.2.2 _ (lim2H_mem hp i) _ har).symm
    (fun m hm => hFr m hm _ har)

omit hlab hA13 in
/-- **A load of a runtime word at `h2`'s side.** -/
theorem ctr_ldH (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) {a : BitVec 64} (har : a ∈ (Ly).rtWords) :
    LdOk ms2 F a :=
  ⟨rt_H asm hp i E ls hstat hf (by simpa using ((Ly).words_mapped _ har).2.2 0 (by decide)),
    ⟨((Ly).words_mapped _ har).2.1, fun h => nomatch h⟩, fun m hm => hFr m hm _ har⟩

end Fields

/-! ## The second take's counters (`H1GAH0W.htk`) -/

/-- A node state's `%rsp` is its region's address at the node's `%rsp` offset. -/
private theorem at_sp {L : RuntimeLayout} {ep : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : Spike.Lib.X64.ND} {s : State} {c : Ctl} (h : Spike.Lib.X64.At L.exe ep R F n s c) :
    s.st.1.regs.rsp.toBitVec = R.addr n.o.sp ∧ s.st.2 = n.pc := by
  obtain ⟨-, -, -, hpc, σ, hA, -, -⟩ := h
  exact ⟨Spike.Lib.X64ConsumerA.rsp_of_abs hA, hpc⟩

/-- A frame address `R.addr k` near `R`'s base, `R.base + 96` the first stack's top (`BoxPureH`): no wrap. -/
private theorem addr_boxH {L : RuntimeLayout} {R : Spike.Lib.Region}
    (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) {k : Int} (h1 : -480 ≤ k) (h2 : k ≤ 0) :
    ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have hB := R.base.isLt
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- **Main's frame at `.x23` on a pool stack** (`tcbA_H`'s `hb`) from `BoxPureH`'s `R.base + 96` the first
stack's top: `scc_rt_alloc_tcb`'s frame `R.addr (-320) … R.addr (-128)` lies in the first stack. -/
theorem bandSp3H_of {L : RuntimeLayout} {R : Spike.Lib.Region} (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) :
    BandSp3H L R := by
  unfold BandSp3H Spike.Lib.X64.HelloPh.Tcb2W.BandAH
  intro k h1 h2
  rw [Spike.Lib.Region.callee_addr]
  have hB := addr_boxH hb (k := -136 + k) (by omega) (by omega)
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  omega

/-- **The second take's nodes' `%rsp` on the first stack**: `R`'s `-136` callee's `-48` callee at `-200` is
`R.addr (-384)`, inside the pool (`hb`). -/
private theorem sp_ofH {L : RuntimeLayout} {ep : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : Spike.Lib.X64.ND} {s : State} {c : Ctl} (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384)
    (h : Spike.Lib.X64.At L.exe ep ((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8) F n s c)
    (hn : n.o.sp = -200) : Spike.Lib.X64.WakePh.spPool L s ∧ s.st.2 = n.pc := by
  obtain ⟨hsp, hpc⟩ := at_sp h
  refine ⟨?_, hpc⟩
  have hB := addr_boxH hb (k := -384) (by decide) (by decide)
  have hs := L.stacks_sub
  have e : ((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8).addr n.o.sp = R.addr (-384) := by
    rw [hn, Spike.Lib.Region.callee_addr, Spike.Lib.Region.callee_addr]; rfl
  unfold Spike.Lib.X64.WakePh.spPool
  rw [hsp, e]
  simp only [Scc.Sem.Range.Sub] at hs
  omega

/-- **A pc `lab l + k` lies between labels `l₁`, `l₂`**: decided on `codeT` (`h`), the labels resolved (`hlab`;
wake's `Ti2Tk.inPc_of` at `helloCells`). -/
private theorem inPc_ofH {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {l l₁ l₂ : Label} {k : Nat}
    (h : ((codeT lo helloCells l).bind fun x => (codeT lo helloCells l₁).bind fun x₁ =>
      (codeT lo helloCells l₂).map fun x₂ => decide (x₁ ≤ x + k ∧ x + k < x₂ ∧ x₂ < 2 ^ 64)) = some true)
    {s : State} (hs : pcOf s = (L.lab l + Int64.ofNat k).toBitVec.toNat) : Spike.Lib.X64.WakePh.inPc L l₁ l₂ s := by
  rw [codeT_eq] at h
  cases e : codeLabel lo helloCells l <;> cases e₁ : codeLabel lo helloCells l₁ <;>
    cases e₂ : codeLabel lo helloCells l₂ <;> simp only [e, e₁, e₂, Option.bind_none,
      Option.bind_some, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, decide_eq_true_eq] at h
  rename_i x x₁ x₂
  have hl : ∀ {l : Label} {y : Nat}, codeLabel lo helloCells l = some y → y < 2 ^ 64 →
      (L.lab l).toBitVec.toNat = y := fun hy hy' => by
    rw [hlab _ _ hy]; show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy']
  unfold Spike.Lib.X64.WakePh.inPc
  rw [hs, pc_eq hlab e, hl e₁ (by omega), hl e₂ h.2.2, Nat.mod_eq_of_lt (by omega)]
  exact ⟨h.1, h.2.1⟩

/-- **The phase facts at the take's two owned stores**: the lock's swap (`.spin14 + 11`) and the next offset's
store (`.bump + 56`) at phase `12` of `ph2bH` (`take2_factH`'s rows). -/
theorem ph_takeH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {lab : Label → Int64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    ph2bH (lab Spike.Lib.X64.Flow.Ret0.StackTake.spinL + Int64.ofNat 11).toBitVec.toNat = 12 ∧
      ph2bH (lab Spike.Lib.X64.Flow.Ret0.StackTake.bumpL + Int64.ofNat 56).toBitVec.toNat = 12 :=
  ⟨ph_of_factOk hlab (take2_factH hΛ (f := .ph Spike.Lib.X64.Rt.Code.Take.spinL 11 12)
      (by simp [take2TabH, Spike.Lib.X64.Rt.takeTkRows])),
    ph_of_factOk hlab (take2_factH hΛ (f := .ph Spike.Lib.X64.Rt.Code.Take.bumpL 56 12)
      (by simp [take2TabH, Spike.Lib.X64.Rt.takeTkRows]))⟩

section Tk

variable (hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x)
  (hstat : Λ0.static = fun _ => none) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
  (hf : Fresh2H (Spike.Lib.X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n')
  {F : MachineData → Prop} {R : Spike.Lib.Region}

include hlab hstat hA13 hf

/-- **`H1GAH0W.htk`**: the second take's lock, free count and next offset at `h2`'s side, owned at their nodes'
states on the first stack (`hb`: `BoxPureH`'s `R.base + 96` the first stack's top), where `ownGH` picks `own2bH`
(`ownGH_2b`; wake's `Ti2Tk.htk2_W`). -/
theorem htk_H (hb : R.base.toNat + 96 = (Ly).stacksA.toNat + 16384)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) :
    ∀ (c0 : Ctl) (R' : Spike.Lib.Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-136) (-248) 8 → ∀ (g g' : Spike.Lib.X64.Flow.Ret0.AllocTcb.G),
      Spike.Lib.X64.Rt.TakeOkA ms2 F (Ly).exe (Ly).endPc (R'.callee (-48 - 0) (-200) 8) F'
        (Spike.Lib.X64.Flow.Ret0.tiTake (Spike.Lib.X64.Flow.WakeWc.tiQ (tH (Ly).lab) c0 g) g') := by
  intro c0 R' F' _ hR g g'
  subst hR
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have hph := ph_takeH hΛ hlab
  refine ⟨?_, ?_, ?_, ?_, fun b' s c h => ?_, fun b' s c h => ?_, fun b' s c h => ?_⟩
  · rw [(Ly).lab_lock]; exact ctr_stH asm hp i E ls hstat hA13 hf hFr (by simp) (Ly).lock_mem
  · rw [(Ly).lab_freeN]; exact ctr_ldH asm hp i E ls hstat hf hFr (Ly).freeN_mem
  · rw [(Ly).lab_lock]; exact ctr_stH asm hp i E ls hstat hA13 hf hFr (by simp) (Ly).lock_mem
  · rw [(Ly).lab_next]; exact ctr_stH asm hp i E ls hstat hA13 hf hFr (by simp) (Ly).next_mem
  · obtain ⟨hsp, hpc⟩ := sp_ofH hb h rfl
    have hq : pcOf s = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.spinL + Int64.ofNat 11).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownGH (Ly) (ntA (Ly).lab) s
    rw [ownGH_2b hlab (.inl ⟨inPc_ofH hlab (by decide +kernel) hq, hsp⟩), hq, hph.1, (Ly).lab_lock]
    simp [own2bH, Spike.Lib.X64.WakePh.ownV]
  · obtain ⟨hsp, hpc⟩ := sp_ofH hb h rfl
    have hq : pcOf s = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.lockedL + Int64.ofNat 4).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownGH (Ly) (ntA (Ly).lab) s
    rw [ownGH_2b hlab (.inl ⟨inPc_ofH hlab (by decide +kernel) hq, hsp⟩), (Ly).lab_freeN]
    simp [own2bH, Spike.Lib.X64.WakePh.ownV]
  · obtain ⟨hsp, hpc⟩ := sp_ofH hb h rfl
    have hq : pcOf s = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.bumpL + Int64.ofNat 56).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownGH (Ly) (ntA (Ly).lab) s
    rw [ownGH_2b hlab (.inl ⟨inPc_ofH hlab (by decide +kernel) hq, hsp⟩), hq, hph.2, (Ly).lab_next]
    simp [own2bH, Spike.Lib.X64.WakePh.ownV]

end Tk

end Spike.Lib.X64.HelloPh.H2Rt

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.hoff56_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.hoff56_H

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.resA_H2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.resA_H2

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.hdrA_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.hdrA_H

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.tid_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.tid_H

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.tcbA_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.tcbA_H

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.hfld_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.hfld_H

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.htk_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.htk_H

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.hunSp_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.hunSp_H

/-- info: 'Spike.Lib.X64.HelloPh.H2Rt.bandSp3H_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Rt.bandSp3H_of
