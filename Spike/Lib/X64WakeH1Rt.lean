/-
**`H1G`'s `resA`, `tcbA`, `hdrA`, `tid` at `ofPlaceWX`** (wake.w, x86-64;
the twin of `Spike/Lib/A64WakeH1Rt.lean`): the runtime words
`wake_wc_mid_hatK` writes at `h1`'s memory side `ms1W asm … l b n []`.

- `rt_W`, `stOk_W`: a word in `.data` or `pinned` is in no label's range
  (no static label, `hstat`; the new label `l` of `n` bytes at `b` in the
  arena's heap, `hland`) and, apart from the two fixed limit words, is the
  runtime's to store any value (`StOk`), given it is unmapped under `F`.
- `a13_facts`, `pin16_mem`, `lim2_mem`: A13's facts at `ofPlaceWX`.
- `res_ph`, `tcb_ph`: the phases at the two counter adds, decided.
- `resA_W`, `tcbA_W`, `hdrA_W`, `tid_W`: the fields. The reserve's counter
  add is at a free pc where `ownG` picks `ownW` before `scc_rt_nthreads`'
  add; the second TCB's on a pool stack (`BandSp3`) where it picks `own2a`
  before `scc_rt_pinned_next`'s add (`Tcb2W.good2a_of`, `ownG_2a`).

**Unlike AArch64**: the memory side owns `ownGXW` (`ownG` with main's and
the worker's TCB words appended), so the counter words are `ownG`'s, read
through the appends; the pcs are byte offsets resolved at the canonical base
(the reserve's add at `4199477`, the second TCB's at `lenL + 158 = 4199191`),
decided directly instead of through A64's `phAt` table check; `StOk` has no
executable or end pc; the callee's region is `R.callee (-72) (-184) 8`
(A64's `R.callee (-80) (-192) 0`); the assembly is a parameter `asm`.
-/
import Spike.Lib.X64WakeH1Root
import Spike.Lib.X64WakeLdFacts
import Spike.Lib.X64WakeWfCalOff
import Spike.Lib.X64WakeTcb2CallW
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeOAb

namespace Spike.Lib.X64.WakePh.H1Rt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf cellsOf)
open SccCode (wakeCells)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout TcbOkGA hdrA)
open Spike.Lib.X64.Rt.Reserve (ntA ResOkA rvN)
open Spike.Lib.X64.Rt (tcbNG)
open Spike.Lib.X64.Flow.Ret0 (StOk)
open Spike.Lib.X64.Flow.WakeWc (t2 rAR)
open Spike.Lib.X64.WakePh.Tcb2Call (tcb2Q)
open Spike.Lib.HeapLand (AllocLand)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Scc.Sem.X64.Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (cT : Loc) (ls0 : Spike.Lib.X64Consumer.Lsize) {l : WeakMem.AllocLabel} {b n : Nat}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => Spike.Lib.X64.WakeH1Inv.ms1W asm hp i E cT ls0 l b n []

/-- The phases at the reserve's counter add (`4199477`): free, and before
`scc_rt_nthreads`' add. -/
theorem res_ph : WcW.freeN 4199477 = true ∧ phW 4199477 / 16 % 2 = 0 := by
  rw [phW_eq]; unfold WcW.freeN WcW.inCv WcW.cv; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- The phase at the second TCB's counter add (`4199191`): before
`scc_rt_pinned_next`'s add. -/
theorem tcb_ph : ph2a 4199191 % 2 = 1 := by
  unfold ph2a; rw [phW_eq]; decide +kernel

/-- **A word of `.data` or `pinned` is in no label's range**. -/
theorem rt_W (hstat : Λ0.static = fun _ => none)
    (hland : AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n) {x : Nat}
    (hx : (Ly).Λ.data.contains x ∨ (Ly).Λ.pinned.contains x) : (ms1).rt x := by
  rintro ⟨l', b', hl', hc⟩
  have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (PlaceWX.link i hp)
  obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (PlaceWX.wf_link_of_placeWX i hp).disjoint
  have hdh' : (Ly).Λ.data.Disjoint (Ly).Λ.heap := hdh
  have hph' : (Ly).Λ.heap.Disjoint (Ly).Λ.pinned := hph
  have hh : (Spike.Lib.X64.WakeOD.arW hp i).heap = (Ly).Λ.heap.lo := rfl
  have hn : (Spike.Lib.X64.WakeOD.arW hp i).cells = Scc.Cert.PlaceOK.allocCells := rfl
  unfold AllocLand at hland
  simp only [Spike.Lib.X64ConsumerA.upd, Spike.Lib.X64ConsumerA.updN, Scc.Sem.lrange] at hl' hc
  split at hl'
  · cases hl'; rw [ite_eq_left ‹_›] at hc
    simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hx hc hdh' hph'
    rw [hh, hn] at hland; omega
  · obtain ⟨rfl, -⟩ := Spike.Lib.X64WakeLoadT.l0T_some hstat hl'
    rw [ite_eq_right ‹_›] at hc
    simp [Spike.Lib.X64WakeLoadT.ls0T, Spike.Lib.X64ConsumerA.updN, Scc.Sem.Range.contains] at hc
    omega

/-- **A runtime store's word at `ms1`** (`Ret0.StOk`): in `.data` or
`pinned` byte by byte, not a limit word, unmapped under `F`. -/
theorem stOk_W (hstat : Λ0.static = fun _ => none)
    (hland : AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n)
    {F : MachineData → Prop} {a v : BitVec 64}
    (hby : ∀ j < 8, (Ly).Λ.data.contains (a.toNat + j) ∨ (Ly).Λ.pinned.contains (a.toNat + j))
    (h1 : a ≠ (Ly).pinA + 16#64) (h2 : a ≠ Spike.Lib.X64WakeGOf2.lim2A (Ly))
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) : StOk ms1 F a v :=
  ⟨rt_W asm hp i E cT ls0 hstat hland (hby 0 (by decide)),
    ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem hby, fun _ j hj =>
      (hby j (by simpa [Scc.Sem.Kernel.locBytes] using hj)).elim .inl (.inr ∘ .inr)⟩,
    Spike.Lib.WakeG.wakeG_of (Spike.Lib.X64WakeGOf2.gOf2_ne h1 h2 _), hun⟩

/-- A13's facts at `ofPlaceWX`: `ntA`'s and the spawn words' bytes, `ntA`
apart from the runtime's and the spawn words, the spawn words from the runtime's. -/
theorem a13_facts (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    (∀ j < 8, (Ly).Λ.data.contains ((ntA (Ly).lab).toNat + j) ∨ (Ly).Λ.pinned.contains ((ntA (Ly).lab).toNat + j)) ∧
    (∀ x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA, ∀ j < 8,
      (Ly).Λ.data.contains (x.toNat + j) ∨ (Ly).Λ.pinned.contains (x.toNat + j)) ∧
    (∀ x ∈ (Ly).rtWords, ntA (Ly).lab ≠ x) ∧ (∀ x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA, ntA (Ly).lab ≠ x) ∧
    (∀ x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA, ∀ y ∈ (Ly).rtWords, x ≠ y) := by
  have hnt := ntA_W hp i hA13
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq, List.pairwise_cons] at hA13
  have hw : ∀ x, Scc.Cert.Rt.X64.wordOk (Ly).Λ x = true →
      ∀ j < 8, (Ly).Λ.data.contains (x.toNat + j) ∨ (Ly).Λ.pinned.contains (x.toNat + j) := fun x h j hj => by
    simp only [Scc.Cert.Rt.X64.wordOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true] at h
    exact h.2 j hj
  rw [hnt]
  exact ⟨hw _ hA13.1.1.1.1.2.1, fun x hx => hw x (hA13.1.1.1.1.2.2 x hx),
    fun x hx => CalWf.ne_of_sep (hA13.1.1.1.2.1 x hx), fun x hx => CalWf.ne_of_sep (hA13.1.2.1 x hx),
    fun x hx y hy => CalWf.ne_of_sep (hA13.1.1.1.2.2 x hx y hy)⟩

theorem pin16_mem : (Ly).pinA + 16#64 ∈ (Ly).rtWords := (Ly).fld_mem (i := 1) (by decide)
theorem lim2_mem : Spike.Lib.X64WakeGOf2.lim2A (Ly) ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨4, List.mem_range.2 (by decide), rfl⟩

section Fields

variable (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) (hlo0 : Λ0.code.lo = lo)
  (hstat : Λ0.static = fun _ => none) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
  (hland : AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n)
  {F : MachineData → Prop} {R : Spike.Lib.Region}

include hpa hwp hlo0 hstat hA13 hland

/-- **`H1G.resA`**: the reserve's counter `scc_rt_nthreads` at old value `0`. -/
theorem resA_W (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) :
    ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl, ResOkA ms1 F (Ly).exe (Spike.Lib.X64.WakeH1Inv.endR hp i)
      (rAR R) F ⟨g.1, 0#64, g.2⟩ := by
  have hA := a13_facts hp i hA13
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  refine fun g => ⟨stOk_W asm hp i E cT ls0 hstat hland hA.1 (hA.2.2.1 _ (pin16_mem hp i))
    (hA.2.2.2.1 _ (lim2_mem hp i)) hunN, fun s c hAt => ?_⟩
  have hs : s.st.2 = Spike.Lib.X64.Flow.Reserve.rmwPc (Ly).lab := hAt.2.2.2.1
  have hpc : pcOf s = 4199477 := by
    unfold pcOf; rw [hs]; exact pc_eq hlab resLabs.2.1 22
  have hf := res_ph
  rw [← hpc] at hf
  show _ ∈ ownGXW (Ly) (ntA (Ly).lab) s
  unfold ownGXW ownGX
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  rw [ownG_W hlab (WcW.goodW_of_freeN hlab hf.1), ownW_eq]
  simp [ownV, hf.2]

/-- **`H1G.tcbA`**: the second TCB's counter `scc_rt_pinned_next` at old
value `80`, its add on a pool stack (`hb`). -/
theorem tcbA_W (hb : Tcb2CallW.BandSp3 (Ly) R) (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) :
    ∀ c0 g, TcbOkGA ms1 F (Ly).exe (Spike.Lib.X64.WakeH1Inv.endR hp i) (R.callee (-72) (-184) 8) F
      (tcb2Q g c0) := by
  have hA := a13_facts hp i hA13
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hd := List.pairwise_cons.mp (Scc.Cert.Rt.X64.words_disj_of_wordsOk
    (Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (PlaceWX.rtWordsOk_link_of_placeWX i hp)))
  refine fun c0 g => ⟨?_, fun s c hAt => ?_⟩
  · show StOk ms1 F (Spike.Lib.X64.Flow.Ret0.pnA (Ly).lab) _
    rw [(Ly).lab_pn]
    exact stOk_W asm hp i E cT ls0 hstat hland ((Ly).words_mapped _ (Ly).pn_mem).2.2
      (CalWf.ne_of_sep (hd.1 _ (List.mem_append_right _ (List.mem_map.2 ⟨1, List.mem_range.2 (by decide), rfl⟩))))
      (hA.2.2.2.2 _ (lim2_mem hp i) _ (Ly).pn_mem).symm hunP
  obtain ⟨-, -, -, hs, σ, hAb, -, -⟩ := hAt
  obtain ⟨-, -, eLen, -, -, -⟩ := Tcb2W.tcb_labs hlab (L := Ly)
  have hpcA : Tcb2W.PcA s.st.2 := by
    rw [hs]; dsimp only [tcbNG, Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc]; rw [eLen]; decide
  have hpc : pcOf s = 4199191 := by
    unfold pcOf; rw [hs]; dsimp only [tcbNG, Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc]; rw [eLen]; rfl
  have hg := Tcb2W.good2a_of hlab hb hpcA ⟨-184, by decide, by decide, Spike.Lib.X64ConsumerA.rsp_of_abs hAb⟩
  have hf := tcb_ph
  rw [← hpc] at hf
  show _ ∈ ownGXW (Ly) (ntA (Ly).lab) s
  unfold ownGXW ownGX
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  rw [ownG_2a hlab hg]
  simp [own2a, ownV, hf, (Ly).lab_pn, tcb2Q]

omit hpa hwp hlo0 in
/-- **`H1G.hdrA`**: the second TCB's header `pinA + 96`. -/
theorem hdrA_W (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 128#64) 8 = none) :
    ∀ c0 g, StOk ms1 F (hdrA (Ly).lab (tcb2Q g c0)) ((tcb2Q g c0).h ||| 1#64 <<< 36) := by
  intro c0 g
  rw [Tcb2Call.tcb2Q_hdrA, (Ly).lab_pin]
  exact stOk_W asm hp i E cT ls0 hstat hland
    ((a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨2, List.mem_range.2 (by decide), rfl⟩))
    (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64WakeGOf2.pin_ne2 (by decide)) hunH

omit hpa hwp hlo0 in
/-- **`H1G.tid`**: the second TCB's id word `t2 + 56 = pinA + 192`. -/
theorem tid_W (hunT : ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none) :
    (ms1).rt (t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨t2 (Ly).lab + 56#64, 8⟩ true ∧
      (ms1).G ⟨t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none := by
  have e : t2 (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 192 := by
    show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 136#64 + 56#64 = _
    rw [(Ly).lab_pin, BitVec.add_assoc]; rfl
  rw [e] at hunT ⊢
  have h : StOk ms1 F ((Ly).pinA + BitVec.ofNat 64 192) 1#64 :=
    stOk_W asm hp i E cT ls0 hstat hland
      ((a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨10, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.X64.PhRec.pin_ne (by decide)) (Spike.Lib.X64WakeGOf2.pin_ne2 (by decide)) hunT
  exact ⟨h.rt, h.mp, h.G, h.unmapped⟩

end Fields

end Spike.Lib.X64.WakePh.H1Rt

/-- info: 'Spike.Lib.X64.WakePh.H1Rt.resA_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.H1Rt.resA_W

/-- info: 'Spike.Lib.X64.WakePh.H1Rt.tcbA_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.H1Rt.tcbA_W

/-- info: 'Spike.Lib.X64.WakePh.H1Rt.hdrA_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.H1Rt.hdrA_W

/-- info: 'Spike.Lib.X64.WakePh.H1Rt.tid_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.H1Rt.tid_W
