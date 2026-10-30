/-
**`H1G`'s `resA`, `tcbA`, `hdrA`, `tid` at `ofPlaceW`** (wake.w, AArch64):
the runtime words `wake_wc_mid_hatW` writes at `h1`'s memory side
`ms1W … l b n []`.

- `rt_W`, `stOk_W`: a word in `.data` or `pinned` is in no label's range
  (no static label, `hstat`; the new label `l` of `n` words at `b` in the
  arena's heap, `hland`) and, apart from the two fixed limit words, is the
  runtime's to store any value (`StOk`), given it is unmapped under `F`.
- `phAt`, `phAt_pc`: a label-relative pc check, read through `L.lab`.
- `resA_W`, `tcbA_W`, `hdrA_W`, `tid_W`: the fields. The reserve's counter
  add is at a free pc where `ownG` picks `ownW` before `scc_rt_nthreads`'
  add; the second TCB's on a pool stack (`BandSp3`) where it picks `own2a`
  before `scc_rt_pinned_next`'s add (`Tcb2W.good2a_of`, `ownG_2a`).
-/
import Spike.Lib.A64WakeH1Root
import Spike.Lib.A64WakeLdFacts
import Spike.Lib.A64WakeWfCalOff
import Spike.Lib.A64WakeTcb2CallW

namespace Spike.Lib.A64.WakePh.H1Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout TcbOkGA hdrA)
open Spike.Lib.A64.Rt.Reserve (ntA ResOkA)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.HeapLand (AllocLand)

/-- **A label-relative pc check**: `f` at `l + 4 k` of wakeProg. -/
def phAt (f : Nat → Bool) (l : Label) (k : Nat) : Bool :=
  match Scc.Cert.Rt.A64.pcAt (codeOf lo wakeProg) l k with
  | some t => f t
  | none => false

theorem phAt_pc {L : RuntimeLayout} (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {f : Nat → Bool} {l : Label} {k : Nat} (h : phAt f l k = true) {s : State}
    (hs : s.st.2 = L.lab l + Int64.ofNat (4 * k)) : f (pcOf s) = true := by
  unfold phAt at h
  split at h
  · next t ht => unfold pcOf; rw [hs, Spike.Lib.A64.Rt.PhOfTab.pcAt_eq hlab ht]; exact h
  · cases h

/-- The phase facts at the two counter adds: the reserve's free and before
`scc_rt_nthreads`' add, the second TCB's before `scc_rt_pinned_next`'s. -/
theorem ph_rmw : phAt (fun t => WcW.freeN t && phW t / 16 % 2 == 0) Spike.Lib.A64.Flow.Reserve.entryL 5 = true ∧
    phAt (fun t => ph2a t % 2 == 1) Spike.Lib.A64.Flow.Ret0.AllocTcb.lenL 37 = true := by
  unfold phAt WcW.freeN WcW.inCv WcW.cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (cT : Loc) (ls0 : Spike.Lib.A64Consumer.Lsize) {l : WeakMem.AllocLabel} {b n : Nat}

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

/-- **A word of `.data` or `pinned` is in no label's range**. -/
theorem rt_W (hstat : Λ0.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n) {x : Nat}
    (hx : (Ly).Λ.data.contains x ∨ (Ly).Λ.pinned.contains x) : (ms1).rt x := by
  rintro ⟨l', b', hl', hc⟩
  have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link i hp)
  obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (Spike.Lib.PlaceW.wf_link_of_placeW i hp).disjoint
  have hdh' : (Ly).Λ.data.Disjoint (Ly).Λ.heap := hdh
  have hph' : (Ly).Λ.heap.Disjoint (Ly).Λ.pinned := hph
  have hh : (WakeOD.arW hp i).heap = (Ly).Λ.heap.lo := rfl
  have hn : (WakeOD.arW hp i).cells = Scc.Cert.PlaceOK.allocCells := rfl
  unfold AllocLand at hland
  simp only [A64ConsumerA.upd, A64ConsumerA.updN, Scc.Sem.lrange] at hl' hc
  split at hl'
  · cases hl'; rw [ite_eq_left ‹_›] at hc
    simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hx hc hdh' hph'
    rw [hh, hn] at hland; omega
  · obtain ⟨rfl, -⟩ := WakeLoadT.l0T_some hstat hl'
    rw [ite_eq_right ‹_›] at hc
    simp [WakeLoadT.ls0T, A64ConsumerA.updN, Scc.Sem.Range.contains] at hc
    omega

/-- **A runtime store's word at `ms1`** (`Ret0.StOk`): in `.data` or
`pinned` byte by byte, not a limit word, unmapped under `F`. -/
theorem stOk_W (hstat : Λ0.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n) {F : MachineData → Prop}
    {exe : _root_.Executable} {endPc : Int64} {a v : BitVec 64}
    (hby : ∀ j < 8, (Ly).Λ.data.contains (a.toNat + j) ∨ (Ly).Λ.pinned.contains (a.toNat + j))
    (h1 : a ≠ (Ly).pinA + 16#64) (h2 : a ≠ WakeGOf2.lim2A (Ly)) (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    Spike.Lib.A64.Flow.Ret0.StOk ms1 F exe endPc a v :=
  ⟨rt_W hp i E cT ls0 hstat hland (hby 0 (by decide)),
    ⟨Spike.Lib.A64Consumer.mapped_K0_of_mem hby, fun _ j hj =>
      (hby j (by simpa [Scc.Sem.Kernel.locBytes] using hj)).elim .inl (.inr ∘ .inr)⟩,
    WakeG.wakeG_of (WakeGOf2.gOf2_ne h1 h2 _), hun⟩

/-- A13's facts at `ofPlaceW`: `ntA`'s and the spawn words' bytes, `ntA`
apart from the runtime's and the spawn words, the spawn words from the runtime's. -/
theorem a13_facts (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    (∀ j < 8, (Ly).Λ.data.contains ((ntA (Ly).lab).toNat + j) ∨ (Ly).Λ.pinned.contains ((ntA (Ly).lab).toNat + j)) ∧
    (∀ x ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA, ∀ j < 8,
      (Ly).Λ.data.contains (x.toNat + j) ∨ (Ly).Λ.pinned.contains (x.toNat + j)) ∧
    (∀ x ∈ (Ly).rtWords, ntA (Ly).lab ≠ x) ∧ (∀ x ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA, ntA (Ly).lab ≠ x) ∧
    (∀ x ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA, ∀ y ∈ (Ly).rtWords, x ≠ y) := by
  have hnt := StartPlaceLy.ntA_W hp i hA13
  simp only [Scc.Cert.Spawn.A64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq, List.pairwise_cons] at hA13
  have hw : ∀ x, Scc.Cert.Rt.A64.wordOk (Ly).Λ x = true →
      ∀ j < 8, (Ly).Λ.data.contains (x.toNat + j) ∨ (Ly).Λ.pinned.contains (x.toNat + j) := fun x h j hj => by
    simp only [Scc.Cert.Rt.A64.wordOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true] at h
    exact h.2 j hj
  rw [hnt]
  exact ⟨hw _ hA13.1.1.1.1.2.1, fun x hx => hw x (hA13.1.1.1.1.2.2 x hx),
    fun x hx => CalWf.ne_of_sep (hA13.1.1.1.2.1 x hx), fun x hx => CalWf.ne_of_sep (hA13.1.2.1 x hx),
    fun x hx y hy => CalWf.ne_of_sep (hA13.1.1.1.2.2 x hx y hy)⟩

theorem pin16_mem : (Ly).pinA + 16#64 ∈ (Ly).rtWords :=
  List.mem_append_right _ (List.mem_map.2 ⟨1, List.mem_range.2 (by decide), rfl⟩)
theorem lim2_mem : WakeGOf2.lim2A (Ly) ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨4, List.mem_range.2 (by decide), rfl⟩

section Fields

variable (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
  (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
  (hstat : Λ0.static = fun _ => none) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
  (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n) {F : MachineData → Prop} {R : Region}

omit hstat hA13 hland in
include hpa hwp hlo0 in
theorem hlab_W : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x := fun l x h =>
  Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by rw [StartPlaceLy.hlo_W hp i hlo0, StartPlaceLy.hp_W hpa hwp]; exact h)

include hpa hwp hlo0 hstat hA13 hland

/-- **`H1G.resA`**: the reserve's counter `scc_rt_nthreads` at old value `0`. -/
theorem resA_W (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) :
    ∀ g : Spike.Lib.A64.Flow.Reserve.G × Ctl, ResOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i)
      (Spike.Lib.A64.Flow.WakeWc.rAR R) F ⟨g.1, 0#64, g.2⟩ := by
  have hA := a13_facts hp i hA13
  refine fun g => ⟨stOk_W hp i E cT ls0 hstat hland hA.1 (hA.2.2.1 _ (pin16_mem hp i))
    (hA.2.2.2.1 _ (lim2_mem hp i)) hunN, fun s c hAt => ?_⟩
  have hf := phAt_pc (hlab_W hp i hpa hwp hlo0) ph_rmw.1 hAt.2.2.2.1
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  show _ ∈ ownG (Ly) (ntA (Ly).lab) s
  rw [ownG_W (hlab_W hp i hpa hwp hlo0) (WcW.goodW_of_freeN (hlab_W hp i hpa hwp hlo0) hf.1), ownW_eq]
  simp [ownV, hf.2]

/-- **`H1G.tcbA`**: the second TCB's counter `scc_rt_pinned_next` at old
value `80`, its add on a pool stack (`hb`). -/
theorem tcbA_W (hb : Tcb2CallW.BandSp3 (Ly) R) (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) :
    ∀ c0 g, TcbOkGA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R.callee (-80) (-192) 0) F (Tcb2Call.tcb2Q g c0) := by
  have hA := a13_facts hp i hA13
  have hlab := hlab_W hp i hpa hwp hlo0
  have hd := List.pairwise_cons.mp (Scc.Cert.Rt.A64.words_disj_of_wordsOk
    (Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (PlaceW.rtWordsOk_link_of_placeW i hp)))
  refine fun c0 g => ⟨?_, fun s c hAt => ?_⟩
  · show Spike.Lib.A64.Flow.Ret0.StOk ms1 F _ _ (Spike.Lib.A64.Flow.Ret0.pnA (Ly).lab) _
    rw [(Ly).lab_pn]
    exact stOk_W hp i E cT ls0 hstat hland ((Ly).words_mapped _ (Ly).pn_mem).2.2
      (CalWf.ne_of_sep (hd.1 _ (List.mem_append_right _ (List.mem_map.2 ⟨1, List.mem_range.2 (by decide), rfl⟩))))
      (hA.2.2.2.2 _ (lim2_mem hp i) _ (Ly).pn_mem).symm hunP
  obtain ⟨-, -, -, hs, σ, hAb, -, -⟩ := hAt
  have hpcA : Tcb2W.PcA s.st.2 := by
    obtain ⟨-, -, eLen, -, -, -⟩ := Tcb2W.tcb_labs hlab (L := Ly)
    rw [hs]; dsimp only [Spike.Lib.A64.Rt.tcbNG, Spike.Lib.A64.Flow.Ret0.AllocTcb.rmwPc]; rw [eLen]; decide
  have hg := Tcb2W.good2a_of hlab hb hpcA ⟨-192, by decide, by decide, by rw [hAb.regs]; exact hAb.so .SP _ rfl⟩
  have hf := phAt_pc hlab ph_rmw.2 hs
  simp only [beq_iff_eq] at hf
  show _ ∈ ownG (Ly) (ntA (Ly).lab) s
  rw [ownG_2a hlab hg]
  simp [own2a, ownV, hf, (Ly).lab_pn, Tcb2Call.tcb2Q]

omit hpa hwp hlo0 in
/-- **`H1G.hdrA`**: the second TCB's header `pinA + 96`. -/
theorem hdrA_W (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none) :
    ∀ c0 g, Spike.Lib.A64.Flow.Ret0.StOk ms1 F (Ly).exe (WakeSpawnR.endR hp i) (hdrA (Ly).lab (Tcb2Call.tcb2Q g c0))
      ((Tcb2Call.tcb2Q g c0).h ||| 1#64 <<< 36) := by
  intro c0 g
  rw [Tcb2Call.tcb2Q_hdrA, (Ly).lab_pin]
  exact stOk_W hp i E cT ls0 hstat hland ((a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨2, List.mem_range.2 (by decide), rfl⟩))
    (Spike.Lib.A64.PhRec.pin_ne (by decide)) (WakeGOf2.pin_ne2 (by decide)) hunH

omit hpa hwp hlo0 in
/-- **`H1G.tid`**: the second TCB's id word `t2 + 56 = pinA + 160`. -/
theorem tid_W (hunT : ∀ m', F m' → Mem.loadInt m'.dmem (Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64) 8 = none) :
    (ms1).rt (Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64).toNat ∧ (ms1).mp ⟨Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64, 8⟩ true ∧
      (ms1).G ⟨Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64) 8 = none := by
  have e : Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 160 := by
    show Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 104#64 + 56#64 = _
    rw [(Ly).lab_pin, BitVec.add_assoc]; rfl
  rw [e] at hunT ⊢
  have h : Spike.Lib.A64.Flow.Ret0.StOk ms1 F (Ly).exe (Ly).endPc ((Ly).pinA + BitVec.ofNat 64 160) 1#64 :=
    stOk_W hp i E cT ls0 hstat hland ((a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨10, List.mem_range.2 (by decide), rfl⟩))
      (Spike.Lib.A64.PhRec.pin_ne (by decide)) (WakeGOf2.pin_ne2 (by decide)) hunT
  exact ⟨h.rt, h.mp, h.G, h.unmapped⟩

end Fields

end Spike.Lib.A64.WakePh.H1Rt

/-- info: 'Spike.Lib.A64.WakePh.H1Rt.resA_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.H1Rt.resA_W

/-- info: 'Spike.Lib.A64.WakePh.H1Rt.tcbA_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.H1Rt.tcbA_W

/-- info: 'Spike.Lib.A64.WakePh.H1Rt.hdrA_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.H1Rt.hdrA_W

/-- info: 'Spike.Lib.A64.WakePh.H1Rt.tid_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.H1Rt.tid_W
