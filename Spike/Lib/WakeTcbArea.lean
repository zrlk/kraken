/-
**The second TCB's words at wake's memory side** (AArch64):
`Rt.PreChild.TcbArea (wakeMs hp i g) L.lab q` for main's second
`scc_rt_alloc_tcb` (`q.n0 = 80`, `q.h = 8390915`: header `pinA + 96`, TCB
`pinA + 104`, its limit word `lim2A = pinA + 112`, its id word `pinA + 160`),
the `TcbArea` part of `ClonePre`'s `X` (`PreChild`).

- `Q2`, `q2_mk` (the request `tcbPh2a` fixes), `q2_of` (from the call's
  `x0` and the owned counter).
- `hdrA_q2`, `tcbOf_q2`: the header and the TCB at `q`.
- `pin2_contains`, `pin2_unplaced`: an address in `[pinA, pinA + 168)` has
  its byte in `pinned` (`hpin2`), outside every placed label (labels lie in
  the heap or `.data`, `Layout.WF` disjoint from `pinned`).
- `tcbArea_q2`: the `TcbArea`, given `hpin2`, the second limit word's
  initial value `0` (`hinit2`), the memory relation at the spawn's
  placement and `GhOK` (so the flag `cT` is placed, not the limit word);
  `hPC_q2`: `PreChild` from `X`'s register and own-map facts and it.

`hpin2 : L.pinA.toNat + 168 ≤ L.Λ.pinned.lo + L.Λ.pinned.size` and
`hinit2 : (m0Of L.Λ o.prog o.secs).initVal ⟨lim2A L, 8⟩ = 0` are facts of
the concrete layout, decided there.
-/
import Spike.Lib.A64StartOfPlaceOK2
import Spike.Lib.WakeInstFields
import Spike.Lib.Rt.A64RtPreChild
import Spike.Lib.A64WakeTcb2
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeTcbArea

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (MemRelP lrange)
open Spike.Lib.A64.Rt (RuntimeLayout TcbGG hdrA tcbOf)
open Spike.Lib.A64.Rt.PreChild (TcbArea r1Of tidA)
open Spike.Lib.A64.PhRec (m0Of pin_ne)
open Spike.Lib.WakeGOf2 (lim2A lim2Off lim2V GOf2 gOf2_ne pin_ne2 gOf2_lim2V gOf2_lim2_le pinA_toNat_ofPlaceOK2)
open Spike.Lib.WakeInst (Gh wakeMs)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **wake's second TCB request**: header `8390915`, at `scc_rt_pinned_next = 80`. -/
def Q2 (q : TcbGG) : Prop := q.n0 = 80#64 ∧ q.h = 8390915#64

/-- **`Q2` of the request `tcbPh2a` fixes** (`TcbPhGP … hdr2 80#64`, the
fields `tcbW_postG` reads off `q`): any ghost and control. -/
theorem q2_mk (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (c0 : Ctl) :
    Q2 ⟨g, Spike.Lib.A64.WakePh.hdr2, 80#64, c0⟩ := ⟨rfl, rfl⟩

/-- **`Q2` from the call**: the header the caller's `x0` at the second
`bl scc_rt_alloc_tcb` (`hx0`, the `movz`/`movk` rows; `q.h` is `x0`, the
callee's `PreG`), the counter's old value the owned `scc_rt_pinned_next`
(`hn0`, from the first call's post; `q.n0` is it). -/
theorem q2_of {q : TcbGG} {x0 n : BitVec 64} (hh : q.h = x0) (hx0 : x0 = 8390915#64) (hn : q.n0 = n)
    (hn0 : n = 80#64) : Q2 q :=
  ⟨hn.trans hn0, hh.trans hx0⟩

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
include hp

set_option hygiene false in
/-- The layout of `ofPlaceOK`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **The header** at `q`: `pinA + 80 + 8·mOf 8390915 = pinA + 96`. -/
theorem hdrA_q2 {q : TcbGG} (hq : Q2 q) : hdrA (Ly).lab q = (Ly).pinA + 96#64 := by
  obtain ⟨hn, hh⟩ := hq
  have hm : Spike.Lib.A64.Flow.Ret0.AllocTcb.mOf 8390915#64 <<< 3 = 16#64 := by decide
  simp only [hdrA, hn, hh, hm, (Ly).lab_pin, BitVec.add_assoc]
  rfl

/-- **The TCB** at `q`: `pinA + 104`. -/
theorem tcbOf_q2 {q : TcbGG} (hq : Q2 q) : tcbOf (Ly).lab q = (Ly).pinA + 104#64 := by
  simp only [tcbOf, hdrA_q2 hp i hq, BitVec.add_assoc]
  rfl

/-- `pinA + c` for `c ≤ 168` does not wrap. -/
theorem pin2_toNat {c : Nat} (hc : c ≤ 168) :
    ((Ly).pinA + BitVec.ofNat 64 c).toNat = (Ly).pinA.toNat + c := by
  have := (Ly).words_small _ (Ly).pin_mem
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

variable (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
include hpin2

/-- **An address in `[pinA, pinA + 168)` is in `pinned`.** -/
theorem pin2_contains {x : Nat} (h0 : (Ly).pinA.toNat ≤ x) (h1 : x < (Ly).pinA.toNat + 168) :
    (Ly).Λ.pinned.contains x := by
  have hp0 : (Ly).pinA.toNat = (Ly).Λ.pinned.lo := PlaceW.pinA_toNat_ofPlaceW hp i
  simp only [Scc.Sem.Range.contains]
  omega

/-- **A word of the pinned region is outside every placed label.** -/
theorem pin2_unplaced {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tp tq sp) {x : Nat} (h0 : (Ly).pinA.toNat ≤ x)
    (h1 : x < (Ly).pinA.toNat + 168) :
    ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains x := by
  rintro ⟨l, b, hl, hx⟩
  have hc : Λ.pinned.contains x := pin2_contains hp i hpin2 h0 h1
  have hs : Λ.heap.contains x ∨ Λ.data.contains x := Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := (PlaceW.wf_link_of_placeW i hp).disjoint
  have hdp' : Λ.data.Disjoint Λ.pinned := hdp
  have hhp' : Λ.heap.Disjoint Λ.pinned := hhp
  simp only [Scc.Sem.Range.contains] at hc hs
  simp only [Scc.Sem.Range.Disjoint] at hdp' hhp'
  omega

/-- **A word of `[pinA + 96, pinA + 168)` at `wakeMs`**: runtime, mapped
for a write and for a read. -/
theorem pin2_word (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) {c : Nat} (hc0 : 96 ≤ c) (hc1 : c + 8 ≤ 168) :
    (wakeMs hp i g).rt ((Ly).pinA + BitVec.ofNat 64 c).toNat ∧
      (wakeMs hp i g).mp ⟨(Ly).pinA + BitVec.ofNat 64 c, 8⟩ true ∧
      (wakeMs hp i g).mp ⟨(Ly).pinA + BitVec.ofNat 64 c, 8⟩ false := by
  have ht := pin2_toNat hp i (c := c) (by omega)
  have hin : ∀ j < 8, (Ly).Λ.pinned.contains (((Ly).pinA + BitVec.ofNat 64 c).toNat + j) :=
    fun j hj => pin2_contains hp i hpin2 (by omega) (by omega)
  have hK : ∀ w, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) w ⟨(Ly).pinA + BitVec.ofNat 64 c, 8⟩ = true :=
    fun _ => Spike.Lib.A64Consumer.mapped_K0_of_mem fun j hj => .inr (hin j hj)
  refine ⟨pin2_unplaced hp i hpin2 hm (by omega) (by omega), ⟨hK true, fun _ => ⟨fun j hj => ?_, ?_⟩⟩,
    ⟨hK false, fun h => nomatch h⟩⟩
  · exact .inr (.inr (hin j (by simpa [Scc.Sem.Kernel.locBytes] using hj)))
  · rintro ⟨l, b, hl, hx⟩
    exact pin2_unplaced hp i hpin2 hm (x := ((Ly).pinA + BitVec.ofNat 64 c).toNat) (by omega) (by omega)
      ⟨l, b, hl, hx⟩

/-- **The flag is not the second limit word**: `GhOK` places it. -/
theorem cT_ne_lim2 (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) (hok : Spike.Lib.WakeInstFields.GhOK (Ly).Λ g) :
    (⟨lim2A Ly, 8⟩ : Loc) ≠ g.cT := by
  obtain ⟨-, -, -, ⟨b, hl, ho, hT⟩, -⟩ := hok
  intro he
  have hx : (lrange g.lsize g.cS.label b).contains (b + 8 * g.cS.offset) := by
    simp only [lrange, Scc.Sem.Range.contains]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left ho (by decide)) b⟩
  have hs : Λ.heap.contains (b + 8 * g.cS.offset) ∨ Λ.data.contains (b + 8 * g.cS.offset) :=
    Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
  have hwf := PlaceW.wf_link_of_placeW i hp
  have hd : Λ.data.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh : Λ.heap.InSpace := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  have hlt : b + 8 * g.cS.offset < 2 ^ 64 := by
    simp only [Scc.Sem.Range.InSpace, Scc.Sem.Range.contains] at hd hh hs; omega
  rw [hT] at he
  have ha := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Scc.Sem.wordLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ha
  have h112 := pin2_toNat hp i (c := 112) (by decide)
  simp only [lim2A, lim2Off] at ha
  rw [show (112#64 : BitVec 64) = BitVec.ofNat 64 112 from rfl, h112] at ha
  exact pin2_unplaced hp i hpin2 hm (x := b + 8 * g.cS.offset) (by omega) (by omega) ⟨_, _, hl, hx⟩

/-- **wake's second TCB's words** (`PreChild`'s `TcbArea`) at `wakeMs`, for
main's second `scc_rt_alloc_tcb` (`Q2 q`). -/
theorem tcbArea_q2 (hinit2 : (m0Of (Ly).Λ o.prog o.secs).initVal ⟨lim2A Ly, 8⟩ = 0)
    (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) (hok : Spike.Lib.WakeInstFields.GhOK (Ly).Λ g)
    {q : TcbGG} (hq : Q2 q) : TcbArea (wakeMs hp i g) (Ly).lab q := by
  have hW := fun c (h0 : 96 ≤ c) (h1 : c + 8 ≤ 168) => pin2_word hp i hpin2 g hm h0 h1
  have hT := tcbOf_q2 hp i hq
  have hH := hdrA_q2 hp i hq
  -- the TCB's words, as `pinA + c`
  have e : ∀ c : Nat, (Ly).pinA + 104#64 + BitVec.ofNat 64 c = (Ly).pinA + BitVec.ofNat 64 (104 + c) := by
    intro c; rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have e96 : (Ly).pinA + 96#64 = (Ly).pinA + BitVec.ofNat 64 96 := rfl
  have hstk : Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA := (Ly).lab_stacks
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [tidA, hT, hH, Spike.Lib.A64.Rt.Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hW 96 (by decide) (by decide)).1
    · rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e]; exact (hW _ (by decide) (by decide)).1
    all_goals (rw [e]; exact (hW _ (by decide) (by decide)).1)
  · intro a ha
    simp only [tidA, hT, hH, Spike.Lib.A64.Rt.Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hW 96 (by decide) (by decide)).2.1
    · rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e]; exact (hW _ (by decide) (by decide)).2.1
    all_goals (rw [e]; exact (hW _ (by decide) (by decide)).2.1)
  · rw [hT, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e]
    exact (hW _ (by decide) (by decide)).2.2
  · rw [hH]
    exact .inr (gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _)
  · simp only [tidA, hT]
    rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e]
    exact .inr (gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _)
  · intro e' he'
    rw [hT, hstk] at he'
    rw [hT]
    simp only [Spike.Lib.A64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> rw [e]
    · exact .inr (gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _)
    · exact .inr gOf2_lim2V
    all_goals exact .inr (gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _)
  · intro v hv
    rw [hT, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e] at hv
    have hv' := Spike.Lib.WakeG.wakeG_off hv (cT_ne_lim2 hp i hpin2 g hm hok)
    have := gOf2_lim2_le hinit2 hv'
    simp only [r1Of, hstk]
    exact this

/-- **`hPC` at wake's instance** (`A64WakeChildNNA`'s `PreChild` premise):
`X`'s register and own-map facts (main's pre-spawn) plus `tcbArea_q2`. -/
theorem hPC_q2 (hinit2 : (m0Of (Ly).Λ o.prog o.secs).initVal ⟨lim2A Ly, 8⟩ = 0)
    (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) (hok : Spike.Lib.WakeInstFields.GhOK (Ly).Λ g)
    {q : TcbGG} (hq : Q2 q) {own : Spike.Lib.A64Consumer.Own} {X : State → Prop}
    (hX : ∀ st, X st → (st.st.1.regs.getXReg .X3).toBitVec = tcbOf (Ly).lab q ∧
      Spike.Lib.A64.Rt.PreChild.NthOk own (Ly).lab 1#64 st ∧
      (⟨Spike.Lib.A64.Flow.Ret0.nextA (Ly).lab, 8⟩, (32768#64 : BitVec 64).setWidth 128) ∈ own st) :
    ∀ st, X st → Spike.Lib.A64.Rt.PreChild.PreChild (wakeMs hp i g) own (Ly).lab q st :=
  fun st hs => ⟨(hX st hs).1, (hX st hs).2.1, (hX st hs).2.2, tcbArea_q2 hp i hpin2 hinit2 g hm hok hq⟩

end Place

/-- info: 'Spike.Lib.WakeTcbArea.tcbArea_q2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcbArea_q2

end Spike.Lib.WakeTcbArea
