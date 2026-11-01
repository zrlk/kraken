/-
**The second TCB's words at hello's worker memory side** (AArch64; B8-hS-Q2;
the hello twin of `WakeTcbArea`): `Rt.PreChild.TcbArea` at `HelloMs.msH (LH hp i) (GH hp i (G0H hp i))
(SRH hp i) w` for main's second `scc_rt_alloc_tcb` (`tcb2QH g c0`: header `pinA + 104`, TCB `tH = pinA + 112`, its
limit word `lim2AH = pinA + 120`, its id word `pinA + 168`), and so `HelloChildTls.TlsTcb` at the second take
`r1Of` with the clone's thread pointer the TCB.

- `hpin3_H`: the pinned region reaches `pinA + 176` (the id word's end) once the `.zero` after `scc_rt_pinned` has
  `176` bytes; at hello's certificate `hpin3_H hp i CertFacts.pinZ_helloCert (by decide)` (`131072` bytes).
- `pin3_toNat`, `pin3_contains`, `pin3_unplaced`, `pin3_word`: a word `pinA + c` (`c + 8 ≤ 176`) does not wrap,
  lies in `pinned`, outside every label placed under a memory relation (labels lie in the heap or `.data`), and is
  the runtime's at `msH`, mapped for a write and for a read.
- `cT_ne_lim2H`: the flag is not the second limit word (`GhOK` places it).
- `tcbArea_H`: the `TcbArea`, given `hpin3`, the second limit word's initial value `0` (`hinit2`) and a memory
  relation at the record's placement (`SpawnPre.inv1`'s, at the clone).
- `tlsTcb_H`: `TlsTcb` at `r1Of`, the thread pointer `tls` the TCB `tH` (`htls`), the second take in the stack
  pool (`hsub1`, `StartPlaceLy.hsub1_W`).
- An `example`: `TlsTcb`'s thread-pointer hypothesis `htls` is met by `tH` itself.

Open (row B8-hS-Q2, the clone side): `htls`, the clone's `x3` the TCB; `ClonePostH` leaves `wcNSH`'s `x3` (`tc`)
existential, so it comes with the `PreRH` `X` fix (row 5j-misc-X-fix).
-/
import Spike.Lib.A64HelloChildTls
import Spike.Lib.HelloAssemblyIM
import Spike.Lib.WakeTcbArea
import Spike.Lib.WakeChildXI
import Spike.Lib.A64HelloWcSp3
import Spike.Lib.A64HelloHMid

namespace Spike.Lib.HelloTcbArea

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (MemRelP lrange)
open Spike.Lib.A64.Rt (RuntimeLayout TcbGG hdrA tcbOf)
open Spike.Lib.A64.Rt.PreChild (TcbArea r1Of tidA)
open Spike.Lib.A64.PhRec (m0Of pin_ne)
open Spike.Lib.HelloGOf2H (lim2AH GOf2H gOf2H_ne pin_ne2H gOf2H_lim2V gOf2H_lim2_le)
open Spike.Lib.HelloMs (msH)
open Spike.Lib.HelloAssemblyI (LH ιH SRH GH)
open Spike.Lib.HelloAssemblyIM (G0H)
open Spike.Lib.A64.Flow.HelloWc (tcb2QH tcb2QH_hdrA tcb2QH_tcbOf tH)
open Spike.Lib.HelloChildTls (TlsTcb room_r1Of)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
include hp

/-- **The pinned region reaches `pinA + 176`** once the `.zero` after `scc_rt_pinned` has `176` bytes (wake's
`StartPlaceLy.hpin2_W` at `176`; hello's id word `pinA + 168` ends there). -/
theorem hpin3_H {n : Nat}
    (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some n)
    (hn : 176 ≤ n) : (LH hp i).pinA.toNat + 176 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size := by
  have hreg := PlaceW.regionsTied_of_placeW hp
  simp only [Scc.Cert.PlaceOK.regionsTied, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hreg
  have hsz : Λ0.pinned.size = n := Option.some.inj (hreg.2.2.2.symm.trans hz)
  have hp0 : (LH hp i).pinA.toNat = Λ0.pinned.lo := PlaceW.pinA_toNat_ofPlaceW hp i
  show (LH hp i).pinA.toNat + 176 ≤ Λ0.pinned.lo + Λ0.pinned.size
  omega

/-- `pinA + c` for `c ≤ 176` does not wrap. -/
theorem pin3_toNat {c : Nat} (hc : c ≤ 176) :
    ((LH hp i).pinA + BitVec.ofNat 64 c).toNat = (LH hp i).pinA.toNat + c := by
  have := (LH hp i).words_small _ (LH hp i).pin_mem
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

variable (hpin3 : (LH hp i).pinA.toNat + 176 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
include hpin3

/-- **An address in `[pinA, pinA + 176)` is in `pinned`.** -/
theorem pin3_contains {x : Nat} (h0 : (LH hp i).pinA.toNat ≤ x) (h1 : x < (LH hp i).pinA.toNat + 176) :
    (LH hp i).Λ.pinned.contains x := by
  have hp0 : (LH hp i).pinA.toNat = (LH hp i).Λ.pinned.lo := PlaceW.pinA_toNat_ofPlaceW hp i
  simp only [Scc.Sem.Range.contains]
  omega

/-- **A word of `[pinA, pinA + 176)` is outside every placed label.** -/
theorem pin3_unplaced {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ lbl lsize ts tm sm tp tq sp) {x : Nat} (h0 : (LH hp i).pinA.toNat ≤ x)
    (h1 : x < (LH hp i).pinA.toNat + 176) :
    ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains x := by
  rintro ⟨l, b, hl, hx⟩
  have hc : (LH hp i).Λ.pinned.contains x := pin3_contains hp i hpin3 h0 h1
  have hs : (LH hp i).Λ.heap.contains x ∨ (LH hp i).Λ.data.contains x :=
    Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := (PlaceW.wf_link_of_placeW i hp).disjoint
  have hdp' : (LH hp i).Λ.data.Disjoint (LH hp i).Λ.pinned := hdp
  have hhp' : (LH hp i).Λ.heap.Disjoint (LH hp i).Λ.pinned := hhp
  simp only [Scc.Sem.Range.contains] at hc hs
  simp only [Scc.Sem.Range.Disjoint] at hdp' hhp'
  omega

/-- **A word of `[pinA, pinA + 176)` at `msH`**: runtime, mapped for a write and for a read. -/
theorem pin3_word (G : ιH hp i → Loc → Val → Prop) (w : ιH hp i) {ts : Nat → Option Nat} {tm : Memory}
    {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp) {c : Nat} (hc1 : c + 8 ≤ 176) :
    (msH (LH hp i) G (SRH hp i) w).rt ((LH hp i).pinA + BitVec.ofNat 64 c).toNat ∧
      (msH (LH hp i) G (SRH hp i) w).mp ⟨(LH hp i).pinA + BitVec.ofNat 64 c, 8⟩ true ∧
      (msH (LH hp i) G (SRH hp i) w).mp ⟨(LH hp i).pinA + BitVec.ofNat 64 c, 8⟩ false := by
  have ht := pin3_toNat hp i (c := c) (by omega)
  have hin : ∀ j < 8, (LH hp i).Λ.pinned.contains (((LH hp i).pinA + BitVec.ofNat 64 c).toNat + j) :=
    fun j hj => pin3_contains hp i hpin3 (by omega) (by omega)
  have hK : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (LH hp i).Λ) wr
      ⟨(LH hp i).pinA + BitVec.ofNat 64 c, 8⟩ = true :=
    fun _ => Spike.Lib.A64Consumer.mapped_K0_of_mem fun j hj => .inr (hin j hj)
  refine ⟨pin3_unplaced hp i hpin3 hm (by omega) (by omega), ⟨hK true, fun _ => ⟨fun j hj => ?_, ?_⟩⟩,
    ⟨hK false, fun h => nomatch h⟩⟩
  · exact .inr (.inr (hin j (by simpa [Scc.Sem.Kernel.locBytes] using hj)))
  · rintro ⟨l, b, hl, hx⟩
    exact pin3_unplaced hp i hpin3 hm (x := ((LH hp i).pinA + BitVec.ofNat 64 c).toNat) (by omega) (by omega)
      ⟨l, b, hl, hx⟩

/-- **The flag is not the second limit word**: `GhOK` places it (in the heap or `.data`). -/
theorem cT_ne_lim2H (w : ιH hp i) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp) :
    (⟨lim2AH (LH hp i), 8⟩ : Loc) ≠ w.1.cT := by
  obtain ⟨-, -, -, ⟨b, hl, ho, hT⟩, -⟩ := w.2.1
  intro he
  have hx : (lrange w.1.lsize w.1.cS.label b).contains (b + 8 * w.1.cS.offset) := by
    simp only [lrange, Scc.Sem.Range.contains]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left ho (by decide)) b⟩
  have hs : (LH hp i).Λ.heap.contains (b + 8 * w.1.cS.offset) ∨
      (LH hp i).Λ.data.contains (b + 8 * w.1.cS.offset) :=
    Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
  have hwf := PlaceW.wf_link_of_placeW i hp
  have hd : (LH hp i).Λ.data.InSpace :=
    hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (LH hp i).Λ.data ∈ (LH hp i).Λ.regions)
  have hh : (LH hp i).Λ.heap.InSpace :=
    hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (LH hp i).Λ.heap ∈ (LH hp i).Λ.regions)
  have hlt : b + 8 * w.1.cS.offset < 2 ^ 64 := by
    simp only [Scc.Sem.Range.InSpace, Scc.Sem.Range.contains] at hd hh hs; omega
  rw [hT] at he
  have ha := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Scc.Sem.wordLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ha
  have h120 := pin3_toNat hp i (c := 120) (by decide)
  simp only [lim2AH, Spike.Lib.HelloGOf2H.lim2OffH] at ha
  rw [show (120#64 : BitVec 64) = BitVec.ofNat 64 120 from rfl, h120] at ha
  exact pin3_unplaced hp i hpin3 hm (x := b + 8 * w.1.cS.offset) (by omega) (by omega) ⟨_, _, hl, hx⟩

/-- **hello's second TCB's words** (`TcbArea`) at `msH` with the root's guarantee `GH (G0H)`, for main's second
`scc_rt_alloc_tcb` (`tcb2QH g c0`), given `hpin3`, the second limit word's initial value `0` (`hinit2`) and a
memory relation at the record's placement (`hm`). -/
theorem tcbArea_H (hinit2 : (m0Of (LH hp i).Λ o.prog o.secs).initVal ⟨lim2AH (LH hp i), 8⟩ = 0)
    (w : ιH hp i) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp)
    (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (c0 : Ctl) :
    TcbArea (msH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w) (LH hp i).lab (tcb2QH g c0) := by
  have hW := fun c (h1 : c + 8 ≤ 176) => pin3_word hp i hpin3 (GH hp i (G0H hp i)) w hm h1
  have hT : tcbOf (LH hp i).lab (tcb2QH g c0) = (LH hp i).pinA + 112#64 := by
    rw [tcb2QH_tcbOf]; show Spike.Lib.A64.Flow.Ret0.pinA (LH hp i).lab + 112#64 = _; rw [(LH hp i).lab_pin]
  have hH : hdrA (LH hp i).lab (tcb2QH g c0) = (LH hp i).pinA + 104#64 := by
    rw [tcb2QH_hdrA, (LH hp i).lab_pin]
  -- the TCB's words, as `pinA + c`
  have e : ∀ c : Nat, (LH hp i).pinA + 112#64 + BitVec.ofNat 64 c = (LH hp i).pinA + BitVec.ofNat 64 (112 + c) := by
    intro c; rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have hstk : Spike.Lib.A64.Flow.Ret0.stacksA (LH hp i).lab = (LH hp i).stacksA := (LH hp i).lab_stacks
  have hG : ∀ c : Nat, BitVec.ofNat 64 c ≠ 16#64 → BitVec.ofNat 64 c ≠ 120#64 → ∀ v,
      (msH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).G ⟨(LH hp i).pinA + BitVec.ofNat 64 c, 8⟩ v :=
    fun c h16 h120 v => .inr (gOf2H_ne (pin_ne h16) (pin_ne2H h120) v)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [tidA, hT, hH, Spike.Lib.A64.Rt.Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hW 104 (by decide)).1
    · rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e]; exact (hW _ (by decide)).1
    all_goals (rw [e]; exact (hW _ (by decide)).1)
  · intro a ha
    simp only [tidA, hT, hH, Spike.Lib.A64.Rt.Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hW 104 (by decide)).2.1
    · rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e]; exact (hW _ (by decide)).2.1
    all_goals (rw [e]; exact (hW _ (by decide)).2.1)
  · rw [hT, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e]
    exact (hW _ (by decide)).2.2
  · rw [hH]
    exact hG 104 (by decide) (by decide) _
  · simp only [tidA, hT]
    rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, e]
    exact hG _ (by decide) (by decide) _
  · intro e' he'
    rw [hT, hstk] at he'
    rw [hT]
    simp only [Spike.Lib.A64.Flow.Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> rw [e]
    · exact hG _ (by decide) (by decide) _
    · exact .inr gOf2H_lim2V
    all_goals exact hG _ (by decide) (by decide) _
  · intro v hv
    rw [hT, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, e] at hv
    have hv' := Spike.Lib.WakeG.wakeG_off hv (cT_ne_lim2H hp i hpin3 w hm)
    have := gOf2H_lim2_le hinit2 hv'
    simp only [r1Of, hstk]
    exact this

/-- **`TlsTcb` at the second take** (row clone-tls-TcbArea): `tcbArea_H`, the thread pointer `tls` the TCB `tH`
(`htls`), its limit word fitting (the pinned words are small) and off `r1Of` (the second take in the stack pool,
`hsub1`; the pool disjoint from `pinned`), and the frames' room at `r1Of` (`room_r1Of`). -/
theorem tlsTcb_H (hinit2 : (m0Of (LH hp i).Λ o.prog o.secs).initVal ⟨lim2AH (LH hp i), 8⟩ = 0)
    (hsub1 : (r1Of (LH hp i).lab).Sub (LH hp i).Λ.stackPool)
    (w : ιH hp i) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp)
    (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (c0 : Ctl) {tls : Nat} (htls : tls = (tH (LH hp i).lab).toNat) :
    TlsTcb (msH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w) (LH hp i).lab (tcb2QH g c0) tls (r1Of (LH hp i).lab) := by
  have hT : tH (LH hp i).lab = (LH hp i).pinA + BitVec.ofNat 64 112 := by
    show Spike.Lib.A64.Flow.Ret0.pinA (LH hp i).lab + 112#64 = _; rw [(LH hp i).lab_pin]
  have ht : tls = (LH hp i).pinA.toNat + 112 := by rw [htls, hT, pin3_toNat hp i (by decide)]
  have hsm := (LH hp i).words_small _ (LH hp i).pin_mem
  have hpool : ∀ x, (LH hp i).pinA.toNat ≤ x → x < (LH hp i).pinA.toNat + 176 →
      ¬ (LH hp i).Λ.stackPool.contains x := fun x h0 h1 =>
    Spike.Lib.WakeChildXI.notPool (PlaceW.wf_link_of_placeW i hp) (.inr (.inr (pin3_contains hp i hpin3 h0 h1)))
  refine ⟨tcbArea_H hp i hpin3 hinit2 w hm g c0, by rw [tcb2QH_tcbOf, htls], by omega, ?_, room_r1Of _⟩
  obtain ⟨hs0, hs1⟩ := hsub1
  have hsz : (r1Of (LH hp i).lab).size = 16384 := rfl
  by_cases h1 : tls + 16 ≤ (r1Of (LH hp i).lab).lo
  · exact .inl h1
  by_cases h2 : (r1Of (LH hp i).lab).lo + (r1Of (LH hp i).lab).size ≤ tls + 8
  · exact .inr h2
  exfalso
  by_cases hle : (r1Of (LH hp i).lab).lo ≤ tls + 8
  · exact hpool (tls + 8) (by omega) (by omega) ⟨by omega, by omega⟩
  · exact hpool (r1Of (LH hp i).lab).lo (by omega) (by omega) ⟨by omega, by omega⟩

end Place

/-! ## The clone's thread pointer -/

/-- **At the clone's `svc` `x3` is the node's thread pointer** (`wcNSH`'s `t`). -/
theorem x3_of_wcNSH {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region}
    {F : MachineData → Prop} {lab : Label → Int64} {c0 : Ctl} {t k : BitVec 64}
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    {s : State} {c : Ctl} (h : Spike.Lib.A64.Flow.At exe endPc R F
      (Spike.Lib.A64.HelloPh.WcSp6.wcNSH lab c0 t k sl me cA fr) s c) :
    (s.st.1.regs.getXReg .X3).toBitVec = t := by
  obtain ⟨-, -, -, -, σ, hA, -, hJ⟩ := h
  obtain ⟨-, -, -, -, h3, -⟩ := hJ
  rw [hA.regs]
  simpa [Scc.Sem.A64.xRegs] using h3

/-- **At main's clone in `h2`'s invariant `x3` is the second TCB** (row B8-hS-Q2's clone side, for the `PreRH` `X`
fix): `CloneMidH`'s node is `wcNSH` at `tH`. -/
theorem x3_of_cloneMidH {L : RuntimeLayout} {F0 : MachineData → Prop}
    {G : Spike.Lib.Region → (MachineData → Prop) → (Spike.Lib.A64.Flow.AS → Ctl → Prop) → UInt64 → Prop}
    {W : Spike.Lib.FragS isaLSE2} {Wc : Spike.Lib.Frag isaLSE2} {l : WeakMem.AllocLabel} {b : Nat}
    {ws : List TermRun.Word} {n : Nat} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : Spike.Lib.HelloHMid.CloneMidH L F0 G W Wc l b ws n s c fs) :
    (s.st.1.regs.getXReg .X3).toBitVec = tH L.lab := by
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA, fr, -, -, -, -, -, hA, -⟩ := h
  exact x3_of_wcNSH hA

/-- `tlsTcb_H`'s thread-pointer hypothesis is met by the TCB itself (its premise is not vacuous). -/
example (lab : Label → Int64) : ∃ tls : Nat, tls = (tH lab).toNat := ⟨_, rfl⟩

end Spike.Lib.HelloTcbArea

/-- info: 'Spike.Lib.HelloTcbArea.tcbArea_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloTcbArea.tcbArea_H

/-- info: 'Spike.Lib.HelloTcbArea.tlsTcb_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloTcbArea.tlsTcb_H

/-- info: 'Spike.Lib.HelloTcbArea.x3_of_cloneMidH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloTcbArea.x3_of_cloneMidH
