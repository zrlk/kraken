/-
**hello.w on x86-64: a placed record's self words** (the twin of `X64WakeSpawnR.selfOK_placed` at hello's two
TCBs): `SelfOK (tcbM L) (tcbWH L) g` for a record whose labels the memory relation places, given that the pinned
region reaches `pinA + 168` (`hpin2`).

- `selfOK_placedH`: main's TCB word `tcbM L = pinA + 8` and the worker's `tcbWH L = pinA + 112` lie in `pinned`
  (`hpin2`), so off every label the memory relation places (in `.data` or the heap, disjoint from `pinned`,
  `X64WakeGOf.heapData_of_placed`); the flag's word lies in its label (`X64WakeInst.inLabel_cT`), so it is not
  main's.
- `cT_ne_tcbWH_placedH`: such a record's flag word is not the worker's TCB word (in its label, which `tcbWH`
  is not).
- an inhabitation example: the record built at the clone (`X64WakeOkW.recW`) satisfies hello's `okHR` at the TCB
  words from the clone's facts and `hpin2`.

Consumer: `X64HelloAssemblyI.hello_obligations_I` (the records' `okHR` at the clone, through
`X64HelloRec.hrec_okHRc`).

**Unlike AArch64**, where the records need no self words (A64's threads own no word), x86-64's memory sides own
the TCB words `%fs:0` reads, so each record carries `SelfOK`; hello's second TCB is at `pinA + 112` (wake's at
`pinA + 104`).
-/
import Spike.Lib.X64HelloOwnLift
import Spike.Lib.X64WakeChildSt
import Spike.Lib.X64HelloOkHR

namespace Spike.Lib.X64HelloSelfOK

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.Inv2Core
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (tcbM)
open Spike.Lib.X64WakeInst (Gh SelfOK)
open Spike.Lib.X64WakeInstFields (GhOK)
open Spike.Lib.X64HelloOwnLift (tcbWH tcbM_ne_tcbWH)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`SelfOK` of a record placed by the memory relation** at hello's TCB words (see the module doc). -/
theorem selfOK_placedH (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {g : Gh}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) (hg : GhOK (Ly).Λ g) :
    SelfOK (tcbM (Ly)) (tcbWH (Ly)) g := by
  have hwf := Spike.Lib.X64WakeQ.hwf_ofPlaceOK hp i
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  have hH := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  have hD := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have h0 := PlaceWX.pinA_toNat_ofPlaceWX hp i
  have hsm := X64WakeChildSt.pinA_small hp i
  have eT : (tcbM (Ly)).toNat = (Ly).pinA.toNat + 8 := X64WakeChildSt.pinA_add hp i (c := 8) (by decide)
  have eW : (tcbWH (Ly)).toNat = (Ly).pinA.toNat + 112 := X64WakeChildSt.pinA_add hp i (c := 112) (by decide)
  simp only [Range.Disjoint, Range.InSpace] at hdp hhp hH hD
  have hoff : ∀ a : BitVec 64, a.toNat = (Ly).pinA.toNat + 8 ∨ a.toNat = (Ly).pinA.toNat + 112 →
      ¬ InLabel g.lbl g.lsize ⟨a, 8⟩ := by
    rintro a ha ⟨l, b, hl, hx⟩
    have hs := Spike.Lib.X64WakeGOf.heapData_of_placed hm hl hx
    simp only [Range.contains] at hs
    omega
  refine Spike.Lib.X64WakeInst.selfOK_of (tcbM_ne_tcbWH _) (hoff _ (.inl eT)) (hoff _ (.inr eW))
    (Spike.Lib.X64WakeInst.inLabel_cT hm (fun x hx => ?_) hg)
  simp only [Range.contains] at hx
  omega

/-- **The flag's word is not the worker's TCB word** at a record placed by the memory relation, with `SelfOK`
(`X64HelloOwn1.own1H_XW`'s `hcT` at `X64HelloAssemblyRV`): the flag's word lies in its label
(`X64WakeInst.inLabel_cT`), `tcbWH` in none. -/
theorem cT_ne_tcbWH_placedH {g : Gh} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) (hg : GhOK (Ly).Λ g)
    (hs : SelfOK (tcbM (Ly)) (tcbWH (Ly)) g) : g.cT ≠ ⟨tcbWH (Ly), 8⟩ := by
  have hwf := Spike.Lib.X64WakeQ.hwf_ofPlaceOK hp i
  have hH := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  have hD := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  simp only [Range.InSpace] at hH hD
  have hin := Spike.Lib.X64WakeInst.inLabel_cT hm (fun x hx => by
    simp only [Range.contains] at hx; omega) hg
  intro h
  exact hs.2.2.1 (h ▸ hin)

/-- **Inhabitation at hello's records**: the record built at the clone (`X64WakeOkW.recW`) satisfies hello's full
`okHR` at the TCB words, `SelfOK` included, from the clone's memory relation, `c`'s and the buffer's placement and
`hpin2` alone (what `X64HelloRec.hrec_okHRc` builds at `X64HelloAssemblyI.ιH`). -/
example (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {lB : WeakMem.AllocLabel}
    {b0 T S : Nat} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {l : WeakMem.AllocLabel} {pT : Loc} {cw : TermRun.Word} {ts : Nat → Option Nat} {tm : Memory}
    {sm : WeakMem.Memory} {tp tq sp : List Nat} (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tp tq sp) {cA : Nat}
    (hv : ValRep lbl (.loc ⟨l, 0⟩ 0) cA) (hcw : cw.val = .loc ⟨l, 0⟩ 0) (hin : 0 < lsize l) (hS : 0 < S)
    (hB : X64HelloInst.BufPl lbl lsize ⟨l, 0⟩ lB b0) :
    X64HelloOkHR.okHR (Ly).Λ lB (tcbM (Ly)) (tcbWH (Ly)) (X64WakeOkW.recW T S lbl lsize l pT cw) :=
  have hwf := Spike.Lib.X64WakeQ.hwf_ofPlaceOK hp i
  X64HelloOkHR.okHR_recW hm hwf hv hcw hin hS hB
    (selfOK_placedH hp i hpin2 hm (X64WakeOkW.okW_of_clone hm hwf hv hcw hin hS rfl rfl).1)

end Inst

end Spike.Lib.X64HelloSelfOK

/-- info: 'Spike.Lib.X64HelloSelfOK.selfOK_placedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSelfOK.selfOK_placedH

/-- info: 'Spike.Lib.X64HelloSelfOK.cT_ne_tcbWH_placedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSelfOK.cT_ne_tcbWH_placedH
