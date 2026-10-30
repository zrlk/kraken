/-
**wake.w's second `scc_rt_alloc_tcb` call** (AArch64): the instance of
`own2a` (`Spike/Lib/A64WakeOwn2.lean`) at the phase projection
`ph2a := phW % 4` with the take's phase always held (main holds its range
for the whole call), and `scc_rt_alloc_tcb`'s post-take phase facts
`TcbPhGP` (`Spike/Lib/Rt/A64RtTcbPost.lean`) there, returning to
`wc_main`'s `.sp4`.

Per-call phase projection; generic multi-spawn wants a reserve/post-take
phase bit (trusted, cleanup list). `own2a` reads only the bits `0`
(`scc_rt_pinned_next`) and `1` (`scc_rt_stack_lock`) of the phase, so it
factors through `ph2a`; `alloc_tcb`'s return (phase `12`) and `.sp4` (`16`)
have the same projection `0`, where the canonical phase would split them.

- `ph2a`, `ph2aC`, `ph2a_eq`: the projection, through the resolved tables.
- `tcb2Tab`, `tcb2Facts`: `tcbPhTab` returning to `.sp4`, the add's phases;
  decided at `ph2aC` (`decide +kernel`).
- `own2a_mod4`, `own2a_wc`: `own2a` through the projection.
- `own1_own2a_ph`: the first switch at the two phase maps (`phW` at the
  caller's `bl`, `ph2a` at the callee's entry).
- `instOk2aP`: the instance's facts; `tcbPh2a`: the phase facts.
-/
import Spike.Lib.A64WakeOwn2
import Spike.Lib.Rt.A64RtTcbPost
import Spike.Lib.Rt.A64RtPhTab

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout ownUpdB)
open Spike.Lib.A64.Rt.Tcb (TcbPhGP)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.Flow.Ret0.AllocTcb

/-- **The second `scc_rt_alloc_tcb` call's phase projection**: the bits
`0` and `1` of `phW`. -/
def ph2a (pc : Nat) : Nat := phW pc % 4

/-- The projection through the resolved tables. -/
def ph2aC (pc : Nat) : Nat := phC pc % 4

theorem ph2a_eq : ph2a = ph2aC := by
  funext pc; unfold ph2a ph2aC; rw [phW_eq]

open Spike.Lib.A64.Rt.Code in
/-- **The second call's facts**: `tcbPhTab` returning to `wc_main`'s
`.sp4`, and the add's phase and the next pc's. -/
def tcb2Tab : List PhFact :=
  [.blk Tcb.fnL 0 Tcb.atPro none none, .blk Tcb.entryL 0 Tcb.atChk none (some ".L3_scc_rt_alloc_tcb.2_full"),
    .blk Tcb.entryL 4 Tcb.atJ1 none none, .blk Tcb.lenL 0 Tcb.atLen none none,
    .blk Tcb.lenL 34 Tcb.atArg none none, .blk Tcb.lenL 38 Tcb.atBnd none none,
    .blk Tcb.lenL 47 Tcb.atJ2 none none, .blk Tcb.okL 2 Tcb.atOk none none,
    .blk Tcb.okL 30 Tcb.atRet (some ".L21_wc_main.sp4") none,
    .ne Tcb.entryL 4 ".L3_scc_rt_alloc_tcb.2_full" 0,
    .step Tcb.lenL 32, .step Tcb.lenL 33, .step Tcb.okL 0, .step Tcb.okL 1, .step Tcb.okL 29,
    .ok Tcb.lenL 37, .ph Tcb.lenL 37 1, .ph Tcb.lenL 38 0]

/-- **The second call's facts hold** at the projection. -/
theorem tcb2Facts : tcb2Tab.all (factOk (codeT lo wakeProg) okC ph2aC) = true := by
  decide +kernel

theorem tcb2_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ tcb2Tab) : factOk (codeOf lo wakeProg) (okPcOf lo wakeProg Λ) ph2a f = true := by
  have := List.all_eq_true.mp tcb2Facts f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← ph2a_eq] at this
  exact this

/-- **`own2a` factors through the projection**: it reads the phase's bits
`0` and `1` only. -/
theorem own2a_mod4 (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : own2a L a (i % 4) = own2a L a i := by
  have h1 : i % 4 % 2 = i % 2 := by omega
  have h2 : i % 4 / 2 % 2 = i / 2 % 2 := by omega
  unfold own2a ownV
  rw [h1, h2]
  simp

/-- At `wc_main`'s pcs after the reserve (phase `16`) the instance's list
is `own2a`'s at `16`. -/
theorem own2a_wc (L : RuntimeLayout) (a : BitVec 64) : own2a L a (16 % 4) = own2a L a 16 :=
  own2a_mod4 L a 16

/-- **The first switch at the two phase maps**: past `wc_main`'s second
`bl scc_rt_alloc_tcb` (`phW`, the first instance) at the callee's entry
(`ph2a`, this one) the lists agree. -/
theorem own1_own2a_ph (L : RuntimeLayout) (a : BitVec 64) :
    ownW L a (phW 2169264) = own2a L a (ph2a 2164712) := by
  have h1 : phW 2169264 = 16 := by rw [phW_eq]; exact allocTcb2_ph.1
  have h2 : ph2a 2164712 = 1 := by rw [ph2a_eq]; unfold ph2aC; rw [allocTcb2_ph.2.2]
  rw [h1, h2, ownW_eq]; unfold own2a ownV; simp

/-- **The instance's facts of the second `scc_rt_alloc_tcb` call**:
`own2a` through `ph2a`, the take's phase always held. -/
theorem instOk2aP {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2a L a (ph2a (pcOf s)))
      (fun _ => True) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo wakeProg L.Λ) ph2a L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (own2a L a) h, Iff.rfl⟩
  off := (instOkW hp hlo 0#64 (fun _ => True) hsite (rS := rS)).off

/-- The header's word offset at `wc_main`'s header: `8·mOf h = 16`. -/
theorem mOf_hdr2 : mOf hdr2 <<< 3 = 16#64 := by decide

/-- **The second `scc_rt_alloc_tcb` call's phase facts after the take** at
`ph2a`, returning to `wc_main`'s `.sp4`, the counter's old value `80`,
given the counters distinct (`hsep`) and the header's word none of them
(`hhdr`). -/
theorem tcbPh2a {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) :
    TcbPhGP (okPcOf lo wakeProg Λ) ph2a (fun _ => True) (own2a L a) L.lab
      (fun _ => L.lab ".L21_wc_main.sp4") hdr2 80#64 := by
  have hf : ∀ f ∈ tcb2Tab, _ := fun f hf => tcb2_fact hΛ (f := f) hf
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.A64.deadN (codeOf lo wakeProg) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → L.lab ".L21_wc_main.sp4" = L.lab r := fun _ h => nomatch h
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h1 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Tcb.lenL 37 1) (by simp [tcb2Tab]))
  have h0 := ph_of_factOk hlab (hf (.ph Spike.Lib.A64.Rt.Code.Tcb.lenL 38 0) (by simp [tcb2Tab]))
  obtain ⟨s1, s2, s3, s4⟩ := hsep
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.fnL 0 Spike.Lib.A64.Rt.Code.Tcb.atPro none none) (by simp [tcb2Tab]))
    entry := blkPh_of_factOk hlab hr
      (fun t ht => by
        simp only [Scc.Cert.Rt.A64.deadN] at ht
        split at ht
        · next d hd =>
          simp only [Spike.Lib.A64.Rt.Tcb.tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          rw [pcAt0_eq hlab hd]; exact ht
        · cases ht)
      (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.entryL 0 Spike.Lib.A64.Rt.Code.Tcb.atChk none (some ".L3_scc_rt_alloc_tcb.2_full")) (by simp [tcb2Tab]))
    j1 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.entryL 4 Spike.Lib.A64.Rt.Code.Tcb.atJ1 none none) (by simp [tcb2Tab]))
    len := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.lenL 0 Spike.Lib.A64.Rt.Code.Tcb.atLen none none)
      (by simp [tcb2Tab]))
    arg := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.lenL 34 Spike.Lib.A64.Rt.Code.Tcb.atArg none none) (by simp [tcb2Tab]))
    bnd := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.lenL 38 Spike.Lib.A64.Rt.Code.Tcb.atBnd none none) (by simp [tcb2Tab]))
    j2 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.lenL 47 Spike.Lib.A64.Rt.Code.Tcb.atJ2 none none) (by simp [tcb2Tab]))
    ok2 := blkPh_of_factOk hlab hr hn (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.okL 2 Spike.Lib.A64.Rt.Code.Tcb.atOk none none) (by simp [tcb2Tab]))
    ret := blkPh_of_factOk hlab (fun _ h => by cases h; rfl) hn
      (hf (.blk Spike.Lib.A64.Rt.Code.Tcb.okL 30 Spike.Lib.A64.Rt.Code.Tcb.atRet (some ".L21_wc_main.sp4") none) (by simp [tcb2Tab]))
    fullNe := by
      have := ne_of_factOk hlab (hf (.ne Spike.Lib.A64.Rt.Code.Tcb.entryL 4 ".L3_scc_rt_alloc_tcb.2_full" 0)
        (by simp [tcb2Tab]))
      rw [Spike.Lib.A64.Flow.ofNat4_zero] at this
      exact this
    si := by
      intro p hp
      simp only [Spike.Lib.A64.Rt.Tcb.siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Tcb.lenL 32) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Tcb.lenL 33) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Tcb.okL 0) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Tcb.okL 1) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Spike.Lib.A64.Rt.Code.Tcb.okL 29) (by simp [tcb2Tab]))
    rmwOk := ok_of_factOk hlab (hf (.ok Spike.Lib.A64.Rt.Code.Tcb.lenL 37) (by simp [tcb2Tab]))
    rmwTk := fun _ _ _ => Iff.rfl
    rmwIn := ⟨(80#64).setWidth 128, by rw [rmwPc, h1, hpn]; simp [own2a, ownV]⟩
    rmwUpd := by
      rw [rmwPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', h1, h0, hpn]
      simp [ownUpdB, own2a, ownV, s1, s2, s3, s4, Ne.symm s1, Ne.symm s2, Ne.symm s3, Ne.symm s4]
      decide
    hdrNo := fun j w hm => by
      rw [hpin, mOf_hdr2] at hm
      simp only [own2a, ownV, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, Loc.mk.injEq] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hhdr
      obtain ⟨n1, n2, n3, n4, n5⟩ := hhdr
      rcases hm with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩
      · exact n1 h
      · exact n2 h
      · exact n3 h
      · exact n4 h
      · exact n5 h }

end Spike.Lib.A64.WakePh

/-- info: 'Spike.Lib.A64.WakePh.tcbPh2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.tcbPh2a

/-- info: 'Spike.Lib.A64.WakePh.instOk2aP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.instOk2aP

/-- info: 'Spike.Lib.A64.WakePh.own1_own2a_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.own1_own2a_ph
