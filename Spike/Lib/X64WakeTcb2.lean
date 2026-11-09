/-
**wake.w's second `scc_rt_alloc_tcb` call** (x86-64; twin of
`Spike/Lib/A64WakeTcb2.lean`): the instance of `own2a`
(`Spike/Lib/X64WakeOwn2.lean`) at the phase projection `ph2a := phW % 4`
with the take's phase always held (main holds its range for the whole
call), and `scc_rt_alloc_tcb`'s post-take phase facts `TcbPhGP`
(`Spike/Lib/Rt/X64RtTcbPost.lean`) there, returning to `wc_main`'s `.x20`.

Per-call phase projection; generic multi-spawn wants a reserve/post-take
phase bit (trusted, cleanup list). `own2a` reads only the bits `0`
(`scc_rt_pinned_next`) and `1` (`scc_rt_stack_lock`) of the phase, so it
factors through `ph2a`; `alloc_tcb`'s return (phase `12`) and `.x20` (`16`)
have the same projection `0`, where the canonical phase would split them.

- `ph2a`, `ph2aC`, `ph2a_eq`: the projection, through the resolved tables.
- `tcb2Tab`, `tcb2Facts`: `tcbPhTab` (`Spike/Lib/Rt/X64RtPhTab.lean`)
  returning to `.x20`, the add's phases (`1` at the `lock xadd`, `.len` +
  158, `0` past it); decided at `ph2aC` (`decide +kernel`).
- `own2a_mod4`, `own2a_wc`: `own2a` through the projection.
- `own1_own2a_ph`: the first switch at the two phase maps (`phW` at the
  caller's `call`, `ph2a` at the callee's entry).
- `instOk2aP`: the instance's facts; `tcbPh2a`: the phase facts.
-/
import Spike.Lib.X64WakeOwn2
import Spike.Lib.Rt.X64RtTcbPost
import Spike.Lib.Rt.X64RtPhTab

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout ownUpdB tcbFullL)
open Spike.Lib.X64.Rt.Tcb (TcbPhGP)
open Spike.Lib.X64.Rt.PhOfTab
open Spike.Lib.X64.Flow.Ret0.AllocTcb

/-- **The second `scc_rt_alloc_tcb` call's phase projection**: the bits
`0` and `1` of `phW`. -/
def ph2a (pc : Nat) : Nat := phW pc % 4

/-- The projection through the resolved tables. -/
def ph2aC (pc : Nat) : Nat := phC pc % 4

theorem ph2a_eq : ph2a = ph2aC := by
  funext pc; unfold ph2a ph2aC; rw [phW_eq]

open Spike.Lib.X64.Rt.Code in
/-- **The second call's facts**: `tcbPhTab` returning to `wc_main`'s
`.x20`, and the add's phase and the next pc's. -/
def tcb2Tab : List PhFact :=
  [.blk Tcb.fnL 0 Tcb.atPro none none, .blk Tcb.entryL 0 Tcb.atChk none (some tcbFullL),
    .blk Tcb.entryL 20 Tcb.atJ1 none none, .blk Tcb.lenL 0 Tcb.atL0 none none,
    .blk Tcb.lenL 14 Tcb.atL1 none none, .blk Tcb.lenL 32 Tcb.atL2 none none,
    .blk Tcb.lenL 50 Tcb.atL3 none none, .blk Tcb.lenL 68 Tcb.atL4 none none,
    .blk Tcb.lenL 99 Tcb.atL5 none none, .blk Tcb.lenL 135 Tcb.atL6 none none,
    .blk Tcb.lenL 146 Tcb.atArg none none, .blk Tcb.lenL 163 Tcb.atBnd none none,
    .blk Tcb.lenL 198 Tcb.atJ2 none none, .blk Tcb.okL 7 Tcb.atO1 none none,
    .blk Tcb.okL 38 Tcb.atO2 none none, .blk Tcb.okL 56 Tcb.atO3 none none,
    .blk Tcb.okL 77 Tcb.atO4 none none, .blk Tcb.okL 98 Tcb.atO5 none none,
    .blk Tcb.okL 143 Tcb.atRet (some (".Lwc_main.x2", 0)) none,
    .ne Tcb.entryL 20 tcbFullL 0,
    .step Tcb.lenL 11 3, .step Tcb.lenL 29 3, .step Tcb.lenL 47 3, .step Tcb.lenL 65 3, .step Tcb.lenL 95 4,
    .step Tcb.lenL 132 3, .step Tcb.lenL 139 7, .step Tcb.okL 0 7, .step Tcb.okL 34 4, .step Tcb.okL 53 3,
    .step Tcb.okL 74 3, .step Tcb.okL 95 3, .step Tcb.okL 140 3,
    .ok Tcb.lenL 158, .ph Tcb.lenL 158 1, .ph Tcb.lenL 163 0]

/-- **The second call's facts hold** at the projection. -/
theorem tcb2Facts : tcb2Tab.all (factOk (codeT lo wakeCells) okC ph2aC) = true := by
  decide +kernel

theorem tcb2_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ tcb2Tab) : factOk (codeLabel lo wakeCells) (okPcOf lo wakeCells Λ) ph2a f = true := by
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
`call scc_rt_alloc_tcb` (`phW`, the first instance) at the callee's entry
(`ph2a`, this one) the lists agree. -/
theorem own1_own2a_ph (L : RuntimeLayout) (a : BitVec 64) :
    ownW L a (phW 4203405) = own2a L a (ph2a 4198992) := by
  have h1 : phW 4203405 = 16 := by rw [phW_eq]; exact allocTcb2_ph.1
  have h2 : ph2a 4198992 = 1 := by rw [ph2a_eq]; unfold ph2aC; rw [allocTcb2_ph.2.2]
  rw [h1, h2, ownW_eq]; unfold own2a ownV; simp

/-- **The instance's facts of the second `scc_rt_alloc_tcb` call**:
`own2a` through `ph2a`, the take's phase always held. -/
theorem instOk2aP {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => own2a L a (ph2a (pcOf s)))
      (fun _ => True) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo wakeCells L.Λ) ph2a L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (own2a L a) h, Iff.rfl⟩
  off := (instOkW hp hlo 0#64 (fun _ => True) hsite (rS := rS)).off

/-- The header's word offset at `wc_main`'s header: `8·mOf h = 16`. -/
theorem mOf_hdr2 : mOf hdr2 <<< 3 = 16#64 := by decide

open Spike.Lib.X64.Rt in
/-- **The second `scc_rt_alloc_tcb` call's phase facts after the take** at
`ph2a`, returning to `wc_main`'s `.x20`, the counter's old value `112`,
given the counters distinct (`hsep`) and the header's word none of them
(`hhdr`). -/
theorem tcbPh2a {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout}
    {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 112#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) :
    TcbPhGP (okPcOf lo wakeCells Λ) ph2a (fun _ => True) (own2a L a) L.lab
      (fun _ => L.lab ".Lwc_main.x2") hdr2 112#64 := by
  have hf : ∀ f ∈ tcb2Tab, _ := fun f hf => tcb2_fact hΛ (f := f) hf
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo wakeCells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab ".Lwc_main.x2" = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.X64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h1 := ph_of_factOk hlab (hf (.ph Code.Tcb.lenL 158 1) (by simp [tcb2Tab]))
  have h0 := ph_of_factOk hlab (hf (.ph Code.Tcb.lenL 163 0) (by simp [tcb2Tab]))
  have e5 : rmwPc L.lab + Int64.ofNat 5 = L.lab Code.Tcb.lenL + Int64.ofNat 163 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 158 5).symm
  obtain ⟨s1, s2, s3, s4⟩ := hsep
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.fnL 0 Code.Tcb.atPro none none) (by simp [tcb2Tab]))
    entry := blkPh_of_factOk hlab hr
      (fun t ht => by
        simp only [Scc.Cert.Rt.X64.deadN] at ht
        split at ht
        · next d hd =>
          simp only [Tcb.tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          exact ht.trans (pcAt0_eq hlab hd).symm
        · cases ht)
      (hf (.blk Code.Tcb.entryL 0 Code.Tcb.atChk none (some tcbFullL)) (by simp [tcb2Tab]))
    j1 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.entryL 20 Code.Tcb.atJ1 none none) (by simp [tcb2Tab]))
    len := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 0 Code.Tcb.atL0 none none) (by simp [tcb2Tab]))
    l1 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 14 Code.Tcb.atL1 none none) (by simp [tcb2Tab]))
    l2 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 32 Code.Tcb.atL2 none none) (by simp [tcb2Tab]))
    l3 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 50 Code.Tcb.atL3 none none) (by simp [tcb2Tab]))
    l4 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 68 Code.Tcb.atL4 none none) (by simp [tcb2Tab]))
    l5 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 99 Code.Tcb.atL5 none none) (by simp [tcb2Tab]))
    l6 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 135 Code.Tcb.atL6 none none) (by simp [tcb2Tab]))
    arg := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 146 Code.Tcb.atArg none none) (by simp [tcb2Tab]))
    bnd := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 163 Code.Tcb.atBnd none none) (by simp [tcb2Tab]))
    j2 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 198 Code.Tcb.atJ2 none none) (by simp [tcb2Tab]))
    o1 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 7 Code.Tcb.atO1 none none) (by simp [tcb2Tab]))
    o2 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 38 Code.Tcb.atO2 none none) (by simp [tcb2Tab]))
    o3 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 56 Code.Tcb.atO3 none none) (by simp [tcb2Tab]))
    o4 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 77 Code.Tcb.atO4 none none) (by simp [tcb2Tab]))
    o5 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 98 Code.Tcb.atO5 none none) (by simp [tcb2Tab]))
    ret := blkPh_of_factOk hlab (fun _ _ h => by cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) hn
      (hf (.blk Code.Tcb.okL 143 Code.Tcb.atRet (some (".Lwc_main.x2", 0)) none) (by simp [tcb2Tab]))
    fullNe := by
      have := ne_of_factOk hlab (hf (.ne Code.Tcb.entryL 20 tcbFullL 0) (by simp [tcb2Tab]))
      rw [Spike.Lib.X64.Flow.ofNat_zero'] at this
      exact this
    step := by
      intro pz hp
      simp only [Tcb.stepPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 11 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 29 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 47 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 65 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 95 4) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 132 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 139 7) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 0 7) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 34 4) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 53 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 74 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 95 3) (by simp [tcb2Tab]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 140 3) (by simp [tcb2Tab]))
    rmwOk := ok_of_factOk hlab (hf (.ok Code.Tcb.lenL 158) (by simp [tcb2Tab]))
    rmwTk := fun _ _ _ => Iff.rfl
    rmwIn := ⟨(112#64).setWidth 128, by rw [rmwPc, h1, hpn]; simp [own2a, ownV]⟩
    rmwUpd := by
      rw [e5, rmwPc, h1, h0, hpn]
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

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.ph2a_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ph2a_eq

/-- info: 'Spike.Lib.X64.WakePh.tcb2Facts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcb2Facts

/-- info: 'Spike.Lib.X64.WakePh.tcb2_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcb2_fact

/-- info: 'Spike.Lib.X64.WakePh.own2a_mod4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.own2a_mod4

/-- info: 'Spike.Lib.X64.WakePh.own2a_wc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.own2a_wc

/-- info: 'Spike.Lib.X64.WakePh.own1_own2a_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.own1_own2a_ph

/-- info: 'Spike.Lib.X64.WakePh.instOk2aP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.instOk2aP

/-- info: 'Spike.Lib.X64.WakePh.mOf_hdr2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.mOf_hdr2

/-- info: 'Spike.Lib.X64.WakePh.tcbPh2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbPh2a
