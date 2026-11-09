/-
**hello.w's second `scc_rt_alloc_tcb` call** (AArch64, the
`htcb` chain): the twin of `Spike/Lib/A64WakeTcb2.lean` at helloProg. The
instance of `own2aH` (`Spike/Lib/A64HelloOwn2.lean`) at the phase
projection `ph2aH := phH % 4` with the take's phase always held, and
`scc_rt_alloc_tcb`'s post-take phase facts `TcbPhGP` there, returning to
`wc_main`'s `.sp4` (hello.w's `.L22_wc_main`).

hello.w's header is `hdr2H` (`0xC00C03`: three argument words, so the
header's word is at `pinA + 80 + 24`, wake's `+ 16`).

- `tcb2TabH`, `tcb2FactsH`, `tcb2_factH`: `tcbPhTab` returning to `.sp4`,
  the add's phases; decided at `ph2aHC` (`decide +kernel`).
- `own2aH_wc`: `own2aH` at `wc_main`'s phase through the projection.
- `instOk2aPH`: the instance's facts; `mOf_hdr2H`; `tcbPh2aH`: the phase
  facts.
-/
import Spike.Lib.A64HelloOwn2
import Spike.Lib.A64WakeTcb2

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout ownUpdB)
open Spike.Lib.A64.Rt.Tcb (TcbPhGP)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.Flow.Ret0.AllocTcb
open Spike.Lib.A64.WakePh (ownV)

open Spike.Lib.A64.Rt.Code in
/-- **The second call's facts**: `tcbPhTab` returning to `wc_main`'s
`.sp4`, and the add's phase and the next pc's. -/
def tcb2TabH : List PhFact :=
  [.blk Tcb.fnL 0 Tcb.atPro none none, .blk Tcb.entryL 0 Tcb.atChk none (some ".L3_scc_rt_alloc_tcb.2_full"),
    .blk Tcb.entryL 4 Tcb.atJ1 none none, .blk Tcb.lenL 0 Tcb.atLen none none,
    .blk Tcb.lenL 34 Tcb.atArg none none, .blk Tcb.lenL 38 Tcb.atBnd none none,
    .blk Tcb.lenL 48 Tcb.atJ2 none none, .blk Tcb.okL 2 Tcb.atOk none none,
    .blk Tcb.okL 30 Tcb.atRet (some ".L22_wc_main.sp4") none,
    .ne Tcb.entryL 4 ".L3_scc_rt_alloc_tcb.2_full" 0,
    .step Tcb.lenL 32, .step Tcb.lenL 33, .step Tcb.okL 0, .step Tcb.okL 1, .step Tcb.okL 29,
    .ok Tcb.lenL 37, .ph Tcb.lenL 37 1, .ph Tcb.lenL 38 0]

/-- **The second call's facts hold** at the projection. -/
theorem tcb2FactsH : tcb2TabH.all (factOk (codeT lo SccCode.helloProg) okC ph2aHC) = true := by
  decide +kernel

theorem tcb2_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ tcb2TabH) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) ph2aH f = true := by
  have := List.all_eq_true.mp tcb2FactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← ph2aH_eq] at this
  exact this

/-- At `wc_main`'s pcs after the reserve (phase `16`) the instance's list
is `own2aH`'s at `16`. -/
theorem own2aH_wc (L : RuntimeLayout) (a : BitVec 64) : own2aH L a (16 % 4) = own2aH L a 16 :=
  own2aH_mod4 L a 16

/-- **The instance's facts of the second `scc_rt_alloc_tcb` call**:
`own2aH` through `ph2aH`, the take's phase always held. -/
theorem instOk2aPH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2aH L a (ph2aH (pcOf s)))
      (fun _ => True) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo SccCode.helloProg L.Λ) ph2aH L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (own2aH L a) h, Iff.rfl⟩
  off := (instOkH hp hlo 0#64 (fun _ => True) hsite (rS := rS)).off

/-- The header's word offset at `wc_main`'s header: `8·mOf h = 24`. -/
theorem mOf_hdr2H : mOf hdr2H <<< 3 = 24#64 := by decide

open Spike.Lib.A64.Rt.Code in
/-- **The second `scc_rt_alloc_tcb` call's phase facts after the take** at
`ph2aH`, returning to `wc_main`'s `.sp4`, the counter's old value `112`,
given the counters distinct (`hsep`) and the header's word none of them
(`hhdr`). -/
theorem tcbPh2aH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 112#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) :
    TcbPhGP (okPcOf lo SccCode.helloProg Λ) ph2aH (fun _ => True) (own2aH L a) L.lab
      (fun _ => L.lab ".L22_wc_main.sp4") hdr2H 112#64 := by
  have hf : ∀ f ∈ tcb2TabH, _ := fun f hf => tcb2_factH hΛ (f := f) hf
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → L.lab ".L22_wc_main.sp4" = L.lab r := fun _ h => nomatch h
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h1 := ph_of_factOk hlab (hf (.ph Tcb.lenL 37 1) (by simp [tcb2TabH]))
  have h0 := ph_of_factOk hlab (hf (.ph Tcb.lenL 38 0) (by simp [tcb2TabH]))
  obtain ⟨s1, s2, s3, s4⟩ := hsep
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Tcb.fnL 0 Tcb.atPro none none) (by simp [tcb2TabH]))
    entry := blkPh_of_factOk hlab hr
      (fun t ht => by
        simp only [Scc.Cert.Rt.A64.deadN] at ht
        split at ht
        · next d hd =>
          simp only [Spike.Lib.A64.Rt.Tcb.tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          rw [pcAt0_eq hlab hd]; exact ht
        · cases ht)
      (hf (.blk Tcb.entryL 0 Tcb.atChk none (some ".L3_scc_rt_alloc_tcb.2_full")) (by simp [tcb2TabH]))
    j1 := blkPh_of_factOk hlab hr hn (hf (.blk Tcb.entryL 4 Tcb.atJ1 none none) (by simp [tcb2TabH]))
    len := blkPh_of_factOk hlab hr hn (hf (.blk Tcb.lenL 0 Tcb.atLen none none)
      (by simp [tcb2TabH]))
    arg := blkPh_of_factOk hlab hr hn (hf (.blk Tcb.lenL 34 Tcb.atArg none none) (by simp [tcb2TabH]))
    bnd := blkPh_of_factOk hlab hr hn (hf (.blk Tcb.lenL 38 Tcb.atBnd none none) (by simp [tcb2TabH]))
    j2 := blkPh_of_factOk hlab hr hn (hf (.blk Tcb.lenL 48 Tcb.atJ2 none none) (by simp [tcb2TabH]))
    ok2 := blkPh_of_factOk hlab hr hn (hf (.blk Tcb.okL 2 Tcb.atOk none none) (by simp [tcb2TabH]))
    ret := blkPh_of_factOk hlab (fun _ h => by cases h; rfl) hn
      (hf (.blk Tcb.okL 30 Tcb.atRet (some ".L22_wc_main.sp4") none) (by simp [tcb2TabH]))
    fullNe := by
      have := ne_of_factOk hlab (hf (.ne Tcb.entryL 4 ".L3_scc_rt_alloc_tcb.2_full" 0)
        (by simp [tcb2TabH]))
      rw [Spike.Lib.A64.Flow.ofNat4_zero] at this
      exact this
    si := by
      intro p hp
      simp only [Spike.Lib.A64.Rt.Tcb.siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Tcb.lenL 32) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Tcb.lenL 33) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Tcb.okL 0) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Tcb.okL 1) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Tcb.okL 29) (by simp [tcb2TabH]))
    rmwOk := ok_of_factOk hlab (hf (.ok Tcb.lenL 37) (by simp [tcb2TabH]))
    rmwTk := fun _ _ _ => Iff.rfl
    rmwIn := ⟨(112#64).setWidth 128, by rw [rmwPc, h1, hpn]; simp [own2aH, ownV]⟩
    rmwUpd := by
      rw [rmwPc, Spike.Lib.A64.Flow.Ret0.ofNat4_succ', h1, h0, hpn]
      simp [ownUpdB, own2aH, ownV, s1, s2, s3, s4, Ne.symm s1, Ne.symm s2, Ne.symm s3, Ne.symm s4]
      decide
    hdrNo := fun j w hm => by
      rw [hpin, mOf_hdr2H] at hm
      simp only [own2aH, ownV, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, Loc.mk.injEq] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hhdr
      obtain ⟨n1, n2, n3, n4, n5⟩ := hhdr
      rcases hm with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩
      · exact n1 h
      · exact n2 h
      · exact n3 h
      · exact n4 h
      · exact n5 h }

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.tcbPh2aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.tcbPh2aH

/-- info: 'Spike.Lib.A64.HelloPh.instOk2aPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.instOk2aPH
