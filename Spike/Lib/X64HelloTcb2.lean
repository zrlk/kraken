/-
**hello.w's second `scc_rt_alloc_tcb` call** (x86-64; the twin of
`Spike/Lib/A64HelloTcb2.lean`): the instance of `own2aH`
(`Spike/Lib/X64HelloOwn2.lean`) at the phase projection `ph2aH := phH % 4`
with the take's phase always held, and `scc_rt_alloc_tcb`'s post-take phase
facts `TcbPhGP` there, returning to `wc_main`'s `.x24`.

hello.w's header is `hdr2H` (`0xC00C03`: three argument words, so the
header's word is at `pinA + 80 + 24`, wake's `+ 16`).

- `tcb2TabH`, `tcb2FactsH`, `tcb2_factH`: `tcbPhTab` returning to `.x24`,
  the add's phases; decided at `ph2aHC` (`decide +kernel`).
- `instOk2aPH`: the instance's facts; `mOf_hdr2H`; `tcbPh2aH`: the phase
  facts.

## Differences from the AArch64 version

- The table is x86-64's `scc_rt_alloc_tcb` (`X64WakeTcb2.tcb2Tab`'s blocks,
  steps and the `lock xadd` phases at `.len + 158`), returning to
  `.Lwc_main.x2` (A64: `.L22_wc_main.sp4`).
- The projection `ph2aH`, `own2aH_mod4` and the first switch
  `own1_own2aH_ph` are in `X64HelloOwn2`; A64's `own2aH_wc` (dead) is not
  twinned.
-/
import Spike.Lib.X64HelloOwn2
import Spike.Lib.X64WakeTcb2

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout ownUpdB tcbFullL)
open Spike.Lib.X64.Rt.Tcb (TcbPhGP)
open Spike.Lib.X64.Rt.PhOfTab
open Spike.Lib.X64.Flow.Ret0.AllocTcb
open Spike.Lib.X64.WakePh (ownV)

open Spike.Lib.X64.Rt.Code in
/-- **The second call's facts**: `tcbPhTab` returning to `wc_main`'s
`.x24`, and the add's phase and the next pc's. -/
def tcb2TabH : List PhFact :=
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
theorem tcb2FactsH : tcb2TabH.all (factOk (codeT lo helloCells) okC ph2aHC) = true := by
  decide +kernel

theorem tcb2_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ tcb2TabH) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) ph2aH f = true := by
  have := List.all_eq_true.mp tcb2FactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← ph2aH_eq] at this
  exact this

/-- **The instance's facts of the second `scc_rt_alloc_tcb` call**:
`own2aH` through `ph2aH`, the take's phase always held. -/
theorem instOk2aPH {L : RuntimeLayout} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => own2aH L a (ph2aH (pcOf s)))
      (fun _ => True) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo helloCells L.Λ) ph2aH L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (own2aH L a) h, Iff.rfl⟩
  off := (instOkH hp hlo 0#64 (fun _ => True) hsite (rS := rS)).off

/-- The header's word offset at `wc_main`'s header: `8·mOf h = 24`. -/
theorem mOf_hdr2H : mOf hdr2H <<< 3 = 24#64 := by decide

open Spike.Lib.X64.Rt in
/-- **The second `scc_rt_alloc_tcb` call's phase facts after the take** at
`ph2aH`, returning to `wc_main`'s `.x24`, the counter's old value `112`,
given the counters distinct (`hsep`) and the header's word none of them
(`hhdr`). -/
theorem tcbPh2aH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout}
    {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 112#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) :
    TcbPhGP (okPcOf lo helloCells Λ) ph2aH (fun _ => True) (own2aH L a) L.lab
      (fun _ => L.lab ".Lwc_main.x2") hdr2H 112#64 := by
  have hf : ∀ f ∈ tcb2TabH, _ := fun f hf => tcb2_factH hΛ (f := f) hf
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      L.lab ".Lwc_main.x2" = L.lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.X64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have h1 := ph_of_factOk hlab (hf (.ph Code.Tcb.lenL 158 1) (by simp [tcb2TabH]))
  have h0 := ph_of_factOk hlab (hf (.ph Code.Tcb.lenL 163 0) (by simp [tcb2TabH]))
  have e5 : rmwPc L.lab + Int64.ofNat 5 = L.lab Code.Tcb.lenL + Int64.ofNat 163 :=
    (Spike.Lib.X64.Flow.ofNat_add' _ 158 5).symm
  obtain ⟨s1, s2, s3, s4⟩ := hsep
  exact {
    e := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.fnL 0 Code.Tcb.atPro none none) (by simp [tcb2TabH]))
    entry := blkPh_of_factOk hlab hr
      (fun t ht => by
        simp only [Scc.Cert.Rt.X64.deadN] at ht
        split at ht
        · next d hd =>
          simp only [Tcb.tcbDead, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht ⊢
          exact ht.trans (pcAt0_eq hlab hd).symm
        · cases ht)
      (hf (.blk Code.Tcb.entryL 0 Code.Tcb.atChk none (some tcbFullL)) (by simp [tcb2TabH]))
    j1 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.entryL 20 Code.Tcb.atJ1 none none) (by simp [tcb2TabH]))
    len := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 0 Code.Tcb.atL0 none none) (by simp [tcb2TabH]))
    l1 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 14 Code.Tcb.atL1 none none) (by simp [tcb2TabH]))
    l2 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 32 Code.Tcb.atL2 none none) (by simp [tcb2TabH]))
    l3 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 50 Code.Tcb.atL3 none none) (by simp [tcb2TabH]))
    l4 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 68 Code.Tcb.atL4 none none) (by simp [tcb2TabH]))
    l5 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 99 Code.Tcb.atL5 none none) (by simp [tcb2TabH]))
    l6 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 135 Code.Tcb.atL6 none none) (by simp [tcb2TabH]))
    arg := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 146 Code.Tcb.atArg none none) (by simp [tcb2TabH]))
    bnd := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 163 Code.Tcb.atBnd none none) (by simp [tcb2TabH]))
    j2 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.lenL 198 Code.Tcb.atJ2 none none) (by simp [tcb2TabH]))
    o1 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 7 Code.Tcb.atO1 none none) (by simp [tcb2TabH]))
    o2 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 38 Code.Tcb.atO2 none none) (by simp [tcb2TabH]))
    o3 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 56 Code.Tcb.atO3 none none) (by simp [tcb2TabH]))
    o4 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 77 Code.Tcb.atO4 none none) (by simp [tcb2TabH]))
    o5 := blkPh_of_factOk hlab hr hn (hf (.blk Code.Tcb.okL 98 Code.Tcb.atO5 none none) (by simp [tcb2TabH]))
    ret := blkPh_of_factOk hlab (fun _ _ h => by cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm) hn
      (hf (.blk Code.Tcb.okL 143 Code.Tcb.atRet (some (".Lwc_main.x2", 0)) none) (by simp [tcb2TabH]))
    fullNe := by
      have := ne_of_factOk hlab (hf (.ne Code.Tcb.entryL 20 tcbFullL 0) (by simp [tcb2TabH]))
      rw [Spike.Lib.X64.Flow.ofNat_zero'] at this
      exact this
    step := by
      intro pz hp
      simp only [Tcb.stepPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 11 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 29 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 47 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 65 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 95 4) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 132 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.lenL 139 7) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 0 7) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 34 4) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 53 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 74 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 95 3) (by simp [tcb2TabH]))
      · exact step_of_factOk hlab (hf (.step Code.Tcb.okL 140 3) (by simp [tcb2TabH]))
    rmwOk := ok_of_factOk hlab (hf (.ok Code.Tcb.lenL 158) (by simp [tcb2TabH]))
    rmwTk := fun _ _ _ => Iff.rfl
    rmwIn := ⟨(112#64).setWidth 128, by rw [rmwPc, h1, hpn]; simp [own2aH, ownV]⟩
    rmwUpd := by
      rw [e5, rmwPc, h1, h0, hpn]
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

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.tcb2FactsH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.tcb2FactsH

/-- info: 'Spike.Lib.X64.HelloPh.tcb2_factH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.tcb2_factH

/-- info: 'Spike.Lib.X64.HelloPh.instOk2aPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.instOk2aPH

/-- info: 'Spike.Lib.X64.HelloPh.mOf_hdr2H' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.mOf_hdr2H

/-- info: 'Spike.Lib.X64.HelloPh.tcbPh2aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.tcbPh2aH
