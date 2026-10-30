/-
**`scc_rt_park` inside the abort-site predicate** (AArch64):
`Park.seg_park` (`Spike/Lib/A64Park.lean`) as a `SegW` segment inside
`AbOffL` (`Spike/Lib/A64AbOffLDef.lean`): every state of the routine is off
the `writeErr` and `threads` exit calls, given that the routine's pcs are
(`RunsOff lab parkRuns`, decided on the listing).

- `pcOff_add`: the pc `label l + 4c + 4k` of a run is off the exits.
- `parkRuns`: the routine's pcs as runs after its four labels.
- `seg_parkW`: the routine as one segment inside `AbOffL`.
- `ParkGW`, `seg_parkWG`: the routine inside any `W`, given every node's
  states in it (`BlkW` per block, `NodeW` per exchange and the `svc`).
-/
import Spike.Lib.A64Park
import Spike.Lib.A64AbOffLDef

namespace Spike.Lib.A64.Flow.Park

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64AbOffL (PcOff AbOffL RunsOff)

/-- **A pc of a run is off the exits**: `q = label l + 4c`, and `c + k`
within the run `(l, lo, hi)`. -/
theorem _root_.Spike.Lib.A64AbOffL.pcOff_add {lab : String → Int64} {runs : List (String × Nat × Nat)}
    (h : RunsOff lab runs) {l : String} {lo hi c k : Nat} (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ c)
    (h2 : c + k < hi) {q : Int64} (hq' : q = lab l + Int64.ofNat (4 * c)) : PcOff lab (q + Int64.ofNat (4 * k)) := by
  subst hq'
  rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add]
  exact h _ hq (c + k) (show lo ≤ c + k by omega) h2

/-- **A pc of a run is off the exits** (`k = 0` form of `pcOff_add`). -/
theorem _root_.Spike.Lib.A64AbOffL.pcOff_at {lab : String → Int64} {runs : List (String × Nat × Nat)}
    (h : RunsOff lab runs) {l : String} {lo hi c : Nat} (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ c)
    (h2 : c < hi) {q : Int64} (hq' : q = lab l + Int64.ofNat (4 * c)) : PcOff lab q := by
  subst hq'
  exact h _ hq c h1 h2

open Spike.Lib.A64AbOffL (pcOff_add pcOff_at)

/-- **`scc_rt_park`'s pcs**: the runs after its four labels. -/
def parkRuns : List (String × Nat × Nat) :=
  [("scc_rt_park", 0, 4), (".L10_scc_rt_park.0_entry", 0, 12), (".L10_scc_rt_park.1_wait", 0, 22),
    (".L10_scc_rt_park.2_done", 0, 4)]

section ProofW

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {x29 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node inside `AbOffL`: the block, its `okBlk`, its code, its run
`(l, lo, hi)` and offset `c` in it; the edge is left. -/
macro "nodeW " b:ident ok:ident f:ident l:term:max lo:term:max hi:term:max c:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn)
    (fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ => ⟨pcOff_add hW (l := $l) (lo := $lo) (hi := $hi) (c := $c) (by simp [parkRuns]) (by omega)
      (by simp [$b:ident] at hk; omega) (by simp only [N, Int64.add_assoc]; first | rfl | simp), fun _ h => h⟩)
    fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A one-instruction node's states inside `AbOffL`. -/
macro "oneW " l:term:max lo:term:max hi:term:max c:term:max : tactic =>
  `(tactic| exact fun s _ ⟨_, _, _, hpc, _⟩ => ⟨by
    show PcOff _ s.st.2
    rw [hpc, show N _ c0 x29 ra tp _ = _ from rfl]
    exact pcOff_at hW (l := $l) (lo := $lo) (hi := $hi) (c := $c) (by simp [parkRuns]) (by omega) (by omega)
      (by simp only [N, pcSvc, Int64.add_assoc]; first | rfl | simp), fun _ h => h⟩)

/-- **`scc_rt_park` inside `AbOffL`** (`seg_park` with every state off the
`writeErr` and `threads` exit calls, `hW`). -/
theorem seg_parkW (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -64)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hcode : Code c0 x29 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4)
    (hW : RunsOff (_root_.Executable.labels exe).label parkRuns) :
    SegW (AbOffL (_root_.Executable.labels exe).label) (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c0 x29 ra tp x) s c) := by
  refine fn_segW (N := N _ c0 x29 ra tp) (E := E c0 x29 ra tp) (fun i => ?_) PN.e
  cases i
  case e => nodeW b0 b0_ok e "scc_rt_park" 0 4 0; rw [N, b0_run]; hit PN.n1
  case n1 => nodeW b1 b1_ok n1 ".L10_scc_rt_park.0_entry" 0 12 0; rw [N, b1_run]; hit PN.swp1
  case swp1 =>
    refine rtSwp_ndW (A := tp + 16#64) hF (fun s he hn => hcode.swp1 s he hn) ?_ fun m σ c _ _ hJ => ?_
    · oneW ".L10_scc_rt_park.0_entry" 0 12 5
    obtain ⟨hT, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, fun v => ?_⟩
    hit PN.n2
  case n2 =>
    nodeW b2 b2_ok n2 ".L10_scc_rt_park.0_entry" 0 12 6; rw [N, b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => nodeW b3 b3_ok n3 ".L10_scc_rt_park.0_entry" 0 12 11; rw [N, b3_run]; hit PN.wait
  case wait => nodeW b4 b4_ok wait ".L10_scc_rt_park.1_wait" 0 22 0; rw [N, b4_run]; hit PN.svc
  case svc =>
    refine svc_ndW hK hF (fun s he hn => hcode.svc s he hn) ?_ (fun σ c hJ => ?_) ?_
    · oneW ".L10_scc_rt_park.1_wait" 0 22 11
    · obtain ⟨hT, h0, h1, h3, h8⟩ := hJ
      refine ⟨.futexWait, svcCall_futexWait (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl)
        (by rw [h3]; rfl), fun v _ => ⟨c, .refl c, ?_⟩⟩
      hit PN.n5
    · rintro s c σ call - ⟨-, h0, h1, h3, h8⟩ hcall
      rw [svcCall_futexWait (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl) (by rw [h3]; rfl)]
        at hcall
      cases hcall
      exact ⟨nofun, nofun, nofun, nofun⟩
  case n5 => nodeW b5 b5_ok n5 ".L10_scc_rt_park.1_wait" 0 22 12; rw [N, b5_run]; hit PN.swp2
  case swp2 =>
    refine rtSwp_ndW (A := tp + 16#64) hF (fun s he hn => hcode.swp2 s he hn) ?_ fun m σ c _ _ hJ => ?_
    · oneW ".L10_scc_rt_park.1_wait" 0 22 16
    obtain ⟨hT, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, fun v => ?_⟩
    hit PN.n6
  case n6 => nodeW b6 b6_ok n6 ".L10_scc_rt_park.1_wait" 0 22 17; rw [N, b6_run]; exit PX.ret
  case done => nodeW b7 b7_ok done ".L10_scc_rt_park.2_done" 0 4 0; rw [N, b7_run]; exit PX.ret

/-- **The routine's states inside `W`**, at one region `R` and frame
condition `F`: every block node's internal states (`BlkW`), the two
exchanges' and the futex wait's (`NodeW`). -/
structure ParkGW (W : Frag isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (c0 : Ctl) (x29 ra tp : BitVec 64) : Prop where
  e : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .e) b0
  n1 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .n1) b1
  swp1 : NodeW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .swp1)
  n2 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .n2) b2
  n3 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .n3) b3
  wait : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .wait) b4
  svc : NodeW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .svc)
  n5 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .n5) b5
  swp2 : NodeW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .swp2)
  n6 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .n6) b6
  done : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .done) b7

set_option hygiene false in
/-- A block node inside `W`: the block, its `okBlk`, its code and `ParkGW`
field; the edge is left. -/
macro "nodeGW " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) hW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_park` inside any `W`** (`seg_park` with every node's states
in `W`, `hW`). -/
theorem seg_parkWG {W : Frag isaLSE2} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -64) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hcode : Code c0 x29 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4)
    (hW : ParkGW W exe endPc R F c0 x29 ra tp) :
    SegW W (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c0 x29 ra tp x) s c) := by
  refine fn_segW (N := N _ c0 x29 ra tp) (E := E c0 x29 ra tp) (fun i => ?_) PN.e
  cases i
  case e => nodeGW b0 b0_ok e; rw [N, b0_run]; hit PN.n1
  case n1 => nodeGW b1 b1_ok n1; rw [N, b1_run]; hit PN.swp1
  case swp1 =>
    refine rtSwp_ndW (A := tp + 16#64) hF (fun s he hn => hcode.swp1 s he hn) hW.swp1 fun m σ c _ _ hJ => ?_
    obtain ⟨hT, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, fun v => ?_⟩
    hit PN.n2
  case n2 =>
    nodeGW b2 b2_ok n2; rw [N, b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => nodeGW b3 b3_ok n3; rw [N, b3_run]; hit PN.wait
  case wait => nodeGW b4 b4_ok wait; rw [N, b4_run]; hit PN.svc
  case svc =>
    refine svc_ndW hK hF (fun s he hn => hcode.svc s he hn) hW.svc (fun σ c hJ => ?_) ?_
    · obtain ⟨hT, h0, h1, h3, h8⟩ := hJ
      refine ⟨.futexWait, svcCall_futexWait (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl)
        (by rw [h3]; rfl), fun v _ => ⟨c, .refl c, ?_⟩⟩
      hit PN.n5
    · rintro s c σ call - ⟨-, h0, h1, h3, h8⟩ hcall
      rw [svcCall_futexWait (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl) (by rw [h3]; rfl)]
        at hcall
      cases hcall
      exact ⟨nofun, nofun, nofun, nofun⟩
  case n5 => nodeGW b5 b5_ok n5; rw [N, b5_run]; hit PN.swp2
  case swp2 =>
    refine rtSwp_ndW (A := tp + 16#64) hF (fun s he hn => hcode.swp2 s he hn) hW.swp2 fun m σ c _ _ hJ => ?_
    obtain ⟨hT, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, fun v => ?_⟩
    hit PN.n6
  case n6 => nodeGW b6 b6_ok n6; rw [N, b6_run]; exit PX.ret
  case done => nodeGW b7 b7_ok done; rw [N, b7_run]; exit PX.ret

end ProofW

end Spike.Lib.A64.Flow.Park
