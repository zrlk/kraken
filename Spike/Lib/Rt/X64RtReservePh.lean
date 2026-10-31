/-
**`scc_rt_thread_reserve`'s phase facts from A13** (x86-64; twin of
`Spike/Lib/Rt/A64RtReservePh.lean`): A13's code part
(`Scc.Cert.Spawn.X64.a13code`: `spawnGrps` in the cells and its phase table
`spawnPhTab` passing) gives `ResPh`'s table-checked fields (each block's
phase check, the label's single step, the `lock xadd` off the sites) with
the certificate's `okPcOf`/`phOf`, returning to `raL`
(`Scc.Cert.Spawn.X64.userRa`); the take's and the own map's fields are
asked of the caller (`resPh_of_a13code`).

Deviation from the A64 twin: x86-64 has one single-step site (`siPcs`, the
counter's address at `entry + 0`, 7 bytes) and the counter's add is the
5-byte `lock xadd` at `rmwPc = entry + 22`.
-/
import Spike.Lib.Rt.X64RtReserve
import Spike.Lib.Rt.X64RtPhOfTab

namespace Spike.Lib.X64.Rt.Reserve

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Reserve
open Scc.Cert.Rt.X64 (factOk_of_rtPhOk rtPhOk okPcOf phOf PhFact)
open Scc.Sem.X64 (codeLabel pcOf)
open Spike.Lib.X64.Rt.PhOfTab

-- Phase facts compare (for the membership checks below).
deriving instance DecidableEq for PhFact

/-- The facts of A13's table this file uses. -/
theorem spawnPhTab_mem :
    PhFact.blk fnL 0 rPro none none ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.blk entryL 7 rArg none none ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.blk entryL 27 rBnd none none ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.blk entryL 65 rJ none none ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.blk okL 0 rRet Scc.Cert.Spawn.X64.userRa none ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.step entryL 0 7 ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.step entryL 22 5 ∈ Scc.Cert.Spawn.X64.spawnPhTab := by
  decide +kernel

/-- **`ResPh` from A13's code part**: the table's fields from `a13code`, the
labels resolved as the certificate's (`hlab`), returning to `raL`; the
take's (`noTk`) and the own map's (`rmwIn`, `rmwUpd`) fields given. -/
theorem resPh_of_a13code {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout}
    {lab : Label → Int64} {Tk : State → Prop} {ownOf : Nat → List (Loc × Val)}
    (h : Scc.Cert.Spawn.X64.a13code lo cells Λ = true)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (phOf lo cells (rmwPc lab).toBitVec.toNat))
    (rmwUpd : ownUpdB (ownOf (phOf lo cells (rmwPc lab).toBitVec.toNat))
      (ownOf (phOf lo cells (rmwPc lab + Int64.ofNat 5).toBitVec.toNat))
      ⟨ntA lab, 8⟩ (fun old => (old.setWidth 64 + 1#64).setWidth 128) = true) :
    ResPh (okPcOf lo cells Λ) (phOf lo cells) Tk ownOf lab (lab Spike.Lib.LowerX64.raL) := by
  simp only [Scc.Cert.Spawn.X64.a13code, Bool.and_eq_true] at h
  have hf : ∀ f ∈ Scc.Cert.Spawn.X64.spawnPhTab, _ := fun f hf => factOk_of_rtPhOk (f := f) h.2 hf
  obtain ⟨mE, mArg, mBnd, mJ, mRet, mS0, mS22⟩ := spawnPhTab_mem
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo cells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      lab Spike.Lib.LowerX64.raL = lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  exact {
    e := blkPh_of_factOk hlab hr hn (hf _ mE)
    arg := blkPh_of_factOk hlab hr hn (hf _ mArg)
    bnd := blkPh_of_factOk hlab hr hn (hf _ mBnd)
    j := blkPh_of_factOk hlab hr hn (hf _ mJ)
    ok := blkPh_of_factOk hlab (fun _ _ h => by cases h; simp) hn (hf _ mRet)
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact step_of_factOk hlab (hf _ mS0)
    rmwOk := (step_of_factOk hlab (hf _ mS22)).1
    noTk := noTk
    rmwIn := rmwIn
    rmwUpd := rmwUpd }

end Spike.Lib.X64.Rt.Reserve

/-- info: 'Spike.Lib.X64.Rt.Reserve.spawnPhTab_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.spawnPhTab_mem

/-- info: 'Spike.Lib.X64.Rt.Reserve.resPh_of_a13code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.resPh_of_a13code
