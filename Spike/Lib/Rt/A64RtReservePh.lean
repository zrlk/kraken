/-
**`scc_rt_thread_reserve`'s phase facts from A13** (AArch64): A13's code
part (`Scc.Cert.Spawn.A64.a13code`: `spawnGrps` in the program and its phase
table `spawnPhTab` passing) gives `ResPh`'s table-checked fields (each
block's phase check, the label pair's single steps, the add off the sites)
with the certificate's `okPcOf`/`phOf`, returning to `raL`
(`Scc.Cert.Spawn.A64.userRa`); the take's and the own map's fields are
asked of the caller (`resPh_of_a13code`).
-/
import Spike.Lib.Rt.A64RtReserve
import Spike.Lib.Rt.A64RtPhOfTab

namespace Spike.Lib.A64.Rt.Reserve

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Reserve
open Scc.Cert.Rt.A64 (factOk_of_rtPhOk rtPhOk okPcOf phOf PhFact)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt.PhOfTab

-- Phase facts compare (for the membership checks below).
deriving instance DecidableEq for PhFact

/-- The facts of A13's table this file uses. -/
theorem spawnPhTab_mem :
    PhFact.blk fnL 0 rPro none none ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.blk entryL 2 rArg none none ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.blk entryL 6 rBnd none none ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.blk entryL 15 rJ none none ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.blk okL 0 rRet Scc.Cert.Spawn.A64.userRa none ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.step entryL 0 ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.step entryL 1 ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.step entryL 5 ∈ Scc.Cert.Spawn.A64.spawnPhTab := by
  decide +kernel

/-- **`ResPh` from A13's code part**: the table's fields from `a13code`, the
labels resolved as the certificate's (`hlab`), returning to `raL`; the
take's (`noTk`) and the own map's (`rmwIn`, `rmwUpd`) fields given. -/
theorem resPh_of_a13code {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {lab : Label → Int64}
    {Tk : State → Prop} {ownOf : Nat → List (Loc × Val)}
    (h : Scc.Cert.Spawn.A64.a13code lo prog Λ = true)
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (phOf lo prog (rmwPc lab).toBitVec.toNat))
    (rmwUpd : ownUpdB (ownOf (phOf lo prog (rmwPc lab).toBitVec.toNat))
      (ownOf (phOf lo prog (rmwPc lab + Int64.ofNat 4).toBitVec.toNat))
      ⟨ntA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) 1#64).setWidth 128) = true) :
    ResPh (okPcOf lo prog Λ) (phOf lo prog) Tk ownOf lab (lab Spike.Lib.LowerA64.raL) := by
  simp only [Scc.Cert.Spawn.A64.a13code, Bool.and_eq_true] at h
  have hf : ∀ f ∈ Scc.Cert.Spawn.A64.spawnPhTab, _ := fun f hf => factOk_of_rtPhOk (f := f) h.2 hf
  obtain ⟨mE, mArg, mBnd, mJ, mRet, mS0, mS1, mS5⟩ := spawnPhTab_mem
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.A64.deadN (codeOf lo prog) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → lab Spike.Lib.LowerA64.raL = lab r := fun _ h => nomatch h
  exact {
    e := blkPh_of_factOk hlab hr hn (hf _ mE)
    arg := blkPh_of_factOk hlab hr hn (hf _ mArg)
    bnd := blkPh_of_factOk hlab hr hn (hf _ mBnd)
    j := blkPh_of_factOk hlab hr hn (hf _ mJ)
    ok := blkPh_of_factOk hlab (fun _ h => by cases h; rfl) hn (hf _ mRet)
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact step_of_factOk hlab (hf _ mS0)
      · exact step_of_factOk hlab (hf _ mS1)
    rmwOk := (step_of_factOk hlab (hf _ mS5)).1
    noTk := noTk
    rmwIn := rmwIn
    rmwUpd := rmwUpd }

end Spike.Lib.A64.Rt.Reserve
