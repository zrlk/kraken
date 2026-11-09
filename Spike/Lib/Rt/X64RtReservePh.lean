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
    PhFact.blk okL 0 (rRet.take 3) none none ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.blk retL 0 (rRet.drop 3) Scc.Cert.Spawn.X64.userRa none ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.step entryL 0 7 ∈ Scc.Cert.Spawn.X64.spawnPhTab ∧
    PhFact.step entryL 22 5 ∈ Scc.Cert.Spawn.X64.spawnPhTab := by
  decide +kernel

/-- **The phase check of two blocks in a row**, the second at the first's
end and its start in the first's phase. -/
theorem blkPh_appendX {okPc : Nat → Bool} {ph : Nat → Nat} {dd : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {a b : List (Directive × Nat)}
    (ha : Spike.Lib.X64Consumer.blkPh okPc ph dd lab pc ra a = true)
    (hb : Spike.Lib.X64Consumer.blkPh okPc ph dd lab (pc + Int64.ofNat (a.map (·.2)).sum) ra b = true)
    (he : ph (pc + Int64.ofNat (a.map (·.2)).sum).toBitVec.toNat = ph pc.toBitVec.toNat) :
    Spike.Lib.X64Consumer.blkPh okPc ph dd lab pc ra (a ++ b) = true := by
  unfold Spike.Lib.X64Consumer.blkPh at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · have hc : Spike.Lib.X64.cellOff (a ++ b) k = Spike.Lib.X64.cellOff a k := by
      simp [Spike.Lib.X64.cellOff, List.take_append_of_le_length (Nat.le_of_lt h')]
    rw [List.getElem?_append_left h', hc]
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    have hc : Spike.Lib.X64.cellOff (a ++ b) (a.length + j) = (a.map (·.2)).sum + Spike.Lib.X64.cellOff b j := by
      simp only [Spike.Lib.X64.cellOff, List.take_append, List.map_append, List.sum_append,
        List.take_of_length_le (show a.length ≤ a.length + j by omega), Nat.add_sub_cancel_left]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hc, Int64.ofNat_add, ← Int64.add_assoc]
    exact this

/-- **`ResPh` from A13's code part**: the table's fields from `a13code`, the
labels resolved as the certificate's (`hlab`), returning to `raL`; the
take's (`noTk`) and the own map's (`rmwIn`, `rmwUpd`) fields given.
`hgap`: the return label `retL` is 8 bytes past `okL` (the `ok` block is
split at it, two facts of the table; `rtIn`'s gap counts cells only, not
the size of `okL`'s label cell); concrete cells discharge it by `decide`. -/
theorem resPh_of_a13code {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout}
    {lab : Label → Int64} {Tk : State → Prop} {ownOf : Nat → List (Loc × Val)}
    (h : Scc.Cert.Spawn.X64.a13code lo cells Λ = true)
    (hgap : codeLabel lo cells retL = (codeLabel lo cells okL).map (· + 8))
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (phOf lo cells (rmwPc lab).toBitVec.toNat))
    (rmwUpd : ownUpdB (ownOf (phOf lo cells (rmwPc lab).toBitVec.toNat))
      (ownOf (phOf lo cells (rmwPc lab + Int64.ofNat 5).toBitVec.toNat))
      ⟨ntA lab, 8⟩ (fun old => (old.setWidth 64 + 1#64).setWidth 128) = true) :
    ResPh (okPcOf lo cells Λ) (phOf lo cells) Tk ownOf lab (lab Spike.Lib.LowerX64.raL) := by
  simp only [Scc.Cert.Spawn.X64.a13code, Bool.and_eq_true] at h
  have hf : ∀ f ∈ Scc.Cert.Spawn.X64.spawnPhTab, _ := fun f hf => factOk_of_rtPhOk (f := f) h.2 hf
  obtain ⟨mE, mArg, mBnd, mJ, mRet3, mRet, mS0, mS22⟩ := spawnPhTab_mem
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo cells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') →
      lab Spike.Lib.LowerX64.raL = lab r + Int64.ofNat o' := fun _ _ h => nomatch h
  have p3 := blkPh_of_factOk (rapc := lab Spike.Lib.LowerX64.raL) (dset := fun _ => false) hlab hr hn (hf _ mRet3)
  have pR := blkPh_of_factOk (rapc := lab Spike.Lib.LowerX64.raL) (dset := fun _ => false) hlab
    (fun _ _ h => by cases h; simp) hn (hf _ mRet)
  have hok : ∃ a, codeLabel lo cells okL = some a := by
    have := hf _ mRet3
    simp only [Scc.Cert.Rt.X64.factOk] at this
    split at this
    · exact ⟨_, by assumption⟩
    · cases this
  obtain ⟨a, ha⟩ := hok
  have eR : lab retL = lab okL + Int64.ofNat 8 := by
    rw [hlab _ _ (by rw [hgap, ha]; rfl), hlab _ _ ha, Int64.ofNat_add]
  have he : phOf lo cells (lab okL + Int64.ofNat 0 + Int64.ofNat ((rRet.take 3).map (·.2)).sum).toBitVec.toNat =
      phOf lo cells (lab okL + Int64.ofNat 0).toBitVec.toNat := by
    unfold Spike.Lib.X64Consumer.blkPh at p3
    have := (List.all_eq_true.mp p3) 2 (by decide)
    simp [rRet, Spike.Lib.X64.cellOff, Spike.Lib.X64Consumer.aiTgts, Spike.Lib.X64.classify] at this
    have h8 : ((rRet.take 3).map (·.2)).sum = 8 := rfl
    rw [h8, Spike.Lib.X64.Flow.ofNat_zero']
    simpa [Int64.toBitVec_add, BitVec.toNat_add, Int64.toBitVec_ofNat] using this.2
  have okPh := blkPh_appendX p3 (by
    have hs : ((rRet.take 3).map (·.2)).sum = 8 := rfl
    rw [hs, Spike.Lib.X64.Flow.ofNat_zero', ← eR]; simpa [Spike.Lib.X64.Flow.ofNat_zero'] using pR) he
  exact {
    e := blkPh_of_factOk hlab hr hn (hf _ mE)
    arg := blkPh_of_factOk hlab hr hn (hf _ mArg)
    bnd := blkPh_of_factOk hlab hr hn (hf _ mBnd)
    j := blkPh_of_factOk hlab hr hn (hf _ mJ)
    ok := okPh
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
