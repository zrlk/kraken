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
    PhFact.blk okL 0 (rRet.take 4) none none ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.blk retL 0 (rRet.drop 4) Scc.Cert.Spawn.A64.userRa none ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.step entryL 0 ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.step entryL 1 ∈ Scc.Cert.Spawn.A64.spawnPhTab ∧
    PhFact.step entryL 5 ∈ Scc.Cert.Spawn.A64.spawnPhTab := by
  decide +kernel

/-- **The phase check of two blocks in a row**, the second at the first's
end and its start in the first's phase. -/
theorem blkPh_appendX {okPc : Nat → Bool} {ph : Nat → Nat} {dd : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {a b : List Directive}
    (ha : Spike.Lib.A64Consumer.blkPh okPc ph dd lab pc ra a = true)
    (hb : Spike.Lib.A64Consumer.blkPh okPc ph dd lab (pc + Int64.ofNat (4 * a.length)) ra b = true)
    (he : ph (pc + Int64.ofNat (4 * a.length)).toBitVec.toNat = ph pc.toBitVec.toNat) :
    Spike.Lib.A64Consumer.blkPh okPc ph dd lab pc ra (a ++ b) = true := by
  unfold Spike.Lib.A64Consumer.blkPh at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · rw [List.getElem?_append_left h']
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Nat.mul_add, Int64.ofNat_add,
      ← Int64.add_assoc]
    exact this

/-- **`ResPh` from A13's code part**: the table's fields from `a13code`, the
labels resolved as the certificate's (`hlab`), returning to `raL`; the
take's (`noTk`) and the own map's (`rmwIn`, `rmwUpd`) fields given.
`hgap`: the return label `retL` is 4 instructions (16 bytes) past `okL`
(the `ok` block is split at it, two facts of the table; `rtIn`'s gap counts
directives only, not the size of `okL`'s label); concrete programs
discharge it by `decide`. -/
theorem resPh_of_a13code {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {lab : Label → Int64}
    {Tk : State → Prop} {ownOf : Nat → List (Loc × Val)}
    (h : Scc.Cert.Spawn.A64.a13code lo prog Λ = true)
    (hgap : codeOf lo prog retL = (codeOf lo prog okL).map (· + 16))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (phOf lo prog (rmwPc lab).toBitVec.toNat))
    (rmwUpd : ownUpdB (ownOf (phOf lo prog (rmwPc lab).toBitVec.toNat))
      (ownOf (phOf lo prog (rmwPc lab + Int64.ofNat 4).toBitVec.toNat))
      ⟨ntA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) 1#64).setWidth 128) = true) :
    ResPh (okPcOf lo prog Λ) (phOf lo prog) Tk ownOf lab (lab Spike.Lib.LowerA64.raL) := by
  simp only [Scc.Cert.Spawn.A64.a13code, Bool.and_eq_true] at h
  have hf : ∀ f ∈ Scc.Cert.Spawn.A64.spawnPhTab, _ := fun f hf => factOk_of_rtPhOk (f := f) h.2 hf
  obtain ⟨mE, mArg, mBnd, mJ, mRet4, mRet, mS0, mS1, mS5⟩ := spawnPhTab_mem
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.A64.deadN (codeOf lo prog) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → lab Spike.Lib.LowerA64.raL = lab r := fun _ h => nomatch h
  have p4 := blkPh_of_factOk (rapc := lab Spike.Lib.LowerA64.raL) (dset := fun _ => false) hlab hr hn
    (hf _ mRet4)
  have pR := blkPh_of_factOk (rapc := lab Spike.Lib.LowerA64.raL) (dset := fun _ => false) hlab
    (fun _ h => by cases h; rfl) hn (hf _ mRet)
  have hok : ∃ a, codeOf lo prog okL = some a := by
    have := hf _ mRet4
    simp only [Scc.Cert.Rt.A64.factOk] at this
    split at this
    · exact ⟨_, by assumption⟩
    · cases this
  obtain ⟨a, ha⟩ := hok
  have eR : lab retL = lab okL + Int64.ofNat (4 * (rRet.take 4).length) := by
    rw [hlab _ _ (by rw [hgap, ha]; rfl), hlab _ _ ha, ← Int64.ofNat_add]; rfl
  have he : phOf lo prog (lab okL + Int64.ofNat (4 * 0) + Int64.ofNat (4 * (rRet.take 4).length)).toBitVec.toNat =
      phOf lo prog (lab okL + Int64.ofNat (4 * 0)).toBitVec.toNat := by
    unfold Spike.Lib.A64Consumer.blkPh at p4
    have := (List.all_eq_true.mp p4) 3 (by decide)
    simp (config := { decide := true }) [rRet, Spike.Lib.A64Consumer.aiTgts, Spike.Lib.A64.Flow.classify]
      at this
    rw [ofNat4_zero, show 4 * (rRet.take 4).length = 12 + 4 from rfl]
    simpa [Int64.toBitVec_add, BitVec.toNat_add, Int64.toBitVec_ofNat] using this.2
  have okPh := blkPh_appendX p4 (by rw [ofNat4_zero, ← eR]; simpa [ofNat4_zero] using pR) he
  exact {
    e := blkPh_of_factOk hlab hr hn (hf _ mE)
    arg := blkPh_of_factOk hlab hr hn (hf _ mArg)
    bnd := blkPh_of_factOk hlab hr hn (hf _ mBnd)
    j := blkPh_of_factOk hlab hr hn (hf _ mJ)
    ok := okPh
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
